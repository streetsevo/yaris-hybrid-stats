# -*- coding: utf-8 -*-
"""
Toyota Yaris 4 Hybrid (2021) — Полная панель диагностики и ТО
================================================================
Источники данных:
  1. hybridassistant.db (SQLite, приложение Hybrid Assistant) —
     скачивается автоматически с Google Диска при запуске.
  2. Ежемесячные CSV-логи Dr. Prius — загружаются вручную админом
     через st.file_uploader на вкладке "Мониторинг Dr. Prius".
  3. maintenance.json — локальный журнал ТО (создаётся автоматически).

Разверни на Streamlit Community Cloud: положи этот файл и
requirements.txt в репозиторий на GitHub. Саму базу hybridassistant.db
в репозиторий загружать НЕ нужно — она скачивается с Google Диска.

============================== СХЕМА БД =========================
Проверена на реальном файле hybridassistant.db:

  TRIPS   (TSDEB, TSFIN, NBSEC, NKMS) — сводка по поездкам,
           TSDEB/TSFIN в мс Unix-времени, NKMS — пробег поездки в км.

  TRIPINFO (TIMESTAMP=TSFIN, NUMBRAKES, NUMBADBRAKES, NUMHALFBRAKES,
            ICE_KWH, KWHPOS, KWHNEG, REGENKWH, ...) — агрегаты по
            поездке от самого Hybrid Assistant.

  FASTLOG (TIMESTAMP, ODO, SPEED_OBD, GPS_LAT, GPS_LON, GPS_SPEED,
           HV_V, HV_A, SOC, ICE_TEMP, ICE_RPM, ICE_LOAD, BRK_REG_TRQ,
           BRK_MCYL_TRQ, TRIP_DIST, TRIP_EV_DIST, LTFT, STFT,
           TRIPFUEL(мл), FUELFLOWH, INVERTER_TEMP, BATTERY_TEMP,
           MG_TEMP, AMBIENT_TEMP, MG1_RPM, MG1_TORQUE, MG2_RPM,
           MG2_TORQUE, MGR_RPM, MGR_TORQUE, ...) — посекундная
           телеметрия. Это основной источник данных для карт,
           графиков и экспертных параметров.
           ВАЖНО: BRK_MCYL_TRQ — крутящий момент главного тормозного
           цилиндра (механическое/фрикционное торможение колодками),
           BRK_REG_TRQ — момент рекуперативного торможения. У Hybrid
           Assistant нет отдельных PID для фазных токов MG1/MG2 —
           доступны только обороты и крутящий момент.

  BATTLOG (TIMESTAMP, CELL_01..CELL_19, TB1..TB8, AMP, SOC) —
           поблочные напряжения и до 8 датчиков температуры ВВБ.
           Заполняется только если в настройках Hybrid Assistant
           включён HighSpeedLogging (по умолчанию выключен).

  HVCHECK / HVCHECKCELL / HVCHECKTEMPERATURE (TIMESTAMP, ELEMENT,
           VALUE) — данные отдельной процедуры "HV Check".

TRIPFUEL обнуляется в начале каждой поездки и накапливается в мл.
Нет PID для сопротивления изоляции ВВБ — Hybrid Assistant этот
параметр не считывает, поэтому соответствующий индикатор безопасности
показывается честно как "нет данных", а не выдумывается.
==================================================================
"""

import hashlib
import hmac
import io
import json
import os
import re
import sqlite3
import time
from datetime import date, datetime, timedelta

import gdown
import numpy as np
import pandas as pd
import plotly.graph_objects as go
import streamlit as st

try:
    import google.generativeai as genai

    GENAI_AVAILABLE = True
except ImportError:
    GENAI_AVAILABLE = False


# ============================================================
# КОНФИГУРАЦИЯ
# ============================================================

# --- Источник основной базы данных: Google Диск ---
GDRIVE_FILE_ID = "1VrS5Kh-a1lh_P-FWNMyolVeigenI6dLa"
LOCAL_DB_CACHE_PATH = "/tmp/hybridassistant_downloaded.db"
DB_CACHE_TTL_SECONDS = 30 * 60  # 30 минут между автоматическими обновлениями

MAINTENANCE_FILE = "maintenance.json"
DR_PRIUS_UPLOAD_DIR = "/tmp/dr_prius_logs"

# --- Защита формы ТО и кода доступа к картам ---
# Секреты НИКОГДА не хранятся в коде в открытом виде — только их
# SHA-256 хеши. Реальные значения задаются через st.secrets:
#   maintenance_password_hash = "..."
#   map_access_code_hash = "..."
# Хеши ниже — запасной вариант "из коробки" для пароля ALPzqmfg1029
# и кода 95-100 (сгенерированы командой:
#   python3 -c "import hashlib; print(hashlib.sha256('ЗНАЧЕНИЕ'.encode()).hexdigest())" )
_FALLBACK_PASSWORD_HASH = "b3ff0fc30e7ac18f4fc1b8c492379aeeeb7b3cf840bb00d3f1248a8a6854ad6c"
_FALLBACK_MAP_CODE_HASH = "80f71f5ee58fee5ad5ccb7d31d125818580dbefecbbe8e6ed43b674c717b242b"

MAX_PASSWORD_ATTEMPTS = 5   # попыток до временной блокировки (для пароля ТО И кода карт)
LOCKOUT_SECONDS = 5 * 60    # длительность блокировки, сек

# --- Пороговые значения перегрева ---
INVERTER_TEMP_LIMIT = 75.0  # °C
ENGINE_TEMP_LIMIT = 95.0    # °C

# --- Диапазон дельты напряжений ВВБ для расчёта SOH ---
SOH_DELTA_MIN = 0.02  # В -> 100% здоровья
SOH_DELTA_MAX = 0.20  # В -> 0% здоровья

# --- LTFT (долговременная топливная коррекция) ---
LTFT_WARNING_MIN = -8.0
LTFT_WARNING_MAX = 8.0

# --- Расхождения между HA и Dr. Prius, при которых значение красим красным ---
SOH_DIFF_THRESHOLD = 3.0       # процентных пунктов
DELTA_V_DIFF_THRESHOLD = 0.03  # вольт

# --- ГБО ---
LPG_INSTALL_ODO_KM = 117_000
CAR_MANUFACTURE_YEAR = 2021

# Паспортная (справочная, не измеренная) ёмкость NiMH-модулей Yaris/Aqua.
# Показывается как ориентир завода-изготовителя, а не как измерение.
FACTORY_AH_CAPACITY_REFERENCE = 6.5  # Ah

# Порог для усреднения температурного графика (иначе Plotly будет тормозить)
TEMP_CHART_RESAMPLE_THRESHOLD = 5000

# --- Интервалы ТО ---
# lpg_km/lpg_years — интервал ПОСЛЕ установки ГБО (если None — как до ГБО).
# lpg_only — пункт появляется только после установки ГБО.
# first_at_km — для lpg_only-пунктов: пробег первого обслуживания
# отсчитывается не от точки установки ГБО + интервал, а задан явно.
MAINTENANCE_ITEMS = [
    {
        "key": "oil",
        "km": 15_000, "years": 1,
        "lpg_km": 15_000, "lpg_years": 1,
        "smart_oil_forecast": True,
        "keywords": ["масло", "olej", "oil", "0w-16", "0w16"],
    },
    {
        "key": "spark_plugs",
        "km": 90_000, "years": None,
        "lpg_km": 45_000, "lpg_years": None,
        "keywords": ["свеч", "świec", "swiec", "plug"],
    },
    {
        "key": "brake_fluid",
        "km": 30_000, "years": 2,
        "lpg_km": 30_000, "lpg_years": 2,
        "keywords": ["тормозн", "hamulc", "brake fluid", "dot"],
    },
    {
        "key": "coolant",
        "km": 150_000, "years": 5,
        "lpg_km": 150_000, "lpg_years": 5,
        "keywords": ["антифриз", "охлажда", "chłodz", "chlodz", "coolant", "sllc"],
    },
    {
        "key": "air_filter",
        "km": 45_000, "years": 3,
        "lpg_km": 45_000, "lpg_years": 3,
        "keywords": ["воздушн", "powietrz", "air filter"],
    },
    {
        "key": "lpg_filters",
        "km": None, "years": None,
        "lpg_km": 15_000, "lpg_years": None,
        "lpg_only": True,
        "keywords": ["гбо фильтр", "filtr gazu", "lpg filter", "фильтр газа"],
    },
    {
        "key": "lpg_valves",
        "km": None, "years": None,
        "lpg_km": 45_000, "lpg_years": None,
        "lpg_only": True,
        "first_at_km": 162_000,
        "keywords": ["клапан", "zawor", "zawór", "valve clearance", "зазор клапан"],
    },
]

# Порог "скоро" для предупреждений по ТО
MAINTENANCE_SOON_KM = 1500
MAINTENANCE_SOON_DAYS = 30


# ============================================================
# ПЕРЕВОДЫ / TŁUMACZENIA
# ============================================================

TR = {
    "ru": {
        "page_title": "Toyota Yaris 4 Hybrid — Диагностика",
        "app_title": "🚗 Toyota Yaris 4 Hybrid (2021) — Полная диагностика",
        "language_label": "Язык / Language",
        "refresh_db_button": "🔄 Обновить базу данных",
        "db_last_loaded": "База данных загружена: {timestamp}",
        "downloading_db": "Загрузка базы данных с Google Диска…",
        "db_missing": "⚠️ Не удалось скачать базу данных с Google Диска. Проверьте, что доступ к файлу открыт по ссылке (\"Все, у кого есть ссылка\" → \"Читатель\").",
        "db_error": "⚠️ Не удалось прочитать базу данных: {error}",
        "no_trip_data": "Нет данных о поездках для отображения.",
        "no_log_data": "Нет данных телеметрии (логов) для отображения.",
        "no_cell_data": "Нет данных о напряжении элементов батареи. Включите HighSpeedLogging в настройках Hybrid Assistant или проведите процедуру HV Check.",
        "no_gps_data": "Нет GPS-данных для этой поездки/периода.",
        "not_enough_data": "Недостаточно данных для расчёта.",
        # --- Вкладки ---
        "tab1": "📊 Аналитика и Диагностика",
        "tab2": "📈 Детальные логи",
        "tab3": "🔋 Мониторинг Dr. Prius",
        "tab4": "⚖️ Сравнение и тренды",
        "tab5": "🔧 Техническое обслуживание",
        # --- Код доступа к картам ---
        "map_code_label": "Введите код доступа",
        "map_code_check_button": "Проверить код",
        "map_code_close_button": "Продолжить без карт",
        "code_wrong": "🔒 Неверный код. Осталось попыток: {attempts_left}.",
        "code_locked": "🔒 Слишком много неверных попыток. Повторите через {minutes} мин {seconds} сек.",
        "maps_locked_message": "Доступ к картам ограничен. Введите код доступа.",
        # --- Метрики / карточки ---
        "metric_total_trips": "Всего поездок",
        "metric_total_distance": "Общий пробег (км)",
        "metric_avg_consumption": "Средний расход (л/100км)",
        "metric_soh": "Здоровье батареи (SOH)",
        "metric_ev_pct": "% пути на EV",
        "metric_ice_pct": "% пути на ДВС",
        "metric_fuel_ml": "Расход топлива, мл",
        "metric_brake_events": "Механических торможений",
        # --- Карты ---
        "map_section_title": "🗺️ Карта поездки (стиль My Toyota)",
        "map_select_trip": "Выберите поездку",
        "map_period_title": "🗺️ Карта за период",
        "map_period_label": "Период",
        "map_period_day": "День",
        "map_period_week": "Неделя",
        "map_period_month": "Месяц",
        "map_period_year": "Год",
        "map_period_avg_consumption": "Средний расход за период: {value} л/100км",
        "legend_ev": "EV (ДВС выключен)",
        "legend_ice": "ДВС работает",
        # --- Экспертные параметры ---
        "expert_params_title": "🧪 Экспертные параметры",
        "ltft_title": "Долговременная топливная коррекция (LTFT), среднее после установки ГБО",
        "ltft_warning": "⚠️ Рекомендуется проверить газовые форсунки и карту ГБО (смесь неоптимальна).",
        "hv_safety_title": "Индикатор безопасности ВВБ (сопротивление изоляции)",
        "hv_safety_no_data": "ℹ️ Hybrid Assistant не считывает параметр сопротивления изоляции ВВБ через OBD — эта диагностика недоступна программно. Для проверки изоляции обратитесь в сервис с мегаомметром.",
        # --- Smart diagnostics ---
        "smart_diag_title": "🔮 Умный прогноз (Smart Diagnostics)",
        "soh_forecast_title": "Прогноз остатка ресурса ВВБ до критической дельты (0.20В)",
        "soh_forecast_result": "При текущей динамике критическая дельта ожидается примерно через {days} дн. ({date}).",
        "soh_forecast_stable": "Дельта напряжений стабильна или уменьшается — угрозы в обозримом будущем не выявлено.",
        "soh_no_data_hint": "Для расчёта прогноза ВВБ выполните тест HV Check в приложении на телефоне и обновите базу данных.",
        "maint_forecast_title": "🧰 Прогноз по регламентным работам",
        "maint_gbo_not_installed": "ГБО ещё не установлено (устанавливается на пробеге 117 000 км).",
        "maint_no_record_generic_remaining": "Запись о замене не найдена в журнале. Расчёт ведётся от 2021 года выпуска автомобиля и пробега 0 км. По регламенту осталось: {km} км.",
        "maint_no_record_generic_overdue": "Запись о замене не найдена в журнале. Расчёт ведётся от 2021 года выпуска автомобиля и пробега 0 км. Замена пропущена — пробег без замены: {km} км.",
        "maint_no_record_lpg_remaining": "Запись о замене не найдена в журнале. Расчёт ведётся от точки установки ГБО (пробег 117 000 км). По регламенту осталось: {km} км.",
        "maint_no_record_lpg_overdue": "Запись о замене не найдена в журнале. Расчёт ведётся от точки установки ГБО (пробег 117 000 км). Замена пропущена — пробег без замены: {km} км.",
        "radiator_forecast_title": "Прогноз загрязнения радиаторов (тренд температур относительно уличной)",
        "radiator_forecast_result": "Разница температура инвертора/ДВС минус уличная растёт на ~{value}°C в месяц — стоит присмотреться к радиаторам.",
        "radiator_forecast_stable": "Разница температур относительно уличной стабильна — признаков забивания радиаторов не выявлено.",
        # --- Вкладка 2: детальные логи ---
        "logs_select_trip": "Выберите поездку для детального анализа",
        "logs_chart_speed_rpm": "Скорость и обороты ДВС",
        "logs_chart_hv": "Напряжение и ток батареи (HV)",
        "logs_chart_temps": "Температуры ДВС, инвертора и ВВБ",
        "logs_chart_mg": "Мотор-генераторы MG1 / MG2 (обороты и момент)",
        "logs_mg_note": "ℹ️ Hybrid Assistant не логирует фазные токи MG1/MG2 — доступны только обороты и крутящий момент.",
        "logs_battlog_note": "Показаны отдельные датчики ВВБ из подробного лога (BATTLOG) за время этой поездки.",
        "logs_no_battlog": "Подробные датчики ВВБ (BATTLOG) для этой поездки недоступны — показана усреднённая температура ВВБ из основного лога.",
        # --- Вкладка 3: Dr. Prius ---
        "drprius_upload_label": "Загрузите ежемесячный CSV-отчёт Dr. Prius",
        "drprius_upload_help": "Можно загрузить сразу несколько файлов за разные месяцы.",
        "drprius_no_files": "Файлы Dr. Prius ещё не загружены.",
        "drprius_parse_error": "⚠️ Не удалось распознать формат файла {name}: не найдены столбцы с сопротивлением/напряжением по блокам. Проверьте, что заголовки колонок содержат слово resistance/opór и voltage/napięcie с номером блока.",
        "drprius_resistance_chart": "Внутреннее сопротивление по блокам (мОм)",
        "drprius_voltage_chart": "Напряжение по блокам (мВ)",
        "drprius_wear_title": "Прогноз износа ячеек",
        "drprius_wear_result": "⚠️ Блок(и) {blocks} — сопротивление растёт быстрее остальных. Рекомендуется дополнительная проверка.",
        "drprius_wear_ok": "Существенных отклонений в темпе роста сопротивления между блоками не выявлено.",
        "drprius_temp_spread_title": "Температурный разброс между датчиками ВВБ",
        "drprius_temp_spread_warning": "⚠️ Максимальный разброс температур между датчиками: {value}°C — рекомендуется прочистить вентиляцию ВВБ.",
        "drprius_temp_spread_ok": "Разброс температур между датчиками в норме (макс. {value}°C).",
        "drprius_need_two_months": "Для прогноза износа нужно минимум 2 файла за разные месяцы.",
        # --- Вкладка 4: сравнение ---
        "compare_select_month": "Выберите месяц для сравнения",
        "compare_table_title": "Сравнение показателей: Hybrid Assistant vs Dr. Prius",
        "compare_col_metric": "Показатель",
        "compare_col_ha": "Hybrid Assistant",
        "compare_col_drprius": "Dr. Prius",
        "compare_col_diff_flag": "Расхождение",
        "compare_diff_high": "⚠️ выше нормы",
        "compare_diff_ok": "в норме",
        "compare_na": "н/д",
        "compare_metric_soh": "SOH, %",
        "compare_metric_delta": "Макс. дельта напряжений, В",
        "compare_metric_peak_temp": "Пиковая температура ВВБ, °C",
        "compare_metric_ah": "Ёмкость Ah (заводская, справочно)",
        "compare_trend_soh": "Тренд SOH во времени",
        "compare_trend_delta": "Рост дельты напряжений во времени",
        "compare_trend_seasonal": "Сезонное сравнение температур ВВБ (лето к лету)",
        "compare_seasonal_not_enough": "В базе данных пока только один сезон/год наблюдений — для сравнения \"лето к лету\" нужно больше исторических данных.",
        # --- Вкладка 5: ТО ---
        "maintenance_title": "История технического обслуживания",
        "maintenance_empty": "Записи о техническом обслуживании отсутствуют.",
        "col_date": "Дата",
        "col_mileage": "Пробег (км)",
        "col_description": "Что сделано",
        "maintenance_status_title": "Статус регламентных работ",
        "maintenance_status_overdue": "🔴 Просрочено",
        "maintenance_status_soon": "🟡 Скоро",
        "maintenance_status_ok": "🟢 В норме",
        "maintenance_status_km_left": "Осталось: {km} км",
        "maintenance_status_days_left": "{days} дн.",
        "maintenance_current_mileage": "Текущий пробег (по данным базы): {value} км",
        "lpg_installed_note": "ℹ️ На пробеге 117 000 км установлено ГБО — интервалы ниже уже адаптированы под газовое оборудование.",
        "add_record_header": "Добавить новую запись",
        "password_label": "Введите пароль для доступа к добавлению записей",
        "password_wrong": "🔒 Неверный пароль. Осталось попыток: {attempts_left}.",
        "password_needed": "🔒 Для добавления новой записи введите пароль выше.",
        "password_locked": "🔒 Слишком много неверных попыток. Повторите через {minutes} мин {seconds} сек.",
        "password_unlocked": "🔓 Доступ разрешён для текущей сессии.",
        "lock_again_button": "🔒 Закрыть доступ",
        "form_date": "Дата обслуживания",
        "form_mileage": "Пробег на момент ТО (км)",
        "form_description": "Описание выполненных работ",
        "save_button": "💾 Сохранить запись",
        "save_success": "✅ Запись успешно сохранена!",
        "save_fill_all": "⚠️ Заполните все поля перед сохранением.",
        "invoice_upload_label": "📷 Сфотографируйте фактуру/чек — данные подставятся автоматически",
        "invoice_processing": "Распознаём фактуру через Gemini…",
        "invoice_success": "✅ Данные распознаны и подставлены в форму ниже.",
        "invoice_error": "⚠️ Не удалось распознать фактуру: {error}",
        "invoice_unavailable": "ℹ️ Автоматическое распознавание фактур недоступно: не настроен GEMINI_API_KEY в Secrets или не установлена библиотека google-generativeai.",
        "smart_oil_hint": "🧠 Прогноз с учётом моточасов ДВС: остаток пробега скорректирован на {pct}% из-за интенсивной работы ДВС/ГБО.",
    },
    "pl": {
        "page_title": "Toyota Yaris 4 Hybrid — Diagnostyka",
        "app_title": "🚗 Toyota Yaris 4 Hybrid (2021) — Pełna diagnostyka",
        "language_label": "Język / Язык",
        "refresh_db_button": "🔄 Odśwież bazę danych",
        "db_last_loaded": "Baza danych wczytana: {timestamp}",
        "downloading_db": "Pobieranie bazy danych z Google Drive…",
        "db_missing": "⚠️ Nie udało się pobrać bazy danych z Google Drive. Sprawdź, czy dostęp do pliku jest ustawiony jako \"Każdy, kto ma link\" → \"Czytelnik\".",
        "db_error": "⚠️ Nie udało się odczytać bazy danych: {error}",
        "no_trip_data": "Brak danych o przejazdach do wyświetlenia.",
        "no_log_data": "Brak danych telemetrycznych (logów) do wyświetlenia.",
        "no_cell_data": "Brak danych o napięciu ogniw baterii. Włącz HighSpeedLogging w ustawieniach Hybrid Assistant lub wykonaj procedurę HV Check.",
        "no_gps_data": "Brak danych GPS dla tego przejazdu/okresu.",
        "not_enough_data": "Za mało danych do obliczeń.",
        "tab1": "📊 Analityka i Diagnostyka",
        "tab2": "📈 Szczegółowe logi",
        "tab3": "🔋 Monitorowanie Dr. Prius",
        "tab4": "⚖️ Porównanie i trendy",
        "tab5": "🔧 Przeglądy techniczne",
        "map_code_label": "Wprowadź kod dostępu",
        "map_code_check_button": "Sprawdź kod",
        "map_code_close_button": "Kontynuuj bez map",
        "code_wrong": "🔒 Nieprawidłowy kod. Pozostałe próby: {attempts_left}.",
        "code_locked": "🔒 Zbyt wiele nieudanych prób. Spróbuj ponownie za {minutes} min {seconds} s.",
        "maps_locked_message": "Dostęp do map ograniczony. Wprowadź kod dostępu.",
        "metric_total_trips": "Liczba przejazdów",
        "metric_total_distance": "Łączny przebieg (km)",
        "metric_avg_consumption": "Średnie spalanie (l/100km)",
        "metric_soh": "Kondycja baterii (SOH)",
        "metric_ev_pct": "% trasy na EV",
        "metric_ice_pct": "% trasy na silniku",
        "metric_fuel_ml": "Zużyte paliwo, ml",
        "metric_brake_events": "Hamowań mechanicznych",
        "map_section_title": "🗺️ Mapa przejazdu (styl My Toyota)",
        "map_select_trip": "Wybierz przejazd",
        "map_period_title": "🗺️ Mapa za okres",
        "map_period_label": "Okres",
        "map_period_day": "Dzień",
        "map_period_week": "Tydzień",
        "map_period_month": "Miesiąc",
        "map_period_year": "Rok",
        "map_period_avg_consumption": "Średnie spalanie w okresie: {value} l/100km",
        "legend_ev": "EV (silnik wyłączony)",
        "legend_ice": "Silnik pracuje",
        "expert_params_title": "🧪 Parametry eksperckie",
        "ltft_title": "Długoterminowa korekta paliwa (LTFT), średnia po montażu LPG",
        "ltft_warning": "⚠️ Zalecana kontrola wtryskiwaczy gazowych i mapy LPG (mieszanka nieoptymalna).",
        "hv_safety_title": "Wskaźnik bezpieczeństwa HV (rezystancja izolacji)",
        "hv_safety_no_data": "ℹ️ Hybrid Assistant nie odczytuje rezystancji izolacji HV przez OBD — ta diagnostyka jest niedostępna programowo. W celu sprawdzenia izolacji skontaktuj się z serwisem (megaomomierz).",
        "smart_diag_title": "🔮 Inteligentna prognoza (Smart Diagnostics)",
        "soh_forecast_title": "Prognoza zasobu baterii HV do krytycznej delty (0.20V)",
        "soh_forecast_result": "Przy obecnej dynamice krytyczna delta oczekiwana za ok. {days} dni ({date}).",
        "soh_forecast_stable": "Delta napięć jest stabilna lub maleje — nie wykryto zagrożenia w najbliższym czasie.",
        "soh_no_data_hint": "Aby obliczyć prognozę baterii HV, wykonaj test HV Check w aplikacji na telefonie i zaktualizuj bazę danych.",
        "maint_forecast_title": "🧰 Prognoza przeglądów okresowych",
        "maint_gbo_not_installed": "LPG jeszcze nie zamontowano (montaż przy przebiegu 117 000 km).",
        "maint_no_record_generic_remaining": "Nie znaleziono wpisu o wymianie w dzienniku. Obliczenia liczone są od 2021 roku produkcji auta i przebiegu 0 km. Pozostało wg harmonogramu: {km} km.",
        "maint_no_record_generic_overdue": "Nie znaleziono wpisu o wymianie w dzienniku. Obliczenia liczone są od 2021 roku produkcji auta i przebiegu 0 km. Wymiana przeoczona — przebieg bez wymiany: {km} km.",
        "maint_no_record_lpg_remaining": "Nie znaleziono wpisu o wymianie w dzienniku. Obliczenia liczone są od momentu montażu LPG (przebieg 117 000 km). Pozostało wg harmonogramu: {km} km.",
        "maint_no_record_lpg_overdue": "Nie znaleziono wpisu o wymianie w dzienniku. Obliczenia liczone są od momentu montażu LPG (przebieg 117 000 km). Wymiana przeoczona — przebieg bez wymiany: {km} km.",
        "radiator_forecast_title": "Prognoza zabrudzenia chłodnic (trend temperatur względem otoczenia)",
        "radiator_forecast_result": "Różnica temperatury falownika/silnika minus otoczenie rośnie o ~{value}°C miesięcznie — warto sprawdzić chłodnice.",
        "radiator_forecast_stable": "Różnica temperatur względem otoczenia jest stabilna — brak oznak zabrudzenia chłodnic.",
        "logs_select_trip": "Wybierz przejazd do szczegółowej analizy",
        "logs_chart_speed_rpm": "Prędkość i obroty silnika",
        "logs_chart_hv": "Napięcie i prąd baterii (HV)",
        "logs_chart_temps": "Temperatury silnika, falownika i baterii HV",
        "logs_chart_mg": "Silniki MG1 / MG2 (obroty i moment)",
        "logs_mg_note": "ℹ️ Hybrid Assistant nie loguje prądów fazowych MG1/MG2 — dostępne są tylko obroty i moment obrotowy.",
        "logs_battlog_note": "Pokazano osobne czujniki baterii HV ze szczegółowego logu (BATTLOG) dla tego przejazdu.",
        "logs_no_battlog": "Szczegółowe czujniki baterii HV (BATTLOG) niedostępne dla tego przejazdu — pokazano uśrednioną temperaturę z głównego logu.",
        "drprius_upload_label": "Wgraj miesięczny raport CSV z Dr. Prius",
        "drprius_upload_help": "Można wgrać od razu kilka plików za różne miesiące.",
        "drprius_no_files": "Pliki Dr. Prius nie zostały jeszcze wgrane.",
        "drprius_parse_error": "⚠️ Nie udało się rozpoznać formatu pliku {name}: brak kolumn z rezystancją/napięciem dla bloków. Sprawdź, czy nagłówki zawierają słowo resistance/opór oraz voltage/napięcie z numerem bloku.",
        "drprius_resistance_chart": "Rezystancja wewnętrzna wg bloków (mOhm)",
        "drprius_voltage_chart": "Napięcie wg bloków (mV)",
        "drprius_wear_title": "Prognoza zużycia ogniw",
        "drprius_wear_result": "⚠️ Blok(i) {blocks} — rezystancja rośnie szybciej niż pozostałe. Zalecana dodatkowa kontrola.",
        "drprius_wear_ok": "Nie wykryto istotnych odchyleń w tempie wzrostu rezystancji między blokami.",
        "drprius_temp_spread_title": "Rozrzut temperatur między czujnikami HV",
        "drprius_temp_spread_warning": "⚠️ Maksymalny rozrzut temperatur między czujnikami: {value}°C — zalecane oczyszczenie wentylacji baterii HV.",
        "drprius_temp_spread_ok": "Rozrzut temperatur w normie (maks. {value}°C).",
        "drprius_need_two_months": "Do prognozy zużycia potrzebne są minimum 2 pliki z różnych miesięcy.",
        "compare_select_month": "Wybierz miesiąc do porównania",
        "compare_table_title": "Porównanie wskaźników: Hybrid Assistant vs Dr. Prius",
        "compare_col_metric": "Wskaźnik",
        "compare_col_ha": "Hybrid Assistant",
        "compare_col_drprius": "Dr. Prius",
        "compare_col_diff_flag": "Rozbieżność",
        "compare_diff_high": "⚠️ powyżej normy",
        "compare_diff_ok": "w normie",
        "compare_na": "brak danych",
        "compare_metric_soh": "SOH, %",
        "compare_metric_delta": "Maks. delta napięć, V",
        "compare_metric_peak_temp": "Szczytowa temperatura HV, °C",
        "compare_metric_ah": "Pojemność Ah (fabryczna, orientacyjnie)",
        "compare_trend_soh": "Trend SOH w czasie",
        "compare_trend_delta": "Wzrost delty napięć w czasie",
        "compare_trend_seasonal": "Sezonowe porównanie temperatur HV (lato do lata)",
        "compare_seasonal_not_enough": "W bazie danych jest na razie tylko jeden sezon/rok obserwacji — do porównania \"lato do lata\" potrzeba więcej danych historycznych.",
        "maintenance_title": "Historia przeglądów technicznych",
        "maintenance_empty": "Brak zapisanych przeglądów.",
        "col_date": "Data",
        "col_mileage": "Przebieg (km)",
        "col_description": "Zakres prac",
        "maintenance_status_title": "Status przeglądów okresowych",
        "maintenance_status_overdue": "🔴 Przeterminowane",
        "maintenance_status_soon": "🟡 Wkrótce",
        "maintenance_status_ok": "🟢 W normie",
        "maintenance_status_km_left": "Pozostało: {km} km",
        "maintenance_status_days_left": "{days} dni",
        "maintenance_current_mileage": "Bieżący przebieg (wg bazy danych): {value} km",
        "lpg_installed_note": "ℹ️ Przy przebiegu 117 000 km zamontowano LPG — poniższe interwały są już dostosowane do instalacji gazowej.",
        "add_record_header": "Dodaj nowy wpis",
        "password_label": "Wprowadź hasło, aby dodać wpis",
        "password_wrong": "🔒 Nieprawidłowe hasło. Pozostałe próby: {attempts_left}.",
        "password_needed": "🔒 Aby dodać nowy wpis, wprowadź hasło powyżej.",
        "password_locked": "🔒 Zbyt wiele nieudanych prób. Spróbuj ponownie za {minutes} min {seconds} s.",
        "password_unlocked": "🔓 Dostęp odblokowany na tę sesję.",
        "lock_again_button": "🔒 Zablokuj ponownie",
        "form_date": "Data przeglądu",
        "form_mileage": "Przebieg w dniu przeglądu (km)",
        "form_description": "Opis wykonanych prac",
        "save_button": "💾 Zapisz wpis",
        "save_success": "✅ Wpis został zapisany!",
        "save_fill_all": "⚠️ Uzupełnij wszystkie pola przed zapisaniem.",
        "invoice_upload_label": "📷 Sfotografuj fakturę/paragon — dane zostaną podstawione automatycznie",
        "invoice_processing": "Rozpoznawanie faktury przez Gemini…",
        "invoice_success": "✅ Dane rozpoznane i podstawione do formularza poniżej.",
        "invoice_error": "⚠️ Nie udało się rozpoznać faktury: {error}",
        "invoice_unavailable": "ℹ️ Automatyczne rozpoznawanie faktur niedostępne: brak GEMINI_API_KEY w Secrets lub brak biblioteki google-generativeai.",
        "smart_oil_hint": "🧠 Prognoza z uwzględnieniem motogodzin silnika: pozostały przebieg skorygowany o {pct}% z powodu intensywnej pracy silnika/LPG.",
    },
}


def t(key: str) -> str:
    """Достаёт перевод для текущего языка."""
    lang = st.session_state.get("lang", "pl")
    return TR[lang].get(key, key)


# ============================================================
# ЗАГРУЗКА БАЗЫ ДАННЫХ С GOOGLE ДИСКА
# ============================================================

@st.cache_resource(show_spinner=False, ttl=DB_CACHE_TTL_SECONDS)
def download_database() -> str:
    """Скачивает hybridassistant.db с Google Диска во временное
    хранилище контейнера. Результат кэшируется, чтобы не скачивать
    файл заново на каждый ререндер страницы — только на холодном
    старте, по истечении TTL или по кнопке "Обновить базу данных"."""
    output_path = LOCAL_DB_CACHE_PATH
    if os.path.exists(output_path):
        try:
            os.remove(output_path)
        except OSError:
            pass

    gdown.download(id=GDRIVE_FILE_ID, output=output_path, quiet=True)

    if not os.path.exists(output_path) or os.path.getsize(output_path) == 0:
        raise RuntimeError(
            "Пустой или отсутствующий файл после скачивания — проверьте доступ по ссылке."
        )
    with open(output_path, "rb") as f:
        header = f.read(16)
    if not header.startswith(b"SQLite format 3"):
        raise RuntimeError(
            "Скачанный файл не является базой SQLite — вероятно, доступ по ссылке не открыт."
        )
    return output_path


# ============================================================
# РАБОТА С БАЗОЙ ДАННЫХ (SQLite)
# ============================================================
# Все функции принимают file_version (mtime скачанного файла), чтобы
# кэш Streamlit корректно инвалидировался при каждом новом скачивании
# файла с одним и тем же путём на диске.

@st.cache_data(show_spinner=False)
def _table_exists(db_path: str, table_name: str, file_version: float) -> bool:
    with sqlite3.connect(db_path) as conn:
        cur = conn.execute(
            "SELECT name FROM sqlite_master WHERE type='table' AND name=?", (table_name,)
        )
        return cur.fetchone() is not None


# Машина эксплуатируется в Польше — используем это как опорный диапазон,
# чтобы автоматически подобрать масштаб координат, а не гадать по одному
# порогу. Разные экспорты Hybrid Assistant хранят GPS по-разному: где-то
# уже готовые градусы (51.844563), где-то целые числа, умноженные на
# 10^6 или 10^7 (форматы Android "E6"/"E7"). Диапазон ниже — с запасом,
# чтобы не отсекать легитимные поездки, например, к границе с Германией
# или Украиной.
_POLAND_LAT_RANGE = (47.0, 56.0)
_POLAND_LON_RANGE = (13.0, 26.0)
_GPS_SCALE_CANDIDATES = (1.0, 1_000.0, 100_000.0, 1_000_000.0, 10_000_000.0)


def _normalize_gps_coordinate(series: pd.Series, expected_min: float, expected_max: float) -> pd.Series:
    """Подбирает делитель из кандидатов (1, 10^3, 10^5, 10^6, 10^7),
    проверяя, какой из них даёт наибольшую долю значений внутри
    ожидаемого диапазона (примерная территория Польши). Если ни один
    вариант не даёт разумного результата, данные не трогаем — лучше
    оставить как есть, чем сломать ещё сильнее."""
    numeric = pd.to_numeric(series, errors="coerce")
    sample = numeric.dropna()
    if sample.empty:
        return numeric

    best_divisor = 1.0
    best_fraction = -1.0
    for divisor in _GPS_SCALE_CANDIDATES:
        scaled = sample / divisor
        fraction_in_range = ((scaled >= expected_min) & (scaled <= expected_max)).mean()
        if fraction_in_range > best_fraction:
            best_fraction = fraction_in_range
            best_divisor = divisor

    if best_fraction <= 0:
        return numeric
    return numeric / best_divisor


def _filter_gps_outliers(df: pd.DataFrame) -> pd.DataFrame:
    """Отбрасывает единичные "сбойные" GPS-точки — типичная ситуация,
    когда модуль ещё не поймал сигнал в начале маршрута и на секунду-две
    отдаёт координаты за тысячи километров от реального положения.
    Порог считается адаптивно через медианное абсолютное отклонение
    (MAD), а не фиксированным числом градусов — иначе короткая поездка
    по городу и длинный загородный перегон требовали бы разных порогов.
    Минимальный порог 0.5° (~50 км) защищает от чрезмерной фильтрации
    на очень компактных поездках, где MAD близок к нулю."""
    if df.empty or "GPS_LAT" not in df.columns or "GPS_LON" not in df.columns:
        return df
    valid = df.dropna(subset=["GPS_LAT", "GPS_LON"])
    if len(valid) < 3:
        return df
    median_lat = valid["GPS_LAT"].median()
    median_lon = valid["GPS_LON"].median()
    mad_lat = (valid["GPS_LAT"] - median_lat).abs().median()
    mad_lon = (valid["GPS_LON"] - median_lon).abs().median()
    lat_threshold = max(mad_lat * 20, 0.5)
    lon_threshold = max(mad_lon * 20, 0.5)
    mask = (
        (df["GPS_LAT"] - median_lat).abs() <= lat_threshold
    ) & ((df["GPS_LON"] - median_lon).abs() <= lon_threshold)
    return df[mask | df["GPS_LAT"].isna() | df["GPS_LON"].isna()]


@st.cache_data(show_spinner=False)
def load_fastlog_full(db_path: str, file_version: float) -> pd.DataFrame:
    """Читает FASTLOG целиком и добавляет производные колонки:
    datetime, режим EV/ICE (по ICE_RPM) и флаг активного механического
    (фрикционного) торможения (по BRK_MCYL_TRQ)."""
    if not _table_exists(db_path, "FASTLOG", file_version):
        return pd.DataFrame()

    with sqlite3.connect(db_path) as conn:
        df = pd.read_sql_query("SELECT * FROM FASTLOG ORDER BY TIMESTAMP", conn)

    if df.empty:
        return df

    df["datetime"] = pd.to_datetime(df["TIMESTAMP"], unit="ms", errors="coerce")
    numeric_cols = [c for c in df.columns if c not in ("TIMESTAMP", "datetime")]
    for c in numeric_cols:
        df[c] = pd.to_numeric(df[c], errors="coerce")

    if "GPS_LAT" in df.columns:
        df["GPS_LAT"] = _normalize_gps_coordinate(df["GPS_LAT"], *_POLAND_LAT_RANGE)
    if "GPS_LON" in df.columns:
        df["GPS_LON"] = _normalize_gps_coordinate(df["GPS_LON"], *_POLAND_LON_RANGE)

    df["mode"] = np.where(df["ICE_RPM"].fillna(0) > 0, "ICE", "EV")
    df["friction_braking_active"] = df["BRK_MCYL_TRQ"].fillna(0) != 0
    return df


@st.cache_data(show_spinner=False)
def load_trips_full(db_path: str, file_version: float) -> pd.DataFrame:
    """Читает TRIPS и TRIPINFO, обогащает их метриками из FASTLOG:
    расход топлива, % EV/ДВС, число механических торможений."""
    if not _table_exists(db_path, "TRIPS", file_version):
        return pd.DataFrame()

    with sqlite3.connect(db_path) as conn:
        trips = pd.read_sql_query(
            "SELECT TSDEB, TSFIN, NBSEC, NKMS FROM TRIPS ORDER BY TSDEB", conn
        )
        tripinfo = (
            pd.read_sql_query(
                "SELECT TIMESTAMP, NUMBRAKES, NUMBADBRAKES, NUMHALFBRAKES, ICE_KWH "
                "FROM TRIPINFO",
                conn,
            )
            if _table_exists(db_path, "TRIPINFO", file_version)
            else pd.DataFrame()
        )

    if trips.empty:
        return pd.DataFrame()

    trips["date"] = pd.to_datetime(trips["TSFIN"], unit="ms", errors="coerce")
    trips["distance"] = pd.to_numeric(trips["NKMS"], errors="coerce")
    trips["duration_min"] = pd.to_numeric(trips["NBSEC"], errors="coerce") / 60.0

    fastlog = load_fastlog_full(db_path, file_version)

    consumption, ev_pct, fuel_ml_list, brake_events, avg_ltft = [], [], [], [], []

    for _, row in trips.iterrows():
        if fastlog.empty:
            consumption.append(None)
            ev_pct.append(None)
            fuel_ml_list.append(None)
            brake_events.append(None)
            avg_ltft.append(None)
            continue

        mask = (fastlog["TIMESTAMP"] >= row["TSDEB"]) & (fastlog["TIMESTAMP"] <= row["TSFIN"])
        trip_log = fastlog.loc[mask]

        if trip_log.empty:
            consumption.append(None)
            ev_pct.append(None)
            fuel_ml_list.append(None)
            brake_events.append(None)
            avg_ltft.append(None)
            continue

        fuel_ml = trip_log["TRIPFUEL"].dropna().max() if "TRIPFUEL" in trip_log else None
        if pd.notna(fuel_ml) and row["distance"] and row["distance"] > 0:
            consumption.append(fuel_ml / 1000.0 / row["distance"] * 100.0)
        else:
            consumption.append(None)
        fuel_ml_list.append(fuel_ml if pd.notna(fuel_ml) else None)

        total_dist = trip_log["TRIP_DIST"].dropna().max() if "TRIP_DIST" in trip_log else None
        ev_dist = trip_log["TRIP_EV_DIST"].dropna().max() if "TRIP_EV_DIST" in trip_log else None
        if pd.notna(total_dist) and total_dist and pd.notna(ev_dist):
            ev_pct.append(min(100.0, max(0.0, ev_dist / total_dist * 100.0)))
        else:
            ev_pct.append(None)

        braking = trip_log["friction_braking_active"].astype(int)
        edges = int((braking.diff() == 1).sum())
        brake_events.append(edges)

        avg_ltft.append(trip_log["LTFT"].dropna().mean() if "LTFT" in trip_log else None)

    trips["consumption"] = consumption
    trips["ev_pct"] = ev_pct
    trips["fuel_ml"] = fuel_ml_list
    trips["brake_events"] = brake_events
    trips["avg_ltft"] = avg_ltft

    trips = trips.sort_values("date").reset_index(drop=True)

    if not tripinfo.empty:
        tripinfo = tripinfo.rename(columns={"TIMESTAMP": "TSFIN"})
        trips = trips.merge(tripinfo, on="TSFIN", how="left")

    return trips


@st.cache_data(show_spinner=False)
def load_temperature_log(db_path: str, file_version: float) -> pd.DataFrame:
    """Читает температуры узлов из FASTLOG, усредняя при большом объёме."""
    fastlog = load_fastlog_full(db_path, file_version)
    if fastlog.empty:
        return pd.DataFrame()

    cols = ["datetime", "ICE_TEMP", "INVERTER_TEMP", "BATTERY_TEMP", "AMBIENT_TEMP"]
    cols = [c for c in cols if c in fastlog.columns]
    df = fastlog[cols].rename(
        columns={
            "ICE_TEMP": "engine_temp",
            "INVERTER_TEMP": "inverter_temp",
            "BATTERY_TEMP": "battery_temp",
            "AMBIENT_TEMP": "ambient_temp",
        }
    ).dropna(subset=["datetime"])

    original_points = len(df)
    resampled = original_points > TEMP_CHART_RESAMPLE_THRESHOLD
    if resampled:
        value_cols = [c for c in df.columns if c != "datetime"]
        df = (
            df.set_index("datetime")[value_cols]
            .resample("1min")
            .mean()
            .dropna(how="all")
            .reset_index()
        )
    df.attrs["original_points"] = original_points
    df.attrs["resampled"] = resampled
    return df


@st.cache_data(show_spinner=False)
def load_cell_delta_series(db_path: str, file_version: float) -> pd.DataFrame:
    """Ищет поблочные напряжения батареи в BATTLOG или HVCHECKCELL и
    считает дельту (max-min) для каждого момента времени."""
    frames = []

    if _table_exists(db_path, "BATTLOG", file_version):
        with sqlite3.connect(db_path) as conn:
            df = pd.read_sql_query("SELECT * FROM BATTLOG", conn)
        if not df.empty:
            cell_cols = [c for c in df.columns if c.startswith("CELL_")]
            if cell_cols:
                for c in cell_cols:
                    df[c] = pd.to_numeric(df[c], errors="coerce")
                df["cell_delta"] = df[cell_cols].max(axis=1) - df[cell_cols].min(axis=1)
                sub = df[["TIMESTAMP", "cell_delta"]].dropna()
                if not sub.empty:
                    sub = sub.copy()
                    sub["source"] = "battlog"
                    frames.append(sub)

    if _table_exists(db_path, "HVCHECKCELL", file_version):
        with sqlite3.connect(db_path) as conn:
            df2 = pd.read_sql_query("SELECT TIMESTAMP, ELEMENT, VALUE FROM HVCHECKCELL", conn)
        if not df2.empty:
            df2["VALUE"] = pd.to_numeric(df2["VALUE"], errors="coerce")
            grouped = (
                df2.groupby("TIMESTAMP")["VALUE"]
                .agg(lambda s: s.max() - s.min())
                .reset_index(name="cell_delta")
            )
            grouped = grouped.dropna()
            if not grouped.empty:
                grouped["source"] = "hvcheck"
                frames.append(grouped)

    if not frames:
        return pd.DataFrame()

    combined = pd.concat(frames, ignore_index=True).sort_values("TIMESTAMP")
    combined["timestamp"] = pd.to_datetime(combined["TIMESTAMP"], unit="ms", errors="coerce")
    return combined.reset_index(drop=True)


@st.cache_data(show_spinner=False)
def load_battlog_probes(db_path: str, file_version: float) -> pd.DataFrame:
    """Читает подробные датчики температуры ВВБ (TB1..TB8) из BATTLOG,
    если этот лог включён и заполнен."""
    if not _table_exists(db_path, "BATTLOG", file_version):
        return pd.DataFrame()
    with sqlite3.connect(db_path) as conn:
        df = pd.read_sql_query("SELECT * FROM BATTLOG ORDER BY TIMESTAMP", conn)
    if df.empty:
        return df
    df["datetime"] = pd.to_datetime(df["TIMESTAMP"], unit="ms", errors="coerce")
    probe_cols = [c for c in df.columns if c.startswith("TB")]
    for c in probe_cols:
        df[c] = pd.to_numeric(df[c], errors="coerce")
    return df


def calculate_soh(delta_v: float):
    """Линейная интерполяция SOH по дельте напряжений элементов под
    нагрузкой. delta_v<=0.02В -> 100%, delta_v>=0.20В -> 0%."""
    if pd.isna(delta_v):
        return None
    if delta_v <= SOH_DELTA_MIN:
        return 100.0
    if delta_v >= SOH_DELTA_MAX:
        return 0.0
    ratio = (delta_v - SOH_DELTA_MIN) / (SOH_DELTA_MAX - SOH_DELTA_MIN)
    return round(100.0 * (1 - ratio), 1)


@st.cache_data(show_spinner=False)
def get_lpg_install_date(db_path: str, file_version: float) -> "datetime | None":
    """Оценивает дату установки ГБО как первый момент, когда одометр
    (ODO) в логах достиг порога LPG_INSTALL_ODO_KM. Если в базе нет
    записей с таким пробегом, возвращает None (год выпуска используется
    как единственный ориентир)."""
    fastlog = load_fastlog_full(db_path, file_version)
    if fastlog.empty or "ODO" not in fastlog.columns:
        return None
    reached = fastlog.loc[fastlog["ODO"] >= LPG_INSTALL_ODO_KM]
    if reached.empty:
        return None
    return reached["datetime"].min()


@st.cache_data(show_spinner=False)
def get_current_mileage(db_path: str, file_version: float) -> "float | None":
    fastlog = load_fastlog_full(db_path, file_version)
    if fastlog.empty or "ODO" not in fastlog.columns:
        return None
    val = fastlog["ODO"].dropna().max()
    return float(val) if pd.notna(val) else None


# ============================================================
# ЗАЩИТА ОТ ПОДБОРА: ПАРОЛЬ ТО + КОД ДОСТУПА К КАРТАМ
# ============================================================

def _expected_secret_hash(secret_key: str, fallback_hash: str) -> str:
    try:
        return st.secrets.get(secret_key, fallback_hash)
    except Exception:
        return fallback_hash


def _verify_secret(value_input: str, secret_key: str, fallback_hash: str) -> bool:
    input_hash = hashlib.sha256(value_input.encode("utf-8")).hexdigest()
    return hmac.compare_digest(input_hash, _expected_secret_hash(secret_key, fallback_hash))


def _lockout_remaining_seconds(namespace: str) -> int:
    lockout_until = st.session_state.get(f"{namespace}_lockout_until", 0.0)
    return max(0, int(lockout_until - time.time()))


def _register_failed_attempt(namespace: str) -> int:
    attempts = st.session_state.get(f"{namespace}_failed_attempts", 0) + 1
    st.session_state[f"{namespace}_failed_attempts"] = attempts
    if attempts >= MAX_PASSWORD_ATTEMPTS:
        st.session_state[f"{namespace}_lockout_until"] = time.time() + LOCKOUT_SECONDS
        st.session_state[f"{namespace}_failed_attempts"] = 0
        return 0
    return MAX_PASSWORD_ATTEMPTS - attempts


def _register_successful_unlock(namespace: str, unlocked_flag: str) -> None:
    st.session_state[unlocked_flag] = True
    st.session_state[f"{namespace}_failed_attempts"] = 0
    st.session_state[f"{namespace}_lockout_until"] = 0.0


@st.dialog("🔒 Код доступа к картам / Kod dostępu do map")
def _map_access_code_dialog():
    remaining = _lockout_remaining_seconds("mapcode")

    if remaining > 0:
        minutes, seconds = divmod(remaining, 60)
        st.error(t("code_locked").format(minutes=minutes, seconds=seconds))
        if st.button(t("map_code_close_button"), use_container_width=True):
            st.session_state["map_dialog_completed"] = True
            st.session_state["map_unlocked"] = False
            st.rerun()
        return

    code_input = st.text_input(t("map_code_label"), type="password", key="map_code_dialog_input")

    col_check, col_close = st.columns(2)
    check_clicked = col_check.button(f"✅ {t('map_code_check_button')}", use_container_width=True)
    close_clicked = col_close.button(f"❌ {t('map_code_close_button')}", use_container_width=True)

    if check_clicked:
        if _verify_secret(code_input, "map_access_code_hash", _FALLBACK_MAP_CODE_HASH):
            _register_successful_unlock("mapcode", "map_unlocked")
            st.session_state["map_dialog_completed"] = True
            st.rerun()
        else:
            attempts_left = _register_failed_attempt("mapcode")
            st.error(t("code_wrong").format(attempts_left=attempts_left))

    if close_clicked:
        st.session_state["map_dialog_completed"] = True
        st.session_state["map_unlocked"] = False
        st.rerun()


def ensure_map_code_dialog_shown() -> None:
    if "map_dialog_completed" not in st.session_state:
        _map_access_code_dialog()


def maps_are_unlocked() -> bool:
    return st.session_state.get("map_unlocked", False)


def render_maps_locked_placeholder() -> None:
    st.info(t("maps_locked_message"))


# ============================================================
# ЖУРНАЛ ТО (maintenance.json)
# ============================================================

def load_maintenance() -> list:
    if not os.path.exists(MAINTENANCE_FILE):
        with open(MAINTENANCE_FILE, "w", encoding="utf-8") as f:
            json.dump([], f, ensure_ascii=False, indent=2)
        return []
    try:
        with open(MAINTENANCE_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    except (json.JSONDecodeError, OSError):
        return []


def save_maintenance_record(record: dict) -> None:
    records = load_maintenance()
    records.append(record)
    with open(MAINTENANCE_FILE, "w", encoding="utf-8") as f:
        json.dump(records, f, ensure_ascii=False, indent=2)


def _find_last_matching_record(records: list, keywords: list):
    """Ищет последнюю (по пробегу) запись ТО, чьё описание содержит
    один из ключевых слов пункта регламента."""
    matches = []
    for rec in records:
        desc = str(rec.get("description", "")).lower()
        if any(kw.lower() in desc for kw in keywords):
            matches.append(rec)
    if not matches:
        return None
    return max(matches, key=lambda r: r.get("mileage", 0))


def compute_maintenance_status(
    db_path: "str | None", file_version: "float | None", records: list
) -> list:
    """Считает статус каждого пункта регламента ТО. Возвращает список
    словарей: key, due_km, due_date, remaining_km, remaining_days, status."""
    current_mileage = None
    if db_path:
        try:
            current_mileage = get_current_mileage(db_path, file_version)
        except Exception:
            current_mileage = None
    if current_mileage is None:
        last_record = max(records, key=lambda r: r.get("mileage", 0)) if records else None
        current_mileage = last_record["mileage"] if last_record else 0.0

    lpg_active = current_mileage >= LPG_INSTALL_ODO_KM

    lpg_install_date = None
    if db_path:
        try:
            lpg_install_date = get_lpg_install_date(db_path, file_version)
        except Exception:
            lpg_install_date = None

    # Эвристика "умного" прогноза для масла: если ДВС в среднем работал
    # с высокой нагрузкой (ICE_LOAD выше медианы по всей истории),
    # немного сокращаем прогнозируемый остаток пробега. Это ОЦЕНКА, а
    # не точный расчёт по моточасам.
    oil_adjustment_pct = 0
    if db_path:
        try:
            fastlog = load_fastlog_full(db_path, file_version)
            if not fastlog.empty and "ICE_LOAD" in fastlog.columns:
                ice_rows = fastlog.loc[fastlog["ICE_RPM"].fillna(0) > 0, "ICE_LOAD"]
                if len(ice_rows) > 50:
                    median_load = ice_rows.median()
                    recent_cutoff = fastlog["datetime"].max() - timedelta(days=30)
                    recent_rows = fastlog.loc[
                        (fastlog["datetime"] >= recent_cutoff) & (fastlog["ICE_RPM"].fillna(0) > 0),
                        "ICE_LOAD",
                    ]
                    if len(recent_rows) > 20 and recent_rows.mean() > median_load * 1.15:
                        oil_adjustment_pct = 15
        except Exception:
            oil_adjustment_pct = 0

    today = date.today()
    results = []

    for item in MAINTENANCE_ITEMS:
        is_lpg_only = item.get("lpg_only", False)
        if is_lpg_only and not lpg_active:
            continue  # пункт появляется только после установки ГБО

        keywords = item["keywords"]
        last_record = _find_last_matching_record(records, keywords)

        interval_km = item.get("lpg_km") if lpg_active and item.get("lpg_km") is not None else item.get("km")
        interval_years = (
            item.get("lpg_years") if lpg_active and item.get("lpg_years") is not None else item.get("years")
        )

        if last_record is None:
            if is_lpg_only:
                baseline_km = LPG_INSTALL_ODO_KM
                baseline_date = lpg_install_date
                if item.get("first_at_km") is not None:
                    due_km = item["first_at_km"]
                else:
                    due_km = baseline_km + (interval_km or 0)
            else:
                baseline_km = 0.0
                baseline_date = date(CAR_MANUFACTURE_YEAR, 1, 1)
                due_km = interval_km
        else:
            baseline_km = last_record.get("mileage", 0.0)
            try:
                baseline_date = datetime.strptime(last_record.get("date", ""), "%Y-%m-%d").date()
            except (ValueError, TypeError):
                baseline_date = None
            due_km = baseline_km + (interval_km or 10 ** 9)

        remaining_km = (due_km - current_mileage) if due_km is not None else None

        if item.get("smart_oil_forecast") and oil_adjustment_pct and remaining_km is not None:
            remaining_km = remaining_km * (1 - oil_adjustment_pct / 100.0)

        due_date = None
        remaining_days = None
        if interval_years is not None and baseline_date is not None:
            try:
                due_date = baseline_date.replace(year=baseline_date.year + interval_years)
            except ValueError:
                due_date = baseline_date + timedelta(days=365 * interval_years)
            remaining_days = (due_date - today).days

        if (remaining_km is not None and remaining_km <= 0) or (
            remaining_days is not None and remaining_days <= 0
        ):
            status = "overdue"
        elif (remaining_km is not None and remaining_km <= MAINTENANCE_SOON_KM) or (
            remaining_days is not None and remaining_days <= MAINTENANCE_SOON_DAYS
        ):
            status = "soon"
        else:
            status = "ok"

        results.append(
            {
                "key": item["key"],
                "remaining_km": remaining_km,
                "remaining_days": remaining_days,
                "status": status,
                "oil_adjustment_pct": oil_adjustment_pct if item.get("smart_oil_forecast") else None,
                "record_found": last_record is not None,
                "is_lpg_only": is_lpg_only,
                "km_since_baseline": (current_mileage - baseline_km) if baseline_km is not None else None,
            }
        )

    return results, current_mileage, lpg_active


# ============================================================
# GEMINI: РАСПОЗНАВАНИЕ ФАКТУР
# ============================================================

def get_gemini_api_key() -> "str | None":
    try:
        return st.secrets.get("GEMINI_API_KEY")
    except Exception:
        return None


def extract_invoice_data(image_bytes: bytes, mime_type: str) -> dict:
    """Отправляет фото фактуры в Gemini 1.5 Flash и просит вернуть
    дату/пробег/описание работ строго в формате JSON."""
    if not GENAI_AVAILABLE:
        return {"error": "google-generativeai не установлен"}
    api_key = get_gemini_api_key()
    if not api_key:
        return {"error": "GEMINI_API_KEY не задан в Secrets"}

    prompt = (
        "Ты — эксперт по распознаванию автодокументов. Проанализируй фото "
        "фактуры/чека на польском или русском языке. Извлеки: Дату "
        "(ГГГГ-ММ-ДД), Пробег (числом в км), и Краткий список сделанных "
        "работ на языке интерфейса. Верни ответ строго в формате JSON с "
        "ключами: 'date', 'odo', 'desc'. Не выводи ничего, кроме чистого JSON."
    )
    try:
        genai.configure(api_key=api_key)
        model = genai.GenerativeModel("gemini-1.5-flash")
        response = model.generate_content(
            [prompt, {"mime_type": mime_type, "data": image_bytes}]
        )
        text = (response.text or "").strip().strip("`")
        if text.lower().startswith("json"):
            text = text[4:].strip()
        data = json.loads(text)
        return data
    except Exception as e:
        return {"error": str(e)}


# ============================================================
# DR. PRIUS: ЧТЕНИЕ ЕЖЕМЕСЯЧНЫХ CSV
# ============================================================
# ВАЖНО: точный формат экспорта Dr. Prius не проверялся на реальном
# файле (в отличие от hybridassistant.db). Ниже — гибкий парсер,
# который ищет колонки по ключевым словам и номеру блока в заголовке.
# Если твои CSV называют колонки иначе — поправь регулярные выражения
# в _RESISTANCE_PATTERNS / _VOLTAGE_PATTERNS / _TEMP_PATTERNS ниже.

_RESISTANCE_PATTERNS = [
    re.compile(r"(?:resistance|opor|opór|impedance|res)[_\s#]*?(\d+)", re.IGNORECASE),
    re.compile(r"^r[_\s]?(\d+)$", re.IGNORECASE),
]
_VOLTAGE_PATTERNS = [
    re.compile(r"(?:voltage|napiecie|napięcie|volt|cell)[_\s#]*?(\d+)", re.IGNORECASE),
    re.compile(r"^[uv][_\s]?(\d+)$", re.IGNORECASE),
]
_TEMP_PATTERNS = [
    re.compile(r"(?:temp|temperatura)[_\s#]*?(\d+)", re.IGNORECASE),
]


def _match_block_columns(columns, patterns) -> dict:
    matches = {}
    for col in columns:
        col_str = str(col).strip()
        for pat in patterns:
            m = pat.search(col_str)
            if m:
                matches[int(m.group(1))] = col
                break
    return matches


def parse_dr_prius_csv(df: pd.DataFrame, month_label: str) -> "dict | None":
    """Возвращает словарь {block_num: {"resistance":.., "voltage":.., "temp":..}}
    усреднённый по всему файлу, либо None, если колонки не распознаны."""
    res_cols = _match_block_columns(df.columns, _RESISTANCE_PATTERNS)
    volt_cols = _match_block_columns(df.columns, _VOLTAGE_PATTERNS)
    temp_cols = _match_block_columns(df.columns, _TEMP_PATTERNS)

    if not res_cols and not volt_cols:
        return None

    blocks = {}
    all_block_nums = sorted(set(res_cols) | set(volt_cols) | set(temp_cols))
    for num in all_block_nums:
        entry = {"month": month_label}
        if num in res_cols:
            entry["resistance"] = pd.to_numeric(df[res_cols[num]], errors="coerce").mean()
        if num in volt_cols:
            entry["voltage"] = pd.to_numeric(df[volt_cols[num]], errors="coerce").mean()
        if num in temp_cols:
            entry["temp"] = pd.to_numeric(df[temp_cols[num]], errors="coerce").mean()
        blocks[num] = entry
    return blocks


def load_dr_prius_files(uploaded_files) -> dict:
    """Парсит все загруженные CSV. Возвращает {month_label: {block: {...}}}."""
    result = {}
    for uf in uploaded_files or []:
        try:
            raw = uf.read()
            df = pd.read_csv(io.BytesIO(raw), sep=None, engine="python")
        except Exception:
            result[uf.name] = None
            continue
        month_label = os.path.splitext(uf.name)[0]
        parsed = parse_dr_prius_csv(df, month_label)
        result[uf.name] = parsed
    return result


# ============================================================
# ИНТЕРФЕЙС — ОБЩЕЕ
# ============================================================

def render_sidebar():
    st.sidebar.header(t("language_label"))
    lang_display = {"ru": "Русский", "pl": "Polski"}
    current_lang = st.session_state.get("lang", "pl")
    choice = st.sidebar.selectbox(
        t("language_label"),
        options=list(lang_display.keys()),
        format_func=lambda code: lang_display[code],
        index=list(lang_display.keys()).index(current_lang),
        label_visibility="collapsed",
    )
    st.session_state["lang"] = choice

    st.sidebar.divider()
    if st.sidebar.button(t("refresh_db_button"), use_container_width=True):
        download_database.clear()
        st.rerun()


def _build_route_map_figure(trip_log: pd.DataFrame) -> go.Figure:
    """Строит карту маршрута, окрашивая сегменты в синий (EV) и чёрный
    (ДВС работает), в стиле My Toyota."""
    fig = go.Figure()
    trip_log = _filter_gps_outliers(trip_log)
    points = trip_log.dropna(subset=["GPS_LAT", "GPS_LON"]).reset_index(drop=True)

    if points.empty:
        return fig

    color_map = {"EV": "#0066FF", "ICE": "#000000"}
    seg_start = 0
    for i in range(1, len(points) + 1):
        if i == len(points) or points.loc[i, "mode"] != points.loc[seg_start, "mode"]:
            seg = points.loc[seg_start : i - 1 + (1 if i < len(points) else 0)]
            mode = points.loc[seg_start, "mode"]
            fig.add_trace(
                go.Scattermap(
                    lat=seg["GPS_LAT"],
                    lon=seg["GPS_LON"],
                    mode="lines",
                    line=dict(width=4, color=color_map.get(mode, "#888888")),
                    name=t("legend_ev") if mode == "EV" else t("legend_ice"),
                    showlegend=False,
                    hoverinfo="skip",
                )
            )
            seg_start = i

    center_lat = points["GPS_LAT"].mean()
    center_lon = points["GPS_LON"].mean()
    fig.update_layout(
        map=dict(style="open-street-map", center=dict(lat=center_lat, lon=center_lon), zoom=12),
        margin=dict(l=0, r=0, t=0, b=0),
        height=450,
        showlegend=False,
    )
    return fig


def _render_single_maintenance_item(item: "dict | None", header_label: str) -> None:
    """Отображает одну карточку регламентного пункта. Работает даже
    если журнал ТО пуст: в этом случае явно пишет, что запись не
    найдена, и всё равно считает остаток от 2021 года/0 км (или от
    точки установки ГБО для пунктов ГБО)."""
    if item is None:
        st.markdown(f"**{header_label}**")
        st.info(t("maint_gbo_not_installed"))
        return

    status_icon = {
        "overdue": t("maintenance_status_overdue"),
        "soon": t("maintenance_status_soon"),
        "ok": t("maintenance_status_ok"),
    }[item["status"]]
    st.markdown(f"**{header_label}** — {status_icon}")

    prefix = "maint_no_record_lpg" if item.get("is_lpg_only") else "maint_no_record_generic"

    if not item.get("record_found", True):
        if item["status"] == "overdue" and item.get("km_since_baseline") is not None:
            st.warning(
                t(f"{prefix}_overdue").format(
                    km=f"{item['km_since_baseline']:,.0f}".replace(",", " ")
                )
            )
        elif item.get("remaining_km") is not None:
            st.info(
                t(f"{prefix}_remaining").format(
                    km=f"{item['remaining_km']:,.0f}".replace(",", " ")
                )
            )
        else:
            st.info(t(f"{prefix}_remaining").format(km="—"))
    else:
        parts = []
        if item.get("remaining_km") is not None:
            parts.append(
                t("maintenance_status_km_left").format(
                    km=f"{item['remaining_km']:,.0f}".replace(",", " ")
                )
            )
        if item.get("remaining_days") is not None:
            parts.append(t("maintenance_status_days_left").format(days=item["remaining_days"]))
        if parts:
            st.caption(" · ".join(parts))

    if item.get("oil_adjustment_pct"):
        st.caption(t("smart_oil_hint").format(pct=item["oil_adjustment_pct"]))


def render_smart_maintenance_cards(status_list: list, lpg_active: bool) -> None:
    """Карточки прогноза по маслу/свечам/антифризу/ГБО в блоке Smart
    Diagnostics — отображаются ВСЕГДА, даже если журнал ТО пуст."""
    lang = st.session_state.get("lang", "pl")
    by_key = {item["key"]: item for item in status_list}
    titles = {
        "oil": {"ru": "Моторное масло", "pl": "Olej silnikowy"},
        "spark_plugs": {"ru": "Свечи зажигания", "pl": "Świece zapłonowe"},
        "coolant": {"ru": "Антифриз SLLC", "pl": "Płyn chłodniczy SLLC"},
        "lpg_filters": {"ru": "ГБО: фильтры", "pl": "LPG: filtry"},
        "lpg_valves": {"ru": "ГБО: клапаны", "pl": "LPG: zawory"},
    }

    cols = st.columns(4)
    with cols[0]:
        _render_single_maintenance_item(by_key.get("oil"), titles["oil"][lang])
    with cols[1]:
        _render_single_maintenance_item(by_key.get("spark_plugs"), titles["spark_plugs"][lang])
    with cols[2]:
        _render_single_maintenance_item(by_key.get("coolant"), titles["coolant"][lang])
    with cols[3]:
        gbo_title = {"ru": "ГБО", "pl": "LPG"}[lang]
        if not lpg_active:
            st.markdown(f"**{gbo_title}**")
            st.info(t("maint_gbo_not_installed"))
        else:
            _render_single_maintenance_item(by_key.get("lpg_filters"), titles["lpg_filters"][lang])
            _render_single_maintenance_item(by_key.get("lpg_valves"), titles["lpg_valves"][lang])


def render_tab1(trips_df, fastlog_df, temp_df, cell_df, db_path, file_version):
    if trips_df.empty:
        st.info(t("no_trip_data"))
        return

    total_trips = len(trips_df)
    total_distance = trips_df["distance"].sum()
    avg_consumption = trips_df["consumption"].mean()
    latest_soh = calculate_soh(cell_df.sort_values("timestamp")["cell_delta"].iloc[-1]) if not cell_df.empty else None

    col1, col2, col3, col4 = st.columns(4)
    col1.metric(t("metric_total_trips"), f"{total_trips}")
    col2.metric(t("metric_total_distance"), f"{total_distance:,.0f}".replace(",", " "))
    col3.metric(
        t("metric_avg_consumption"),
        f"{avg_consumption:.1f}" if pd.notna(avg_consumption) else "—",
    )
    col4.metric(t("metric_soh"), f"{latest_soh:.0f}%" if latest_soh is not None else "—")

    st.divider()

    # --- Карты ---
    if maps_are_unlocked():
        st.subheader(t("map_section_title"))
        trip_options = {
            f"{row['date'].strftime('%Y-%m-%d %H:%M')} — {row['distance']:.1f} км": idx
            for idx, row in trips_df.iterrows()
        }
        if trip_options and not fastlog_df.empty:
            selected_label = st.selectbox(t("map_select_trip"), list(trip_options.keys()))
            sel_idx = trip_options[selected_label]
            sel_row = trips_df.loc[sel_idx]
            mask = (fastlog_df["TIMESTAMP"] >= sel_row["TSDEB"]) & (fastlog_df["TIMESTAMP"] <= sel_row["TSFIN"])
            trip_log = fastlog_df.loc[mask]
            if trip_log[["GPS_LAT", "GPS_LON"]].dropna().empty:
                st.info(t("no_gps_data"))
            else:
                st.plotly_chart(_build_route_map_figure(trip_log), use_container_width=True)

            ev_pct = sel_row.get("ev_pct")
            ice_pct = 100 - ev_pct if pd.notna(ev_pct) else None
            mcol1, mcol2, mcol3, mcol4, mcol5 = st.columns(5)
            mcol1.metric(t("metric_total_distance"), f"{sel_row['distance']:.1f}")
            mcol2.metric(t("metric_ev_pct"), f"{ev_pct:.0f}%" if pd.notna(ev_pct) else "—")
            mcol3.metric(t("metric_ice_pct"), f"{ice_pct:.0f}%" if ice_pct is not None else "—")
            mcol4.metric(t("metric_fuel_ml"), f"{sel_row['fuel_ml']:.0f}" if pd.notna(sel_row.get("fuel_ml")) else "—")
            mcol5.metric(t("metric_brake_events"), f"{int(sel_row['brake_events'])}" if pd.notna(sel_row.get("brake_events")) else "—")
        else:
            st.info(t("no_gps_data"))

        st.subheader(t("map_period_title"))
        period_options = {
            t("map_period_day"): "D",
            t("map_period_week"): "W",
            t("map_period_month"): "M",
            t("map_period_year"): "Y",
        }
        period_label = st.selectbox(t("map_period_label"), list(period_options.keys()), key="period_select")
        freq = period_options[period_label]
        if not fastlog_df.empty:
            latest_ts = fastlog_df["datetime"].max()
            period_start = {
                "D": latest_ts.normalize(),
                "W": latest_ts - timedelta(days=7),
                "M": latest_ts - timedelta(days=30),
                "Y": latest_ts - timedelta(days=365),
            }[freq]
            period_df = fastlog_df[fastlog_df["datetime"] >= period_start]
            period_df = _filter_gps_outliers(period_df)
            period_trips = trips_df[trips_df["date"] >= period_start]
            period_avg_consumption = period_trips["consumption"].mean()

            points = period_df.dropna(subset=["GPS_LAT", "GPS_LON"])
            if not points.empty:
                grid_fig = go.Figure(
                    go.Scattermap(
                        lat=points["GPS_LAT"],
                        lon=points["GPS_LON"],
                        mode="markers",
                        marker=dict(size=4, color="#0057FF", opacity=0.4),
                        hoverinfo="skip",
                    )
                )
                grid_fig.update_layout(
                    map=dict(
                        style="open-street-map",
                        center=dict(lat=points["GPS_LAT"].mean(), lon=points["GPS_LON"].mean()),
                        zoom=10,
                    ),
                    margin=dict(l=0, r=0, t=0, b=0),
                    height=400,
                )
                st.plotly_chart(grid_fig, use_container_width=True)
                if pd.notna(period_avg_consumption):
                    st.markdown(
                        f"### {t('map_period_avg_consumption').format(value=f'{period_avg_consumption:.1f}')}"
                    )
            else:
                st.info(t("no_gps_data"))
    else:
        render_maps_locked_placeholder()

    st.divider()

    # --- Экспертные параметры ---
    st.subheader(t("expert_params_title"))
    ecol1, ecol2 = st.columns(2)
    with ecol1:
        st.markdown(f"**{t('ltft_title')}**")
        ltft_post_lpg = trips_df.loc[trips_df.get("avg_ltft").notna(), "avg_ltft"] if "avg_ltft" in trips_df else pd.Series(dtype=float)
        if not ltft_post_lpg.empty:
            ltft_avg = ltft_post_lpg.mean()
            st.metric("LTFT", f"{ltft_avg:.1f}%")
            if ltft_avg < LTFT_WARNING_MIN or ltft_avg > LTFT_WARNING_MAX:
                st.warning(t("ltft_warning"))
        else:
            st.info(t("not_enough_data"))
    with ecol2:
        st.markdown(f"**{t('hv_safety_title')}**")
        st.info(t("hv_safety_no_data"))

    st.divider()

    # --- Smart Diagnostics ---
    st.subheader(t("smart_diag_title"))
    dcol1, dcol2 = st.columns(2)
    with dcol1:
        st.markdown(f"**{t('soh_forecast_title')}**")
        valid_cell_df = (
            cell_df.dropna(subset=["cell_delta"]).loc[cell_df["cell_delta"] != 0]
            if not cell_df.empty
            else cell_df
        )
        if len(valid_cell_df) >= 5:
            x = (valid_cell_df["timestamp"] - valid_cell_df["timestamp"].min()).dt.total_seconds().to_numpy()
            y = valid_cell_df["cell_delta"].to_numpy()
            slope, intercept = np.polyfit(x, y, 1)
            if slope > 0:
                seconds_to_critical = (SOH_DELTA_MAX - intercept) / slope - x.max()
                if seconds_to_critical > 0:
                    days = int(seconds_to_critical / 86400)
                    forecast_date = (valid_cell_df["timestamp"].max() + timedelta(seconds=seconds_to_critical)).strftime("%Y-%m-%d")
                    st.warning(t("soh_forecast_result").format(days=days, date=forecast_date))
                else:
                    st.warning(t("soh_forecast_result").format(days=0, date=t("not_enough_data")))
            else:
                st.success(t("soh_forecast_stable"))
        else:
            # Дельта напряжений пуста/полностью нулевая (BATTLOG/HVCHECKCELL
            # не заполнены) — вместо общей фразы "недостаточно данных"
            # даём конкретную инструкцию, что нужно сделать пользователю.
            st.info(t("soh_no_data_hint"))
    with dcol2:
        st.markdown(f"**{t('radiator_forecast_title')}**")
        if not temp_df.empty and "ambient_temp" in temp_df.columns and len(temp_df) >= 20:
            df = temp_df.dropna(subset=["ambient_temp", "inverter_temp"]).copy()
            if len(df) >= 20:
                df["diff"] = df["inverter_temp"] - df["ambient_temp"]
                x = (df["datetime"] - df["datetime"].min()).dt.total_seconds().to_numpy()
                y = df["diff"].to_numpy()
                slope, _ = np.polyfit(x, y, 1)
                slope_per_month = slope * 86400 * 30
                if slope_per_month > 0.5:
                    st.warning(t("radiator_forecast_result").format(value=f"{slope_per_month:.1f}"))
                else:
                    st.success(t("radiator_forecast_stable"))
            else:
                st.info(t("not_enough_data"))
        else:
            st.info(t("not_enough_data"))

    st.markdown(f"**{t('maint_forecast_title')}**")
    records = load_maintenance()
    status_list, _current_mileage, lpg_active = compute_maintenance_status(db_path, file_version, records)
    render_smart_maintenance_cards(status_list, lpg_active)


def render_tab2(trips_df, fastlog_df, db_path, file_version):
    if trips_df.empty or fastlog_df.empty:
        st.info(t("no_trip_data"))
        return

    trip_options = {
        f"{row['date'].strftime('%Y-%m-%d %H:%M')} — {row['distance']:.1f} км": idx
        for idx, row in trips_df.iterrows()
    }
    selected_label = st.selectbox(t("logs_select_trip"), list(trip_options.keys()), key="tab2_trip_select")
    sel_idx = trip_options[selected_label]
    sel_row = trips_df.loc[sel_idx]
    mask = (fastlog_df["TIMESTAMP"] >= sel_row["TSDEB"]) & (fastlog_df["TIMESTAMP"] <= sel_row["TSFIN"])
    trip_log = fastlog_df.loc[mask].sort_values("TIMESTAMP")

    if trip_log.empty:
        st.info(t("no_log_data"))
        return

    # 1. Скорость и обороты ДВС
    st.markdown(f"#### {t('logs_chart_speed_rpm')}")
    fig1 = go.Figure()
    fig1.add_trace(go.Scatter(x=trip_log["datetime"], y=trip_log["SPEED_OBD"], name="Speed (км/ч)", line=dict(color="#1f77b4")))
    fig1.add_trace(go.Scatter(x=trip_log["datetime"], y=trip_log["ICE_RPM"], name="ICE RPM", yaxis="y2", line=dict(color="#d62728")))
    fig1.update_layout(
        yaxis=dict(title="км/ч"),
        yaxis2=dict(title="об/мин", overlaying="y", side="right"),
        height=380,
        legend=dict(orientation="h"),
    )
    st.plotly_chart(fig1, use_container_width=True)

    # 2. Напряжение и ток батареи
    st.markdown(f"#### {t('logs_chart_hv')}")
    fig2 = go.Figure()
    fig2.add_trace(go.Scatter(x=trip_log["datetime"], y=trip_log["HV_V"], name="HV_V (В)", line=dict(color="#2ca02c")))
    fig2.add_trace(go.Scatter(x=trip_log["datetime"], y=trip_log["HV_A"], name="HV_A (А)", yaxis="y2", line=dict(color="#ff7f0e")))
    fig2.update_layout(
        yaxis=dict(title="В"),
        yaxis2=dict(title="А", overlaying="y", side="right"),
        height=380,
        legend=dict(orientation="h"),
    )
    st.plotly_chart(fig2, use_container_width=True)

    # 3. Температуры
    st.markdown(f"#### {t('logs_chart_temps')}")
    fig3 = go.Figure()
    fig3.add_trace(go.Scatter(x=trip_log["datetime"], y=trip_log["ICE_TEMP"], name="ДВС", line=dict(color="#d62728")))
    fig3.add_trace(go.Scatter(x=trip_log["datetime"], y=trip_log["INVERTER_TEMP"], name="Инвертор", line=dict(color="#ff7f0e")))
    fig3.add_trace(go.Scatter(x=trip_log["datetime"], y=trip_log["BATTERY_TEMP"], name="ВВБ (среднее)", line=dict(color="#9467bd")))

    battlog = load_battlog_probes(db_path, file_version) if db_path else pd.DataFrame()
    if not battlog.empty:
        probe_mask = (battlog["TIMESTAMP"] >= sel_row["TSDEB"]) & (battlog["TIMESTAMP"] <= sel_row["TSFIN"])
        probe_log = battlog.loc[probe_mask]
        probe_cols = [c for c in ["TB1", "TB2", "TB3"] if c in probe_log.columns and probe_log[c].notna().any()]
        if probe_cols:
            for c in probe_cols:
                fig3.add_trace(go.Scatter(x=probe_log["datetime"], y=probe_log[c], name=f"ВВБ {c}", line=dict(dash="dot")))
            st.caption(t("logs_battlog_note"))
        else:
            st.caption(t("logs_no_battlog"))
    else:
        st.caption(t("logs_no_battlog"))

    fig3.update_layout(yaxis=dict(title="°C"), height=380, legend=dict(orientation="h"))
    st.plotly_chart(fig3, use_container_width=True)

    # 4. MG1/MG2
    st.markdown(f"#### {t('logs_chart_mg')}")
    fig4 = go.Figure()
    fig4.add_trace(go.Scatter(x=trip_log["datetime"], y=trip_log["MG1_TORQUE"], name="MG1 момент (Нм)", line=dict(color="#17becf")))
    fig4.add_trace(go.Scatter(x=trip_log["datetime"], y=trip_log["MG2_TORQUE"], name="MG2 момент (Нм)", line=dict(color="#bcbd22")))
    fig4.add_trace(go.Scatter(x=trip_log["datetime"], y=trip_log["MG1_RPM"], name="MG1 об/мин", yaxis="y2", line=dict(color="#17becf", dash="dot")))
    fig4.add_trace(go.Scatter(x=trip_log["datetime"], y=trip_log["MG2_RPM"], name="MG2 об/мин", yaxis="y2", line=dict(color="#bcbd22", dash="dot")))
    fig4.update_layout(
        yaxis=dict(title="Нм"),
        yaxis2=dict(title="об/мин", overlaying="y", side="right"),
        height=380,
        legend=dict(orientation="h"),
    )
    st.plotly_chart(fig4, use_container_width=True)
    st.caption(t("logs_mg_note"))


def render_tab3():
    st.file_uploader(
        t("drprius_upload_label"),
        type=["csv"],
        accept_multiple_files=True,
        help=t("drprius_upload_help"),
        key="drprius_uploader",
    )
    uploaded_files = st.session_state.get("drprius_uploader")

    if not uploaded_files:
        st.info(t("drprius_no_files"))
        return

    parsed_by_file = load_dr_prius_files(uploaded_files)
    all_blocks_by_month = {}
    for fname, blocks in parsed_by_file.items():
        if blocks is None:
            st.warning(t("drprius_parse_error").format(name=fname))
            continue
        month_label = os.path.splitext(fname)[0]
        all_blocks_by_month[month_label] = blocks

    if not all_blocks_by_month:
        return

    latest_month = list(all_blocks_by_month.keys())[-1]
    latest_blocks = all_blocks_by_month[latest_month]

    block_nums = sorted(latest_blocks.keys())
    resistances = [latest_blocks[b].get("resistance") for b in block_nums]
    voltages = [latest_blocks[b].get("voltage") for b in block_nums]
    temps = [latest_blocks[b].get("temp") for b in block_nums]

    if any(r is not None for r in resistances):
        st.markdown(f"#### {t('drprius_resistance_chart')}")
        fig_r = go.Figure(go.Bar(x=[f"#{b}" for b in block_nums], y=resistances, marker_color="#ff7f0e"))
        fig_r.update_layout(height=350)
        st.plotly_chart(fig_r, use_container_width=True)

    if any(v is not None for v in voltages):
        st.markdown(f"#### {t('drprius_voltage_chart')}")
        fig_v = go.Figure(go.Bar(x=[f"#{b}" for b in block_nums], y=voltages, marker_color="#2ca02c"))
        fig_v.update_layout(height=350)
        st.plotly_chart(fig_v, use_container_width=True)

    st.divider()
    st.markdown(f"#### {t('drprius_wear_title')}")
    months_sorted = list(all_blocks_by_month.keys())
    if len(months_sorted) < 2:
        st.info(t("drprius_need_two_months"))
    else:
        common_blocks = set.intersection(
            *[set(all_blocks_by_month[m].keys()) for m in months_sorted]
        )
        slopes = {}
        for b in common_blocks:
            series = [all_blocks_by_month[m][b].get("resistance") for m in months_sorted]
            if any(v is None or pd.isna(v) for v in series):
                continue
            slope = np.polyfit(range(len(series)), series, 1)[0]
            slopes[b] = slope
        if slopes:
            median_slope = float(np.median(list(slopes.values())))
            fast_blocks = [b for b, s in slopes.items() if s > median_slope * 1.5 and s > 0]
            if fast_blocks:
                st.warning(t("drprius_wear_result").format(blocks=", ".join(f"#{b}" for b in fast_blocks)))
            else:
                st.success(t("drprius_wear_ok"))
        else:
            st.info(t("not_enough_data"))

    st.divider()
    st.markdown(f"#### {t('drprius_temp_spread_title')}")
    if any(v is not None for v in temps):
        valid_temps = [v for v in temps if v is not None and pd.notna(v)]
        if len(valid_temps) >= 2:
            spread = max(valid_temps) - min(valid_temps)
            if spread > 5:
                st.warning(t("drprius_temp_spread_warning").format(value=f"{spread:.1f}"))
            else:
                st.success(t("drprius_temp_spread_ok").format(value=f"{spread:.1f}"))
        else:
            st.info(t("not_enough_data"))
    else:
        st.info(t("not_enough_data"))


def render_tab4(trips_df, temp_df, cell_df):
    st.markdown(f"#### {t('compare_table_title')}")

    dr_files = st.session_state.get("drprius_uploader")
    dr_parsed = load_dr_prius_files(dr_files) if dr_files else {}
    dr_months = {
        os.path.splitext(fname)[0]: blocks
        for fname, blocks in dr_parsed.items()
        if blocks is not None
    }

    if not temp_df.empty:
        temp_df = temp_df.copy()
        temp_df["month"] = temp_df["datetime"].dt.strftime("%Y-%m")
        available_months = sorted(temp_df["month"].dropna().unique())
    else:
        available_months = []

    if not available_months:
        st.info(t("not_enough_data"))
        return

    selected_month = st.selectbox(t("compare_select_month"), available_months, index=len(available_months) - 1)

    ha_peak_temp = temp_df.loc[temp_df["month"] == selected_month, "battery_temp"].max()

    ha_soh = None
    ha_delta = None
    if not cell_df.empty:
        cell_df_m = cell_df.copy()
        cell_df_m["month"] = cell_df_m["timestamp"].dt.strftime("%Y-%m")
        month_cells = cell_df_m.loc[cell_df_m["month"] == selected_month, "cell_delta"]
        if not month_cells.empty:
            ha_delta = month_cells.max()
            ha_soh = calculate_soh(ha_delta)

    dr_blocks = dr_months.get(selected_month)
    dr_voltages = None
    if dr_blocks:
        vals = [b.get("voltage") for b in dr_blocks.values() if b.get("voltage") is not None]
        if vals:
            dr_voltages = (max(vals) - min(vals)) / 1000.0  # мВ -> В

    rows = []

    def _fmt(v, suffix=""):
        return f"{v:.2f}{suffix}" if v is not None and pd.notna(v) else t("compare_na")

    soh_diff_flag = (
        t("compare_diff_high")
        if ha_soh is not None and dr_voltages is not None and abs(ha_soh - 100) > SOH_DIFF_THRESHOLD
        else t("compare_diff_ok")
    )
    rows.append(
        {
            t("compare_col_metric"): t("compare_metric_soh"),
            t("compare_col_ha"): _fmt(ha_soh),
            t("compare_col_drprius"): t("compare_na"),
            t("compare_col_diff_flag"): t("compare_na") if dr_voltages is None else soh_diff_flag,
        }
    )

    delta_diff_flag = (
        t("compare_diff_high")
        if ha_delta is not None and dr_voltages is not None and abs(ha_delta - dr_voltages) > DELTA_V_DIFF_THRESHOLD
        else t("compare_diff_ok")
    )
    rows.append(
        {
            t("compare_col_metric"): t("compare_metric_delta"),
            t("compare_col_ha"): _fmt(ha_delta),
            t("compare_col_drprius"): _fmt(dr_voltages),
            t("compare_col_diff_flag"): t("compare_na") if dr_voltages is None else delta_diff_flag,
        }
    )

    rows.append(
        {
            t("compare_col_metric"): t("compare_metric_peak_temp"),
            t("compare_col_ha"): _fmt(ha_peak_temp),
            t("compare_col_drprius"): t("compare_na"),
            t("compare_col_diff_flag"): t("compare_na"),
        }
    )

    rows.append(
        {
            t("compare_col_metric"): t("compare_metric_ah"),
            t("compare_col_ha"): f"{FACTORY_AH_CAPACITY_REFERENCE:.1f} Ah",
            t("compare_col_drprius"): t("compare_na"),
            t("compare_col_diff_flag"): t("compare_na"),
        }
    )

    df_compare = pd.DataFrame(rows)

    def _highlight(row):
        color = "color: red; font-weight: bold" if row[t("compare_col_diff_flag")] == t("compare_diff_high") else ""
        return [color] * len(row)

    st.dataframe(df_compare.style.apply(_highlight, axis=1), use_container_width=True, hide_index=True)

    st.divider()

    if not cell_df.empty:
        st.markdown(f"#### {t('compare_trend_soh')}")
        soh_series = cell_df["cell_delta"].apply(calculate_soh)
        fig_soh = go.Figure(go.Scatter(x=cell_df["timestamp"], y=soh_series, mode="lines+markers"))
        fig_soh.update_layout(height=300, yaxis_title="SOH %")
        st.plotly_chart(fig_soh, use_container_width=True)

        st.markdown(f"#### {t('compare_trend_delta')}")
        fig_delta = go.Figure(go.Scatter(x=cell_df["timestamp"], y=cell_df["cell_delta"], mode="lines+markers"))
        fig_delta.update_layout(height=300, yaxis_title="Delta, В")
        st.plotly_chart(fig_delta, use_container_width=True)
    else:
        st.info(t("no_cell_data"))

    st.markdown(f"#### {t('compare_trend_seasonal')}")
    if not temp_df.empty:
        years_present = temp_df["datetime"].dt.year.nunique()
        if years_present < 2:
            st.info(t("compare_seasonal_not_enough"))
        else:
            seasonal = temp_df.copy()
            seasonal["year"] = seasonal["datetime"].dt.year
            seasonal["month_num"] = seasonal["datetime"].dt.month
            summer = seasonal[seasonal["month_num"].isin([6, 7, 8])]
            pivot = summer.groupby(["year", "month_num"])["battery_temp"].mean().reset_index()
            fig_season = go.Figure()
            for yr in sorted(pivot["year"].unique()):
                sub = pivot[pivot["year"] == yr]
                fig_season.add_trace(go.Scatter(x=sub["month_num"], y=sub["battery_temp"], name=str(yr), mode="lines+markers"))
            fig_season.update_layout(height=300, xaxis_title="Месяц", yaxis_title="°C ВВБ")
            st.plotly_chart(fig_season, use_container_width=True)
    else:
        st.info(t("not_enough_data"))


def render_tab5(db_path, file_version):
    st.subheader(t("maintenance_title"))

    records = load_maintenance()
    if records:
        df = pd.DataFrame(records)
        df_display = df.rename(
            columns={"date": t("col_date"), "mileage": t("col_mileage"), "description": t("col_description")}
        )
        st.dataframe(df_display, use_container_width=True, hide_index=True)
    else:
        st.info(t("maintenance_empty"))

    st.divider()
    st.subheader(t("maintenance_status_title"))

    status_list, current_mileage, lpg_active = compute_maintenance_status(db_path, file_version, records)
    st.caption(t("maintenance_current_mileage").format(value=f"{current_mileage:,.0f}".replace(",", " ")))
    if lpg_active:
        st.caption(t("lpg_installed_note"))

    item_labels = {
        "oil": {"ru": "Моторное масло 0W-16", "pl": "Olej silnikowy 0W-16"},
        "spark_plugs": {"ru": "Свечи зажигания", "pl": "Świece zapłonowe"},
        "brake_fluid": {"ru": "Тормозная жидкость", "pl": "Płyn hamulcowy"},
        "coolant": {"ru": "Антифриз SLLC", "pl": "Płyn chłodniczy SLLC"},
        "air_filter": {"ru": "Воздушный фильтр", "pl": "Filtr powietrza"},
        "lpg_filters": {"ru": "Фильтры ГБО", "pl": "Filtry LPG"},
        "lpg_valves": {"ru": "Зазоры клапанов (ГБО)", "pl": "Luzy zaworowe (LPG)"},
    }
    status_icon = {
        "overdue": t("maintenance_status_overdue"),
        "soon": t("maintenance_status_soon"),
        "ok": t("maintenance_status_ok"),
    }

    lang = st.session_state.get("lang", "pl")
    for item in status_list:
        label = item_labels.get(item["key"], {}).get(lang, item["key"])
        cols = st.columns([3, 2, 2, 2])
        cols[0].markdown(f"**{label}**")
        cols[1].markdown(status_icon[item["status"]])
        if item["remaining_km"] is not None:
            cols[2].markdown(t("maintenance_status_km_left").format(km=f"{item['remaining_km']:,.0f}".replace(",", " ")))
        if item["remaining_days"] is not None:
            cols[3].markdown(t("maintenance_status_days_left").format(days=item["remaining_days"]))
        if item.get("oil_adjustment_pct"):
            st.caption(t("smart_oil_hint").format(pct=item["oil_adjustment_pct"]))

    st.divider()
    st.subheader(t("add_record_header"))

    # --- Распознавание фактуры через Gemini ---
    if GENAI_AVAILABLE and get_gemini_api_key():
        uploaded_invoice = st.file_uploader(t("invoice_upload_label"), type=["jpg", "jpeg", "png"], key="invoice_uploader")
        if uploaded_invoice is not None and st.session_state.get("last_invoice_name") != uploaded_invoice.name:
            with st.spinner(t("invoice_processing")):
                data = extract_invoice_data(uploaded_invoice.getvalue(), uploaded_invoice.type or "image/jpeg")
            st.session_state["last_invoice_name"] = uploaded_invoice.name
            if "error" in data:
                st.error(t("invoice_error").format(error=data["error"]))
            else:
                st.session_state["invoice_prefill_date"] = data.get("date")
                st.session_state["invoice_prefill_odo"] = data.get("odo")
                st.session_state["invoice_prefill_desc"] = data.get("desc")
                st.success(t("invoice_success"))
    else:
        st.caption(t("invoice_unavailable"))

    remaining = _lockout_remaining_seconds("maintenance")
    if remaining > 0:
        minutes, seconds = divmod(remaining, 60)
        st.error(t("password_locked").format(minutes=minutes, seconds=seconds))
        return

    if not st.session_state.get("maintenance_unlocked", False):
        password_input = st.text_input(t("password_label"), type="password", key="maintenance_password_input")
        if password_input == "":
            st.info(t("password_needed"))
        elif _verify_secret(password_input, "maintenance_password_hash", _FALLBACK_PASSWORD_HASH):
            _register_successful_unlock("maintenance", "maintenance_unlocked")
            st.rerun()
        else:
            attempts_left = _register_failed_attempt("maintenance")
            st.error(t("password_wrong").format(attempts_left=attempts_left))
        return

    st.success(t("password_unlocked"))
    if st.button(t("lock_again_button")):
        st.session_state["maintenance_unlocked"] = False
        st.rerun()

    prefill_date = st.session_state.get("invoice_prefill_date")
    try:
        prefill_date_value = datetime.strptime(prefill_date, "%Y-%m-%d").date() if prefill_date else date.today()
    except (ValueError, TypeError):
        prefill_date_value = date.today()
    prefill_odo = st.session_state.get("invoice_prefill_odo") or 0
    prefill_desc = st.session_state.get("invoice_prefill_desc") or ""

    with st.form("maintenance_form", clear_on_submit=True):
        record_date = st.date_input(t("form_date"), value=prefill_date_value)
        record_mileage = st.number_input(t("form_mileage"), min_value=0, step=100, value=int(prefill_odo) if prefill_odo else 0)
        record_description = st.text_area(t("form_description"), value=prefill_desc)
        submitted = st.form_submit_button(t("save_button"))

        if submitted:
            if record_description.strip() == "":
                st.warning(t("save_fill_all"))
            else:
                save_maintenance_record(
                    {
                        "date": record_date.strftime("%Y-%m-%d"),
                        "mileage": int(record_mileage),
                        "description": record_description.strip(),
                    }
                )
                st.session_state.pop("invoice_prefill_date", None)
                st.session_state.pop("invoice_prefill_odo", None)
                st.session_state.pop("invoice_prefill_desc", None)
                st.success(t("save_success"))
                st.rerun()


def main():
    if "lang" not in st.session_state:
        st.session_state["lang"] = "pl"

    st.set_page_config(page_title=t("page_title"), page_icon="🚗", layout="wide")

    ensure_map_code_dialog_shown()

    render_sidebar()

    st.title(t("app_title"))

    tab1, tab2, tab3, tab4, tab5 = st.tabs(
        [t("tab1"), t("tab2"), t("tab3"), t("tab4"), t("tab5")]
    )

    trips_df = pd.DataFrame()
    fastlog_df = pd.DataFrame()
    temp_df = pd.DataFrame()
    cell_df = pd.DataFrame()
    db_ok = True
    db_missing = False
    db_error_message = None
    db_path = None
    file_version = None

    with st.spinner(t("downloading_db")):
        try:
            db_path = download_database()
        except RuntimeError:
            db_ok = False
            db_missing = True
        except Exception as e:
            db_ok = False
            db_error_message = str(e)

    if db_ok and db_path:
        file_version = os.path.getmtime(db_path)
        st.sidebar.caption(
            t("db_last_loaded").format(
                timestamp=pd.to_datetime(file_version, unit="s").strftime("%Y-%m-%d %H:%M:%S")
            )
        )
        try:
            trips_df = load_trips_full(db_path, file_version)
            fastlog_df = load_fastlog_full(db_path, file_version)
            temp_df = load_temperature_log(db_path, file_version)
            cell_df = load_cell_delta_series(db_path, file_version)
        except sqlite3.Error as e:
            db_ok = False
            db_error_message = str(e)
        except Exception as e:
            db_ok = False
            db_error_message = str(e)

    with tab1:
        if not db_ok:
            st.warning(t("db_missing")) if db_missing else st.error(t("db_error").format(error=db_error_message))
        else:
            render_tab1(trips_df, fastlog_df, temp_df, cell_df, db_path, file_version)

    with tab2:
        if not db_ok:
            st.warning(t("db_missing")) if db_missing else st.error(t("db_error").format(error=db_error_message))
        else:
            render_tab2(trips_df, fastlog_df, db_path, file_version)

    with tab3:
        render_tab3()

    with tab4:
        if not db_ok:
            st.warning(t("db_missing")) if db_missing else st.error(t("db_error").format(error=db_error_message))
        else:
            render_tab4(trips_df, temp_df, cell_df)

    with tab5:
        render_tab5(db_path, file_version)


if __name__ == "__main__":
    main()
