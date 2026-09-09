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

import base64
import hashlib
import hmac
import io
import json
import math
import os
import re
import shutil
import sqlite3
import tempfile
import threading
import time
import traceback
from datetime import date, datetime, timedelta

import gdown
import numpy as np
import pandas as pd
import plotly.graph_objects as go
import streamlit as st
from bs4 import BeautifulSoup
import pypdf
import requests

try:
    import google.generativeai as genai

    GENAI_AVAILABLE = True
except ImportError:
    GENAI_AVAILABLE = False


# ============================================================
# КОНФИГУРАЦИЯ
# ============================================================

# --- Источник основной базы данных: Google Диск ---
GDRIVE_FOLDER_ID = "1euBXP38wifqzXUSv0RkySvbtmoUQ_HTL"
LOCAL_DB_FOLDER_PATH = "/tmp/hybridassistant_folder"
DB_REFRESH_COOLDOWN_SECONDS = 40  # скачивание занимает ~30 сек — не даём кликать чаще

# Скачивание занимает ~30 секунд. Если пользователь нажмёт "Обновить базу
# данных" ещё раз, не дождавшись первого запроса, второй вызов раньше
# начинал удалять и перезаписывать ТУ ЖЕ папку, пока первый ещё писал в
# неё файлы — отсюда зависания и битые/неполные скачивания. Блокировка
# ниже гарантирует, что параллельные вызовы выполняются строго по одному.
_download_lock = threading.Lock()
DB_CACHE_TTL_SECONDS = 8 * 60 * 60  # автообновление 3 раза в сутки (каждые 8 часов)

MAINTENANCE_FILE = "maintenance.json"
DR_PRIUS_UPLOAD_DIR = "/tmp/dr_prius_logs"

# Hybrid Assistant хранит все TIMESTAMP/TSDEB/TSFIN в миллисекундах
# UTC-времени. Машина и водитель — в Польше, поэтому для отображения
# конвертируем в локальное время Europe/Warsaw (с учётом перехода на
# летнее время), иначе часы на графиках/в списке поездок не совпадают
# с реальными часами на телефоне.
LOCAL_TIMEZONE = "Europe/Warsaw"


def _ms_to_local_datetime(ms_series: pd.Series) -> pd.Series:
    """Мс Unix-времени (UTC) -> наивный локальный datetime (Europe/Warsaw)."""
    dt_utc = pd.to_datetime(ms_series, unit="ms", errors="coerce", utc=True)
    return dt_utc.dt.tz_convert(LOCAL_TIMEZONE).dt.tz_localize(None)

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
        # "моторн"/"silnikow" — падежестойкие основы слов "моторное"/
        # "silnikowy" (а не полное слово "масло", которое не совпадает с
        # "масла" в родительном падеже — это и было причиной бага).
        # Специально НЕ используем голое "масл", чтобы запись о замене
        # масла в коробке e-CVT не засчиталась как замена моторного масла.
        "keywords": ["моторн", "silnikow", "engine oil", "0w-16", "0w16"],
    },
    {
        "key": "spark_plugs",
        "km": 90_000, "years": None,
        "lpg_km": 45_000, "lpg_years": None,
        "keywords": ["свеч", "świec", "swiec", "plug"],
    },
    {
        # Трансмиссионное масло e-CVT (Toyota ATF WS). Регламент не
        # зависит от ГБО, поэтому lpg_km/lpg_years совпадают с km/years.
        "key": "cvt_oil",
        "km": 90_000, "years": 5,
        "lpg_km": 90_000, "lpg_years": 5,
        "custom_no_record_message_key": "cvt_oil_no_record_message",
        "keywords": ["масло в коробке", "e-cvt", "atf ws", "atf", "olej w skrzyni", "коробк"],
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
        "map_style_label": "Стиль карты",
        "map_stadia_key_found": "🔑 Ключ Stadia найден в Secrets.",
        "map_stadia_key_missing": "🔑 Ключ Stadia не найден в Secrets. Проверьте имя параметра — оно должно быть ровно stadia_api_key.",
        "map_stadia_troubleshoot": "Если подложка не загружается даже с ключом — в личном кабинете Stadia добавьте домен приложения (*.streamlit.app) в список разрешённых для вашего проекта: браузерные запросы Stadia проверяет по домену.",
        "db_autorefresh_note": "База обновляется автоматически 3 раза в сутки (каждые 8 часов). Кнопка ниже — если нужно прямо сейчас.",
        "db_last_loaded": "База данных загружена: {timestamp}",
        "downloading_db": "Загрузка базы данных с Google Диска (обычно занимает 20-30 секунд, не закрывайте страницу)…",
        "refresh_in_progress_warning": "⏳ Обновление уже запущено — подождите примерно 30 секунд, повторное нажатие сейчас только всё замедлит.",
        "db_missing": "⚠️ Не удалось скачать базу данных с Google Диска. Проверьте, что доступ к файлу открыт по ссылке (\"Все, у кого есть ссылка\" → \"Читатель\").",
        "db_error": "⚠️ Не удалось прочитать базу данных: {error}",
        "no_trip_data": "Нет данных о поездках для отображения.",
        "no_log_data": "Нет данных телеметрии (логов) для отображения.",
        "no_cell_data": "Нет данных о напряжении элементов батареи. Включите HighSpeedLogging в настройках Hybrid Assistant или проведите процедуру HV Check.",
        "no_gps_data": "Нет GPS-данных для этой поездки/периода.",
        "gps_signal_lost_warning": "⚠️ GPS-модуль частично потерял сигнал во время этой поездки (по данным OBD машина ехала, но координаты не обновлялись) — на карте показан только участок с надёжным сигналом. Это ограничение исходных данных, а не ошибка приложения.",
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
        "map_section_title": "🗺️ Карта поездки",
        "map_select_trip": "Выберите поездку",
        "map_param_label": "Показатель на карте",
        "map_param_mode": "Режим (EV / ДВС)",
        "map_param_braking": "Торможение",
        "map_param_speed": "Скорость",
        "map_param_soc": "Заряд батареи (SOC)",
        "map_period_title": "🗺️ Карта за период",
        "map_period_label": "Период",
        "map_period_day": "День",
        "map_period_week": "Неделя",
        "map_period_month": "Месяц",
        "map_period_year": "Год",
        "map_period_avg_consumption": "Средний расход за период: {value} л/100км",
        "fuel_forecast_badge": "🔮 (прогноз)",
        "unit_kmh": "км/ч",
        "unit_l100km": "л/100км",
        "unit_l": "л",
        "weather_title": "🌤️ Метеорологические условия поездки",
        "weather_loading": "Запрашиваю историческую погоду…",
        "weather_no_gps": "Нет достоверных GPS-координат для этой поездки — без них невозможно узнать, какая была погода именно в том месте.",
        "weather_no_time": "Не удалось определить время старта поездки.",
        "weather_unavailable": "⚠️ Не удалось получить данные о погоде (сервис Open-Meteo недоступен или для этой даты нет данных).",
        "weather_air_temp": "Температура воздуха",
        "weather_condition": "Осадки",
        "weather_wind": "Ветер (откуда)",
        "weather_road_temp": "Температура асфальта",
        "weather_road_temp_help": "Расчётная оценка, а не измерение: асфальт нагревается солнцем сильнее воздуха и остывает ночью ниже него. Реальное значение зависит ещё от цвета и возраста покрытия, ветра и влажности.",
        "weather_precip": "Осадки за час: {mm} мм.",
        "weather_cold_warning": "❄️ Повышенный расход из-за прогрева ДВС и салона: при температуре ниже +5 °C гибрид дольше держит двигатель включённым для прогрева, а батарея отдаёт меньше мощности.",
        "weather_headwind": "🌬️ Встречный ветер ~{speed} км/ч — аэродинамическое сопротивление выше примерно на {pct}%. Это прирост именно аэродинамической составляющей, а не всего расхода топлива.",
        "weather_headwind_slow": "🌬️ Встречный ветер ~{speed} км/ч. На такой средней скорости аэродинамика почти не влияет на расход.",
        "weather_tailwind": "🍃 Попутный ветер ~{speed} км/ч — аэродинамическое сопротивление ниже обычного.",
        "weather_source_note": "Источник погоды: Open-Meteo (историческая реанализация) по координатам старта поездки.",
        "elevation_profile_title": "⛰️ Профиль высот (рельеф маршрута)",
        "elevation_no_data": "Нет данных о высоте для этой поездки.",
        "elevation_flat": "Высота на всём маршруте не менялась — либо участок действительно ровный, либо GPS писал высоту с шагом в целые метры.",
        "unit_price_per_l": "zł/л",
        "unit_rpm": "об/мин",
        "unit_nm": "Нм",
        "fuel_forecast_help": "Оценка ЭБУ по длительности впрыска (данные Hybrid Assistant) — не прямое измерение топлива.",
        "fuel_real_badge": "🧾 (реально)",
        "fuel_real_badge_note": "🧾 Реальный расход по чекам АЗС (отчёт Fuelio), в отличие от прогноза ЭБУ — это подтверждённые литры и стоимость.",
        "fuel_type_lpg": "ГБО (газ)",
        "fuel_type_petrol": "Бензин",
        "map_day_refuel_note": "⛽ В этот день заправлено: {fuel} — {liters} л по {price} zł/л.",
        "fuel_log_title": "⛽ Заправки (реальные данные, отчёт Fuelio)",
        "fuel_log_no_data": "Нет данных о заправках — загрузите отчёт Fuelio (PDF) в папку на Google Диске рядом с базой данных.",
        "fuel_last_refuel_date": "Последняя заправка",
        "fuel_liters": "Залито",
        "fuel_price": "Цена",
        "fuel_days_ago": "{days} дн. назад",
        "fuel_avg_consumption": "Средний расход",
        "fuel_petrol_no_avg_note": "Нет данных — неизвестно, сколько бензина было в баке до начала наблюдений, а расход сильно зависит от доли использования бензина (в основном пуск/прогрев), так что усреднение по общему пробегу вводит в заблуждение.",
        "fuel_trend_title": "📈 История заправок",
        "fuel_metric_label": "Показатель",
        "fuel_metric_days": "Дней с прошлой заправки",
        "fuel_metric_liters": "Сколько залито, л",
        "fuel_metric_cost": "Стоимость, zł",
        "fuel_period_label": "Период",
        "fuel_trend_health_title": "⛽ Тренд реального расхода LPG (по чекам)",
        "fuel_lpg_trend_warn": "⚠️ Реальный расход LPG растёт (~{value} л/100км в мес.) — стоит проверить ГБО (форсунки, редуктор, смесь).",
        "fuel_lpg_trend_ok": "Реальный расход LPG стабилен или снижается — признаков проблем с ГБО не выявлено.",
        "fuel_crosscheck_title": "Сверка: прогноз ЭБУ vs реальный расход, по месяцам",
        "fuel_crosscheck_note": "Если разрыв между прогнозом и реальным расходом растёт со временем — возможен уход калибровки форсунок/датчиков от реальности, стоит присмотреться к LTFT на вкладке \"Аналитика\".",
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
        "cvt_oil_no_record_message": "Замена масла в коробке e-CVT не зафиксирована. Регламент Toyota для тяжёлых условий составляет 90 000 км или 5 лет. Рекомендуется превентивно обновить жидкость Toyota ATF WS для защиты электромоторов MG1/MG2 от перегрева.",
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
        # --- Полный отчёт по поездке (как в Hybrid Assistant) ---
        "rep_summary_title": "📋 Сводка по поездке",
        "rep_trip": "Поездка",
        "rep_distance": "Расстояние",
        "rep_time": "Время",
        "rep_moving": "В движении",
        "rep_total": "Всего",
        "rep_ev": "EV",
        "rep_speed_avg": "Средняя скорость",
        "rep_speed_max": "Макс. скорость",
        "rep_speed_ev_avg": "Средняя скорость на EV",
        "rep_soc_start_end": "SOC начало → конец",
        "rep_ambient_avg": "Ср. темп. воздуха",
        "rep_fuel_consumption": "Расход топлива",
        "rep_ev_time_note": "Точная классификация EV/ДВС у Hybrid Assistant опирается на внутренний индикатор гибридной системы (HSI) — наш расчёт по ICE_RPM=0 может немного отличаться от их значений.",
        "rep_soc_title": "🔋 Статистика заряда (SOC)",
        "rep_soc_note": "ℹ️ Разбивка \"откуда взялся заряд\" (рекуперация/накат/ДВС) — фирменный внутренний расчёт Hybrid Assistant, у нас нет доступа к точной формуле, поэтому не воспроизводится.",
        "rep_hv_title": "⚡ Высоковольтная батарея (ВВБ)",
        "rep_hv_levels": "Уровни",
        "rep_current": "Ток",
        "rep_voltage": "Напряжение",
        "rep_hv_power": "Мощность и лимиты",
        "rep_power": "Мощность",
        "rep_hv_from_batt": "Отдано батареей",
        "rep_hv_to_batt": "Заряжено в батарею",
        "rep_hv_balance": "Баланс энергии",
        "rep_ccl_dcl_note": "CCL/DCL — лимиты заряда/разряда батареи (меняются с уровнем заряда и температурой).",
        "rep_temp_title": "🌡️ Температуры",
        "rep_temp_ambient": "Воздух",
        "rep_temp_room": "В салоне/корпусе",
        "rep_temp_coolant": "Охлаждающая жидкость ДВС",
        "rep_temp_inverter": "Инвертор",
        "rep_temp_mg": "Мотор-генератор",
        "rep_hv_probes": "Датчики ВВБ",
        "rep_elevation_title": "⛰️ Высота над уровнем моря",
        "rep_altitude": "Высота, м",
        "rep_upward": "Подъём",
        "rep_downward": "Спуск",
        "rep_elevation_note": "Подъём/спуск считаются по колонке GPS-высоты в базе — она грубее, чем внутренний расчёт Hybrid Assistant, поэтому суммарный набор высоты может быть занижен.",
        "rep_energy_title": "🔥 Энергия от ДВС",
        "rep_energy_from_ice": "Энергия от ДВС",
        "rep_energy_per_100km": "Расход энергии",
        "rep_engine_title": "🚗 Двигатель",
        "rep_load": "Нагрузка",
        "rep_ignitions_total": "Запусков ДВС",
        "rep_ignitions_inefficient": "Неэффективных (<5 сек)",
        "rep_ignitions_note": "Неэффективным считается запуск ДВС короче 5 секунд — частые короткие пуски увеличивают износ.",
        "rep_engine_state": "Состояние ДВС",
        "rep_ice_running": "Работает (с топливом)",
        "rep_ice_spinning": "Крутится без топлива",
        "rep_ice_off": "Выключен",
        "rep_engine_state_note": "\"Крутится без топлива\" — накат/торможение двигателем без впрыска (приблизительная оценка по FUELFLOWH).",
        "rep_psd_title": "⚙️ Планетарный редуктор (PSD): ДВС и MG1/MG2",
        "rep_ice_torque": "Момент ДВС (расч.)",
        "rep_psd_note": "Момент ДВС рассчитан из мощности и оборотов (М = P / ω) — это оценка, не прямое измерение.",
        "rep_trims_title": "🎛️ Топливные коррекции",
        "rep_effective": "Суммарная",
        "rep_bsfc_title": "⛽ Удельный расход топлива (BSFC)",
        "rep_bsfc_avg": "Среднее",
        "rep_bsfc_std": "Ст. отклонение",
        "rep_bsfc_note": "BSFC (г/кВт·ч) — сколько топлива тратится на каждый кВт·ч выработанной ДВС мощности; чем меньше, тем эффективнее работает двигатель в данной точке. Считается только по ненулевым показаниям.",
        "rep_braking_title": "🛑 Торможение",
        "rep_brakings_total": "Всего торможений",
        "rep_brakings_good": "Только рекуперация",
        "rep_brakings_bad": "Только механическое",
        "rep_brakings_mixed": "Смешанные",
        "rep_braking_efficiency": "Эффективность торможений",
        "rep_energy_recovered": "Энергия рекуперации",
        "rep_braking_note": "Эффективность = доля торможений, обошедшихся полностью рекуперацией, без задействования колодок.",
        "rep_driver_eval_title": "👤 Оценка стиля вождения",
        "rep_accel_nervousness": "\"Нервозность\" педали газа",
        "rep_driver_eval_note": "Нервозность педали — среднее изменение положения педали газа между замерами; чем выше, тем резче стиль езды.",
        "rep_glide_title": "🛞 Индекс наката (Glide)",
        "rep_glide_avg": "Средний индекс",
        "rep_glide_max": "Макс. индекс",
        "rep_glide_note": "Индекс наката показывает, насколько эффективно используется накат без тяги ДВС/электромотора. Точная методика Hybrid Assistant не раскрыта, здесь — по сырому показателю GLIDEINDEX из лога.",
        "rep_maps_title": "🗺️ Карта поездки",
        "rep_charts_title": "📈 Графики по времени",
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
        "ha_reports_title": "📄 Тренды из HTML-отчётов Hybrid Assistant",
        "ha_reports_explainer": "Почти все показатели уже честно считаются из самой базы данных (см. вкладку \"Детальные логи\") и совпадают с отчётом почти до знака. Но несколько фирменных расчётов Hybrid Assistant — разбивка заряда батареи по источникам, индекс наката (Glide) и оценка стиля вождения — хранятся только в готовом виде в HTML-отчёте. Загрузи несколько отчётов за разное время, чтобы отслеживать тренды по ним.",
        "ha_reports_upload_label": "Загрузите HTML-отчёты Hybrid Assistant (можно сразу несколько)",
        "ha_reports_limit_caption": "За один раз можно загрузить до 100 файлов, каждый до 200 МБ — это ограничения самого Streamlit по умолчанию.",
        "ha_reports_loaded_count": "Распознано отчётов: {n}",
        "ha_reports_drive_found": "✅ Автоматически загружено с Google Диска: {n} отчёт(ов). Отдельно загружать их не нужно.",
        "ha_reports_drive_none": "ℹ️ В папке на Google Диске HTML-отчётов не найдено. Положите их туда рядом с базой данных — тогда они будут подхватываться автоматически при каждом обновлении. Либо загрузите вручную ниже.",
        "ha_reports_drive_list": "Показать список отчётов с Google Диска",
        "ha_reports_upload_help": "Отчёт создаётся в приложении Hybrid Assistant: откройте поездку и выберите экспорт в HTML.",
        "ha_reports_none_at_all": "Отчётов пока нет — ни на Google Диске, ни загруженных вручную.",
        "ha_reports_upload_success": "✅ Успешно распознано отчётов: {n}",
        "ha_reports_upload_failed": "❌ Не удалось распознать «{name}»: {reason}",
        "ha_reports_fail_no_time": "в файле не найдено время поездки — похоже, это не отчёт Hybrid Assistant",
        "ha_reports_details": "Показать, какие отчёты распознаны",
        "ha_reports_col_file": "Файл",
        "ha_reports_col_source": "Источник",
        "ha_reports_source_drive": "Google Диск",
        "ha_reports_source_manual": "Загружен вручную",
        "ha_maps_title": "🗺️ Карты из отчёта Hybrid Assistant",
        "ha_trip_extras_title": "📄 Данные из HTML-отчёта для этой поездки",
        "ha_maps_source_note": "📄 Карта построена из HTML-отчёта Hybrid Assistant (его собственный расчёт категорий).",
        "ha_trip_no_report": "Для этой поездки не загружен HTML-отчёт. Загрузите отчёты на вкладке «Сравнение и тренды» — приложение само сопоставит их с поездками по времени и покажет здесь фирменные показатели и карты Hybrid Assistant.",
        "ha_trip_report_found": "Найден отчёт для этой поездки: {name}",
        "ha_maps_explainer": "Эти карты рисует сам Hybrid Assistant по своим внутренним алгоритмам. Карты «Мгновенный расход», «BSFC» и «Оценка наката» невозможно построить из базы данных — там нет ни готовых категорий, ни открытой формулы их расчёта.",
        "ha_maps_select_report": "Отчёт",
        "ha_maps_select_map": "Карта",
        "ha_maps_no_maps": "В этом отчёте не найдено карт (возможно, у поездки не было GPS-данных).",
        "ha_maps_gps_warning": "⚠️ В этом отчёте GPS-точки укладываются в пятно менее 100 м, хотя поездка была длиннее — значит, GPS-модуль терял сигнал во время записи. Цветовые категории при этом достоверны, а вот географию такой карты читать бессмысленно.",
        "device_label": "Вид интерфейса",
        "device_auto": "Автоматически",
        "device_mobile": "Телефон",
        "device_desktop": "Компьютер",
        "device_current": "Определено: {device}",
        "ha_reports_parse_error": "⚠️ Не удалось распознать ни один из загруженных файлов как отчёт Hybrid Assistant.",
        "ha_reports_hvcheck_note": "ℹ️ Если в отчёте есть результаты теста HV Check (поблочные напряжения элементов), сообщи мне — пришли пример такого отчёта, и я добавлю автоматическое извлечение этих данных для расчёта SOH, когда в самой базе HV Check пуст.",
        "ha_trend_soc_title": "🔋 Откуда берётся заряд батареи",
        "ha_soc_brakings": "От рекуперации при торможении",
        "ha_soc_coasting": "От наката",
        "ha_soc_ice": "От ДВС",
        "ha_trend_soc_note": "Доля заряда, полученного от каждого источника, в % от общего прироста SOC за поездку.",
        "ha_trend_brakings_warn": "⚠️ Доля заряда от рекуперативного торможения снижается (~{value} п.п./мес.) — стоит проверить тормозную систему и работу рекуперации.",
        "ha_trend_brakings_ok": "Доля заряда от рекуперации стабильна или растёт — признаков износа не выявлено.",
        "ha_trend_glide_title": "🛞 Индекс наката (Glide) по отчётам",
        "ha_glide_score": "Glide score",
        "ha_trend_glide_note": "Индекс наката из официального расчёта Hybrid Assistant (точная методика не раскрыта производителем).",
        "ha_trend_glide_warn": "⚠️ Индекс наката снижается (~{value}/мес.) — возможен рост внутреннего сопротивления трансмиссии/PSD, стоит обратить внимание.",
        "ha_trend_glide_ok": "Индекс наката стабилен или растёт — признаков износа трансмиссии не выявлено.",
        "ha_trend_driver_title": "👤 Стиль вождения по отчётам",
        "ha_accel_nervousness": "Нервозность педали газа",
        "ha_braking_efficiency": "Эффективность торможений, %",
        "ha_trend_driver_note": "Это про стиль вождения, а не про исправность автомобиля — просто дополнительный контекст.",
        "ha_bsfc_crosscheck_title": "⛽ BSFC по отчётам (сверка с расчётом из базы)",
        "ha_bsfc_crosscheck_note": "Собственный расчёт BSFC из базы данных — на вкладке \"Детальные логи\" для той же поездки; эти значения должны быть близки.",
        # --- Вкладка 5: ТО ---
        "maintenance_title": "История технического обслуживания",
        "maintenance_empty": "Записи о техническом обслуживании отсутствуют.",
        "col_date": "Дата",
        "col_mileage": "Пробег (км)",
        "col_description": "Что сделано",
        "unit_km": "км",
        "maintenance_click_hint": "Нажмите на запись, чтобы увидеть подробности.",
        "part_details": "Детали запчасти / расходника",
        "part_details_optional": "необязательно, но помогает при следующем ТО",
        "part_field": "Параметр",
        "part_value": "Значение",
        "part_manufacturer": "Производитель",
        "part_manufacturer_ph": "напр. Toyota, Bosch, Mann",
        "part_name": "Точное название",
        "part_name_ph": "напр. Toyota Genuine Motor Oil",
        "part_spec": "Спецификация / вязкость",
        "part_spec_ph": "напр. 0W-16, ATF WS, DOT 4",
        "part_quantity": "Количество",
        "part_quantity_ph": "напр. 3.9 л или 4 шт.",
        "part_price": "Цена",
        "part_price_ph": "напр. 240 zł",
        "attach_invoice_photo": "Приложить к записи загруженное фото фактуры",
        "invoice_photo_caption": "Фактура",
        "invoice_photo_locked": "🔒 Фото фактуры скрыто. Введите код доступа (тот же, что для карт), чтобы увидеть его — на фактуре могут быть личные данные.",
        "invoice_photo_broken": "⚠️ Не удалось показать сохранённое фото фактуры.",
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
        "save_success_drive": "✅ Запись сохранена и синхронизирована с Google Диском — она не пропадёт при перезапуске приложения.",
        "save_success_local_only": "⚠️ Запись сохранена только во временной копии этого контейнера и БУДЕТ ПОТЕРЯНА при перезапуске приложения. Чтобы записи сохранялись навсегда, настройте сервисный аккаунт Google (см. подсказку выше).",
        "save_failed": "❌ Не удалось сохранить запись ни на Google Диск, ни локально.",
        "storage_mode_drive": "☁️ Журнал хранится в папке на Google Диске — записи переживают перезапуски приложения.",
        "storage_mode_drive_readonly": "⚠️ Журнал читается с Google Диска, но записывать туда приложение не может: не настроен сервисный аккаунт. Новые записи сохранятся только временно и пропадут при перезапуске. Как настроить: создайте сервисный аккаунт Google Cloud, дайте его email право «Редактор» на папку с базой, и вставьте его JSON-ключ в Secrets приложения под именем [gcp_service_account].",
        "storage_mode_local": "⚠️ Журнал хранится только во временной памяти контейнера и пропадёт при перезапуске приложения. Чтобы записи сохранялись навсегда, создайте сервисный аккаунт Google Cloud, дайте его email право «Редактор» на папку с базой на Google Диске и вставьте его JSON-ключ в Secrets приложения под именем [gcp_service_account].",
        "save_fill_all": "⚠️ Заполните все поля перед сохранением.",
        "invoice_upload_label": "📷 Сфотографируйте фактуру/чек — данные подставятся автоматически",
        "invoice_section_title": "📷 Автоматическое распознавание фактуры",
        "invoice_how_it_works": "Сфотографируйте чек или фактуру — приложение распознает дату, пробег и список работ и подставит их в форму ниже. Останется только проверить и сохранить.",
        "invoice_upload_help": "Подойдёт обычное фото с телефона. Важно, чтобы дата, пробег и перечень работ были читаемы.",
        "invoice_waiting": "Обрабатываю фото…",
        "invoice_partial": "⚠️ Распознано частично — не удалось определить: {fields}. Заполните эти поля вручную в форме ниже.",
        "invoice_check_before_save": "Проверьте данные в форме ниже перед сохранением — распознавание может ошибаться.",
        "invoice_error_hint": "Попробуйте переснять при лучшем освещении, без бликов и под прямым углом.",
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
        "map_style_label": "Styl mapy",
        "map_stadia_key_found": "🔑 Klucz Stadia znaleziony w Secrets.",
        "map_stadia_key_missing": "🔑 Nie znaleziono klucza Stadia w Secrets. Sprawdź nazwę parametru — powinna brzmieć dokładnie stadia_api_key.",
        "map_stadia_troubleshoot": "Jeśli podkład nie ładuje się nawet z kluczem — w panelu Stadia dodaj domenę aplikacji (*.streamlit.app) do listy dozwolonych dla Twojego projektu: żądania z przeglądarki Stadia weryfikuje po domenie.",
        "db_autorefresh_note": "Baza odświeża się automatycznie 3 razy na dobę (co 8 godzin). Przycisk poniżej — jeśli potrzebujesz od razu.",
        "db_last_loaded": "Baza danych wczytana: {timestamp}",
        "downloading_db": "Pobieranie bazy danych z Google Drive (zwykle trwa 20-30 sekund, nie zamykaj strony)…",
        "refresh_in_progress_warning": "⏳ Odświeżanie już trwa — poczekaj około 30 sekund, ponowne kliknięcie teraz tylko to spowolni.",
        "db_missing": "⚠️ Nie udało się pobrać bazy danych z Google Drive. Sprawdź, czy dostęp do pliku jest ustawiony jako \"Każdy, kto ma link\" → \"Czytelnik\".",
        "db_error": "⚠️ Nie udało się odczytać bazy danych: {error}",
        "no_trip_data": "Brak danych o przejazdach do wyświetlenia.",
        "no_log_data": "Brak danych telemetrycznych (logów) do wyświetlenia.",
        "no_cell_data": "Brak danych o napięciu ogniw baterii. Włącz HighSpeedLogging w ustawieniach Hybrid Assistant lub wykonaj procedurę HV Check.",
        "no_gps_data": "Brak danych GPS dla tego przejazdu/okresu.",
        "gps_signal_lost_warning": "⚠️ Moduł GPS częściowo utracił sygnał podczas tego przejazdu (wg danych OBD samochód jechał, ale współrzędne się nie aktualizowały) — na mapie pokazano tylko odcinek z wiarygodnym sygnałem. To ograniczenie danych źródłowych, a nie błąd aplikacji.",
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
        "map_section_title": "🗺️ Mapa przejazdu",
        "map_select_trip": "Wybierz przejazd",
        "map_param_label": "Parametr na mapie",
        "map_param_mode": "Tryb (EV / silnik)",
        "map_param_braking": "Hamowanie",
        "map_param_speed": "Prędkość",
        "map_param_soc": "Poziom naładowania (SOC)",
        "map_period_title": "🗺️ Mapa za okres",
        "map_period_label": "Okres",
        "map_period_day": "Dzień",
        "map_period_week": "Tydzień",
        "map_period_month": "Miesiąc",
        "map_period_year": "Rok",
        "map_period_avg_consumption": "Średnie spalanie w okresie: {value} l/100km",
        "fuel_forecast_badge": "🔮 (prognoza)",
        "unit_kmh": "km/h",
        "unit_l100km": "l/100km",
        "unit_l": "l",
        "weather_title": "🌤️ Warunki meteorologiczne przejazdu",
        "weather_loading": "Pobieram dane historyczne o pogodzie…",
        "weather_no_gps": "Brak wiarygodnych współrzędnych GPS dla tego przejazdu — bez nich nie da się ustalić, jaka była pogoda dokładnie w tym miejscu.",
        "weather_no_time": "Nie udało się ustalić czasu startu przejazdu.",
        "weather_unavailable": "⚠️ Nie udało się pobrać danych o pogodzie (serwis Open-Meteo niedostępny lub brak danych dla tej daty).",
        "weather_air_temp": "Temperatura powietrza",
        "weather_condition": "Opady",
        "weather_wind": "Wiatr (skąd)",
        "weather_road_temp": "Temperatura asfaltu",
        "weather_road_temp_help": "Szacunek obliczeniowy, a nie pomiar: asfalt nagrzewa się od słońca mocniej niż powietrze, a nocą wychładza się poniżej jego temperatury. Rzeczywista wartość zależy też od koloru i wieku nawierzchni, wiatru i wilgotności.",
        "weather_precip": "Opady w ciągu godziny: {mm} mm.",
        "weather_cold_warning": "❄️ Zwiększone spalanie z powodu rozgrzewania silnika i kabiny: przy temperaturze poniżej +5 °C hybryda dłużej utrzymuje silnik spalinowy, a bateria oddaje mniej mocy.",
        "weather_headwind": "🌬️ Wiatr czołowy ~{speed} km/h — opór aerodynamiczny wyższy o około {pct}%. To przyrost samej składowej aerodynamicznej, a nie całego zużycia paliwa.",
        "weather_headwind_slow": "🌬️ Wiatr czołowy ~{speed} km/h. Przy tej średniej prędkości aerodynamika prawie nie wpływa na spalanie.",
        "weather_tailwind": "🍃 Wiatr tylny ~{speed} km/h — opór aerodynamiczny niższy niż zwykle.",
        "weather_source_note": "Źródło pogody: Open-Meteo (historyczna reanaliza) dla współrzędnych startu przejazdu.",
        "elevation_profile_title": "⛰️ Profil wysokości (ukształtowanie trasy)",
        "elevation_no_data": "Brak danych o wysokości dla tego przejazdu.",
        "elevation_flat": "Wysokość nie zmieniała się na całej trasie — albo odcinek jest rzeczywiście płaski, albo GPS zapisywał wysokość z dokładnością do pełnych metrów.",
        "unit_price_per_l": "zł/l",
        "unit_rpm": "obr/min",
        "unit_nm": "Nm",
        "fuel_forecast_help": "Szacunek sterownika na podstawie czasu wtrysku (dane Hybrid Assistant) — nie jest to bezpośredni pomiar paliwa.",
        "fuel_real_badge": "🧾 (rzeczywisty)",
        "fuel_real_badge_note": "🧾 Rzeczywiste spalanie wg paragonów ze stacji (raport Fuelio) — w odróżnieniu od prognozy sterownika, to potwierdzone litry i koszt.",
        "fuel_type_lpg": "LPG (gaz)",
        "fuel_type_petrol": "Benzyna",
        "map_day_refuel_note": "⛽ Tego dnia zatankowano: {fuel} — {liters} l po {price} zł/l.",
        "fuel_log_title": "⛽ Tankowania (dane rzeczywiste, raport Fuelio)",
        "fuel_log_no_data": "Brak danych o tankowaniach — wgraj raport Fuelio (PDF) do folderu na Google Drive obok bazy danych.",
        "fuel_last_refuel_date": "Ostatnie tankowanie",
        "fuel_liters": "Zatankowano",
        "fuel_price": "Cena",
        "fuel_days_ago": "{days} dni temu",
        "fuel_avg_consumption": "Średnie spalanie",
        "fuel_petrol_no_avg_note": "Brak danych — nie wiadomo, ile benzyny było w baku przed rozpoczęciem obserwacji, a spalanie mocno zależy od udziału używania benzyny (głównie rozruch/rozgrzewanie), więc uśrednianie po całym przebiegu byłoby mylące.",
        "fuel_trend_title": "📈 Historia tankowań",
        "fuel_metric_label": "Wskaźnik",
        "fuel_metric_days": "Dni od poprzedniego tankowania",
        "fuel_metric_liters": "Ile zatankowano, l",
        "fuel_metric_cost": "Koszt, zł",
        "fuel_period_label": "Okres",
        "fuel_trend_health_title": "⛽ Trend rzeczywistego spalania LPG (wg paragonów)",
        "fuel_lpg_trend_warn": "⚠️ Rzeczywiste spalanie LPG rośnie (~{value} l/100km/mies.) — warto sprawdzić instalację LPG (wtryskiwacze, reduktor, mieszankę).",
        "fuel_lpg_trend_ok": "Rzeczywiste spalanie LPG jest stabilne lub maleje — nie wykryto oznak problemów z LPG.",
        "fuel_crosscheck_title": "Weryfikacja: prognoza sterownika vs rzeczywiste spalanie, wg miesięcy",
        "fuel_crosscheck_note": "Jeśli rozbieżność między prognozą a rzeczywistym spalaniem rośnie z czasem — możliwe rozkalibrowanie wtryskiwaczy/czujników, warto przyjrzeć się LTFT w zakładce \"Analityka\".",
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
        "cvt_oil_no_record_message": "Wymiana oleju w skrzyni e-CVT nie została odnotowana. Zalecenie Toyoty dla trudnych warunków eksploatacji to 90 000 km lub 5 lat. Zaleca się prewencyjną wymianę płynu Toyota ATF WS w celu ochrony silników elektrycznych MG1/MG2 przed przegrzaniem.",
        "radiator_forecast_title": "Prognoza zabrudzenia chłodnic (trend temperatur względem otoczenia)",
        "radiator_forecast_result": "Różnica temperatury falownika/silnika minus otoczenie rośnie o ~{value}°C miesięcznie — warto sprawdzić chłodnice.",
        "radiator_forecast_stable": "Różnica temperatur względem otoczenia jest stabilna — brak oznak zabrudzenia chłodnic.",
        "logs_select_trip": "Wybierz przejazd do szczegółowej analizy",
        "logs_chart_speed_rpm": "Prędkość i obroty silnika",
        "logs_chart_hv": "Napięcie i prąd baterii (HV)",
        "logs_chart_temps": "Temperatury silnika, falownika i baterii HV",
        "logs_chart_mg": "Silniki MG1 / MG2 (obroty i moment)",
        "logs_mg_note": "ℹ️ Hybrid Assistant nie loguje prądów fazowych MG1/MG2 — dostępne są tylko obroty i moment obrotowy.",
        # --- Pełny raport przejazdu (jak w Hybrid Assistant) ---
        "rep_summary_title": "📋 Podsumowanie przejazdu",
        "rep_trip": "Przejazd",
        "rep_distance": "Odległość",
        "rep_time": "Czas",
        "rep_moving": "W ruchu",
        "rep_total": "Razem",
        "rep_ev": "EV",
        "rep_speed_avg": "Średnia prędkość",
        "rep_speed_max": "Maks. prędkość",
        "rep_speed_ev_avg": "Średnia prędkość na EV",
        "rep_soc_start_end": "SOC początek → koniec",
        "rep_ambient_avg": "Śr. temp. otoczenia",
        "rep_fuel_consumption": "Spalanie paliwa",
        "rep_ev_time_note": "Dokładna klasyfikacja EV/silnik w Hybrid Assistant opiera się na wewnętrznym wskaźniku systemu hybrydowego (HSI) — nasze obliczenie na podstawie ICE_RPM=0 może się nieznacznie różnić od ich wartości.",
        "rep_soc_title": "🔋 Statystyka naładowania (SOC)",
        "rep_soc_note": "ℹ️ Podział \"skąd wzięło się naładowanie\" (rekuperacja/wybieg/silnik spalinowy) to wewnętrzny, zastrzeżony algorytm Hybrid Assistant — nie mamy dostępu do dokładnego wzoru, więc nie jest odtwarzany.",
        "rep_hv_title": "⚡ Bateria wysokiego napięcia (HV)",
        "rep_hv_levels": "Poziomy",
        "rep_current": "Prąd",
        "rep_voltage": "Napięcie",
        "rep_hv_power": "Moc i limity",
        "rep_power": "Moc",
        "rep_hv_from_batt": "Oddane przez baterię",
        "rep_hv_to_batt": "Naładowane do baterii",
        "rep_hv_balance": "Bilans energii",
        "rep_ccl_dcl_note": "CCL/DCL — limity ładowania/rozładowania baterii (zmieniają się z poziomem naładowania i temperaturą).",
        "rep_temp_title": "🌡️ Temperatury",
        "rep_temp_ambient": "Powietrze",
        "rep_temp_room": "W kabinie/obudowie",
        "rep_temp_coolant": "Płyn chłodniczy silnika",
        "rep_temp_inverter": "Falownik",
        "rep_temp_mg": "Silnik elektryczny",
        "rep_hv_probes": "Czujniki baterii HV",
        "rep_elevation_title": "⛰️ Wysokość nad poziomem morza",
        "rep_altitude": "Wysokość, m",
        "rep_upward": "Podjazd",
        "rep_downward": "Zjazd",
        "rep_elevation_note": "Podjazd/zjazd liczone są na podstawie kolumny wysokości GPS w bazie — jest ona mniej dokładna niż wewnętrzne obliczenia Hybrid Assistant, więc łączny przyrost wysokości może być zaniżony.",
        "rep_energy_title": "🔥 Energia z silnika spalinowego",
        "rep_energy_from_ice": "Energia z silnika",
        "rep_energy_per_100km": "Zużycie energii",
        "rep_engine_title": "🚗 Silnik",
        "rep_load": "Obciążenie",
        "rep_ignitions_total": "Uruchomień silnika",
        "rep_ignitions_inefficient": "Nieefektywnych (<5 s)",
        "rep_ignitions_note": "Za nieefektywne uznaje się uruchomienie silnika krótsze niż 5 sekund — częste krótkie starty zwiększają zużycie.",
        "rep_engine_state": "Stan silnika",
        "rep_ice_running": "Pracuje (z paliwem)",
        "rep_ice_spinning": "Kręci się bez paliwa",
        "rep_ice_off": "Wyłączony",
        "rep_engine_state_note": "\"Kręci się bez paliwa\" — wybieg/hamowanie silnikiem bez wtrysku (przybliżona ocena na podstawie FUELFLOWH).",
        "rep_psd_title": "⚙️ Przekładnia planetarna (PSD): silnik i MG1/MG2",
        "rep_ice_torque": "Moment silnika (wyl.)",
        "rep_psd_note": "Moment silnika obliczony z mocy i obrotów (M = P / ω) — to szacunek, nie bezpośredni pomiar.",
        "rep_trims_title": "🎛️ Korekty paliwa",
        "rep_effective": "Łączna",
        "rep_bsfc_title": "⛽ Jednostkowe zużycie paliwa (BSFC)",
        "rep_bsfc_avg": "Średnia",
        "rep_bsfc_std": "Odch. std",
        "rep_bsfc_note": "BSFC (g/kWh) — ile paliwa zużywa się na każdą kWh mocy wytworzonej przez silnik; im mniej, tym silnik pracuje efektywniej w danym punkcie. Liczone tylko po niezerowych odczytach.",
        "rep_braking_title": "🛑 Hamowanie",
        "rep_brakings_total": "Wszystkich hamowań",
        "rep_brakings_good": "Tylko rekuperacja",
        "rep_brakings_bad": "Tylko mechaniczne",
        "rep_brakings_mixed": "Mieszane",
        "rep_braking_efficiency": "Efektywność hamowań",
        "rep_energy_recovered": "Energia z rekuperacji",
        "rep_braking_note": "Efektywność = odsetek hamowań, które obyły się wyłącznie rekuperacją, bez użycia klocków.",
        "rep_driver_eval_title": "👤 Ocena stylu jazdy",
        "rep_accel_nervousness": "\"Nerwowość\" pedału gazu",
        "rep_driver_eval_note": "Nerwowość pedału — średnia zmiana położenia pedału gazu między pomiarami; im wyższa, tym bardziej gwałtowny styl jazdy.",
        "rep_glide_title": "🛞 Indeks wybiegu (Glide)",
        "rep_glide_avg": "Średni indeks",
        "rep_glide_max": "Maks. indeks",
        "rep_glide_note": "Indeks wybiegu pokazuje, jak efektywnie wykorzystywany jest wybieg bez napędu silnika/elektromotoru. Dokładna metodologia Hybrid Assistant nie jest ujawniona — tu użyto surowego wskaźnika GLIDEINDEX z logu.",
        "rep_maps_title": "🗺️ Mapa przejazdu",
        "rep_charts_title": "📈 Wykresy w czasie",
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
        "ha_reports_title": "📄 Trendy z raportów HTML Hybrid Assistant",
        "ha_reports_explainer": "Prawie wszystkie wskaźniki są już rzetelnie liczone z samej bazy danych (patrz zakładka \"Szczegółowe logi\") i pokrywają się z raportem niemal co do cyfry. Ale kilka zastrzeżonych obliczeń Hybrid Assistant — podział naładowania baterii wg źródeł, indeks wybiegu (Glide) i ocena stylu jazdy — jest dostępnych tylko w gotowej postaci w raporcie HTML. Wgraj kilka raportów z różnych okresów, aby śledzić trendy.",
        "ha_reports_upload_label": "Wgraj raporty HTML Hybrid Assistant (można od razu kilka)",
        "ha_reports_limit_caption": "Jednorazowo można wgrać do 100 plików, każdy do 200 MB — to domyślne ograniczenia samego Streamlit.",
        "ha_reports_loaded_count": "Rozpoznanych raportów: {n}",
        "ha_reports_drive_found": "✅ Automatycznie pobrano z Google Drive: {n} raport(ów). Nie trzeba ich wgrywać osobno.",
        "ha_reports_drive_none": "ℹ️ W folderze na Google Drive nie znaleziono raportów HTML. Umieść je tam obok bazy danych — wtedy będą pobierane automatycznie przy każdym odświeżeniu. Albo wgraj ręcznie poniżej.",
        "ha_reports_drive_list": "Pokaż listę raportów z Google Drive",
        "ha_reports_upload_help": "Raport tworzy się w aplikacji Hybrid Assistant: otwórz przejazd i wybierz eksport do HTML.",
        "ha_reports_none_at_all": "Nie ma jeszcze żadnych raportów — ani na Google Drive, ani wgranych ręcznie.",
        "ha_reports_upload_success": "✅ Pomyślnie rozpoznano raportów: {n}",
        "ha_reports_upload_failed": "❌ Nie udało się rozpoznać „{name}”: {reason}",
        "ha_reports_fail_no_time": "w pliku nie znaleziono czasu przejazdu — to chyba nie jest raport Hybrid Assistant",
        "ha_reports_details": "Pokaż, które raporty rozpoznano",
        "ha_reports_col_file": "Plik",
        "ha_reports_col_source": "Źródło",
        "ha_reports_source_drive": "Google Drive",
        "ha_reports_source_manual": "Wgrany ręcznie",
        "ha_maps_title": "🗺️ Mapy z raportu Hybrid Assistant",
        "ha_trip_extras_title": "📄 Dane z raportu HTML dla tego przejazdu",
        "ha_maps_source_note": "📄 Mapa zbudowana z raportu HTML Hybrid Assistant (jego własne obliczenie kategorii).",
        "ha_trip_no_report": "Dla tego przejazdu nie wgrano raportu HTML. Wgraj raporty w zakładce „Porównanie i trendy” — aplikacja sama dopasuje je do przejazdów po czasie i pokaże tutaj firmowe wskaźniki oraz mapy Hybrid Assistant.",
        "ha_trip_report_found": "Znaleziono raport dla tego przejazdu: {name}",
        "ha_maps_explainer": "Te mapy rysuje sam Hybrid Assistant według własnych algorytmów. Map „Chwilowe spalanie”, „BSFC” i „Ocena wybiegu” nie da się zbudować z bazy danych — nie ma tam ani gotowych kategorii, ani jawnego wzoru ich obliczania.",
        "ha_maps_select_report": "Raport",
        "ha_maps_select_map": "Mapa",
        "ha_maps_no_maps": "W tym raporcie nie znaleziono map (przejazd mógł nie mieć danych GPS).",
        "ha_maps_gps_warning": "⚠️ W tym raporcie punkty GPS mieszczą się w plamce poniżej 100 m, choć przejazd był dłuższy — moduł GPS tracił sygnał podczas zapisu. Kategorie kolorów są wiarygodne, ale geografii takiej mapy nie ma sensu czytać.",
        "device_label": "Widok interfejsu",
        "device_auto": "Automatycznie",
        "device_mobile": "Telefon",
        "device_desktop": "Komputer",
        "device_current": "Wykryto: {device}",
        "ha_reports_parse_error": "⚠️ Nie udało się rozpoznać żadnego z wgranych plików jako raportu Hybrid Assistant.",
        "ha_reports_hvcheck_note": "ℹ️ Jeśli w raporcie są wyniki testu HV Check (napięcia poszczególnych ogniw), daj znać — wyślij przykład takiego raportu, a dodam automatyczne wyciąganie tych danych do obliczenia SOH, gdy HV Check w samej bazie jest pusty.",
        "ha_trend_soc_title": "🔋 Skąd bierze się naładowanie baterii",
        "ha_soc_brakings": "Z rekuperacji przy hamowaniu",
        "ha_soc_coasting": "Z wybiegu",
        "ha_soc_ice": "Z silnika spalinowego",
        "ha_trend_soc_note": "Udział naładowania z każdego źródła, w % całkowitego przyrostu SOC w przejeździe.",
        "ha_trend_brakings_warn": "⚠️ Udział naładowania z rekuperacji przy hamowaniu maleje (~{value} p.p./mies.) — warto sprawdzić układ hamulcowy i działanie rekuperacji.",
        "ha_trend_brakings_ok": "Udział naładowania z rekuperacji jest stabilny lub rośnie — nie wykryto oznak zużycia.",
        "ha_trend_glide_title": "🛞 Indeks wybiegu (Glide) wg raportów",
        "ha_glide_score": "Glide score",
        "ha_trend_glide_note": "Indeks wybiegu z oficjalnego obliczenia Hybrid Assistant (dokładna metodologia nie jest ujawniona przez producenta).",
        "ha_trend_glide_warn": "⚠️ Indeks wybiegu maleje (~{value}/mies.) — możliwy wzrost oporu wewnętrznego przekładni/PSD, warto zwrócić uwagę.",
        "ha_trend_glide_ok": "Indeks wybiegu jest stabilny lub rośnie — nie wykryto oznak zużycia przekładni.",
        "ha_trend_driver_title": "👤 Styl jazdy wg raportów",
        "ha_accel_nervousness": "Nerwowość pedału gazu",
        "ha_braking_efficiency": "Efektywność hamowań, %",
        "ha_trend_driver_note": "To dotyczy stylu jazdy, a nie sprawności samochodu — dodatkowy kontekst.",
        "ha_bsfc_crosscheck_title": "⛽ BSFC wg raportów (weryfikacja z obliczeniem z bazy)",
        "ha_bsfc_crosscheck_note": "Własne obliczenie BSFC z bazy danych — w zakładce \"Szczegółowe logi\" dla tego samego przejazdu; te wartości powinny być zbliżone.",
        "maintenance_title": "Historia przeglądów technicznych",
        "maintenance_empty": "Brak zapisanych przeglądów.",
        "col_date": "Data",
        "col_mileage": "Przebieg (km)",
        "col_description": "Zakres prac",
        "unit_km": "km",
        "maintenance_click_hint": "Kliknij wpis, aby zobaczyć szczegóły.",
        "part_details": "Szczegóły części / materiału eksploatacyjnego",
        "part_details_optional": "opcjonalnie, ale pomaga przy kolejnym przeglądzie",
        "part_field": "Parametr",
        "part_value": "Wartość",
        "part_manufacturer": "Producent",
        "part_manufacturer_ph": "np. Toyota, Bosch, Mann",
        "part_name": "Dokładna nazwa",
        "part_name_ph": "np. Toyota Genuine Motor Oil",
        "part_spec": "Specyfikacja / lepkość",
        "part_spec_ph": "np. 0W-16, ATF WS, DOT 4",
        "part_quantity": "Ilość",
        "part_quantity_ph": "np. 3.9 l lub 4 szt.",
        "part_price": "Cena",
        "part_price_ph": "np. 240 zł",
        "attach_invoice_photo": "Dołącz do wpisu wgrane zdjęcie faktury",
        "invoice_photo_caption": "Faktura",
        "invoice_photo_locked": "🔒 Zdjęcie faktury ukryte. Wprowadź kod dostępu (ten sam co do map), aby je zobaczyć — na fakturze mogą być dane osobowe.",
        "invoice_photo_broken": "⚠️ Nie udało się wyświetlić zapisanego zdjęcia faktury.",
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
        "save_success_drive": "✅ Wpis zapisany i zsynchronizowany z Google Drive — nie zniknie po restarcie aplikacji.",
        "save_success_local_only": "⚠️ Wpis zapisany tylko w tymczasowej kopii tego kontenera i ZOSTANIE UTRACONY po restarcie aplikacji. Aby wpisy zapisywały się na stałe, skonfiguruj konto serwisowe Google (patrz wskazówka powyżej).",
        "save_failed": "❌ Nie udało się zapisać wpisu ani na Google Drive, ani lokalnie.",
        "storage_mode_drive": "☁️ Dziennik przechowywany jest w folderze na Google Drive — wpisy przetrwają restarty aplikacji.",
        "storage_mode_drive_readonly": "⚠️ Dziennik jest odczytywany z Google Drive, ale aplikacja nie może tam zapisywać: brak konta serwisowego. Nowe wpisy zapiszą się tylko tymczasowo i znikną po restarcie. Jak skonfigurować: utwórz konto serwisowe Google Cloud, nadaj jego adresowi e-mail uprawnienie „Edytor” do folderu z bazą i wklej jego klucz JSON do Secrets aplikacji pod nazwą [gcp_service_account].",
        "storage_mode_local": "⚠️ Dziennik przechowywany jest tylko w tymczasowej pamięci kontenera i zniknie po restarcie aplikacji. Aby wpisy zapisywały się na stałe, utwórz konto serwisowe Google Cloud, nadaj jego adresowi e-mail uprawnienie „Edytor” do folderu z bazą na Google Drive i wklej jego klucz JSON do Secrets aplikacji pod nazwą [gcp_service_account].",
        "save_fill_all": "⚠️ Uzupełnij wszystkie pola przed zapisaniem.",
        "invoice_upload_label": "📷 Sfotografuj fakturę/paragon — dane zostaną podstawione automatycznie",
        "invoice_section_title": "📷 Automatyczne rozpoznawanie faktury",
        "invoice_how_it_works": "Zrób zdjęcie paragonu lub faktury — aplikacja rozpozna datę, przebieg i zakres prac oraz podstawi je do formularza poniżej. Wystarczy sprawdzić i zapisać.",
        "invoice_upload_help": "Wystarczy zwykłe zdjęcie z telefonu. Ważne, aby data, przebieg i zakres prac były czytelne.",
        "invoice_waiting": "Przetwarzam zdjęcie…",
        "invoice_partial": "⚠️ Rozpoznano częściowo — nie udało się ustalić: {fields}. Uzupełnij te pola ręcznie w formularzu poniżej.",
        "invoice_check_before_save": "Sprawdź dane w formularzu poniżej przed zapisaniem — rozpoznawanie może się mylić.",
        "invoice_error_hint": "Spróbuj zrobić zdjęcie ponownie przy lepszym świetle, bez odblasków i pod kątem prostym.",
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
# ОПРЕДЕЛЕНИЕ УСТРОЙСТВА И АДАПТИВНАЯ ВЁРСТКА
# ============================================================
# Тип устройства определяется по заголовку User-Agent через
# официальный API st.context.headers. Это серверная эвристика: она
# надёжна для типичных телефонов и десктопов, но User-Agent можно
# подделать, а планшеты/складные устройства попадают в серую зону.
# Поэтому она влияет ТОЛЬКО на удобство (размеры графиков, число
# колонок), но никогда — на сами данные и расчёты. Дополнительно в
# боковой панели есть ручное переключение на случай неверного
# определения.

_MOBILE_UA_PATTERN = re.compile(
    r"Android|webOS|iPhone|iPod|BlackBerry|IEMobile|Opera Mini|Mobile|Windows Phone",
    re.IGNORECASE,
)
_TABLET_UA_PATTERN = re.compile(r"iPad|Tablet|PlayBook|Silk", re.IGNORECASE)


def _detect_device_from_headers() -> str:
    """Возвращает 'mobile' или 'desktop' по User-Agent. При любой
    ошибке/недоступности заголовков безопасно возвращает 'desktop'."""
    try:
        headers = st.context.headers or {}
        user_agent = headers.get("User-Agent") or headers.get("user-agent") or ""
    except Exception:
        return "desktop"

    if not user_agent:
        return "desktop"
    # Планшеты считаем десктопом: на них хватает места под широкую вёрстку.
    if _TABLET_UA_PATTERN.search(user_agent):
        return "desktop"
    if _MOBILE_UA_PATTERN.search(user_agent):
        return "mobile"
    return "desktop"


def get_device_type() -> str:
    """Тип устройства для текущей сессии. Ручной выбор пользователя
    (если он его сделал) имеет приоритет над автоопределением."""
    override = st.session_state.get("device_override")
    if override in ("mobile", "desktop"):
        return override
    if "device_type_detected" not in st.session_state:
        st.session_state["device_type_detected"] = _detect_device_from_headers()
    return st.session_state["device_type_detected"]


def is_mobile() -> bool:
    return get_device_type() == "mobile"


def rsp_height(desktop_px: int) -> int:
    """Высота графика: на телефоне ниже, чтобы влезало на экран без
    длинной прокрутки, но не настолько, чтобы стало нечитаемо."""
    return int(desktop_px * 0.72) if is_mobile() else desktop_px


# Примечание: уменьшать ЧИСЛО колонок на телефоне нельзя — вызывающий код
# распаковывает фиксированное количество (col1, col2, col3, col4 = ...),
# и меньшее число сломало бы распаковку. Поэтому перенос колонок на узком
# экране решается через CSS (flex-wrap ниже), а не в Python.


def inject_responsive_css() -> None:
    """Немного CSS для аккуратного вида, особенно на телефоне:
    компактнее отступы, читаемые метрики, аккуратные вкладки и
    горизонтальная прокрутка таблиц вместо обрезания."""
    mobile = is_mobile()
    metric_value_size = "1.35rem" if mobile else "1.75rem"
    block_padding = "0.6rem" if mobile else "1.2rem"
    st.markdown(
        f"""
        <style>
        .block-container {{
            padding-top: {block_padding};
            padding-bottom: 2.5rem;
            padding-left: {block_padding};
            padding-right: {block_padding};
        }}
        /* Streamlit по умолчанию обрезает длинные подписи и значения
           метрик многоточием ("Zatank...", "18...."). На узком экране
           это делает их бесполезными, поэтому разрешаем перенос на
           следующую строку вместо обрезки. */
        [data-testid="stMetricValue"],
        [data-testid="stMetricValue"] * {{
            font-size: {metric_value_size};
            line-height: 1.25;
            white-space: normal !important;
            overflow: visible !important;
            text-overflow: clip !important;
            overflow-wrap: anywhere;
        }}
        [data-testid="stMetricLabel"],
        [data-testid="stMetricLabel"] * {{
            font-size: 0.8rem;
            opacity: 0.85;
            white-space: normal !important;
            overflow: visible !important;
            text-overflow: clip !important;
            overflow-wrap: anywhere;
            line-height: 1.25;
        }}
        [data-testid="stMetric"] {{
            background: rgba(140, 160, 200, 0.07);
            border: 1px solid rgba(140, 160, 200, 0.18);
            border-radius: 10px;
            padding: 0.55rem 0.7rem;
            height: 100%;
        }}
        .stTabs [data-baseweb="tab-list"] {{
            gap: 0.15rem;
            overflow-x: auto;
        }}
        .stTabs [data-baseweb="tab"] {{
            padding: 0.35rem 0.7rem;
            white-space: nowrap;
        }}
        [data-testid="stExpander"] {{
            border-radius: 10px;
        }}
        [data-testid="stDataFrame"] {{
            overflow-x: auto;
        }}
        /* На узком экране ряд из 4-5 метрик сжимается до нечитаемых
           колонок в пару символов шириной. Разрешаем колонкам переноситься
           и задаём минимальную ширину — получается аккуратная сетка
           по две метрики в ряд вместо пяти сплющенных. */
        @media (max-width: 640px) {{
            [data-testid="stHorizontalBlock"] {{
                flex-wrap: wrap !important;
                gap: 0.4rem !important;
            }}
            [data-testid="stHorizontalBlock"] > [data-testid="stColumn"] {{
                min-width: calc(50% - 0.4rem) !important;
                flex: 1 1 calc(50% - 0.4rem) !important;
            }}
            /* Вложенные колонки (колонка внутри колонки) на телефоне
               ужимались бы до четверти экрана — там подпись уже не
               помещается ни при каком переносе. Разворачиваем их на всю
               ширину друг под другом. */
            [data-testid="stColumn"] [data-testid="stHorizontalBlock"] > [data-testid="stColumn"] {{
                min-width: 100% !important;
                flex: 1 1 100% !important;
            }}
            .block-container {{
                padding-left: 0.6rem;
                padding-right: 0.6rem;
            }}
            [data-testid="stMetricValue"],
            [data-testid="stMetricValue"] * {{
                font-size: 1.3rem;
            }}
        }}
        </style>
        """,
        unsafe_allow_html=True,
    )


# ============================================================
# ЗАГРУЗКА БАЗЫ ДАННЫХ С GOOGLE ДИСКА
# ============================================================

def _drive_list_folder(service, folder_id: str) -> list:
    """Рекурсивно перечисляет файлы в папке Google Диска через API.
    Возвращает список (id, имя, относительный путь)."""
    items = []
    stack = [(folder_id, "")]
    while stack:
        current_id, prefix = stack.pop()
        page_token = None
        while True:
            response = (
                service.files()
                .list(
                    q=f"'{current_id}' in parents and trashed=false",
                    fields="nextPageToken, files(id, name, mimeType)",
                    pageSize=200,
                    pageToken=page_token,
                    supportsAllDrives=True,
                    includeItemsFromAllDrives=True,
                )
                .execute()
            )
            for f in response.get("files", []):
                if f.get("mimeType") == "application/vnd.google-apps.folder":
                    stack.append((f["id"], os.path.join(prefix, f["name"])))
                else:
                    items.append((f["id"], f["name"], os.path.join(prefix, f["name"])))
            page_token = response.get("nextPageToken")
            if not page_token:
                break
    return items


def download_folder_via_drive_api(service, dest_dir: str) -> "tuple[int, int]":
    """Скачивает папку через Drive API от имени сервисного аккаунта.
    В отличие от анонимного скачивания, такие запросы авторизованы, и
    Google не режет их лимитами на массовые загрузки.
    Возвращает (сколько скачано, сколько не удалось)."""
    from googleapiclient.http import MediaIoBaseDownload

    files = _drive_list_folder(service, GDRIVE_FOLDER_ID)
    ok, failed = 0, 0
    for file_id, name, rel_path in files:
        target = os.path.join(dest_dir, rel_path)
        os.makedirs(os.path.dirname(target), exist_ok=True)
        try:
            request = service.files().get_media(fileId=file_id, supportsAllDrives=True)
            with io.FileIO(target, "wb") as fh:
                downloader = MediaIoBaseDownload(fh, request, chunksize=5 * 1024 * 1024)
                done = False
                while not done:
                    _status, done = downloader.next_chunk()
            ok += 1
        except Exception as e:
            failed += 1
            print(f"[drive] не удалось скачать {name}: {e!r}", flush=True)
            if os.path.exists(target):
                try:
                    os.remove(target)
                except OSError:
                    pass
    return ok, failed


@st.cache_resource(show_spinner=False, ttl=DB_CACHE_TTL_SECONDS)
def download_database() -> str:
    """Скачивает содержимое папки на Google Диске во временное
    хранилище контейнера и находит внутри неё файл базы данных (.db).
    Результат кэшируется, чтобы не скачивать файлы заново на каждый
    ререндер страницы — только на холодном старте, по истечении TTL
    или по кнопке "Обновить базу данных".

    Папка (а не конкретный файл) используется потому, что при
    повторной загрузке нового экспорта в тот же файл на Google Диске
    его внутренний ID иногда меняется — скачивание по ID файла тогда
    продолжает получать старую версию. Скачивание всей папки и выбор
    самого подходящего .db файла внутри неё устойчиво к этому.

    Скачивание идёт в ОТДЕЛЬНУЮ временную папку и переключается на
    неё одним атомарным os.rename только после успешного завершения —
    это защищает от ситуации, когда повторный клик "Обновить базу
    данных" запускает второе скачивание, пока первое ещё не закончило
    писать файлы в общую папку (раньше это приводило к зависанию)."""
    with _download_lock:
        temp_dir = tempfile.mkdtemp(prefix="hybridassistant_dl_", dir="/tmp")
        try:
            print(f"[download_database] начинаю скачивание папки {GDRIVE_FOLDER_ID} -> {temp_dir}", flush=True)
            t0 = time.time()
            download_error = None

            # Если настроен сервисный аккаунт, скачиваем через Drive API:
            # такие запросы авторизованы, и Google не применяет к ним лимиты
            # на массовые анонимные загрузки, из-за которых часть файлов
            # переставала скачиваться по мере роста папки.
            service = get_drive_service()
            if service is not None:
                try:
                    ok, failed = download_folder_via_drive_api(service, temp_dir)
                    print(
                        f"[download_database] Drive API: скачано {ok}, не удалось {failed}, "
                        f"за {time.time() - t0:.1f} сек",
                        flush=True,
                    )
                    if ok == 0:
                        download_error = RuntimeError("Drive API не скачал ни одного файла")
                except Exception as e:
                    download_error = e
                    print(f"[download_database] Drive API не сработал: {e!r}", flush=True)
            else:
                download_error = RuntimeError("сервисный аккаунт не настроен")

            # Запасной путь — анонимное скачивание через gdown. Оно работает
            # без всякой настройки, но Google ограничивает такие загрузки,
            # поэтому часть файлов может не доехать.
            if download_error is not None:
                print("[download_database] использую анонимное скачивание (gdown)", flush=True)
                for attempt in (1, 2):
                    try:
                        gdown.download_folder(
                            id=GDRIVE_FOLDER_ID, output=temp_dir, quiet=True, use_cookies=False
                        )
                        download_error = None
                        break
                    except Exception as e:
                        download_error = e
                        print(
                            f"[download_database] попытка {attempt} не удалась за "
                            f"{time.time() - t0:.1f} сек: {e!r}",
                            flush=True,
                        )
                        if attempt == 1:
                            time.sleep(3)
            print(f"[download_database] скачивание заняло {time.time() - t0:.1f} сек", flush=True)

            db_candidates = []
            for root, _dirs, files in os.walk(temp_dir):
                for fname in files:
                    if fname.lower().endswith(".db"):
                        db_candidates.append(os.path.join(root, fname))

            print(f"[download_database] найдено файлов .db: {len(db_candidates)}: {db_candidates}", flush=True)

            if download_error is not None and db_candidates:
                # База на месте — работаем дальше, пусть часть отчётов и не
                # доехала. Полностью терять работоспособность из-за этого
                # неправильно.
                print(
                    "[download_database] часть файлов не скачалась, но база данных получена — продолжаем",
                    flush=True,
                )
            elif download_error is not None:
                raise download_error

            if not db_candidates:
                raise RuntimeError(
                    "В папке на Google Диске не найден файл базы данных (.db). "
                    "Проверьте, что доступ к папке открыт по ссылке и файл действительно там лежит."
                )

            # Если в папке несколько .db-файлов: сначала предпочитаем файл с
            # обычным именем hybridassistant*.db, а среди подходящих кандидатов
            # берём самый крупный по размеру — на практике база растёт со
            # временем, поэтому самый большой файл почти всегда самый полный/свежий
            # экспорт. Чтобы не гадать, лучше держать в папке только один .db файл.
            named = [c for c in db_candidates if os.path.basename(c).lower().startswith("hybridassistant")]
            pool = named if named else db_candidates
            chosen_temp_path = max(pool, key=os.path.getsize)

            if os.path.getsize(chosen_temp_path) == 0:
                raise RuntimeError("Найденный файл базы данных пуст.")
            with open(chosen_temp_path, "rb") as f:
                header = f.read(16)
            if not header.startswith(b"SQLite format 3"):
                raise RuntimeError(
                    "Найденный файл не является базой SQLite — проверьте содержимое папки на Google Диске."
                )

            # Атомарно подменяем общую папку на только что скачанную. os.rename
            # на одной файловой системе (весь /tmp — одна ФС) — атомарная
            # операция, поэтому читатели никогда не увидят наполовину
            # скачанную/удалённую папку.
            relative_db_path = os.path.relpath(chosen_temp_path, temp_dir)
            final_dir = LOCAL_DB_FOLDER_PATH
            stale_dir = None
            if os.path.exists(final_dir):
                stale_dir = f"{final_dir}_stale_{int(time.time() * 1000)}"
                os.rename(final_dir, stale_dir)
            os.rename(temp_dir, final_dir)
            if stale_dir:
                shutil.rmtree(stale_dir, ignore_errors=True)

            final_db_path = os.path.join(final_dir, relative_db_path)
            print(f"[download_database] готово, используется файл: {final_db_path}", flush=True)
            return final_db_path
        except Exception:
            shutil.rmtree(temp_dir, ignore_errors=True)
            raise


# ============================================================
# FUELIO: РЕАЛЬНЫЙ РАСХОД ТОПЛИВА ИЗ ЧЕКОВ АЗС (PDF-ОТЧЁТ)
# ============================================================
# В той же папке на Google Диске может лежать PDF-отчёт из приложения
# Fuelio — учёт реальных заправок (дата, пробег, литры, цена) отдельно
# по LPG и бензину. В отличие от расхода из hybridassistant.db (который
# ЭБУ ОЦЕНИВАЕТ по длительности впрыска — это ПРОГНОЗ), здесь литры и
# стоимость подтверждены чеком на заправке — это РЕАЛЬНЫЙ расход.
# Показатель расхода для заправки известен только "задним числом" —
# после СЛЕДУЮЩЕЙ заправки того же вида топлива (Fuelio считает его по
# пробегу между двумя заправками одного типа).

FUEL_TYPE_PRICE_THRESHOLD = 4.5  # zł/л: ниже — LPG, выше — бензин (проверено на реальном отчёте)

_FUELIO_ENTRY_PATTERN = re.compile(
    r"(\d{4}-\d{2}-\d{2})\s*\n"
    r"\s*([\d\s\xa0]+?)\s*km\s*\n"
    r"\s*([\d,]+)\s*zł\s*\n"
    r"\s*([\d,]+)\s*zł\s*\n"
    r"\s*([\d,]+)\s*l\s*\n"
    r"(?:\s*([\d,]+)\s*l/100km\s*\n)?"
    r"((?:(?!\d{4}-\d{2}-\d{2}).)*)",
    re.MULTILINE | re.DOTALL,
)


def _fuelio_to_float(value: "str | None"):
    if not value:
        return None
    cleaned = value.replace("\xa0", "").replace(" ", "").replace(",", ".")
    try:
        return float(cleaned)
    except ValueError:
        return None


def find_fuel_report_pdfs(folder_path: str) -> list:
    pdfs = []
    for root, _dirs, files in os.walk(folder_path):
        for fname in files:
            if fname.lower().endswith(".pdf"):
                pdfs.append(os.path.join(root, fname))
    return pdfs


@st.cache_data(show_spinner=False)
def parse_fuelio_pdf(file_bytes: bytes) -> pd.DataFrame:
    """Разбирает PDF-отчёт Fuelio в таблицу заправок. Разбор проверен
    на реальном отчёте: количество найденных записей, суммы литров и
    стоимости по видам топлива и диапазон пробега совпали с итоговой
    статистикой самого отчёта день-в-день."""
    reader = pypdf.PdfReader(io.BytesIO(file_bytes))
    text = "\n".join(page.extract_text() or "" for page in reader.pages)

    idx = text.find("Wg roku")
    section = text[idx:] if idx != -1 else text

    rows = []
    for m in _FUELIO_ENTRY_PATTERN.finditer(section):
        date_str, odo, cost, price, liters, consumption, rest = m.groups()
        try:
            entry_date = datetime.strptime(date_str, "%Y-%m-%d").date()
        except ValueError:
            continue
        price_f = _fuelio_to_float(price)
        if price_f is None:
            continue
        rabat_match = re.search(r"Rabat:\s*([\d,]+)\s*zł", rest)
        rows.append(
            {
                "date": entry_date,
                "odo": _fuelio_to_float(odo),
                "cost": _fuelio_to_float(cost),
                "price": price_f,
                "liters": _fuelio_to_float(liters),
                "consumption_l100": _fuelio_to_float(consumption),
                "discount": _fuelio_to_float(rabat_match.group(1)) if rabat_match else None,
                "fuel_type": "lpg" if price_f < FUEL_TYPE_PRICE_THRESHOLD else "petrol",
            }
        )
    return pd.DataFrame(rows)


# --- CSV-бэкапы Fuelio ---
# Fuelio сохраняет резервные копии в Android/Fuelio/backup-csv (в том
# числе в Google Диск). Формат — CSV из нескольких секций, каждая
# начинается со строки вида "## Log". Заправки лежат в секции Log:
#   Data, Odo (km), Fuel (litres), Full, Price, l/100km, latitude,
#   longitude, City, Notes, Missed, TankNumber, FuelType, VolumePrice, ...
# Здесь Price — это стоимость всей заправки, а VolumePrice — цена за литр.
# CSV точнее PDF: в нём есть координаты, признак полного бака и номер
# бака, поэтому при наличии обоих источников выбираем CSV.

_FUELIO_SECTION_PREFIX = "## "


def find_fuelio_csv_backups(folder_path: str) -> list:
    found = []
    for root, _dirs, files in os.walk(folder_path):
        for fname in files:
            if fname.lower().endswith(".csv"):
                found.append(os.path.join(root, fname))
    return sorted(found)


def _fuelio_pick_column(columns: list, *keywords: str) -> "str | None":
    """Ищет колонку по ключевому слову: в реальных файлах названия
    отличаются единицами измерения — 'Odo (km)' против 'Odo (mi)'."""
    for col in columns:
        low = str(col).strip().strip('"').lower()
        if all(kw in low for kw in keywords):
            return col
    return None


@st.cache_data(show_spinner=False)
def parse_fuelio_csv(file_bytes: bytes) -> pd.DataFrame:
    """Разбирает CSV-бэкап Fuelio. Пустой DataFrame означает, что файл
    не является бэкапом Fuelio (в папке могут лежать любые CSV).

    Проверено на реальном бэкапе: в секции Log Fuelio уже сам считает
    расход в колонке 'l/100km', указывает вид топлива кодом FuelType
    (4xx — газ, 1xx — бензин), пишет скидку в примечании ('Rabat: 0,36 zł',
    с запятой в качестве десятичного разделителя) и название заправки.
    Всё это берём как есть, а не пересчитываем заново."""
    try:
        text = file_bytes.decode("utf-8-sig", errors="replace")
    except Exception:
        return pd.DataFrame()

    lines = text.splitlines()
    sections, current, buffer = {}, None, []
    for line in lines:
        stripped = line.strip().strip('"')
        if stripped.startswith("##"):
            if current and buffer:
                sections[current] = buffer
            current = stripped.lstrip("#").strip().lower()
            buffer = []
        elif current is not None and line.strip():
            buffer.append(line)
    if current and buffer:
        sections[current] = buffer

    log_lines = sections.get("log")
    if not log_lines or len(log_lines) < 2:
        return pd.DataFrame()

    try:
        df = pd.read_csv(io.StringIO("\n".join(log_lines)))
    except Exception:
        return pd.DataFrame()
    if df.empty:
        return pd.DataFrame()

    cols = list(df.columns)
    col_date = _fuelio_pick_column(cols, "data") or _fuelio_pick_column(cols, "date")
    col_odo = _fuelio_pick_column(cols, "odo")
    col_fuel = _fuelio_pick_column(cols, "fuel", "litr") or _fuelio_pick_column(cols, "fuel", "gallon")
    col_cost = _fuelio_pick_column(cols, "price", "optional")
    col_volprice = _fuelio_pick_column(cols, "volumeprice")
    col_cons = _fuelio_pick_column(cols, "l/100km") or _fuelio_pick_column(cols, "mpg")
    col_lat = _fuelio_pick_column(cols, "latitude")
    col_lon = _fuelio_pick_column(cols, "longitude")
    col_tank = _fuelio_pick_column(cols, "tanknumber")
    col_ftype = _fuelio_pick_column(cols, "fueltype")
    col_full = _fuelio_pick_column(cols, "full")
    col_city = _fuelio_pick_column(cols, "city")
    col_notes = _fuelio_pick_column(cols, "notes")

    if not (col_date and col_fuel):
        return pd.DataFrame()

    out = pd.DataFrame(index=df.index)
    # В файле дата идёт вместе со временем ("2026-09-07 16:13") — время
    # сохраняем: за один день бывает несколько заправок разными видами топлива.
    parsed_dt = pd.to_datetime(df[col_date], errors="coerce")
    out["datetime"] = parsed_dt
    out["date"] = parsed_dt.dt.date
    out["liters"] = pd.to_numeric(df[col_fuel], errors="coerce")
    out["odo"] = pd.to_numeric(df[col_odo], errors="coerce") if col_odo else np.nan
    out["cost"] = pd.to_numeric(df[col_cost], errors="coerce") if col_cost else np.nan

    if col_volprice:
        out["price"] = pd.to_numeric(df[col_volprice], errors="coerce")
    else:
        out["price"] = np.nan
    need_price = out["price"].isna() | (out["price"] == 0)
    if need_price.any():
        out.loc[need_price, "price"] = (
            out.loc[need_price, "cost"] / out.loc[need_price, "liters"].replace(0, np.nan)
        )

    # Расход Fuelio считает сам и кладёт в отдельную колонку. Для неполных
    # заправок он пуст — это правильно, по ним расход посчитать нельзя.
    out["consumption_l100"] = pd.to_numeric(df[col_cons], errors="coerce") if col_cons else np.nan
    out.loc[out["consumption_l100"] == 0, "consumption_l100"] = np.nan

    out["full_tank"] = pd.to_numeric(df[col_full], errors="coerce").fillna(1) if col_full else 1
    if col_lat and col_lon:
        lat = pd.to_numeric(df[col_lat], errors="coerce")
        lon = pd.to_numeric(df[col_lon], errors="coerce")
        # (0,0) в Fuelio означает "координаты не записаны".
        valid = (lat != 0) | (lon != 0)
        out["lat"] = lat.where(valid)
        out["lon"] = lon.where(valid)
    out["station"] = df[col_city].astype(str).str.strip() if col_city else None
    out["tank"] = pd.to_numeric(df[col_tank], errors="coerce") if col_tank else np.nan

    # Вид топлива: код FuelType надёжнее цены (4xx — газ, 1xx — бензин).
    # Цена остаётся запасным признаком, если кода нет.
    fuel_type = pd.Series(index=df.index, dtype=object)
    if col_ftype:
        codes = pd.to_numeric(df[col_ftype], errors="coerce")
        fuel_type[(codes >= 400) & (codes < 500)] = "lpg"
        fuel_type[(codes >= 100) & (codes < 200)] = "petrol"
    unknown = fuel_type.isna()
    if unknown.any():
        fuel_type[unknown] = np.where(
            out.loc[unknown, "price"].fillna(0) < FUEL_TYPE_PRICE_THRESHOLD, "lpg", "petrol"
        )
    out["fuel_type"] = fuel_type

    # Скидка записана в примечании как "Rabat: 0,36 zł" (запятая — разделитель).
    if col_notes:
        notes = df[col_notes].astype(str)
        discount = notes.str.extract(r"Rabat:\s*([\d,\.]+)", expand=False)
        out["discount"] = pd.to_numeric(
            discount.str.replace(",", ".", regex=False), errors="coerce"
        )
    else:
        out["discount"] = np.nan

    out = out.dropna(subset=["datetime", "liters"])
    if out.empty:
        return pd.DataFrame()
    return out.sort_values("datetime").reset_index(drop=True)


def _compute_consumption_between_fillups(df: pd.DataFrame) -> pd.DataFrame:
    """Дополняет расход там, где Fuelio его не посчитал (например, в
    PDF-отчётах или у старых записей). Собственные значения Fuelio НЕ
    перезаписываются — они точнее, потому что учитывают неполные баки.

    Метод полного бака: залитые сейчас литры — это ровно то, что
    израсходовано с прошлой полной заправки. Формула сверена с Fuelio:
    для заправки 31.08 (18.68 л, 392 км) выходит 4.77 л/100км — ровно
    как в его собственном отчёте. У первой заправки каждого вида
    топлива расхода нет: не с чем сравнивать пробег."""
    if df.empty or "odo" not in df.columns:
        return df
    df = df.sort_values("datetime").copy()
    if "consumption_l100" not in df.columns:
        df["consumption_l100"] = np.nan

    for _fuel_type, group in df.groupby("fuel_type"):
        distance = group["odo"].diff()
        computed = group["liters"] / distance * 100.0
        computed[(distance <= 0) | distance.isna()] = np.nan
        # Неполная заправка не позволяет применять метод полного бака.
        if "full_tank" in group.columns:
            computed[group["full_tank"] != 1] = np.nan
        missing = df.loc[group.index, "consumption_l100"].isna()
        df.loc[group.index[missing], "consumption_l100"] = computed[missing]
    return df


def load_fuel_reports(folder_path: str) -> pd.DataFrame:
    """Собирает данные о заправках из папки на Google Диске.

    Приоритет у CSV-бэкапов Fuelio: они содержат каждую заправку
    отдельной строкой с координатами и номером бака, тогда как PDF —
    это уже свёрстанный отчёт, который приходится разбирать по тексту.
    PDF используется как запасной вариант, если CSV нет."""
    csv_frames = []
    for path in find_fuelio_csv_backups(folder_path):
        try:
            with open(path, "rb") as f:
                df = parse_fuelio_csv(f.read())
            if not df.empty:
                csv_frames.append(df)
        except Exception:
            continue

    if csv_frames:
        combined = pd.concat(csv_frames, ignore_index=True)
        combined = combined.drop_duplicates(subset=["date", "odo", "liters"])
        combined = combined.sort_values("datetime").reset_index(drop=True)
        combined = _compute_consumption_between_fillups(combined)
        combined.attrs["source"] = "csv"
        return combined

    pdf_paths = find_fuel_report_pdfs(folder_path)
    if not pdf_paths:
        return pd.DataFrame()

    frames = []
    for path in pdf_paths:
        try:
            with open(path, "rb") as f:
                file_bytes = f.read()
            df = parse_fuelio_pdf(file_bytes)
            if not df.empty:
                frames.append(df)
        except Exception:
            continue

    if not frames:
        return pd.DataFrame()

    combined = pd.concat(frames, ignore_index=True)
    combined = combined.drop_duplicates(subset=["date", "odo", "cost", "liters"])
    combined["datetime"] = pd.to_datetime(combined["date"])
    return combined.sort_values("datetime").reset_index(drop=True)



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


def _gps_frozen_ratio(df: pd.DataFrame) -> float:
    """Доля моментов, когда по данным OBD машина реально ехала
    (SPEED_OBD > 5 км/ч), но GPS-координата не изменилась относительно
    предыдущей точки. Частая ситуация: GPS-модуль ещё не поймал сигнал
    в первые секунды после старта, или сигнал теряется у эстакад/в
    туннелях. Высокое значение означает, что трек на карте показывает
    лишь часть реального маршрута — это ограничение исходных данных, а
    не ошибка отрисовки."""
    if df.empty or len(df) < 2 or "SPEED_OBD" not in df.columns:
        return 0.0
    df = df.sort_values("TIMESTAMP")
    same_as_prev = (df["GPS_LAT"].diff() == 0) & (df["GPS_LON"].diff() == 0)
    moving = df["SPEED_OBD"].fillna(0) > 5
    total_moving = int(moving.sum())
    if total_moving == 0:
        return 0.0
    return float((same_as_prev & moving).sum() / total_moving)


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

    df["datetime"] = _ms_to_local_datetime(df["TIMESTAMP"])
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

    trips["date"] = _ms_to_local_datetime(trips["TSFIN"])
    trips["distance"] = pd.to_numeric(trips["NKMS"], errors="coerce")
    # NBSEC — вопреки названию, это НЕ секунды, а число замеров за поездку
    # (проверено на реальном HTML-отчёте Hybrid Assistant: NBSEC совпало
    # с полем "Samples", а не с реальной длительностью поездки). Реальную
    # длительность считаем как разницу TSFIN-TSDEB.
    trips["duration_min"] = (trips["TSFIN"] - trips["TSDEB"]) / 1000.0 / 60.0

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
    combined["timestamp"] = _ms_to_local_datetime(combined["TIMESTAMP"])
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
    df["datetime"] = _ms_to_local_datetime(df["TIMESTAMP"])
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
# ПОГОДА В МОМЕНТ ПОЕЗДКИ (Open-Meteo, без ключа)
# ============================================================
# Погода берётся по координатам старта поездки и её времени. Open-Meteo
# отдаёт исторические данные бесплатно и без регистрации.
# Есть нюанс: архив ERA5 отстаёт примерно на 5 дней, поэтому для свежих
# поездок сначала пробуем обычный forecast-эндпоинт с past_days (он
# хранит до 92 дней назад), и только потом архивный.

_OPEN_METEO_ARCHIVE = "https://archive-api.open-meteo.com/v1/archive"
_OPEN_METEO_FORECAST = "https://api.open-meteo.com/v1/forecast"
_WEATHER_HOURLY_VARS = (
    "temperature_2m,precipitation,rain,snowfall,weather_code,"
    "wind_speed_10m,wind_direction_10m,shortwave_radiation,cloud_cover"
)

# Коды погоды WMO -> понятная человеку категория.
_WMO_GROUPS = [
    ((0,), "clear"),
    ((1, 2, 3), "cloudy"),
    ((45, 48), "fog"),
    ((51, 53, 55, 56, 57, 61, 63, 65, 66, 67, 80, 81, 82), "rain"),
    ((71, 73, 75, 77, 85, 86), "snow"),
    ((95, 96, 99), "thunder"),
]


def _wmo_group(code) -> str:
    if code is None or pd.isna(code):
        return "unknown"
    code = int(code)
    for codes, group in _WMO_GROUPS:
        if code in codes:
            return group
    return "unknown"


@st.cache_data(show_spinner=False, ttl=7 * 24 * 3600)
def fetch_trip_weather(lat: float, lon: float, day: str, hour_index: int) -> dict:
    """Возвращает погоду на конкретный час в конкретной точке.
    Пустой словарь означает, что данных получить не удалось — вызывающий
    код должен это корректно показать, а не выдумывать значения."""
    params = {
        "latitude": round(lat, 4),
        "longitude": round(lon, 4),
        "start_date": day,
        "end_date": day,
        "hourly": _WEATHER_HOURLY_VARS,
        "timezone": LOCAL_TIMEZONE,
    }
    for url in (_OPEN_METEO_FORECAST, _OPEN_METEO_ARCHIVE):
        try:
            resp = requests.get(url, params=params, timeout=12)
            if resp.status_code != 200:
                continue
            hourly = (resp.json() or {}).get("hourly") or {}
            times = hourly.get("time") or []
            if not times:
                continue
            idx = min(max(hour_index, 0), len(times) - 1)

            def val(key):
                seq = hourly.get(key) or []
                return seq[idx] if idx < len(seq) else None

            result = {
                "time": times[idx],
                "temperature": val("temperature_2m"),
                "precipitation": val("precipitation"),
                "rain": val("rain"),
                "snowfall": val("snowfall"),
                "weather_code": val("weather_code"),
                "wind_speed": val("wind_speed_10m"),
                "wind_direction": val("wind_direction_10m"),
                "solar_radiation": val("shortwave_radiation"),
                "cloud_cover": val("cloud_cover"),
                "source": "forecast" if url == _OPEN_METEO_FORECAST else "archive",
            }
            # Пустой ответ (все None) считаем неудачей и пробуем следующий источник.
            if result["temperature"] is not None:
                return result
        except Exception:
            continue
    return {}


def estimate_road_surface_temp(air_temp: float, solar_radiation: float) -> "float | None":
    """ОЦЕНКА температуры асфальта. Это упрощённая инженерная модель, а
    НЕ измерение: асфальт нагревается солнцем сильнее воздуха примерно
    пропорционально приходящей солнечной радиации, а ночью, наоборот,
    остывает излучением на 1-2 градуса ниже воздуха.
    Коэффициент 0.025 °C на Вт/м² даёт привычные +20 °C при ярком
    летнем солнце (~800 Вт/м²). Реальная температура зависит ещё от
    цвета и возраста покрытия, ветра и влажности, поэтому значение
    следует считать ориентировочным."""
    if air_temp is None or pd.isna(air_temp):
        return None
    radiation = 0.0 if (solar_radiation is None or pd.isna(solar_radiation)) else float(solar_radiation)
    if radiation <= 5:  # ночь или плотная облачность
        return round(float(air_temp) - 1.5, 1)
    return round(float(air_temp) + 0.025 * radiation, 1)


def _bearing_deg(lat1, lon1, lat2, lon2) -> "float | None":
    """Азимут движения из точки 1 в точку 2, в градусах от севера."""
    try:
        lat1, lon1, lat2, lon2 = map(math.radians, (lat1, lon1, lat2, lon2))
    except (TypeError, ValueError):
        return None
    dlon = lon2 - lon1
    x = math.sin(dlon) * math.cos(lat2)
    y = math.cos(lat1) * math.sin(lat2) - math.sin(lat1) * math.cos(lat2) * math.cos(dlon)
    return (math.degrees(math.atan2(x, y)) + 360) % 360


def estimate_headwind(wind_speed_kmh, wind_from_deg, travel_bearing_deg) -> "float | None":
    """Продольная составляющая ветра, км/ч. Положительное значение —
    встречный ветер, отрицательное — попутный. В метеорологии направление
    ветра указывается ОТКУДА он дует, что здесь и учитывается."""
    if any(v is None or pd.isna(v) for v in (wind_speed_kmh, wind_from_deg, travel_bearing_deg)):
        return None
    angle = math.radians(float(wind_from_deg) - float(travel_bearing_deg))
    return round(float(wind_speed_kmh) * math.cos(angle), 1)


def estimate_aero_penalty_pct(avg_speed_kmh, headwind_kmh) -> "float | None":
    """Насколько встречный ветер увеличивает аэродинамическое
    сопротивление. Сопротивление растёт как квадрат скорости набегающего
    потока, поэтому считаем ((V+W)^2 - V^2) / V^2.
    ВАЖНО: это прирост именно аэродинамической составляющей, а не общего
    расхода топлива — на городских скоростях аэродинамика составляет лишь
    часть потерь, поэтому реальный прирост расхода будет заметно меньше."""
    if any(v is None or pd.isna(v) for v in (avg_speed_kmh, headwind_kmh)):
        return None
    v = float(avg_speed_kmh)
    if v < 15:  # на малых скоростях аэродинамика почти не играет роли
        return None
    relative = v + float(headwind_kmh)
    if relative <= 0:
        return None
    return round((relative ** 2 - v ** 2) / (v ** 2) * 100.0, 1)


def _first_valid_gps(trip_log: pd.DataFrame) -> "tuple | None":
    """Первая достоверная координата поездки. Нулевые точки — это
    отсутствие GPS-фикса, а не место на нулевом острове."""
    if trip_log.empty or "GPS_LAT" not in trip_log.columns:
        return None
    valid = trip_log.dropna(subset=["GPS_LAT", "GPS_LON"])
    valid = valid[(valid["GPS_LAT"] != 0) | (valid["GPS_LON"] != 0)]
    if valid.empty:
        return None
    first = valid.iloc[0]
    last = valid.iloc[-1]
    return (
        float(first["GPS_LAT"]), float(first["GPS_LON"]),
        float(last["GPS_LAT"]), float(last["GPS_LON"]),
    )


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
        if st.button(t("map_code_close_button"), width="stretch"):
            st.session_state["map_dialog_completed"] = True
            st.session_state["map_unlocked"] = False
            st.rerun()
        return

    code_input = st.text_input(t("map_code_label"), type="password", key="map_code_dialog_input")

    col_check, col_close = st.columns(2)
    check_clicked = col_check.button(f"✅ {t('map_code_check_button')}", width="stretch")
    close_clicked = col_close.button(f"❌ {t('map_code_close_button')}", width="stretch")

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

# ============================================================
# ХРАНЕНИЕ ЖУРНАЛА ТО (Google Диск + локальный запасной вариант)
# ============================================================
# Контейнер Streamlit Cloud эфемерный: локальный maintenance.json
# обнуляется при каждом перезапуске приложения. Поэтому журнал
# хранится в той же папке Google Диска, что и база данных.
#
# ВАЖНО: gdown умеет только СКАЧИВАТЬ. Чтобы записывать файл обратно,
# нужен Google Drive API с сервисным аккаунтом. Настройка (один раз):
#   1. В Google Cloud Console создайте сервисный аккаунт и скачайте
#      его JSON-ключ.
#   2. Откройте доступ к папке на Google Диске для email этого
#      сервисного аккаунта с правом "Редактор".
#   3. Вставьте содержимое ключа в Secrets приложения в виде:
#        [gcp_service_account]
#        type = "service_account"
#        project_id = "..."
#        private_key = "-----BEGIN PRIVATE KEY-----\n...\n-----END PRIVATE KEY-----\n"
#        client_email = "...@....iam.gserviceaccount.com"
#        ... (остальные поля из JSON)
#
# Если сервисный аккаунт не настроен, приложение продолжает работать:
# журнал читается из скачанной копии папки, но новые записи сохраняются
# только локально и будут потеряны при перезапуске — о чём честно
# предупреждает интерфейс.

_DRIVE_SCOPES = ["https://www.googleapis.com/auth/drive"]

# ============================================================
# СТИЛИ ОТОБРАЖЕНИЯ КАРТ
# ============================================================
# Часть стилей встроена в Plotly (не требует ничего), часть
# подключается как растровые тайлы по ссылке.
# Stadia (Alidade Smooth Dark): бесплатно до 2500 просмотров в сутки для
# некоммерческого использования; ключ необязателен, но если он есть —
# положите его в Secrets как stadia_api_key, чтобы не упереться в лимит.
# Esri World Topo: бесплатно, без ключа. Внимание: у Esri порядок
# координат в ссылке {z}/{y}/{x}, а не {z}/{x}/{y}, как у большинства.

MAP_STYLE_OPTIONS = {
    "carto-darkmatter": {
        "builtin": "carto-darkmatter",
        "label": {"ru": "CartoDB Dark Matter (тёмная)", "pl": "CartoDB Dark Matter (ciemna)"},
    },
    "alidade-smooth-dark": {
        # Обычные тайлы 256px, а не @2x: MapLibre внутри Plotly считает
        # размер тайла равным 256, и retina-версия 512px выравнивается
        # неправильно. Качество чуть ниже, зато карта действительно видна.
        "raster": "https://tiles.stadiamaps.com/tiles/alidade_smooth_dark/{z}/{x}/{y}.png",
        "attribution": "© Stadia Maps © OpenMapTiles © OpenStreetMap contributors",
        "needs_key": True,
        "label": {"ru": "Alidade Smooth Dark", "pl": "Alidade Smooth Dark"},
    },
    "esri-world-topo": {
        "raster": "https://server.arcgisonline.com/ArcGIS/rest/services/World_Topo_Map/MapServer/tile/{z}/{y}/{x}",
        "attribution": "© Esri — Esri, DeLorme, NAVTEQ, TomTom, USGS",
        "label": {"ru": "Esri World Topo (рельеф)", "pl": "Esri World Topo (topograficzna)"},
    },
    "carto-positron": {
        "builtin": "carto-positron",
        "label": {"ru": "CartoDB Positron (светлая)", "pl": "CartoDB Positron (jasna)"},
    },
    "open-street-map": {
        "builtin": "open-street-map",
        "label": {"ru": "OpenStreetMap", "pl": "OpenStreetMap"},
    },
}

DEFAULT_MAP_STYLE = "carto-darkmatter"

# Имя секрета могло быть записано по-разному — принимаем несколько
# распространённых вариантов, чтобы ключ не «терялся» молча.
_STADIA_SECRET_NAMES = ("stadia_api_key", "STADIA_API_KEY", "stadia_key", "stadiamaps_api_key")


def get_stadia_api_key() -> "str | None":
    """Ищет ключ Stadia в Secrets.

    Отдельно проверяем вложенные секции: в TOML всё, что записано ПОСЛЕ
    заголовка вида [gcp_service_account], автоматически попадает внутрь
    этой секции. Если ключ дописали в конец файла, он оказывается не на
    верхнем уровне, а внутри чужой секции — и обычный поиск его не
    находит. Это самая частая причина «ключ записан, но не работает»."""
    try:
        secrets = st.secrets
    except Exception:
        return None

    for name in _STADIA_SECRET_NAMES:
        try:
            value = secrets.get(name)
        except Exception:
            value = None
        if value:
            return str(value).strip()

    # Обход вложенных секций.
    try:
        for section_value in secrets.values():
            if hasattr(section_value, "get"):
                for name in _STADIA_SECRET_NAMES:
                    nested = section_value.get(name)
                    if nested:
                        return str(nested).strip()
    except Exception:
        pass
    return None


def get_selected_map_style() -> str:
    style = st.session_state.get("map_style_choice", DEFAULT_MAP_STYLE)
    return style if style in MAP_STYLE_OPTIONS else DEFAULT_MAP_STYLE


def build_map_config(center_lat: float, center_lon: float, zoom: float) -> dict:
    """Собирает секцию map=... для Plotly с учётом выбранного стиля."""
    style_key = get_selected_map_style()
    cfg = MAP_STYLE_OPTIONS.get(style_key, MAP_STYLE_OPTIONS[DEFAULT_MAP_STYLE])
    base = {"center": {"lat": center_lat, "lon": center_lon}, "zoom": zoom}

    if "builtin" in cfg:
        base["style"] = cfg["builtin"]
        return base

    url = cfg["raster"]
    if cfg.get("needs_key"):
        api_key = get_stadia_api_key()
        if api_key:
            url = f"{url}?api_key={api_key}"

    base["style"] = "white-bg"
    base["layers"] = [
        {
            "below": "traces",
            "sourcetype": "raster",
            "sourceattribution": cfg.get("attribution", ""),
            "source": [url],
        }
    ]
    return base


def render_map_style_diagnostics() -> None:
    """Подсказка, если выбран стиль с внешними тайлами: видно ли ключ и
    что проверить, когда подложка не загрузилась."""
    style_key = get_selected_map_style()
    cfg = MAP_STYLE_OPTIONS.get(style_key, {})
    if not cfg.get("needs_key"):
        return
    if get_stadia_api_key():
        st.caption(t("map_stadia_key_found"))
    else:
        st.warning(t("map_stadia_key_missing"))




@st.cache_resource(show_spinner=False)
def get_drive_service():
    """Клиент Google Drive API, если настроен сервисный аккаунт."""
    try:
        sa_info = st.secrets.get("gcp_service_account")
    except Exception:
        return None
    if not sa_info:
        return None
    try:
        from google.oauth2 import service_account
        from googleapiclient.discovery import build

        creds = service_account.Credentials.from_service_account_info(
            dict(sa_info), scopes=_DRIVE_SCOPES
        )
        return build("drive", "v3", credentials=creds, cache_discovery=False)
    except Exception as e:
        print(f"[drive] не удалось создать клиент Drive API: {e!r}", flush=True)
        return None


def _find_drive_file_id(service, filename: str) -> "str | None":
    try:
        safe_name = filename.replace("'", "\\'")
        response = (
            service.files()
            .list(
                q=f"'{GDRIVE_FOLDER_ID}' in parents and name='{safe_name}' and trashed=false",
                fields="files(id, name)",
                supportsAllDrives=True,
                includeItemsFromAllDrives=True,
            )
            .execute()
        )
        files = response.get("files", [])
        return files[0]["id"] if files else None
    except Exception as e:
        print(f"[drive] поиск {filename} не удался: {e!r}", flush=True)
        return None


def load_maintenance_from_drive() -> "list | None":
    """Читает журнал напрямую с Google Диска. None означает, что
    прочитать не удалось (нет доступа/файла) — это НЕ то же самое, что
    пустой журнал, поэтому вызывающий код различает эти случаи."""
    service = get_drive_service()
    if service is None:
        return None
    file_id = _find_drive_file_id(service, MAINTENANCE_FILE)
    if not file_id:
        return None
    try:
        content = service.files().get_media(fileId=file_id, supportsAllDrives=True).execute()
        data = json.loads(content.decode("utf-8"))
        return data if isinstance(data, list) else None
    except Exception as e:
        print(f"[drive] чтение журнала не удалось: {e!r}", flush=True)
        return None


def save_maintenance_to_drive(records: list) -> bool:
    """Записывает журнал на Google Диск. True — успешно."""
    service = get_drive_service()
    if service is None:
        return False
    try:
        from googleapiclient.http import MediaInMemoryUpload

        payload = json.dumps(records, ensure_ascii=False, indent=2).encode("utf-8")
        media = MediaInMemoryUpload(payload, mimetype="application/json", resumable=False)
        file_id = _find_drive_file_id(service, MAINTENANCE_FILE)
        if file_id:
            service.files().update(fileId=file_id, media_body=media, supportsAllDrives=True).execute()
        else:
            service.files().create(
                body={"name": MAINTENANCE_FILE, "parents": [GDRIVE_FOLDER_ID]},
                media_body=media,
                fields="id",
                supportsAllDrives=True,
            ).execute()
        return True
    except Exception as e:
        print(f"[drive] запись журнала не удалась: {e!r}", flush=True)
        return False


def _load_maintenance_local() -> list:
    """Локальная копия журнала: сначала рабочая папка, затем — копия,
    скачанная вместе с базой из папки Google Диска."""
    for path in (MAINTENANCE_FILE, os.path.join(LOCAL_DB_FOLDER_PATH, MAINTENANCE_FILE)):
        if os.path.exists(path):
            try:
                with open(path, "r", encoding="utf-8") as f:
                    data = json.load(f)
                if isinstance(data, list):
                    return data
            except (json.JSONDecodeError, OSError):
                continue
    return []


def get_maintenance_storage_mode() -> str:
    """Как сейчас хранится журнал: 'drive' (надёжно, с синхронизацией),
    'drive_readonly' (файл виден с Диска, но записывать некуда) или
    'local' (только эфемерная копия в контейнере)."""
    if get_drive_service() is not None:
        return "drive"
    if os.path.exists(os.path.join(LOCAL_DB_FOLDER_PATH, MAINTENANCE_FILE)):
        return "drive_readonly"
    return "local"


def load_maintenance() -> list:
    """Журнал ТО. Приоритет у Google Диска — он переживает перезапуски
    контейнера, в отличие от локального файла."""
    if st.session_state.get("maintenance_cache_valid") and "maintenance_cache" in st.session_state:
        return st.session_state["maintenance_cache"]

    records = load_maintenance_from_drive()
    if records is None:
        records = _load_maintenance_local()

    st.session_state["maintenance_cache"] = records
    st.session_state["maintenance_cache_valid"] = True
    return records


def _make_invoice_thumbnail(raw_bytes: bytes, max_side: int = 1400, quality: int = 78) -> "str | None":
    """Уменьшенная JPEG-копия фактуры в base64. Фото с телефона весит
    несколько мегабайт, а журнал ТО читается целиком при каждом
    открытии вкладки — хранить оригиналы там нельзя."""
    try:
        from PIL import Image

        img = Image.open(io.BytesIO(raw_bytes))
        img = img.convert("RGB")
        img.thumbnail((max_side, max_side))
        buf = io.BytesIO()
        img.save(buf, format="JPEG", quality=quality, optimize=True)
        return base64.b64encode(buf.getvalue()).decode("ascii")
    except Exception:
        return None


def save_maintenance_record(record: dict) -> dict:
    """Добавляет запись в журнал. Возвращает результат сохранения, чтобы
    интерфейс мог честно сказать, попала запись на Google Диск или
    осталась только во временной копии контейнера."""
    records = load_maintenance()
    records.append(record)

    # Локальную копию пишем всегда — она страхует на случай, если Диск
    # временно недоступен, и служит источником в пределах сессии.
    local_ok = True
    try:
        with open(MAINTENANCE_FILE, "w", encoding="utf-8") as f:
            json.dump(records, f, ensure_ascii=False, indent=2)
    except OSError as e:
        local_ok = False
        print(f"[maintenance] локальная запись не удалась: {e!r}", flush=True)

    drive_ok = save_maintenance_to_drive(records)

    st.session_state["maintenance_cache"] = records
    st.session_state["maintenance_cache_valid"] = True
    return {"drive": drive_ok, "local": local_ok, "mode": get_maintenance_storage_mode()}


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
                "custom_no_record_message_key": item.get("custom_no_record_message_key"),
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
        # gemini-1.5-flash и gemini-2.0-flash полностью отключены Google
        # (2026 год), а gemini-2.5-flash планово отключается 16 октября
        # 2026. Используем официальный "плавающий" алиас gemini-flash-latest,
        # который Google сам переключает на актуальную модель — это
        # избавляет от необходимости вручную менять имя модели каждый раз,
        # когда очередная версия снимается с поддержки.
        model = genai.GenerativeModel("gemini-flash-latest")
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
    device_options = {"auto": t("device_auto"), "mobile": t("device_mobile"), "desktop": t("device_desktop")}
    current_choice = st.session_state.get("device_choice", "auto")
    chosen = st.sidebar.selectbox(
        t("device_label"),
        options=list(device_options.keys()),
        format_func=lambda k: device_options[k],
        index=list(device_options.keys()).index(current_choice),
        key="device_choice_select",
    )
    st.session_state["device_choice"] = chosen
    st.session_state["device_override"] = None if chosen == "auto" else chosen
    if chosen == "auto":
        detected_label = t("device_mobile") if is_mobile() else t("device_desktop")
        st.sidebar.caption(t("device_current").format(device=detected_label))

    st.sidebar.divider()
    lang_now = st.session_state.get("lang", "pl")
    style_keys = list(MAP_STYLE_OPTIONS.keys())
    current_style = get_selected_map_style()
    chosen_style = st.sidebar.selectbox(
        t("map_style_label"),
        options=style_keys,
        format_func=lambda k: MAP_STYLE_OPTIONS[k]["label"].get(lang_now, k),
        index=style_keys.index(current_style),
        key="map_style_select",
    )
    st.session_state["map_style_choice"] = chosen_style
    with st.sidebar:
        render_map_style_diagnostics()

    st.sidebar.divider()
    st.sidebar.caption(t("db_autorefresh_note"))
    if st.sidebar.button(t("refresh_db_button"), width="stretch"):
        last_refresh = st.session_state.get("db_refresh_triggered_at", 0.0)
        if time.time() - last_refresh < DB_REFRESH_COOLDOWN_SECONDS:
            st.sidebar.warning(t("refresh_in_progress_warning"))
        else:
            st.session_state["db_refresh_triggered_at"] = time.time()
            download_database.clear()
            st.rerun()


_MAP_PARAM_COLORS = {
    "mode": {"EV": "#FFC800", "ICE": "#E30000"},
    "braking": {"friction": "#E30000", "regen": "#2CA02C", "none": "#9AA0A6"},
    "speed": {"low": "#2CA02C", "medium": "#FF8C00", "high": "#E30000"},
    "soc": {"low": "#E30000", "medium": "#FF8C00", "high": "#2CA02C"},
}

_MAP_LEGEND_ITEMS = {
    "mode": [
        ("EV", {"ru": "EV (ДВС выключен)", "pl": "EV (silnik wyłączony)"}),
        ("ICE", {"ru": "ДВС работает", "pl": "Silnik pracuje"}),
    ],
    "braking": [
        ("friction", {"ru": "Механическое торможение", "pl": "Hamowanie mechaniczne"}),
        ("regen", {"ru": "Рекуперация", "pl": "Rekuperacja"}),
        ("none", {"ru": "Без торможения", "pl": "Bez hamowania"}),
    ],
    "speed": [
        ("low", {"ru": "До 30 км/ч", "pl": "Do 30 km/h"}),
        ("medium", {"ru": "30–60 км/ч", "pl": "30–60 km/h"}),
        ("high", {"ru": "Свыше 60 км/ч", "pl": "Powyżej 60 km/h"}),
    ],
    "soc": [
        ("low", {"ru": "Заряд < 30%", "pl": "Ładunek < 30%"}),
        ("medium", {"ru": "Заряд 30–70%", "pl": "Ładunek 30–70%"}),
        ("high", {"ru": "Заряд > 70%", "pl": "Ładunek > 70%"}),
    ],
}


def _drop_frozen_gps_samples(df: pd.DataFrame) -> pd.DataFrame:
    """Убирает точки, где GPS-координата не изменилась относительно
    предыдущей, а машина по OBD (SPEED_OBD) в этот момент реально
    двигалась — такие точки не отражают реальное положение машины и
    рисуют на карте оторванные "хвосты" вне дороги."""
    if df.empty or "SPEED_OBD" not in df.columns:
        return df
    df = df.sort_values("TIMESTAMP")
    same_as_prev = (df["GPS_LAT"].diff() == 0) & (df["GPS_LON"].diff() == 0)
    moving = df["SPEED_OBD"].fillna(0) > 5
    return df.loc[~(same_as_prev & moving)]


def _categorize_for_map(df: pd.DataFrame, parameter: str) -> pd.Series:
    if parameter == "mode":
        return df["mode"]
    if parameter == "braking":
        friction = df["BRK_MCYL_TRQ"].fillna(0) != 0
        regen = df["BRK_REG_TRQ"].fillna(0) != 0
        cat = pd.Series("none", index=df.index)
        cat[regen] = "regen"
        cat[friction] = "friction"
        return cat
    if parameter == "speed":
        speed = pd.to_numeric(df.get("SPEED_OBD"), errors="coerce").fillna(0)
        return pd.cut(speed, bins=[-1, 30, 60, 1e9], labels=["low", "medium", "high"]).astype(str)
    if parameter == "soc":
        soc = pd.to_numeric(df.get("SOC"), errors="coerce").fillna(50)
        return pd.cut(soc, bins=[-1, 30, 70, 101], labels=["low", "medium", "high"]).astype(str)
    return pd.Series("none", index=df.index)


def _render_map_legend(parameter: str) -> None:
    lang = st.session_state.get("lang", "pl")
    color_map = _MAP_PARAM_COLORS.get(parameter, {})
    items = _MAP_LEGEND_ITEMS.get(parameter, [])
    swatches = "".join(
        f'<span style="display:inline-flex;align-items:center;margin-right:18px;">'
        f'<span style="width:14px;height:14px;background:{color_map.get(key, "#888")};'
        f'display:inline-block;border-radius:3px;margin-right:6px;"></span>{label[lang]}</span>'
        for key, label in items
    )
    st.markdown(f'<div style="margin-top:6px;">{swatches}</div>', unsafe_allow_html=True)


def _build_route_map_figure(trip_log: pd.DataFrame, parameter: str = "mode") -> go.Figure:
    """Строит карту маршрута, окрашивая сегменты по выбранному
    параметру (режим EV/ДВС, торможение, скорость или заряд батареи)."""
    fig = go.Figure()
    trip_log = _filter_gps_outliers(trip_log)
    trip_log = _drop_frozen_gps_samples(trip_log)
    points = trip_log.dropna(subset=["GPS_LAT", "GPS_LON"]).reset_index(drop=True)

    if points.empty:
        return fig

    points["_category"] = _categorize_for_map(points, parameter)
    color_map = _MAP_PARAM_COLORS.get(parameter, _MAP_PARAM_COLORS["mode"])

    seg_start = 0
    for i in range(1, len(points) + 1):
        if i == len(points) or points.loc[i, "_category"] != points.loc[seg_start, "_category"]:
            seg = points.loc[seg_start : i - 1 + (1 if i < len(points) else 0)]
            category = points.loc[seg_start, "_category"]
            fig.add_trace(
                go.Scattermap(
                    lat=seg["GPS_LAT"],
                    lon=seg["GPS_LON"],
                    mode="lines",
                    line=dict(width=5, color=color_map.get(category, "#888888")),
                    showlegend=False,
                    hoverinfo="skip",
                )
            )
            seg_start = i

    center_lat = points["GPS_LAT"].mean()
    center_lon = points["GPS_LON"].mean()
    fig.update_layout(
        map=build_map_config(center_lat, center_lon, 13),
        margin=dict(l=0, r=0, t=0, b=0),
        height=rsp_height(450),
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
        custom_key = item.get("custom_no_record_message_key")
        if custom_key:
            st.warning(t(custom_key))
        elif item["status"] == "overdue" and item.get("km_since_baseline") is not None:
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
        "cvt_oil": {"ru": "Масло e-CVT (ATF WS)", "pl": "Olej e-CVT (ATF WS)"},
        "lpg_filters": {"ru": "ГБО: фильтры", "pl": "LPG: filtry"},
        "lpg_valves": {"ru": "ГБО: клапаны", "pl": "LPG: zawory"},
    }

    cols = st.columns(5)
    with cols[0]:
        _render_single_maintenance_item(by_key.get("oil"), titles["oil"][lang])
    with cols[1]:
        _render_single_maintenance_item(by_key.get("spark_plugs"), titles["spark_plugs"][lang])
    with cols[2]:
        _render_single_maintenance_item(by_key.get("coolant"), titles["coolant"][lang])
    with cols[3]:
        _render_single_maintenance_item(by_key.get("cvt_oil"), titles["cvt_oil"][lang])
    with cols[4]:
        gbo_title = {"ru": "ГБО", "pl": "LPG"}[lang]
        if not lpg_active:
            st.markdown(f"**{gbo_title}**")
            st.info(t("maint_gbo_not_installed"))
        else:
            _render_single_maintenance_item(by_key.get("lpg_filters"), titles["lpg_filters"][lang])
            _render_single_maintenance_item(by_key.get("lpg_valves"), titles["lpg_valves"][lang])


def _render_fuel_log_section(fuel_df: pd.DataFrame) -> None:
    """Блок реального расхода топлива (по чекам Fuelio): последние
    заправки LPG/бензина и график истории заправок с легендой."""
    st.subheader(t("fuel_log_title"))
    if fuel_df.empty:
        st.info(t("fuel_log_no_data"))
        return

    today = date.today()
    col1, col2 = st.columns(2)
    for col, ftype, label_key in ((col1, "lpg", "fuel_type_lpg"), (col2, "petrol", "fuel_type_petrol")):
        sub = fuel_df[fuel_df["fuel_type"] == ftype].sort_values("date")
        with col:
            st.markdown(f"**{t(label_key)}**")
            if sub.empty:
                st.info(t("fuel_log_no_data"))
                continue
            last = sub.iloc[-1]
            days_ago = (today - last["date"]).days
            st.metric(t("fuel_last_refuel_date"), last["date"].strftime("%Y-%m-%d"))
            c1, c2 = st.columns(2)
            c1.metric(t("fuel_liters"), f"{last['liters']:.2f} {t('unit_l')}")
            c2.metric(t("fuel_price"), f"{last['price']:.2f} {t('unit_price_per_l')}")
            st.caption(t("fuel_days_ago").format(days=days_ago))

            if ftype == "lpg":
                avg_cons = sub["consumption_l100"].dropna().mean()
                st.metric(
                    f"{t('fuel_avg_consumption')} {t('fuel_real_badge')}",
                    f'{avg_cons:.2f} {t("unit_l100km")}' if pd.notna(avg_cons) else "—",
                )
            else:
                st.markdown(f"**{t('fuel_avg_consumption')} {t('fuel_real_badge')}**")
                st.info(t("fuel_petrol_no_avg_note"))

    st.markdown(f"**{t('fuel_trend_title')}**")
    metric_options = {
        "days_since_last": t("fuel_metric_days"),
        "liters": t("fuel_metric_liters"),
        "cost": t("fuel_metric_cost"),
    }
    period_options = {t("map_period_month"): 30, t("map_period_year"): 365}

    c1, c2 = st.columns(2)
    with c1:
        selected_metric = st.selectbox(
            t("fuel_metric_label"), list(metric_options.keys()),
            format_func=lambda k: metric_options[k], key="fuel_trend_metric",
        )
    with c2:
        selected_period_label = st.selectbox(t("fuel_period_label"), list(period_options.keys()), key="fuel_trend_period")
    days_back = period_options[selected_period_label]

    plot_df = fuel_df.copy()
    plot_df["date"] = pd.to_datetime(plot_df["date"])
    plot_df["days_since_last"] = (
        plot_df.sort_values("date").groupby("fuel_type")["date"].diff().dt.days
    )
    cutoff = today - timedelta(days=days_back)
    plot_df = plot_df[plot_df["date"] >= pd.Timestamp(cutoff)]

    fig = go.Figure()
    for ftype, label_key, color in (("lpg", "fuel_type_lpg", "#FF8C00"), ("petrol", "fuel_type_petrol", "#1f77b4")):
        sub = plot_df[plot_df["fuel_type"] == ftype].sort_values("date")
        if sub.empty or selected_metric not in sub.columns:
            continue
        fig.add_trace(
            go.Scatter(x=sub["date"], y=sub[selected_metric], name=t(label_key), mode="lines+markers", line=dict(color=color))
        )
    if fig.data:
        fig.update_layout(height=rsp_height(350), yaxis_title=metric_options[selected_metric], legend=dict(orientation="h"))
        st.plotly_chart(fig, width="stretch", key="tab1_fuel_trend_chart")
    else:
        st.info(t("not_enough_data"))
    st.caption(t("fuel_real_badge_note"))


def render_trip_weather_section(trip_row, trip_log: pd.DataFrame) -> None:
    """Блок метеоусловий поездки + профиль высот."""
    st.subheader(t("weather_title"))

    coords = _first_valid_gps(trip_log)
    if coords is None:
        st.info(t("weather_no_gps"))
    else:
        lat, lon, lat_end, lon_end = coords
        start_dt = trip_log["datetime"].min()
        if pd.isna(start_dt):
            st.info(t("weather_no_time"))
        else:
            with st.spinner(t("weather_loading")):
                weather = fetch_trip_weather(
                    lat, lon, start_dt.strftime("%Y-%m-%d"), int(start_dt.hour)
                )

            if not weather:
                st.warning(t("weather_unavailable"))
            else:
                air_temp = weather.get("temperature")
                road_temp = estimate_road_surface_temp(air_temp, weather.get("solar_radiation"))
                group = _wmo_group(weather.get("weather_code"))
                lang = st.session_state.get("lang", "pl")
                condition_label = _WEATHER_CONDITION_LABELS.get(group, {}).get(lang, group)

                c1, c2, c3, c4 = st.columns(4)
                c1.metric(t("weather_air_temp"), f"{air_temp:.1f} °C" if air_temp is not None else "—")
                c2.metric(t("weather_condition"), condition_label)
                wind_speed = weather.get("wind_speed")
                wind_dir = weather.get("wind_direction")
                wind_text = "—"
                if wind_speed is not None:
                    wind_text = f"{wind_speed:.0f} {t('unit_kmh')}"
                    if wind_dir is not None:
                        wind_text += f" · {_compass_label(wind_dir, lang)}"
                c3.metric(t("weather_wind"), wind_text)
                c4.metric(
                    f"{t('weather_road_temp')} 🔮",
                    f"{road_temp:.1f} °C" if road_temp is not None else "—",
                    help=t("weather_road_temp_help"),
                )

                precip = weather.get("precipitation")
                if precip:
                    st.caption(t("weather_precip").format(mm=f"{precip:.1f}"))

                # --- Влияние на гибридную систему ---
                if air_temp is not None and air_temp < 5:
                    st.warning(t("weather_cold_warning"))

                travel_bearing = _bearing_deg(lat, lon, lat_end, lon_end)
                headwind = estimate_headwind(wind_speed, wind_dir, travel_bearing)
                if headwind is not None:
                    avg_speed = pd.to_numeric(trip_log.get("SPEED_OBD"), errors="coerce")
                    avg_speed = avg_speed[avg_speed > 0].mean() if avg_speed is not None else None
                    if headwind > 3:
                        penalty = estimate_aero_penalty_pct(avg_speed, headwind)
                        if penalty is not None:
                            st.warning(
                                t("weather_headwind").format(
                                    speed=f"{headwind:.0f}", pct=f"{penalty:.0f}"
                                )
                            )
                        else:
                            st.info(t("weather_headwind_slow").format(speed=f"{headwind:.0f}"))
                    elif headwind < -3:
                        st.success(t("weather_tailwind").format(speed=f"{abs(headwind):.0f}"))
                st.caption(t("weather_source_note"))

    # --- Профиль высот ---
    st.markdown(f"**{t('elevation_profile_title')}**")
    alt = pd.to_numeric(trip_log.get("GPS_ALT"), errors="coerce") if "GPS_ALT" in trip_log.columns else None
    if alt is None or alt.dropna().empty:
        st.info(t("elevation_no_data"))
        return

    profile = pd.DataFrame({"datetime": trip_log["datetime"], "alt": alt}).dropna()
    if profile["alt"].nunique() <= 1:
        st.info(t("elevation_flat"))
        return

    fig = go.Figure(
        go.Scatter(x=profile["datetime"], y=profile["alt"], mode="lines", fill="tozeroy",
                   line=dict(color="#8D6E63"), name=t("rep_altitude"))
    )
    fig.update_layout(
        height=rsp_height(280),
        yaxis_title=t("rep_altitude"),
        yaxis=dict(range=[profile["alt"].min() - 5, profile["alt"].max() + 5]),
        margin=dict(l=0, r=0, t=10, b=0),
    )
    st.plotly_chart(fig, width="stretch", key="tab1_elevation_profile")
    st.caption(t("rep_elevation_note"))


_WEATHER_CONDITION_LABELS = {
    "clear": {"ru": "Ясно", "pl": "Bezchmurnie"},
    "cloudy": {"ru": "Облачно", "pl": "Pochmurno"},
    "fog": {"ru": "Туман", "pl": "Mgła"},
    "rain": {"ru": "Дождь", "pl": "Deszcz"},
    "snow": {"ru": "Снег", "pl": "Śnieg"},
    "thunder": {"ru": "Гроза", "pl": "Burza"},
    "unknown": {"ru": "Нет данных", "pl": "Brak danych"},
}

_COMPASS = {
    "ru": ["С", "СВ", "В", "ЮВ", "Ю", "ЮЗ", "З", "СЗ"],
    "pl": ["N", "NE", "E", "SE", "S", "SW", "W", "NW"],
}


def _compass_label(degrees: float, lang: str) -> str:
    """Направление ветра словами (откуда дует)."""
    names = _COMPASS.get(lang, _COMPASS["pl"])
    return names[int((float(degrees) + 22.5) % 360 // 45)]


def render_tab1(trips_df, fastlog_df, temp_df, cell_df, db_path, file_version, fuel_df):
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
        f"{t('metric_avg_consumption')} {t('fuel_forecast_badge')}",
        f"{avg_consumption:.1f}" if pd.notna(avg_consumption) else "—",
        help=t("fuel_forecast_help"),
    )
    col4.metric(t("metric_soh"), f"{latest_soh:.0f}%" if latest_soh is not None else "—")

    st.divider()

    # --- Карты ---
    if maps_are_unlocked():
        st.subheader(t("map_section_title"))
        trip_options = {
            f"{row['date'].strftime('%Y-%m-%d %H:%M')} — {row['distance']:.1f} км": idx
            for idx, row in trips_df.sort_values("date", ascending=False).iterrows()
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
                param_options = {
                    "mode": t("map_param_mode"),
                    "braking": t("map_param_braking"),
                    "speed": t("map_param_speed"),
                    "soc": t("map_param_soc"),
                }
                # Если для этой поездки загружен HTML-отчёт, добавляем его
                # карты прямо сюда — включая те, что из базы не построить
                # (мгновенный расход, BSFC, оценка наката).
                ha_match = find_ha_report_for_trip(sel_row)
                ha_maps = {}
                if ha_match is not None:
                    ha_file_name, _ha_data = ha_match
                    ha_file_by_name = {f.name: f for f in get_uploaded_ha_files()}
                    ha_maps = parse_ha_html_maps(ha_file_by_name[ha_file_name].getvalue())
                    lang_now = st.session_state.get("lang", "pl")
                    for ha_name in ha_maps:
                        label = HA_MAP_TITLES.get(ha_name, {}).get(lang_now, ha_name)
                        param_options[f"ha::{ha_name}"] = f"📄 {label}"

                selected_param = st.selectbox(
                    t("map_param_label"),
                    options=list(param_options.keys()),
                    format_func=lambda k: param_options[k],
                    key="map_param_select",
                )
                if selected_param.startswith("ha::"):
                    ha_name = selected_param[4:]
                    render_ha_html_map(ha_name, ha_maps[ha_name], key_prefix="tab1")
                    st.caption(t("ha_maps_source_note"))
                else:
                    st.plotly_chart(_build_route_map_figure(trip_log, selected_param), width="stretch", key="tab1_route_map")
                    _render_map_legend(selected_param)
                    if _gps_frozen_ratio(trip_log) > 0.3:
                        st.warning(t("gps_signal_lost_warning"))

            ev_pct = sel_row.get("ev_pct")
            ice_pct = 100 - ev_pct if pd.notna(ev_pct) else None
            mcol1, mcol2, mcol3, mcol4, mcol5 = st.columns(5)
            mcol1.metric(t("metric_total_distance"), f"{sel_row['distance']:.1f}")
            mcol2.metric(t("metric_ev_pct"), f"{ev_pct:.0f}%" if pd.notna(ev_pct) else "—")
            mcol3.metric(t("metric_ice_pct"), f"{ice_pct:.0f}%" if ice_pct is not None else "—")
            mcol4.metric(f"{t('metric_fuel_ml')} {t('fuel_forecast_badge')}", f"{sel_row['fuel_ml']:.0f}" if pd.notna(sel_row.get("fuel_ml")) else "—", help=t("fuel_forecast_help"))
            mcol5.metric(t("metric_brake_events"), f"{int(sel_row['brake_events'])}" if pd.notna(sel_row.get("brake_events")) else "—")

            st.divider()
            render_trip_weather_section(sel_row, trip_log)
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
                    map=build_map_config(
                        points["GPS_LAT"].mean(), points["GPS_LON"].mean(), 10
                    ),
                    margin=dict(l=0, r=0, t=0, b=0),
                    height=rsp_height(400),
                )
                st.plotly_chart(grid_fig, width="stretch", key="tab1_period_map")
                if pd.notna(period_avg_consumption):
                    st.markdown(
                        f"### {t('map_period_avg_consumption').format(value=f'{period_avg_consumption:.1f}')} {t('fuel_forecast_badge')}"
                    )
                if freq == "D" and not fuel_df.empty:
                    day_fuel = fuel_df[fuel_df["date"] == period_start.date()]
                    for _, frow in day_fuel.iterrows():
                        fuel_label = t("fuel_type_lpg") if frow["fuel_type"] == "lpg" else t("fuel_type_petrol")
                        st.success(
                            t("map_day_refuel_note").format(
                                fuel=fuel_label,
                                liters=f"{frow['liters']:.2f}",
                                price=f"{frow['price']:.2f}",
                            )
                        )
            else:
                st.info(t("no_gps_data"))
    else:
        render_maps_locked_placeholder()

    st.divider()

    _render_fuel_log_section(fuel_df)

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


def _fmt_hms(seconds: float) -> str:
    """Форматирует секунды как H:MM:SS (или MM:SS, если меньше часа) —
    как в отчётах Hybrid Assistant."""
    if seconds is None or pd.isna(seconds):
        return "—"
    seconds = int(round(seconds))
    h, rem = divmod(seconds, 3600)
    m, s = divmod(rem, 60)
    return f"{h}:{m:02d}:{s:02d}" if h else f"{m}:{s:02d}"


def _integrate_kwh(timestamps_ms: np.ndarray, power_kw: np.ndarray, sign: str = "all") -> float:
    """Интегрирует мощность (кВт) по времени (мс) в энергию (кВт·ч).
    sign="pos"/"neg" — считать только положительные/отрицательные интервалы."""
    if len(timestamps_ms) < 2:
        return 0.0
    dt_h = np.diff(timestamps_ms) / 1000.0 / 3600.0
    p = power_kw[1:]
    if sign == "pos":
        mask = p > 0
    elif sign == "neg":
        mask = p < 0
    else:
        mask = np.ones_like(p, dtype=bool)
    return float(np.nansum(p[mask] * dt_h[mask]))


def _render_matrix_table(row_labels: list, col_labels: list, data: list, key: str) -> None:
    """Универсальная таблица со значениями (как в отчёте HA): строки —
    row_labels (Avg/Min/Max...), колонки — col_labels (Current/Voltage...)."""
    df = pd.DataFrame(data, index=row_labels, columns=col_labels)
    st.dataframe(df, width="stretch", key=key)


def compute_trip_report(trip_log: pd.DataFrame, trip_row: pd.Series, battlog_probe_log: pd.DataFrame) -> dict:
    """Считает все показатели детального отчёта по одной поездке на
    основе реальных колонок FASTLOG. Формулы проверены на реальном
    HTML-отчёте Hybrid Assistant для контрольной поездки (совпадения
    почти точные: BSFC, температуры, энергия ВВБ, высота и т.д.)."""
    df = trip_log.sort_values("TIMESTAMP").reset_index(drop=True)
    ts = df["TIMESTAMP"].to_numpy()
    n = len(df)
    report = {}

    def col(name):
        return pd.to_numeric(df[name], errors="coerce") if name in df.columns else pd.Series(dtype=float)

    speed = col("SPEED_OBD")
    ice_rpm = col("ICE_RPM")
    moving_mask = speed.fillna(0) > 0
    ev_mask = ice_rpm.fillna(0) == 0
    fuelflow = col("FUELFLOWH")
    no_fuel_mask = ev_mask | (fuelflow.fillna(0) == 0)

    total_seconds = (ts[-1] - ts[0]) / 1000.0 if n > 1 else 0.0
    dt_s = np.diff(ts) / 1000.0 if n > 1 else np.array([])

    def masked_seconds(mask_series):
        if n < 2:
            return 0.0
        m = mask_series.to_numpy()[1:]
        return float(np.nansum(dt_s[m]))

    report["summary"] = {
        "start": trip_row["date"] - pd.to_timedelta(total_seconds, unit="s") if False else None,
        "distance_total": trip_row.get("distance"),
        "distance_ev": trip_row.get("distance") * (df["TRIP_EV_DIST"].max() / df["TRIP_DIST"].max())
        if "TRIP_EV_DIST" in df.columns and "TRIP_DIST" in df.columns and pd.notna(df["TRIP_DIST"].max()) and df["TRIP_DIST"].max()
        else None,
        "time_total_s": total_seconds,
        "time_ev_s": masked_seconds(ev_mask),
        "time_moving_s": masked_seconds(moving_mask),
        "time_moving_ev_s": masked_seconds(moving_mask & ev_mask),
        "speed_avg": speed.mean(),
        "speed_moving_avg": speed[moving_mask].mean() if moving_mask.any() else None,
        "speed_ev_avg": speed[ev_mask & moving_mask].mean() if (ev_mask & moving_mask).any() else None,
        "speed_max": speed.max(),
        "soc_start": col("SOC").iloc[0] if n else None,
        "soc_end": col("SOC").iloc[-1] if n else None,
        "ambient_avg": col("AMBIENT_TEMP").mean(),
        "alt_start": col("GPS_ALT").iloc[0] if n and "GPS_ALT" in df.columns else None,
        "alt_end": col("GPS_ALT").iloc[-1] if n and "GPS_ALT" in df.columns else None,
    }

    fuel_ml = col("TRIPFUEL").max() if "TRIPFUEL" in df.columns else None
    dist = trip_row.get("distance")
    report["fuel"] = {
        "consumption_l100": (fuel_ml / 1000.0 / dist * 100.0) if fuel_ml and dist else None,
        "usage_l": (fuel_ml / 1000.0) if fuel_ml else None,
    }

    # --- SOC ---
    soc = col("SOC")
    report["soc"] = {
        "avg": soc.mean(), "start": soc.iloc[0] if n else None, "end": soc.iloc[-1] if n else None,
        "delta": (soc.iloc[-1] - soc.iloc[0]) if n else None, "min": soc.min(), "max": soc.max(), "std": soc.std(),
    }

    # --- HV Battery ---
    hv_v, hv_a = col("HV_V"), col("HV_A")
    hv_pwr_kw = (hv_v * hv_a / 1000.0) if not hv_v.empty else pd.Series(dtype=float)
    dcl, ccl = col("DCL"), col("CCL")
    report["hv_levels"] = {
        "current_avg": hv_a.mean(), "current_min": hv_a.min(), "current_max": hv_a.max(),
        "voltage_avg": hv_v.mean(), "voltage_min": hv_v.min(), "voltage_max": hv_v.max(),
    }
    report["hv_power"] = {
        "power_avg": hv_pwr_kw.mean(), "power_start": hv_pwr_kw.iloc[0] if n else None,
        "power_end": hv_pwr_kw.iloc[-1] if n else None, "power_min": hv_pwr_kw.min(), "power_max": hv_pwr_kw.max(),
        "ccl_avg": ccl.mean(), "ccl_min": ccl.min(), "ccl_max": ccl.max(),
        "dcl_avg": dcl.mean(), "dcl_min": dcl.min(), "dcl_max": dcl.max(),
    }
    from_batt = _integrate_kwh(ts, hv_pwr_kw.to_numpy(), "pos")
    to_batt = _integrate_kwh(ts, hv_pwr_kw.to_numpy(), "neg")
    report["hv_energy"] = {
        "from_battery": from_batt, "to_battery": -to_batt, "balance": (-to_batt) - from_batt,
        "avg_services_kw": None,
    }

    # --- Temperature ---
    report["temperature"] = {
        label: {
            "avg": col(colname).mean(), "min": col(colname).min(), "max": col(colname).max(),
        }
        for label, colname in [
            ("ambient", "AMBIENT_TEMP"), ("room", "ROOM_TEMP"), ("coolant", "ICE_TEMP"),
            ("inverter", "INVERTER_TEMP"), ("mg", "MG_TEMP"),
        ]
    }

    # HV battery multi-probe temps (только если есть BATTLOG за этот отрезок)
    probe_stats = {}
    if battlog_probe_log is not None and not battlog_probe_log.empty:
        probe_cols = [c for c in battlog_probe_log.columns if c.startswith("TB")]
        for c in probe_cols:
            s = pd.to_numeric(battlog_probe_log[c], errors="coerce")
            if s.notna().any():
                probe_stats[c] = {"avg": s.mean(), "min": s.min(), "max": s.max()}
    report["hv_probes"] = probe_stats

    # --- Elevation ---
    alt = col("GPS_ALT")
    if not alt.empty and alt.notna().any():
        alt_diff = alt.diff().fillna(0)
        report["elevation"] = {
            "avg": alt.mean(), "start": alt.iloc[0], "end": alt.iloc[-1],
            "min": alt.min(), "max": alt.max(),
            "upward": float(alt_diff[alt_diff > 0].sum()), "downward": float(-alt_diff[alt_diff < 0].sum()),
            "delta": float(alt.iloc[-1] - alt.iloc[0]),
        }
    else:
        report["elevation"] = None

    # --- Energy from petrol engine ---
    ice_pwr = col("ICE_PWR")
    energy_ice_kwh = _integrate_kwh(ts, ice_pwr.to_numpy(), "all") if not ice_pwr.empty else None
    report["energy_engine"] = {
        "energy_kwh": energy_ice_kwh,
        "energy_kwh_100km": (energy_ice_kwh / dist * 100.0) if energy_ice_kwh and dist else None,
    }

    # --- Engine ---
    ice_load = col("ICE_LOAD")
    report["engine"] = {
        "rpm_avg": ice_rpm.mean(), "rpm_max": ice_rpm.max(),
        "load_avg": ice_load.mean(), "load_max": ice_load.max(),
        "power_avg": ice_pwr.mean(), "power_max": ice_pwr.max(),
    }

    # Ignitions: подъёмы ICE_RPM 0 -> >0, короткие (<5 сек) считаются неэффективными
    ign_total, ign_ineff = 0, 0
    if n > 1:
        running = (ice_rpm.fillna(0) > 0).to_numpy()
        starts = np.where((~running[:-1]) & running[1:])[0] + 1
        for s_idx in starts:
            e_idx = s_idx
            while e_idx < n - 1 and running[e_idx]:
                e_idx += 1
            duration = (ts[e_idx] - ts[s_idx]) / 1000.0
            ign_total += 1
            if duration < 5:
                ign_ineff += 1
    report["ignitions"] = {"total": ign_total, "inefficient": ign_ineff}

    ice_state_running = masked_seconds(pd.Series(ice_rpm.fillna(0) > 0, index=df.index) & (fuelflow.fillna(0) > 0))
    ice_state_spinning = masked_seconds(pd.Series(ice_rpm.fillna(0) > 0, index=df.index) & (fuelflow.fillna(0) == 0))
    ice_state_off = total_seconds - ice_state_running - ice_state_spinning
    report["engine_state"] = {
        "running_s": ice_state_running, "spinning_s": ice_state_spinning, "off_s": max(0.0, ice_state_off),
    }

    ev_dist = report["summary"]["distance_ev"]
    report["ev_stats"] = {"trip_length": dist, "ev_range": ev_dist}

    # --- PSD (расчётный крутящий момент ДВС из мощности и оборотов) ---
    ice_torque_est = (ice_pwr * 1000.0) / (ice_rpm.replace(0, np.nan) * 2 * np.pi / 60.0)
    report["psd"] = {
        "ice_rpm_avg": ice_rpm.mean(), "ice_rpm_max": ice_rpm.max(),
        "ice_torque_avg": ice_torque_est.mean(), "ice_torque_max": ice_torque_est.max(),
        "mg1_rpm_avg": col("MG1_RPM").mean(), "mg1_rpm_max": col("MG1_RPM").max(),
        "mg2_rpm_avg": col("MG2_RPM").mean(), "mg2_rpm_max": col("MG2_RPM").max(),
        "mg1_torque_avg": col("MG1_TORQUE").mean(), "mg1_torque_max": col("MG1_TORQUE").max(),
        "mg2_torque_avg": col("MG2_TORQUE").mean(), "mg2_torque_max": col("MG2_TORQUE").max(),
    }

    # --- Fuel Trims ---
    ltft, stft = col("LTFT"), col("STFT")
    effective = ltft.fillna(0) + stft.fillna(0)
    report["fuel_trim"] = {
        "st_avg": stft.mean(), "st_min": stft.min(), "st_max": stft.max(),
        "lt_avg": ltft.mean(), "lt_min": ltft.min(), "lt_max": ltft.max(),
        "eff_avg": effective[stft.notna() | ltft.notna()].mean() if (stft.notna() | ltft.notna()).any() else None,
        "eff_min": effective[stft.notna() | ltft.notna()].min() if (stft.notna() | ltft.notna()).any() else None,
        "eff_max": effective[stft.notna() | ltft.notna()].max() if (stft.notna() | ltft.notna()).any() else None,
    }

    # --- BSFC (усредняется только по ненулевым значениям — так же, как в HA) ---
    bsfc = col("BSFC")
    bsfc_valid = bsfc[bsfc > 0]
    report["bsfc"] = {
        "avg": bsfc_valid.mean() if not bsfc_valid.empty else None,
        "std": bsfc_valid.std() if not bsfc_valid.empty else None,
    }

    # --- Braking ---
    friction = col("BRK_MCYL_TRQ").fillna(0) != 0
    regen = col("BRK_REG_TRQ").fillna(0) != 0
    braking_active = friction | regen
    edges = braking_active.astype(int).diff().fillna(0)
    brake_starts = df.index[edges == 1].tolist()
    brake_ends = df.index[edges == -1].tolist()
    if braking_active.iloc[0]:
        brake_starts = [0] + brake_starts
    if braking_active.iloc[-1]:
        brake_ends = brake_ends + [n - 1]

    good, bad, mixed, longest = 0, 0, 0, 0.0
    for s_idx, e_idx in zip(brake_starts, brake_ends):
        seg_friction = friction.iloc[s_idx:e_idx + 1].any()
        seg_regen = regen.iloc[s_idx:e_idx + 1].any()
        duration = (ts[e_idx] - ts[s_idx]) / 1000.0
        longest = max(longest, duration)
        if seg_regen and seg_friction:
            mixed += 1
        elif seg_regen:
            good += 1
        elif seg_friction:
            bad += 1

    total_brakings = good + bad + mixed
    regen_energy = -_integrate_kwh(ts, hv_pwr_kw.where(regen, 0).to_numpy(), "neg") if not hv_pwr_kw.empty else 0.0
    report["braking"] = {
        "total": total_brakings, "good": good, "bad": bad, "mixed": mixed,
        "efficiency_pct": (good / total_brakings * 100.0) if total_brakings else None,
        "moving_pct": (masked_seconds(braking_active) / report["summary"]["time_moving_s"] * 100.0)
        if report["summary"]["time_moving_s"] else None,
        "longest_s": longest, "energy_recovered_kwh": regen_energy,
    }

    # --- Driver evaluation ---
    accel = col("ACCELERATOR")
    report["driver_eval"] = {
        "accel_nervousness": accel.diff().abs().mean() if accel.notna().any() else None,
        "braking_efficiency_pct": report["braking"]["efficiency_pct"],
        "inefficient_ignitions": ign_ineff, "total_ignitions": ign_total,
    }

    # --- Glide (по колонке GLIDEINDEX, приблизительно) ---
    glide = col("GLIDEINDEX")
    report["glide"] = {
        "avg": glide.mean() if glide.notna().any() else None,
        "max": glide.max() if glide.notna().any() else None,
    }

    return report


def render_trip_report_sections(report: dict, lang: str) -> None:
    """Отрисовывает вычисленный отчёт по секциям (сворачиваемые блоки),
    как в HTML-отчёте Hybrid Assistant, полностью на выбранном языке."""

    def fmt(v, unit="", digits=1):
        if v is None or (isinstance(v, float) and pd.isna(v)):
            return "—"
        return f"{v:,.{digits}f}{unit}".replace(",", " ")

    lbl = {
        "avg": {"ru": "Среднее", "pl": "Średnia"}, "min": {"ru": "Мин.", "pl": "Min"},
        "max": {"ru": "Макс.", "pl": "Maks"}, "start": {"ru": "Начало", "pl": "Start"},
        "end": {"ru": "Конец", "pl": "Koniec"}, "delta": {"ru": "Дельта", "pl": "Delta"},
        "std": {"ru": "Ст. откл.", "pl": "Odch. std"},
    }
    L = lambda k: lbl[k][lang]

    with st.expander(t("rep_summary_title"), expanded=True):
        s, f = report["summary"], report["fuel"]
        st.markdown(f"**{t('rep_trip')}**")
        _render_matrix_table(
            [t("rep_distance"), t("rep_time"), t("rep_moving")],
            [t("rep_total"), t("rep_ev"), "%"],
            [
                [fmt(s["distance_total"], " km"), fmt(s["distance_ev"], " km"),
                 fmt((s["distance_ev"] / s["distance_total"] * 100) if s["distance_ev"] and s["distance_total"] else None, "%", 0)],
                [_fmt_hms(s["time_total_s"]), _fmt_hms(s["time_ev_s"]),
                 fmt((s["time_ev_s"] / s["time_total_s"] * 100) if s["time_total_s"] else None, "%", 0)],
                [_fmt_hms(s["time_moving_s"]), _fmt_hms(s["time_moving_ev_s"]),
                 fmt((s["time_moving_ev_s"] / s["time_moving_s"] * 100) if s["time_moving_s"] else None, "%", 0)],
            ],
            key="matrix_table_1",
        )
        c1, c2, c3 = st.columns(3)
        c1.metric(t("rep_speed_avg"), fmt(s["speed_avg"], f' {t("unit_kmh")}', 0))
        c2.metric(t("rep_speed_max"), fmt(s["speed_max"], f' {t("unit_kmh")}', 0))
        c3.metric(t("rep_speed_ev_avg"), fmt(s["speed_ev_avg"], f' {t("unit_kmh")}', 0))
        c4, c5, c6 = st.columns(3)
        c4.metric(t("rep_soc_start_end"), f"{fmt(s['soc_start'], '%', 0)} → {fmt(s['soc_end'], '%', 0)}")
        c5.metric(t("rep_ambient_avg"), fmt(s["ambient_avg"], " °C", 0))
        c6.metric(f"{t('rep_fuel_consumption')} {t('fuel_forecast_badge')}", fmt(f["consumption_l100"], f' {t("unit_l100km")}', 2), help=t("fuel_forecast_help"))
        st.caption(t("rep_ev_time_note"))

    with st.expander(t("rep_soc_title")):
        soc = report["soc"]
        _render_matrix_table(
            [L("avg"), L("start"), L("end"), L("delta"), L("min"), L("max"), L("std")],
            ["SOC"],
            [[fmt(soc[k], "%", 2)] for k in ("avg", "start", "end", "delta", "min", "max", "std")],
            key="matrix_table_2",
        )
        st.caption(t("rep_soc_note"))

    with st.expander(t("rep_hv_title")):
        lv, pw, en = report["hv_levels"], report["hv_power"], report["hv_energy"]
        st.markdown(f"**{t('rep_hv_levels')}**")
        _render_matrix_table(
            [L("avg"), L("min"), L("max")], [t("rep_current"), t("rep_voltage")],
            [
                [fmt(lv["current_avg"], " A"), fmt(lv["voltage_avg"], " V", 0)],
                [fmt(lv["current_min"], " A"), fmt(lv["voltage_min"], " V", 0)],
                [fmt(lv["current_max"], " A"), fmt(lv["voltage_max"], " V", 0)],
            ],
            key="matrix_table_3",
        )
        st.markdown(f"**{t('rep_hv_power')}**")
        _render_matrix_table(
            [L("avg"), L("min"), L("max")], [t("rep_power"), "CCL", "DCL"],
            [
                [fmt(pw["power_avg"], " kW", 2), fmt(pw["ccl_avg"], " kW", 1), fmt(pw["dcl_avg"], " kW", 1)],
                [fmt(pw["power_min"], " kW", 2), fmt(pw["ccl_min"], " kW", 1), fmt(pw["dcl_min"], " kW", 1)],
                [fmt(pw["power_max"], " kW", 2), fmt(pw["ccl_max"], " kW", 1), fmt(pw["dcl_max"], " kW", 1)],
            ],
            key="matrix_table_4",
        )
        c1, c2, c3 = st.columns(3)
        c1.metric(t("rep_hv_from_batt"), fmt(en["from_battery"], " kWh", 3))
        c2.metric(t("rep_hv_to_batt"), fmt(en["to_battery"], " kWh", 3))
        c3.metric(t("rep_hv_balance"), fmt(en["balance"], " kWh", 3))
        st.caption(t("rep_ccl_dcl_note"))

    with st.expander(t("rep_temp_title")):
        temps = report["temperature"]
        temp_labels = {
            "ambient": t("rep_temp_ambient"), "room": t("rep_temp_room"), "coolant": t("rep_temp_coolant"),
            "inverter": t("rep_temp_inverter"), "mg": t("rep_temp_mg"),
        }
        _render_matrix_table(
            [L("avg"), L("min"), L("max")],
            [temp_labels[k] for k in ("ambient", "room", "coolant", "inverter", "mg")],
            [
                [fmt(temps[k]["avg"], " °C", 0) for k in ("ambient", "room", "coolant", "inverter", "mg")],
                [fmt(temps[k]["min"], " °C", 0) for k in ("ambient", "room", "coolant", "inverter", "mg")],
                [fmt(temps[k]["max"], " °C", 0) for k in ("ambient", "room", "coolant", "inverter", "mg")],
            ],
            key="matrix_table_5",
        )
        if report["hv_probes"]:
            st.markdown(f"**{t('rep_hv_probes')}**")
            probes = report["hv_probes"]
            names = list(probes.keys())
            _render_matrix_table(
                [L("avg"), L("min"), L("max")], names,
                [
                    [fmt(probes[k]["avg"], " °C", 0) for k in names],
                    [fmt(probes[k]["min"], " °C", 0) for k in names],
                    [fmt(probes[k]["max"], " °C", 0) for k in names],
                ],
                key="matrix_table_6",
            )
        else:
            st.caption(t("logs_no_battlog"))

    if report["elevation"]:
        with st.expander(t("rep_elevation_title")):
            e = report["elevation"]
            _render_matrix_table(
                [t("rep_altitude")],
                [L("avg"), L("start"), L("end"), L("min"), L("max"), t("rep_upward"), t("rep_downward"), L("delta")],
                [[fmt(e[k], " м", 0) for k in ("avg", "start", "end", "min", "max", "upward", "downward", "delta")]],
                key="matrix_table_7",
            )
            st.caption(t("rep_elevation_note"))

    with st.expander(t("rep_energy_title")):
        ee = report["energy_engine"]
        c1, c2 = st.columns(2)
        c1.metric(t("rep_energy_from_ice"), fmt(ee["energy_kwh"], " kWh", 2))
        c2.metric(t("rep_energy_per_100km"), fmt(ee["energy_kwh_100km"], " kWh/100км", 2))

    with st.expander(t("rep_engine_title")):
        eng, ign, es = report["engine"], report["ignitions"], report["engine_state"]
        _render_matrix_table(
            [L("avg"), L("max")], ["RPM", t("rep_load"), t("rep_power")],
            [
                [fmt(eng["rpm_avg"], "", 0), fmt(eng["load_avg"], "%", 0), fmt(eng["power_avg"], " kW", 2)],
                [fmt(eng["rpm_max"], "", 0), fmt(eng["load_max"], "%", 0), fmt(eng["power_max"], " kW", 2)],
            ],
            key="matrix_table_8",
        )
        c1, c2 = st.columns(2)
        c1.metric(t("rep_ignitions_total"), ign["total"])
        c2.metric(t("rep_ignitions_inefficient"), ign["inefficient"])
        st.caption(t("rep_ignitions_note"))
        st.markdown(f"**{t('rep_engine_state')}**")
        total_t = max(report["summary"]["time_total_s"], 1e-6)
        _render_matrix_table(
            [t("rep_ice_running"), t("rep_ice_spinning"), t("rep_ice_off")], ["%", t("rep_time")],
            [
                [fmt(es["running_s"] / total_t * 100, "%", 0), _fmt_hms(es["running_s"])],
                [fmt(es["spinning_s"] / total_t * 100, "%", 0), _fmt_hms(es["spinning_s"])],
                [fmt(es["off_s"] / total_t * 100, "%", 0), _fmt_hms(es["off_s"])],
            ],
            key="matrix_table_9",
        )
        st.caption(t("rep_engine_state_note"))

    with st.expander(t("rep_psd_title")):
        p = report["psd"]
        _render_matrix_table(
            [L("avg"), L("max")],
            ["ICE RPM", t("rep_ice_torque"), "MG1 RPM", "MG2 RPM", "MG1 Nm", "MG2 Nm"],
            [
                [fmt(p["ice_rpm_avg"], "", 0), fmt(p["ice_torque_avg"], " Nm", 0), fmt(p["mg1_rpm_avg"], "", 0),
                 fmt(p["mg2_rpm_avg"], "", 0), fmt(p["mg1_torque_avg"], "", 0), fmt(p["mg2_torque_avg"], "", 0)],
                [fmt(p["ice_rpm_max"], "", 0), fmt(p["ice_torque_max"], " Nm", 0), fmt(p["mg1_rpm_max"], "", 0),
                 fmt(p["mg2_rpm_max"], "", 0), fmt(p["mg1_torque_max"], "", 0), fmt(p["mg2_torque_max"], "", 0)],
            ],
            key="matrix_table_10",
        )
        st.caption(t("rep_psd_note"))

    with st.expander(t("rep_trims_title")):
        ft = report["fuel_trim"]
        _render_matrix_table(
            [L("avg"), L("min"), L("max")], ["STFT", "LTFT", t("rep_effective")],
            [
                [fmt(ft["st_avg"], "%", 1), fmt(ft["lt_avg"], "%", 1), fmt(ft["eff_avg"], "%", 1)],
                [fmt(ft["st_min"], "%", 1), fmt(ft["lt_min"], "%", 1), fmt(ft["eff_min"], "%", 1)],
                [fmt(ft["st_max"], "%", 1), fmt(ft["lt_max"], "%", 1), fmt(ft["eff_max"], "%", 1)],
            ],
            key="matrix_table_11",
        )

    with st.expander(t("rep_bsfc_title")):
        b = report["bsfc"]
        c1, c2 = st.columns(2)
        c1.metric(t("rep_bsfc_avg"), fmt(b["avg"], " g/kWh", 0))
        c2.metric(t("rep_bsfc_std"), fmt(b["std"], "", 0))
        st.caption(t("rep_bsfc_note"))

    with st.expander(t("rep_braking_title")):
        br = report["braking"]
        c1, c2, c3, c4 = st.columns(4)
        c1.metric(t("rep_brakings_total"), br["total"])
        c2.metric(t("rep_brakings_good"), br["good"])
        c3.metric(t("rep_brakings_bad"), br["bad"])
        c4.metric(t("rep_brakings_mixed"), br["mixed"])
        c5, c6 = st.columns(2)
        c5.metric(t("rep_braking_efficiency"), fmt(br["efficiency_pct"], "%", 1))
        c6.metric(t("rep_energy_recovered"), fmt(br["energy_recovered_kwh"], " kWh", 3))
        st.caption(t("rep_braking_note"))

    with st.expander(t("rep_driver_eval_title")):
        de = report["driver_eval"]
        c1, c2, c3 = st.columns(3)
        c1.metric(t("rep_accel_nervousness"), fmt(de["accel_nervousness"], "", 2))
        c2.metric(t("rep_braking_efficiency"), fmt(de["braking_efficiency_pct"], "%", 1))
        c3.metric(t("rep_ignitions_inefficient"), f"{de['inefficient_ignitions']}/{de['total_ignitions']}")
        st.caption(t("rep_driver_eval_note"))

    with st.expander(t("rep_glide_title")):
        g = report["glide"]
        c1, c2 = st.columns(2)
        c1.metric(t("rep_glide_avg"), fmt(g["avg"], "", 1))
        c2.metric(t("rep_glide_max"), fmt(g["max"], "", 1))
        st.caption(t("rep_glide_note"))


def render_tab2(trips_df, fastlog_df, db_path, file_version):
    if trips_df.empty or fastlog_df.empty:
        st.info(t("no_trip_data"))
        return

    trip_options = {
        f"{row['date'].strftime('%Y-%m-%d %H:%M')} — {row['distance']:.1f} км": idx
        for idx, row in trips_df.sort_values("date", ascending=False).iterrows()
    }
    selected_label = st.selectbox(t("logs_select_trip"), list(trip_options.keys()), key="tab2_trip_select")
    sel_idx = trip_options[selected_label]
    sel_row = trips_df.loc[sel_idx]
    mask = (fastlog_df["TIMESTAMP"] >= sel_row["TSDEB"]) & (fastlog_df["TIMESTAMP"] <= sel_row["TSFIN"])
    trip_log = fastlog_df.loc[mask].sort_values("TIMESTAMP")

    if trip_log.empty:
        st.info(t("no_log_data"))
        return

    lang = st.session_state.get("lang", "pl")

    battlog = load_battlog_probes(db_path, file_version) if db_path else pd.DataFrame()
    battlog_probe_log = pd.DataFrame()
    if not battlog.empty:
        probe_mask = (battlog["TIMESTAMP"] >= sel_row["TSDEB"]) & (battlog["TIMESTAMP"] <= sel_row["TSFIN"])
        battlog_probe_log = battlog.loc[probe_mask]

    report = compute_trip_report(trip_log, sel_row, battlog_probe_log)
    render_trip_report_sections(report, lang)

    # --- Карта поездки (тот же виджет, что и на вкладке "Аналитика") ---
    with st.expander(t("ha_trip_extras_title")):
        render_ha_trip_extras(sel_row)

    with st.expander(t("rep_maps_title")):
        if maps_are_unlocked():
            if trip_log[["GPS_LAT", "GPS_LON"]].dropna().empty:
                st.info(t("no_gps_data"))
            else:
                param_options = {
                    "mode": t("map_param_mode"),
                    "braking": t("map_param_braking"),
                    "speed": t("map_param_speed"),
                    "soc": t("map_param_soc"),
                }
                selected_param = st.selectbox(
                    t("map_param_label"),
                    options=list(param_options.keys()),
                    format_func=lambda k: param_options[k],
                    key="tab2_map_param_select",
                )
                st.plotly_chart(_build_route_map_figure(trip_log, selected_param), width="stretch", key="tab2_route_map")
                _render_map_legend(selected_param)
                if _gps_frozen_ratio(trip_log) > 0.3:
                    st.warning(t("gps_signal_lost_warning"))
        else:
            render_maps_locked_placeholder()

    # --- Подробные посекундные графики ---
    with st.expander(t("rep_charts_title")):
        st.markdown(f"#### {t('logs_chart_speed_rpm')}")
        fig1 = go.Figure()
        fig1.add_trace(go.Scatter(x=trip_log["datetime"], y=trip_log["SPEED_OBD"], name=f'Speed ({t("unit_kmh")})', line=dict(color="#1f77b4")))
        fig1.add_trace(go.Scatter(x=trip_log["datetime"], y=trip_log["ICE_RPM"], name="ICE RPM", yaxis="y2", line=dict(color="#d62728")))
        fig1.update_layout(
            yaxis=dict(title=t("unit_kmh")),
            yaxis2=dict(title=t("unit_rpm"), overlaying="y", side="right"),
            height=rsp_height(380),
            legend=dict(orientation="h"),
        )
        st.plotly_chart(fig1, width="stretch", key="tab2_chart_speed_rpm")

        st.markdown(f"#### {t('logs_chart_hv')}")
        fig2 = go.Figure()
        fig2.add_trace(go.Scatter(x=trip_log["datetime"], y=trip_log["HV_V"], name="HV_V (В)", line=dict(color="#2ca02c")))
        fig2.add_trace(go.Scatter(x=trip_log["datetime"], y=trip_log["HV_A"], name="HV_A (А)", yaxis="y2", line=dict(color="#ff7f0e")))
        fig2.update_layout(
            yaxis=dict(title="В"),
            yaxis2=dict(title="А", overlaying="y", side="right"),
            height=rsp_height(380),
            legend=dict(orientation="h"),
        )
        st.plotly_chart(fig2, width="stretch", key="tab2_chart_hv")

        st.markdown(f"#### {t('logs_chart_temps')}")
        fig3 = go.Figure()
        fig3.add_trace(go.Scatter(x=trip_log["datetime"], y=trip_log["ICE_TEMP"], name="ДВС", line=dict(color="#d62728")))
        fig3.add_trace(go.Scatter(x=trip_log["datetime"], y=trip_log["INVERTER_TEMP"], name="Инвертор", line=dict(color="#ff7f0e")))
        fig3.add_trace(go.Scatter(x=trip_log["datetime"], y=trip_log["BATTERY_TEMP"], name="ВВБ (среднее)", line=dict(color="#9467bd")))
        if not battlog_probe_log.empty:
            probe_cols = [c for c in ["TB1", "TB2", "TB3"] if c in battlog_probe_log.columns and battlog_probe_log[c].notna().any()]
            if probe_cols:
                for c in probe_cols:
                    fig3.add_trace(go.Scatter(x=battlog_probe_log["datetime"], y=battlog_probe_log[c], name=f"ВВБ {c}", line=dict(dash="dot")))
                st.caption(t("logs_battlog_note"))
            else:
                st.caption(t("logs_no_battlog"))
        else:
            st.caption(t("logs_no_battlog"))
        fig3.update_layout(yaxis=dict(title="°C"), height=rsp_height(380), legend=dict(orientation="h"))
        st.plotly_chart(fig3, width="stretch", key="tab2_chart_temps")

        st.markdown(f"#### {t('logs_chart_mg')}")
        fig4 = go.Figure()
        fig4.add_trace(go.Scatter(x=trip_log["datetime"], y=trip_log["MG1_TORQUE"], name="MG1 момент (Нм)", line=dict(color="#17becf")))
        fig4.add_trace(go.Scatter(x=trip_log["datetime"], y=trip_log["MG2_TORQUE"], name="MG2 момент (Нм)", line=dict(color="#bcbd22")))
        fig4.add_trace(go.Scatter(x=trip_log["datetime"], y=trip_log["MG1_RPM"], name=f'MG1 {t("unit_rpm")}', yaxis="y2", line=dict(color="#17becf", dash="dot")))
        fig4.add_trace(go.Scatter(x=trip_log["datetime"], y=trip_log["MG2_RPM"], name=f'MG2 {t("unit_rpm")}', yaxis="y2", line=dict(color="#bcbd22", dash="dot")))
        fig4.update_layout(
            yaxis=dict(title=t("unit_nm")),
            yaxis2=dict(title=t("unit_rpm"), overlaying="y", side="right"),
            height=rsp_height(380),
            legend=dict(orientation="h"),
        )
        st.plotly_chart(fig4, width="stretch", key="tab2_chart_mg")
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
        fig_r.update_layout(height=rsp_height(350))
        st.plotly_chart(fig_r, width="stretch", key="tab3_resistance_chart")

    if any(v is not None for v in voltages):
        st.markdown(f"#### {t('drprius_voltage_chart')}")
        fig_v = go.Figure(go.Bar(x=[f"#{b}" for b in block_nums], y=voltages, marker_color="#2ca02c"))
        fig_v.update_layout(height=rsp_height(350))
        st.plotly_chart(fig_v, width="stretch", key="tab3_voltage_chart")

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


# ============================================================
# HTML-ОТЧЁТЫ HYBRID ASSISTANT (для трендов, которых нет в БД)
# ============================================================
# Почти все показатели самого отчёта уже честно вычисляются из
# hybridassistant.db (см. compute_trip_report) и совпадают с отчётом
# почти до знака. Но несколько фирменных расчётов Hybrid Assistant НЕ
# хранятся как отдельные колонки в базе и есть только в готовом виде
# в HTML-отчёте: разбивка SOC по источникам заряда (рекуперация /
# накат / ДВС), индекс и тип наката (Glide) и итоговая оценка стиля
# вождения. Именно их мы вытаскиваем из HTML для отслеживания трендов.

def _ha_section_tables(soup: BeautifulSoup, section_id: str) -> list:
    """Возвращает все <table> между <h2 id=section_id> и следующим <h2>."""
    tables = []
    capturing = False
    for el in soup.find_all(["h2", "table"]):
        if el.name == "h2":
            capturing = el.get("id") == section_id
            continue
        if capturing and el.name == "table":
            tables.append(el)
    return tables


def _ha_table_to_rows(table) -> tuple:
    """Разбирает одну табличку отчёта HA в (заголовок, {метка: значение})."""
    title = None
    data = {}
    for r in table.find_all("tr"):
        cells = [c.get_text(strip=True) for c in r.find_all(["th", "td"])]
        if not cells:
            continue
        if len(cells) == 1:
            title = cells[0]
        elif len(cells) == 2:
            data[cells[0]] = cells[1]
        else:
            data[cells[0]] = cells[1:]
    return title, data


def _parse_pct(value: "str | None"):
    if value is None:
        return None
    try:
        return float(str(value).replace("%", "").strip())
    except ValueError:
        return None


@st.cache_data(show_spinner=False)
def parse_ha_html_report(file_bytes: bytes) -> dict:
    """Извлекает из HTML-отчёта Hybrid Assistant показатели, которых
    нет как отдельных колонок в hybridassistant.db (разбивка SOC по
    источникам заряда, Glide, оценка стиля вождения), плюс BSFC для
    сверки с расчётом из базы."""
    soup = BeautifulSoup(file_bytes, "html.parser")
    result = {}

    for table in soup.find_all("table"):
        title, data = _ha_table_to_rows(table)
        if title == "Info":
            result["odometer"] = data.get("Odometer")
            break

    for table in _ha_section_tables(soup, "summary"):
        title, data = _ha_table_to_rows(table)
        if title == "Time":
            for key, dest in (("Start", "start"), ("Finish", "finish")):
                try:
                    result[dest] = datetime.strptime(data.get(key, ""), "%d/%m/%Y %H:%M:%S")
                except ValueError:
                    pass

    for table in _ha_section_tables(soup, "socstats"):
        title, data = _ha_table_to_rows(table)
        if title == "Variations":
            result["soc_gained_brakings"] = _parse_pct(data.get("SOC gained from brakings"))
            result["soc_gained_coasting"] = _parse_pct(data.get("SOC gained from coasting"))
            result["soc_charged_by_ice"] = _parse_pct(data.get("SOC charged by ICE"))

    for table in _ha_section_tables(soup, "glide"):
        title, data = _ha_table_to_rows(table)
        if "Glide score" in data or "Glide type" in data:
            result["glide_type"] = data.get("Glide type")
            try:
                result["glide_score"] = float(data.get("Glide score"))
            except (TypeError, ValueError):
                pass

    for table in _ha_section_tables(soup, "eval"):
        title, data = _ha_table_to_rows(table)
        if "Accelerator Nervousness" in data:
            try:
                result["accel_nervousness"] = float(data.get("Accelerator Nervousness"))
            except (TypeError, ValueError):
                pass
            result["braking_efficiency"] = _parse_pct(data.get("Braking Efficiency"))
            ineff = data.get("Inefficient Ignitions", "")
            if "/" in str(ineff):
                try:
                    num, den = str(ineff).split("/")
                    result["inefficient_ignitions"] = int(num)
                    result["total_ignitions"] = int(den)
                except ValueError:
                    pass

    for table in _ha_section_tables(soup, "bsfc"):
        title, data = _ha_table_to_rows(table)
        if title == "BSFC":
            try:
                result["bsfc_avg_report"] = float(data.get("Average"))
            except (TypeError, ValueError):
                pass

    return result


# --- Карты из HTML-отчёта ---
# Hybrid Assistant рисует в отчёте пять карт Leaflet, где каждая точка
# маршрута — это L.circle([lat, lon], radius, {color: '...'}). Цвет
# кодирует категорию, посчитанную самим Hybrid Assistant. Для карт
# "Мгновенный расход", "Торможение", "BSFC" и "Оценка наката" это
# ЕДИНСТВЕННЫЙ способ их получить: в hybridassistant.db нет ни готовых
# категорий, ни (для Glide/BSFC) открытой формулы их расчёта.
# Координаты те же, что в базе, так что качество GPS-трека одинаковое.

_HA_MAP_CIRCLE_RE = re.compile(
    r"L\.circle\(\[([-\d.]+),\s*([-\d.]+)\],\s*(\d+),\s*\{\s*color:\s*'(\w+)'"
)
_HA_MAP_ID_RE = re.compile(r"id='([^']*Map)'")

# Подписи цветов для каждой карты, взятые из легенд самого отчёта.
HA_MAP_LEGENDS = {
    "EV Map": {
        "gold": {"ru": "EV (ДВС выключен)", "pl": "EV (silnik wyłączony)"},
        "red": {"ru": "ДВС работает", "pl": "Silnik pracuje"},
    },
    "Brake Map": {
        "green": {"ru": "Рекуперация", "pl": "Rekuperacja"},
        "red": {"ru": "Механическое торможение", "pl": "Hamowanie mechaniczne"},
        "black": {"ru": "Без торможения", "pl": "Bez hamowania"},
    },
    "Instant Consumption Map": {
        "green": {"ru": "Очень низкий расход", "pl": "Bardzo niskie spalanie"},
        "gold": {"ru": "Низкий расход", "pl": "Niskie spalanie"},
        "orange": {"ru": "Средний расход", "pl": "Średnie spalanie"},
        "red": {"ru": "Высокий расход", "pl": "Wysokie spalanie"},
        "gray": {"ru": "Без расхода (EV)", "pl": "Bez spalania (EV)"},
    },
    "BSFC Map": {
        "green": {"ru": "Эффективно", "pl": "Efektywnie"},
        "gold": {"ru": "Умеренно", "pl": "Umiarkowanie"},
        "orange": {"ru": "Неэффективно", "pl": "Nieefektywnie"},
        "red": {"ru": "Очень неэффективно", "pl": "Bardzo nieefektywnie"},
        "gray": {"ru": "Нет данных", "pl": "Brak danych"},
    },
    "Glide Evaluation Map": {
        "green": {"ru": "Хороший накат", "pl": "Dobry wybieg"},
        "gold": {"ru": "Умеренный накат", "pl": "Umiarkowany wybieg"},
        "red": {"ru": "Плохой накат", "pl": "Słaby wybieg"},
        "gray": {"ru": "Нейтрально", "pl": "Neutralnie"},
    },
}

HA_MAP_TITLES = {
    "EV Map": {"ru": "Режим EV / ДВС", "pl": "Tryb EV / silnik"},
    "Brake Map": {"ru": "Торможение", "pl": "Hamowanie"},
    "Instant Consumption Map": {"ru": "Мгновенный расход", "pl": "Chwilowe spalanie"},
    "BSFC Map": {"ru": "Эффективность ДВС (BSFC)", "pl": "Efektywność silnika (BSFC)"},
    "Glide Evaluation Map": {"ru": "Оценка наката (Glide)", "pl": "Ocena wybiegu (Glide)"},
}

# Цвета Leaflet -> нормальные hex-цвета для Plotly.
_HA_COLOR_HEX = {
    "gold": "#FFC800",
    "red": "#E30000",
    "green": "#2CA02C",
    "orange": "#FF8C00",
    "gray": "#9AA0A6",
    "black": "#111111",
    "blue": "#1f77b4",
}


@st.cache_data(show_spinner=False)
def parse_ha_html_maps(file_bytes: bytes) -> dict:
    """Извлекает точки всех карт из HTML-отчёта Hybrid Assistant.
    Возвращает {название_карты: DataFrame(lat, lon, radius, color)}."""
    try:
        text = file_bytes.decode("utf-8", errors="replace")
    except Exception:
        return {}

    positions = [(m.group(1), m.start()) for m in _HA_MAP_ID_RE.finditer(text)]
    maps = {}
    for i, (name, pos) in enumerate(positions):
        end = positions[i + 1][1] if i + 1 < len(positions) else len(text)
        section = text[pos:end]
        rows = [
            {"lat": float(lat), "lon": float(lon), "radius": int(radius), "color": color}
            for lat, lon, radius, color in _HA_MAP_CIRCLE_RE.findall(section)
        ]
        if rows:
            df = pd.DataFrame(rows)
            # Точки (0,0) — это "GPS не поймал сигнал", а не реальное место.
            df = df[(df["lat"] != 0) | (df["lon"] != 0)]
            if not df.empty:
                maps[name] = df.reset_index(drop=True)
    return maps


def render_ha_html_map(map_name: str, points: pd.DataFrame, key_prefix: str = "tab4") -> None:
    """Рисует одну карту из HTML-отчёта с легендой на выбранном языке."""
    lang = st.session_state.get("lang", "pl")
    fig = go.Figure()
    legend = HA_MAP_LEGENDS.get(map_name, {})

    for color, group in points.groupby("color"):
        label = legend.get(color, {}).get(lang, color)
        fig.add_trace(
            go.Scattermap(
                lat=group["lat"],
                lon=group["lon"],
                mode="markers",
                marker=dict(size=6, color=_HA_COLOR_HEX.get(color, "#888888")),
                name=label,
                hoverinfo="skip",
            )
        )

    fig.update_layout(
        map=build_map_config(points["lat"].mean(), points["lon"].mean(), 11),
        margin=dict(l=0, r=0, t=0, b=0),
        height=rsp_height(460),
        legend=dict(orientation="h", yanchor="bottom", y=0.01, xanchor="left", x=0.01,
                    bgcolor="rgba(255,255,255,0.75)"),
    )
    st.plotly_chart(fig, width="stretch", key=f"{key_prefix}_ha_map_{map_name.replace(' ', '_')}")


class LocalReportFile:
    """Обёртка над файлом с диска с тем же интерфейсом, что у файла из
    st.file_uploader (.name / .getvalue()). Позволяет обрабатывать
    отчёты из папки Google Диска и загруженные вручную одним кодом."""

    def __init__(self, path: str):
        self.path = path
        self.name = os.path.basename(path)
        self.source = "drive"

    def getvalue(self) -> bytes:
        with open(self.path, "rb") as f:
            return f.read()


def find_ha_report_htmls(folder_path: str) -> list:
    """Ищет HTML-отчёты Hybrid Assistant в скачанной папке Google Диска."""
    found = []
    for root, _dirs, files in os.walk(folder_path):
        for fname in files:
            if fname.lower().endswith((".html", ".htm")):
                found.append(os.path.join(root, fname))
    return sorted(found)


def get_ha_files_from_drive() -> list:
    """HTML-отчёты, автоматически скачанные вместе с базой данных."""
    try:
        return [LocalReportFile(p) for p in find_ha_report_htmls(LOCAL_DB_FOLDER_PATH)]
    except Exception:
        return []


def get_uploaded_ha_files() -> list:
    """Все доступные HTML-отчёты: и автоматически скачанные из папки
    Google Диска вместе с базой, и загруженные вручную. Отчёт относится
    к конкретной поездке, поэтому этот список используется на всех
    вкладках. При совпадении имён приоритет у загруженного вручную —
    он новее и добавлен пользователем осознанно."""
    manual = st.session_state.get("ha_reports_uploader") or []
    manual = list(manual)
    manual_names = {f.name for f in manual}
    from_drive = [f for f in get_ha_files_from_drive() if f.name not in manual_names]
    return manual + from_drive


@st.cache_data(show_spinner=False)
def _ha_report_time_index(file_names: tuple, file_contents: tuple) -> dict:
    """Строит индекс {имя файла: (начало, конец)} по отчётам."""
    index = {}
    for name, content in zip(file_names, file_contents):
        try:
            data = parse_ha_html_report(content)
        except Exception:
            continue
        if data.get("start") and data.get("finish"):
            index[name] = (data["start"], data["finish"])
    return index


def find_ha_report_for_trip(trip_row) -> "tuple | None":
    """Ищет HTML-отчёт, соответствующий выбранной поездке. Сопоставление
    идёт по времени окончания: Hybrid Assistant пишет в отчёт локальное
    время, и мы приводим TSFIN из базы к тому же локальному часовому
    поясу, поэтому они должны совпадать с точностью до минут.
    Возвращает (имя файла, разобранные данные) или None."""
    files = get_uploaded_ha_files()
    if not files:
        return None

    trip_finish = trip_row.get("date")
    if pd.isna(trip_finish):
        return None

    names = tuple(f.name for f in files)
    contents = tuple(f.getvalue() for f in files)
    index = _ha_report_time_index(names, contents)

    best_name, best_delta = None, None
    for name, (_start, finish) in index.items():
        delta = abs((pd.Timestamp(finish) - pd.Timestamp(trip_finish)).total_seconds())
        if best_delta is None or delta < best_delta:
            best_name, best_delta = name, delta

    # 5 минут допуска: секунды могут разойтись из-за округления, но две
    # разные поездки почти никогда не заканчиваются так близко.
    if best_name is None or best_delta > 300:
        return None

    file_by_name = {f.name: f for f in files}
    return best_name, parse_ha_html_report(file_by_name[best_name].getvalue())


def render_ha_trip_extras(trip_row) -> None:
    """Показывает данные из HTML-отчёта для КОНКРЕТНОЙ поездки:
    фирменные показатели Hybrid Assistant, которых нет в базе, и его
    собственные карты. Вызывается на вкладке детальных логов."""
    match = find_ha_report_for_trip(trip_row)
    if match is None:
        st.info(t("ha_trip_no_report"))
        return

    file_name, data = match
    st.success(t("ha_trip_report_found").format(name=file_name))

    lang = st.session_state.get("lang", "pl")

    # --- Показатели, которых нет в базе ---
    soc_keys = ("soc_gained_brakings", "soc_gained_coasting", "soc_charged_by_ice")
    if any(data.get(k) is not None for k in soc_keys):
        st.markdown(f"**{t('ha_trend_soc_title')}**")
        c1, c2, c3 = st.columns(3)
        c1.metric(t("ha_soc_brakings"), f"{data.get('soc_gained_brakings', 0):.0f}%" if data.get("soc_gained_brakings") is not None else "—")
        c2.metric(t("ha_soc_coasting"), f"{data.get('soc_gained_coasting', 0):.0f}%" if data.get("soc_gained_coasting") is not None else "—")
        c3.metric(t("ha_soc_ice"), f"{data.get('soc_charged_by_ice', 0):.0f}%" if data.get("soc_charged_by_ice") is not None else "—")
        st.caption(t("rep_soc_note"))

    c1, c2, c3 = st.columns(3)
    if data.get("glide_score") is not None:
        c1.metric(t("ha_glide_score"), f"{data['glide_score']:.1f}")
    if data.get("glide_type"):
        c2.metric(t("rep_glide_title").replace("🛞 ", ""), str(data["glide_type"]))
    if data.get("braking_efficiency") is not None:
        c3.metric(t("ha_braking_efficiency"), f"{data['braking_efficiency']:.1f}%")

    # --- Карты этой поездки из отчёта ---
    st.markdown(f"**{t('ha_maps_title')}**")
    if not maps_are_unlocked():
        render_maps_locked_placeholder()
        return

    file_by_name = {f.name: f for f in get_uploaded_ha_files()}
    maps = parse_ha_html_maps(file_by_name[file_name].getvalue())
    if not maps:
        st.info(t("ha_maps_no_maps"))
        return

    map_labels = {name: HA_MAP_TITLES.get(name, {}).get(lang, name) for name in maps}
    chosen_map = st.selectbox(
        t("ha_maps_select_map"),
        list(maps.keys()),
        format_func=lambda n: map_labels[n],
        key="tab2_ha_map_select",
    )
    points = maps[chosen_map]
    render_ha_html_map(chosen_map, points, key_prefix="tab2")
    lat_span_m = (points["lat"].max() - points["lat"].min()) * 111_000
    lon_span_m = (points["lon"].max() - points["lon"].min()) * 111_000 * 0.62
    if max(lat_span_m, lon_span_m) < 100:
        st.warning(t("ha_maps_gps_warning"))


def load_ha_reports(uploaded_files) -> pd.DataFrame:
    records = []
    for uf in uploaded_files or []:
        try:
            data = parse_ha_html_report(uf.getvalue())
        except Exception:
            continue
        if "finish" in data:
            data = dict(data)
            data["filename"] = uf.name
            records.append(data)
    if not records:
        return pd.DataFrame()
    return pd.DataFrame(records).sort_values("finish").reset_index(drop=True)


def _render_password_gate(
    namespace: str, secret_key: str, fallback_hash: str, unlocked_flag: str, widget_key_prefix: "str | None" = None
) -> bool:
    """Универсальный UI-гейт по паролю (хеш + защита от подбора).
    namespace/unlocked_flag определяют состояние защиты (общее, если
    вызывается из нескольких мест с одинаковым namespace — один пароль
    разблокирует все такие места сразу в этой сессии). widget_key_prefix
    даёт виджетам уникальные ключи для каждого места вызова, чтобы
    Streamlit не ругался на повторяющиеся key при рендере нескольких
    вкладок за один прогон скрипта.
    Возвращает True, если доступ уже разблокирован в этой сессии —
    тогда вызывающий код рисует защищённый контент дальше. Если
    возвращает False, весь нужный UI (запрос пароля/блокировка/ошибка)
    уже отрисован, и вызывающий код должен просто ничего больше не
    показывать в этом месте."""
    key_prefix = widget_key_prefix or namespace
    remaining = _lockout_remaining_seconds(namespace)
    if remaining > 0:
        minutes, seconds = divmod(remaining, 60)
        st.error(t("password_locked").format(minutes=minutes, seconds=seconds))
        return False

    if not st.session_state.get(unlocked_flag, False):
        password_input = st.text_input(
            t("password_label"), type="password", key=f"{key_prefix}_password_input"
        )
        if password_input == "":
            st.info(t("password_needed"))
        elif _verify_secret(password_input, secret_key, fallback_hash):
            _register_successful_unlock(namespace, unlocked_flag)
            st.rerun()
        else:
            attempts_left = _register_failed_attempt(namespace)
            st.error(t("password_wrong").format(attempts_left=attempts_left))
        return False

    st.success(t("password_unlocked"))
    if st.button(t("lock_again_button"), key=f"{key_prefix}_lock_again"):
        st.session_state[unlocked_flag] = False
        st.rerun()
    return True


def render_tab4(trips_df, temp_df, cell_df, fuel_df):
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

    st.dataframe(df_compare.style.apply(_highlight, axis=1), width="stretch", hide_index=True)

    st.divider()

    if not cell_df.empty:
        st.markdown(f"#### {t('compare_trend_soh')}")
        soh_series = cell_df["cell_delta"].apply(calculate_soh)
        fig_soh = go.Figure(go.Scatter(x=cell_df["timestamp"], y=soh_series, mode="lines+markers"))
        fig_soh.update_layout(height=rsp_height(300), yaxis_title="SOH %")
        st.plotly_chart(fig_soh, width="stretch", key="tab4_soh_trend")

        st.markdown(f"#### {t('compare_trend_delta')}")
        fig_delta = go.Figure(go.Scatter(x=cell_df["timestamp"], y=cell_df["cell_delta"], mode="lines+markers"))
        fig_delta.update_layout(height=rsp_height(300), yaxis_title="Delta, В")
        st.plotly_chart(fig_delta, width="stretch", key="tab4_delta_trend")
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
            fig_season.update_layout(height=rsp_height(300), xaxis_title="Месяц", yaxis_title="°C ВВБ")
            st.plotly_chart(fig_season, width="stretch", key="tab4_seasonal_chart")
    else:
        st.info(t("not_enough_data"))

    # --- Fuelio: реальный расход LPG во времени (по чекам АЗС) ---
    st.divider()
    st.subheader(t("fuel_trend_health_title"))
    if fuel_df.empty:
        st.info(t("fuel_log_no_data"))
    else:
        lpg_df = fuel_df[(fuel_df["fuel_type"] == "lpg") & fuel_df["consumption_l100"].notna()].sort_values("date")
        if len(lpg_df) >= 3:
            fig = go.Figure(
                go.Scatter(x=lpg_df["date"], y=lpg_df["consumption_l100"], mode="lines+markers", name=t("fuel_type_lpg"))
            )
            fig.update_layout(height=rsp_height(300), yaxis_title=t("unit_l100km"))
            st.plotly_chart(fig, width="stretch", key="tab4_fuel_lpg_trend")
            st.caption(t("fuel_real_badge_note"))

            x = (pd.to_datetime(lpg_df["date"]) - pd.to_datetime(lpg_df["date"]).min()).dt.total_seconds().to_numpy()
            slope_per_month = np.polyfit(x, lpg_df["consumption_l100"].to_numpy(), 1)[0] * 86400 * 30
            if slope_per_month > 0.3:
                st.warning(t("fuel_lpg_trend_warn").format(value=f"{slope_per_month:.2f}"))
            else:
                st.success(t("fuel_lpg_trend_ok"))
        else:
            st.info(t("not_enough_data"))

        # Сверка: прогноз ЭБУ (из базы) vs реальный расход (по чекам), по месяцам
        if not trips_df.empty and "consumption" in trips_df.columns:
            db_monthly = trips_df.dropna(subset=["consumption"]).copy()
            db_monthly["month"] = db_monthly["date"].dt.strftime("%Y-%m")
            db_monthly = db_monthly.groupby("month")["consumption"].mean().reset_index()

            fuel_monthly = fuel_df[fuel_df["consumption_l100"].notna()].copy()
            fuel_monthly["month"] = pd.to_datetime(fuel_monthly["date"]).dt.strftime("%Y-%m")
            fuel_monthly = fuel_monthly.groupby(["month", "fuel_type"])["consumption_l100"].mean().reset_index()

            if not db_monthly.empty and not fuel_monthly.empty:
                st.markdown(f"**{t('fuel_crosscheck_title')}**")
                fig2 = go.Figure()
                fig2.add_trace(go.Scatter(x=db_monthly["month"], y=db_monthly["consumption"], name=f"{t('rep_fuel_consumption')} {t('fuel_forecast_badge')}", mode="lines+markers"))
                for ftype, label_key in (("lpg", "fuel_type_lpg"), ("petrol", "fuel_type_petrol")):
                    sub = fuel_monthly[fuel_monthly["fuel_type"] == ftype]
                    if not sub.empty:
                        fig2.add_trace(go.Scatter(x=sub["month"], y=sub["consumption_l100"], name=f"{t(label_key)} {t('fuel_real_badge')}", mode="lines+markers"))
                fig2.update_layout(height=rsp_height(320), yaxis_title=t("unit_l100km"), legend=dict(orientation="h"))
                st.plotly_chart(fig2, width="stretch", key="tab4_fuel_crosscheck")
                st.caption(t("fuel_crosscheck_note"))

    # --- HTML-отчёты Hybrid Assistant: доп. тренды, которых нет в БД ---
    st.divider()
    st.subheader(t("ha_reports_title"))
    st.caption(t("ha_reports_explainer"))

    # Сначала показываем, что уже нашлось на Google Диске автоматически —
    # чтобы было понятно, нужно ли вообще что-то загружать вручную.
    drive_files = get_ha_files_from_drive()
    if drive_files:
        st.success(t("ha_reports_drive_found").format(n=len(drive_files)))
        with st.expander(t("ha_reports_drive_list"), expanded=False):
            for f in drive_files:
                st.markdown(f"- `{f.name}`")
    else:
        st.info(t("ha_reports_drive_none"))

    if not _render_password_gate(
        "maintenance", "maintenance_password_hash", _FALLBACK_PASSWORD_HASH, "maintenance_unlocked",
        widget_key_prefix="ha_reports",
    ):
        return

    st.file_uploader(
        t("ha_reports_upload_label"),
        type=["html", "htm"],
        accept_multiple_files=True,
        key="ha_reports_uploader",
        help=t("ha_reports_upload_help"),
    )
    st.caption(t("ha_reports_limit_caption"))

    ha_files = get_uploaded_ha_files()
    if not ha_files:
        st.info(t("ha_reports_none_at_all"))
        return

    # Разбираем каждый файл по отдельности и честно показываем результат
    # по каждому: что распозналось, что нет и почему.
    ok_rows, failed = [], []
    for uf in ha_files:
        try:
            data = parse_ha_html_report(uf.getvalue())
        except Exception as e:
            failed.append((uf.name, str(e)[:120]))
            continue
        if data.get("finish"):
            ok_rows.append((uf, data))
        else:
            failed.append((uf.name, t("ha_reports_fail_no_time")))

    if ok_rows:
        st.success(t("ha_reports_upload_success").format(n=len(ok_rows)))
        with st.expander(t("ha_reports_details"), expanded=False):
            summary = pd.DataFrame(
                [
                    {
                        t("col_date"): d["finish"].strftime("%Y-%m-%d %H:%M"),
                        t("ha_reports_col_file"): uf.name,
                        t("ha_reports_col_source"): (
                            t("ha_reports_source_drive")
                            if getattr(uf, "source", None) == "drive"
                            else t("ha_reports_source_manual")
                        ),
                    }
                    for uf, d in ok_rows
                ]
            ).sort_values(t("col_date"), ascending=False)
            st.dataframe(summary, width="stretch", hide_index=True, key="ha_reports_summary_table")

    for name, reason in failed:
        st.error(t("ha_reports_upload_failed").format(name=name, reason=reason))

    if not ok_rows:
        return

    reports_df = load_ha_reports([uf for uf, _ in ok_rows])
    if reports_df.empty:
        st.warning(t("ha_reports_parse_error"))
        return

    # --- Карты из HTML-отчётов ---
    with st.expander(t("ha_maps_title"), expanded=False):
        st.caption(t("ha_maps_explainer"))
        if not maps_are_unlocked():
            render_maps_locked_placeholder()
        else:
            file_by_name = {uf.name: uf for uf in ha_files}
            chosen_file_name = st.selectbox(
                t("ha_maps_select_report"), list(file_by_name.keys()), key="ha_maps_report_select"
            )
            maps = parse_ha_html_maps(file_by_name[chosen_file_name].getvalue())
            if not maps:
                st.info(t("ha_maps_no_maps"))
            else:
                lang = st.session_state.get("lang", "pl")
                map_labels = {
                    name: HA_MAP_TITLES.get(name, {}).get(lang, name) for name in maps
                }
                chosen_map = st.selectbox(
                    t("ha_maps_select_map"),
                    list(maps.keys()),
                    format_func=lambda n: map_labels[n],
                    key="ha_maps_map_select",
                )
                points = maps[chosen_map]
                render_ha_html_map(chosen_map, points)
                # Если весь трек укладывается в крошечное пятно — это признак
                # потери GPS-сигнала, а не реального маршрута.
                lat_span_m = (points["lat"].max() - points["lat"].min()) * 111_000
                lon_span_m = (points["lon"].max() - points["lon"].min()) * 111_000 * 0.62
                if max(lat_span_m, lon_span_m) < 100:
                    st.warning(t("ha_maps_gps_warning"))

    lang = st.session_state.get("lang", "pl")

    def _trend_check(series: pd.Series, dates: pd.Series, warn_key: str, ok_key: str, min_points: int = 3):
        valid = series.dropna()
        if len(valid) < min_points:
            st.info(t("not_enough_data"))
            return
        x = (dates.loc[valid.index] - dates.loc[valid.index].min()).dt.total_seconds().to_numpy()
        slope = np.polyfit(x, valid.to_numpy(), 1)[0]
        slope_per_month = slope * 86400 * 30
        if slope_per_month < 0:
            st.warning(t(warn_key).format(value=f"{abs(slope_per_month):.2f}"))
        else:
            st.success(t(ok_key))

    with st.expander(t("ha_trend_soc_title"), expanded=True):
        fig = go.Figure()
        fig.add_trace(go.Scatter(x=reports_df["finish"], y=reports_df.get("soc_gained_brakings"), name=t("ha_soc_brakings"), mode="lines+markers"))
        fig.add_trace(go.Scatter(x=reports_df["finish"], y=reports_df.get("soc_gained_coasting"), name=t("ha_soc_coasting"), mode="lines+markers"))
        fig.add_trace(go.Scatter(x=reports_df["finish"], y=reports_df.get("soc_charged_by_ice"), name=t("ha_soc_ice"), mode="lines+markers"))
        fig.update_layout(height=rsp_height(320), yaxis_title="%")
        st.plotly_chart(fig, width="stretch", key="tab4_ha_soc_trend")
        st.caption(t("ha_trend_soc_note"))
        if "soc_gained_brakings" in reports_df.columns:
            _trend_check(reports_df["soc_gained_brakings"], reports_df["finish"], "ha_trend_brakings_warn", "ha_trend_brakings_ok")

    with st.expander(t("ha_trend_glide_title")):
        if "glide_score" in reports_df.columns:
            fig = go.Figure(go.Scatter(x=reports_df["finish"], y=reports_df["glide_score"], mode="lines+markers"))
            fig.update_layout(height=rsp_height(300), yaxis_title=t("ha_glide_score"))
            st.plotly_chart(fig, width="stretch", key="tab4_ha_glide_trend")
            st.caption(t("ha_trend_glide_note"))
            _trend_check(reports_df["glide_score"], reports_df["finish"], "ha_trend_glide_warn", "ha_trend_glide_ok")
        else:
            st.info(t("not_enough_data"))

    with st.expander(t("ha_trend_driver_title")):
        c1, c2 = st.columns(2)
        with c1:
            if "accel_nervousness" in reports_df.columns:
                fig = go.Figure(go.Scatter(x=reports_df["finish"], y=reports_df["accel_nervousness"], mode="lines+markers"))
                fig.update_layout(height=rsp_height(280), yaxis_title=t("ha_accel_nervousness"))
                st.plotly_chart(fig, width="stretch", key="tab4_ha_accel_nervousness")
        with c2:
            if "braking_efficiency" in reports_df.columns:
                fig = go.Figure(go.Scatter(x=reports_df["finish"], y=reports_df["braking_efficiency"], mode="lines+markers"))
                fig.update_layout(height=rsp_height(280), yaxis_title=t("ha_braking_efficiency"))
                st.plotly_chart(fig, width="stretch", key="tab4_ha_braking_efficiency")
        st.caption(t("ha_trend_driver_note"))

    with st.expander(t("ha_bsfc_crosscheck_title")):
        if "bsfc_avg_report" in reports_df.columns:
            fig = go.Figure(go.Scatter(x=reports_df["finish"], y=reports_df["bsfc_avg_report"], mode="lines+markers", name="BSFC (отчёт HA)"))
            fig.update_layout(height=rsp_height(280), yaxis_title="g/kWh")
            st.plotly_chart(fig, width="stretch", key="tab4_ha_bsfc_crosscheck")
            st.caption(t("ha_bsfc_crosscheck_note"))
        else:
            st.info(t("not_enough_data"))

    st.caption(t("ha_reports_hvcheck_note"))


def render_maintenance_journal(records: list) -> None:
    """Журнал ТО: каждая запись раскрывается в подробную карточку.
    Фото фактуры показывается только при разблокированном коде — оно
    может содержать личные данные (адрес, номер авто, реквизиты)."""
    if not records:
        st.info(t("maintenance_empty"))
        return

    ordered = sorted(records, key=lambda r: (r.get("date") or "", r.get("mileage") or 0), reverse=True)
    st.caption(t("maintenance_click_hint"))

    for i, rec in enumerate(ordered):
        mileage = rec.get("mileage")
        mileage_txt = f"{mileage:,.0f}".replace(",", " ") if isinstance(mileage, (int, float)) else "—"
        desc = (rec.get("description") or "").strip()
        short_desc = desc if len(desc) <= 60 else desc[:57] + "…"
        header = f"📄 {rec.get('date', '—')} · {mileage_txt} {t('unit_km')} · {short_desc}"

        with st.expander(header):
            c1, c2 = st.columns(2)
            c1.metric(t("col_date"), rec.get("date") or "—")
            c2.metric(t("col_mileage"), mileage_txt)

            if desc:
                st.markdown(f"**{t('col_description')}**")
                st.write(desc)

            # Подробности о запчасти/расходнике — все поля необязательные,
            # старые записи их просто не содержат.
            detail_fields = [
                ("manufacturer", t("part_manufacturer")),
                ("product_name", t("part_name")),
                ("spec", t("part_spec")),
                ("quantity", t("part_quantity")),
                ("price", t("part_price")),
            ]
            present = [(label, rec.get(key)) for key, label in detail_fields if rec.get(key)]
            if present:
                st.markdown(f"**{t('part_details')}**")
                st.dataframe(
                    pd.DataFrame({t("part_field"): [p[0] for p in present],
                                  t("part_value"): [str(p[1]) for p in present]}),
                    width="stretch", hide_index=True, key=f"maint_details_{i}",
                )

            photo_b64 = rec.get("invoice_photo_b64")
            if photo_b64:
                if maps_are_unlocked():
                    try:
                        st.image(base64.b64decode(photo_b64), caption=t("invoice_photo_caption"), width="stretch")
                    except Exception:
                        st.caption(t("invoice_photo_broken"))
                else:
                    st.info(t("invoice_photo_locked"))


def render_tab5(db_path, file_version):
    st.subheader(t("maintenance_title"))

    # Показываем результат последнего сохранения (форма делает st.rerun,
    # поэтому сообщение нужно пронести через session_state).
    status = st.session_state.pop("last_save_status", None)
    if status:
        kind, _ = status
        if kind == "drive":
            st.success(t("save_success_drive"))
        elif kind == "local_only":
            st.warning(t("save_success_local_only"))
        else:
            st.error(t("save_failed"))

    mode = get_maintenance_storage_mode()
    if mode == "drive":
        st.caption(t("storage_mode_drive"))
    elif mode == "drive_readonly":
        st.warning(t("storage_mode_drive_readonly"))
    else:
        st.warning(t("storage_mode_local"))

    records = load_maintenance()
    render_maintenance_journal(records)

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
        "cvt_oil": {"ru": "Масло e-CVT (ATF WS)", "pl": "Olej e-CVT (ATF WS)"},
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
    st.markdown(f"**{t('invoice_section_title')}**")
    if GENAI_AVAILABLE and get_gemini_api_key():
        st.caption(t("invoice_how_it_works"))
        uploaded_invoice = st.file_uploader(
            t("invoice_upload_label"),
            type=["jpg", "jpeg", "png"],
            key="invoice_uploader",
            help=t("invoice_upload_help"),
        )
        if uploaded_invoice is not None:
            preview_col, result_col = st.columns([1, 2])
            with preview_col:
                st.image(uploaded_invoice, caption=uploaded_invoice.name, width="stretch")

            with result_col:
                # Распознаём только при появлении НОВОГО файла, иначе каждый
                # клик по странице заново дёргал бы платный API.
                if st.session_state.get("last_invoice_name") != uploaded_invoice.name:
                    with st.spinner(t("invoice_processing")):
                        data = extract_invoice_data(
                            uploaded_invoice.getvalue(), uploaded_invoice.type or "image/jpeg"
                        )
                    st.session_state["last_invoice_name"] = uploaded_invoice.name
                    st.session_state["last_invoice_bytes"] = uploaded_invoice.getvalue()
                    st.session_state["last_invoice_result"] = data

                data = st.session_state.get("last_invoice_result", {})
                if not data:
                    st.info(t("invoice_waiting"))
                elif "error" in data:
                    st.error(t("invoice_error").format(error=data["error"]))
                    st.caption(t("invoice_error_hint"))
                else:
                    recognized_date = data.get("date")
                    recognized_odo = data.get("odo")
                    recognized_desc = data.get("desc")
                    st.session_state["invoice_prefill_date"] = recognized_date
                    st.session_state["invoice_prefill_odo"] = recognized_odo
                    st.session_state["invoice_prefill_desc"] = recognized_desc

                    missing = [
                        label
                        for value, label in (
                            (recognized_date, t("form_date")),
                            (recognized_odo, t("form_mileage")),
                            (recognized_desc, t("form_description")),
                        )
                        if not value
                    ]
                    if missing:
                        st.warning(t("invoice_partial").format(fields=", ".join(missing)))
                    else:
                        st.success(t("invoice_success"))

                    st.markdown(
                        f"- **{t('form_date')}:** {recognized_date or '—'}\n"
                        f"- **{t('form_mileage')}:** {recognized_odo or '—'}\n"
                        f"- **{t('form_description')}:** {recognized_desc or '—'}"
                    )
                    st.caption(t("invoice_check_before_save"))
    else:
        st.info(t("invoice_unavailable"))

    if not _render_password_gate(
        "maintenance", "maintenance_password_hash", _FALLBACK_PASSWORD_HASH, "maintenance_unlocked",
        widget_key_prefix="maintenance_form",
    ):
        return

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

        st.markdown(f"**{t('part_details')}** — {t('part_details_optional')}")
        p1, p2 = st.columns(2)
        with p1:
            part_manufacturer = st.text_input(t("part_manufacturer"), placeholder=t("part_manufacturer_ph"))
            part_spec = st.text_input(t("part_spec"), placeholder=t("part_spec_ph"))
            part_price = st.text_input(t("part_price"), placeholder=t("part_price_ph"))
        with p2:
            part_name = st.text_input(t("part_name"), placeholder=t("part_name_ph"))
            part_quantity = st.text_input(t("part_quantity"), placeholder=t("part_quantity_ph"))

        attach_photo = st.checkbox(t("attach_invoice_photo"), value=True)
        submitted = st.form_submit_button(t("save_button"))

        if submitted:
            if record_description.strip() == "":
                st.warning(t("save_fill_all"))
            else:
                new_record = {
                    "date": record_date.strftime("%Y-%m-%d"),
                    "mileage": int(record_mileage),
                    "description": record_description.strip(),
                }
                for key, value in (
                    ("manufacturer", part_manufacturer),
                    ("product_name", part_name),
                    ("spec", part_spec),
                    ("quantity", part_quantity),
                    ("price", part_price),
                ):
                    if value and value.strip():
                        new_record[key] = value.strip()

                # Фото фактуры сохраняем уменьшенной копией: оригинал с
                # телефона весит несколько мегабайт, а maintenance.json
                # хранится целиком в памяти при каждом чтении.
                if attach_photo:
                    raw_photo = st.session_state.get("last_invoice_bytes")
                    if raw_photo:
                        thumb = _make_invoice_thumbnail(raw_photo)
                        if thumb:
                            new_record["invoice_photo_b64"] = thumb

                save_result = save_maintenance_record(new_record)
                for k in ("invoice_prefill_date", "invoice_prefill_odo", "invoice_prefill_desc",
                          "last_invoice_bytes", "last_invoice_name", "last_invoice_result"):
                    st.session_state.pop(k, None)
                if save_result.get("drive"):
                    st.session_state["last_save_status"] = ("drive", None)
                elif save_result.get("local"):
                    st.session_state["last_save_status"] = ("local_only", None)
                else:
                    st.session_state["last_save_status"] = ("failed", None)
                st.rerun()


def main():
    if "lang" not in st.session_state:
        st.session_state["lang"] = "pl"

    st.set_page_config(page_title=t("page_title"), page_icon="🚗", layout="wide")

    inject_responsive_css()

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
    fuel_df = pd.DataFrame()
    db_ok = True
    db_missing = False
    db_error_message = None
    db_path = None
    file_version = None

    with st.spinner(t("downloading_db")):
        try:
            db_path = download_database()
        except RuntimeError as e:
            print(f"[main] download_database RuntimeError: {e!r}", flush=True)
            db_ok = False
            db_missing = True
        except Exception as e:
            print("[main] download_database неожиданная ошибка:", flush=True)
            traceback.print_exc()
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

        try:
            fuel_df = load_fuel_reports(LOCAL_DB_FOLDER_PATH)
        except Exception:
            fuel_df = pd.DataFrame()

    with tab1:
        if not db_ok:
            # Именно if/else, а не тернарное выражение: у Streamlit включена
            # "магия", которая сама выводит значение выражения-инструкции, а
            # st.warning() возвращает DeltaGenerator — и на экран попадала его
            # документация вместо сообщения об ошибке.
            if db_missing:
                st.warning(t("db_missing"))
            else:
                st.error(t("db_error").format(error=db_error_message))
        else:
            render_tab1(trips_df, fastlog_df, temp_df, cell_df, db_path, file_version, fuel_df)

    with tab2:
        if not db_ok:
            # Именно if/else, а не тернарное выражение: у Streamlit включена
            # "магия", которая сама выводит значение выражения-инструкции, а
            # st.warning() возвращает DeltaGenerator — и на экран попадала его
            # документация вместо сообщения об ошибке.
            if db_missing:
                st.warning(t("db_missing"))
            else:
                st.error(t("db_error").format(error=db_error_message))
        else:
            render_tab2(trips_df, fastlog_df, db_path, file_version)

    with tab3:
        render_tab3()

    with tab4:
        if not db_ok:
            # Именно if/else, а не тернарное выражение: у Streamlit включена
            # "магия", которая сама выводит значение выражения-инструкции, а
            # st.warning() возвращает DeltaGenerator — и на экран попадала его
            # документация вместо сообщения об ошибке.
            if db_missing:
                st.warning(t("db_missing"))
            else:
                st.error(t("db_error").format(error=db_error_message))
        else:
            render_tab4(trips_df, temp_df, cell_df, fuel_df)

    with tab5:
        render_tab5(db_path, file_version)


if __name__ == "__main__":
    main()
