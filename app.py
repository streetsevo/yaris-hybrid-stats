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
        "app_title": "Toyota Yaris 4 Hybrid (2021) — Полная диагностика",
        "language_label": "Язык / Language",
        "nav_section": "Раздел",
        "app_header_title": "Панель диагностики",
        "refresh_db_button": "🔄 Обновить базу данных",
        "map_style_label": "Стиль карты",
        "triplog_title": "Точная карта поездки (TripLog + телеметрия)",
        "triplog_explainer": "Геометрия маршрута берётся из TripLog — у него нормальный GPS-трек. Режим EV/ДВС берётся из телеметрии Hybrid Assistant, где он известен всегда. Там, где телеметрии за нужный момент нет, участок помечается отдельным цветом, а не достраивается догадками.",
        "triplog_upload_label": "Загрузите KML-экспорт маршрутов из TripLog",
        "triplog_upload_help": "В TripLog: страница Trips → отметьте поездки → экспорт KML («route details»). Обычный отчёт на email не подойдёт — в нём нет геометрии маршрутов.",
        "triplog_no_file": "Файл маршрутов не загружен.",
        "triplog_parse_failed": "❌ В файле не найдено маршрутов. Убедитесь, что это KML-экспорт маршрутов TripLog, а не отчёт о пробеге.",
        "triplog_loaded": "✅ Загружено маршрутов: {n}",
        "triplog_select_route": "Маршрут",
        "triplog_select_day": "День",
        "triplog_drive_found": "✅ Автоматически загружено с Google Диска: {n} файл(ов) с маршрутами.",
        "triplog_drive_none": "ℹ️ Файлов с маршрутами на Google Диске не найдено. Положите KML-экспорты в подпапку triplog рядом с базой данных — они будут подхватываться автоматически. Либо загрузите вручную ниже.",
        "triplog_drive_list": "Показать список файлов с Google Диска",
        "triplog_parsing": "Разбираю маршруты…",
        "triplog_file_skipped": "⚠️ Пропущен файл «{name}»: маршрутов в нём не найдено.",
        "triplog_no_overlap": "⚠️ Телеметрия за время этих маршрутов не найдена — весь трек будет помечен как «нет данных о режиме». Скорее всего, Hybrid Assistant в эти дни не записывал поездки, либо база ещё не обновилась.",
        "triplog_offset_applied": "🕐 Обнаружено расхождение часов между TripLog и телеметрией: применён сдвиг {hours} ч (совпало {pct}% точек).",
        "triplog_offset_none": "Часы совпадают, сдвиг не потребовался (совпало {pct}% точек).",
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
        "tab1": "Аналитика и Диагностика",
        "tab2": "Детальные логи",
        "tab_triplog": "TripLog: маршруты",
        "tab3": "Мониторинг Dr. Prius",
        "tab4": "Сравнение и тренды",
        "tab5": "Техническое обслуживание",
        # --- Код доступа к картам ---
        "map_code_label": "Введите код доступа",
        "access_dialog_subtitle": "Панель диагностики",
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
        "map_section_title": "Карта поездки",
        "map_section_group": "Карты и маршруты",
        "map_select_trip": "Выберите поездку",
        "map_param_label": "Показатель на карте",
        "map_param_mode": "Режим (EV / ДВС)",
        "map_param_braking": "Торможение",
        "map_param_speed": "Скорость",
        "map_param_soc": "Заряд батареи (SOC)",
        "map_period_title": "Карта за период",
        "map_period_label": "Период",
        "map_period_day": "День",
        "map_period_week": "Неделя",
        "map_period_month": "Месяц",
        "map_period_year": "Год",
        "map_period_avg_consumption": "Средний расход за период: {value} л/100км",
        "map_period_distance_odo": "Пробег по одометру",
        "map_period_distance_odo_help": "Одометр читается напрямую с автомобиля по OBD — это весь реально пройденный путь за период, включая поездки, которые Hybrid Assistant не записывал.",
        "map_period_distance_logged": "Из них записано",
        "map_period_distance_logged_help": "Сумма дистанций поездок, которые Hybrid Assistant успел зафиксировать. Он пишет только когда запущен и подключён к OBD-адаптеру.",
        "map_period_gap_metric": "Не записано",
        "map_period_gap_note": "За период {km} км пройдено без записи Hybrid Assistant — приложение в это время не было подключено. На карте и в расчётах расхода эти километры не учтены.",
        "map_period_trips": "Поездок за период",
        "triplog_day_distance": "Пробег за день",
        "triplog_day_trips": "Поездок за день",
        "fuel_forecast_badge": "🔮 (прогноз)",
        "unit_kmh": "км/ч",
        "unit_l100km": "л/100км",
        "unit_l": "л",
        "weather_title": "Метеорологические условия поездки",
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
        "elevation_profile_title": "Профиль высот (рельеф маршрута)",
        "elevation_no_data": "Нет данных о высоте для этой поездки.",
        "elevation_flat": "Высота на всём маршруте не менялась — либо участок действительно ровный, либо GPS писал высоту с шагом в целые метры.",
        "unit_price_per_l": "zł/л",
        "unit_rpm": "об/мин",
        "unit_nm": "Нм",
        "fuel_forecast_help": "Оценка ЭБУ по длительности впрыска (данные Hybrid Assistant) — не прямое измерение топлива.",
        "fuel_real_badge": "🧾 (реально)",
        "fuel_real_badge_short": "🧾 Данные по чекам АЗС",
        "fuel_real_badge_note": "🧾 Реальный расход по чекам АЗС (отчёт Fuelio), в отличие от прогноза ЭБУ — это подтверждённые литры и стоимость.",
        "fuel_type_lpg": "ГБО (газ)",
        "fuel_type_petrol": "Бензин",
        "map_day_refuel_note": "⛽ В этот день заправлено: {fuel} — {liters} л по {price} zł/л.",
        "fuel_log_title": "Заправки (реальные данные, отчёт Fuelio)",
        "fuel_log_no_data": "Нет данных о заправках — загрузите отчёт Fuelio (PDF) в папку на Google Диске рядом с базой данных.",
        "fuel_last_refuel_date": "Последняя заправка",
        "fuel_liters": "Залито",
        "fuel_price": "Цена",
        "fuel_days_ago": "{days} дн. назад",
        "fuel_avg_consumption": "Средний расход",
        "fuel_petrol_no_avg_note": "Нет данных — неизвестно, сколько бензина было в баке до начала наблюдений, а расход сильно зависит от доли использования бензина (в основном пуск/прогрев), так что усреднение по общему пробегу вводит в заблуждение.",
        "fuel_trend_title": "История заправок",
        "fuel_metric_label": "Показатель",
        "fuel_metric_days": "Дней с прошлой заправки",
        "fuel_metric_liters": "Сколько залито, л",
        "fuel_metric_cost": "Стоимость, zł",
        "fuel_period_label": "Период",
        "fuel_trend_health_title": "Тренд реального расхода LPG (по чекам)",
        "fuel_lpg_trend_warn": "⚠️ Реальный расход LPG растёт (~{value} л/100км в мес.) — стоит проверить ГБО (форсунки, редуктор, смесь).",
        "fuel_lpg_trend_ok": "Реальный расход LPG стабилен или снижается — признаков проблем с ГБО не выявлено.",
        "fuel_crosscheck_title": "Сверка: прогноз ЭБУ vs реальный расход, по месяцам",
        "fuel_crosscheck_note": "Если разрыв между прогнозом и реальным расходом растёт со временем — возможен уход калибровки форсунок/датчиков от реальности, стоит присмотреться к LTFT на вкладке \"Аналитика\".",
        "legend_ev": "EV (ДВС выключен)",
        "legend_ice": "ДВС работает",
        # --- Экспертные параметры ---
        "expert_params_title": "Экспертные параметры",
        "ltft_title": "Долговременная топливная коррекция (LTFT), среднее после установки ГБО",
        "ltft_warning": "⚠️ Рекомендуется проверить газовые форсунки и карту ГБО (смесь неоптимальна).",
        "hv_safety_title": "Индикатор безопасности ВВБ (сопротивление изоляции)",
        "hv_safety_no_data": "ℹ️ Hybrid Assistant не считывает параметр сопротивления изоляции ВВБ через OBD — эта диагностика недоступна программно. Для проверки изоляции обратитесь в сервис с мегаомметром.",
        # --- Smart diagnostics ---
        "smart_diag_title": "Умный прогноз (Smart Diagnostics)",
        "soh_forecast_title": "Прогноз остатка ресурса ВВБ до критической дельты (0.20В)",
        "soh_forecast_result": "При текущей динамике критическая дельта ожидается примерно через {days} дн. ({date}).",
        "soh_forecast_stable": "Дельта напряжений стабильна или уменьшается — угрозы в обозримом будущем не выявлено.",
        "soh_no_data_hint": "Для расчёта прогноза ВВБ выполните тест HV Check в приложении на телефоне и обновите базу данных.",
        "maint_forecast_title": "Прогноз по регламентным работам",
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
        "logs_select_trip": "Поездка",
        "logs_select_day": "День",
        "logs_chart_speed_rpm": "Скорость и обороты ДВС",
        "logs_chart_hv": "Напряжение и ток батареи (HV)",
        "logs_chart_temps": "Температуры ДВС, инвертора и ВВБ",
        "logs_chart_mg": "Мотор-генераторы MG1 / MG2 (обороты и момент)",
        "logs_mg_note": "ℹ️ Hybrid Assistant не логирует фазные токи MG1/MG2 — доступны только обороты и крутящий момент.",
        # --- Полный отчёт по поездке (как в Hybrid Assistant) ---
        "rep_summary_title": "Сводка по поездке",
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
        "rep_soc_title": "Статистика заряда (SOC)",
        "rep_soc_note": "ℹ️ Разбивка \"откуда взялся заряд\" (рекуперация/накат/ДВС) — фирменный внутренний расчёт Hybrid Assistant, у нас нет доступа к точной формуле, поэтому не воспроизводится.",
        "rep_hv_title": "Высоковольтная батарея (ВВБ)",
        "rep_hv_levels": "Уровни",
        "rep_current": "Ток",
        "rep_voltage": "Напряжение",
        "rep_hv_power": "Мощность и лимиты",
        "rep_power": "Мощность",
        "rep_hv_from_batt": "Отдано батареей",
        "rep_hv_to_batt": "Заряжено в батарею",
        "rep_hv_balance": "Баланс энергии",
        "rep_ccl_dcl_note": "CCL/DCL — лимиты заряда/разряда батареи (меняются с уровнем заряда и температурой).",
        "rep_temp_title": "Температуры",
        "rep_temp_ambient": "Воздух",
        "rep_temp_room": "В салоне/корпусе",
        "rep_temp_coolant": "Охлаждающая жидкость ДВС",
        "rep_temp_inverter": "Инвертор",
        "rep_temp_mg": "Мотор-генератор",
        "rep_hv_probes": "Датчики ВВБ",
        "rep_elevation_title": "Высота над уровнем моря",
        "rep_altitude": "Высота, м",
        "rep_upward": "Подъём",
        "rep_downward": "Спуск",
        "rep_elevation_note": "Подъём/спуск считаются по колонке GPS-высоты в базе — она грубее, чем внутренний расчёт Hybrid Assistant, поэтому суммарный набор высоты может быть занижен.",
        "rep_energy_title": "Энергия от ДВС",
        "rep_energy_from_ice": "Энергия от ДВС",
        "rep_energy_per_100km": "Расход энергии",
        "rep_engine_title": "Двигатель",
        "rep_load": "Нагрузка",
        "rep_ignitions_total": "Запусков ДВС",
        "rep_ignitions_inefficient": "Неэффективных (<5 сек)",
        "rep_ignitions_note": "Неэффективным считается запуск ДВС короче 5 секунд — частые короткие пуски увеличивают износ.",
        "rep_engine_state": "Состояние ДВС",
        "rep_ice_running": "Работает (с топливом)",
        "rep_ice_spinning": "Крутится без топлива",
        "rep_ice_off": "Выключен",
        "rep_engine_state_note": "\"Крутится без топлива\" — накат/торможение двигателем без впрыска (приблизительная оценка по FUELFLOWH).",
        "rep_psd_title": "Планетарный редуктор (PSD): ДВС и MG1/MG2",
        "rep_ice_torque": "Момент ДВС (расч.)",
        "rep_psd_note": "Момент ДВС рассчитан из мощности и оборотов (М = P / ω) — это оценка, не прямое измерение.",
        "rep_trims_title": "Топливные коррекции",
        "rep_effective": "Суммарная",
        "rep_bsfc_title": "Удельный расход топлива (BSFC)",
        "rep_bsfc_avg": "Среднее",
        "rep_bsfc_std": "Ст. отклонение",
        "rep_bsfc_note": "BSFC (г/кВт·ч) — сколько топлива тратится на каждый кВт·ч выработанной ДВС мощности; чем меньше, тем эффективнее работает двигатель в данной точке. Считается только по ненулевым показаниям.",
        "rep_braking_title": "Торможение",
        "rep_brakings_total": "Всего торможений",
        "rep_brakings_good": "Только рекуперация",
        "rep_brakings_bad": "Только механическое",
        "rep_brakings_mixed": "Смешанные",
        "rep_braking_efficiency": "Эффективность торможений",
        "rep_energy_recovered": "Энергия рекуперации",
        "rep_braking_note": "Эффективность = доля торможений, обошедшихся полностью рекуперацией, без задействования колодок.",
        "rep_driver_eval_title": "Оценка стиля вождения",
        "rep_accel_nervousness": "\"Нервозность\" педали газа",
        "rep_driver_eval_note": "Нервозность педали — среднее изменение положения педали газа между замерами; чем выше, тем резче стиль езды.",
        "rep_glide_title": "Индекс наката (Glide)",
        "rep_glide_avg": "Средний индекс",
        "rep_glide_max": "Макс. индекс",
        "rep_glide_note": "Индекс наката показывает, насколько эффективно используется накат без тяги ДВС/электромотора. Точная методика Hybrid Assistant не раскрыта, здесь — по сырому показателю GLIDEINDEX из лога.",
        "rep_maps_title": "Карта поездки",
        "rep_charts_title": "Графики по времени",
        "logs_battlog_note": "Показаны отдельные датчики ВВБ из подробного лога (BATTLOG) за время этой поездки.",
        "logs_no_battlog": "Подробные датчики ВВБ (BATTLOG) для этой поездки недоступны — показана усреднённая температура ВВБ из основного лога.",
        # --- Вкладка 3: Dr. Prius ---
        "drprius_upload_label": "Загрузите ежемесячный CSV-отчёт Dr. Prius",
        "drprius_upload_help": "Можно загрузить сразу несколько файлов за разные месяцы.",
        "drprius_no_files": "Файлы Dr. Prius ещё не загружены.",
        "drprius_parse_error": "⚠️ Не удалось распознать формат файла {name}: не найдены столбцы с сопротивлением/напряжением по блокам. Проверьте, что заголовки колонок содержат слово resistance/opór и voltage/napięcie с номером блока.",
        "drprius_blocks_group": "Показатели по блокам ВВБ",
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
        "compare_trends_group": "Исторические тренды",
        "compare_trend_soh": "Тренд SOH во времени",
        "compare_trend_delta": "Рост дельты напряжений во времени",
        "compare_trend_seasonal": "Сезонное сравнение температур ВВБ (лето к лету)",
        "compare_seasonal_not_enough": "В базе данных пока только один сезон/год наблюдений — для сравнения \"лето к лету\" нужно больше исторических данных.",
        "ha_reports_title": "Тренды из HTML-отчётов Hybrid Assistant",
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
        "ha_maps_title": "Карты из отчёта Hybrid Assistant",
        "ha_trip_extras_title": "Данные из HTML-отчёта для этой поездки",
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
        "ha_trend_soc_title": "Откуда берётся заряд батареи",
        "ha_soc_brakings": "От рекуперации при торможении",
        "ha_soc_coasting": "От наката",
        "ha_soc_ice": "От ДВС",
        "ha_trend_soc_note": "Доля заряда, полученного от каждого источника, в % от общего прироста SOC за поездку.",
        "ha_trend_brakings_warn": "⚠️ Доля заряда от рекуперативного торможения снижается (~{value} п.п./мес.) — стоит проверить тормозную систему и работу рекуперации.",
        "ha_trend_brakings_ok": "Доля заряда от рекуперации стабильна или растёт — признаков износа не выявлено.",
        "ha_trend_glide_title": "Индекс наката (Glide) по отчётам",
        "ha_glide_score": "Glide score",
        "ha_trend_glide_note": "Индекс наката из официального расчёта Hybrid Assistant (точная методика не раскрыта производителем).",
        "ha_trend_glide_warn": "⚠️ Индекс наката снижается (~{value}/мес.) — возможен рост внутреннего сопротивления трансмиссии/PSD, стоит обратить внимание.",
        "ha_trend_glide_ok": "Индекс наката стабилен или растёт — признаков износа трансмиссии не выявлено.",
        "ha_trend_driver_title": "Стиль вождения по отчётам",
        "ha_accel_nervousness": "Нервозность педали газа",
        "ha_braking_efficiency": "Эффективность торможений, %",
        "ha_trend_driver_note": "Это про стиль вождения, а не про исправность автомобиля — просто дополнительный контекст.",
        "ha_bsfc_crosscheck_title": "BSFC по отчётам (сверка с расчётом из базы)",
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
        "drive_api_disabled": "❌ Ключ сервисного аккаунта прочитан верно, но в проекте Google Cloud {project} не включён Google Drive API. Откройте консоль Google Cloud, выберите этот проект, найдите «Google Drive API» и нажмите «Включить». Через пару минут обновите базу данных — синхронизация заработает.",
        "drive_json_invalid": "❌ Параметр gcp_service_account_json есть в Secrets, но внутри него не JSON ({error}). В тройных кавычках должно лежать содержимое скачанного JSON-файла как есть: пары вида \"ключ\": \"значение\" через двоеточие и запятые, а не строки вида ключ = \"значение\".",
        "storage_mode_drive_readonly": "⚠️ Журнал читается с Google Диска, но записывать туда приложение не может: не настроен сервисный аккаунт. Новые записи сохранятся только временно и пропадут при перезапуске. Как настроить: создайте сервисный аккаунт Google Cloud, дайте его email право «Редактор» на папку с базой, и вставьте его JSON-ключ в Secrets приложения под именем [gcp_service_account].",
        "storage_mode_local": "⚠️ Журнал хранится только во временной памяти контейнера и пропадёт при перезапуске приложения. Чтобы записи сохранялись навсегда, создайте сервисный аккаунт Google Cloud, дайте его email право «Редактор» на папку с базой на Google Диске и вставьте его JSON-ключ в Secrets приложения под именем [gcp_service_account].",
        "save_fill_all": "⚠️ Заполните все поля перед сохранением.",
        "invoice_upload_label": "📷 Сфотографируйте фактуру/чек — данные подставятся автоматически",
        "invoice_section_title": "Автоматическое распознавание фактуры",
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
        "app_title": "Toyota Yaris 4 Hybrid (2021) — Pełna diagnostyka",
        "language_label": "Język / Язык",
        "nav_section": "Sekcja",
        "app_header_title": "Panel diagnostyczny",
        "refresh_db_button": "🔄 Odśwież bazę danych",
        "map_style_label": "Styl mapy",
        "triplog_title": "Dokładna mapa przejazdu (TripLog + telemetria)",
        "triplog_explainer": "Geometria trasy pochodzi z TripLog — tam ślad GPS jest poprawny. Tryb EV/silnik pochodzi z telemetrii Hybrid Assistant, gdzie jest znany zawsze. Tam, gdzie telemetrii na dany moment brak, odcinek oznaczany jest osobnym kolorem, a nie zgadywany.",
        "triplog_upload_label": "Wgraj eksport tras KML z TripLog",
        "triplog_upload_help": "W TripLog: strona Trips → zaznacz przejazdy → eksport KML („route details”). Zwykły raport wysyłany e-mailem nie zadziała — nie zawiera geometrii tras.",
        "triplog_no_file": "Nie wgrano pliku z trasami.",
        "triplog_parse_failed": "❌ W pliku nie znaleziono tras. Upewnij się, że to eksport KML tras z TripLog, a nie raport przebiegu.",
        "triplog_loaded": "✅ Wczytano tras: {n}",
        "triplog_select_route": "Trasa",
        "triplog_select_day": "Dzień",
        "triplog_drive_found": "✅ Automatycznie pobrano z Google Drive: {n} plik(ów) z trasami.",
        "triplog_drive_none": "ℹ️ Nie znaleziono plików z trasami na Google Drive. Umieść eksporty KML w podfolderze triplog obok bazy danych — będą pobierane automatycznie. Albo wgraj ręcznie poniżej.",
        "triplog_drive_list": "Pokaż listę plików z Google Drive",
        "triplog_parsing": "Przetwarzam trasy…",
        "triplog_file_skipped": "⚠️ Pominięto plik „{name}”: nie znaleziono w nim tras.",
        "triplog_no_overlap": "⚠️ Nie znaleziono telemetrii z czasu tych tras — cały ślad zostanie oznaczony jako „brak danych o trybie”. Prawdopodobnie Hybrid Assistant nie zapisywał wtedy przejazdów albo baza nie została jeszcze odświeżona.",
        "triplog_offset_applied": "🕐 Wykryto rozbieżność zegarów między TripLog a telemetrią: zastosowano przesunięcie {hours} h (dopasowano {pct}% punktów).",
        "triplog_offset_none": "Zegary są zgodne, przesunięcie zbędne (dopasowano {pct}% punktów).",
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
        "tab1": "Analityka i Diagnostyka",
        "tab2": "Szczegółowe logi",
        "tab_triplog": "TripLog: trasy",
        "tab3": "Monitorowanie Dr. Prius",
        "tab4": "Porównanie i trendy",
        "tab5": "Przeglądy techniczne",
        "map_code_label": "Wprowadź kod dostępu",
        "access_dialog_subtitle": "Panel diagnostyczny",
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
        "map_section_title": "Mapa przejazdu",
        "map_section_group": "Mapy i trasy",
        "map_select_trip": "Wybierz przejazd",
        "map_param_label": "Parametr na mapie",
        "map_param_mode": "Tryb (EV / silnik)",
        "map_param_braking": "Hamowanie",
        "map_param_speed": "Prędkość",
        "map_param_soc": "Poziom naładowania (SOC)",
        "map_period_title": "Mapa za okres",
        "map_period_label": "Okres",
        "map_period_day": "Dzień",
        "map_period_week": "Tydzień",
        "map_period_month": "Miesiąc",
        "map_period_year": "Rok",
        "map_period_avg_consumption": "Średnie spalanie w okresie: {value} l/100km",
        "map_period_distance_odo": "Przebieg wg licznika",
        "map_period_distance_odo_help": "Licznik odczytywany jest bezpośrednio z auta przez OBD — to cała rzeczywiście przejechana droga w okresie, łącznie z przejazdami, których Hybrid Assistant nie zapisał.",
        "map_period_distance_logged": "W tym zapisane",
        "map_period_distance_logged_help": "Suma dystansów przejazdów, które Hybrid Assistant zdążył zarejestrować. Zapisuje tylko wtedy, gdy jest uruchomiony i połączony z adapterem OBD.",
        "map_period_gap_metric": "Bez zapisu",
        "map_period_gap_note": "W tym okresie {km} km przejechano bez zapisu Hybrid Assistant — aplikacja nie była wtedy połączona. Te kilometry nie są uwzględnione na mapie ani w obliczeniach spalania.",
        "map_period_trips": "Przejazdów w okresie",
        "triplog_day_distance": "Przebieg w dniu",
        "triplog_day_trips": "Przejazdów w dniu",
        "fuel_forecast_badge": "🔮 (prognoza)",
        "unit_kmh": "km/h",
        "unit_l100km": "l/100km",
        "unit_l": "l",
        "weather_title": "Warunki meteorologiczne przejazdu",
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
        "elevation_profile_title": "Profil wysokości (ukształtowanie trasy)",
        "elevation_no_data": "Brak danych o wysokości dla tego przejazdu.",
        "elevation_flat": "Wysokość nie zmieniała się na całej trasie — albo odcinek jest rzeczywiście płaski, albo GPS zapisywał wysokość z dokładnością do pełnych metrów.",
        "unit_price_per_l": "zł/l",
        "unit_rpm": "obr/min",
        "unit_nm": "Nm",
        "fuel_forecast_help": "Szacunek sterownika na podstawie czasu wtrysku (dane Hybrid Assistant) — nie jest to bezpośredni pomiar paliwa.",
        "fuel_real_badge": "🧾 (rzeczywisty)",
        "fuel_real_badge_short": "🧾 Dane wg paragonów",
        "fuel_real_badge_note": "🧾 Rzeczywiste spalanie wg paragonów ze stacji (raport Fuelio) — w odróżnieniu od prognozy sterownika, to potwierdzone litry i koszt.",
        "fuel_type_lpg": "LPG (gaz)",
        "fuel_type_petrol": "Benzyna",
        "map_day_refuel_note": "⛽ Tego dnia zatankowano: {fuel} — {liters} l po {price} zł/l.",
        "fuel_log_title": "Tankowania (dane rzeczywiste, raport Fuelio)",
        "fuel_log_no_data": "Brak danych o tankowaniach — wgraj raport Fuelio (PDF) do folderu na Google Drive obok bazy danych.",
        "fuel_last_refuel_date": "Ostatnie tankowanie",
        "fuel_liters": "Zatankowano",
        "fuel_price": "Cena",
        "fuel_days_ago": "{days} dni temu",
        "fuel_avg_consumption": "Średnie spalanie",
        "fuel_petrol_no_avg_note": "Brak danych — nie wiadomo, ile benzyny było w baku przed rozpoczęciem obserwacji, a spalanie mocno zależy od udziału używania benzyny (głównie rozruch/rozgrzewanie), więc uśrednianie po całym przebiegu byłoby mylące.",
        "fuel_trend_title": "Historia tankowań",
        "fuel_metric_label": "Wskaźnik",
        "fuel_metric_days": "Dni od poprzedniego tankowania",
        "fuel_metric_liters": "Ile zatankowano, l",
        "fuel_metric_cost": "Koszt, zł",
        "fuel_period_label": "Okres",
        "fuel_trend_health_title": "Trend rzeczywistego spalania LPG (wg paragonów)",
        "fuel_lpg_trend_warn": "⚠️ Rzeczywiste spalanie LPG rośnie (~{value} l/100km/mies.) — warto sprawdzić instalację LPG (wtryskiwacze, reduktor, mieszankę).",
        "fuel_lpg_trend_ok": "Rzeczywiste spalanie LPG jest stabilne lub maleje — nie wykryto oznak problemów z LPG.",
        "fuel_crosscheck_title": "Weryfikacja: prognoza sterownika vs rzeczywiste spalanie, wg miesięcy",
        "fuel_crosscheck_note": "Jeśli rozbieżność między prognozą a rzeczywistym spalaniem rośnie z czasem — możliwe rozkalibrowanie wtryskiwaczy/czujników, warto przyjrzeć się LTFT w zakładce \"Analityka\".",
        "legend_ev": "EV (silnik wyłączony)",
        "legend_ice": "Silnik pracuje",
        "expert_params_title": "Parametry eksperckie",
        "ltft_title": "Długoterminowa korekta paliwa (LTFT), średnia po montażu LPG",
        "ltft_warning": "⚠️ Zalecana kontrola wtryskiwaczy gazowych i mapy LPG (mieszanka nieoptymalna).",
        "hv_safety_title": "Wskaźnik bezpieczeństwa HV (rezystancja izolacji)",
        "hv_safety_no_data": "ℹ️ Hybrid Assistant nie odczytuje rezystancji izolacji HV przez OBD — ta diagnostyka jest niedostępna programowo. W celu sprawdzenia izolacji skontaktuj się z serwisem (megaomomierz).",
        "smart_diag_title": "Inteligentna prognoza (Smart Diagnostics)",
        "soh_forecast_title": "Prognoza zasobu baterii HV do krytycznej delty (0.20V)",
        "soh_forecast_result": "Przy obecnej dynamice krytyczna delta oczekiwana za ok. {days} dni ({date}).",
        "soh_forecast_stable": "Delta napięć jest stabilna lub maleje — nie wykryto zagrożenia w najbliższym czasie.",
        "soh_no_data_hint": "Aby obliczyć prognozę baterii HV, wykonaj test HV Check w aplikacji na telefonie i zaktualizuj bazę danych.",
        "maint_forecast_title": "Prognoza przeglądów okresowych",
        "maint_gbo_not_installed": "LPG jeszcze nie zamontowano (montaż przy przebiegu 117 000 km).",
        "maint_no_record_generic_remaining": "Nie znaleziono wpisu o wymianie w dzienniku. Obliczenia liczone są od 2021 roku produkcji auta i przebiegu 0 km. Pozostało wg harmonogramu: {km} km.",
        "maint_no_record_generic_overdue": "Nie znaleziono wpisu o wymianie w dzienniku. Obliczenia liczone są od 2021 roku produkcji auta i przebiegu 0 km. Wymiana przeoczona — przebieg bez wymiany: {km} km.",
        "maint_no_record_lpg_remaining": "Nie znaleziono wpisu o wymianie w dzienniku. Obliczenia liczone są od momentu montażu LPG (przebieg 117 000 km). Pozostało wg harmonogramu: {km} km.",
        "maint_no_record_lpg_overdue": "Nie znaleziono wpisu o wymianie w dzienniku. Obliczenia liczone są od momentu montażu LPG (przebieg 117 000 km). Wymiana przeoczona — przebieg bez wymiany: {km} km.",
        "cvt_oil_no_record_message": "Wymiana oleju w skrzyni e-CVT nie została odnotowana. Zalecenie Toyoty dla trudnych warunków eksploatacji to 90 000 km lub 5 lat. Zaleca się prewencyjną wymianę płynu Toyota ATF WS w celu ochrony silników elektrycznych MG1/MG2 przed przegrzaniem.",
        "radiator_forecast_title": "Prognoza zabrudzenia chłodnic (trend temperatur względem otoczenia)",
        "radiator_forecast_result": "Różnica temperatury falownika/silnika minus otoczenie rośnie o ~{value}°C miesięcznie — warto sprawdzić chłodnice.",
        "radiator_forecast_stable": "Różnica temperatur względem otoczenia jest stabilna — brak oznak zabrudzenia chłodnic.",
        "logs_select_trip": "Przejazd",
        "logs_select_day": "Dzień",
        "logs_chart_speed_rpm": "Prędkość i obroty silnika",
        "logs_chart_hv": "Napięcie i prąd baterii (HV)",
        "logs_chart_temps": "Temperatury silnika, falownika i baterii HV",
        "logs_chart_mg": "Silniki MG1 / MG2 (obroty i moment)",
        "logs_mg_note": "ℹ️ Hybrid Assistant nie loguje prądów fazowych MG1/MG2 — dostępne są tylko obroty i moment obrotowy.",
        # --- Pełny raport przejazdu (jak w Hybrid Assistant) ---
        "rep_summary_title": "Podsumowanie przejazdu",
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
        "rep_soc_title": "Statystyka naładowania (SOC)",
        "rep_soc_note": "ℹ️ Podział \"skąd wzięło się naładowanie\" (rekuperacja/wybieg/silnik spalinowy) to wewnętrzny, zastrzeżony algorytm Hybrid Assistant — nie mamy dostępu do dokładnego wzoru, więc nie jest odtwarzany.",
        "rep_hv_title": "Bateria wysokiego napięcia (HV)",
        "rep_hv_levels": "Poziomy",
        "rep_current": "Prąd",
        "rep_voltage": "Napięcie",
        "rep_hv_power": "Moc i limity",
        "rep_power": "Moc",
        "rep_hv_from_batt": "Oddane przez baterię",
        "rep_hv_to_batt": "Naładowane do baterii",
        "rep_hv_balance": "Bilans energii",
        "rep_ccl_dcl_note": "CCL/DCL — limity ładowania/rozładowania baterii (zmieniają się z poziomem naładowania i temperaturą).",
        "rep_temp_title": "Temperatury",
        "rep_temp_ambient": "Powietrze",
        "rep_temp_room": "W kabinie/obudowie",
        "rep_temp_coolant": "Płyn chłodniczy silnika",
        "rep_temp_inverter": "Falownik",
        "rep_temp_mg": "Silnik elektryczny",
        "rep_hv_probes": "Czujniki baterii HV",
        "rep_elevation_title": "Wysokość nad poziomem morza",
        "rep_altitude": "Wysokość, m",
        "rep_upward": "Podjazd",
        "rep_downward": "Zjazd",
        "rep_elevation_note": "Podjazd/zjazd liczone są na podstawie kolumny wysokości GPS w bazie — jest ona mniej dokładna niż wewnętrzne obliczenia Hybrid Assistant, więc łączny przyrost wysokości może być zaniżony.",
        "rep_energy_title": "Energia z silnika spalinowego",
        "rep_energy_from_ice": "Energia z silnika",
        "rep_energy_per_100km": "Zużycie energii",
        "rep_engine_title": "Silnik",
        "rep_load": "Obciążenie",
        "rep_ignitions_total": "Uruchomień silnika",
        "rep_ignitions_inefficient": "Nieefektywnych (<5 s)",
        "rep_ignitions_note": "Za nieefektywne uznaje się uruchomienie silnika krótsze niż 5 sekund — częste krótkie starty zwiększają zużycie.",
        "rep_engine_state": "Stan silnika",
        "rep_ice_running": "Pracuje (z paliwem)",
        "rep_ice_spinning": "Kręci się bez paliwa",
        "rep_ice_off": "Wyłączony",
        "rep_engine_state_note": "\"Kręci się bez paliwa\" — wybieg/hamowanie silnikiem bez wtrysku (przybliżona ocena na podstawie FUELFLOWH).",
        "rep_psd_title": "Przekładnia planetarna (PSD): silnik i MG1/MG2",
        "rep_ice_torque": "Moment silnika (wyl.)",
        "rep_psd_note": "Moment silnika obliczony z mocy i obrotów (M = P / ω) — to szacunek, nie bezpośredni pomiar.",
        "rep_trims_title": "Korekty paliwa",
        "rep_effective": "Łączna",
        "rep_bsfc_title": "Jednostkowe zużycie paliwa (BSFC)",
        "rep_bsfc_avg": "Średnia",
        "rep_bsfc_std": "Odch. std",
        "rep_bsfc_note": "BSFC (g/kWh) — ile paliwa zużywa się na każdą kWh mocy wytworzonej przez silnik; im mniej, tym silnik pracuje efektywniej w danym punkcie. Liczone tylko po niezerowych odczytach.",
        "rep_braking_title": "Hamowanie",
        "rep_brakings_total": "Wszystkich hamowań",
        "rep_brakings_good": "Tylko rekuperacja",
        "rep_brakings_bad": "Tylko mechaniczne",
        "rep_brakings_mixed": "Mieszane",
        "rep_braking_efficiency": "Efektywność hamowań",
        "rep_energy_recovered": "Energia z rekuperacji",
        "rep_braking_note": "Efektywność = odsetek hamowań, które obyły się wyłącznie rekuperacją, bez użycia klocków.",
        "rep_driver_eval_title": "Ocena stylu jazdy",
        "rep_accel_nervousness": "\"Nerwowość\" pedału gazu",
        "rep_driver_eval_note": "Nerwowość pedału — średnia zmiana położenia pedału gazu między pomiarami; im wyższa, tym bardziej gwałtowny styl jazdy.",
        "rep_glide_title": "Indeks wybiegu (Glide)",
        "rep_glide_avg": "Średni indeks",
        "rep_glide_max": "Maks. indeks",
        "rep_glide_note": "Indeks wybiegu pokazuje, jak efektywnie wykorzystywany jest wybieg bez napędu silnika/elektromotoru. Dokładna metodologia Hybrid Assistant nie jest ujawniona — tu użyto surowego wskaźnika GLIDEINDEX z logu.",
        "rep_maps_title": "Mapa przejazdu",
        "rep_charts_title": "Wykresy w czasie",
        "logs_battlog_note": "Pokazano osobne czujniki baterii HV ze szczegółowego logu (BATTLOG) dla tego przejazdu.",
        "logs_no_battlog": "Szczegółowe czujniki baterii HV (BATTLOG) niedostępne dla tego przejazdu — pokazano uśrednioną temperaturę z głównego logu.",
        "drprius_upload_label": "Wgraj miesięczny raport CSV z Dr. Prius",
        "drprius_upload_help": "Można wgrać od razu kilka plików za różne miesiące.",
        "drprius_no_files": "Pliki Dr. Prius nie zostały jeszcze wgrane.",
        "drprius_parse_error": "⚠️ Nie udało się rozpoznać formatu pliku {name}: brak kolumn z rezystancją/napięciem dla bloków. Sprawdź, czy nagłówki zawierają słowo resistance/opór oraz voltage/napięcie z numerem bloku.",
        "drprius_blocks_group": "Wskaźniki wg bloków baterii HV",
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
        "compare_trends_group": "Trendy historyczne",
        "compare_trend_soh": "Trend SOH w czasie",
        "compare_trend_delta": "Wzrost delty napięć w czasie",
        "compare_trend_seasonal": "Sezonowe porównanie temperatur HV (lato do lata)",
        "compare_seasonal_not_enough": "W bazie danych jest na razie tylko jeden sezon/rok obserwacji — do porównania \"lato do lata\" potrzeba więcej danych historycznych.",
        "ha_reports_title": "Trendy z raportów HTML Hybrid Assistant",
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
        "ha_maps_title": "Mapy z raportu Hybrid Assistant",
        "ha_trip_extras_title": "Dane z raportu HTML dla tego przejazdu",
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
        "ha_trend_soc_title": "Skąd bierze się naładowanie baterii",
        "ha_soc_brakings": "Z rekuperacji przy hamowaniu",
        "ha_soc_coasting": "Z wybiegu",
        "ha_soc_ice": "Z silnika spalinowego",
        "ha_trend_soc_note": "Udział naładowania z każdego źródła, w % całkowitego przyrostu SOC w przejeździe.",
        "ha_trend_brakings_warn": "⚠️ Udział naładowania z rekuperacji przy hamowaniu maleje (~{value} p.p./mies.) — warto sprawdzić układ hamulcowy i działanie rekuperacji.",
        "ha_trend_brakings_ok": "Udział naładowania z rekuperacji jest stabilny lub rośnie — nie wykryto oznak zużycia.",
        "ha_trend_glide_title": "Indeks wybiegu (Glide) wg raportów",
        "ha_glide_score": "Glide score",
        "ha_trend_glide_note": "Indeks wybiegu z oficjalnego obliczenia Hybrid Assistant (dokładna metodologia nie jest ujawniona przez producenta).",
        "ha_trend_glide_warn": "⚠️ Indeks wybiegu maleje (~{value}/mies.) — możliwy wzrost oporu wewnętrznego przekładni/PSD, warto zwrócić uwagę.",
        "ha_trend_glide_ok": "Indeks wybiegu jest stabilny lub rośnie — nie wykryto oznak zużycia przekładni.",
        "ha_trend_driver_title": "Styl jazdy wg raportów",
        "ha_accel_nervousness": "Nerwowość pedału gazu",
        "ha_braking_efficiency": "Efektywność hamowań, %",
        "ha_trend_driver_note": "To dotyczy stylu jazdy, a nie sprawności samochodu — dodatkowy kontekst.",
        "ha_bsfc_crosscheck_title": "BSFC wg raportów (weryfikacja z obliczeniem z bazy)",
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
        "drive_api_disabled": "❌ Klucz konta serwisowego został odczytany poprawnie, ale w projekcie Google Cloud {project} nie jest włączone Google Drive API. Otwórz konsolę Google Cloud, wybierz ten projekt, znajdź „Google Drive API” i kliknij „Włącz”. Po kilku minutach odśwież bazę danych — synchronizacja zacznie działać.",
        "drive_json_invalid": "❌ Parametr gcp_service_account_json jest w Secrets, ale w środku nie ma JSON-a ({error}). W potrójnych cudzysłowach powinna znaleźć się zawartość pobranego pliku JSON w oryginalnej postaci: pary \"klucz\": \"wartość\" z dwukropkiem i przecinkami, a nie wiersze typu klucz = \"wartość\".",
        "storage_mode_drive_readonly": "⚠️ Dziennik jest odczytywany z Google Drive, ale aplikacja nie może tam zapisywać: brak konta serwisowego. Nowe wpisy zapiszą się tylko tymczasowo i znikną po restarcie. Jak skonfigurować: utwórz konto serwisowe Google Cloud, nadaj jego adresowi e-mail uprawnienie „Edytor” do folderu z bazą i wklej jego klucz JSON do Secrets aplikacji pod nazwą [gcp_service_account].",
        "storage_mode_local": "⚠️ Dziennik przechowywany jest tylko w tymczasowej pamięci kontenera i zniknie po restarcie aplikacji. Aby wpisy zapisywały się na stałe, utwórz konto serwisowe Google Cloud, nadaj jego adresowi e-mail uprawnienie „Edytor” do folderu z bazą na Google Drive i wklej jego klucz JSON do Secrets aplikacji pod nazwą [gcp_service_account].",
        "save_fill_all": "⚠️ Uzupełnij wszystkie pola przed zapisaniem.",
        "invoice_upload_label": "📷 Sfotografuj fakturę/paragon — dane zostaną podstawione automatycznie",
        "invoice_section_title": "Automatyczne rozpoznawanie faktury",
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


def stacked_columns(n: int):
    """Колонки, которые на телефоне превращаются в вертикальный стек.

    Нужно для блоков с длинным текстом: в узкой колонке абзац
    вытягивается в «столбик» по два-три слова в строке и становится
    нечитаемым. Возвращает контейнеры с тем же интерфейсом, что и
    st.columns, поэтому вызывающий код не меняется."""
    if is_mobile():
        return [st.container() for _ in range(n)]
    return st.columns(n)


# Баннер вкладки «Техническое обслуживание»: личное фото с мойки.
# Кадрировано так, чтобы машина ушла вправо (слева ложится заголовок),
# и приглушено по яркости — белая пена иначе выбивалась из тёмной темы.
_BANNER_MAINTENANCE_B64 = "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"

# Баннер вкладки TripLog: карта Лодзи и Згежа, построенная по реальным
# GPS-трекам из TripLog (947 городских маршрутов). Отрисована светящимися
# линиями на графите — фон тёмный изначально, поэтому искусственное
# затемнение не требуется, в отличие от скриншота светлой карты.
# Композиция сдвинута вправо: слева ложится заголовок раздела.
_BANNER_TRIPLOG_B64 = "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"

# Баннеры вкладок. Ключ — идентификатор вкладки, значение — картинка в
# base64. Если для вкладки баннера нет, берётся общий (фото фары).
_TAB_BANNERS: dict = {
    "tab_triplog": _BANNER_TRIPLOG_B64,
    "tab5": _BANNER_MAINTENANCE_B64,
}


def render_app_header(section_title: str, tab_key: "str | None" = None) -> None:
    """Шапка с фотографией и названием текущего раздела."""
    image_b64 = _TAB_BANNERS.get(tab_key) or _HEADER_IMAGE_B64
    st.markdown(
        f"""
        <div class="app-header" style="background-image:
            linear-gradient(to right,
                rgba(10, 11, 14, 0.93) 0%,
                rgba(10, 11, 14, 0.62) 42%,
                rgba(10, 11, 14, 0.10) 100%),
            url('data:image/webp;base64,{image_b64}');">
          <div class="app-header-text">
            <div class="app-header-title">{section_title}</div>
            <div class="app-header-sub">Toyota Yaris 4 Hybrid</div>
          </div>
        </div>
        """,
        unsafe_allow_html=True,
    )


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

        /* Всплывающие подсказки: по умолчанию Streamlit обрезает длинный
           текст по ширине, из-за чего пояснения читались наполовину. */
        [data-testid="stTooltipContent"] {{
            max-width: min(92vw, 460px) !important;
            white-space: normal !important;
            overflow: visible !important;
            text-overflow: clip !important;
            line-height: 1.45;
            font-size: 0.85rem;
            padding: 0.7rem 0.85rem !important;
            background: rgba(18, 22, 28, 0.97) !important;
            border: 1px solid rgba(120, 200, 255, 0.20) !important;
            border-radius: 10px !important;
            box-shadow: 0 10px 32px rgba(0, 0, 0, 0.6) !important;
        }}
        [data-testid="stTooltipContent"] p {{
            white-space: normal !important;
            margin: 0;
        }}

        /* Навигация по разделам в боковой панели. */
        section[data-testid="stSidebar"] .stButton > button {{
            border-radius: 10px 10px 6px 6px !important;
            border: 1px solid rgba(140, 160, 200, 0.14) !important;
            border-bottom: 2px solid transparent !important;
            font-weight: 500 !important;
            text-align: left !important;
            justify-content: flex-start !important;
            padding: 0.55rem 0.8rem !important;
            transition: background 200ms ease, color 200ms ease,
                        border-color 240ms ease, box-shadow 240ms ease !important;
        }}
        section[data-testid="stSidebar"] .stButton > button:hover {{
            background: rgba(120, 200, 255, 0.09) !important;
            border-color: rgba(120, 200, 255, 0.30) !important;
            color: #9fd0ff !important;
        }}
        /* Активный раздел: заливка и синяя полоса снизу. */
        section[data-testid="stSidebar"] .stButton > button[kind="primary"] {{
            background: rgba(120, 200, 255, 0.12) !important;
            border-color: rgba(120, 200, 255, 0.26) !important;
            border-bottom-color: rgba(90, 180, 255, 0.95) !important;
            color: #eaf4ff !important;
            box-shadow: 0 3px 14px rgba(90, 180, 255, 0.16) !important;
        }}
        section[data-testid="stSidebar"] .stButton > button[kind="primary"]:hover {{
            background: rgba(120, 200, 255, 0.17) !important;
        }}

        /* На узком экране ряд из 4-5 метрик сжимается до нечитаемых
           колонок в пару символов шириной. Разрешаем колонкам переноситься
           и задаём минимальную ширину — получается аккуратная сетка
           по две метрики в ряд вместо пяти сплющенных. */
        @media (max-width: 640px) {{
            .app-header {{ height: 118px; }}
            .app-header-title {{ font-size: 1.05rem; }}
            .app-header-text {{ max-width: 72%; }}
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
                    _remember_drive_api_error(e)
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


def _render_access_dialog_styles() -> None:
    """Оформление экрана ввода кода: тёмная графитовая база, матовое
    стекло и тонкая неоновая рамка.

    Стили вставляются один раз за показ диалога и написаны так, чтобы
    ничего не считать в Python: браузер отрисовывает их сразу, без
    дополнительных запросов и без обращений к сети — фон уже вшит в
    страницу как base64."""
    st.markdown(
        f"""
        <style>
        /* Само окно диалога: убираем светлую подложку Streamlit и
           делаем глубокий антрацит с мягким свечением по краю. */
        div[role="dialog"] {{
            background: linear-gradient(160deg, #14171c 0%, #0d0f13 55%, #0a0b0e 100%) !important;
            border: 1px solid rgba(120, 200, 255, 0.14) !important;
            border-radius: 20px !important;
            box-shadow: 0 24px 70px rgba(0, 0, 0, 0.75),
                        0 0 0 1px rgba(120, 200, 255, 0.05) inset !important;
            overflow: hidden !important;
        }}
        div[role="dialog"] h2 {{
            font-size: 1.05rem !important;
            font-weight: 600 !important;
            letter-spacing: 0.02em;
            opacity: 0.92;
        }}

        /* Баннер с фотографией. Затемняющий градиент сверху вниз
           уводит низ снимка в фон карточки, чтобы не было резкой
           границы и текст читался поверх спокойно. */
        .hero-banner {{
            position: relative;
            height: 132px;
            margin: -0.25rem -0.25rem 1.1rem -0.25rem;
            border-radius: 14px;
            overflow: hidden;
            background-image:
                linear-gradient(to bottom,
                    rgba(10, 11, 14, 0.15) 0%,
                    rgba(10, 11, 14, 0.55) 55%,
                    rgba(13, 15, 19, 0.97) 100%),
                url("data:image/webp;base64,{_HERO_IMAGE_B64}");
            background-size: cover;
            background-position: center 42%;
        }}
        .hero-caption {{
            position: absolute;
            left: 14px;
            bottom: 10px;
            color: #eaf2ff;
            font-size: 0.95rem;
            font-weight: 600;
            letter-spacing: 0.01em;
            text-shadow: 0 2px 12px rgba(0, 0, 0, 0.85);
        }}
        .hero-caption span {{
            display: block;
            font-size: 0.72rem;
            font-weight: 400;
            opacity: 0.72;
            margin-top: 2px;
        }}

        /* Матовое стекло вокруг поля ввода. */
        div[role="dialog"] div[data-testid="stTextInput"] input {{
            background: rgba(255, 255, 255, 0.045) !important;
            backdrop-filter: blur(14px);
            -webkit-backdrop-filter: blur(14px);
            border: 1px solid rgba(120, 200, 255, 0.18) !important;
            border-radius: 12px !important;
            color: #eef4ff !important;
            padding: 0.65rem 0.85rem !important;
            transition: border-color 220ms ease, box-shadow 220ms ease,
                        background 220ms ease;
        }}
        div[role="dialog"] div[data-testid="stTextInput"] input:focus {{
            border-color: rgba(120, 200, 255, 0.55) !important;
            box-shadow: 0 0 0 3px rgba(90, 180, 255, 0.13),
                        0 0 18px rgba(90, 180, 255, 0.16) !important;
            background: rgba(255, 255, 255, 0.07) !important;
        }}

        /* Кнопки: плавные переходы, лёгкий подъём при наведении. */
        div[role="dialog"] .stButton > button {{
            border-radius: 12px !important;
            font-weight: 500 !important;
            padding: 0.6rem 1rem !important;
            transition: transform 200ms cubic-bezier(0.2, 0.8, 0.3, 1),
                        box-shadow 220ms ease,
                        background 220ms ease,
                        border-color 220ms ease !important;
        }}
        div[role="dialog"] .stButton > button:hover {{
            transform: translateY(-1px);
        }}
        div[role="dialog"] .stButton > button[kind="primary"] {{
            background: linear-gradient(135deg, #2f7fd4 0%, #1f5fa8 100%) !important;
            border: 1px solid rgba(140, 210, 255, 0.35) !important;
            color: #f4f9ff !important;
        }}
        div[role="dialog"] .stButton > button[kind="primary"]:hover {{
            box-shadow: 0 8px 26px rgba(47, 127, 212, 0.38),
                        0 0 0 1px rgba(140, 210, 255, 0.35) !important;
        }}
        div[role="dialog"] .stButton > button[kind="secondary"] {{
            background: rgba(255, 255, 255, 0.04) !important;
            backdrop-filter: blur(10px);
            -webkit-backdrop-filter: blur(10px);
            border: 1px solid rgba(255, 255, 255, 0.10) !important;
            color: #c9d4e3 !important;
        }}
        div[role="dialog"] .stButton > button[kind="secondary"]:hover {{
            background: rgba(255, 255, 255, 0.075) !important;
            border-color: rgba(255, 255, 255, 0.20) !important;
            color: #eaf2ff !important;
        }}

        /* Уважаем системную настройку «уменьшить движение». */
        @media (prefers-reduced-motion: reduce) {{
            div[role="dialog"] .stButton > button {{
                transition: none !important;
            }}
            div[role="dialog"] .stButton > button:hover {{
                transform: none;
            }}
        }}
        </style>
        """,
        unsafe_allow_html=True,
    )


@st.dialog("Код доступа / Kod dostępu")
def _map_access_code_dialog():
    _render_access_dialog_styles()
    st.markdown(
        f'<div class="hero-banner"><div class="hero-caption">Toyota Yaris 4 Hybrid'
        f'<span>{t("access_dialog_subtitle")}</span></div></div>',
        unsafe_allow_html=True,
    )

    remaining = _lockout_remaining_seconds("mapcode")

    if remaining > 0:
        minutes, seconds = divmod(remaining, 60)
        st.error(t("code_locked").format(minutes=minutes, seconds=seconds))
        if st.button(t("map_code_close_button"), width="stretch", key="map_code_close_locked"):
            st.session_state["map_dialog_completed"] = True
            st.session_state["map_unlocked"] = False
            st.rerun()
        return

    code_input = st.text_input(t("map_code_label"), type="password", key="map_code_dialog_input")

    # Кнопки друг под другом, а не в два столбца: на узком экране во
    # вторую колонку не помещалась подпись и обрезалась многоточием.
    # Основную кнопку выделяем стилем, а не значком — значок сути не
    # передаёт, а место занимает.
    check_clicked = st.button(
        t("map_code_check_button"), width="stretch", type="primary", key="map_code_check"
    )
    close_clicked = st.button(
        t("map_code_close_button"), width="stretch", key="map_code_close"
    )

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
    "alidade-smooth-dark": {
        # Обычные тайлы 256px, а не @2x: MapLibre внутри Plotly считает
        # размер тайла равным 256, и retina-версия 512px выравнивается
        # неправильно. Качество чуть ниже, зато карта действительно видна.
        "raster": "https://tiles.stadiamaps.com/tiles/alidade_smooth_dark/{z}/{x}/{y}.png",
        "attribution": "© Stadia Maps © OpenMapTiles © OpenStreetMap contributors",
        "needs_key": True,
        "label": {"ru": "Alidade Smooth Dark", "pl": "Alidade Smooth Dark"},
    },
    "carto-darkmatter": {
        "builtin": "carto-darkmatter",
        "label": {"ru": "CartoDB Dark Matter (тёмная)", "pl": "CartoDB Dark Matter (ciemna)"},
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

DEFAULT_MAP_STYLE = "alidade-smooth-dark"

# ============================================================
# ФОНОВОЕ ИЗОБРАЖЕНИЕ ЭКРАНА ВВОДА КОДА
# ============================================================
# Личное фото автомобиля, подготовленное для веба: кадрировано в
# горизонтальный баннер, ужато до 900px и сжато в WebP (~27 КБ).
# Встроено прямо в код в виде base64 намеренно: так браузеру не нужен
# отдельный сетевой запрос, и картинка появляется мгновенно вместе с
# диалогом, а не подгружается с задержкой.
_HERO_IMAGE_B64 = "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"

# Баннер шапки приложения: фото задней фары (авторское), кадрировано
# в горизонтальную полосу. Тёмная левая часть оставлена под заголовок.
# Снимок тёмный, поэтому WebP ужимает его всего до ~8 КБ.
_HEADER_IMAGE_B64 = "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"

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
    """Клиент Google Drive API, если настроен сервисный аккаунт.

    Поддерживаются два способа записи в Secrets:
      1) Секция [gcp_service_account] с полями по отдельности (классика).
      2) Один параметр gcp_service_account_json, в который вставлен ВЕСЬ
         JSON-файл ключа как есть, в тройных кавычках. Второй способ
         надёжнее: не нужно вручную переписывать JSON в TOML, а именно
         на этом чаще всего и ломается — длинные значения (private_key,
         ссылки на сертификаты) при переносе разрываются на несколько
         строк, а обычная строка TOML многострочной быть не может."""
    sa_info = None

    # Способ 2: цельный JSON одной строкой.
    try:
        raw_json = st.secrets.get("gcp_service_account_json")
    except Exception:
        raw_json = None
    if raw_json:
        try:
            sa_info = json.loads(str(raw_json))
        except Exception as e:
            print(f"[drive] gcp_service_account_json не разобран как JSON: {e!r}", flush=True)
            st.session_state["_drive_json_error"] = str(e)

    # Способ 1: обычная секция TOML.
    if sa_info is not None:
        st.session_state.pop("_drive_json_error", None)

    if sa_info is None:
        try:
            section = st.secrets.get("gcp_service_account")
        except Exception:
            section = None
        if section:
            sa_info = dict(section)

    if not sa_info:
        return None

    try:
        from google.oauth2 import service_account
        from googleapiclient.discovery import build

        creds = service_account.Credentials.from_service_account_info(
            sa_info, scopes=_DRIVE_SCOPES
        )
        return build("drive", "v3", credentials=creds, cache_discovery=False)
    except Exception as e:
        print(f"[drive] не удалось создать клиент Drive API: {e!r}", flush=True)
        return None


_DRIVE_API_DISABLED_MARKERS = ("accessNotConfigured", "has not been used in project")


def _remember_drive_api_error(error: Exception) -> None:
    """Запоминает характерные ошибки Drive API, чтобы показать причину в
    интерфейсе. Самая частая — API не включён в проекте Google Cloud:
    ключ при этом полностью рабочий, дело лишь в одной галочке в консоли."""
    message = str(error)
    if any(marker in message for marker in _DRIVE_API_DISABLED_MARKERS):
        project = ""
        match = re.search(r"project (\d+)", message)
        if match:
            project = match.group(1)
        st.session_state["_drive_api_disabled"] = project


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
        _remember_drive_api_error(e)
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

def render_sidebar(nav_renderer=None):
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

    # Навигация идёт сразу за языком: это главный элемент управления,
    # и листать до него через настройки карт было неудобно.
    if nav_renderer is not None:
        st.sidebar.divider()
        nav_renderer()

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
    # Цвета режима как в TripLog: EV — синий, ДВС — чёрный.
    # На тёмных подложках чёрный сливается с картой, поэтому там он
    # подменяется светлым (см. _mode_colors_for_current_style).
    "mode": {"EV": "#1477C7", "ICE": "#000000"},
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



_DARK_MAP_STYLES = {"carto-darkmatter", "alidade-smooth-dark"}


def _mode_colors_for_current_style() -> dict:
    """Цвета режима EV/ДВС с поправкой на тему подложки.
    Чёрная линия на тёмной карте попросту не видна, поэтому там вместо
    чёрного берём светло-серый — визуально это тот же «не-EV», но
    различимый."""
    colors = dict(_MAP_PARAM_COLORS["mode"])
    if get_selected_map_style() in _DARK_MAP_STYLES:
        colors["ICE"] = "#E8ECF2"
    return colors


# ============================================================
# МАРШРУТЫ ИЗ TRIPLOG (KML) + СШИВКА С ТЕЛЕМЕТРИЕЙ
# ============================================================
# Идея: у двух источников ломается разное. У Hybrid Assistant почти
# половина GPS-точек «залипает» при движении, но режим EV/ДВС известен
# всегда. У TripLog наоборот — нормальная геометрия трека, но нет
# сведений о работе двигателя. Сшиваем их по ВРЕМЕНИ.
#
# В KML геометрия лежит в <LineString> без отметок времени, а рядом
# идут отдельные точки <Point> с метками примерно каждые 5 минут.
# Поэтому время для каждой вершины трека получаем интерполяцией между
# ближайшими опорными точками пропорционально пройденному расстоянию.


# Допуск при сопоставлении точки трека с телеметрией. Телеметрия пишется
# примерно раз в 2.6 секунды, так что 15 секунд с запасом покрывают
# нормальную запись, но не дают «притянуть» режим из совсем другого
# момента поездки.
TELEMETRY_MATCH_TOLERANCE_S = 15


def _haversine_m(lat1, lon1, lat2, lon2):
    r = 6371000.0
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dp = math.radians(lat2 - lat1)
    dl = math.radians(lon2 - lon1)
    a = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * r * math.asin(math.sqrt(min(1.0, a)))


def _cumulative_distance_m(lat: np.ndarray, lon: np.ndarray) -> np.ndarray:
    """Накопленное расстояние вдоль трека, векторизованно.
    На больших выгрузках (сотни тысяч точек) поэлементный цикл в Python
    занимал бы десятки секунд, тогда как numpy справляется за миллисекунды."""
    if len(lat) < 2:
        return np.zeros(len(lat))
    p1 = np.radians(lat[:-1]); p2 = np.radians(lat[1:])
    dp = p2 - p1
    dl = np.radians(lon[1:] - lon[:-1])
    a = np.sin(dp / 2) ** 2 + np.cos(p1) * np.cos(p2) * np.sin(dl / 2) ** 2
    seg = 2 * 6371000.0 * np.arcsin(np.sqrt(np.clip(a, 0, 1)))
    return np.concatenate([[0.0], np.cumsum(seg)])


def _parse_kml_time(value: str):
    """KML от TripLog пишет время в нестандартном виде 07.09.2026T20:56:00Z.
    Суффикс Z означает UTC, поэтому приводим к местному времени — в базе
    Hybrid Assistant время тоже местное."""
    try:
        naive = datetime.strptime(value.strip(), "%d.%m.%YT%H:%M:%SZ")
    except ValueError:
        try:
            naive = datetime.strptime(value.strip(), "%Y-%m-%dT%H:%M:%SZ")
        except ValueError:
            return None
    utc = pd.Timestamp(naive, tz="UTC")
    return utc.tz_convert(LOCAL_TIMEZONE).tz_localize(None)


_KML_PLACEMARK_RE = re.compile(r"<Placemark>(.*?)</Placemark>", re.DOTALL)
_KML_NAME_RE = re.compile(r"<name>([^<]*)</name>")
_KML_DISTANCE_RE = re.compile(r"([\d]+[.,]?[\d]*)\s*km\s*$", re.IGNORECASE)
_KML_WHEN_RE = re.compile(r"<when>([^<]+)</when>")
_KML_COORDS_RE = re.compile(r"<coordinates>([^<]+)</coordinates>")


@st.cache_data(show_spinner=False)
def parse_triplog_kml(file_bytes: bytes) -> list:
    """Разбирает KML-экспорт TripLog. Возвращает список маршрутов:
    {name, points: DataFrame(lat, lon, dist_m, datetime)}.

    Разбор идёт по порядку элементов в файле: TripLog выкладывает
    точки с отметками времени непосредственно ПЕРЕД линией своего
    маршрута. Привязывать их по близости координат нельзя — по одним
    и тем же улицам ездишь каждый день, и к маршруту цеплялись метки
    от совершенно других поездок."""
    try:
        text = file_bytes.decode("utf-8", errors="replace")
    except Exception:
        return []

    routes = []
    pending_anchors = []

    for mark in _KML_PLACEMARK_RE.findall(text):
        coord_match = _KML_COORDS_RE.search(mark)
        if not coord_match:
            continue

        if "route_style" in mark:
            when = _KML_WHEN_RE.search(mark)
            ts = _parse_kml_time(when.group(1)) if when else None
            parts = coord_match.group(1).strip().split(",")
            if ts is not None and len(parts) >= 2:
                pending_anchors.append((float(parts[1]), float(parts[0]), ts))
            continue

        if "line_style" not in mark:
            continue

        coords = []
        for token in coord_match.group(1).split():
            parts = token.split(",")
            if len(parts) >= 2:
                coords.append((float(parts[1]), float(parts[0])))
        anchors, pending_anchors = pending_anchors, []
        if len(coords) < 2:
            continue

        df = pd.DataFrame(coords, columns=["lat", "lon"])
        df["dist_m"] = _cumulative_distance_m(df["lat"].to_numpy(), df["lon"].to_numpy())
        df["datetime"] = _assign_times_from_anchors(df, anchors)

        name_match = _KML_NAME_RE.search(mark)
        name = name_match.group(1).strip() if name_match else "?"
        km_match = _KML_DISTANCE_RE.search(name)
        distance_km = None
        if km_match:
            try:
                distance_km = float(km_match.group(1).replace(",", "."))
            except ValueError:
                distance_km = None
        if distance_km is None:
            distance_km = float(df["dist_m"].iloc[-1]) / 1000.0
        routes.append({"name": name, "points": df, "distance_km": distance_km})
    return routes


def _assign_times_from_anchors(df: pd.DataFrame, anchors: list) -> pd.Series:
    """Присваивает каждой вершине трека время. Опорные точки с метками
    привязываются к ближайшей вершине, между ними время распределяется
    пропорционально пройденному расстоянию (то есть предполагается
    равномерная скорость только на коротком участке между метками,
    а не на всём маршруте)."""
    times = pd.Series(pd.NaT, index=df.index, dtype="datetime64[ns]")
    if not anchors:
        return times

    lat = df["lat"].to_numpy()
    lon = df["lon"].to_numpy()
    for a_lat, a_lon, a_time in anchors:
        d = np.sqrt((lat - a_lat) ** 2 + (lon - a_lon) ** 2)
        idx = int(np.argmin(d))
        # Метка должна лежать на этом треке, а не на соседнем маршруте:
        # ~0.0015 градуса это примерно 150 метров.
        if d[idx] < 0.0015:
            times.iloc[idx] = a_time

    known = times.dropna()
    if len(known) < 2:
        return times

    # Линейная интерполяция по накопленному расстоянию.
    interp = np.interp(
        df["dist_m"].to_numpy(),
        df.loc[known.index, "dist_m"].to_numpy(),
        known.astype("int64").to_numpy(),
        left=np.nan,
        right=np.nan,
    )
    return pd.Series(pd.to_datetime(interp, errors="coerce"), index=df.index)


def match_route_with_telemetry(route_points: pd.DataFrame, fastlog: pd.DataFrame) -> pd.DataFrame:
    """Для каждой вершины трека находит ближайшую по времени запись
    телеметрии и берёт оттуда режим EV/ДВС. Там, где телеметрии нет
    (Hybrid Assistant не работал или разрыв в записи), режим помечается
    как unknown — это честнее, чем достраивать его догадками."""
    out = route_points.copy()
    out["mode"] = "unknown"
    if fastlog.empty or out["datetime"].isna().all():
        return out

    telemetry = fastlog.dropna(subset=["datetime"]).sort_values("datetime")
    if telemetry.empty:
        return out
    telemetry = telemetry.assign(datetime=telemetry["datetime"].astype("datetime64[ns]"))
    out["datetime"] = out["datetime"].astype("datetime64[ns]")

    valid = out["datetime"].notna()
    if not valid.any():
        return out

    matched = pd.merge_asof(
        out.loc[valid, ["datetime"]].sort_values("datetime").reset_index(),
        telemetry[["datetime", "mode"]].rename(columns={"mode": "tel_mode"}),
        on="datetime",
        direction="nearest",
        tolerance=pd.Timedelta(seconds=TELEMETRY_MATCH_TOLERANCE_S),
    ).set_index("index")

    out.loc[matched.index, "mode"] = matched["tel_mode"].fillna("unknown")
    return out


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
    color_map = (
        _mode_colors_for_current_style()
        if parameter == "mode"
        else _MAP_PARAM_COLORS.get(parameter, {})
    )
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
    color_map = (
        _mode_colors_for_current_style()
        if parameter == "mode"
        else _MAP_PARAM_COLORS.get(parameter, _MAP_PARAM_COLORS["mode"])
    )

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

    cols = stacked_columns(5)
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
    st.caption(t("fuel_real_badge_short"), help=t("fuel_real_badge_note"))


_TRIPLOG_MODE_LEGEND = {
    "EV": {"ru": "EV (ДВС выключен)", "pl": "EV (silnik wyłączony)"},
    "ICE": {"ru": "ДВС работает", "pl": "Silnik pracuje"},
    "unknown": {"ru": "Нет данных о режиме", "pl": "Brak danych o trybie"},
}


def _best_time_offset(routes: list, fastlog: pd.DataFrame) -> "tuple[int, float]":
    """Подбирает сдвиг времени между TripLog и телеметрией.

    KML помечает время суффиксом Z (UTC), но приложения не всегда пишут
    его честно. Если ошибиться на пару часов, вся раскраска станет
    правдоподобной, но неверной — поэтому сдвиг подбирается по факту:
    берётся тот, при котором совпало больше всего точек.
    Возвращает (сдвиг в часах, доля совпавших точек)."""
    if fastlog.empty or not routes:
        return 0, 0.0
    telemetry = fastlog.dropna(subset=["datetime"]).sort_values("datetime")
    if telemetry.empty:
        return 0, 0.0

    all_times = pd.concat([r["points"]["datetime"] for r in routes]).dropna()
    if all_times.empty:
        return 0, 0.0
    # Для определения сдвига достаточно выборки: перебирать сотни тысяч
    # точек по семь раз незачем, а на нескольких тысячах ответ тот же.
    if len(all_times) > 4000:
        all_times = all_times.sample(4000, random_state=0)
    all_times = all_times.astype("datetime64[ns]")
    telemetry = telemetry.assign(datetime=telemetry["datetime"].astype("datetime64[ns]"))

    best_offset, best_rate = 0, 0.0
    for offset in range(-3, 4):
        shifted = (all_times + pd.Timedelta(hours=offset)).sort_values()
        merged = pd.merge_asof(
            pd.DataFrame({"datetime": shifted}),
            telemetry[["datetime", "mode"]].rename(columns={"mode": "m"}),
            on="datetime",
            direction="nearest",
            tolerance=pd.Timedelta(seconds=TELEMETRY_MATCH_TOLERANCE_S),
        )
        rate = merged["m"].notna().mean()
        if rate > best_rate:
            best_offset, best_rate = offset, float(rate)
    return best_offset, best_rate


def render_triplog_route_section(fastlog: pd.DataFrame) -> None:
    """Точная карта поездки: геометрия из TripLog, режим EV/ДВС из
    телеметрии Hybrid Assistant, отдельный цвет там, где режим неизвестен."""
    st.subheader(t("triplog_title"))
    st.caption(t("triplog_explainer"))

    # Сначала показываем, что уже нашлось на Google Диске автоматически.
    drive_files = get_triplog_files_from_drive()
    if drive_files:
        st.success(t("triplog_drive_found").format(n=len(drive_files)))
        st.caption(", ".join(f.name for f in drive_files))
    else:
        st.info(t("triplog_drive_none"))

    st.file_uploader(
        t("triplog_upload_label"), type=["kml"], key="triplog_uploader",
        accept_multiple_files=True, help=t("triplog_upload_help"),
    )

    all_files = get_all_triplog_files()
    if not all_files:
        st.info(t("triplog_no_file"))
        return

    routes = []
    failed = []
    with st.spinner(t("triplog_parsing")):
        for f in all_files:
            try:
                parsed = parse_triplog_kml(f.getvalue())
            except Exception:
                parsed = []
            if parsed:
                routes.extend(parsed)
            else:
                failed.append(f.name)

    if not routes:
        st.error(t("triplog_parse_failed"))
        return
    st.success(t("triplog_loaded").format(n=len(routes)))
    for name in failed:
        st.warning(t("triplog_file_skipped").format(name=name))

    offset, rate = _best_time_offset(routes, fastlog)
    if rate < 0.05:
        st.warning(t("triplog_no_overlap"))
    elif offset != 0:
        st.info(t("triplog_offset_applied").format(hours=offset, pct=f"{rate*100:.0f}"))
    else:
        st.caption(t("triplog_offset_none").format(pct=f"{rate*100:.0f}"))

    # Название маршрута начинается с даты ("08.09.2026 Business 4,7 km"),
    # поэтому сначала сужаем выбор по дню — иначе в списке оказываются
    # тысячи пунктов и найти нужную поездку невозможно.
    by_date = {}
    for i, r in enumerate(routes):
        day = r["name"].split()[0] if r["name"] else "?"
        by_date.setdefault(day, []).append(i)

    def _day_key(d):
        try:
            return datetime.strptime(d, "%d.%m.%Y")
        except ValueError:
            return datetime.min

    days = sorted(by_date.keys(), key=_day_key, reverse=True)
    chosen_day = st.selectbox(t("triplog_select_day"), days, key="triplog_day_select")
    day_routes = by_date[chosen_day]

    # Пробег берём из данных самого TripLog: он считает его по полному
    # GPS-треку, тогда как сумма отрезков прореженной полилинии на карте
    # занижает результат примерно на 2%.
    day_km = sum(routes[i].get("distance_km") or 0.0 for i in day_routes)
    dc1, dc2 = st.columns(2)
    dc1.metric(t("triplog_day_distance"), f"{day_km:.1f} {t('unit_km')}")
    dc2.metric(t("triplog_day_trips"), f"{len(day_routes)}")

    labels = {i: routes[i]["name"] for i in day_routes}
    idx = st.selectbox(
        t("triplog_select_route"), list(labels.keys()),
        format_func=lambda i: labels[i], key="triplog_route_select",
    )
    points = routes[idx]["points"].copy()
    if offset:
        points["datetime"] = points["datetime"] + pd.Timedelta(hours=offset)
    matched = match_route_with_telemetry(points, fastlog)

    lang = st.session_state.get("lang", "pl")
    mode_colors = _mode_colors_for_current_style()
    colors = {
        "EV": mode_colors["EV"],
        "ICE": mode_colors["ICE"],
        "unknown": "#8A8F98",
    }

    fig = go.Figure()
    # Рисуем сплошными отрезками одного режима, чтобы линия не рвалась.
    start = 0
    for i in range(1, len(matched) + 1):
        if i == len(matched) or matched["mode"].iloc[i] != matched["mode"].iloc[start]:
            seg = matched.iloc[start : i + (1 if i < len(matched) else 0)]
            mode = matched["mode"].iloc[start]
            fig.add_trace(
                go.Scattermap(
                    lat=seg["lat"], lon=seg["lon"], mode="lines",
                    line=dict(width=5, color=colors.get(mode, "#8A8F98")),
                    showlegend=False, hoverinfo="skip",
                )
            )
            start = i

    fig.update_layout(
        map=build_map_config(matched["lat"].mean(), matched["lon"].mean(), 12),
        margin=dict(l=0, r=0, t=0, b=0),
        height=rsp_height(460),
    )
    st.plotly_chart(fig, width="stretch", key="triplog_route_map")

    swatches = "".join(
        f'<span style="display:inline-flex;align-items:center;margin-right:18px;">'
        f'<span style="width:14px;height:14px;background:{colors[k]};display:inline-block;'
        f'border-radius:3px;margin-right:6px;"></span>{_TRIPLOG_MODE_LEGEND[k][lang]}</span>'
        for k in ("EV", "ICE", "unknown")
    )
    st.markdown(f'<div style="margin-top:6px;">{swatches}</div>', unsafe_allow_html=True)

    counts = matched["mode"].value_counts()
    total = len(matched)
    c1, c2, c3 = st.columns(3)
    c1.metric(_TRIPLOG_MODE_LEGEND["EV"][lang], f"{counts.get('EV', 0) / total * 100:.0f}%")
    c2.metric(_TRIPLOG_MODE_LEGEND["ICE"][lang], f"{counts.get('ICE', 0) / total * 100:.0f}%")
    c3.metric(_TRIPLOG_MODE_LEGEND["unknown"][lang], f"{counts.get('unknown', 0) / total * 100:.0f}%")


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


def render_tab_triplog(fastlog_df) -> None:
    """Отдельная вкладка TripLog. Сшивка маршрутов с телеметрией
    Hybrid Assistant сохранена — она и есть смысл раздела; из главной
    вкладки блок убран, чтобы не занимать там место."""
    if not maps_are_unlocked():
        render_maps_locked_placeholder()
        return
    render_triplog_route_section(fastlog_df)


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

    with st.expander(t("map_section_group"), expanded=True, icon=":material/map:"):
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
                period_distance = period_trips["distance"].sum()

                # Одометр ODO читается напрямую с машины по OBD, поэтому его
                # прирост — это ВЕСЬ реально пройденный путь за период,
                # включая поездки, которые Hybrid Assistant не записал
                # (он пишет только когда запущен и подключён к адаптеру).
                period_odo = pd.to_numeric(
                    period_df["ODO"], errors="coerce"
                ).dropna() if "ODO" in period_df.columns else pd.Series(dtype=float)
                odo_distance = (
                    float(period_odo.max() - period_odo.min())
                    if len(period_odo) >= 2 else None
                )

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
                    pc1, pc2, pc3 = st.columns(3)
                    pc1.metric(
                        t("map_period_distance_odo"),
                        (f"{odo_distance:,.0f}".replace(",", " ") + f" {t('unit_km')}")
                        if odo_distance is not None else "—",
                        help=t("map_period_distance_odo_help"),
                    )
                    pc2.metric(
                        t("map_period_distance_logged"),
                        f"{period_distance:,.1f}".replace(",", " ") + f" {t('unit_km')}",
                        help=t("map_period_distance_logged_help"),
                    )
                    pc3.metric(t("map_period_trips"), f"{len(period_trips)}")
                    if odo_distance is not None and period_distance > 0:
                        gap = odo_distance - period_distance
                        if gap > max(5.0, odo_distance * 0.05):
                            st.metric(
                                t("map_period_gap_metric"),
                                f"{gap:,.0f}".replace(",", " ") + f" {t('unit_km')}",
                                help=t("map_period_gap_note").format(
                                    km=f"{gap:,.0f}".replace(",", " ")
                                ),
                            )
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

    with st.expander(t("fuel_log_title"), expanded=False, icon=":material/local_gas_station:"):
        _render_fuel_log_section(fuel_df)

    st.divider()

    with st.expander(t("expert_params_title"), expanded=False, icon=":material/science:"):
        # --- Экспертные параметры ---
        st.subheader(t("expert_params_title"))
        ecol1, ecol2 = stacked_columns(2)
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

    with st.expander(t("smart_diag_title"), expanded=False, icon=":material/insights:"):
        # --- Smart Diagnostics ---
        st.subheader(t("smart_diag_title"))
        dcol1, dcol2 = stacked_columns(2)
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

    with st.expander(t("maint_forecast_title"), expanded=False, icon=":material/build:"):
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

    # Короткая сводка всегда на виду — без раскрытия блоков.
    s0, f0 = report["summary"], report["fuel"]
    k1, k2, k3, k4 = st.columns(4)
    k1.metric(t("rep_distance"), fmt(s0["distance_total"], f" {t('unit_km')}", 1))
    k2.metric(t("rep_time"), _fmt_hms(s0["time_total_s"]))
    ev_share = (
        s0["distance_ev"] / s0["distance_total"] * 100
        if s0.get("distance_ev") and s0.get("distance_total") else None
    )
    k3.metric(t("metric_ev_pct"), fmt(ev_share, "%", 0))
    k4.metric(
        f"{t('rep_fuel_consumption')} {t('fuel_forecast_badge')}",
        fmt(f0["consumption_l100"], f" {t('unit_l100km')}", 2),
        help=t("fuel_forecast_help"),
    )
    st.divider()

    with st.expander(t("rep_summary_title"), expanded=False, icon=":material/summarize:"):
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

    with st.expander(t("rep_soc_title"), icon=":material/battery_charging_full:"):
        soc = report["soc"]
        _render_matrix_table(
            [L("avg"), L("start"), L("end"), L("delta"), L("min"), L("max"), L("std")],
            ["SOC"],
            [[fmt(soc[k], "%", 2)] for k in ("avg", "start", "end", "delta", "min", "max", "std")],
            key="matrix_table_2",
        )
        st.caption(t("rep_soc_note"))

    with st.expander(t("rep_hv_title"), icon=":material/bolt:"):
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

    with st.expander(t("rep_temp_title"), icon=":material/thermostat:"):
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
        with st.expander(t("rep_elevation_title"), icon=":material/terrain:"):
            e = report["elevation"]
            _render_matrix_table(
                [t("rep_altitude")],
                [L("avg"), L("start"), L("end"), L("min"), L("max"), t("rep_upward"), t("rep_downward"), L("delta")],
                [[fmt(e[k], " м", 0) for k in ("avg", "start", "end", "min", "max", "upward", "downward", "delta")]],
                key="matrix_table_7",
            )
            st.caption(t("rep_elevation_note"))

    with st.expander(t("rep_energy_title"), icon=":material/local_fire_department:"):
        ee = report["energy_engine"]
        c1, c2 = st.columns(2)
        c1.metric(t("rep_energy_from_ice"), fmt(ee["energy_kwh"], " kWh", 2))
        c2.metric(t("rep_energy_per_100km"), fmt(ee["energy_kwh_100km"], " kWh/100км", 2))

    with st.expander(t("rep_engine_title"), icon=":material/settings:"):
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

    with st.expander(t("rep_psd_title"), icon=":material/precision_manufacturing:"):
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

    with st.expander(t("rep_trims_title"), icon=":material/tune:"):
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

    with st.expander(t("rep_bsfc_title"), icon=":material/eco:"):
        b = report["bsfc"]
        c1, c2 = st.columns(2)
        c1.metric(t("rep_bsfc_avg"), fmt(b["avg"], " g/kWh", 0))
        c2.metric(t("rep_bsfc_std"), fmt(b["std"], "", 0))
        st.caption(t("rep_bsfc_note"))

    with st.expander(t("rep_braking_title"), icon=":material/pan_tool:"):
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

    with st.expander(t("rep_driver_eval_title"), icon=":material/person:"):
        de = report["driver_eval"]
        c1, c2, c3 = st.columns(3)
        c1.metric(t("rep_accel_nervousness"), fmt(de["accel_nervousness"], "", 2))
        c2.metric(t("rep_braking_efficiency"), fmt(de["braking_efficiency_pct"], "%", 1))
        c3.metric(t("rep_ignitions_inefficient"), f"{de['inefficient_ignitions']}/{de['total_ignitions']}")
        st.caption(t("rep_driver_eval_note"))

    with st.expander(t("rep_glide_title"), icon=":material/air:"):
        g = report["glide"]
        c1, c2 = st.columns(2)
        c1.metric(t("rep_glide_avg"), fmt(g["avg"], "", 1))
        c2.metric(t("rep_glide_max"), fmt(g["max"], "", 1))
        st.caption(t("rep_glide_note"))


def render_tab2(trips_df, fastlog_df, db_path, file_version):
    if trips_df.empty or fastlog_df.empty:
        st.info(t("no_trip_data"))
        return

    ordered = trips_df.sort_values("date", ascending=False)
    by_day = {}
    for idx, row in ordered.iterrows():
        by_day.setdefault(row["date"].strftime("%Y-%m-%d"), []).append(idx)

    sc1, sc2 = st.columns([1, 2])
    with sc1:
        chosen_day = st.selectbox(
            t("logs_select_day"), list(by_day.keys()), key="tab2_day_select"
        )
    day_indices = by_day[chosen_day]
    trip_options = {
        f"{trips_df.loc[i, 'date'].strftime('%H:%M')} — "
        f"{trips_df.loc[i, 'distance']:.1f} {t('unit_km')}": i
        for i in day_indices
    }
    with sc2:
        selected_label = st.selectbox(
            t("logs_select_trip"), list(trip_options.keys()), key="tab2_trip_select"
        )
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
    with st.expander(t("ha_trip_extras_title"), icon=":material/description:"):
        render_ha_trip_extras(sel_row)

    with st.expander(t("rep_maps_title"), icon=":material/map:"):
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
    with st.expander(t("rep_charts_title"), icon=":material/show_chart:"):
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

    with st.expander(t("drprius_blocks_group"), expanded=True, icon=":material/bar_chart:"):
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
    with st.expander(t("drprius_wear_title"), expanded=False, icon=":material/trending_down:"):
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
    with st.expander(t("drprius_temp_spread_title"), expanded=False, icon=":material/thermostat:"):
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


def find_triplog_kml_files(folder_path: str) -> list:
    """Ищет KML-маршруты TripLog в скачанной папке Google Диска.
    Обходятся и вложенные папки, поэтому достаточно положить файлы в
    подпапку triplog рядом с базой — скачивание через Drive API
    забирает вложенные папки целиком."""
    found = []
    for root, _dirs, files in os.walk(folder_path):
        for fname in files:
            if fname.lower().endswith(".kml"):
                found.append(os.path.join(root, fname))
    return sorted(found)


def get_triplog_files_from_drive() -> list:
    try:
        return [LocalReportFile(p) for p in find_triplog_kml_files(LOCAL_DB_FOLDER_PATH)]
    except Exception:
        return []


def get_all_triplog_files() -> list:
    """Все доступные KML: скачанные с Google Диска и загруженные вручную.
    При совпадении имён приоритет у загруженного вручную."""
    manual = list(st.session_state.get("triplog_uploader") or [])
    manual_names = {f.name for f in manual}
    from_drive = [f for f in get_triplog_files_from_drive() if f.name not in manual_names]
    return manual + from_drive


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
    with st.expander(t("compare_table_title"), expanded=True, icon=":material/compare_arrows:"):
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

    with st.expander(t("compare_trends_group"), expanded=False, icon=":material/trending_up:"):
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
    with st.expander(t("fuel_trend_health_title"), expanded=False, icon=":material/local_gas_station:"):
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
                st.caption(t("fuel_real_badge_short"), help=t("fuel_real_badge_note"))

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
        with st.expander(t("ha_reports_drive_list"), expanded=False, icon=":material/folder:"):
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
        with st.expander(t("ha_reports_details"), expanded=False, icon=":material/checklist:"):
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
    with st.expander(t("ha_maps_title"), expanded=False, icon=":material/map:"):
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

    with st.expander(t("ha_trend_soc_title"), expanded=True, icon=":material/battery_charging_full:"):
        fig = go.Figure()
        fig.add_trace(go.Scatter(x=reports_df["finish"], y=reports_df.get("soc_gained_brakings"), name=t("ha_soc_brakings"), mode="lines+markers"))
        fig.add_trace(go.Scatter(x=reports_df["finish"], y=reports_df.get("soc_gained_coasting"), name=t("ha_soc_coasting"), mode="lines+markers"))
        fig.add_trace(go.Scatter(x=reports_df["finish"], y=reports_df.get("soc_charged_by_ice"), name=t("ha_soc_ice"), mode="lines+markers"))
        fig.update_layout(height=rsp_height(320), yaxis_title="%")
        st.plotly_chart(fig, width="stretch", key="tab4_ha_soc_trend")
        st.caption(t("ha_trend_soc_note"))
        if "soc_gained_brakings" in reports_df.columns:
            _trend_check(reports_df["soc_gained_brakings"], reports_df["finish"], "ha_trend_brakings_warn", "ha_trend_brakings_ok")

    with st.expander(t("ha_trend_glide_title"), icon=":material/air:"):
        if "glide_score" in reports_df.columns:
            fig = go.Figure(go.Scatter(x=reports_df["finish"], y=reports_df["glide_score"], mode="lines+markers"))
            fig.update_layout(height=rsp_height(300), yaxis_title=t("ha_glide_score"))
            st.plotly_chart(fig, width="stretch", key="tab4_ha_glide_trend")
            st.caption(t("ha_trend_glide_note"))
            _trend_check(reports_df["glide_score"], reports_df["finish"], "ha_trend_glide_warn", "ha_trend_glide_ok")
        else:
            st.info(t("not_enough_data"))

    with st.expander(t("ha_trend_driver_title"), icon=":material/person:"):
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

    with st.expander(t("ha_bsfc_crosscheck_title"), icon=":material/eco:"):
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

        with st.expander(header, icon=":material/receipt_long:"):
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

    json_error = st.session_state.get("_drive_json_error")
    if json_error:
        st.error(t("drive_json_invalid").format(error=json_error))

    disabled_project = st.session_state.get("_drive_api_disabled")
    if disabled_project is not None:
        st.error(t("drive_api_disabled").format(project=disabled_project or "—"))

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
    with st.expander(t("maintenance_status_title"), expanded=True, icon=":material/event_available:"):
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
    with st.expander(t("add_record_header"), expanded=False, icon=":material/add_circle:"):
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
                preview_col, result_col = (
                    stacked_columns(2) if is_mobile() else st.columns([1, 2])
                )
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

    tab_keys = ["tab1", "tab2", "tab_triplog", "tab3", "tab4", "tab5"]

    # На телефоне шесть вкладок сверху не помещаются и обрезаются, поэтому
    # там навигация уезжает в боковую панель, а на экране остаётся только
    # выбранный раздел. На широком экране вкладки удобнее — оставляем их.
    mobile_nav = is_mobile()

    def _render_nav() -> None:
        # Названия считаются здесь, а не заранее: язык выбирается выше в
        # той же панели, и до её отрисовки они были бы от прошлого языка.
        #
        # Используются обычные кнопки, а не переключатель: у радио-кнопок
        # Streamlit рисует собственный кружок глубоко внутри разметки, и
        # убрать его стилями надёжно не выходит — вёрстка меняется от
        # версии к версии. С кнопками активный раздел выделяется штатным
        # видом primary, без вмешательства во внутренности виджета.
        titles = [t(k) for k in tab_keys]
        current = int(st.session_state.get("_active_tab", 0))
        current = current if 0 <= current < len(titles) else 0
        for i, title in enumerate(titles):
            if st.sidebar.button(
                title,
                key=f"nav_{tab_keys[i]}",
                width="stretch",
                type="primary" if i == current else "secondary",
            ):
                st.session_state["_active_tab"] = i
                st.rerun()

    render_sidebar(_render_nav if mobile_nav else None)

    tab_titles = [t(k) for k in tab_keys]
    active = None
    if mobile_nav:
        active = int(st.session_state.get("_active_tab", 0))
        active = active if 0 <= active < len(tab_keys) else 0
        render_app_header(tab_titles[active], tab_keys[active])
    else:
        render_app_header(t("app_header_title"), "tab1")
        tabs = st.tabs(tab_titles)

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

    def _db_problem() -> bool:
        """Сообщение о проблеме с базой. True, если раздел рисовать нельзя."""
        if db_ok:
            return False
        if db_missing:
            st.warning(t("db_missing"))
        else:
            st.error(t("db_error").format(error=db_error_message))
        return True

    def _render_section(index: int) -> None:
        key = tab_keys[index]
        if key == "tab1":
            if not _db_problem():
                render_tab1(trips_df, fastlog_df, temp_df, cell_df, db_path, file_version, fuel_df)
        elif key == "tab2":
            if not _db_problem():
                render_tab2(trips_df, fastlog_df, db_path, file_version)
        elif key == "tab_triplog":
            if not _db_problem():
                render_tab_triplog(fastlog_df)
        elif key == "tab3":
            render_tab3()
        elif key == "tab4":
            if not _db_problem():
                render_tab4(trips_df, temp_df, cell_df, fuel_df)
        else:
            render_tab5(db_path, file_version)

    if mobile_nav:
        # Рисуем только выбранный раздел: на телефоне это ещё и заметно
        # быстрее, чем считать все пять сразу, как делают вкладки.
        _render_section(active)
    else:
        for i, tab in enumerate(tabs):
            with tab:
                _render_section(i)


if __name__ == "__main__":
    main()
