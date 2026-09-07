# -*- coding: utf-8 -*-
"""
Toyota Yaris 4 Hybrid (2021) — Панель диагностики / Panel diagnostyczny
Источник данных: hybridassistant.db (SQLite, приложение Hybrid Assistant),
скачивается автоматически с Google Диска при запуске приложения.

Разверни на Streamlit Community Cloud: положи этот файл и requirements.txt
в репозиторий на GitHub. Саму базу данных .db в репозиторий загружать
НЕ нужно — она скачивается с Google Диска по ссылке ниже (GDRIVE_FILE_ID).

Схема БД (проверена на реальном файле hybridassistant.db):
  TRIPS       (TSDEB, TSFIN, NBSEC, NKMS)              — сводка по поездкам
  FASTLOG     (TIMESTAMP, TRIPFUEL(мл), ICE_TEMP,
               INVERTER_TEMP, BATTERY_TEMP, ...)        — подробная телеметрия
  BATTLOG     (TIMESTAMP, CELL_01..CELL_19, ...)        — поблочные напряжения (если включено HighSpeedLogging)
  HVCHECKCELL (TIMESTAMP, ELEMENT, VALUE)                — поблочные напряжения во время процедуры HV Check
TSDEB/TSFIN/TIMESTAMP хранятся в миллисекундах Unix-времени.
TRIPFUEL обнуляется в начале каждой поездки и накапливается в миллилитрах.
"""

import hashlib
import hmac
import json
import os
import sqlite3
import time
from datetime import date

import gdown
import pandas as pd
import plotly.graph_objects as go
import streamlit as st

# ============================================================
# КОНФИГУРАЦИЯ
# ============================================================

# --- Источник базы данных: Google Диск ---
# ID файла взят из ссылки:
# https://drive.google.com/file/d/1VrS5Kh-a1lh_P-FWNMyolVeigenI6dLa/view
# ВАЖНО: у файла на Google Диске должен быть включён доступ по ссылке
# ("Все, у кого есть ссылка" → "Читатель"), иначе скачивание не сработает.
GDRIVE_FILE_ID = "1VrS5Kh-a1lh_P-FWNMyolVeigenI6dLa"

# Локальный путь во временном хранилище контейнера, куда база
# скачивается при запуске. Это НЕ файл из репозитория — он создаётся
# заново при каждом холодном старте приложения (и по кнопке "Обновить").
LOCAL_DB_CACHE_PATH = "/tmp/hybridassistant_downloaded.db"

# Как долго переиспользовать уже скачанную копию базы, прежде чем
# скачать её заново автоматически (в секундах). Это не мешает кнопке
# "Обновить базу данных" в боковой панели скачать файл немедленно.
DB_CACHE_TTL_SECONDS = 30 * 60  # 30 минут

MAINTENANCE_FILE = "maintenance.json"

# --- Защита формы добавления записей ТО ---
# Пароль НИКОГДА не хранится в коде в открытом виде (код лежит в
# публичном репозитории GitHub!). Вместо этого хранится и сравнивается
# только SHA-256 хеш пароля.
#
# Хеш ниже — это запасной вариант "из коробки" для пароля ALPzqmfg1029
# (сгенерирован один раз локально командой:
#   python3 -c "import hashlib; print(hashlib.sha256('ALPzqmfg1029'.encode()).hexdigest())"
# ), но правильный способ — задать свой хеш через Secrets в настройках
# Streamlit Community Cloud (Settings → Secrets), тогда он вообще не
# попадёт в git-репозиторий:
#
#   maintenance_password_hash = "ваш_хеш_сюда"
#
# Чтобы получить хеш для своего пароля, выполни ту же команду, подставив
# свой пароль вместо ALPzqmfg1029, и скопируй результат в Secrets.
_FALLBACK_PASSWORD_HASH = (
    "b3ff0fc30e7ac18f4fc1b8c492379aeeeb7b3cf840bb00d3f1248a8a6854ad6c"
)

# --- Защита кода доступа к картам (код "95-100") ---
# По той же схеме: в коде хранится только SHA-256 хеш, реальный код
# нигде не фигурирует в открытом виде. Хеш ниже соответствует коду
# "95-100" (сгенерирован той же командой, что и для пароля выше, с
# заменой пароля на 95-100). Чтобы задать свой код без изменения кода
# приложения — пропиши хеш в Secrets:
#
#   map_access_code_hash = "ваш_хеш_сюда"
_FALLBACK_MAP_CODE_HASH = (
    "80f71f5ee58fee5ad5ccb7d31d125818580dbefecbbe8e6ed43b674c717b242b"
)

# Общие настройки защиты от подбора (применяются и к паролю ТО, и к
# коду доступа к картам — независимо друг от друга, у каждого свой
# счётчик попыток).
MAX_PASSWORD_ATTEMPTS = 5       # попыток до временной блокировки
LOCKOUT_SECONDS = 5 * 60        # длительность блокировки, сек

# Пороговые значения перегрева
INVERTER_TEMP_LIMIT = 75.0  # °C
ENGINE_TEMP_LIMIT = 95.0    # °C

# Диапазон дельты напряжений ВВБ под нагрузкой для расчёта SOH
SOH_DELTA_MIN = 0.02  # В  -> 100% здоровья
SOH_DELTA_MAX = 0.20  # В  -> 0% здоровья

# Порог "разумного" количества точек для температурного графика:
# при большем числе строк FASTLOG усредняем по минутным интервалам,
# чтобы график оставался быстрым и читаемым.
TEMP_CHART_RESAMPLE_THRESHOLD = 5000

# ============================================================
# ПЕРЕВОДЫ / TŁUMACZENIA
# ============================================================

TR = {
    "ru": {
        "page_title": "Toyota Yaris 4 Hybrid — Диагностика",
        "app_title": "🚗 Toyota Yaris 4 Hybrid (2021) — Панель диагностики",
        "language_label": "Язык / Language",
        "tab1": "📊 Аналитика и Диагностика",
        "tab2": "🔧 Техническое обслуживание",
        "db_missing": "⚠️ Не удалось скачать базу данных с Google Диска. Проверьте, что доступ к файлу открыт по ссылке (\"Все, у кого есть ссылка\" → \"Читатель\"), и что ссылка ведёт на нужный файл.",
        "db_error": "⚠️ Не удалось прочитать базу данных: {error}",
        "downloading_db": "Загрузка базы данных с Google Диска…",
        "refresh_db_button": "🔄 Обновить базу данных",
        "db_last_loaded": "База данных загружена: {timestamp}",
        "no_trip_data": "Нет данных о поездках для отображения.",
        "no_log_data": "Нет данных телеметрии (логов) для отображения.",
        "no_cell_data": "Нет данных о напряжении элементов батареи. Включите подробное логирование (HighSpeedLogging) в настройках приложения или проведите процедуру HV Check, чтобы увидеть динамику SOH.",
        "metric_total_trips": "Всего поездок",
        "metric_total_distance": "Общий пробег (км)",
        "metric_avg_consumption": "Средний расход (л/100км)",
        "metric_soh": "Здоровье батареи (SOH)",
        "chart1_title": "Динамика расхода топлива по поездкам",
        "chart1_x": "Поездка",
        "chart1_y": "Расход, л/100км",
        "chart2_title": "Изменение здоровья батареи (SOH) во времени",
        "chart2_x": "Время",
        "chart2_y": "SOH, %",
        "chart2_source_battlog": "Источник данных: подробный лог батареи (BATTLOG).",
        "chart2_source_hvcheck": "Источник данных: процедуры HV Check.",
        "chart3_title": "Температуры узлов (ДВС, Инвертор, ВВБ)",
        "chart3_x": "Время",
        "chart3_y": "Температура, °C",
        "chart3_resampled": "График усреднён по минутным интервалам ({points} исходных точек).",
        "legend_engine": "ДВС",
        "legend_inverter": "Инвертор",
        "legend_battery": "ВВБ",
        "warning_inverter": "🔥 Внимание: температура инвертора превышала {limit}°C (макс. {value}°C)!",
        "warning_engine": "🔥 Внимание: температура ДВС превышала {limit}°C (макс. {value}°C)!",
        "maintenance_title": "История технического обслуживания",
        "maintenance_empty": "Записи о техническом обслуживании отсутствуют.",
        "col_date": "Дата",
        "col_mileage": "Пробег (км)",
        "col_description": "Что сделано",
        "add_record_header": "Добавить новую запись",
        "password_label": "Введите пароль для доступа к добавлению записей",
        "password_wrong": "🔒 Неверный пароль. Осталось попыток: {attempts_left}.",
        "password_needed": "🔒 Для добавления новой записи введите пароль выше.",
        "password_locked": "🔒 Слишком много неверных попыток. Повторите через {minutes} мин {seconds} сек.",
        "password_unlocked": "🔓 Доступ разрешён для текущей сессии.",
        "lock_again_button": "🔒 Закрыть доступ",
        "map_code_label": "Введите код доступа",
        "map_code_check_button": "Проверить код",
        "map_code_close_button": "Закрыть без карт",
        "code_wrong": "🔒 Неверный код. Осталось попыток: {attempts_left}.",
        "code_locked": "🔒 Слишком много неверных попыток. Повторите через {minutes} мин {seconds} сек.",
        "maps_locked_message": "Доступ к картам ограничен. Введите код доступа.",
        "form_date": "Дата обслуживания",
        "form_mileage": "Пробег на момент ТО (км)",
        "form_description": "Описание выполненных работ",
        "save_button": "💾 Сохранить запись",
        "save_success": "✅ Запись успешно сохранена!",
        "save_fill_all": "⚠️ Заполните все поля перед сохранением.",
    },
    "pl": {
        "page_title": "Toyota Yaris 4 Hybrid — Diagnostyka",
        "app_title": "🚗 Toyota Yaris 4 Hybrid (2021) — Panel diagnostyczny",
        "language_label": "Język / Язык",
        "tab1": "📊 Analityka i Diagnostyka",
        "tab2": "🔧 Przeglądy techniczne",
        "db_missing": "⚠️ Nie udało się pobrać bazy danych z Google Drive. Sprawdź, czy dostęp do pliku jest ustawiony jako \"Każdy, kto ma link\" → \"Czytelnik\", i czy link prowadzi do właściwego pliku.",
        "db_error": "⚠️ Nie udało się odczytać bazy danych: {error}",
        "downloading_db": "Pobieranie bazy danych z Google Drive…",
        "refresh_db_button": "🔄 Odśwież bazę danych",
        "db_last_loaded": "Baza danych wczytana: {timestamp}",
        "no_trip_data": "Brak danych o przejazdach do wyświetlenia.",
        "no_log_data": "Brak danych telemetrycznych (logów) do wyświetlenia.",
        "no_cell_data": "Brak danych o napięciu ogniw baterii. Włącz szczegółowe logowanie (HighSpeedLogging) w ustawieniach aplikacji lub wykonaj procedurę HV Check, aby zobaczyć zmianę SOH.",
        "metric_total_trips": "Liczba przejazdów",
        "metric_total_distance": "Łączny przebieg (km)",
        "metric_avg_consumption": "Średnie spalanie (l/100km)",
        "metric_soh": "Kondycja baterii (SOH)",
        "chart1_title": "Zmiana spalania w kolejnych przejazdach",
        "chart1_x": "Przejazd",
        "chart1_y": "Spalanie, l/100km",
        "chart2_title": "Zmiana kondycji baterii (SOH) w czasie",
        "chart2_x": "Czas",
        "chart2_y": "SOH, %",
        "chart2_source_battlog": "Źródło danych: szczegółowy log baterii (BATTLOG).",
        "chart2_source_hvcheck": "Źródło danych: procedury HV Check.",
        "chart3_title": "Temperatury podzespołów (silnik, falownik, HV)",
        "chart3_x": "Czas",
        "chart3_y": "Temperatura, °C",
        "chart3_resampled": "Wykres uśredniony w interwałach minutowych ({points} punktów źródłowych).",
        "legend_engine": "Silnik spalinowy",
        "legend_inverter": "Falownik",
        "legend_battery": "Bateria HV",
        "warning_inverter": "🔥 Uwaga: temperatura falownika przekroczyła {limit}°C (maks. {value}°C)!",
        "warning_engine": "🔥 Uwaga: temperatura silnika przekroczyła {limit}°C (maks. {value}°C)!",
        "maintenance_title": "Historia przeglądów technicznych",
        "maintenance_empty": "Brak zapisanych przeglądów.",
        "col_date": "Data",
        "col_mileage": "Przebieg (km)",
        "col_description": "Zakres prac",
        "add_record_header": "Dodaj nowy wpis",
        "password_label": "Wprowadź hasło, aby dodać wpis",
        "password_wrong": "🔒 Nieprawidłowe hasło. Pozostałe próby: {attempts_left}.",
        "password_needed": "🔒 Aby dodać nowy wpis, wprowadź hasło powyżej.",
        "password_locked": "🔒 Zbyt wiele nieudanych prób. Spróbuj ponownie za {minutes} min {seconds} s.",
        "password_unlocked": "🔓 Dostęp odblokowany na tę sesję.",
        "lock_again_button": "🔒 Zablokuj ponownie",
        "map_code_label": "Wprowadź kod dostępu",
        "map_code_check_button": "Sprawdź kod",
        "map_code_close_button": "Zamknij bez map",
        "code_wrong": "🔒 Nieprawidłowy kod. Pozostałe próby: {attempts_left}.",
        "code_locked": "🔒 Zbyt wiele nieudanych prób. Spróbuj ponownie za {minutes} min {seconds} s.",
        "maps_locked_message": "Dostęp do map ograniczony. Wprowadź kod dostępu.",
        "form_date": "Data przeglądu",
        "form_mileage": "Przebieg w dniu przeglądu (km)",
        "form_description": "Opis wykonanych prac",
        "save_button": "💾 Zapisz wpis",
        "save_success": "✅ Wpis został zapisany!",
        "save_fill_all": "⚠️ Uzupełnij wszystkie pola przed zapisaniem.",
    },
}


def t(key: str) -> str:
    """Достаёт перевод для текущего языка."""
    lang = st.session_state.get("lang", "ru")
    return TR[lang].get(key, key)


# ============================================================
# ЗАГРУЗКА БАЗЫ ДАННЫХ С GOOGLE ДИСКА
# ============================================================

@st.cache_resource(show_spinner=False, ttl=DB_CACHE_TTL_SECONDS)
def download_database() -> str:
    """Скачивает hybridassistant.db с Google Диска во временное
    хранилище контейнера и возвращает путь к локальному файлу.

    Результат кэшируется на время жизни процесса Streamlit (либо на
    DB_CACHE_TTL_SECONDS секунд) — иначе файл скачивался бы заново
    на каждый ререндер страницы, а не только при запуске приложения.
    Кнопка "Обновить базу данных" в боковой панели сбрасывает кэш и
    вызывает немедленное повторное скачивание.
    """
    output_path = LOCAL_DB_CACHE_PATH
    # На случай, если предыдущая попытка скачивания оборвалась на середине.
    if os.path.exists(output_path):
        try:
            os.remove(output_path)
        except OSError:
            pass

    gdown.download(id=GDRIVE_FILE_ID, output=output_path, quiet=True, fuzzy=True)

    if not os.path.exists(output_path) or os.path.getsize(output_path) == 0:
        raise RuntimeError(
            "Пустой или отсутствующий файл после скачивания — проверьте настройки доступа файла на Google Диске."
        )

    # Быстрая проверка, что скачался именно файл SQLite, а не HTML-страница
    # с ошибкой доступа (Google Диск возвращает такую страницу, если файл
    # не расшарен по ссылке).
    with open(output_path, "rb") as f:
        header = f.read(16)
    if not header.startswith(b"SQLite format 3"):
        raise RuntimeError(
            "Скачанный файл не является базой SQLite — вероятно, доступ к файлу на Google Диске не открыт по ссылке."
        )

    return output_path


# ============================================================
# РАБОТА С БАЗОЙ ДАННЫХ (SQLite)
# ============================================================
# ВАЖНО: путь к скачанному файлу (LOCAL_DB_CACHE_PATH) всегда один и
# тот же, даже после повторного скачивания по кнопке "Обновить базу
# данных" или по истечении DB_CACHE_TTL_SECONDS. Если кэшировать эти
# функции только по db_path, st.cache_data не заметит, что файл на
# диске перезаписан новыми данными, и продолжит отдавать старые
# DataFrame из кэша. Поэтому каждая функция дополнительно принимает
# file_version — время последнего изменения файла (mtime): как только
# файл перезаписывается свежей версией, mtime меняется, и Streamlit
# автоматически считает это новым набором аргументов и перечитывает
# базу заново.

@st.cache_data(show_spinner=False)
def _table_exists(db_path: str, table_name: str, file_version: float) -> bool:
    with sqlite3.connect(db_path) as conn:
        cur = conn.execute(
            "SELECT name FROM sqlite_master WHERE type='table' AND name=?", (table_name,)
        )
        return cur.fetchone() is not None


@st.cache_data(show_spinner=False)
def load_trips_with_consumption(db_path: str, file_version: float) -> pd.DataFrame:
    """Читает таблицу TRIPS и считает расход топлива (л/100км) для
    каждой поездки на основании максимального значения TRIPFUEL (мл) в
    FASTLOG в пределах временного окна поездки [TSDEB, TSFIN]."""
    if not _table_exists(db_path, "TRIPS", file_version):
        return pd.DataFrame()

    with sqlite3.connect(db_path) as conn:
        trips = pd.read_sql_query(
            "SELECT TSDEB, TSFIN, NBSEC, NKMS FROM TRIPS ORDER BY TSDEB", conn
        )
        fastlog_available = _table_exists(db_path, "FASTLOG", file_version)
        fuel = (
            pd.read_sql_query(
                "SELECT TIMESTAMP, TRIPFUEL FROM FASTLOG ORDER BY TIMESTAMP", conn
            )
            if fastlog_available
            else pd.DataFrame(columns=["TIMESTAMP", "TRIPFUEL"])
        )

    if trips.empty:
        return pd.DataFrame()

    trips["date"] = pd.to_datetime(trips["TSFIN"], unit="ms", errors="coerce")
    trips["distance"] = pd.to_numeric(trips["NKMS"], errors="coerce")
    trips["duration_min"] = pd.to_numeric(trips["NBSEC"], errors="coerce") / 60.0

    fuel_ts = fuel["TIMESTAMP"].to_numpy() if not fuel.empty else None
    fuel_val = pd.to_numeric(fuel["TRIPFUEL"], errors="coerce").to_numpy() if not fuel.empty else None

    consumption = []
    for _, row in trips.iterrows():
        fuel_ml = None
        if fuel_ts is not None:
            mask = (fuel_ts >= row["TSDEB"]) & (fuel_ts <= row["TSFIN"])
            if mask.any():
                trip_fuel_values = fuel_val[mask]
                trip_fuel_values = trip_fuel_values[~pd.isna(trip_fuel_values)]
                if len(trip_fuel_values) > 0:
                    fuel_ml = trip_fuel_values.max()
        if fuel_ml is not None and row["distance"] and row["distance"] > 0:
            consumption.append(fuel_ml / 1000.0 / row["distance"] * 100.0)
        else:
            consumption.append(None)

    trips["consumption"] = consumption
    return trips.sort_values("date").reset_index(drop=True)


@st.cache_data(show_spinner=False)
def load_temperature_log(db_path: str, file_version: float) -> pd.DataFrame:
    """Читает температуры узлов из FASTLOG. При большом объёме данных
    усредняет по минутным интервалам для быстрого отображения."""
    if not _table_exists(db_path, "FASTLOG", file_version):
        return pd.DataFrame()

    with sqlite3.connect(db_path) as conn:
        df = pd.read_sql_query(
            "SELECT TIMESTAMP, ICE_TEMP, INVERTER_TEMP, BATTERY_TEMP FROM FASTLOG ORDER BY TIMESTAMP",
            conn,
        )

    if df.empty:
        return df

    df["timestamp"] = pd.to_datetime(df["TIMESTAMP"], unit="ms", errors="coerce")
    df = df.rename(
        columns={
            "ICE_TEMP": "engine_temp",
            "INVERTER_TEMP": "inverter_temp",
            "BATTERY_TEMP": "battery_temp",
        }
    )
    for col in ("engine_temp", "inverter_temp", "battery_temp"):
        df[col] = pd.to_numeric(df[col], errors="coerce")

    original_points = len(df)
    resampled = original_points > TEMP_CHART_RESAMPLE_THRESHOLD

    if resampled:
        df = (
            df.set_index("timestamp")[["engine_temp", "inverter_temp", "battery_temp"]]
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
    """Ищет данные о поблочных напряжениях батареи в BATTLOG (подробный
    непрерывный лог) или HVCHECKCELL (данные процедуры HV Check) и
    считает дельту (max-min) между элементами для каждого момента
    времени. Возвращает DataFrame с колонками timestamp, cell_delta, source."""
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


def calculate_soh(delta_v: float):
    """Линейная интерполяция здоровья батареи (SOH) по дельте напряжений
    элементов под нагрузкой.
    delta_v <= 0.02В -> 100%
    delta_v >= 0.20В -> 0%
    """
    if pd.isna(delta_v):
        return None
    if delta_v <= SOH_DELTA_MIN:
        return 100.0
    if delta_v >= SOH_DELTA_MAX:
        return 0.0
    ratio = (delta_v - SOH_DELTA_MIN) / (SOH_DELTA_MAX - SOH_DELTA_MIN)
    return round(100.0 * (1 - ratio), 1)


# ============================================================
# РАБОТА С ФАЙЛОМ ОБСЛУЖИВАНИЯ (JSON)
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


# ============================================================
# ЗАЩИТА ОТ ПОДБОРА: ПАРОЛЬ ТО + КОД ДОСТУПА К КАРТАМ
# ============================================================
# Общие функции для двух независимых механизмов защиты:
#   namespace="maintenance" — пароль формы ТО
#   namespace="mapcode"     — код доступа к картам ("95-100")
# У каждого свой счётчик неудачных попыток и своя блокировка в
# st.session_state, поэтому подбор одного не влияет на другой.

def _expected_secret_hash(secret_key: str, fallback_hash: str) -> str:
    """Хеш секрета берётся из st.secrets, если он там задан (рекомендуемый
    способ для продакшена — тогда секрет не попадает в git-репозиторий),
    иначе используется запасной хеш, зашитый в код."""
    try:
        return st.secrets.get(secret_key, fallback_hash)
    except Exception:
        return fallback_hash


def _verify_secret(value_input: str, secret_key: str, fallback_hash: str) -> bool:
    """Сравнение хешей за постоянное время (защита от timing-атак),
    секрет в открытом виде никогда не хранится и не логируется."""
    input_hash = hashlib.sha256(value_input.encode("utf-8")).hexdigest()
    return hmac.compare_digest(input_hash, _expected_secret_hash(secret_key, fallback_hash))


def _lockout_remaining_seconds(namespace: str) -> int:
    """Сколько секунд ещё осталось до снятия блокировки (0, если блокировки нет)."""
    lockout_until = st.session_state.get(f"{namespace}_lockout_until", 0.0)
    remaining = lockout_until - time.time()
    return max(0, int(remaining))


def _register_failed_attempt(namespace: str) -> int:
    """Регистрирует неудачную попытку и, при превышении лимита, включает
    блокировку. Возвращает число оставшихся попыток до блокировки."""
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


# ============================================================
# ДИАЛОГ КОДА ДОСТУПА К КАРТАМ ("95-100")
# ============================================================
# Показывается не более одного раза за сессию: как только пользователь
# либо ввёл верный код, либо нажал "Закрыть без карт", флаг
# map_dialog_completed сохраняется в st.session_state и диалог больше
# не появляется до перезапуска браузера/сессии.

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

    code_input = st.text_input(
        t("map_code_label"), type="password", key="map_code_dialog_input"
    )

    col_check, col_close = st.columns(2)
    check_clicked = col_check.button(
        f"✅ {t('map_code_check_button')}", use_container_width=True
    )
    close_clicked = col_close.button(
        f"❌ {t('map_code_close_button')}", use_container_width=True
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
    """Вызывать один раз в начале main(). Открывает диалог только если
    он ещё не был пройден в этой сессии (успешно или через "Закрыть")."""
    if "map_dialog_completed" not in st.session_state:
        _map_access_code_dialog()


def maps_are_unlocked() -> bool:
    return st.session_state.get("map_unlocked", False)


def render_maps_locked_placeholder() -> None:
    """Аккуратная заглушка вместо карт, если код не был введён."""
    st.info(t("maps_locked_message"))


# ============================================================
# ИНТЕРФЕЙС
# ============================================================

def render_sidebar():
    st.sidebar.header(t("language_label"))
    lang_display = {"ru": "Русский", "pl": "Polski"}
    current_lang = st.session_state.get("lang", "ru")
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


def render_analytics_tab(trips_df: pd.DataFrame, temp_df: pd.DataFrame, cell_df: pd.DataFrame):
    if trips_df.empty and temp_df.empty:
        st.info(t("no_trip_data"))
        return

    # --- Карточки метрик ---
    total_trips = len(trips_df) if not trips_df.empty else 0
    total_distance = trips_df["distance"].sum() if "distance" in trips_df.columns else 0
    avg_consumption = trips_df["consumption"].mean() if "consumption" in trips_df.columns else None

    latest_soh = None
    if not cell_df.empty:
        latest_soh = calculate_soh(cell_df.sort_values("timestamp")["cell_delta"].iloc[-1])

    col1, col2, col3, col4 = st.columns(4)
    col1.metric(t("metric_total_trips"), f"{total_trips}")
    col2.metric(t("metric_total_distance"), f"{total_distance:,.0f}".replace(",", " "))
    col3.metric(
        t("metric_avg_consumption"),
        f"{avg_consumption:.1f}" if avg_consumption is not None and not pd.isna(avg_consumption) else "—",
    )
    col4.metric(
        t("metric_soh"),
        f"{latest_soh:.0f}%" if latest_soh is not None else "—",
    )

    st.divider()

    # --- График 1: расход топлива по поездкам ---
    trips_with_consumption = trips_df.dropna(subset=["consumption"]) if "consumption" in trips_df.columns else pd.DataFrame()
    if not trips_with_consumption.empty:
        fig1 = go.Figure()
        fig1.add_trace(
            go.Scatter(
                x=list(range(1, len(trips_with_consumption) + 1)),
                y=trips_with_consumption["consumption"],
                mode="lines+markers",
                name=t("chart1_y"),
                line=dict(color="#1f77b4"),
                hovertext=trips_with_consumption["date"].dt.strftime("%Y-%m-%d %H:%M"),
            )
        )
        fig1.update_layout(
            title=t("chart1_title"),
            xaxis_title=t("chart1_x"),
            yaxis_title=t("chart1_y"),
            height=400,
        )
        st.plotly_chart(fig1, use_container_width=True)
    else:
        st.info(t("no_trip_data"))

    # --- График 2: SOH во времени ---
    if not cell_df.empty:
        soh_series = cell_df["cell_delta"].apply(calculate_soh)
        fig2 = go.Figure()
        fig2.add_trace(
            go.Scatter(
                x=cell_df["timestamp"],
                y=soh_series,
                mode="lines+markers",
                name=t("chart2_y"),
                line=dict(color="#2ca02c"),
            )
        )
        fig2.update_layout(
            title=t("chart2_title"),
            xaxis_title=t("chart2_x"),
            yaxis_title=t("chart2_y"),
            yaxis_range=[0, 105],
            height=400,
        )
        st.plotly_chart(fig2, use_container_width=True)
        source = cell_df["source"].iloc[-1] if "source" in cell_df.columns else None
        if source == "battlog":
            st.caption(t("chart2_source_battlog"))
        elif source == "hvcheck":
            st.caption(t("chart2_source_hvcheck"))
    else:
        st.info(t("no_cell_data"))

    # --- График 3: температуры узлов ---
    temp_cols = [c for c in ("engine_temp", "inverter_temp", "battery_temp") if c in temp_df.columns]
    if not temp_df.empty and temp_cols:
        fig3 = go.Figure()
        color_map = {
            "engine_temp": ("#d62728", t("legend_engine")),
            "inverter_temp": ("#ff7f0e", t("legend_inverter")),
            "battery_temp": ("#9467bd", t("legend_battery")),
        }
        for col in temp_cols:
            color, label = color_map[col]
            fig3.add_trace(
                go.Scatter(
                    x=temp_df["timestamp"],
                    y=temp_df[col],
                    mode="lines",
                    name=label,
                    line=dict(color=color),
                )
            )
        fig3.update_layout(
            title=t("chart3_title"),
            xaxis_title=t("chart3_x"),
            yaxis_title=t("chart3_y"),
            height=400,
        )
        st.plotly_chart(fig3, use_container_width=True)

        if temp_df.attrs.get("resampled"):
            st.caption(t("chart3_resampled").format(points=temp_df.attrs.get("original_points", "?")))

        # Предупреждения о перегреве
        if "inverter_temp" in temp_df.columns:
            max_inv = temp_df["inverter_temp"].max()
            if pd.notna(max_inv) and max_inv > INVERTER_TEMP_LIMIT:
                st.warning(
                    t("warning_inverter").format(limit=INVERTER_TEMP_LIMIT, value=round(max_inv, 1))
                )
        if "engine_temp" in temp_df.columns:
            max_eng = temp_df["engine_temp"].max()
            if pd.notna(max_eng) and max_eng > ENGINE_TEMP_LIMIT:
                st.warning(
                    t("warning_engine").format(limit=ENGINE_TEMP_LIMIT, value=round(max_eng, 1))
                )
    else:
        st.info(t("no_log_data"))


def render_maintenance_tab():
    st.subheader(t("maintenance_title"))

    records = load_maintenance()
    if records:
        df = pd.DataFrame(records)
        df = df.rename(
            columns={
                "date": t("col_date"),
                "mileage": t("col_mileage"),
                "description": t("col_description"),
            }
        )
        st.dataframe(df, use_container_width=True, hide_index=True)
    else:
        st.info(t("maintenance_empty"))

    st.divider()
    st.subheader(t("add_record_header"))

    remaining = _lockout_remaining_seconds("maintenance")

    if remaining > 0:
        # Слишком много неверных попыток — форма ввода пароля временно скрыта.
        minutes, seconds = divmod(remaining, 60)
        st.error(t("password_locked").format(minutes=minutes, seconds=seconds))
        return

    if not st.session_state.get("maintenance_unlocked", False):
        password_input = st.text_input(
            t("password_label"), type="password", key="maintenance_password_input"
        )

        if password_input == "":
            st.info(t("password_needed"))
        elif _verify_secret(password_input, "maintenance_password_hash", _FALLBACK_PASSWORD_HASH):
            _register_successful_unlock("maintenance", "maintenance_unlocked")
            st.rerun()
        else:
            attempts_left = _register_failed_attempt("maintenance")
            st.error(t("password_wrong").format(attempts_left=attempts_left))
        return

    # --- Доступ разблокирован для текущей сессии ---
    st.success(t("password_unlocked"))
    if st.button(t("lock_again_button")):
        st.session_state["maintenance_unlocked"] = False
        st.rerun()

    with st.form("maintenance_form", clear_on_submit=True):
        record_date = st.date_input(t("form_date"), value=date.today())
        record_mileage = st.number_input(t("form_mileage"), min_value=0, step=100)
        record_description = st.text_area(t("form_description"))
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
                st.success(t("save_success"))
                st.rerun()


def main():
    if "lang" not in st.session_state:
        st.session_state["lang"] = "ru"

    st.set_page_config(page_title=t("page_title"), page_icon="🚗", layout="wide")

    ensure_map_code_dialog_shown()

    render_sidebar()

    st.title(t("app_title"))

    tab1, tab2 = st.tabs([t("tab1"), t("tab2")])

    trips_df = pd.DataFrame()
    temp_df = pd.DataFrame()
    cell_df = pd.DataFrame()
    db_ok = True
    db_missing = False
    db_error_message = None
    db_path = None

    with st.spinner(t("downloading_db")):
        try:
            db_path = download_database()
        except RuntimeError:
            # Файл не расшарен по ссылке, ссылка неверна, или скачался пустым.
            db_ok = False
            db_missing = True
        except Exception as e:  # сетевые сбои, недоступность Google Диска и т.п.
            db_ok = False
            db_error_message = str(e)

    if db_ok and db_path:
        file_version = os.path.getmtime(db_path)
        st.sidebar.caption(
            t("db_last_loaded").format(
                timestamp=pd.to_datetime(file_version, unit="s").strftime(
                    "%Y-%m-%d %H:%M:%S"
                )
            )
        )
        try:
            trips_df = load_trips_with_consumption(db_path, file_version)
            temp_df = load_temperature_log(db_path, file_version)
            cell_df = load_cell_delta_series(db_path, file_version)
        except sqlite3.Error as e:
            db_ok = False
            db_error_message = str(e)
        except Exception as e:  # защитный общий catch, чтобы приложение не падало
            db_ok = False
            db_error_message = str(e)

    with tab1:
        if not db_ok:
            if db_missing:
                st.warning(t("db_missing"))
            else:
                st.error(t("db_error").format(error=db_error_message))
        else:
            render_analytics_tab(trips_df, temp_df, cell_df)

    with tab2:
        render_maintenance_tab()


if __name__ == "__main__":
    main()
