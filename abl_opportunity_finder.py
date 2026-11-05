"""
ABL Opportunity Finder
======================
Search engine for intralogistics opportunities for Actemium Barcelona Logistics (ABL)
in the Spanish and European market, with an interactive interface and Google Maps view.

Sources
-------
1. TED - Tenders Electronic Daily (EU Official Journal, all EU/EEA countries)
   Public Search API v3, anonymous, no key needed.
2. PLACSP - Plataforma de Contratacion del Sector Publico (Spain, incl. below-EU-threshold)
   Official ATOM/CODICE syndication feed, no key needed.
3. News signals (private projects: new warehouses, DCs, hubs, sorters announced in the press)
   Google News RSS. Location/price extracted from the headline when possible.

Install & run
-------------
    pip install streamlit requests pandas openpyxl
    streamlit run abl_opportunity_finder.py

Google Maps
-----------
Paste a Google Maps API key in the sidebar (or set env var GOOGLE_MAPS_API_KEY).
Required APIs on the key: "Maps JavaScript API" (+ "Geocoding API" for better geocoding).
Without a key the app falls back to an OpenStreetMap map + free Nominatim geocoding,
and every opportunity still gets an "Open in Google Maps" link.
"""

from __future__ import annotations

import html
import io
import json
import os
import random
import re
import time
import unicodedata
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from pathlib import Path
from urllib.parse import quote_plus

import pandas as pd
import requests
import streamlit as st
import streamlit.components.v1 as components

# =============================================================================
# CONFIGURATION  (edit freely)
# =============================================================================

APP_TITLE = "ABL Opportunity Finder - Intralogistics Projects Spain & Europe"
USER_AGENT = "ABL-Opportunity-Finder/1.0 (Actemium Barcelona Logistics internal tool)"
GEOCODE_CACHE_FILE = Path(__file__).with_name("abl_geocode_cache.json")

TED_URL = "https://api.ted.europa.eu/v3/notices/search"
PLACSP_URL = ("https://contrataciondelsectorpublico.gob.es/sindicacion/"
              "sindicacion_643/licitacionesPerfilesContratanteCompleto3.atom")
GNEWS_URL = "https://news.google.com/rss/search?q={q}&hl={hl}&gl={gl}&ceid={gl}:{hl}"

# CPV codes relevant to ABL (intralogistics, sorting, baggage, handling, WMS, maintenance)
DEFAULT_CPVS = {
    "42410000": "Lifting and handling equipment",
    "42417200": "Conveyors",
    "42417300": "Conveyor equipment",
    "42418000": "Lifting, handling, loading or unloading machinery",
    "42418900": "Loading or handling machinery",
    "42415000": "Forklift trucks / works trucks",
    "42965100": "Warehouse management system",
    "34961000": "Baggage-handling system",
    "34961100": "Baggage-handling equipment",
    "39131000": "Shelving / racking",
    "51511000": "Installation of lifting and handling equipment",
    "50530000": "Repair and maintenance of machinery",
}

# Business segments + keywords (lower-case, accents are ignored). Weight = relevance points.
SEGMENTS = {
    "Automated warehouse / AS/RS": {
        "weight": 3,
        "kw": ["almacen automatico", "almacen automatizado", "almacen robotizado", "asrs",
               "as/rs", "transelevador", "miniload", "shuttle", "silo automatico",
               "automated warehouse", "automated storage", "high bay", "autoportante",
               "entrepot automatise", "armazem automatico", "hochregallager", "klt"],
    },
    "Parcel / postal sorting": {
        "weight": 3,
        "kw": ["clasificador", "clasificacion de paqueteria", "sorter", "sortation",
               "paqueteria", "cross docking", "crossdocking", "tri de colis", "trieur",
               "sistema de clasificacion", "parcel", "centro de tratamiento postal",
               "classificacao", "hub logistico"],
    },
    "Airport baggage handling (BHS)": {
        "weight": 3,
        "kw": ["equipajes", "tratamiento de equipajes", "baggage", "bhs", "hall de",
               "hipodromo", "carrusel", "facturacion", "bagagem", "bagages", "aena",
               "ana aeroportos", "aeropuerto", "aeroporto", "airport"],
    },
    "Conveyors & material handling": {
        "weight": 2,
        "kw": ["transportador", "transportadores", "cinta transportadora", "conveyor",
               "rodillos", "manutencion", "intralogistica", "intralogistics",
               "convoyeur", "transportador de rodillos", "elevador de cajas",
               "material handling", "paletizador", "paletizado", "despaletizado"],
    },
    "AGV / AMR / robotics": {
        "weight": 2,
        "kw": ["agv", "amr", "vehiculo de guiado automatico", "vehiculos guiados",
               "robot movil", "robotica logistica", "rgv", "lgv", "carretilla autonoma",
               "autonomous mobile robot", "picking robotizado", "goods to person"],
    },
    "Warehouse / logistics centre (general)": {
        "weight": 1,
        "kw": ["centro logistico", "plataforma logistica", "almacen", "centro de distribucion",
               "distribution center", "warehouse", "logistica", "nave logistica",
               "entrepot", "armazem", "picking", "estanterias", "racks", "wms", "sga"],
    },
    "Maintenance / retrofit": {
        "weight": 1,
        "kw": ["mantenimiento", "renovacion", "modernizacion", "retrofit", "ampliacion",
               "maintenance", "upgrade"],
    },
}

# Words that usually mean "not for us" (cleaning, food supply, vehicles fleet, etc.)
DEFAULT_EXCLUDE = ["limpieza", "comedor", "combustible",
                   "seguros", "vigilancia", "jardineria", "consultoria juridica"]

# News queries for private-sector project signals
DEFAULT_NEWS_QUERIES = [
    ("nuevo almacén automático inversión", "es", "ES"),
    ("nuevo centro logístico automatizado millones", "es", "ES"),
    ("construirá centro de distribución robotizado", "es", "ES"),
    ("nuevo hub paquetería clasificador automático", "es", "ES"),
    ("ampliación almacén robotizado", "es", "ES"),
    ("novo centro logístico automatizado investimento", "pt-PT", "PT"),
    ("nouvel entrepôt automatisé investissement", "fr", "FR"),
    ("new automated warehouse Spain investment", "en", "GB"),
    ("automated distribution centre Europe investment million", "en", "GB"),
]

COUNTRIES = {  # ISO3 -> (name, lat, lon)  (centroids used as last-resort location)
    "ESP": ("Spain", 40.2, -3.6), "PRT": ("Portugal", 39.6, -8.0),
    "FRA": ("France", 46.6, 2.4), "ITA": ("Italy", 42.8, 12.6),
    "DEU": ("Germany", 51.1, 10.4), "BEL": ("Belgium", 50.6, 4.6),
    "NLD": ("Netherlands", 52.2, 5.5), "AND": ("Andorra", 42.5, 1.5),
    "AUT": ("Austria", 47.6, 14.1), "POL": ("Poland", 52.1, 19.4),
    "IRL": ("Ireland", 53.2, -8.1), "LUX": ("Luxembourg", 49.8, 6.1),
    "CHE": ("Switzerland", 46.8, 8.2), "CZE": ("Czechia", 49.8, 15.5),
    "DNK": ("Denmark", 56.0, 9.5), "SWE": ("Sweden", 62.0, 15.0),
    "FIN": ("Finland", 64.0, 26.0), "NOR": ("Norway", 61.0, 9.0),
    "GRC": ("Greece", 39.0, 22.0), "ROU": ("Romania", 45.9, 24.9),
    "HUN": ("Hungary", 47.2, 19.5), "SVK": ("Slovakia", 48.7, 19.7),
    "SVN": ("Slovenia", 46.1, 14.8), "HRV": ("Croatia", 45.1, 15.2),
    "BGR": ("Bulgaria", 42.7, 25.5), "LTU": ("Lithuania", 55.2, 23.9),
    "LVA": ("Latvia", 56.9, 24.6), "EST": ("Estonia", 58.6, 25.0),
    "MLT": ("Malta", 35.9, 14.4), "CYP": ("Cyprus", 35.1, 33.4),
}

# Known logistics hubs for headline-based location detection (news signals)
KNOWN_PLACES = {
    "barcelona": (41.385, 2.173), "zona franca": (41.335, 2.130), "el prat": (41.326, 2.095),
    "sant boi": (41.343, 2.036), "martorell": (41.474, 1.930), "granollers": (41.608, 2.288),
    "tarragona": (41.119, 1.245), "lleida": (41.617, 0.620), "girona": (41.979, 2.821),
    "madrid": (40.417, -3.704), "getafe": (40.305, -3.732), "coslada": (40.424, -3.561),
    "san fernando de henares": (40.425, -3.535), "alcala de henares": (40.482, -3.364),
    "torrejon": (40.459, -3.480), "illescas": (40.122, -3.848), "seseña": (40.104, -3.698),
    "sesena": (40.104, -3.698), "toledo": (39.863, -4.027), "guadalajara": (40.633, -3.167),
    "cabanillas": (40.636, -3.231), "azuqueca": (40.567, -3.267), "valencia": (39.470, -0.376),
    "sagunto": (39.680, -0.278), "ribarroja": (39.546, -0.570), "castellon": (39.986, -0.051),
    "zaragoza": (41.649, -0.889), "plaza zaragoza": (41.630, -0.990), "huesca": (42.140, -0.409),
    "sevilla": (37.389, -5.984), "guillena": (37.543, -6.060), "malaga": (36.721, -4.421),
    "cordoba": (37.888, -4.779), "granada": (37.177, -3.599), "algeciras": (36.131, -5.454),
    "cadiz": (36.527, -6.289), "huelva": (37.261, -6.945), "almeria": (36.834, -2.464),
    "murcia": (37.992, -1.131), "cartagena": (37.606, -0.986), "alicante": (38.345, -0.481),
    "elche": (38.267, -0.698), "bilbao": (43.263, -2.935), "vitoria": (42.847, -2.672),
    "san sebastian": (43.318, -1.981), "pamplona": (42.812, -1.646), "navarra": (42.695, -1.676),
    "logroño": (42.465, -2.445), "logrono": (42.465, -2.445), "burgos": (42.344, -3.697),
    "valladolid": (41.652, -4.724), "leon": (42.599, -5.567), "salamanca": (40.970, -5.664),
    "santander": (43.462, -3.810), "oviedo": (43.362, -5.849), "gijon": (43.532, -5.661),
    "a coruña": (43.362, -8.411), "a coruna": (43.362, -8.411), "vigo": (42.240, -8.721),
    "santiago de compostela": (42.878, -8.545), "badajoz": (38.879, -6.970),
    "palma": (39.570, 2.650), "melilla": (35.292, -2.938), "ceuta": (35.889, -5.321),
    "las palmas": (28.124, -15.430), "tenerife": (28.291, -16.629),
    "lisboa": (38.722, -9.139), "lisbon": (38.722, -9.139), "porto": (41.158, -8.629),
    "azambuja": (39.070, -8.868), "setubal": (38.524, -8.893), "braga": (41.545, -8.426),
    "paris": (48.857, 2.352), "lyon": (45.764, 4.836), "marseille": (43.296, 5.370),
    "toulouse": (43.605, 1.444), "lille": (50.629, 3.057), "bordeaux": (44.838, -0.579),
    "perpignan": (42.699, 2.895), "milano": (45.464, 9.190), "milan": (45.464, 9.190),
    "roma": (41.903, 12.496), "rome": (41.903, 12.496), "torino": (45.070, 7.687),
    "bologna": (44.495, 11.343), "rotterdam": (51.924, 4.478), "amsterdam": (52.370, 4.895),
    "venlo": (51.370, 6.172), "tilburg": (51.556, 5.091), "antwerp": (51.219, 4.402),
    "amberes": (51.219, 4.402), "bruselas": (50.850, 4.352), "brussels": (50.850, 4.352),
    "liege": (50.633, 5.567), "frankfurt": (50.110, 8.682), "hamburg": (53.551, 9.993),
    "munich": (48.135, 11.582), "berlin": (52.520, 13.405), "duisburg": (51.434, 6.762),
    "cologne": (50.938, 6.960), "warsaw": (52.230, 21.012), "poznan": (52.406, 16.925),
    "prague": (50.075, 14.438), "vienna": (48.208, 16.373), "dublin": (53.350, -6.260),
    "andorra": (42.507, 1.522),
}

SOURCE_COLORS = {"TED (EU)": "#0055A4", "PLACSP (ES)": "#C8102E", "News signal": "#F39200"}


# =============================================================================
# HELPERS
# =============================================================================

def norm(text: str) -> str:
    """lower-case, strip accents -> for keyword matching."""
    if not text:
        return ""
    text = unicodedata.normalize("NFKD", str(text))
    return "".join(c for c in text if not unicodedata.combining(c)).lower()


def pick_lang(value, prefer=("spa", "eng", "por", "fra", "cat")) -> str:
    """TED multilingual fields come as {'spa': [...], 'eng': [...]} or lists/strings."""
    if value is None:
        return ""
    if isinstance(value, str):
        return value
    if isinstance(value, (int, float)):
        return str(value)
    if isinstance(value, list):
        return " | ".join(dict.fromkeys(pick_lang(v, prefer) for v in value if v is not None))
    if isinstance(value, dict):
        for lang in prefer:
            for k in (lang, lang.upper()):
                if k in value and value[k]:
                    return pick_lang(value[k], prefer)
        for v in value.values():
            if v:
                return pick_lang(v, prefer)
    return str(value)


def first_number(value):
    """Return first numeric value found in a scalar/list/dict."""
    if value is None:
        return None
    if isinstance(value, (int, float)):
        return float(value)
    if isinstance(value, str):
        try:
            return float(value.replace(",", "."))
        except ValueError:
            return None
    if isinstance(value, list):
        nums = [first_number(v) for v in value]
        nums = [n for n in nums if n is not None]
        return max(nums) if nums else None
    if isinstance(value, dict):
        return first_number(list(value.values()))
    return None


def score_text(text: str, cpvs: list[str], target_cpvs: list[str], exclude: list[str]):
    """Return (score, segments matched, matched keywords)."""
    t = norm(text)
    score, segs, hits = 0, [], []
    for seg, cfg in SEGMENTS.items():
        found = [k for k in cfg["kw"] if re.search(r"(?<![a-z])" + re.escape(norm(k)) + r"(?![a-z])", t)]
        if found:
            score += cfg["weight"] * min(len(found), 3)
            segs.append(seg)
            hits += found
    if any(c[:5] == tc[:5] for c in cpvs for tc in target_cpvs if c and tc):
        score += 3
        if not segs:
            segs.append("CPV match")
    if any(re.search(r"(?<![a-z])" + re.escape(norm(e)) + r"(?![a-z])", t) for e in exclude if e):
        score -= 5
    return score, segs, hits


def money(v, cur="EUR"):
    if v is None or pd.isna(v):
        return "n/a"
    return f"{v:,.0f} {cur or 'EUR'}".replace(",", ".")


# =============================================================================
# GEOCODING  (Google Geocoding API if key, else Nominatim/OSM) with disk cache
# =============================================================================

def _load_cache():
    try:
        return json.loads(GEOCODE_CACHE_FILE.read_text(encoding="utf-8"))
    except Exception:
        return {}


def _save_cache(cache):
    try:
        GEOCODE_CACHE_FILE.write_text(json.dumps(cache, ensure_ascii=False, indent=0), encoding="utf-8")
    except Exception:
        pass


def geocode(address: str, api_key: str | None, cache: dict):
    if not address or not address.strip():
        return None
    key = norm(address).strip()
    if key in cache:
        return cache[key]
    result = None
    try:
        if api_key:
            r = requests.get("https://maps.googleapis.com/maps/api/geocode/json",
                             params={"address": address, "key": api_key}, timeout=15)
            js = r.json()
            if js.get("status") == "OK":
                loc = js["results"][0]["geometry"]["location"]
                result = [loc["lat"], loc["lng"]]
        else:
            time.sleep(1.05)  # Nominatim usage policy: max 1 request/second
            r = requests.get("https://nominatim.openstreetmap.org/search",
                             params={"q": address, "format": "json", "limit": 1},
                             headers={"User-Agent": USER_AGENT}, timeout=15)
            js = r.json()
            if js:
                result = [float(js[0]["lat"]), float(js[0]["lon"])]
    except Exception:
        result = None
    cache[key] = result
    return result


# =============================================================================
# SOURCE 1 - TED (EU)
# =============================================================================

TED_CORE_FIELDS = ["publication-number", "notice-title", "buyer-name", "buyer-country",
                   "publication-date"]
TED_OPTIONAL_FIELDS = ["buyer-city", "place-of-performance", "classification-cpv",
                       "description-lot", "description-proc", "deadline-receipt-tender-date-lot",
                       "estimated-value-lot", "estimated-value-cur-lot", "total-value",
                       "total-value-cur", "notice-type", "contract-nature"]


def build_ted_query(countries, cpvs, keywords, days_back):
    since = (datetime.now(timezone.utc) - timedelta(days=days_back)).strftime("%Y%m%d")
    parts = []
    if cpvs:
        parts.append(f"classification-cpv IN ({' '.join(cpvs)})")
    for kw in keywords:
        kw = kw.replace('"', "").strip()
        if kw:
            parts.append(f'FT ~ ("{kw}")')
    subject = "(" + " OR ".join(parts) + ")" if parts else ""
    q = f"(buyer-country IN ({' '.join(countries)}) OR place-of-performance IN ({' '.join(countries)}))"
    if subject:
        q += f" AND {subject}"
    q += f" AND publication-date >= {since} SORT BY publication-date DESC"
    return q


def fetch_ted(countries, cpvs, keywords, days_back, max_results, log):
    query = build_ted_query(countries, cpvs, keywords, days_back)
    log(f"TED query: {query}")
    fields = TED_CORE_FIELDS + TED_OPTIONAL_FIELDS
    notices, token, page = [], None, 1
    while len(notices) < max_results:
        body = {"query": query, "fields": fields, "limit": min(100, max_results - len(notices)),
                "scope": "ACTIVE", "paginationMode": "ITERATION", "onlyLatestVersions": True}
        if token:
            body["iterationNextToken"] = token
        r = requests.post(TED_URL, json=body, headers={"User-Agent": USER_AGENT}, timeout=60)
        if r.status_code == 400:
            # A field name may not exist in the current TED catalogue -> drop it and retry
            bad = [f for f in fields if f in TED_OPTIONAL_FIELDS and f in r.text]
            if bad:
                fields = [f for f in fields if f not in bad]
                log(f"TED: removed unsupported fields {bad}, retrying")
                continue
            if fields != TED_CORE_FIELDS:
                fields = TED_CORE_FIELDS
                log("TED: falling back to core fields")
                continue
            raise RuntimeError(f"TED API 400: {r.text[:400]}")
        r.raise_for_status()
        js = r.json()
        batch = js.get("notices", [])
        notices += batch
        token = js.get("iterationNextToken")
        log(f"TED page {page}: {len(batch)} notices (total match: {js.get('totalNoticeCount', '?')})")
        page += 1
        if not batch or not token:
            break
    rows = []
    for n in notices:
        pub = n.get("publication-number", "")
        title = pick_lang(n.get("notice-title"))
        desc = pick_lang(n.get("description-lot")) or pick_lang(n.get("description-proc"))
        country = pick_lang(n.get("buyer-country")).split(" | ")[0]
        value = first_number(n.get("estimated-value-lot")) or first_number(n.get("total-value"))
        cur = (pick_lang(n.get("estimated-value-cur-lot")) or pick_lang(n.get("total-value-cur")) or "EUR").split(" | ")[0]
        cpv = pick_lang(n.get("classification-cpv")).split(" | ")
        rows.append({
            "source": "TED (EU)",
            "id": pub,
            "title": title,
            "description": desc[:1500],
            "company": pick_lang(n.get("buyer-name")).split(" | ")[0],
            "city": pick_lang(n.get("buyer-city")).split(" | ")[0],
            "country": country,
            "value": value,
            "currency": cur,
            "deadline": pick_lang(n.get("deadline-receipt-tender-date-lot")).split(" | ")[0][:10],
            "published": pick_lang(n.get("publication-date"))[:10],
            "cpv": [c for c in cpv if c],
            "url": f"https://ted.europa.eu/en/notice/-/detail/{pub}",
        })
    return rows


# =============================================================================
# SOURCE 2 - PLACSP (Spain)
# =============================================================================

def _find(el, path):
    """Namespace-agnostic find: path like 'ProcurementProject/Name'."""
    if el is None:
        return None
    return el.find("/".join("{*}" + p for p in path.split("/")))


def _text(el, path, default=""):
    x = _find(el, path)
    return (x.text or "").strip() if x is not None and x.text else default


def fetch_placsp(pages, statuses, log):
    rows, url = [], PLACSP_URL
    for i in range(pages):
        r = requests.get(url, headers={"User-Agent": USER_AGENT}, timeout=120)
        r.raise_for_status()
        root = ET.fromstring(r.content)
        entries = root.findall("{http://www.w3.org/2005/Atom}entry")
        log(f"PLACSP page {i + 1}: {len(entries)} entries")
        for e in entries:
            cfs = e.find("{*}ContractFolderStatus")
            if cfs is None:
                continue
            status = _text(cfs, "ContractFolderStatusCode")
            if statuses and status not in statuses:
                continue
            party = _find(cfs, "LocatedContractingParty/Party")
            proj = _find(cfs, "ProcurementProject")
            budget = _find(proj, "BudgetAmount")
            value = None
            for tag in ("EstimatedOverallContractAmount", "TaxExclusiveAmount", "TotalAmount"):
                v = _text(budget, tag)
                if v:
                    try:
                        value = float(v)
                        break
                    except ValueError:
                        pass
            cpvs = [x.text.strip() for x in proj.findall("{*}RequiredCommodityClassification/{*}ItemClassificationCode")
                    if x.text] if proj is not None else []
            link_el = e.find("{http://www.w3.org/2005/Atom}link")
            city = _text(party, "PostalAddress/CityName")
            postal = _text(party, "PostalAddress/PostalZone")
            street = _text(party, "PostalAddress/AddressLine/Line")
            place_exec = _text(proj, "RealizedLocation/CountrySubentity")
            summary = (e.findtext("{http://www.w3.org/2005/Atom}summary") or "").strip()
            rows.append({
                "source": "PLACSP (ES)",
                "id": _text(cfs, "ContractFolderID"),
                "title": _text(proj, "Name") or (e.findtext("{http://www.w3.org/2005/Atom}title") or ""),
                "description": (summary + (f" | Lugar de ejecucion: {place_exec}" if place_exec else ""))[:1500],
                "company": _text(party, "PartyName/Name"),
                "city": city,
                "postal": postal,
                "street": street,
                "country": "ESP",
                "value": value,
                "currency": "EUR",
                "deadline": _text(cfs, "TenderingProcess/TenderSubmissionDeadlinePeriod/EndDate"),
                "published": (e.findtext("{http://www.w3.org/2005/Atom}updated") or "")[:10],
                "cpv": cpvs,
                "status": status,
                "url": link_el.get("href") if link_el is not None else "",
            })
        nxt = [l.get("href") for l in root.findall("{http://www.w3.org/2005/Atom}link") if l.get("rel") == "next"]
        if not nxt:
            break
        url = nxt[0]
    return rows


# =============================================================================
# SOURCE 3 - News signals (private projects)
# =============================================================================

PRICE_RE = re.compile(
    r"(\d{1,4}(?:[.,]\d{1,3})?)\s*(millones de euros|millones|mill\.|m€|m eur|million euros|"
    r"million|€ million|milhoes de euros|milhoes|millions d'euros|millions)", re.I)


def extract_price(text):
    m = PRICE_RE.search(text or "")
    if not m:
        return None
    try:
        return float(m.group(1).replace(",", ".")) * 1_000_000
    except ValueError:
        return None


def detect_place(text):
    t = norm(text)
    for name in sorted(KNOWN_PLACES, key=len, reverse=True):
        if re.search(r"(?<![a-z])" + re.escape(norm(name)) + r"(?![a-z])", t):
            return name.title(), KNOWN_PLACES[name]
    return "", None


def fetch_news(queries, days_back, log):
    rows, seen = [], set()
    limit_date = datetime.now(timezone.utc) - timedelta(days=days_back)
    for q, hl, gl in queries:
        url = GNEWS_URL.format(q=quote_plus(q), hl=hl, gl=gl)
        try:
            r = requests.get(url, headers={"User-Agent": USER_AGENT}, timeout=30)
            r.raise_for_status()
            root = ET.fromstring(r.content)
        except Exception as ex:
            log(f"News '{q}': error {ex}")
            continue
        items = root.findall(".//item")
        log(f"News '{q}': {len(items)} items")
        for it in items:
            title = (it.findtext("title") or "").strip()
            if title in seen:
                continue
            seen.add(title)
            try:
                pub = parsedate_to_datetime(it.findtext("pubDate"))
                if pub < limit_date:
                    continue
            except Exception:
                pub = None
            src = (it.findtext("source") or "").strip()
            place, coords = detect_place(title)
            rows.append({
                "source": "News signal",
                "id": "",
                "title": title,
                "description": re.sub("<[^>]+>", " ", it.findtext("description") or "")[:800],
                "company": f"(see article - {src})" if src else "(see article)",
                "city": place,
                "country": {"ES": "ESP", "PT": "PRT", "FR": "FRA"}.get(gl, ""),
                "value": extract_price(title),
                "currency": "EUR",
                "deadline": "",
                "published": pub.strftime("%Y-%m-%d") if pub else "",
                "cpv": [],
                "url": it.findtext("link") or "",
                "_coords": coords,
            })
    return rows


# =============================================================================
# PIPELINE
# =============================================================================

def enrich(rows, target_cpvs, exclude, api_key, log, progress=None):
    cache = _load_cache()
    out = []
    for i, r in enumerate(rows):
        s, segs, hits = score_text(f"{r['title']} {r['description']}", r.get("cpv", []), target_cpvs, exclude)
        r["score"], r["segments"], r["keywords_hit"] = s, ", ".join(segs), ", ".join(dict.fromkeys(hits))
        coords = r.pop("_coords", None)
        cname = COUNTRIES.get(r.get("country", ""), (r.get("country", ""), None, None))[0]
        approx = False
        if not coords and r["source"] != "News signal":
            addr_full = ", ".join(x for x in [r.get("street"), r.get("postal"), r.get("city"), cname] if x)
            coords = geocode(f"{r['company']}, {r.get('city','')}, {cname}", api_key, cache) if api_key else None
            coords = coords or geocode(addr_full, api_key, cache)
            if not coords and r.get("city"):
                coords = geocode(f"{r['city']}, {cname}", api_key, cache)
        if not coords and r.get("country") in COUNTRIES:
            _, la, lo = COUNTRIES[r["country"]]
            coords, approx = (la, lo), True
        if coords:
            # small jitter so markers in the same city don't hide each other
            r["lat"] = coords[0] + random.uniform(-0.004, 0.004)
            r["lon"] = coords[1] + random.uniform(-0.004, 0.004)
        else:
            r["lat"] = r["lon"] = None
        r["location_approx"] = approx
        r["country_name"] = cname
        r["gmaps_link"] = (f"https://www.google.com/maps/search/?api=1&query="
                           f"{quote_plus(r['company'] + ' ' + (r.get('city') or '') + ' ' + cname)}")
        out.append(r)
        if progress and len(rows):
            progress.progress((i + 1) / len(rows), text=f"Geocoding & scoring {i + 1}/{len(rows)}")
    _save_cache(cache)
    return out


# =============================================================================
# MAP (Google Maps JS API, OSM/Leaflet fallback)
# =============================================================================

def build_map_html(df: pd.DataFrame, api_key: str | None, height=620) -> str:
    markers = []
    for _, r in df.dropna(subset=["lat", "lon"]).iterrows():
        info = (
            f"<div style='max-width:340px;font-family:Arial;font-size:12px'>"
            f"<b style='color:{SOURCE_COLORS.get(r['source'], '#333')}'>{html.escape(r['source'])}</b>"
            f" &middot; score {int(r['score'])}<br>"
            f"<b>{html.escape(str(r['company']))}</b><br>"
            f"{html.escape(str(r.get('city') or ''))} {html.escape(str(r['country_name']))}"
            f"{' (approx.)' if r['location_approx'] else ''}<hr style='margin:4px 0'>"
            f"<b>{html.escape(str(r['title'])[:220])}</b><br>"
            f"<span>{html.escape(str(r['description'])[:400])}</span><br><br>"
            f"<b>Value:</b> {html.escape(money(r['value'], r['currency']))}<br>"
            f"<b>Deadline:</b> {html.escape(str(r['deadline'] or 'n/a'))}<br>"
            f"<b>Segments:</b> {html.escape(str(r['segments'] or '-'))}<br>"
            f"<a href='{html.escape(str(r['url']))}' target='_blank'>Open notice</a> &nbsp;|&nbsp; "
            f"<a href='{html.escape(r['gmaps_link'])}' target='_blank'>Google Maps</a></div>"
        )
        markers.append({"lat": float(r["lat"]), "lng": float(r["lon"]), "info": info,
                        "color": SOURCE_COLORS.get(r["source"], "#555"),
                        "title": str(r["company"])[:80]})
    data = json.dumps(markers, ensure_ascii=False).replace("</", "<\\/")
    legend = "".join(f"<span style='margin-right:12px'><span style='display:inline-block;width:10px;height:10px;"
                     f"border-radius:50%;background:{c}'></span> {s}</span>" for s, c in SOURCE_COLORS.items())
    head = (f"<div style='font-family:Arial;font-size:12px;padding:4px 0'>{legend}</div>"
            f"<div id='map' style='width:100%;height:{height - 40}px;border-radius:8px'></div>")
    if api_key:
        return head + f"""
<script>
const MARKERS = {data};
function initMap() {{
  const map = new google.maps.Map(document.getElementById('map'), {{center: {{lat: 43.5, lng: 3}}, zoom: 5}});
  const iw = new google.maps.InfoWindow();
  const bounds = new google.maps.LatLngBounds();
  MARKERS.forEach(m => {{
    const mk = new google.maps.Marker({{position: {{lat: m.lat, lng: m.lng}}, map, title: m.title,
      icon: {{path: google.maps.SymbolPath.CIRCLE, scale: 8, fillColor: m.color, fillOpacity: 0.9,
              strokeColor: '#fff', strokeWeight: 1.5}}}});
    mk.addListener('click', () => {{ iw.setContent(m.info); iw.open(map, mk); }});
    bounds.extend(mk.getPosition());
  }});
  if (MARKERS.length > 1) map.fitBounds(bounds);
}}
</script>
<script src="https://maps.googleapis.com/maps/api/js?key={quote_plus(api_key)}&callback=initMap" async defer></script>
"""
    return head + f"""
<link rel="stylesheet" href="https://unpkg.com/leaflet@1.9.4/dist/leaflet.css"/>
<script src="https://unpkg.com/leaflet@1.9.4/dist/leaflet.js"></script>
<script>
const MARKERS = {data};
const map = L.map('map').setView([43.5, 3], 5);
L.tileLayer('https://{{s}}.tile.openstreetmap.org/{{z}}/{{x}}/{{y}}.png',
  {{maxZoom: 18, attribution: '&copy; OpenStreetMap'}}).addTo(map);
const pts = [];
MARKERS.forEach(m => {{
  L.circleMarker([m.lat, m.lng], {{radius: 8, color: '#fff', weight: 1.5, fillColor: m.color, fillOpacity: 0.9}})
   .bindPopup(m.info, {{maxWidth: 360}}).addTo(map);
  pts.push([m.lat, m.lng]);
}});
if (pts.length > 1) map.fitBounds(pts, {{padding: [30, 30]}});
</script>
"""


# =============================================================================
# STREAMLIT UI
# =============================================================================

def main():
    st.set_page_config(page_title="ABL Opportunity Finder", page_icon="📦", layout="wide")
    st.markdown("""<style>
      .block-container{padding-top:1.2rem}
      h1{color:#0055A4} .stMetric{background:#f4f7fb;border-radius:8px;padding:8px}
    </style>""", unsafe_allow_html=True)
    st.title("📦 " + APP_TITLE)
    st.caption("Actemium Barcelona Logistics · Public tenders (TED + PLACSP) and private project signals (news)")

    # ---------------- Sidebar ----------------
    with st.sidebar:
        st.header("🔎 Search settings")
        api_key = st.text_input("Google Maps API key", value=os.getenv("GOOGLE_MAPS_API_KEY", ""),
                                type="password", help="Empty = OpenStreetMap fallback")
        st.subheader("Sources")
        use_ted = st.checkbox("TED - EU tenders", True)
        use_placsp = st.checkbox("PLACSP - Spanish public tenders", True)
        use_news = st.checkbox("News - private project signals", True)

        st.subheader("Market")
        country_opts = list(COUNTRIES.keys())
        countries = st.multiselect("Countries (TED)", country_opts,
                                   default=["ESP", "PRT", "FRA", "AND", "ITA"],
                                   format_func=lambda c: f"{c} - {COUNTRIES[c][0]}")
        days_back = st.slider("Published in the last (days)", 7, 365, 60)

        st.subheader("Subject")
        cpv_text = st.text_area("CPV codes (one per line)",
                                "\n".join(f"{k}  # {v}" for k, v in DEFAULT_CPVS.items()), height=150)
        target_cpvs = [l.split("#")[0].strip() for l in cpv_text.splitlines() if l.split("#")[0].strip()]
        kw_text = st.text_area("Extra free-text keywords for TED (one per line)",
                               "conveyor\nsorter\nbaggage handling\nautomated warehouse\n"
                               "transportador\nclasificador\nequipajes\nalmacén automático\n"
                               "intralogística\nAGV", height=150)
        keywords = [k.strip() for k in kw_text.splitlines() if k.strip()]
        excl_text = st.text_input("Exclude words (comma separated)", ", ".join(DEFAULT_EXCLUDE))
        exclude = [e.strip() for e in excl_text.split(",") if e.strip()]

        st.subheader("Volume & filters")
        ted_max = st.number_input("Max TED notices", 50, 2000, 400, step=50)
        placsp_pages = st.number_input("PLACSP feed pages (≈500 entries each)", 1, 40, 6)
        placsp_status = st.multiselect("PLACSP status", ["PUB", "EV", "PRE", "ADJ", "RES"],
                                       default=["PUB", "PRE"],
                                       help="PUB=open for bids · PRE=prior notice · EV=evaluation")
        min_score = st.slider("Minimum relevance score", 0, 15, 3)
        run = st.button("🚀 Search opportunities", type="primary", use_container_width=True)

    # ---------------- Search ----------------
    if run:
        logs = []
        log_box = st.status("Searching sources…", expanded=True)

        def log(msg):
            logs.append(msg)
            log_box.write(msg)

        rows = []
        if use_ted:
            if not countries:
                log("TED skipped: select at least one country")
            else:
                try:
                    rows += fetch_ted(countries, [c for c in target_cpvs if c.isdigit()],
                                      keywords, days_back, int(ted_max), log)
                except Exception as ex:
                    log(f"⚠️ TED error: {ex}")
        if use_placsp:
            try:
                rows += fetch_placsp(int(placsp_pages), placsp_status, log)
            except Exception as ex:
                log(f"⚠️ PLACSP error: {ex}")
        if use_news:
            try:
                rows += fetch_news(DEFAULT_NEWS_QUERIES, days_back, log)
            except Exception as ex:
                log(f"⚠️ News error: {ex}")

        log(f"Raw results: {len(rows)}. Scoring relevance first (geocoding only relevant ones)…")
        # score first, geocode only what passes the threshold (saves API calls / time)
        prelim = []
        for r in rows:
            s, _, _ = score_text(f"{r['title']} {r['description']}", r.get("cpv", []), target_cpvs, exclude)
            if s >= min_score:
                prelim.append(r)
        log(f"Relevant (score ≥ {min_score}): {len(prelim)}")
        prog = st.progress(0.0, text="Geocoding…")
        results = enrich(prelim, target_cpvs, exclude, api_key or None, log, prog)
        prog.empty()
        log_box.update(label=f"Done - {len(results)} relevant opportunities", state="complete", expanded=False)
        st.session_state["results"] = pd.DataFrame(results)
        st.session_state["api_key"] = api_key

    df: pd.DataFrame | None = st.session_state.get("results")
    if df is None:
        st.info("Set your filters in the sidebar and press **Search opportunities**.\n\n"
                "Segments targeted by default: automated warehouses, parcel sorting, airport baggage "
                "handling (AENA / ANA), conveyors, AGV/AMR, warehouse retrofits.")
        return
    if df.empty:
        st.warning("No relevant opportunities found. Lower the minimum score, extend the date range "
                   "or add keywords/CPVs.")
        return

    # ---------------- Result filters ----------------
    c1, c2, c3, c4 = st.columns([2, 2, 2, 3])
    src_sel = c1.multiselect("Source", sorted(df["source"].unique()), default=sorted(df["source"].unique()))
    all_segs = sorted({s.strip() for v in df["segments"] for s in str(v).split(",") if s.strip()})
    seg_sel = c2.multiselect("Segment", all_segs)
    only_price = c3.checkbox("Only with known value")
    max_v = float(df["value"].max()) if df["value"].notna().any() else 0.0
    vrange = c4.slider("Value range (M€)", 0.0, max(1.0, round(max_v / 1e6 + 0.5, 1)),
                       (0.0, max(1.0, round(max_v / 1e6 + 0.5, 1))), step=0.1)
    text_q = st.text_input("🔍 Filter results by text (company, title, city…)")

    f = df[df["source"].isin(src_sel)].copy()
    if seg_sel:
        f = f[f["segments"].apply(lambda s: any(x in str(s) for x in seg_sel))]
    if only_price:
        f = f[f["value"].notna()]
    f = f[f["value"].isna() | f["value"].between(vrange[0] * 1e6, vrange[1] * 1e6)]
    if text_q:
        t = norm(text_q)
        f = f[f.apply(lambda r: t in norm(f"{r['company']} {r['title']} {r.get('city', '')} {r['description']}"), axis=1)]
    f = f.sort_values(["score", "value"], ascending=[False, False])

    # ---------------- KPIs ----------------
    k1, k2, k3, k4 = st.columns(4)
    k1.metric("Opportunities", len(f))
    k2.metric("With known value", int(f["value"].notna().sum()))
    k3.metric("Total known value", money(f["value"].sum()) if f["value"].notna().any() else "n/a")
    k4.metric("Countries", f["country"].nunique())

    # ---------------- Map + table ----------------
    tab_map, tab_table, tab_detail = st.tabs(["🗺️ Map", "📋 Table", "📄 Details"])
    with tab_map:
        components.html(build_map_html(f, st.session_state.get("api_key")), height=640)
        st.caption("Markers marked '(approx.)' are placed at the country centroid (address not geocodable).")

    with tab_table:
        show = f[["score", "source", "company", "city", "country_name", "title", "value", "currency",
                  "deadline", "published", "segments", "url", "gmaps_link"]].rename(columns={
            "country_name": "country", "value": "value (EUR)", "url": "notice", "gmaps_link": "map"})
        st.dataframe(show, use_container_width=True, hide_index=True, height=560, column_config={
            "notice": st.column_config.LinkColumn("Notice", display_text="Open"),
            "map": st.column_config.LinkColumn("Google Maps", display_text="📍 Map"),
            "value (EUR)": st.column_config.NumberColumn(format="%.0f"),
            "score": st.column_config.ProgressColumn("Score", min_value=0, max_value=max(15, int(f["score"].max() or 1)),
                                                     format="%d"),
        })
        # exports
        export = f.drop(columns=["lat", "lon"], errors="ignore").copy()
        export["cpv"] = export["cpv"].apply(lambda x: ", ".join(x) if isinstance(x, list) else x)
        buf = io.BytesIO()
        with pd.ExcelWriter(buf, engine="openpyxl") as xw:
            export.to_excel(xw, index=False, sheet_name="Opportunities")
        stamp = datetime.now().strftime("%Y%m%d_%H%M")
        e1, e2 = st.columns(2)
        e1.download_button("⬇️ Export Excel", buf.getvalue(), f"ABL_opportunities_{stamp}.xlsx",
                           "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
        e2.download_button("⬇️ Export CSV", export.to_csv(index=False, sep=";").encode("utf-8-sig"),
                           f"ABL_opportunities_{stamp}.csv", "text/csv")

    with tab_detail:
        for _, r in f.head(150).iterrows():
            with st.expander(f"[{int(r['score'])}] {r['company']} - {str(r['title'])[:120]}"):
                a, b = st.columns([3, 1])
                a.markdown(f"**Project:** {r['title']}")
                a.write(r["description"] or "-")
                b.markdown(f"**Source:** {r['source']}  \n**Location:** {r.get('city') or '-'}, {r['country_name']}"
                           f"  \n**Value:** {money(r['value'], r['currency'])}  \n**Deadline:** {r['deadline'] or '-'}"
                           f"  \n**Published:** {r['published'] or '-'}  \n**Segments:** {r['segments'] or '-'}"
                           f"  \n**Keywords:** {r['keywords_hit'] or '-'}")
                b.markdown(f"[Open notice]({r['url']}) · [📍 Google Maps]({r['gmaps_link']})")


if __name__ == "__main__":
    main()
