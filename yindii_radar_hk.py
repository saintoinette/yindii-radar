#!/usr/bin/env python3
"""
Yindii Hong Kong, new-business radar.

Watches Hong Kong's open food registers, detects newly appearing businesses,
routes each to the right Yindii product, and alerts.

  FEHD RESTAURANTS   General and Light Refreshment restaurant licences. Daily.
  FEHD FOOD          Bakery, food factory, siu mei, composite shop and other
                     food licences. Daily. Bakery Licence is an explicit type.
  CFS IMPORTERS      Register of registered food importers and distributors
                     under the Food Safety Ordinance. Daily. The Drop audience.
  CR COMPANIES       Companies Registry weekly list of new companies. Names only,
                     no industry or address, so matched on name keywords. OFF by
                     default because it is noisy. Turn on with --sources ... cr.

HOW "NEW" WORKS HERE
  Hong Kong licence files carry an expiry date, not an issue date. So the radar
  records the day it FIRST SEES each licence. The first run is a baseline. After
  that, anything appearing for the first time is a new business, and 90 days
  later it is re-flagged as DUE, when it has a surplus pattern worth discussing.

    python3 yindii_radar_hk.py --selftest
    python3 yindii_radar_hk.py --once
    python3 yindii_radar_hk.py --once --sources fehd_food importers

NOT TESTED LIVE
  The build sandbox cannot reach gov.hk, so no live download has run. The XML
  and JSON parsers read fields by tag-name patterns rather than fixed names,
  and the first run prints the field names it found, so a mismatch is easy to
  spot and fix. Run --selftest, then --once, and check the first 20 rows.

PRODUCT NOTE
  Yindii Drop launched as a Singapore pilot. [CONFIRM] whether Drop runs in
  Hong Kong before working the importer list as Drop prospects. Until then it
  is still useful as a channel list and for Surprise Bag merchants.
"""

from __future__ import annotations

import argparse
import csv
import io
import json
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from dataclasses import dataclass, asdict
from datetime import date, timedelta
from pathlib import Path
from typing import Any

STATE_FILE = Path("yindii_radar_hk_state.json")
URLS = {
    "fehd_restaurants": "https://www.fehd.gov.hk/english/licensing/license/text/LP_Restaurants_EN.XML",
    "fehd_food": "https://www.fehd.gov.hk/english/licensing/license/text/LP_OtherFood_EN.XML",
    "importers": "https://www.ftp.cfs.gov.hk/enquiry/registered_trader_data.json",
    "cr_package": ("https://data.gov.hk/en-data/api/3/action/package_show?"
                   "id=hk-cr-crdata-list-newly-registered-companies-2526"),
}
DEFAULT_SOURCES = ["fehd_restaurants", "fehd_food", "importers"]
DUE_AFTER_DAYS = 90
_sleep = time.sleep

# ---------------------------------------------------------------- licence types
# Matched on the licence-type DESCRIPTION, read from the file's own code table,
# so a renumbered code does not break routing. From FEHD dataset pages.
# (keyword, icp, fit 0-5, archetype, ambient_for_drop)
FEHD_TYPES: list[tuple[str, str, int, str, bool]] = [
    ("bakery", "MERCHANT", 5, "Bakery", True),
    ("light refreshment", "MERCHANT", 5, "Cafe / Light refreshment", True),
    ("general restaurant", "MERCHANT", 4, "Restaurant", True),
    ("siu mei", "MERCHANT", 4, "Siu mei and lo mei shop", True),
    ("composite food", "MERCHANT", 3, "Composite food shop (convenience, dessert, tea)", True),
    ("food factory", "MERCHANT", 4, "Takeaway or bakery outlet (food factory licence)", True),
    ("marine restaurant", "MERCHANT", 2, "Marine restaurant", True),
    ("factory canteen", "MERCHANT", 1, "Factory canteen (closed catchment)", True),
    ("fresh provision", "DISTRIBUTOR", 0, "Fresh provision shop (FRESH meat or fish, gate fails)", False),
    ("cold store", "DISTRIBUTOR", 0, "Cold store (COLD CHAIN, gate fails)", False),
    ("frozen confection", "DISTRIBUTOR", 0, "Frozen confection (COLD CHAIN, gate fails)", False),
    ("milk factory", "DISTRIBUTOR", 0, "Milk factory (CHILLED, gate fails)", False),
]

# FEHD code tables, decoded from the live data on 12 Nov 2026 by checking which
# businesses and addresses sit under each code. Used whenever the file's own
# code table cannot be read.
FEHD_TYPE_CODES: dict[str, str] = {
    "RL": "General Restaurant Licence",        # 12,609, matches FEHD's published count
    "RR": "Light Refreshment Restaurant Licence",  # 4,678, % Arabica and cafes
    "MR": "Marine Restaurant Licence",         # floating restaurants
    "FB": "Bakery Licence",                    # King Bakery, Mama Bakery
    "FF": "Food Factory Licence",              # mostly takeaway shops and bakery outlets
    "FP": "Fresh Provision Shop Licence",      # supermarket meat counters, wet market stalls
    "FS": "Siu Mei and Lo Mei Shop Licence",   # roast meat shops
    "FC": "Cold Store Licence",                # cold storage logistics firms
    "FE": "Factory Canteen Licence",           # staff canteens, airline catering
    "FM": "Milk Factory Licence",              # Vitasoy, Trappist Dairy
    "FG": "Composite Food Shop Licence",       # 7-Eleven, Godiva, tea shops [CONFIRM]
}
FEHD_DISTRICT_CODES: dict[str, str] = {
    "11": "Eastern", "12": "Wan Chai", "15": "Southern", "17": "Islands",
    "18": "Central and Western", "51": "Kwun Tong", "52": "Kowloon City",
    "53": "Wong Tai Sin", "61": "Yau Tsim", "62": "Mong Kok", "63": "Sham Shui Po",
    "91": "Kwai Tsing", "92": "Tsuen Wan", "93": "Tuen Mun", "94": "Yuen Long",
    "95": "Tai Po", "96": "North", "97": "Sha Tin", "98": "Sai Kung",
}
PLACEHOLDER_NAME = re.compile(r"^\(?\s*no\s*record(\s*found)?\s*\)?$", re.I)
INDUSTRIAL_ADDR = re.compile(r"INDUSTRIAL|FACTORY BUILDING|WORKSHOP|FLATTED FACTORY|INDUSTRIAL ESTATE|GODOWN|WAREHOUSE")
BAKERY_NAME = re.compile(r"BAKERY|BAKE|CAKE|PATISSERIE|BOULANGERIE|BREAD|PASTRY|餅|麵包|西餅")

# CFS importer food categories. Inferred from the official registration form's
# food types plus importer names under each code. [CONFIRM] against
# https://ftp.cfs.gov.hk/web/files/pdf/registered_trader_en_data_dictionary.pdf
CFS_CATEGORIES: dict[str, tuple[str, str]] = {
    "C1": ("Cereals and grains", "ambient"),
    "C2": ("Fruit and vegetables", "cold"),
    "C3": ("Meat and poultry (inferred)", "cold"),
    "C4": ("Aquatic products", "cold"),
    "C5": ("Unclear, verify", "unknown"),
    "C6": ("Eggs and egg products", "cold"),
    "C7": ("Milk and dairy (inferred)", "cold"),
    "C8": ("Frozen confections", "cold"),
    "C9": ("Fats and oils", "ambient"),
    "C10": ("Non-alcoholic beverages", "ambient"),
    "C11": ("Sugars, sweets and snacks", "ambient"),
    "C12": ("Unclear, possibly bakery products", "unknown"),
    "C13": ("Salts, condiments and sauces", "ambient"),
    "C14": ("Chinese herbs (inferred)", "unfit"),
    "C15": ("Unclear, verify", "unknown"),
    "C16": ("Health food and supplements", "unfit"),
}

# Importer register has no product category, so the name is the only hint.
COLD_NAME = re.compile(r"SEAFOOD|SEA FOOD|MEAT|POULTRY|FROZEN|FISH|BEEF|PORK|CHICKEN|DAIRY|ICE CREAM|COLD STOR")
AMBIENT_NAME = re.compile(r"SNACK|CONFECTION|BISCUIT|CANDY|CHOCOLATE|NOODLE|SAUCE|TEA|COFFEE|BEVERAGE|GROCER|"
                          r"DRIED|CANNED|PROVISION|BAKERY|RICE|OIL|SPICE|CONDIMENT")
ALCOHOL_NAME = re.compile(r"WINE|LIQUOR|SPIRIT|BREWERY|BEER|WHISKY|SAKE")

# CR company names, for the optional weekly feed.
CR_MERCHANT = re.compile(r"RESTAURANT|CAFE|CAFÉ|COFFEE|BAKERY|BAKE|PATISSERIE|DESSERT|KITCHEN|CATERING|"
                         r"NOODLE|DIM SUM|BISTRO|EATERY|TEA HOUSE|酒家|餐廳|茶餐廳|餅|咖啡")
CR_DISTRIB = re.compile(r"FOOD|FOODS|PROVISION|GROCER|SNACK|CONFECTION|BEVERAGE|NOODLE|SAUCE|食品")

# ---------------------------------------------------------------- districts
# Placeholder weights for HK's 18 districts. [CONFIRM] against Yindii HK's
# real partner density and saved ratio, then edit these numbers.
DISTRICT_WEIGHT: dict[str, int] = {
    "central and western": 5, "wan chai": 5, "yau tsim mong": 5, "yau tsim": 5, "mong kok": 5, "eastern": 4,
    "kowloon city": 4, "kwun tong": 4, "sha tin": 4, "sham shui po": 3,
    "wong tai sin": 3, "southern": 3, "tsuen wan": 3, "kwai tsing": 3,
    "tai po": 3, "sai kung": 3, "tuen mun": 3, "yuen long": 3,
    "north": 2, "islands": 2,
}

W_FIT, W_DIST, W_MAT, W_EXP, W_WARM = 0.30, 0.25, 0.20, 0.15, 0.10


@dataclass
class Signal:
    detected: str = ""
    source: str = ""
    icp: str = ""
    name: str = ""
    licence_or_reg: str = ""
    licence_type: str = ""
    archetype: str = ""
    district: str = ""
    address: str = ""
    phone: str = ""
    expiry: str = ""
    first_seen: str = ""
    days_since: int = -1
    outlets: int = 1
    ambient_gate: str = ""
    fit_score: int = 0
    district_score: int = 1
    maturity_score: int = 1
    signal_score: float = 0.0
    trigger: str = ""
    next_action: str = ""

    def key(self) -> str:
        if self.source == "importers":
            # Matches the key format of the first live baseline, so the upgrade
            # does not make 11,597 existing importers look new.
            return f"importers|{norm(self.name)}|"
        if self.licence_or_reg:
            return f"{self.source}|{self.licence_or_reg}"
        return f"{self.source}|{norm(self.name)}|{norm(self.address)[:40]}"

    def finalise(self, baseline: bool = False) -> "Signal":
        if self.icp == "DISTRIBUTOR":
            if self.ambient_gate == "FAIL":
                self.signal_score, self.trigger = 0.0, "EXCLUDE - cold chain"
                self.next_action = "Chilled, frozen, fresh or alcohol. Not viable for a delivered dry-goods box."
            else:
                self.signal_score = float(self.fit_score)
                self.trigger = "ENRICH - distributor"
                self.next_action = ("Check the product range is ambient, then research. "
                                    "[CONFIRM] Drop is live in HK before pitching Drop.")
            return self
        exp = 5 if self.outlets >= 10 else (3 if self.outlets >= 3 else 1)
        self.signal_score = round(self.fit_score * W_FIT + self.district_score * W_DIST
                                  + self.maturity_score * W_MAT + exp * W_EXP + 1 * W_WARM, 2)
        if self.fit_score <= 1:
            self.trigger, self.next_action = "EXCLUDE", "Low fit. Suppress."
        elif baseline:
            self.trigger, self.next_action = "BASELINE", "Existing business, part of the first scan."
        elif 0 <= self.days_since < 60:
            due = (date.fromisoformat(self.first_seen) + timedelta(days=DUE_AFTER_DAYS)).isoformat()
            self.trigger = "NURTURE 90"
            self.next_action = f"Newly licensed. The radar re-flags it as DUE on about {due}."
        elif self.signal_score >= 4.0:
            self.trigger, self.next_action = "HOT - same week", "Visit near closing within 5 working days."
        elif self.signal_score >= 3.4:
            self.trigger, self.next_action = "WARM - 14 day", "Add to outreach cadence, then visit."
        else:
            self.trigger, self.next_action = "NURTURE 90", "Hold and recheck."
        return self


# ================================================================ helpers
def norm(s: str) -> str:
    s = (s or "").upper()
    s = re.sub(r"\b(LIMITED|LTD\.?|CO\.?|COMPANY|HK|HONG KONG)\b", " ", s)
    s = re.sub(r"[^A-Z0-9\u4e00-\u9fff ]", " ", s)
    return re.sub(r"\s+", " ", s).strip()


def maturity_score(days: int) -> int:
    if days < 0:
        return 1
    if 90 <= days <= 180:
        return 5
    if 60 <= days < 90 or 180 < days <= 365:
        return 3
    if 30 <= days < 60:
        return 2
    return 1


def district_score(district: str) -> int:
    return DISTRICT_WEIGHT.get((district or "").strip().lower(), 1)


def _get_bytes(url: str, timeout: int = 120) -> bytes:
    for attempt in range(5):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "yindii-radar-hk/1.0"})
            with urllib.request.urlopen(req, timeout=timeout) as r:
                return r.read()
        except urllib.error.HTTPError as exc:
            if exc.code in (429, 502, 503, 504) and attempt < 4:
                wait = min(60, 5 * 2 ** attempt)
                print(f"    ... server busy ({exc.code}), waiting {wait}s", file=sys.stderr)
                _sleep(wait)
                continue
            raise
    raise RuntimeError("retries exhausted")


def decode(raw: bytes) -> str:
    for enc in ("utf-8-sig", "big5hkscs", "big5", "utf-16"):
        try:
            return raw.decode(enc)
        except (UnicodeDecodeError, LookupError):
            continue
    return raw.decode("utf-8", errors="replace")


_shown: set[str] = set()


def show_fields(label: str, fields: list[str]) -> None:
    if fields and label not in _shown:
        _shown.add(label)
        print(f"    fields ({label}): {', '.join(fields[:20])}", file=sys.stderr)


# ================================================================ FEHD XML
def _txt(el) -> str:
    return "".join(el.itertext()).strip() if el is not None else ""


def parse_fehd_xml(text: str) -> tuple[list[dict], dict[str, str], dict[str, str]]:
    """Parse an FEHD licence file into flat records.

    The file opens with code tables (licence types, districts, info flags),
    each entry carrying an ID attribute, then a list of <LP> records. Tag
    names are matched by pattern, so modest renames do not break parsing.
    """
    root = ET.fromstring(text)
    type_map: dict[str, str] = dict(FEHD_TYPE_CODES)
    dist_map: dict[str, str] = dict(FEHD_DISTRICT_CODES)
    # Code tables sit in sections such as TYPE_CODE and DIST_CODE. Read every
    # child carrying an ID attribute and file it by the SECTION's name.
    for section in root.iter():
        stag = section.tag.upper()
        target = type_map if "TYPE" in stag else dist_map if "DIST" in stag else None
        if target is None:
            continue
        for child in section:
            ident = child.attrib.get("ID") or child.attrib.get("id")
            val = _txt(child)
            if ident and val:
                target[ident] = val

    records = []
    for lp in root.iter():
        if lp.tag.upper() != "LP":
            continue
        flat = {child.tag.upper(): _txt(child) for child in lp}
        if not flat:
            continue
        records.append(flat)
    if records:
        show_fields("FEHD", list(records[0].keys()))
    return records, type_map, dist_map


def pick_tag(rec: dict, *patterns: str) -> str:
    for p in patterns:
        for k, v in rec.items():
            if re.fullmatch(p, k) and v:
                return v
    return ""


def classify_fehd(type_desc: str) -> tuple[str, int, str, bool]:
    d = (type_desc or "").lower()
    for kw, icp, fit, arch, amb in FEHD_TYPES:
        if kw in d:
            return icp, fit, arch, amb
    return "MERCHANT", 2, f"Other licence: {type_desc or 'unknown'}", True


def fehd_signals(text: str, source: str, today: date) -> list[Signal]:
    records, type_map, dist_map = parse_fehd_xml(text)
    out = []
    for rec in records:
        tcode = pick_tag(rec, r"TYPE", r"TYPE_?CODE", r"LIC_?TYPE")
        tdesc = type_map.get(tcode, tcode)
        dcode = pick_tag(rec, r"DIST", r"DIST(RICT)?_?CODE", r"DISTRICT")
        dist = dist_map.get(dcode, dcode)
        icp, fit, arch, amb = classify_fehd(tdesc)
        name = pick_tag(rec, r"SS", r"SHOP_?SIGN", r"NAME", r"SHOPSIGN")
        addr = pick_tag(rec, r"ADR", r"ADDR(ESS)?")
        no_sign = bool(PLACEHOLDER_NAME.match(name.strip()))
        if no_sign:
            name = "(no shop sign)"
        if "food factory" in (tdesc or "").lower():
            if INDUSTRIAL_ADDR.search(addr.upper()):
                icp, fit, arch, amb = "DISTRIBUTOR", 3, "Food factory in industrial premises (verify products)", True
            elif BAKERY_NAME.search(name.upper()):
                fit, arch = 5, "Bakery outlet (food factory licence)"
        s = Signal(detected=today.isoformat(), source=source, icp=icp, name=name,
                   licence_or_reg=pick_tag(rec, r"LICNO", r"LIC_?NO", r"LICEN[CS]E_?NO"),
                   licence_type=tdesc, archetype=arch, district=dist, address=addr,
                   expiry=pick_tag(rec, r"EXPDATE", r"EXP(IRY)?_?DATE"),
                   fit_score=fit, district_score=district_score(dist))
        if no_sign:
            s.next_action = "No shop sign on the licence. Visit the address to identify it."
        if icp == "DISTRIBUTOR":
            s.ambient_gate = "PASS" if amb else "FAIL"
        out.append(s)
    return out


# ================================================================ CFS importers
def _flatten_json(obj: Any) -> list[dict]:
    if isinstance(obj, list):
        return [x for x in obj if isinstance(x, dict)]
    if isinstance(obj, dict):
        for v in obj.values():
            if isinstance(v, list) and v and isinstance(v[0], dict):
                return v
            if isinstance(v, dict):
                inner = _flatten_json(v)
                if inner:
                    return inner
    return []


def jpick(rec: dict, *patterns: str) -> str:
    """First non-empty value whose key matches, trying patterns in order."""
    low = {str(k).lower(): v for k, v in rec.items()}
    for p in patterns:
        for k, v in low.items():
            if re.search(p, k) and v not in (None, ""):
                return str(v)
    return ""


def parse_categories(rec: dict) -> list[str]:
    for v in rec.values():
        vals = v if isinstance(v, list) else re.findall(r"C\d{1,2}", str(v)) if re.search(r"\bC\d{1,2}\b", str(v)) else []
        codes = [str(x).strip() for x in vals if re.fullmatch(r"C\d{1,2}", str(x).strip())]
        if codes:
            return codes
    return []


def classify_importer(name: str, cats: list[str]) -> tuple[str, int, str]:
    """Returns (ambient gate, fit, archetype). Categories first, name as backup."""
    upper = name.upper()
    if ALCOHOL_NAME.search(upper):
        return "FAIL", 0, "Alcohol importer (excluded)"
    kinds = [CFS_CATEGORIES.get(c, ("Unknown", "unknown"))[1] for c in cats]
    ambient = [c for c in cats if CFS_CATEGORIES.get(c, ("", ""))[1] == "ambient"]
    labels = ", ".join(CFS_CATEGORIES[c][0] for c in ambient)
    if ambient:
        fit = min(5, 3 + len(ambient))
        broad = " (broadline, many categories)" if len(cats) >= 6 else ""
        return "PASS", fit, f"Ambient: {labels}{broad}"
    if kinds and all(k in ("cold", "unfit") for k in kinds):
        return "FAIL", 0, "Only fresh, chilled, frozen or supplement categories"
    if COLD_NAME.search(upper):
        return "FAIL", 0, "Name suggests chilled or frozen (verify)"
    if AMBIENT_NAME.search(upper):
        return "PASS", 4, "Name suggests ambient goods"
    return "PASS", 2, "Category unclear, verify ambient range"


def importer_role(rec: dict) -> str:
    """Read the I (importer) and D (distributor) flags in foodClassification."""
    raw = rec.get("foodClassification") or rec.get("foodclassification") or ""
    items = raw if isinstance(raw, list) else []
    if not items and isinstance(raw, str):
        try:
            import ast
            items = ast.literal_eval(raw)
        except (ValueError, SyntaxError):
            items = []
    imp = any(str(i.get("I", "")).upper() == "Y" for i in items if isinstance(i, dict))
    dis = any(str(i.get("D", "")).upper() == "Y" for i in items if isinstance(i, dict))
    if not items:
        imp = "'I': 'Y'" in str(raw)
        dis = "'D': 'Y'" in str(raw)
    return ("Importer and distributor" if imp and dis else "Importer" if imp
            else "Distributor" if dis else "Registered trader")


def importer_signals(text: str, today: date) -> list[Signal]:
    rows = _flatten_json(json.loads(text))
    if rows:
        show_fields("CFS importers", list(rows[0].keys()))
        sample = {k: (str(v)[:40]) for k, v in list(rows[0].items())[:8]}
        print(f"    sample record: {sample}", file=sys.stderr)
    out = []
    for r in rows:
        name = jpick(r, r"^en.*name", r"name.*en", r"^name$", r"company|trader", r"name")
        if not name:
            continue
        cats = parse_categories(r)
        gate, fit, arch = classify_importer(name, cats)
        role = importer_role(r)
        out.append(Signal(detected=today.isoformat(), source="importers", icp="DISTRIBUTOR",
                          name=name, licence_or_reg=jpick(r, r"^trn$", r"reg.*n|registration|^no$|number|licen"),
                          licence_type=f"{role}: {' '.join(cats)}" if cats else role,
                          archetype=arch, address=jpick(r, r"en.*addr", r"addr"),
                          phone=jpick(r, r"tel|phone"),
                          expiry=jpick(r, r"expir|valid"), ambient_gate=gate, fit_score=fit))
    return out


# ================================================================ CR (optional)
def cr_signals(today: date, weeks: int = 6) -> list[Signal]:
    meta = json.loads(decode(_get_bytes(URLS["cr_package"])))
    resources = (meta.get("result") or {}).get("resources") or []
    local = [r for r in resources if "local" in (r.get("name") or "").lower()
             and (r.get("format") or "").upper() == "CSV"]
    local.sort(key=lambda r: r.get("url", ""), reverse=True)
    skipped_xls = sum(1 for r in resources if (r.get("format") or "").upper() == "XLS")
    if skipped_xls:
        print(f"    ... {skipped_xls} weekly files are XLS only and are skipped "
              f"(no extra libraries needed this way)", file=sys.stderr)
    out = []
    for res in local[:weeks]:
        text = decode(_get_bytes(res["url"]))
        rows = list(csv.reader(io.StringIO(text)))
        for row in rows:
            cells = [c.strip() for c in row]
            joined = " ".join(cells).upper()
            brn = next((c for c in cells if re.fullmatch(r"\d{7,8}", c)), "")
            if not brn:
                continue
            name = max(cells, key=len)
            if CR_MERCHANT.search(joined):
                icp, fit, arch = "MERCHANT", 2, "New company, name suggests F&B (no address yet)"
            elif CR_DISTRIB.search(joined):
                icp, fit, arch = "DISTRIBUTOR", 2, "New company, name suggests food trading"
            else:
                continue
            s = Signal(detected=today.isoformat(), source="cr", icp=icp, name=name,
                       licence_or_reg=brn, licence_type="New company (CR weekly list)",
                       archetype=arch, fit_score=fit)
            if icp == "DISTRIBUTOR":
                s.ambient_gate = "FAIL" if COLD_NAME.search(joined) else "PASS"
            out.append(s)
        _sleep(1)
    return out


# ================================================================ pipeline
def detect_chains(signals: list[Signal]) -> None:
    counts: dict[str, int] = {}
    for s in signals:
        if s.icp == "MERCHANT" and s.name != "(no shop sign)":
            counts[norm(s.name)] = counts.get(norm(s.name), 0) + 1
    for s in signals:
        if s.icp == "MERCHANT" and s.name != "(no shop sign)":
            s.outlets = counts.get(norm(s.name), 1)


def load_state() -> dict:
    if STATE_FILE.exists():
        try:
            return json.loads(STATE_FILE.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            print("  ! state file corrupt, starting fresh", file=sys.stderr)
    return {"first_seen": {}, "due_sent": [], "last_run": None}


def save_state(state: dict) -> None:
    try:
        STATE_FILE.write_text(json.dumps(state, ensure_ascii=False), encoding="utf-8")
    except OSError as exc:
        print(f"  ! could not write state ({exc}). Next run will re-alert.", file=sys.stderr)


def process(signals: list[Signal], state: dict, today: date) -> tuple[list[Signal], list[Signal], bool]:
    """Returns (new signals, day-90 due signals, is_baseline)."""
    seen: dict = state.setdefault("first_seen", {})
    due_sent: set = set(state.setdefault("due_sent", []))
    baseline = not seen
    # v1 skipped importers with no English name. On the first v2 run, record
    # those silently as baseline so they are not reported as new.
    upgrading = bool(seen) and state.get("v", 1) < 2
    state["v"] = 2
    detect_chains(signals)

    new, due = [], []
    for s in signals:
        k = s.key()
        if k not in seen:
            silent = upgrading and s.source == "importers"
            seen[k] = {"d": today.isoformat(), "b": baseline or silent}
            if silent:
                continue
            s.first_seen, s.days_since = today.isoformat(), 0
            s.maturity_score = maturity_score(0)
            s.finalise(baseline=baseline)
            if not s.trigger.startswith("EXCLUDE"):
                new.append(s)
            continue
        info = seen[k]
        if info.get("b") or k in due_sent:
            continue
        age = (today - date.fromisoformat(info["d"])).days
        if age >= DUE_AFTER_DAYS and s.icp == "MERCHANT":
            s.first_seen, s.days_since = info["d"], age
            s.maturity_score = maturity_score(age)
            s.finalise()
            if not s.trigger.startswith("EXCLUDE"):
                s.trigger = "DUE - day 90"
                s.next_action = "Opened about 3 months ago. Surplus pattern now visible. Approach this week."
                due.append(s)
                due_sent.add(k)

    state["due_sent"] = sorted(due_sent)
    state["last_run"] = today.isoformat()
    order = lambda x: (-x.signal_score, x.name)
    return sorted(new, key=order), sorted(due, key=order), baseline


COLUMNS = list(Signal.__dataclass_fields__.keys())


def write_csv(rows: list[Signal], path: Path) -> None:
    with path.open("w", newline="", encoding="utf-8-sig") as fh:
        w = csv.DictWriter(fh, fieldnames=COLUMNS)
        w.writeheader()
        for s in rows:
            w.writerow(asdict(s))


def format_alert(new: list[Signal], due: list[Signal], baseline: bool, status: dict, today: date) -> str:
    tag = " (BASELINE, first run: the whole register, not new businesses)" if baseline else ""
    lines = [f"*Yindii HK radar* {today.isoformat()}, {len(new)} new, {len(due)} due{tag}",
             "  sources: " + ", ".join(f"{k}={v}" for k, v in status.items())]
    groups = [("DUE - day 90, approach now", due),
              ("NEW bakeries and cafes", [s for s in new if s.icp == "MERCHANT" and s.fit_score >= 5]),
              ("NEW restaurants and others", [s for s in new if s.icp == "MERCHANT" and s.fit_score < 5]),
              ("NEW importers and distributors", [s for s in new if s.icp == "DISTRIBUTOR"])]
    for label, g in groups:
        if not g or baseline:
            continue
        lines += ["", f"{label} ({len(g)})"]
        for s in g[:10]:
            lines.append(f"  {s.signal_score:>5}  {s.name[:40]:<40} {s.district or s.archetype[:28]}")
        if len(g) > 10:
            lines.append(f"  ... and {len(g) - 10} more")
    return "\n".join(lines)


def post_webhook(url: str, text: str) -> None:
    try:
        req = urllib.request.Request(url, data=json.dumps({"text": text}).encode(),
                                     headers={"Content-Type": "application/json"})
        urllib.request.urlopen(req, timeout=15)
    except Exception as exc:  # noqa: BLE001
        print(f"  ! webhook failed: {exc}", file=sys.stderr)


def run_once(args) -> int:
    today = date.today()
    state = load_state()
    wanted = [s.lower() for s in (args.sources or DEFAULT_SOURCES)]
    status: dict[str, str] = {}
    signals: list[Signal] = []
    for src in wanted:
        print(f"  {src.upper()} ...")
        try:
            if src in ("fehd_restaurants", "fehd_food"):
                got = fehd_signals(decode(_get_bytes(URLS[src])), src, today)
            elif src == "importers":
                got = importer_signals(decode(_get_bytes(URLS["importers"])), today)
            elif src == "cr":
                got = cr_signals(today)
            else:
                print(f"    ! unknown source {src}", file=sys.stderr)
                continue
            status[src] = f"{len(got):,}"
            print(f"    {len(got):,} records")
            signals.extend(got)
        except Exception as exc:  # noqa: BLE001
            status[src] = "FAILED"
            print(f"    ! {src} failed: {type(exc).__name__}: {exc}", file=sys.stderr)

    if status and all(v == "FAILED" for v in status.values()):
        print("\nCONNECTION FAILED. Every source failed. Nothing written.", file=sys.stderr)
        return 3

    new, due, baseline = process(signals, state, today)
    save_state(state)
    write_csv(due + new, Path(args.out))
    alert = format_alert(new, due, baseline, status, today)
    if args.webhook and (new or due) and not baseline:
        post_webhook(args.webhook, alert)
    try:
        print()
        print(alert)
        print(f"\nWrote {args.out}. Remembering {len(state['first_seen']):,} records.")
    except BrokenPipeError:
        pass
    return 0


# ================================================================ selftest
FEHD_FIXTURE = """<?xml version="1.0" encoding="UTF-8"?>
<DATA>
 <TYPE_CODE><TYPE ID="RL">General Restaurant Licence</TYPE><TYPE ID="LR">Light Refreshment Restaurant Licence</TYPE>
  <TYPE ID="BL">Bakery Licence</TYPE><TYPE ID="FP">Fresh Provision Shop Licence</TYPE>
  <TYPE ID="FF">Food Factory Licence</TYPE></TYPE_CODE>
 <DIST_CODE><DIST ID="11">Eastern</DIST><DIST ID="18">Central and Western</DIST><DIST ID="95">Tai Po</DIST></DIST_CODE>
 <LPS>
  <LP><TYPE>BL</TYPE><DIST>18</DIST><LICNO>2218800001</LICNO><SS>Example Bakery</SS>
      <ADR>SHOP 1, G/F, 1 QUEEN'S ROAD CENTRAL, CENTRAL</ADR><EXPDATE>2027-05-01</EXPDATE></LP>
  <LP><TYPE>LR</TYPE><DIST>11</DIST><LICNO>2211800002</LICNO><SS>Example Cafe</SS>
      <ADR>SHOP 2, G/F, 10 KING'S ROAD, NORTH POINT</ADR><EXPDATE>2027-06-01</EXPDATE></LP>
  <LP><TYPE>FP</TYPE><DIST>95</DIST><LICNO>2995800003</LICNO><SS>Example Meat Shop</SS>
      <ADR>STALL 3, TAI PO MARKET</ADR><EXPDATE>2027-07-01</EXPDATE></LP>
  <LP><TYPE>RL</TYPE><DIST>18</DIST><LICNO>2218800004</LICNO><SS>Chain Noodles</SS>
      <ADR>SHOP A, CENTRAL</ADR><EXPDATE>2027-01-01</EXPDATE></LP>
  <LP><TYPE>RL</TYPE><DIST>11</DIST><LICNO>2211800005</LICNO><SS>Chain Noodles</SS>
      <ADR>SHOP B, NORTH POINT</ADR><EXPDATE>2027-01-01</EXPDATE></LP>
  <LP><TYPE>RL</TYPE><DIST>95</DIST><LICNO>2995800006</LICNO><SS>Chain Noodles</SS>
      <ADR>SHOP C, TAI PO</ADR><EXPDATE>2027-01-01</EXPDATE></LP>
 </LPS>
</DATA>"""

IMPORTER_FIXTURE = json.dumps({"data": [
    {"Registration No": "TR-0001", "Name (English)": "EXAMPLE SNACK TRADING LIMITED",
     "Type": "Registered food importer", "Address": "KWUN TONG"},
    {"Registration No": "TR-0002", "Name (English)": "EXAMPLE FROZEN SEAFOOD CO LTD",
     "Type": "Registered food importer", "Address": "KWAI CHUNG"},
    {"Registration No": "TR-0003", "Name (English)": "EXAMPLE WINE CELLAR LIMITED",
     "Type": "Registered food distributor", "Address": "CENTRAL"},
    {"Registration No": "TR-0004", "Name (English)": "EXAMPLE GENERAL TRADING LIMITED",
     "Type": "Registered food distributor", "Address": "SHEUNG WAN"}]})


def selftest() -> int:
    fails: list[str] = []

    def chk(label, got, want):
        ok = got == want
        print(f"  {'PASS' if ok else 'FAIL'}  {label}: got {got!r}, want {want!r}")
        if not ok:
            fails.append(label)

    d0 = date(2026, 10, 1)
    print("FEHD XML parsing")
    sigs = fehd_signals(FEHD_FIXTURE, "fehd_food", d0)
    by = {s.licence_or_reg: s for s in sigs}
    chk("six records parsed", len(sigs), 6)
    chk("bakery type decoded from code table", by["2218800001"].licence_type, "Bakery Licence")
    chk("district decoded", by["2218800001"].district, "Central and Western")
    chk("bakery routed to merchant", (by["2218800001"].icp, by["2218800001"].fit_score), ("MERCHANT", 5))
    chk("light refreshment is a cafe", by["2211800002"].archetype, "Cafe / Light refreshment")
    chk("fresh provision fails gate", by["2995800003"].ambient_gate, "FAIL")

    print("\nimporter register")
    imp = {s.name: s for s in importer_signals(IMPORTER_FIXTURE, d0)}
    chk("snack importer ambient by name", (imp["EXAMPLE SNACK TRADING LIMITED"].ambient_gate,
                                           imp["EXAMPLE SNACK TRADING LIMITED"].fit_score), ("PASS", 4))
    chk("frozen seafood excluded", imp["EXAMPLE FROZEN SEAFOOD CO LTD"].ambient_gate, "FAIL")
    chk("wine importer excluded", imp["EXAMPLE WINE CELLAR LIMITED"].ambient_gate, "FAIL")
    chk("unknown category kept for checking", imp["EXAMPLE GENERAL TRADING LIMITED"].fit_score, 2)
    chk("registration number captured", imp["EXAMPLE SNACK TRADING LIMITED"].licence_or_reg, "TR-0001")

    print("\nbaseline, then new, then day-90 due")
    state = {"first_seen": {}, "due_sent": []}
    new, due, base = process(fehd_signals(FEHD_FIXTURE, "fehd_food", d0), state, d0)
    chk("first run is baseline", base, True)
    chk("baseline rows marked BASELINE", {s.trigger for s in new if s.icp == "MERCHANT"}, {"BASELINE"})
    chk("chain detected across districts", next(s for s in new if s.name == "Chain Noodles").outlets, 3)

    fixture2 = FEHD_FIXTURE.replace("</LPS>", """<LP><TYPE>BL</TYPE><DIST>18</DIST><LICNO>2218800099</LICNO>
      <SS>Brand New Bakery</SS><ADR>SHOP 9, CENTRAL</ADR><EXPDATE>2027-10-01</EXPDATE></LP></LPS>""")
    d1 = d0 + timedelta(days=7)
    new, due, base = process(fehd_signals(fixture2, "fehd_food", d1), state, d1)
    chk("second run not baseline", base, False)
    chk("only the new bakery is new", [s.name for s in new], ["Brand New Bakery"])
    chk("new bakery waits for day 90", new[0].trigger, "NURTURE 90")

    d2 = d1 + timedelta(days=91)
    new, due, base = process(fehd_signals(fixture2, "fehd_food", d2), state, d2)
    chk("day 90: flagged DUE", [(s.name, s.trigger) for s in due], [("Brand New Bakery", "DUE - day 90")])
    chk("nothing new on day 90", len(new), 0)
    new, due, base = process(fehd_signals(fixture2, "fehd_food", d2 + timedelta(days=1)), state,
                             d2 + timedelta(days=1))
    chk("DUE only fires once", len(due), 0)
    chk("baseline businesses never go DUE", "fehd_food|2218800001" in state["due_sent"], False)

    print("\nreal 2026 file format: codes only, no readable code table")
    real_xml = """<DATA><LPS>
      <LP><TYPE>FF</TYPE><DIST>18</DIST><LICNO>2918811534</LICNO><SS>SAINT HONORE CAKE SHOP</SS>
          <ADR>SHOP 1, G/F, CENTRAL</ADR><EXPDATE>2027-12-15</EXPDATE></LP>
      <LP><TYPE>FF</TYPE><DIST>51</DIST><LICNO>2951805468</LICNO><SS>BAKERY CORNER</SS>
          <ADR>ROOM 5, 7/F, MEI HING INDUSTRIAL BUILDING, KWUN TONG</ADR><EXPDATE>2027-04-13</EXPDATE></LP>
      <LP><TYPE>FF</TYPE><DIST>61</DIST><LICNO>3961800001</LICNO><SS>HANA-MUSUBI</SS>
          <ADR>SHOP 3, TSIM SHA TSUI</ADR><EXPDATE>2027-01-01</EXPDATE></LP>
      <LP><TYPE>RR</TYPE><DIST>62</DIST><LICNO>3962800002</LICNO><SS>(NO RECORD FOUND)</SS>
          <ADR>SHOP 4, MONG KOK</ADR><EXPDATE>2027-01-01</EXPDATE></LP>
      <LP><TYPE>RR</TYPE><DIST>12</DIST><LICNO>3912800003</LICNO><SS>No Record</SS>
          <ADR>SHOP 5, WAN CHAI</ADR><EXPDATE>2027-01-01</EXPDATE></LP>
      <LP><TYPE>FC</TYPE><DIST>91</DIST><LICNO>2991800004</LICNO><SS>REAL COOL COLD STORAGE</SS>
          <ADR>KWAI CHUNG</ADR><EXPDATE>2027-01-01</EXPDATE></LP>
    </LPS></DATA>"""
    rs = {s.licence_or_reg: s for s in fehd_signals(real_xml, "fehd_food", d0)}
    chk("FF decoded without a code table", rs["2918811534"].licence_type, "Food Factory Licence")
    chk("district 18 decoded", rs["2918811534"].district, "Central and Western")
    chk("district 61 decoded", rs["3961800001"].district, "Yau Tsim")
    chk("FF bakery outlet is a top merchant", (rs["2918811534"].icp, rs["2918811534"].fit_score), ("MERCHANT", 5))
    chk("FF takeaway outlet is a merchant", (rs["3961800001"].icp, rs["3961800001"].fit_score), ("MERCHANT", 4))
    chk("FF in industrial building is a distributor", rs["2951805468"].icp, "DISTRIBUTOR")
    chk("cold store fails the gate", rs["2991800004"].ambient_gate, "FAIL")
    chk("placeholder name relabelled", rs["3962800002"].name, "(no shop sign)")
    detect_chains(list(rs.values()))
    chk("no-sign premises never form a chain", rs["3962800002"].outlets, 1)

    print("\nimporter categories")
    cat_json = json.dumps([
        {"name_en": "BROADLINE FOODS LIMITED", "category": ["C1", "C9", "C10", "C11", "C13", "C4", "C2"]},
        {"name_en": "OCEAN SEAFOOD LIMITED", "category": ["C4"]},
        {"name_en": "HEALTH WELLNESS LIMITED", "category": ["C16"]},
        {"name_en": "TEA HOUSE LIMITED", "category": ["C10"]},
        {"name_tc": "某某食品有限公司", "category": ["C13"]}])
    ci = {s.name: s for s in importer_signals(cat_json, d0)}
    chk("broadline ambient importer scores 5", (ci["BROADLINE FOODS LIMITED"].ambient_gate,
                                                ci["BROADLINE FOODS LIMITED"].fit_score), ("PASS", 5))
    chk("broadline flagged", "broadline" in ci["BROADLINE FOODS LIMITED"].archetype, True)
    chk("seafood-only importer excluded", ci["OCEAN SEAFOOD LIMITED"].ambient_gate, "FAIL")
    chk("supplements-only importer excluded", ci["HEALTH WELLNESS LIMITED"].ambient_gate, "FAIL")
    chk("single ambient category passes", (ci["TEA HOUSE LIMITED"].ambient_gate,
                                            ci["TEA HOUSE LIMITED"].fit_score), ("PASS", 4))
    chk("Chinese-name-only importer kept", "某某食品有限公司" in ci, True)

    print("\nreal CFS record shape, from the live log")
    live = json.dumps([{"trn": "TR-11-001017", "cnBusName": "",
                        "mainFoodCategory": "['C4', 'C2', 'C6', 'C5', 'C7', 'C1', 'C11']",
                        "cnBusAddr": "新界葵涌國瑞路116-122號",
                        "foodClassification": "[{'I': 'Y', 'D': 'Y', 'code': 'C2C'}]",
                        "enBusName": "Honortry Enterprise Limited",
                        "enBusAddr": "Flat F, 12/F, City Industrial Complex", "telNo": "24101651"},
                       {"trn": "TR-11-000002", "cnBusName": "某食品", "mainFoodCategory": "['C10']",
                        "cnBusAddr": "九龍", "foodClassification": "[{'I': 'N', 'D': 'Y', 'code': 'C10A'}]",
                        "enBusName": "", "enBusAddr": "", "telNo": ""}])
    lv = importer_signals(live, d0)
    chk("registration number from trn", lv[0].licence_or_reg, "TR-11-001017")
    chk("English address preferred", lv[0].address, "Flat F, 12/F, City Industrial Complex")
    chk("phone captured", lv[0].phone, "24101651")
    chk("importer and distributor role read", lv[0].licence_type.split(":")[0], "Importer and distributor")
    chk("categories parsed from string", "C11" in lv[0].licence_type, True)
    chk("Chinese name used when English is blank", lv[1].name, "某食品")
    chk("distributor-only role read", lv[1].licence_type.split(":")[0], "Distributor")
    chk("falls back to Chinese address", lv[1].address, "九龍")

    print("\nupgrade from the first live baseline")
    st = {"first_seen": {"importers|BROADLINE FOODS|": {"d": "2026-11-12", "b": True}}, "due_sent": []}
    new_u, _, _ = process(importer_signals(cat_json, d0), st, d0)
    chk("upgrade run reports no importers as new", len(new_u), 0)
    chk("state version bumped", st.get("v"), 2)
    new_n, _, _ = process(importer_signals(cat_json.replace("TEA HOUSE", "NEW TEA"), d0), st, d0)
    chk("after upgrade, a genuinely new importer is reported", [s.name for s in new_n], ["NEW TEA LIMITED"])

    print("\ndistrict weights")
    chk("central and western high", district_score("Central and Western"), 5)
    chk("unknown district low", district_score("Atlantis"), 1)

    print(f"\n{'ALL CHECKS PASSED' if not fails else f'{len(fails)} FAILED: ' + ', '.join(fails)}")
    return 0 if not fails else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--once", action="store_true")
    ap.add_argument("--sources", nargs="*", help="fehd_restaurants fehd_food importers cr")
    ap.add_argument("--out", default="yindii_radar_hk_new.csv")
    ap.add_argument("--webhook")
    args = ap.parse_args()
    if args.selftest:
        return selftest()
    return run_once(args)


if __name__ == "__main__":
    sys.exit(main())
