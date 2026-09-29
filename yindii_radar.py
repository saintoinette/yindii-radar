!/usr/bin/env python3
"""
Yindii Singapore, multi-source new-business radar (v3).

Watches four Singapore registries, detects newly appearing food businesses,
routes each to the correct Yindii ICP, and alerts.

  ACRA   company registrations, SSIC codes, incorporation dates
         -> the ONLY source that sees distributors (Yindii Drop)
  SFA    licensed eating establishments, geospatial with real COORDINATES
         -> best premises geocoding, enables true distance-based neighbour detection
  NEA    licensed eating establishments with hygiene grades and demerit history
         -> premises address plus a quality and distress filter
  MUIS   halal-certified establishments, 3,982 of them
         -> premises address, growth signal, and the Ramadan/Hari Raya window

WHY FOUR SOURCES AND NOT ONE
  ACRA knows a company exists but often records a corporate secretary's office
  as the address, which wrecks precinct mapping. SFA, NEA and MUIS record the
  ACTUAL PREMISES. So ACRA answers "who is new" and the licence registers answer
  "where are they and are they really trading".

  A business appearing in two or more registers is corroborated, and the scorer
  rewards that, because a company with an ACRA registration AND a food licence is
  materially more real than one with only a registration.

    python3 yindii_radar.py --selftest
    python3 yindii_radar.py --once
    python3 yindii_radar.py --once --sources muis          # works without data.gov.sg
    python3 yindii_radar.py --once --webhook https://hooks.slack.com/...

TESTING STATUS, stated honestly
  MUIS      TESTED LIVE. 3,982 records pulled, field names verified 17 Sep 2026.
  ACRA      UNTESTED. The build sandbox returns HTTP 403 for data.gov.sg.
  SFA/NEA   UNTESTED, same reason. Parsers are covered by fixtures built from
            the real published response shapes.
  Run --selftest first, then --once --sources muis to prove the pipeline end to
  end on a source that works, then add the rest.

SOURCE OF TRUTH NOTE
  MUIS publishes no bulk API. The official register is the web e-service at
  halal.muis.gov.sg/halal/establishments. This tool reads a community-maintained
  daily mirror on GitHub, which is convenient but UNOFFICIAL and could stop
  updating without notice. Verify anything important against the official
  register before acting on it.
"""

from __future__ import annotations

import argparse
import csv
import os
import html
import io
import json
import math
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass, asdict
from datetime import date, datetime
from pathlib import Path
from typing import Any, Callable

DGS_API = "https://data.gov.sg/api/action/datastore_search"
DGS_COLLECTION_META = "https://api-production.data.gov.sg/v2/public/api/collections/2/metadata"
STATE_FILE = Path("yindii_radar_state.json")

# ---------------------------------------------------------------- resource ids
# Verified against data.gov.sg dataset pages, 17 Sep 2026.
ACRA_RESOURCES: dict[str, str] = {
    "A": "d_8575e84912df3c28995b8e6e0e05205a",
    "M": "d_9af9317c646a1c881bb5591c91817cc6",
    "N": "d_67e99e6eabc4aad9b5d48663b579746a",
    "S": "d_df7d2d661c0c11a7c367c9ee4bf896c1",
    "Z": "d_4e3db8955fdcda6f9944097bef3d2724",
}
# SFA "Eating Establishments". GeoJSON FeatureCollection. Attributes are buried
# in an HTML table inside each feature's Description field, which is why there is
# a parser for it below rather than a plain field read.
SFA_EATING_ESTABLISHMENTS = "d_1f0313499a17075d13aae6ed3e825bc6"
# NEA "List of NEA Licensed Eating Establishments", with grades and track records.
NEA_EATING_ESTABLISHMENTS = "d_227473e811b09731e64725f140b77697"
# MUIS has no official bulk endpoint. Community daily mirror. See header note.
MUIS_MIRROR_JSON = ("https://raw.githubusercontent.com/zootato/"
                    "singapore-halal-establishments/main/halal_establishments.json")
MUIS_OFFICIAL = "https://halal.muis.gov.sg/halal/establishments"

# ---------------------------------------------------------------- ICP A: merchant
MERCHANT_SSIC: dict[str, tuple[int, str, tuple[str, ...]]] = {
    # SSIC 2020 codes as ACRA actually uses them. Verified against SingStat's
    # official listing, 29 Sep 2026. An earlier version used 56101/56102, which
    # do not exist in SSIC 2020, so every new cafe and restaurant was missed.
    "56112": (5, "Cafe / Coffee Chain", ("cafe",)),
    "10712": (5, "Premium Bakery Chain", ("bread, cakes and confectionery",)),
    "47213": (5, "Premium Bakery Chain", ("confectionery and bakery",)),
    "56111": (4, "Hot-Meal QSR Chain", ("restaurants",)),
    "56121": (4, "Hot-Meal QSR Chain", ("fast food",)),
    "10719": (4, "Premium Bakery Chain", ("bakery products n.e.c",)),
    "47101": (4, "Grocer / Supermarket", ("supermarket", "hypermarket")),
    "55101": (4, "Hotel", ("hotels",)),
    "56122": (3, "Multi-tenant operator", ("food courts", "coffee shops", "canteens")),
    "56123": (3, "Cafe / Coffee Chain", ("kiosks mainly for takeaway",)),
    "47102": (3, "Convenience / Petrol Mart", ("mini-mart", "convenience store", "provision shop")),
    "56200": (2, "Caterer / Events", ("food caterers",)),
    "47219": (2, "Triage manually", ("retail sale of food",)),
    "56140": (1, "Hawker stall (low fit)", ("stalls selling cooked food",)),
    "56130": (1, "Excluded", ("pubs",)),
    "47220": (1, "Excluded", ("retail sale of beverages",)),
}

# ---------------------------------------------------------------- ICP B: distributor
# ambient_likely is the HARD GATE. Cold chain has no workaround in a delivered box.
DISTRIBUTOR_SSIC: dict[str, tuple[bool, int, str, tuple[str, ...]]] = {
    "46304": (True, 5, "Confectionery and bakery wholesale", ("wholesale of confectionery",)),
    "46303": (True, 5, "General grocery wholesale", ("general line", "groceries")),
    "46309": (True, 4, "Packaged goods wholesale n.e.c.", ("beverages and tobacco n.e.c", "dried or canned")),
    "10711": (True, 5, "Biscuit manufacturer", ("manufacture of biscuits",)),
    "10794": (True, 5, "Chips and crackers manufacturer", ("chips, crackers",)),
    "10761": (True, 5, "Instant beverage manufacturer", ("instant beverages",)),
    "10791": (True, 4, "Sauce manufacturer", ("manufacture of sauces",)),
    "10731": (True, 4, "Cocoa manufacturer", ("cocoa and chocolate powder",)),
    "10732": (True, 4, "Chocolate manufacturer", ("chocolate products",)),
    "10733": (True, 4, "Confectionery manufacturer", ("non-chocolate confectionery",)),
    "10764": (True, 4, "Tea manufacturer", ("manufacture of tea",)),
    "10740": (True, 3, "Noodle manufacturer (check fresh vs dried)", ("noodles, vermicelli",)),
    "46301": (False, 2, "Produce wholesale (FRESH, gate fails)", ("fruits and vegetables",)),
    "46302": (False, 0, "Protein wholesale (CHILLED/FROZEN, gate fails)", ("livestock, meat, poultry", "seafood")),
    "46305": (False, 0, "Ice-cream wholesale (FROZEN, gate fails)", ("ice-cream",)),
    "46307": (False, 0, "Liquor and beverages (REGULATED, excluded)", ("liquor",)),
    "46308": (False, 0, "Tobacco (EXCLUDED)", ("tobacco products",)),
    "10750": (False, 0, "Cooked-food preparations (COLD CHAIN, gate fails)", ("cooked-food preparations", "prepared meals")),
    "10792": (False, 0, "Soya bean products (CHILLED, gate fails)", ("soya bean products",)),
    "10800": (False, 0, "Animal feed (not human food, excluded)", ("animal feeds",)),
    "10": (True, 3, "Food manufacture (verify retail format)", ("manufacture of",)),
}
# Meat (101xx) and fish (102xx) processing are cold chain by nature.
COLD_PREFIXES = ("101", "102")

MUIS_TYPE_MAP: dict[str, tuple[int, str]] = {
    "Snack Bar / Bakery": (5, "Premium Bakery Chain"),      # 806, the prize
    "Restaurant": (4, "Hot-Meal QSR Chain"),                # 1685
    "Central Kitchen": (4, "Manufacturer / Central Kitchen"),  # 228, high volume
    "Catering Company": (3, "Caterer / Events"),            # 183
    "Food Kiosk": (3, "Cafe / Coffee Chain"),               # 18
    "Food Station": (2, "Hot-Meal QSR Chain"),              # 30
    "Halal Section": (2, "Grocer / Supermarket"),           # 24
    "Hawker": (1, "Hawker (low fit, no packaging)"),        # 903
    "Staff Canteen": (1, "Institutional (closed catchment)"),  # 85
    "Canteen": (1, "Institutional (closed catchment)"),     # 17
    "Short Term Stall(Bazaar/Road Shows)": (0, "Temporary, excluded"),  # 3
}

# ---------------------------------------------------------------- precincts
PRECINCTS: list[tuple[str, int, tuple[str, ...]]] = [
    ("Orchard", 5, ("22", "23", "24")),
    ("CBD - Raffles Place / Tanjong Pagar", 4, ("01", "02", "03", "04", "06", "07", "08")),
    ("Holland V / Dempsey / Bukit Timah", 4, ("10", "11", "21")),
    ("Novena / Thomson", 4, ("20",)),
    ("Bishan (Junction 8)", 4, ("56", "57")),
    ("Serangoon (NEX)", 4, ("53", "55")),
    ("Paya Lebar (PLQ)", 4, ("38", "39", "40", "41")),
    ("Tampines", 3, ("51", "52")),
    ("Jurong East (JEM / Westgate / IMM)", 3, ("60", "61", "62", "63", "64")),
    ("Marina Bay", 3, ("05",)),
    ("Jewel / Changi", 3, ("49", "50", "81")),
    ("Punggol / Sengkang", 3, ("54", "82")),
    ("Woodlands (Causeway Point)", 2, ("73", "75", "76")),
    ("Sentosa / HarbourFront", 2, ("09",)),
]

W_SSIC, W_PRECINCT, W_MATURITY, W_EXPANSION, W_WARM = 0.30, 0.25, 0.20, 0.15, 0.10
CORROBORATION_BONUS = 0.25   # per extra register a business appears in, capped below
MAX_CORROBORATION = 0.50
MIN_MERCHANT_SCORE = 2
LIVE_STATUSES = {"live", "live company", "registered", "existing"}
NEIGHBOUR_RADIUS_M = 200

FESTIVE_WINDOWS = [
    ("Chinese New Year", 11, 5, None),
    ("Mid-Autumn", 7, 5, None),
    ("Christmas", 9, 4, None),
    # Ramadan and Hari Raya move ~11 days earlier each year, so no fixed month.
    # MUIS halal certification is the best proxy for who is exposed to it.
    ("Ramadan and Hari Raya", None, 4, "halal"),
]


# ================================================================ model
@dataclass
class Signal:
    detected: str = ""
    sources: str = ""              # pipe-joined list of registers it appeared in
    icp: str = ""                  # MERCHANT | DISTRIBUTOR
    entity_name: str = ""
    uen: str = ""
    licence_no: str = ""
    ssic: str = ""
    ssic_desc: str = ""
    archetype: str = ""
    precinct: str = ""
    postal: str = ""
    address: str = ""
    lat: float = 0.0
    lon: float = 0.0
    reference_date: str = ""
    days_since: int = -1
    hygiene_grade: str = ""
    halal: str = ""
    ambient_gate: str = ""
    fit_score: int = 0
    precinct_score: int = 0
    maturity_score: int = 0
    corroboration: int = 1
    signal_score: float = 0.0
    trigger: str = ""
    next_action: str = ""

    outlets: int = 1

    def finalise(self, warm: bool = False) -> "Signal":
        if self.icp == "DISTRIBUTOR":
            if self.ambient_gate == "FAIL":
                self.signal_score = 0.0
                self.trigger = "EXCLUDE - cold chain"
                self.next_action = ("Anti-ICP. Chilled, frozen, fresh or regulated. "
                                    "Not viable for a delivered Drop box.")
            else:
                self.signal_score = round(float(self.fit_score), 2)
                self.trigger = "ENRICH - distributor"
                self.next_action = ("Manual enrichment: confirm retail-format ambient range, "
                                    "festive exposure, ESG machinery, principal restrictions.")
            return self

        # Outlet count is the expansion signal. Derived from how many times the
        # same trading name appears across different postal codes in the register.
        expansion = 5 if self.outlets >= 10 else (3 if self.outlets >= 3 else 1)
        warm_pts = 5 if warm else 1
        base = (self.fit_score * W_SSIC + self.precinct_score * W_PRECINCT
                + self.maturity_score * W_MATURITY + expansion * W_EXPANSION
                + warm_pts * W_WARM)
        bonus = min((self.corroboration - 1) * CORROBORATION_BONUS, MAX_CORROBORATION)
        self.signal_score = round(base + bonus, 2)

        if self.fit_score <= 1:
            self.trigger, self.next_action = "EXCLUDE", "Suppress permanently."
        elif warm:
            self.trigger = "NEIGHBOUR"
            self.next_action = "Warm approach citing the nearby partner's clearance rate."
        elif 0 <= self.days_since < 60:
            self.trigger = "NURTURE 90"
            self.next_action = f"Hold. Contact at day 90, which is {90 - self.days_since} days away."
        elif self.signal_score >= 4.0:
            self.trigger = "HOT - same week"
            self.next_action = "Visit at close of service within 5 working days."
        elif self.signal_score >= 3.4:
            self.trigger = "WARM - 14 day"
            self.next_action = "Add to outreach cadence, then visit."
        else:
            self.trigger, self.next_action = "NURTURE 90", "Hold and recheck next cycle."
        return self


# ================================================================ scoring helpers
def maturity_score(days: int) -> int:
    """Peaks at 90-180 days then decays. The one non-monotonic factor.

    A 14-day-old business has no surplus pattern to discuss. A 3-year-old one
    has already budgeted for the waste. Sorting newest-first, which is what a
    naive scraper does, systematically targets the worst window.
    """
    if days < 0:
        return 1
    if 90 <= days <= 180:
        return 5
    if 60 <= days < 90 or 180 < days <= 365:
        return 3
    if 30 <= days < 60:
        return 2
    return 1


def match_precinct(postcode: str, address: str = "") -> tuple[str, int]:
    pc = re.sub(r"\D", "", postcode or "")
    if len(pc) >= 2:
        for name, score, prefixes in PRECINCTS:
            if pc[:2] in prefixes:
                return name, score
    hay = (address or "").lower()
    for name, score, _ in PRECINCTS:
        token = name.split(" ")[0].split("/")[0].strip().lower()
        if token and token in hay:
            return name, score
    return "Unmapped", 1


def postal_from_address(addr: str) -> str:
    """SG postal codes are 6 digits, conventionally at the end of an address."""
    m = re.findall(r"\b(\d{6})\b", addr or "")
    return m[-1] if m else ""


def haversine_m(lat1: float, lon1: float, lat2: float, lon2: float) -> float:
    if not all((lat1, lon1, lat2, lon2)):
        return float("inf")
    r = 6371000.0
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dp, dl = math.radians(lat2 - lat1), math.radians(lon2 - lon1)
    a = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * r * math.asin(math.sqrt(a))


def days_between(iso: str, today: date) -> int:
    for fmt in ("%Y-%m-%d", "%d/%m/%Y", "%Y/%m/%d", "%d-%m-%Y", "%d %b %Y"):
        try:
            return (today - datetime.strptime(str(iso)[:11].strip(), fmt).date()).days
        except (ValueError, TypeError):
            continue
    return -1


def classify_ssic(code: str, desc: str) -> tuple[str, dict[str, Any]] | tuple[None, None]:
    code, d = (code or "").strip(), (desc or "").lower()
    if code in MERCHANT_SSIC:
        s, arch, _ = MERCHANT_SSIC[code]
        return "MERCHANT", {"score": s, "archetype": arch}
    if code in DISTRIBUTOR_SSIC:
        amb, s, arch, _ = DISTRIBUTOR_SSIC[code]
        return "DISTRIBUTOR", {"ambient": amb, "score": s, "archetype": arch}
    if code.startswith(COLD_PREFIXES):
        return "DISTRIBUTOR", {"ambient": False, "score": 0,
                               "archetype": "Meat or fish processing (COLD CHAIN, gate fails)"}
    if code.startswith("10"):
        amb, s, arch, _ = DISTRIBUTOR_SSIC["10"]
        return "DISTRIBUTOR", {"ambient": amb, "score": s, "archetype": arch}
    for _, (s, arch, kws) in MERCHANT_SSIC.items():
        if any(k in d for k in kws):
            return "MERCHANT", {"score": s, "archetype": arch}
    for _, (amb, s, arch, kws) in DISTRIBUTOR_SSIC.items():
        if any(k in d for k in kws):
            return "DISTRIBUTOR", {"ambient": amb, "score": s, "archetype": arch}
    return None, None


def norm_key(name: str, postal: str = "") -> str:
    """Key for matching the same business across registers.

    Strips entity suffixes and punctuation, because ACRA writes
    'EXAMPLE BAKERY PTE. LTD.' where MUIS writes 'Example Bakery'.
    """
    n = (name or "").upper()
    n = re.sub(r"\b(PTE\.?|LTD\.?|LLP|LIMITED|PRIVATE|CO\.?|COMPANY|INC\.?|SDN\.?|BHD\.?)\b", " ", n)
    n = re.sub(r"[^A-Z0-9 ]", " ", n)
    n = re.sub(r"\s+", " ", n).strip()
    pc = re.sub(r"\D", "", postal or "")
    return f"{n}|{pc[:6]}" if pc else n


# ================================================================ fetch
# data.gov.sg rate-limits hard, and far harder for anonymous callers. A free
# account key raises the limit. Set it as an environment variable, never in code:
#   Windows:  setx DATAGOVSG_API_KEY "your-key"   (then open a new PowerShell)
#   Mac:      export DATAGOVSG_API_KEY="your-key"
API_KEY_ENV = "DATAGOVSG_API_KEY"
MAX_RETRIES = 6
MIN_PAGE = 250
DEFAULT_PAGE = 5000
_sleep = time.sleep   # swapped out in tests


DGS_DOWNLOAD = "https://api-open.data.gov.sg/v1/public/api/datasets"
# data.gov.sg allows 5 requests a minute without a key, so space calls ~13s apart.
# With a key the limit is higher and the spacing drops to 1.5s.
_last_call = [0.0]


def _throttle(url: str) -> None:
    if "data.gov.sg" not in url:
        return
    interval = 1.5 if os.environ.get(API_KEY_ENV, "").strip() else 13.0
    wait = _last_call[0] + interval - time.monotonic()
    if wait > 0:
        _sleep(wait)
    _last_call[0] = time.monotonic()


def _headers() -> dict:
    h = {"User-Agent": "yindii-radar/3.2"}
    key = os.environ.get(API_KEY_ENV, "").strip()
    if key:
        h["x-api-key"] = key   # header name confirmed in data.gov.sg's API key guide
    return h


def _get(url: str, timeout: int = 60) -> Any:
    _throttle(url)
    req = urllib.request.Request(url, headers=_headers())
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return json.loads(r.read().decode("utf-8"))


def _get_text(url: str, timeout: int = 300) -> str:
    """Fetch a file from the signed download link. Not a data.gov.sg API call."""
    req = urllib.request.Request(url, headers={"User-Agent": "yindii-radar/3.2"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read().decode("utf-8-sig", errors="replace")


def dgs_download(dataset_id: str, max_polls: int = 20) -> list[dict] | None:
    """Download a whole dataset as one file via data.gov.sg's download API.

    Two or three API calls per dataset instead of dozens of paged requests,
    which matters under the 5-requests-a-minute anonymous quota.
    Returns None if the API is unavailable, so the caller can fall back.
    """
    base = f"{DGS_DOWNLOAD}/{dataset_id}"
    try:
        _get_retry(f"{base}/initiate-download")
    except urllib.error.HTTPError as exc:
        # Non-CSV datasets (GeoJSON, KML) skip initiate and go straight to poll.
        if exc.code not in (400, 404):
            print(f"    ! initiate-download failed: {exc}", file=sys.stderr)
            return None
    except Exception as exc:  # noqa: BLE001
        print(f"    ! initiate-download failed: {exc}", file=sys.stderr)
        return None

    link = ""
    for n in range(max_polls):
        try:
            resp = _get_retry(f"{base}/poll-download")
        except Exception as exc:  # noqa: BLE001
            print(f"    ! poll-download failed: {exc}", file=sys.stderr)
            return None
        link = (resp.get("data") or {}).get("url") or ""
        if link:
            break
        status = (resp.get("data") or {}).get("status", "preparing")
        print(f"    ... file not ready yet ({status}), checking again", file=sys.stderr)
    if not link:
        print("    ! download link never became ready", file=sys.stderr)
        return None

    try:
        text = _get_text(link)
    except Exception as exc:  # noqa: BLE001
        print(f"    ! file download failed: {exc}", file=sys.stderr)
        return None
    stripped = text.lstrip()
    if stripped.startswith("{"):
        try:
            gj = json.loads(stripped)
            return [dict(f.get("properties") or {}) for f in gj.get("features", [])]
        except json.JSONDecodeError:
            return None
    return list(csv.DictReader(io.StringIO(text)))


_shown_columns: set[str] = set()


def show_columns(label: str, recs: list[dict]) -> None:
    """Print the column names once per source, so a renamed column is easy to spot."""
    if recs and label not in _shown_columns:
        _shown_columns.add(label)
        cols = ", ".join(list(recs[0].keys())[:20])
        print(f"    columns ({label}): {cols}", file=sys.stderr)


def dgs_rows(dataset_id: str, limit: int) -> list[dict]:
    """Prefer the whole-file download. Fall back to paged datastore_search."""
    rows = dgs_download(dataset_id)
    if rows is not None:
        return rows
    print("    ... falling back to paged requests (slower)", file=sys.stderr)
    return dgs_fetch(dataset_id, limit=limit)


def _get_retry(url: str) -> Any:
    """GET with polite backoff on rate limits (HTTP 429) and brief server errors.

    Anything else, including 413, is raised so the caller can react to it.
    """
    for attempt in range(MAX_RETRIES + 1):
        try:
            return _get(url)
        except urllib.error.HTTPError as exc:
            if exc.code in (429, 502, 503, 504) and attempt < MAX_RETRIES:
                retry_after = exc.headers.get("Retry-After") if exc.headers else None
                wait = int(retry_after) if (retry_after or "").isdigit() else min(60, 5 * 2 ** attempt)
                print(f"    ... rate limited ({exc.code}), waiting {wait}s then retrying", file=sys.stderr)
                _sleep(wait)
                continue
            raise
    raise RuntimeError("retries exhausted")


def dgs_probe(resource_id: str) -> str:
    try:
        p = _get_retry(f"{DGS_API}?{urllib.parse.urlencode({'resource_id': resource_id, 'limit': 1})}")
        return str(p.get("result", {}).get("total", 0))
    except Exception:  # noqa: BLE001
        return ""


def dgs_fetch(resource_id: str, limit: int = DEFAULT_PAGE, pause: float = 1.0) -> list[dict]:
    """Page through a dataset, shrinking the page size if the server says it is too big.

    ACRA rows are wide (53 columns), so a page that works for a narrow dataset can
    exceed data.gov.sg's response-size cap and come back as HTTP 413. On a 413 the
    page size halves and the same offset is retried.
    """
    records, offset, page = [], 0, max(limit, MIN_PAGE)
    while True:
        url = f"{DGS_API}?{urllib.parse.urlencode({'resource_id': resource_id, 'limit': page, 'offset': offset})}"
        try:
            payload = _get_retry(url)
        except urllib.error.HTTPError as exc:
            if exc.code == 413 and page > MIN_PAGE:
                page = max(MIN_PAGE, page // 2)
                print(f"    ... page too large, retrying with {page} rows per request", file=sys.stderr)
                continue
            print(f"    ! fetch failed at offset {offset}: {exc}", file=sys.stderr)
            break
        except Exception as exc:  # noqa: BLE001
            print(f"    ! fetch failed at offset {offset}: {exc}", file=sys.stderr)
            break
        batch = payload.get("result", {}).get("records", [])
        if not batch:
            break
        records.extend(batch)
        offset += len(batch)
        if offset >= payload.get("result", {}).get("total", 0):
            break
        _sleep(pause)
    return records


# ================================================================ parsers
_KV_RE = re.compile(r"<th>(.*?)</th>\s*<td>(.*?)</td>", re.I | re.S)


def parse_kml_description(desc: str) -> dict[str, str]:
    """SFA geospatial sets bury attributes in an HTML table inside Description.

    Real shape, verified from the published response:
      <center><table><tr><th colspan='2'...><em>Attributes</em></th></tr>
      <tr bgcolor="#E3E3F3"> <th>LIC_NAME</th> <td>OMU PTE. LTD.</td> </tr>...
    """
    out: dict[str, str] = {}
    for k, v in _KV_RE.findall(desc or ""):
        key = re.sub(r"<[^>]+>", "", k).strip().upper()
        val = html.unescape(re.sub(r"<[^>]+>", "", v)).strip()
        if key and key != "ATTRIBUTES":
            out[key] = val
    return out


def pick(rec: dict, *names: str, default: str = "") -> str:
    lowered = {str(k).lower().replace(" ", "_"): v for k, v in rec.items()}
    for n in names:
        v = lowered.get(n.lower().replace(" ", "_"))
        if v not in (None, "", "na", "NA", "-"):
            return str(v)
    return default


def muis_cert_year(cert_no: str) -> int:
    """Best-effort year from a MUIS certificate number.

    Observed live: 'EEHK20250000456' (4-digit year) and 'EEHK25120000014'
    (looks like YYMM). The format is inconsistent, so this is a SOFT signal
    only and returns 0 when it cannot be read confidently.
    [CONFIRM] the numbering scheme with MUIS before relying on it.
    """
    digits = re.sub(r"\D", "", cert_no or "")
    if len(digits) >= 4:
        y = int(digits[:4])
        if 2000 <= y <= 2100:
            return y
        yy = int(digits[:2])
        if 0 <= yy <= 99:
            return 2000 + yy
    return 0


# ================================================================ source adapters
def source_acra(today: date, args) -> list[Signal]:
    """The ONLY source that sees distributors. Also the only one with SSIC codes."""
    resources = dict(ACRA_RESOURCES)
    try:
        meta = _get_retry(DGS_COLLECTION_META)
        ids = meta.get("data", {}).get("collectionMetadata", {}).get("childDatasets", []) or []
        for i, ds in enumerate(ids):
            resources.setdefault(chr(ord("A") + i) if i < 26 else "OTHERS", ds)
    except Exception as exc:  # noqa: BLE001
        print(f"    ! ACRA collection metadata unavailable ({exc}). Using {len(resources)} known ids.",
              file=sys.stderr)

    if args.letters:
        want = {l.upper() for l in args.letters}
        resources = {k: v for k, v in resources.items() if k in want}

    out: list[Signal] = []
    failures = 0
    for letter, rid in sorted(resources.items()):
        recs = dgs_rows(rid, args.limit)
        if not recs:
            failures += 1
        print(f"    ACRA {letter}: {len(recs):,} rows")
        show_columns("ACRA", recs)
        for rec in recs:
            status = pick(rec, "uen_status_desc", "entity_status_description", "entity_status").lower()
            if status and not any(s in status for s in LIVE_STATUSES):
                continue
            code = pick(rec, "primary_ssic_code")
            desc = pick(rec, "primary_ssic_description", "primary_ssic_desc", "primary_ssic_code_description")
            icp, info = classify_ssic(code, desc)
            if icp is None:
                continue
            reg = pick(rec, "registration_incorporation_date", "uen_issue_date", "registration_date",
                       "incorporation_date")
            days = days_between(reg, today)
            postal = pick(rec, "reg_postal_code", "postal_code")
            addr = " ".join(filter(None, [pick(rec, "block", "reg_block_house_no"),
                                          pick(rec, "street_name", "reg_street_name"),
                                          pick(rec, "building_name", "reg_building_name")]))
            s = Signal(detected=today.isoformat(), sources="ACRA", icp=icp,
                       entity_name=pick(rec, "entity_name", default="UNKNOWN"),
                       uen=pick(rec, "uen"), ssic=code, ssic_desc=desc,
                       archetype=info["archetype"], postal=postal, address=addr,
                       reference_date=reg[:10], days_since=days,
                       fit_score=info["score"])
            if icp == "MERCHANT":
                if s.fit_score < MIN_MERCHANT_SCORE:
                    continue
                s.precinct, s.precinct_score = match_precinct(postal, addr)
                s.maturity_score = maturity_score(days)
            else:
                s.ambient_gate = "PASS" if info["ambient"] else "FAIL"
                s.precinct = "n/a - Drop is delivered"
            out.append(s)
    if resources and failures == len(resources):
        raise ConnectionError(f"All {failures} ACRA datasets failed to download")
    return out


def source_sfa(today: date, args) -> list[Signal]:
    """SFA eating establishments. The only source with real COORDINATES."""
    recs = dgs_rows(SFA_EATING_ESTABLISHMENTS, args.limit)
    show_columns("SFA", recs)
    if not recs:
        print("    ! SFA returned no rows", file=sys.stderr)
        return []
    print(f"    SFA: {len(recs):,} rows")
    return [s for s in (_sfa_one(r, today) for r in recs) if s]


def _sfa_one(rec: dict, today: date) -> Signal | None:
    attrs = parse_kml_description(str(rec.get("Description") or rec.get("description") or ""))
    if not attrs:
        attrs = {str(k).upper(): str(v) for k, v in rec.items()}
    name = attrs.get("LIC_NAME") or attrs.get("NAME") or ""
    if not name:
        return None
    addr = attrs.get("ADDRESS") or attrs.get("BLK_HOUSE") or ""
    postal = attrs.get("POSTALCODE") or attrs.get("POSTAL_CODE") or postal_from_address(addr)
    lat = float(attrs.get("LATITUDE") or rec.get("lat") or 0) or 0.0
    lon = float(attrs.get("LONGITUDE") or rec.get("lon") or 0) or 0.0
    precinct, pscore = match_precinct(postal, addr)
    s = Signal(detected=today.isoformat(), sources="SFA", icp="MERCHANT",
               entity_name=name, licence_no=attrs.get("LIC_NO", ""),
               archetype="Licensed eating establishment", precinct=precinct,
               postal=postal, address=addr, lat=lat, lon=lon,
               fit_score=4, precinct_score=pscore, maturity_score=1)
    return s


def source_nea(today: date, args) -> list[Signal]:
    """NEA licensed eating establishments, with hygiene grade and demerit history."""
    try:
        recs = dgs_rows(NEA_EATING_ESTABLISHMENTS, args.limit)
    except Exception as exc:  # noqa: BLE001
        print(f"    ! NEA fetch failed: {exc}", file=sys.stderr)
        return []
    print(f"    NEA: {len(recs):,} rows")
    show_columns("NEA", recs)
    out = []
    for rec in recs:
        name = pick(rec, "licensee_name", "company_name", "name", "premise_name")
        if not name:
            continue
        addr = pick(rec, "premise_address", "address", "street_name")
        postal = pick(rec, "postal_code", "postalcode") or postal_from_address(addr)
        grade = pick(rec, "grade", "hygiene_grade").upper()
        demerit = pick(rec, "demerit_points", "demerit")
        suspended = pick(rec, "suspension_history", "suspended")
        precinct, pscore = match_precinct(postal, addr)

        # A suspended or D-graded business is under regulatory stress.
        # Approaching one is a poor use of time and a reputational risk.
        fit = 4
        if grade == "D" or (suspended and suspended.lower() not in ("", "nil", "no", "none")):
            fit = 1
        elif grade == "C":
            fit = 3
        s = Signal(detected=today.isoformat(), sources="NEA", icp="MERCHANT",
                   entity_name=name, licence_no=pick(rec, "licence_number", "licence_no"),
                   archetype="Licensed eating establishment", precinct=precinct,
                   postal=postal, address=addr, hygiene_grade=grade,
                   fit_score=fit, precinct_score=pscore, maturity_score=1)
        if fit == 1:
            s.next_action = f"Regulatory stress (grade {grade}, demerits {demerit}). Deprioritise."
        out.append(s)
    return out


def source_muis(today: date, args) -> list[Signal]:
    """MUIS halal register. TESTED LIVE. Premises addresses plus a growth signal.

    Unofficial community mirror. Official register: halal.muis.gov.sg
    """
    try:
        recs = _get(MUIS_MIRROR_JSON, timeout=60)
    except Exception as exc:  # noqa: BLE001
        print(f"    ! MUIS fetch failed: {exc}", file=sys.stderr)
        print(f"    ! Official register for manual check: {MUIS_OFFICIAL}", file=sys.stderr)
        return []
    if not isinstance(recs, list):
        print("    ! MUIS mirror returned an unexpected shape.", file=sys.stderr)
        return []
    print(f"    MUIS: {len(recs):,} rows")

    out = []
    for rec in recs:
        mtype = str(rec.get("type") or "")
        fit, archetype = MUIS_TYPE_MAP.get(mtype, (1, f"Unmapped MUIS type: {mtype}"))
        if fit < MIN_MERCHANT_SCORE:
            continue
        addr = str(rec.get("address") or "")
        postal = str(rec.get("postal") or "") or postal_from_address(addr)
        precinct, pscore = match_precinct(postal, addr)
        cert_no = str(rec.get("number") or "")
        year = muis_cert_year(cert_no)

        # Certification year is NOT business age. A 2023 certificate can belong to
        # a 20-year-old bakery. Scoring it as maturity buried every MUIS record.
        # MUIS is a register SNAPSHOT, not a new-business feed: its real signal is
        # the month-on-month delta, which the state file already gives us.
        s = Signal(detected=today.isoformat(), sources="MUIS", icp="MERCHANT",
                   entity_name=str(rec.get("name") or ""), licence_no=cert_no,
                   archetype=archetype, precinct=precinct, postal=postal, address=addr,
                   halal=f"MUIS {rec.get('scheme') or ''}".strip(),
                   reference_date=f"cert {year}" if year else "",
                   days_since=-1, fit_score=fit, precinct_score=pscore,
                   maturity_score=3)
        out.append(s)
    return out


SOURCES: dict[str, Callable[[date, Any], list[Signal]]] = {
    "acra": source_acra, "sfa": source_sfa, "nea": source_nea, "muis": source_muis,
}


# ================================================================ merge
def merge(signals: list[Signal]) -> list[Signal]:
    """Collapse the same business seen in several registers into one row.

    Corroboration matters: a company in ACRA AND a licence register is
    materially more real than one with only a registration.
    """
    buckets: dict[str, list[Signal]] = {}
    for s in signals:
        buckets.setdefault(norm_key(s.entity_name, s.postal), []).append(s)

    merged: list[Signal] = []
    for group in buckets.values():
        if len(group) == 1:
            merged.append(group[0])
            continue
        # Prefer the richest record as the base: distributors first (only ACRA
        # sees them), then whichever has coordinates, then highest fit.
        base = sorted(group, key=lambda s: (s.icp != "DISTRIBUTOR", not s.lat, -s.fit_score))[0]
        seen_sources = sorted({s.sources for s in group})
        base.sources = "|".join(seen_sources)
        base.corroboration = len(seen_sources)
        for s in group:
            base.uen = base.uen or s.uen
            base.ssic = base.ssic or s.ssic
            base.ssic_desc = base.ssic_desc or s.ssic_desc
            base.licence_no = base.licence_no or s.licence_no
            base.hygiene_grade = base.hygiene_grade or s.hygiene_grade
            base.halal = base.halal or s.halal
            base.address = base.address or s.address
            base.postal = base.postal or s.postal
            base.lat = base.lat or s.lat
            base.lon = base.lon or s.lon
            if s.days_since >= 0 and base.days_since < 0:
                base.days_since = s.days_since
                base.reference_date = s.reference_date
            base.fit_score = max(base.fit_score, s.fit_score)
            base.precinct_score = max(base.precinct_score, s.precinct_score)
        # A licence register carries the real premises, so prefer its precinct.
        for s in group:
            if s.sources in ("SFA", "NEA", "MUIS") and s.precinct != "Unmapped":
                base.precinct, base.precinct_score = s.precinct, s.precinct_score
                break
        base.maturity_score = maturity_score(base.days_since)
        merged.append(base)
    return merged


def apply_neighbours(signals: list[Signal], winners: list[dict]) -> int:
    """Mark prospects near a high-clearing Yindii partner.

    Uses real distance when coordinates exist (SFA), and falls back to precinct
    matching when they do not. This is the cheapest warm lead in the business:
    demand at that address is already proven.
    """
    hits = 0
    for s in signals:
        if s.trigger.startswith("EXCLUDE"):
            continue
        warm = False
        for w in winners:
            wlat, wlon = float(w.get("lat", 0) or 0), float(w.get("lon", 0) or 0)
            if s.lat and wlat and haversine_m(s.lat, s.lon, wlat, wlon) <= NEIGHBOUR_RADIUS_M:
                warm = True
            elif w.get("precinct") and w["precinct"] == s.precinct:
                warm = True
            if warm:
                s.finalise(warm=True)
                hits += 1
                break
    signals.sort(key=lambda x: (-x.signal_score, x.entity_name))
    return hits


def within_window(signals: list[Signal], days: int) -> list[Signal]:
    """Keep businesses registered inside the window.

    Only ACRA carries a registration date. Licence-register rows have no age
    (days_since = -1), so they are kept and judged on the month-on-month delta.
    Without this filter, the first ACRA run returns every live food company
    ever registered in Singapore rather than new ones.
    """
    if not days:
        return signals
    return [s for s in signals if s.days_since < 0 or s.days_since <= days]


def festive_priority(today: date) -> list[str]:
    out = []
    for label, month, sev, tag in FESTIVE_WINDOWS:
        if month is None:
            continue
        if today.month == month:
            out.append(f"{label} (severity {sev}) CONTACT WINDOW OPEN NOW")
        elif today.month == month - 1:
            out.append(f"{label} (severity {sev}) opens next month")
    return out


# ================================================================ io
COLUMNS = ["detected", "sources", "corroboration", "icp", "entity_name", "uen", "licence_no",
           "ssic", "ssic_desc", "archetype", "precinct", "postal", "address", "lat", "lon",
           "outlets", "reference_date", "days_since", "hygiene_grade", "halal", "ambient_gate",
           "fit_score", "precinct_score", "maturity_score", "signal_score", "trigger", "next_action"]


def write_csv(rows: list[Signal], path: Path) -> None:
    with path.open("w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=COLUMNS, extrasaction="ignore")
        w.writeheader()
        for s in rows:
            w.writerow(asdict(s))


def load_state() -> dict:
    if STATE_FILE.exists():
        try:
            return json.loads(STATE_FILE.read_text())
        except json.JSONDecodeError:
            print("  ! state file corrupt, starting fresh", file=sys.stderr)
    return {"seen": [], "last_run": None}


def save_state(state: dict) -> None:
    try:
        STATE_FILE.write_text(json.dumps(state, indent=2))
    except OSError as exc:
        print(f"  ! could not write state ({exc}). Next run will re-alert.", file=sys.stderr)


def format_alert(new: list[Signal], today: date, source_status: dict[str, str]) -> str:
    baseline = " (BASELINE, first run: this is the whole register, not new businesses)" if len(new) > 500 else ""
    lines = [f"*Yindii radar* {today.isoformat()}, {len(new)} new signals{baseline}"]
    lines.append("  sources: " + ", ".join(f"{k}={v}" for k, v in source_status.items()))
    fest = festive_priority(today)
    if fest:
        lines += ["", "FESTIVE WINDOW:"] + [f"  {f}" for f in fest]
    groups = [("HOT, visit this week", [s for s in new if s.trigger.startswith("HOT")]),
              ("NEIGHBOUR, warm", [s for s in new if s.trigger == "NEIGHBOUR"]),
              ("WARM, 14 day", [s for s in new if s.trigger.startswith("WARM")]),
              ("DISTRIBUTOR, enrich", [s for s in new if s.trigger.startswith("ENRICH")])]
    for label, g in groups:
        if not g:
            continue
        lines += ["", f"{label} ({len(g)})"]
        for s in g[:10]:
            extra = s.precinct if s.icp == "MERCHANT" else s.archetype
            corr = f" [{s.sources}]" if s.corroboration > 1 else ""
            lines.append(f"  {s.signal_score:>5}  {s.entity_name[:40]:<40} {extra}{corr}")
        if len(g) > 10:
            lines.append(f"  ... and {len(g) - 10} more")
    return "\n".join(lines)


def post_webhook(url: str, text: str) -> bool:
    try:
        data = json.dumps({"text": text}).encode()
        req = urllib.request.Request(url, data=data, headers={"Content-Type": "application/json"})
        urllib.request.urlopen(req, timeout=15)
        return True
    except Exception as exc:  # noqa: BLE001
        print(f"  ! webhook failed: {exc}", file=sys.stderr)
        return False


# ================================================================ run
def run_once(args) -> int:
    today = date.today()
    state = load_state()
    seen = set(state.get("seen", []))

    wanted = [s.lower() for s in (args.sources or list(SOURCES))]
    unknown = [s for s in wanted if s not in SOURCES]
    if unknown:
        print(f"Unknown source(s): {', '.join(unknown)}. Valid: {', '.join(SOURCES)}", file=sys.stderr)
        return 2

    print(f"{today} scanning: {', '.join(wanted)}")
    raw: list[Signal] = []
    status: dict[str, str] = {}
    for name in wanted:
        print(f"  {name.upper()} ...")
        try:
            got = SOURCES[name](today, args)
            raw.extend(got)
            status[name] = f"{len(got):,}"
        except ConnectionError as exc:
            status[name] = "FAILED"
            print(f"    ! {exc}", file=sys.stderr)
        except Exception as exc:  # noqa: BLE001
            status[name] = "FAILED"
            print(f"    ! {name} raised {type(exc).__name__}: {exc}", file=sys.stderr)

    if all(v == "FAILED" for v in status.values()):
        print("\nCONNECTION FAILED. Every source failed. Nothing written.", file=sys.stderr)
        print("  Check internet, VPN and firewall. data.gov.sg must be reachable", file=sys.stderr)
        print("  for acra, sfa and nea. Try: --sources muis  to test the pipeline.", file=sys.stderr)
        return 3

    merged = merge(raw)

    # Chain detection: the same trading name at several postal codes is a chain,
    # and chain conversion is the cheapest growth in the model.
    name_counts: dict[str, int] = {}
    for s in merged:
        name_counts[norm_key(s.entity_name)] = name_counts.get(norm_key(s.entity_name), 0) + 1
    for s in merged:
        s.outlets = name_counts.get(norm_key(s.entity_name), 1)

    fresh = [s.finalise() for s in merged if norm_key(s.entity_name, s.postal) not in seen]
    fresh = [s for s in fresh if not s.trigger.startswith("EXCLUDE")]
    fresh = within_window(fresh, args.days)

    if args.neighbours:
        try:
            winners = json.loads(Path(args.neighbours).read_text())
            if isinstance(winners, dict):
                winners = [{"precinct": k} for k in winners]
            print(f"  neighbour pass promoted {apply_neighbours(fresh, winners)} prospects")
        except Exception as exc:  # noqa: BLE001
            print(f"  ! neighbour file unusable ({exc}). Continuing without it.", file=sys.stderr)

    fresh.sort(key=lambda s: (-s.signal_score, s.entity_name))
    write_csv(fresh, Path(args.out))

    # Persist state BEFORE printing. If the output is piped to head or less and
    # the reader quits early, the process dies on a broken pipe. Saving first
    # means an interrupted run still remembers what it saw.
    for s in merged:
        seen.add(norm_key(s.entity_name, s.postal))
    state["seen"] = sorted(seen)
    state["last_run"] = today.isoformat()
    save_state(state)

    alert = format_alert(fresh, today, status)
    if args.webhook and fresh:
        post_webhook(args.webhook, alert)
    try:
        print()
        print(alert)
        print(f"\nWrote {args.out}. State tracks {len(seen):,} businesses.")
    except BrokenPipeError:
        pass
    return 0


# ================================================================ selftest
SFA_FIXTURE = {"Description": (
    "<center><table><tr><th colspan='2' align='center'><em>Attributes</em></th></tr>"
    "<tr bgcolor=\"#E3E3F3\"> <th>LIC_NAME</th> <td>EXAMPLE BAKERY PTE. LTD.</td> </tr>"
    "<tr> <th>LIC_NO</th> <td>NE12345X</td> </tr>"
    "<tr> <th>ADDRESS</th> <td>9 BISHAN PLACE #01-01 JUNCTION 8 570123</td> </tr>"
    "<tr> <th>POSTALCODE</th> <td>570123</td> </tr>"
    "<tr> <th>LATITUDE</th> <td>1.3509</td> </tr>"
    "<tr> <th>LONGITUDE</th> <td>103.8487</td> </tr></table></center>")}

MUIS_FIXTURE = [
    {"name": "EXAMPLE HALAL BAKERY", "address": "9 BISHAN PLACE #01-02 570123",
     "type": "Snack Bar / Bakery", "number": "EEHK20250000456",
     "scheme": "Eating Establishment", "id": "x1", "postal": "570123"},
    {"name": "EXAMPLE HAWKER STALL", "address": "1 SOME ROAD 123456",
     "type": "Hawker", "number": "EEHK20250000999",
     "scheme": "Eating Establishment", "id": "x2", "postal": "123456"},
    {"name": "EXAMPLE CENTRAL KITCHEN", "address": "5 TUAS AVE 630000",
     "type": "Central Kitchen", "number": "FPHK20240000111",
     "scheme": "Food Preparation Area", "id": "x3", "postal": "630000"},
]

NEA_FIXTURE = [
    {"licensee_name": "EXAMPLE BAKERY PTE. LTD.", "premise_address": "9 BISHAN PLACE",
     "postal_code": "570123", "grade": "A", "licence_number": "NE12345X"},
    {"licensee_name": "EXAMPLE DIRTY CAFE PTE. LTD.", "premise_address": "2 SOME ROAD",
     "postal_code": "238888", "grade": "D", "demerit_points": "18",
     "suspension_history": "Suspended 14 days", "licence_number": "NE99999Z"},
]


def selftest() -> int:
    today = date(2026, 9, 17)
    fails: list[str] = []

    def chk(label, got, want):
        ok = got == want
        print(f"  {'PASS' if ok else 'FAIL'}  {label}: got {got!r}, want {want!r}")
        if not ok:
            fails.append(label)

    print("SFA KML description parser")
    a = parse_kml_description(SFA_FIXTURE["Description"])
    chk("extracts LIC_NAME", a.get("LIC_NAME"), "EXAMPLE BAKERY PTE. LTD.")
    chk("extracts postal", a.get("POSTALCODE"), "570123")
    chk("extracts latitude", a.get("LATITUDE"), "1.3509")
    chk("drops the Attributes header", "ATTRIBUTES" in a, False)
    s = _sfa_one(SFA_FIXTURE, today)
    chk("SFA maps to precinct", s.precinct, "Bishan (Junction 8)")
    chk("SFA carries coordinates", (s.lat, s.lon), (1.3509, 103.8487))

    print("\nMUIS adapter")
    muis = []
    for rec in MUIS_FIXTURE:
        fit, arch = MUIS_TYPE_MAP.get(rec["type"], (1, "?"))
        if fit < MIN_MERCHANT_SCORE:
            continue
        muis.append((rec["name"], fit, arch))
    names = [m[0] for m in muis]
    chk("bakery kept", "EXAMPLE HALAL BAKERY" in names, True)
    chk("central kitchen kept", "EXAMPLE CENTRAL KITCHEN" in names, True)
    chk("hawker dropped (fit 1, no packaging)", "EXAMPLE HAWKER STALL" in names, False)
    chk("bakery scores 5", MUIS_TYPE_MAP["Snack Bar / Bakery"][0], 5)
    chk("cert year, 4-digit form", muis_cert_year("EEHK20250000456"), 2025)
    chk("cert year, YYMM form", muis_cert_year("EEHK25120000014"), 2512 if False else 2025)
    chk("cert year, unreadable", muis_cert_year("ABC"), 0)

    print("\nNEA hygiene and distress filter")
    nea = []
    for rec in NEA_FIXTURE:
        grade = rec.get("grade", "").upper()
        susp = rec.get("suspension_history", "")
        fit = 1 if (grade == "D" or susp) else (3 if grade == "C" else 4)
        nea.append((rec["licensee_name"], fit))
    chk("grade A scores 4", dict(nea)["EXAMPLE BAKERY PTE. LTD."], 4)
    chk("grade D + suspension scores 1", dict(nea)["EXAMPLE DIRTY CAFE PTE. LTD."], 1)

    print("\ncross-source name matching")
    chk("ACRA vs MUIS naming",
        norm_key("EXAMPLE BAKERY PTE. LTD.", "570123"),
        norm_key("Example Bakery", "570123"))
    chk("different postal does not match",
        norm_key("EXAMPLE BAKERY PTE. LTD.", "570123") ==
        norm_key("EXAMPLE BAKERY PTE. LTD.", "238888"), False)

    print("\nmerge and corroboration")
    grp = [
        Signal(sources="ACRA", icp="MERCHANT", entity_name="EXAMPLE BAKERY PTE. LTD.",
               uen="202612345A", ssic="47213", postal="570123", days_since=120,
               fit_score=5, precinct="Unmapped", precinct_score=1),
        Signal(sources="SFA", icp="MERCHANT", entity_name="Example Bakery",
               postal="570123", lat=1.3509, lon=103.8487, fit_score=4,
               precinct="Bishan (Junction 8)", precinct_score=4),
        Signal(sources="MUIS", icp="MERCHANT", entity_name="EXAMPLE BAKERY",
               postal="570123", halal="MUIS Eating Establishment", fit_score=5,
               precinct="Bishan (Junction 8)", precinct_score=4),
    ]
    m = merge(grp)
    chk("three registers collapse to one row", len(m), 1)
    chk("corroboration counted", m[0].corroboration, 3)
    chk("sources recorded", m[0].sources, "ACRA|MUIS|SFA")
    chk("keeps the UEN from ACRA", m[0].uen, "202612345A")
    chk("keeps coordinates from SFA", m[0].lat, 1.3509)
    chk("keeps halal from MUIS", m[0].halal, "MUIS Eating Establishment")
    chk("licence-register precinct overrides ACRA's", m[0].precinct, "Bishan (Junction 8)")
    m[0].finalise()
    # 5*.30 + 4*.25 + 5*.20 + 1*.15 + 1*.10 = 3.75, plus 2 extra sources capped at 0.50
    chk("corroboration bonus applied", m[0].signal_score, 4.25)
    chk("bonus lifts it to HOT", m[0].trigger, "HOT - same week")

    print("\ncorroboration bonus is capped")
    solo = Signal(sources="ACRA", icp="MERCHANT", entity_name="SOLO", postal="570123",
                  days_since=120, fit_score=5, precinct_score=4, maturity_score=5,
                  corroboration=1).finalise()
    four = Signal(sources="A|B|C|D", icp="MERCHANT", entity_name="FOUR", postal="570123",
                  days_since=120, fit_score=5, precinct_score=4, maturity_score=5,
                  corroboration=4).finalise()
    chk("single source has no bonus", solo.signal_score, 3.75)
    chk("four sources capped at +0.50", round(four.signal_score - solo.signal_score, 2), 0.50)

    print("\nchain detection from outlet count")
    one = Signal(icp="MERCHANT", entity_name="SOLO", fit_score=5, precinct_score=4,
                 maturity_score=5, outlets=1, days_since=120).finalise()
    six = Signal(icp="MERCHANT", entity_name="CHAIN6", fit_score=5, precinct_score=4,
                 maturity_score=5, outlets=6, days_since=120).finalise()
    big = Signal(icp="MERCHANT", entity_name="CHAIN20", fit_score=5, precinct_score=4,
                 maturity_score=5, outlets=20, days_since=120).finalise()
    chk("single outlet, expansion 1", one.signal_score, 3.75)
    chk("6 outlets scores higher", six.signal_score > one.signal_score, True)
    chk("6 outlets, expansion 3", round(six.signal_score - one.signal_score, 2), 0.30)
    chk("20 outlets, expansion 5", round(big.signal_score - one.signal_score, 2), 0.60)
    chk("chain reaches HOT", big.trigger, "HOT - same week")

    print("\nSSIC 2020 codes, as ACRA uses them")
    for code, want_icp, want_arch in (
            ("56112", "MERCHANT", "Cafe / Coffee Chain"),
            ("56111", "MERCHANT", "Hot-Meal QSR Chain"),
            ("56121", "MERCHANT", "Hot-Meal QSR Chain"),
            ("10712", "MERCHANT", "Premium Bakery Chain"),
            ("55101", "MERCHANT", "Hotel"),
            ("10711", "DISTRIBUTOR", "Biscuit manufacturer")):
        icp, info = classify_ssic(code, "")
        chk(f"{code} routes to {want_icp}", (icp, info["archetype"]), (want_icp, want_arch))
    for code in ("10750", "10800", "10109", "10200", "46302"):
        icp, info = classify_ssic(code, "")
        chk(f"{code} fails the ambient gate", info.get("ambient"), False)
    chk("old non-existent code 56102 no longer matches", classify_ssic("56102", "")[0], None)

    print("\nregistration-age window")
    young = Signal(entity_name="NEW", days_since=45)
    old_co = Signal(entity_name="OLD", days_since=4000)
    lic = Signal(entity_name="LICENCE ROW", days_since=-1)
    kept = [s.entity_name for s in within_window([young, old_co, lic], 365)]
    chk("new company kept", "NEW" in kept, True)
    chk("decade-old company dropped", "OLD" in kept, False)
    chk("licence row with no date kept", "LICENCE ROW" in kept, True)

    print("\ndistance, for neighbour detection")
    d = haversine_m(1.3509, 103.8487, 1.3509, 103.8505)
    chk("~200m apart is within radius", d <= 250, True)
    chk("missing coordinates return infinity", haversine_m(0, 0, 1.35, 103.8), float("inf"))

    print("\nmaturity curve stays non-monotonic")
    for dd, want in ((14, 1), (45, 2), (75, 3), (120, 5), (300, 3), (900, 1)):
        chk(f"day {dd}", maturity_score(dd), want)

    print("\ndistributor gate unchanged")
    dist = Signal(icp="DISTRIBUTOR", entity_name="COLD CO", ambient_gate="FAIL",
                  fit_score=5).finalise()
    chk("cold chain forced to zero", dist.signal_score, 0.0)
    chk("cold chain excluded", dist.trigger, "EXCLUDE - cold chain")

    print(f"\n{'ALL CHECKS PASSED' if not fails else f'{len(fails)} FAILED: ' + ', '.join(fails)}")
    return 0 if not fails else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--once", action="store_true")
    ap.add_argument("--daemon", action="store_true")
    ap.add_argument("--interval", type=int, default=21600)
    ap.add_argument("--sources", nargs="*", help="acra sfa nea muis. Default: all")
    ap.add_argument("--days", type=int, default=365)
    ap.add_argument("--letters", nargs="*", help="limit ACRA to these letters")
    ap.add_argument("--limit", type=int, default=DEFAULT_PAGE, help="rows per request; shrinks automatically on HTTP 413")
    ap.add_argument("--out", default="yindii_radar_new.csv")
    ap.add_argument("--neighbours", help='JSON: [{"precinct":"Bishan (Junction 8)"}] or with lat/lon')
    ap.add_argument("--webhook")
    ap.add_argument("--force", action="store_true", help="fetch ACRA datasets even if the refresh probe fails")
    args = ap.parse_args()

    if args.selftest:
        return selftest()
    if args.daemon:
        print(f"Radar running. Polling every {args.interval}s. Ctrl-C to stop.")
        try:
            while True:
                run_once(args)
                time.sleep(args.interval)
        except KeyboardInterrupt:
            print("\nStopped.")
            return 0
    return run_once(args)


if __name__ == "__main__":
    sys.exit(main()) 
