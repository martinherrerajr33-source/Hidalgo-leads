#!/usr/bin/env python3
"""
Hidalgo County, TX — Motivated Seller Lead Scraper
===================================================
Sources:
  1. County Clerk records portal (GovOS/Kofile "publicsearch.us"):
       https://hidalgo.tx.publicsearch.us/
     Scraped with async Playwright. The portal's frontend calls a JSON
     search API; we capture those XHR responses AND fall back to DOM
     scraping if the API shape changes.

  2. Hidalgo County Appraisal District (True Prodigy / hidalgoad.org):
     bulk parcel export ZIP containing a DBF. Parsed with `dbfread` to
     build an owner-name -> (situs address, mailing address) lookup.

Outputs:
  dashboard/records.json  and  data/records.json
  data/ghl_import.csv     (GoHighLevel-ready CSV)

Designed to run headless in GitHub Actions (ubuntu-22.04) daily.
Never crashes on a bad record — every record is wrapped defensively.
"""

import asyncio
import csv
import io
import json
import logging
import os
import re
import sys
import time
import zipfile
from datetime import datetime, timedelta, timezone
from pathlib import Path
from urllib.parse import quote, urljoin

import requests
from bs4 import BeautifulSoup

try:
    from dbfread import DBF
except ImportError:  # pragma: no cover
    DBF = None

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

CLERK_BASE = "https://hidalgo.tx.publicsearch.us"
LOOKBACK_DAYS = int(os.environ.get("LOOKBACK_DAYS", "7"))
MAX_PAGES_PER_TYPE = int(os.environ.get("MAX_PAGES_PER_TYPE", "20"))
PAGE_SIZE = 50
RETRIES = 3
RETRY_SLEEP = 5  # seconds, doubled each attempt

REPO_ROOT = Path(__file__).resolve().parent.parent
DASHBOARD_JSON = REPO_ROOT / "dashboard" / "records.json"
DATA_JSON = REPO_ROOT / "data" / "records.json"
GHL_CSV = REPO_ROOT / "data" / "ghl_import.csv"
PARCEL_CACHE_DIR = REPO_ROOT / "data" / "parcel_cache"

# Hidalgo CAD (True Prodigy) bulk data. The first working URL wins.
# Override with env var CAD_BULK_URL if HCAD renames the export file.
CAD_BULK_URL_OVERRIDE = os.environ.get("CAD_BULK_URL", "").strip()
CAD_DOWNLOAD_PAGES = [
    "https://hidalgo.prodigycad.com/data-downloads",
    "https://hidalgoad.org/data-downloads/",
    "https://hidalgoad.org/gis-data/",
    "https://esearch.hidalgoad.org/Downloads",
]
# Direct guesses tried before scraping the pages above:
CAD_DIRECT_GUESSES = [
    "https://hidalgo.prodigycad.com/downloads/appraisal_export.zip",
    "https://hidalgoad.org/wp-content/uploads/gis/parcels.zip",
]

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36")

# ---------------------------------------------------------------------------
# Lead-type taxonomy
# key = internal category code; "terms" are matched against the clerk portal's
# document-type strings (case-insensitive substring match); "search" values are
# what we type into the portal's doc-type filter / quick search.
# ---------------------------------------------------------------------------

LEAD_TYPES = {
    "LP": {
        "label": "Lis Pendens",
        "search": ["LIS PENDENS"],
        "terms": [r"\bLIS\s*PENDENS\b"],
        "exclude": [r"\bRELEASE\b", r"\bREL\b"],
        "flag": "Lis pendens",
    },
    "RELLP": {
        "label": "Release of Lis Pendens",
        "search": ["RELEASE LIS PENDENS"],
        "terms": [r"REL(EASE)?\s*(OF\s*)?LIS\s*PENDENS"],
        "exclude": [],
        "flag": None,  # informational — cancels motivation
    },
    "NOFC": {
        "label": "Notice of Foreclosure",
        "search": ["NOTICE OF FORECLOSURE", "NOTICE OF TRUSTEE SALE",
                    "NOTICE OF SUBSTITUTE TRUSTEE SALE"],
        "terms": [r"FORECLOS", r"TRUSTEE'?S?\s*SALE", r"SUBSTITUTE\s*TRUSTEE"],
        "exclude": [r"\bRESCIS", r"\bWITHDRAW"],
        "flag": "Pre-foreclosure",
    },
    "TAXDEED": {
        "label": "Tax Deed",
        "search": ["TAX DEED", "SHERIFF DEED", "CONSTABLE DEED"],
        "terms": [r"\bTAX\s*DEED\b", r"SHERIFF'?S?\s*DEED", r"CONSTABLE'?S?\s*DEED"],
        "exclude": [],
        "flag": "Tax lien",
    },
    "JUD": {
        "label": "Judgment",
        "search": ["ABSTRACT OF JUDGMENT", "JUDGMENT",
                    "CERTIFIED JUDGMENT", "DOMESTIC JUDGMENT"],
        "terms": [r"JUDGMENT", r"\bAOJ\b"],
        "exclude": [r"\bRELEASE\b", r"\bSATISFACTION\b", r"\bNUNC\b"],
        "flag": "Judgment lien",
    },
    "LNFED": {
        "label": "Federal / IRS / State Tax Lien",
        "search": ["FEDERAL TAX LIEN", "STATE TAX LIEN", "IRS LIEN"],
        "terms": [r"FEDERAL\s*TAX\s*LIEN", r"\bIRS\b.*LIEN", r"STATE\s*TAX\s*LIEN",
                   r"FEDERAL\s*LIEN"],
        "exclude": [r"\bRELEASE\b", r"\bWITHDRAW"],
        "flag": "Tax lien",
    },
    "LN": {
        "label": "Lien (General / Mechanic / HOA)",
        "search": ["LIEN", "MECHANICS LIEN", "HOA LIEN",
                    "ASSESSMENT LIEN", "HOSPITAL LIEN"],
        "terms": [r"\bLIEN\b"],
        "exclude": [r"\bRELEASE\b", r"FEDERAL", r"\bIRS\b", r"STATE\s*TAX",
                     r"MEDICAID", r"\bUCC\b"],
        "flag": "Mechanic lien",
    },
    "MEDLN": {
        "label": "Medicaid Lien",
        "search": ["MEDICAID LIEN"],
        "terms": [r"MEDICAID"],
        "exclude": [r"\bRELEASE\b"],
        "flag": "Judgment lien",
    },
    "PRO": {
        "label": "Probate / Estate",
        "search": ["PROBATE", "AFFIDAVIT OF HEIRSHIP",
                    "LETTERS TESTAMENTARY", "SMALL ESTATE AFFIDAVIT"],
        "terms": [r"PROBATE", r"HEIRSHIP", r"TESTAMENTARY", r"SMALL\s*ESTATE",
                   r"MUNIMENT"],
        "exclude": [],
        "flag": "Probate / estate",
    },
    "NOC": {
        "label": "Notice of Commencement",
        "search": ["NOTICE OF COMMENCEMENT"],
        "terms": [r"COMMENCEMENT"],
        "exclude": [],
        "flag": None,
    },
}

CORP_RE = re.compile(
    r"\b(LLC|L\.L\.C|INC\b|CORP|COMPANY|LTD|L\.P\.|LP\b|TRUST\b|BANK\b|"
    r"HOLDINGS|PROPERTIES|INVESTMENTS|VENTURES|GROUP)\b", re.I)
AMOUNT_RE = re.compile(r"\$?\s*([\d,]+(?:\.\d{2})?)")

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%H:%M:%S",
)
log = logging.getLogger("hidalgo-scraper")


# ---------------------------------------------------------------------------
# Small utilities
# ---------------------------------------------------------------------------

def retry(fn, *args, attempts=RETRIES, what="operation", **kwargs):
    """Synchronous retry wrapper — never raises past final attempt logging."""
    delay = RETRY_SLEEP
    for i in range(1, attempts + 1):
        try:
            return fn(*args, **kwargs)
        except Exception as exc:  # noqa: BLE001 — deliberate catch-all
            log.warning("%s failed (attempt %d/%d): %s", what, i, attempts, exc)
            if i < attempts:
                time.sleep(delay)
                delay *= 2
    return None


async def aretry(coro_factory, attempts=RETRIES, what="operation"):
    """Async retry wrapper for coroutine factories."""
    delay = RETRY_SLEEP
    for i in range(1, attempts + 1):
        try:
            return await coro_factory()
        except Exception as exc:  # noqa: BLE001
            log.warning("%s failed (attempt %d/%d): %s", what, i, attempts, exc)
            if i < attempts:
                await asyncio.sleep(delay)
                delay *= 2
    return None


def parse_amount(value):
    """Parse '$123,456.00' / 123456 / '123456' -> float or None."""
    if value is None:
        return None
    if isinstance(value, (int, float)):
        return float(value) if value > 0 else None
    m = AMOUNT_RE.search(str(value))
    if not m:
        return None
    try:
        amt = float(m.group(1).replace(",", ""))
        return amt if amt > 0 else None
    except ValueError:
        return None


def norm_name(name):
    """Normalize a person/entity name for dictionary matching."""
    if not name:
        return ""
    s = re.sub(r"[^A-Z0-9 ]", " ", str(name).upper())
    s = re.sub(r"\b(JR|SR|II|III|IV|ET\s*AL|ET\s*UX|AKA|DBA)\b", " ", s)
    return re.sub(r"\s+", " ", s).strip()


def name_variants(raw):
    """Yield lookup variants: FIRST LAST, LAST FIRST, LAST, FIRST."""
    n = norm_name(raw)
    if not n:
        return []
    variants = {n}
    # "LAST, FIRST" original form
    if "," in str(raw):
        parts = [norm_name(p) for p in str(raw).split(",", 1)]
        if all(parts):
            variants.add(f"{parts[0]} {parts[1]}")          # LAST FIRST
            variants.add(f"{parts[1]} {parts[0]}")          # FIRST LAST
    words = n.split()
    if len(words) >= 2:
        variants.add(f"{words[-1]} {' '.join(words[:-1])}")  # LAST FIRST...
        variants.add(f"{' '.join(words[1:])} {words[0]}")    # ...swap first word
    return list(variants)


def classify_doc_type(doc_type_str):
    """Map a raw clerk document-type string to (cat, label, flag)."""
    if not doc_type_str:
        return None
    upper = str(doc_type_str).upper()
    # RELLP must win over LP, so check it first via ordered priority list
    priority = ["RELLP", "NOFC", "TAXDEED", "LNFED", "MEDLN", "PRO",
                "NOC", "LP", "JUD", "LN"]
    for cat in priority:
        spec = LEAD_TYPES[cat]
        if any(re.search(p, upper) for p in spec["exclude"]):
            excluded_here = True
        else:
            excluded_here = False
        if not excluded_here and any(re.search(p, upper) for p in spec["terms"]):
            return cat, spec["label"], spec["flag"]
    return None


# ---------------------------------------------------------------------------
# Part 1 — County Clerk portal (Playwright, async)
# ---------------------------------------------------------------------------

def build_results_url(term, offset, start_date, end_date):
    """publicsearch.us results URL with recorded-date range + search term."""
    dr = quote(f"{start_date:%Y%m%d},{end_date:%Y%m%d}", safe="")
    return (f"{CLERK_BASE}/results?department=RP"
            f"&limit={PAGE_SIZE}&offset={offset}"
            f"&recordedDateRange={dr}"
            f"&searchOcrText=false&searchType=quickSearch"
            f"&searchValue={quote(term)}")


def _extract_api_records(payload):
    """Pull result rows out of whatever JSON envelope the portal API uses."""
    if not isinstance(payload, dict):
        return []
    for key in ("results", "data", "documents", "items", "records", "hits"):
        rows = payload.get(key)
        if isinstance(rows, dict):
            rows = rows.get("results") or rows.get("items") or rows.get("hits")
        if isinstance(rows, list) and rows and isinstance(rows[0], dict):
            return rows
    return []


def _first(d, *keys):
    for k in keys:
        v = d.get(k)
        if v not in (None, "", []):
            return v
    return None


def _join_names(v):
    if isinstance(v, list):
        out = []
        for item in v:
            if isinstance(item, dict):
                out.append(_first(item, "name", "fullName", "value") or "")
            else:
                out.append(str(item))
        return "; ".join(x for x in out if x)
    if isinstance(v, dict):
        return _first(v, "name", "fullName", "value") or ""
    return str(v) if v else ""


def normalize_api_row(row):
    """Map one API result row -> our canonical record dict (pre-parcel)."""
    try:
        doc_id = _first(row, "id", "documentId", "docId", "_id")
        doc_num = _first(row, "instrumentNumber", "docNumber",
                         "documentNumber", "instrument_number", "number")
        doc_type = _first(row, "docType", "documentType", "type",
                          "docTypeDescription", "documentTypeDescription")
        filed = _first(row, "recordedDate", "filedDate", "recorded_date",
                       "dateRecorded", "date")
        grantor = _join_names(_first(row, "grantors", "grantor", "partyOne",
                                     "directName", "firstParty"))
        grantee = _join_names(_first(row, "grantees", "grantee", "partyTwo",
                                     "reverseName", "secondParty"))
        legal = _join_names(_first(row, "legalDescription", "legals",
                                   "legal", "legal_description",
                                   "propertyDescription"))
        amount = parse_amount(_first(row, "consideration",
                                     "considerationAmount", "amount",
                                     "salePrice", "debtAmount"))
        # Normalize filed date to YYYY-MM-DD
        filed_norm = ""
        if filed:
            s = str(filed)[:10]
            for fmt in ("%Y-%m-%d", "%m/%d/%Y", "%Y%m%d"):
                try:
                    filed_norm = datetime.strptime(s, fmt).strftime("%Y-%m-%d")
                    break
                except ValueError:
                    continue
            if not filed_norm:
                filed_norm = s
        url = f"{CLERK_BASE}/doc/{doc_id}" if doc_id else CLERK_BASE
        if not doc_num and not grantor:
            return None
        return {
            "doc_num": str(doc_num or ""),
            "doc_type": str(doc_type or ""),
            "filed": filed_norm,
            "owner": grantor.strip(),
            "grantee": grantee.strip(),
            "legal": (legal or "").strip()[:400],
            "amount": amount,
            "clerk_url": url,
        }
    except Exception as exc:  # noqa: BLE001
        log.debug("bad api row skipped: %s", exc)
        return None


def normalize_dom_row(cells, href):
    """Fallback: map a DOM table row's cell texts to a record."""
    try:
        texts = [c.strip() for c in cells]
        if len(texts) < 4:
            return None
        rec = {"doc_num": "", "doc_type": "", "filed": "", "owner": "",
               "grantee": "", "legal": "", "amount": None,
               "clerk_url": urljoin(CLERK_BASE, href) if href else CLERK_BASE}
        for t in texts:
            if re.fullmatch(r"\d{6,}", t) and not rec["doc_num"]:
                rec["doc_num"] = t
            elif re.fullmatch(r"\d{1,2}/\d{1,2}/\d{4}", t) and not rec["filed"]:
                rec["filed"] = datetime.strptime(t, "%m/%d/%Y").strftime("%Y-%m-%d")
            elif classify_doc_type(t) and not rec["doc_type"]:
                rec["doc_type"] = t
        # first long alpha cell = grantor, second = grantee
        alpha = [t for t in texts
                 if t not in (rec["doc_num"], rec["doc_type"])
                 and not re.fullmatch(r"[\d/,$. ]+", t) and len(t) > 3]
        if alpha:
            rec["owner"] = alpha[0]
        if len(alpha) > 1:
            rec["grantee"] = alpha[1]
        if len(alpha) > 2:
            rec["legal"] = alpha[2][:400]
        return rec if (rec["doc_num"] or rec["owner"]) else None
    except Exception:  # noqa: BLE001
        return None


async def scrape_clerk_portal(start_date, end_date):
    """Scrape all lead types from the clerk portal. Returns list of records."""
    from playwright.async_api import async_playwright

    records = {}
    api_buffer = []

    async with async_playwright() as pw:
        browser = await pw.chromium.launch(
            headless=True,
            args=["--disable-blink-features=AutomationControlled",
                  "--no-sandbox"],
        )
        ctx = await browser.new_context(user_agent=UA,
                                        viewport={"width": 1440, "height": 900})
        page = await ctx.new_page()

        async def on_response(resp):
            try:
                if ("api" in resp.url or "search" in resp.url) and \
                        "json" in (resp.headers.get("content-type") or ""):
                    payload = await resp.json()
                    rows = _extract_api_records(payload)
                    if rows:
                        api_buffer.extend(rows)
            except Exception:  # noqa: BLE001
                pass

        page.on("response", on_response)

        # Collect unique search terms across all lead types
        terms = []
        for spec in LEAD_TYPES.values():
            for t in spec["search"]:
                if t not in terms:
                    terms.append(t)

        for term in terms:
            log.info("Clerk search: %s", term)
            for page_num in range(MAX_PAGES_PER_TYPE):
                offset = page_num * PAGE_SIZE
                url = build_results_url(term, offset, start_date, end_date)
                api_buffer.clear()

                async def _go(u=url):
                    await page.goto(u, wait_until="networkidle", timeout=60000)
                    return True

                ok = await aretry(_go, what=f"goto {term} p{page_num + 1}")
                if not ok:
                    break
                await asyncio.sleep(1.5)

                new_rows = []
                # Preferred path: captured JSON API rows
                for row in list(api_buffer):
                    rec = normalize_api_row(row)
                    if rec:
                        new_rows.append(rec)

                # Fallback path: scrape the DOM result rows
                if not new_rows:
                    try:
                        row_handles = await page.query_selector_all(
                            "table tbody tr, [class*='result-row'], "
                            "[data-testid*='result']")
                        for rh in row_handles:
                            cells = [await c.inner_text() for c in
                                     await rh.query_selector_all("td, [class*='cell']")]
                            link = await rh.query_selector("a[href*='/doc']")
                            href = await link.get_attribute("href") if link else None
                            rec = normalize_dom_row(cells, href)
                            if rec:
                                new_rows.append(rec)
                    except Exception as exc:  # noqa: BLE001
                        log.warning("DOM fallback failed: %s", exc)

                added = 0
                for rec in new_rows:
                    cls = classify_doc_type(rec["doc_type"]) or \
                        classify_doc_type(term)
                    if not cls:
                        continue
                    cat, label, _flag = cls
                    key = rec["doc_num"] or f"{rec['owner']}|{rec['filed']}"
                    if key in records:
                        continue
                    rec["cat"] = cat
                    rec["cat_label"] = label
                    records[key] = rec
                    added += 1

                log.info("  page %d: %d rows captured, %d new leads",
                         page_num + 1, len(new_rows), added)
                if len(new_rows) < PAGE_SIZE:
                    break  # last page for this term

        await browser.close()

    return list(records.values())


# ---------------------------------------------------------------------------
# Part 2 — Hidalgo CAD bulk parcel data (requests + BeautifulSoup + dbfread)
# ---------------------------------------------------------------------------

def _download(url, session, binary=True):
    r = session.get(url, timeout=180, headers={"User-Agent": UA})
    r.raise_for_status()
    return r.content if binary else r.text


def _dopostback(session, page_url, soup, target, argument=""):
    """Replay an ASP.NET __doPostBack link to trigger a file download."""
    form = soup.find("form")
    data = {}
    for inp in soup.find_all("input"):
        name = inp.get("name")
        if name:
            data[name] = inp.get("value", "")
    data["__EVENTTARGET"] = target
    data["__EVENTARGUMENT"] = argument
    action = urljoin(page_url, form.get("action") if form else page_url)
    r = session.post(action, data=data, timeout=300,
                     headers={"User-Agent": UA, "Referer": page_url})
    r.raise_for_status()
    return r.content


def find_and_download_parcel_zip():
    """Locate + download the CAD bulk export ZIP. Returns bytes or None."""
    session = requests.Session()

    candidates = []
    if CAD_BULK_URL_OVERRIDE:
        candidates.append(CAD_BULK_URL_OVERRIDE)
    candidates.extend(CAD_DIRECT_GUESSES)

    # 1) direct URLs
    for url in candidates:
        blob = retry(_download, url, session, what=f"download {url}")
        if blob and blob[:2] == b"PK":
            log.info("Parcel ZIP downloaded from %s (%.1f MB)",
                     url, len(blob) / 1e6)
            return blob

    # 2) scrape known download pages for zip/dbf links (incl. __doPostBack)
    for page_url in CAD_DOWNLOAD_PAGES:
        html = retry(_download, page_url, session, binary=False,
                     what=f"fetch {page_url}")
        if not html:
            continue
        soup = BeautifulSoup(html, "lxml")

        # plain <a href> links
        for a in soup.find_all("a", href=True):
            href = a["href"]
            text = (a.get_text() or "").lower()
            if re.search(r"\.(zip|dbf)(\?|$)", href, re.I) or \
                    any(k in text for k in ("appraisal", "export", "parcel",
                                            "roll", "gis", "shape")):
                if href.lower().startswith("javascript:__dopostback"):
                    m = re.search(r"__doPostBack\('([^']*)','([^']*)'\)", href)
                    if m:
                        blob = retry(_dopostback, session, page_url, soup,
                                     m.group(1), m.group(2),
                                     what=f"postback {m.group(1)}")
                        if blob and blob[:2] == b"PK":
                            log.info("Parcel ZIP via __doPostBack on %s", page_url)
                            return blob
                    continue
                full = urljoin(page_url, href)
                if not re.search(r"\.(zip|dbf)(\?|$)", full, re.I):
                    continue
                blob = retry(_download, full, session, what=f"download {full}")
                if blob and (blob[:2] == b"PK" or full.lower().endswith(".dbf")):
                    log.info("Parcel data downloaded from %s (%.1f MB)",
                             full, len(blob) / 1e6)
                    return blob
    log.warning("Could not locate CAD bulk parcel file — leads will be "
                "produced without situs/mailing addresses. Set CAD_BULK_URL "
                "env var to the direct ZIP link to fix.")
    return None


PARCEL_COLS = {
    "owner": ["OWNER", "OWN1", "OWNER_NAME", "OWNERNAME", "NAME", "PY_OWNER"],
    "site_addr": ["SITE_ADDR", "SITEADDR", "SITUS", "SITUS_ADDR", "PROP_ADDR",
                  "SITUSADDR", "LOCATION"],
    "site_city": ["SITE_CITY", "SITUSCITY", "SITUS_CITY", "PROP_CITY"],
    "site_zip": ["SITE_ZIP", "SITUSZIP", "SITUS_ZIP", "PROP_ZIP"],
    "mail_addr": ["ADDR_1", "MAILADR1", "MAIL_ADDR", "MAILADDR", "ADDRESS1",
                  "OWN_ADDR", "MAIL_LINE1"],
    "mail_city": ["CITY", "MAILCITY", "MAIL_CITY", "OWN_CITY"],
    "mail_state": ["STATE", "MAILSTATE", "MAIL_STATE", "ST", "OWN_STATE"],
    "mail_zip": ["ZIP", "MAILZIP", "MAIL_ZIP", "ZIPCODE", "OWN_ZIP"],
}


def _pick_col(fieldnames, wanted):
    up = {f.upper(): f for f in fieldnames}
    for cand in wanted:
        if cand in up:
            return up[cand]
    return None


def build_owner_lookup(zip_bytes):
    """Extract DBF from ZIP (or raw DBF bytes) and build name->parcel dict."""
    if DBF is None:
        log.warning("dbfread not installed — skipping parcel matching")
        return {}

    PARCEL_CACHE_DIR.mkdir(parents=True, exist_ok=True)
    dbf_path = None

    if zip_bytes[:2] == b"PK":
        try:
            zf = zipfile.ZipFile(io.BytesIO(zip_bytes))
            dbf_names = sorted(
                (n for n in zf.namelist() if n.lower().endswith(".dbf")),
                key=lambda n: -zf.getinfo(n).file_size)
            if not dbf_names:
                log.warning("ZIP contains no DBF file")
                return {}
            dbf_path = PARCEL_CACHE_DIR / Path(dbf_names[0]).name
            dbf_path.write_bytes(zf.read(dbf_names[0]))
        except Exception as exc:  # noqa: BLE001
            log.warning("Failed to extract DBF: %s", exc)
            return {}
    else:
        dbf_path = PARCEL_CACHE_DIR / "parcels.dbf"
        dbf_path.write_bytes(zip_bytes)

    lookup = {}
    try:
        table = DBF(str(dbf_path), load=False, char_decode_errors="ignore",
                    ignore_missing_memofile=True)
        cols = {k: _pick_col(table.field_names, v)
                for k, v in PARCEL_COLS.items()}
        log.info("DBF columns mapped: %s", cols)
        if not cols["owner"]:
            log.warning("No owner column found in DBF")
            return {}

        count = 0
        for rec in table:
            try:
                owner_raw = rec.get(cols["owner"])
                if not owner_raw:
                    continue
                parcel = {
                    "prop_address": str(rec.get(cols["site_addr"]) or "").strip()
                    if cols["site_addr"] else "",
                    "prop_city": str(rec.get(cols["site_city"]) or "").strip()
                    if cols["site_city"] else "",
                    "prop_zip": str(rec.get(cols["site_zip"]) or "").strip()
                    if cols["site_zip"] else "",
                    "mail_address": str(rec.get(cols["mail_addr"]) or "").strip()
                    if cols["mail_addr"] else "",
                    "mail_city": str(rec.get(cols["mail_city"]) or "").strip()
                    if cols["mail_city"] else "",
                    "mail_state": str(rec.get(cols["mail_state"]) or "").strip()
                    if cols["mail_state"] else "",
                    "mail_zip": str(rec.get(cols["mail_zip"]) or "").strip()
                    if cols["mail_zip"] else "",
                }
                for variant in name_variants(owner_raw):
                    # first parcel wins for a given name variant
                    lookup.setdefault(variant, parcel)
                count += 1
            except Exception:  # noqa: BLE001
                continue
        log.info("Parcel lookup built: %d parcels, %d name keys",
                 count, len(lookup))
    except Exception as exc:  # noqa: BLE001
        log.warning("DBF parse failed: %s", exc)
    return lookup


def match_parcel(owner, lookup):
    """Find the best parcel match for a clerk-record owner name."""
    if not owner or not lookup:
        return None
    # try each individual name if multiple parties joined with ';'
    for part in str(owner).split(";"):
        for v in name_variants(part):
            hit = lookup.get(v)
            if hit:
                return hit
        # last-ditch: LAST + first word of FIRST
        words = norm_name(part).split()
        if len(words) >= 2:
            hit = lookup.get(f"{words[-1]} {words[0]}") or \
                lookup.get(f"{words[0]} {words[-1]}")
            if hit:
                return hit
    return None


# ---------------------------------------------------------------------------
# Part 3 — Scoring
# ---------------------------------------------------------------------------

def score_record(rec, week_start):
    """Seller score 0–100 per DMR spec, plus motivated-seller flags."""
    flags = []
    cat = rec.get("cat")
    spec = LEAD_TYPES.get(cat, {})
    if spec.get("flag"):
        flags.append(spec["flag"])

    owner = rec.get("owner") or ""
    if CORP_RE.search(owner):
        flags.append("LLC / corp owner")

    is_new = False
    try:
        filed = datetime.strptime(rec.get("filed", ""), "%Y-%m-%d").date()
        is_new = filed >= week_start
    except ValueError:
        pass
    if is_new:
        flags.append("New this week")

    score = 30
    score += 10 * len([f for f in flags if f != "New this week"])

    # LP + foreclosure combo on the same owner is handled by caller via
    # rec["_combo"]; +20 when both an LP and an FC doc exist for the owner.
    if rec.get("_combo"):
        score += 20
        if "Pre-foreclosure" not in flags:
            flags.append("Pre-foreclosure")

    amount = rec.get("amount")
    if amount and amount > 100_000:
        score += 15
    elif amount and amount > 50_000:
        score += 10

    if is_new:
        score += 5
    if rec.get("prop_address") or rec.get("mail_address"):
        score += 5

    rec["flags"] = flags
    rec["score"] = max(0, min(100, score))
    return rec


def mark_lp_fc_combos(records):
    """Flag owners that appear on BOTH a lis pendens and a foreclosure doc."""
    by_owner = {}
    for r in records:
        key = norm_name((r.get("owner") or "").split(";")[0])
        if key:
            by_owner.setdefault(key, set()).add(r.get("cat"))
    for r in records:
        key = norm_name((r.get("owner") or "").split(";")[0])
        cats = by_owner.get(key, set())
        r["_combo"] = "LP" in cats and "NOFC" in cats


# ---------------------------------------------------------------------------
# Part 4 — Output (records.json + GHL CSV)
# ---------------------------------------------------------------------------

def split_name(owner):
    """Best-effort split of an owner string into (first, last) for GHL."""
    if not owner:
        return "", ""
    primary = str(owner).split(";")[0].strip()
    if CORP_RE.search(primary):
        return primary, ""  # company name goes in First Name field
    if "," in primary:
        last, _, first = primary.partition(",")
        return first.strip().title(), last.strip().title()
    words = primary.split()
    if len(words) == 1:
        return words[0].title(), ""
    # Clerk indexes are usually LAST FIRST MIDDLE
    return " ".join(words[1:]).title(), words[0].title()


def export_ghl_csv(records, path):
    """Write a GoHighLevel-import-ready CSV."""
    headers = ["First Name", "Last Name", "Mailing Address", "Mailing City",
               "Mailing State", "Mailing Zip", "Property Address",
               "Property City", "Property State", "Property Zip", "Lead Type",
               "Document Type", "Date Filed", "Document Number",
               "Amount/Debt Owed", "Seller Score", "Motivated Seller Flags",
               "Source", "Public Records URL"]
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow(headers)
        for r in records:
            try:
                first, last = split_name(r.get("owner"))
                w.writerow([
                    first, last,
                    r.get("mail_address", ""), r.get("mail_city", ""),
                    r.get("mail_state", ""), r.get("mail_zip", ""),
                    r.get("prop_address", ""), r.get("prop_city", ""),
                    r.get("prop_state", ""), r.get("prop_zip", ""),
                    r.get("cat_label", ""), r.get("doc_type", ""),
                    r.get("filed", ""), r.get("doc_num", ""),
                    f"{r['amount']:.2f}" if r.get("amount") else "",
                    r.get("score", ""),
                    "; ".join(r.get("flags", [])),
                    "Hidalgo County Clerk",
                    r.get("clerk_url", ""),
                ])
            except Exception as exc:  # noqa: BLE001
                log.warning("CSV row skipped: %s", exc)
    log.info("GHL CSV written: %s (%d rows)", path, len(records))


def save_json(records, start_date, end_date):
    payload = {
        "fetched_at": datetime.now(timezone.utc).isoformat(),
        "source": "Hidalgo County Clerk (publicsearch.us) + Hidalgo CAD",
        "date_range": f"{start_date:%Y-%m-%d} to {end_date:%Y-%m-%d}",
        "total": len(records),
        "with_address": sum(1 for r in records
                            if r.get("prop_address") or r.get("mail_address")),
        "records": records,
    }
    for p in (DASHBOARD_JSON, DATA_JSON):
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(payload, indent=2, default=str),
                     encoding="utf-8")
        log.info("Wrote %s", p)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

async def main():
    end_date = datetime.now().date()
    start_date = end_date - timedelta(days=LOOKBACK_DAYS)
    week_start = end_date - timedelta(days=7)
    log.info("Hidalgo lead scrape: %s -> %s", start_date, end_date)

    # ---- Clerk portal --------------------------------------------------
    clerk_records = []
    try:
        clerk_records = await scrape_clerk_portal(start_date, end_date) or []
    except Exception as exc:  # noqa: BLE001
        log.error("Clerk portal scrape failed entirely: %s", exc)
    log.info("Clerk records collected: %d", len(clerk_records))

    # ---- Parcel matching ------------------------------------------------
    lookup = {}
    try:
        blob = find_and_download_parcel_zip()
        if blob:
            lookup = build_owner_lookup(blob)
    except Exception as exc:  # noqa: BLE001
        log.error("Parcel pipeline failed: %s", exc)

    # ---- Enrich + score --------------------------------------------------
    final = []
    for rec in clerk_records:
        try:
            base = {
                "doc_num": rec.get("doc_num", ""),
                "doc_type": rec.get("doc_type", ""),
                "filed": rec.get("filed", ""),
                "cat": rec.get("cat", ""),
                "cat_label": rec.get("cat_label", ""),
                "owner": rec.get("owner", ""),
                "grantee": rec.get("grantee", ""),
                "amount": rec.get("amount"),
                "legal": rec.get("legal", ""),
                "prop_address": "", "prop_city": "", "prop_state": "TX",
                "prop_zip": "", "mail_address": "", "mail_city": "",
                "mail_state": "", "mail_zip": "",
                "clerk_url": rec.get("clerk_url", CLERK_BASE),
            }
            parcel = match_parcel(base["owner"], lookup)
            if parcel:
                base.update({
                    "prop_address": parcel["prop_address"],
                    "prop_city": parcel["prop_city"],
                    "prop_zip": parcel["prop_zip"],
                    "mail_address": parcel["mail_address"],
                    "mail_city": parcel["mail_city"],
                    "mail_state": parcel["mail_state"] or "TX",
                    "mail_zip": parcel["mail_zip"],
                })
            final.append(base)
        except Exception as exc:  # noqa: BLE001
            log.warning("Record enrichment skipped: %s", exc)

    mark_lp_fc_combos(final)
    for rec in final:
        try:
            score_record(rec, week_start)
        except Exception as exc:  # noqa: BLE001
            rec.setdefault("flags", [])
            rec.setdefault("score", 30)
            log.warning("Scoring failed for %s: %s", rec.get("doc_num"), exc)
        rec.pop("_combo", None)

    # Drop pure releases (RELLP) below everything else, sort by score desc
    final.sort(key=lambda r: (-(r.get("score") or 0), r.get("filed") or ""))

    # ---- Outputs ----------------------------------------------------------
    save_json(final, start_date, end_date)
    export_ghl_csv(final, GHL_CSV)

    log.info("DONE — %d leads, %d with addresses",
             len(final),
             sum(1 for r in final
                 if r.get("prop_address") or r.get("mail_address")))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(asyncio.run(main()))
    except KeyboardInterrupt:
        sys.exit(130)
    except Exception as exc:  # noqa: BLE001 — final safety net: never crash CI
        log.error("FATAL (suppressed): %s", exc)
        # still emit empty outputs so downstream steps don't fail
        try:
            save_json([], datetime.now().date() - timedelta(days=LOOKBACK_DAYS),
                      datetime.now().date())
        except Exception:
            pass
        sys.exit(0)
