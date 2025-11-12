#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Zillow Monthly Emailer — Geo-aware + Ranked ZIP Charts + 12-month ZIP Tables
- Pulls 6 Zillow CSVs (ZHVI+ZORI × Metro/County/Zip) with fallbacks
- For each configured area:
    1) County vs Metro overlay (quarterly annotations on County)
    2) ZIP charts: Top 5 ↑ YoY and Bottom 2 ↓ YoY (legend + right-edge labels)
    3) ZIP 12-month backup table (ALL ZIPs) + YoY% based on a common latest month (CSV attachments only)
- Summary tables (last 12 months) for County/Metro overlays (shown in email body)
- Emails charts inline and attaches summary CSVs + per-metro ZIP CSVs

Notes:
- Robust metro resolver to prevent mis-assignments (e.g., avoids matching "san" to "santa").
- Added Zillow “Total Monthly Payment (20% down)” Metro dataset to compute rental/flip metrics,
  and output detailed CSVs with all intermediate columns used in calculations.
"""

import io, re, ssl, smtplib, pathlib, warnings, requests, pandas as pd, matplotlib.pyplot as plt
from datetime import datetime, timezone
from bs4 import BeautifulSoup
from dateutil.parser import parse as parse_date
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from email.mime.image import MIMEImage
import unicodedata
import os, json

# ================= CONFIG =================
EMAIL_USERNAME = "beluliproperties@gmail.com"

APP_PWD = os.getenv("GMAIL_APP_PWD")
assert APP_PWD, "Missing GMAIL_APP_PWD environment variable"

EMAIL_TO = ["beluliproperties@gmail.com"]
FROM_NAME = "Zillow Monthly Charts"
SUBJECT_PREFIX = "[Zillow]"

OUT_DIR = "./ZillowMonthly"
YEARS_BACK = 5
SMTP_MODE = "starttls"  # "ssl" or "starttls"

# Investment metric knobs
OPEX_RATE = 0.30  # share of gross rent treated as operating expenses
DPCT = 0.20       # down payment percent (20% matches Zillow payment series)
CLOSING_COST_RATE = 0.03
HOLD_MONTHS = 6

# Summary table horizon for county/metro overlays
SUMMARY_LAST_N_MONTHS = 12

# ----- ZIP chart/table controls -----
ZIP_TOP_UP = 5
ZIP_TOP_DOWN = 2
ZIP_MA_MONTHS = 3
ZIP_RANK_MIN_MONTHS = 6

# ----------------- AREAS -----------------
AREAS = [
    {"name": "Sacramento", "county": "Sacramento County, CA", "metro": "Sacramento, CA"},
    {"name": "San Francisco", "county": "San Francisco County, CA", "metro": "San Francisco, CA"},
    {"name": "Chicago", "county": "Cook County, IL", "metro": "Chicago, IL"},
]
# ================================================================================

ZILLOW_DATA_PAGE = "https://www.zillow.com/research/data/"
BASE_PREFIX = "https://files.zillowstatic.com/research/public_csvs"
HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/120.0.0.0 Safari/537.36"
    )
}

FILENAME_PATTERNS = {
    "zhvi": {
        "Metro": r"Metro_zhvi_.*_sm_sa_month\.csv",
        "County": r"County_zhvi_.*_sm_sa_month\.csv",
        "Zip": r"Zip_zhvi_.*_sm_sa_month\.csv",
    },
    "zori": {
        "Metro": r"Metro_zori_.*_sm_month\.csv",
        "County": r"County_zori_.*_sm_month\.csv",
        "Zip": r"Zip_zori_.*_sm_month\.csv",
    },
    "payment": {
        "Metro": r"Metro_total_monthly_payment_downpayment_0\.20_.*_sm_sa_month\.csv",
    },
}

# Known-good fallbacks
FALLBACK_FILES = {
    ("zhvi", "Metro"): "Metro_zhvi_uc_sfrcondo_tier_0.33_0.67_sm_sa_month.csv",
    ("zhvi", "County"): "County_zhvi_uc_sfrcondo_tier_0.33_0.67_sm_sa_month.csv",
    ("zhvi", "Zip"): "Zip_zhvi_uc_sfrcondo_tier_0.33_0.67_sm_sa_month.csv",
    ("zori", "Metro"): "Metro_zori_uc_sfrcondomfr_sm_month.csv",
    ("zori", "County"): "County_zori_uc_sfrcondomfr_sm_month.csv",
    ("zori", "Zip"): "Zip_zori_uc_sfrcondomfr_sm_month.csv",
    ("payment", "Metro"): "Metro_total_monthly_payment_downpayment_0.20_uc_sfrcondo_tier_0.33_0.67_sm_sa_month.csv",
}

# ==================== Core helpers ====================
def _latest_available_month_for_guard() -> str | None:
    df = PREFETCH.get(("zhvi", "Zip"))
    if df is None or df.empty or "date" not in df.columns:
        return None
    latest = pd.to_datetime(df["date"]).max()
    return latest.strftime("%Y-%m") if pd.notna(latest) else None

def _already_sent(asof: str, stamp_path: str) -> bool:
    if not os.path.exists(stamp_path):
        return False
    try:
        with open(stamp_path, "r") as f:
            data = json.load(f)
        last_sent = data.get("last_sent")
        return (last_sent == asof)
    except Exception:
        return False

def _write_sent_extended(asof: str, stamp_path: str, meta: dict):
    pathlib.Path(stamp_path).parent.mkdir(parents=True, exist_ok=True)
    payload = {"last_sent": asof, **meta}
    with open(stamp_path, "w") as f:
        json.dump(payload, f, indent=2, default=str)

def _read_stamp(stamp_path: str) -> dict:
    if not os.path.exists(stamp_path):
        return {}
    try:
        with open(stamp_path, "r") as f:
            return json.load(f)
    except Exception:
        return {}

def find_csv_url(dataset: str, geolevel: str) -> str:
    subfolder = "total_monthly_payment" if dataset == "payment" else dataset
    fallback = f"{BASE_PREFIX}/{subfolder}/{FALLBACK_FILES[(dataset, geolevel)]}"
    try:
        resp = requests.get(ZILLOW_DATA_PAGE, headers=HEADERS, timeout=30)
        resp.raise_for_status()
        soup = BeautifulSoup(resp.text, "html.parser")
        anchors = soup.find_all("a", href=True)
        hrefs = [a["href"].split("?")[0] for a in anchors
                 if "files.zillowstatic.com/research/public_csvs" in a["href"]]
        regex = re.compile(FILENAME_PATTERNS[dataset][geolevel], re.IGNORECASE)
        needle = f"/{subfolder}/"
        for href in hrefs:
            if needle in href and regex.search(href):
                return href
        return fallback
    except Exception as e:
        print(f"[WARN] Could not scrape Zillow page ({e}). Using fallback URL.")
        return fallback

def _head_meta(url: str) -> dict:
    """Fast HEAD to capture Last-Modified and ETag (if provided)."""
    try:
        r = requests.head(url, headers=HEADERS, timeout=30, allow_redirects=True)
        lm = r.headers.get("Last-Modified")
        et = r.headers.get("ETag")
        lm_iso = None
        if lm:
            try:
                dt = parse_date(lm)
                if not dt.tzinfo:
                    dt = dt.replace(tzinfo=timezone.utc)
                lm_iso = dt.astimezone(timezone.utc).isoformat()
            except Exception:
                lm_iso = lm
        return {"last_modified": lm_iso, "etag": et}
    except Exception as e:
        return {"last_modified": None, "etag": None, "error": str(e)}

def load_wide_csv(url: str) -> pd.DataFrame:
    r = requests.get(url, headers=HEADERS, timeout=120)
    if r.status_code == 403:
        print("[WARN] 403 on file download; retrying once…")
        r = requests.get(url, headers=HEADERS, timeout=120)
    if r.status_code == 404 and "/research/public_csvs/payment/" in url:
        fixed_url = url.replace("/research/public_csvs/payment/", "/research/public_csvs/total_monthly_payment/")
        print(f"[WARN] 404 on payment URL; retrying with folder fix → {fixed_url}")
        r = requests.get(fixed_url, headers=HEADERS, timeout=120)
    r.raise_for_status()
    content = r.content
    if b"," not in content and b"\n" not in content:
        raise ValueError(f"Downloaded content does not look like CSV from {url}")
    return pd.read_csv(io.BytesIO(content), low_memory=False)

def to_long(df: pd.DataFrame) -> pd.DataFrame:
    meta_cols, time_cols = set(), []
    for c in df.columns:
        s = str(c)
        if re.fullmatch(r"\d{4}-\d{2}", s) or re.fullmatch(r"\d{4}-\d{2}-\d{2}", s):
            time_cols.append(c); continue
        try:
            dt = parse_date(s, default=datetime(1900, 1, 1))
            if dt.year >= 1900:
                time_cols.append(c); continue
        except Exception:
            pass
        meta_cols.add(c)
    time_cols = [c for c in time_cols if c in df.columns]
    id_vars = [c for c in df.columns if c not in time_cols]
    long = df.melt(id_vars=id_vars, value_vars=time_cols, var_name="date_str", value_name="value")

    def parse_maybe(d):
        try:
            dt = parse_date(str(d), default=datetime(1900, 1, 1))
            return datetime(dt.year, dt.month, 1)
        except Exception:
            return pd.NaT

    long["date"] = long["date_str"].map(parse_maybe)
    long = long.dropna(subset=["date"])
    long["value"] = pd.to_numeric(long["value"], errors="coerce")
    long = long.dropna(subset=["value"])
    return long.sort_values(["date"]).reset_index(drop=True)

# =================== Matching & Series ===================
def normalize_text(s: str) -> str:
    if s is None:
        return ""
    s = str(s)
    s = unicodedata.normalize("NFKC", s).replace("–", "-").replace("—", "-")
    s = " ".join(s.strip().lower().split())
    return s

def parse_target(target: str):
    t = normalize_text(target)
    parts = [p.strip() for p in t.split(",")]
    name = parts[0]; state = parts[1] if len(parts) > 1 else None
    kind = "county" if name.endswith(" county") else None
    if "-" in name and (state or (len(parts) > 1)):
        kind = kind or "metro"
    if kind is None:
        kind = "city"
    if kind == "county" and name.endswith(" county"):
        name = name[:-7].strip()
    return kind, name, state

def smart_match_one(df_long: pd.DataFrame, target: str, geolevel_hint: str | None = None) -> pd.DataFrame:
    if df_long.empty: return pd.DataFrame()
    cols = set(df_long.columns)
    has = {c: (c in cols) for c in ["RegionName", "RegionType", "StateName", "State", "CountyName", "Metro"]}

    def colnorm(c):
        if not has.get(c, False): return pd.Series("", index=df_long.index)
        return df_long[c].astype(str).map(normalize_text)

    rn, rty = colnorm("RegionName"), colnorm("RegionType")
    stn, st = colnorm("StateName"), colnorm("State")
    cty, metro = colnorm("CountyName"), colnorm("Metro")

    kind, name_raw, state_raw = parse_target(target)
    name_l = normalize_text(name_raw)
    state_l = normalize_text(state_raw) if state_raw else ""
    hint = normalize_text(geolevel_hint) if geolevel_hint else None
    target_norm = normalize_text(target)

    state_ok = (stn == state_l) | (st == state_l) if state_l else pd.Series(True, index=df_long.index)
    mask = pd.Series(False, index=df_long.index)

    if (kind == "city") or (hint == "city"):
        m = (rty == "city") & (rn == name_l)
        mask |= (m & state_ok)
        if not mask.any():
            m2 = (rty == "city") & rn.str.contains(rf"^{re.escape(name_l)}$", na=False)
            mask |= (m2 & state_ok)

    elif (kind == "county") or (hint == "county"):
        wanted_rn = f"{name_l} county"
        m = (rty == "county") & ((rn == wanted_rn) | (cty == wanted_rn) | (rn == name_l) | (cty == name_l))
        mask |= (m & state_ok)

    elif (kind == "metro") or (hint == "metro"):
        m_rn = rn == target_norm
        m_metro = pd.Series(False, index=df_long.index)
        if has.get("Metro", False):
            m_metro = (metro == target_norm) | (metro.str.replace(",", "", regex=False) == target_norm.replace(",", ""))
        mask |= ((m_metro | m_rn) & state_ok)
        if not mask.any():
            tn = target_norm.replace(",", "")
            parts = [rn.str.contains(re.escape(tn), na=False)]
            if has.get("Metro", False): parts.append(metro.str.contains(re.escape(tn), na=False))
            mask = parts[0]
            for p in parts[1:]: mask |= p
            mask &= state_ok

    if not mask.any():
        tn = target_norm
        parts = [
            rn.str.contains(re.escape(tn), na=False),
            cty.str.contains(re.escape(tn), na=False),
            stn.str_contains(re.escape(tn), na=False) if hasattr(stn, "str_contains") else stn.str.contains(re.escape(tn), na=False),
            st.str.contains(re.escape(tn), na=False),
        ]
        if "Metro" in df_long.columns:
            parts.append(metro.str.contains(re.escape(tn), na=False))
        mask = parts[0]
        for p in parts[1:]: mask |= p
        mask &= state_ok

    return df_long[mask].copy()

def smart_match_many(df_long: pd.DataFrame, targets, geolevel_hint: str | None = None) -> dict:
    out = {}
    for t in targets:
        hit = smart_match_one(df_long, t, geolevel_hint=geolevel_hint)
        if not hit.empty: out[t] = hit
    return out

PREFETCH = {}  # (dataset, geolevel) -> long_df

def prefetch_all():
    for dataset in ("zhvi", "zori", "payment"):
        levels = ("Metro", "County", "Zip") if dataset in ("zhvi", "zori") else ("Metro",)
        for geolevel in levels:
            url = find_csv_url(dataset, geolevel)
            print(f"[INFO] Prefetch {dataset}/{geolevel} → {url}")
            wide = load_wide_csv(url)
            PREFETCH[(dataset, geolevel)] = to_long(wide)

def get_long_df(dataset: str, geolevel: str) -> pd.DataFrame:
    return PREFETCH.get((dataset, geolevel), pd.DataFrame())

def series_for(dataset: str, geolevel: str, region: str) -> pd.Series:
    df_long = get_long_df(dataset, geolevel)
    if df_long.empty: return pd.Series(dtype=float)
    if geolevel == "Metro":
        rn = df_long.get("RegionName")
        if rn is not None:
            mask = rn.astype(str).str.strip().str.casefold() == str(region).strip().casefold()
            sub = df_long.loc[mask].copy()
        else:
            sub = pd.DataFrame()
        if sub.empty:
            sub = smart_match_many(df_long.copy(), [region], geolevel_hint=geolevel).get(region, pd.DataFrame())
    else:
        sub = smart_match_many(df_long.copy(), [region], geolevel_hint=geolevel).get(region, pd.DataFrame())
    if sub.empty: return pd.Series(dtype=float)
    s = sub.groupby("date")["value"].mean().sort_index()
    if not s.empty and YEARS_BACK:
        now = datetime.now()
        cutoff = pd.Timestamp(now.year - YEARS_BACK, now.month, 1)
        s = s[s.index >= cutoff]
    return s

# ========================= Metro resolver + ZIP selection using ZIP.Metro =========================
def _norm_msa(s: str) -> str:
    if s is None: return ""
    s = unicodedata.normalize("NFKC", str(s)).lower().strip()
    s = s.replace("—", "-").replace("–", "-")
    s = re.sub(r"[,]+", "", s)
    s = re.sub(r"\s+", " ", s)
    return s

def _split_hint(metro_hint: str) -> tuple[str, str]:
    parts = [p.strip() for p in str(metro_hint).split(",")]
    city = normalize_text(parts[0]) if parts else ""
    st = parts[1].strip().upper() if len(parts) > 1 else ""
    return city, st

def _candidate_state_tokens(cand: str) -> set[str]:
    if "," not in cand: return set()
    suffix = cand.split(",")[-1].strip().upper()
    return set(token.strip() for token in suffix.split("-") if token.strip())

def _candidate_city_prefix(cand: str) -> str:
    left = cand.split(",")[0]
    left = left.split("-")[0]
    return normalize_text(left)

def _resolve_metro_name(dataset: str, metro_hint: str) -> str | None:
    candidates = set()
    for level in ("Zip", "County"):
        df = get_long_df(dataset, level)
        if "Metro" in df.columns:
            candidates.update(df["Metro"].dropna().astype(str).unique().tolist())
    if not candidates:
        return None

    hint_city, hint_state = _split_hint(metro_hint)
    if not hint_city:
        return None

    scored = []
    for cand in candidates:
        city_pref = _candidate_city_prefix(cand)
        state_tokens = _candidate_state_tokens(cand)

        state_match = 1 if (not hint_state or (hint_state in state_tokens)) else 0
        city_exact = 1 if (city_pref == hint_city) else 0

        left_side_norm = normalize_text(cand.split(",")[0])
        city_token_contained = 1 if re.search(rf"\b{re.escape(hint_city)}\b", left_side_norm) else 0

        score = (city_exact * 5) + (state_match * 3) + (city_token_contained * 2)

        if city_pref.startswith(hint_city) and city_pref != hint_city:
            score -= 3

        scored.append((score, cand))

    scored.sort(key=lambda t: (t[0], len(t[1])), reverse=True)
    best_score, best_cand = scored[0]
    if best_score >= 5:
        return best_cand
    hint_n = _norm_msa(metro_hint)
    for cand in candidates:
        if _norm_msa(cand) == hint_n:
            return cand
    return None

def zip_series_by_metro(dataset: str, metro_label: str) -> dict[str, pd.Series]:
    dfz = get_long_df(dataset, "Zip")
    if dfz.empty: return {}
    req = {"RegionName", "date", "value", "Metro"}
    if not req.issubset(dfz.columns):
        print(f"[WARN] ZIP CSV for {dataset} missing columns needed for metro filter.")
        return {}
    resolved = _resolve_metro_name(dataset, metro_label)
    if not resolved:
        print(f"[WARN] Could not confidently resolve metro for '{metro_label}' ({dataset}); skipping ZIPs.")
        return {}
    m_norm = _norm_msa(resolved)
    mmask = dfz["Metro"].astype(str).map(_norm_msa) == m_norm
    sub = dfz.loc[mmask, ["RegionName", "date", "value"]]
    if sub.empty:
        print(f"[WARN] ZIP filter by Metro found no rows for {resolved} ({dataset}).")
        return {}
    now = datetime.now()
    cutoff = pd.Timestamp(now.year - YEARS_BACK, now.month, 1) if YEARS_BACK else None
    series_map = {}
    for z, g in sub.groupby("RegionName"):
        s = g.groupby("date")["value"].mean().sort_index()
        if cutoff is not None: s = s[s.index >= cutoff]
        if not s.empty: series_map[str(z)] = s
    return series_map

# ========================= ZIP metrics & tables (common latest month) =========================
def _latest_common_month(series_map: dict[str, pd.Series]) -> pd.Timestamp | None:
    latest_candidates = []
    for s in series_map.values():
        sx = s.dropna()
        if not sx.empty:
            latest_candidates.append(pd.Timestamp(sx.index.max().year, sx.index.max().month, 1))
    return max(latest_candidates) if latest_candidates else None

def zip_metrics(series_map: dict[str, pd.Series]) -> pd.DataFrame:
    latest_month = _latest_common_month(series_map)
    if latest_month is None: return pd.DataFrame()
    rows = []
    for z, s in series_map.items():
        s = s.dropna()
        if s.empty: continue
        s.index = pd.Index([pd.Timestamp(d.year, d.month, 1) for d in s.index])
        v_now = s.get(latest_month, pd.NA)
        v_prev = s.get(pd.Timestamp(latest_month.year - 1, latest_month.month, 1), pd.NA)
        yoy = ((v_now / v_prev - 1) * 100) if (pd.notna(v_now) and pd.notna(v_prev) and v_prev != 0) else pd.NA
        rows.append({"zip": z, "latest_date": latest_month, "latest": v_now, "yoy_pct": yoy, "n": s.size})
    return pd.DataFrame(rows)

def build_zip_last12_table(series_map: dict[str, pd.Series]) -> tuple[pd.DataFrame, pd.DataFrame]:
    if not series_map: return (pd.DataFrame(), pd.DataFrame())
    latest = _latest_common_month(series_map)
    if latest is None: return (pd.DataFrame(), pd.DataFrame())
    months = [pd.Timestamp((latest - pd.DateOffset(months=i)).year,
                           (latest - pd.DateOffset(months=i)).month, 1)
              for i in range(11, -1, -1)]
    month_labels = [m.strftime("%Y-%m") for m in months]

    rows = []
    for z, s in series_map.items():
        s2 = s.copy()
        s2.index = pd.Index([pd.Timestamp(d.year, d.month, 1) for d in s2.index])
        row_vals = [s2.get(m, pd.NA) for m in months]
        v_now = s2.get(latest, pd.NA)
        v_prev = s2.get(pd.Timestamp(latest.year - 1, latest.month, 1), pd.NA)
        yoy = ((v_now / v_prev - 1) * 100) if (pd.notna(v_now) and pd.notna(v_prev) and v_prev != 0) else pd.NA
        rows.append([z] + row_vals + [yoy])

    raw = pd.DataFrame(rows, columns=["ZIP"] + month_labels + ["YoY %"]).set_index("ZIP")
    fmt = raw.copy()
    for c in month_labels:
        fmt[c] = fmt[c].map(lambda v: "" if pd.isna(v) else f"${int(round(v, 0)):,}")
    fmt["YoY %"] = fmt["YoY %"].map(lambda p: "" if pd.isna(p) else f"{'+' if p >= 0 else ''}{p:.1f}%")
    return raw, fmt

# ========================= Formatters =========================
def fmt_home_value(v: float) -> str:
    if v >= 1_000_000: return f"${v / 1_000_000:.1f}M"
    if v >= 1_000:     return f"${v / 1_000:.0f}K"
    return f"${v:,.0f}"

def fmt_rent_exact(v: float) -> str:
    return f"${v:,.0f}"

def slugify_name(name: str) -> str:
    return re.sub(r"[^A-Za-z0-9\-]+", "_", str(name))

# ========================= Overlay plotting =========================
def plot_overlay_chart(series_list, labels, title, ylabel, outfile, annotate_index=0, fmt_fn=fmt_home_value):
    if not series_list: return
    plt.figure(figsize=(10, 5), dpi=150)
    for s, lab in zip(series_list, labels):
        plt.plot(s.index, s.values, linewidth=2, alpha=0.95, label=lab)

    # quarterly annotations on first series
    if 0 <= annotate_index < len(series_list) and not series_list[annotate_index].empty:
        s = series_list[annotate_index]
        q_mask = s.index.month.isin([1, 4, 7, 10])
        q_dates = s.index[q_mask]
        q_values = s[q_mask]
        plt.scatter(q_dates, q_values, s=50, edgecolor="white", zorder=5)
        vrange = (float(s.max()) - float(s.min())) or 1.0
        for i, (d, v) in enumerate(zip(q_dates, q_values)):
            offset_y = vrange * 0.05 * (1 if i % 2 == 0 else -1)
            x_nudge_days = 6 if (i % 2 == 0) else -6
            plt.annotate(
                fmt_fn(float(v)),
                xy=(d, v),
                xytext=(d + pd.Timedelta(days=x_nudge_days), v + offset_y),
                textcoords="data",
                ha="center",
                va="bottom" if offset_y > 0 else "top",
                fontsize=9, color="#222",
                arrowprops=dict(arrowstyle="-", color="gray", lw=0.9, alpha=0.8),
                bbox=dict(facecolor="white", alpha=0.85, edgecolor="#ddd", pad=1.8),
                zorder=6
            )

    plt.title(title, fontsize=12, pad=10)
    plt.xlabel("Date"); plt.ylabel(ylabel)
    plt.grid(True, which="major", linestyle="--", alpha=0.35)
    plt.minorticks_on(); plt.grid(True, which="minor", linestyle=":", alpha=0.15)
    plt.legend(loc="best", frameon=False)
    plt.tight_layout(); plt.savefig(outfile, bbox_inches="tight"); plt.close()

# ========================= ZIP ranked plots =========================
def _ma(s: pd.Series, win: int) -> pd.Series:
    if not win or win <= 1: return s
    return s.rolling(win, min_periods=max(1, win // 2)).mean()

def plot_ranked_zips(series_map: dict[str, pd.Series], title: str, ylabel: str, outfile: str,
                     pick_zips: list[str], yoy_map: dict[str, float], ma_months: int = 3):
    if not series_map or not pick_zips: return
    idx = sorted(set().union(*[series_map[z].index for z in pick_zips if z in series_map]))
    if not idx: return
    plt.figure(figsize=(11, 6), dpi=150)

    last_points = []
    for z in pick_zips:
        s = series_map[z].reindex(idx)
        s = _ma(s, ma_months)
        yoy = yoy_map.get(z, float("nan"))
        lab = f"{z} ({'+' if pd.notna(yoy) and yoy >= 0 else ''}{(yoy if pd.notna(yoy) else float('nan')):.1f}%)"
        plt.plot(idx, s.values, linewidth=2, alpha=0.9, label=lab)
        s2 = s.dropna()
        if not s2.empty:
            last_points.append((lab, s2.index[-1], float(s2.iloc[-1])))

    if idx:
        plt.xlim([min(idx), max(idx) + pd.Timedelta(days=60)])

    if last_points:
        last_points.sort(key=lambda t: t[2])
        y_min = min(p[2] for p in last_points); y_max = max(p[2] for p in last_points)
        ypad = (y_max - y_min or 1) * 0.02
        for i, (lab, d, v) in enumerate(last_points):
            x = pd.Timestamp(d) + pd.Timedelta(days=30)
            off = ((i % 6) - 3) * ypad
            plt.annotate(
                lab,
                xy=(d, v), xytext=(x, v + off), textcoords="data",
                fontsize=9, ha="left", va="center",
                bbox=dict(facecolor="white", edgecolor="#ddd", alpha=0.92, pad=1.6),
                arrowprops=dict(arrowstyle="-", color="#999", lw=0.8, alpha=0.85),
                zorder=6,
            )

    plt.title(title, fontsize=12, pad=10)
    plt.xlabel("Date"); plt.ylabel(ylabel)
    plt.grid(True, which="major", linestyle="--", alpha=0.3)
    plt.minorticks_on(); plt.grid(True, which="minor", linestyle=":", alpha=0.12)
    plt.legend(loc="center left", bbox_to_anchor=(1.02, 0.5), frameon=False)
    plt.tight_layout(); plt.savefig(outfile, bbox_inches="tight"); plt.close()

# ============================== Email ==============================
def table_to_html(df_fmt: pd.DataFrame, title: str) -> str:
    if df_fmt.empty:
        return f"<h3>{title}</h3><p><em>No data</em></p>"
    return (f"<h3>{title}</h3>" + df_fmt.to_html(escape=False, border=0, classes="zsum", justify="center"))

def save_csv(df_raw: pd.DataFrame, path: pathlib.Path):
    if not df_raw.empty:
        df_raw.to_csv(path, index=True)

def email_charts_and_tables(charts, tables_html_sections, csv_paths):
    subject = f"{SUBJECT_PREFIX} Trends – {datetime.now():%b %Y}"
    msg = MIMEMultipart("related")
    msg["Subject"] = subject
    msg["From"] = f"{FROM_NAME} <{EMAIL_USERNAME}>"
    msg["To"] = ", ".join(EMAIL_TO)

    imgs_html = []
    for label, path in charts:
        cid = pathlib.Path(path).stem
        imgs_html.append(
            f"<h3>{label}</h3>"
            f"<img src='cid:{cid}' style='max-width:100%;height:auto;border:1px solid #eee;border-radius:6px'/>"
        )

    body_html = (
        "<html><head><style>"
        ".zsum {font-family: Arial, sans-serif; font-size:12px; border-collapse:collapse;}"
        ".zsum th, .zsum td { padding:6px 8px; border-bottom:1px solid #eee; text-align:right; }"
        ".zsum th { position:sticky; top:0; background:#fafafa; text-align:center; }"
        ".zsum tr:hover td { background:#fcfcfc; }"
        ".zsum td:first-child, .zsum th:first-child { text-align:left; }"
        "</style></head><body>"
        + "".join(imgs_html)
        + "".join(tables_html_sections)
        + "</body></html>"
    )

    alt = MIMEMultipart("alternative")
    msg.attach(alt)
    alt.attach(MIMEText("Your monthly Zillow charts and summary tables are attached.", "plain"))
    alt.attach(MIMEText(body_html, "html"))

    for _, path in charts:
        with open(path, "rb") as f:
            img = MIMEImage(f.read())
            cid = pathlib.Path(path).stem
            img.add_header("Content-ID", f"<{cid}>")
            img.add_header("Content-Disposition", "inline", filename=pathlib.Path(path).name)
            msg.attach(img)

    for p in csv_paths:
        if not p: continue
        with open(p, "rb") as f:
            part = MIMEText(f.read().decode("utf-8"), "csv", "utf-8")
            part.add_header("Content-Disposition", "attachment", filename=pathlib.Path(p).name)
            msg.attach(part)

    context = ssl.create_default_context()
    if SMTP_MODE == "ssl":
        with smtplib.SMTP_SSL("smtp.gmail.com", 465, context=context) as s:
            s.login(EMAIL_USERNAME, APP_PWD)
            s.sendmail(EMAIL_USERNAME, EMAIL_TO, msg.as_string())
    else:
        with smtplib.SMTP("smtp.gmail.com", 587) as s:
            s.ehlo(); s.starttls(context=context); s.ehlo()
            s.login(EMAIL_USERNAME, APP_PWD)
            s.sendmail(EMAIL_USERNAME, EMAIL_TO, msg.as_string())
    print("[OK] Email sent with charts and summary tables.")

# ============================== Summary tables (County/Metro) ==============================
def month_floor(dt: pd.Timestamp) -> pd.Timestamp:
    return pd.Timestamp(dt.year, dt.month, 1)

def fmt_money(v):
    if pd.isna(v): return ""
    return f"${int(round(v, 0)):,}"

def fmt_pct(p):
    if pd.isna(p): return ""
    sign = "+" if p >= 0 else ""
    return f"{sign}{p:.1f}%"

def series_from_dfreg(df_reg: pd.DataFrame) -> pd.Series:
    s = df_reg.groupby("date")["value"].mean().sort_index()
    s.index = s.index.map(month_floor)
    return s

def build_summary_for_dataset(series_map: dict[str, pd.Series], last_n_months=12):
    if not series_map: return (pd.DataFrame(), pd.DataFrame())
    latest = max((s.dropna().index.max() for s in series_map.values() if not s.dropna().empty), default=None)
    if latest is None: return (pd.DataFrame(), pd.DataFrame())
    latest = month_floor(pd.Timestamp(latest))
    months = [month_floor(latest - pd.DateOffset(months=i)) for i in range(last_n_months - 1, -1, -1)]
    month_labels = [m.strftime("%Y-%m") for m in months]

    rows = []
    for label, s in series_map.items():
        s = s.copy(); s.index = s.index.map(month_floor)
        row = [s.get(m, pd.NA) for m in months]
        v_now = s.get(latest, pd.NA)
        v_prev = s.get(month_floor(latest - pd.DateOffset(years=1)), pd.NA)
        yoy = ((v_now / v_prev - 1) * 100) if (pd.notna(v_now) and pd.notna(v_prev) and v_prev != 0) else pd.NA
        rows.append(row + [yoy])

    raw = pd.DataFrame(rows, index=list(series_map.keys()), columns=month_labels + ["YoY %"])
    fmt = raw.copy()
    for c in month_labels: fmt[c] = fmt[c].map(fmt_money)
    fmt["YoY %"] = fmt["YoY %"].map(fmt_pct)
    return raw, fmt

# ========================== Investment metrics (Metro) ==========================
def _latest_common_month_3(s_price: pd.Series, s_rent: pd.Series, s_pay: pd.Series):
    if s_price.empty or s_rent.empty or s_pay.empty:
        return None
    lp = month_floor(pd.Timestamp(s_price.dropna().index.max()))
    lr = month_floor(pd.Timestamp(s_rent.dropna().index.max()))
    lq = month_floor(pd.Timestamp(s_pay.dropna().index.max()))
    latest = min(lp, lr, lq)
    return latest

def _yoy_pct(s: pd.Series, latest_month: pd.Timestamp):
    if s is None or s.empty or latest_month is None:
        return pd.NA
    s2 = s.copy(); s2.index = s2.index.map(month_floor)
    v_now = s2.get(latest_month, pd.NA)
    v_prev = s2.get(month_floor(latest_month - pd.DateOffset(years=1)), pd.NA)
    if pd.isna(v_now) or pd.isna(v_prev) or v_prev == 0:
        return pd.NA
    return (v_now / v_prev - 1) * 100.0

def build_metro_investment_tables(areas: list[dict], out_dir: pathlib.Path) -> tuple[str, str]:
    rows_rental, rows_flip = [], []

    for area in areas:
        metro = area["metro"]

        s_price = series_for("zhvi", "Metro", metro)
        s_rent  = series_for("zori", "Metro", metro)
        s_pay   = series_for("payment", "Metro", metro)

        latest = _latest_common_month_3(s_price, s_rent, s_pay)
        if latest is None:
            print(f"[WARN] Skipping metrics for {metro}: could not align latest month across series.")
            continue

        _p = pd.Series(s_price).rename_axis("date").get(latest, pd.NA)
        _r = pd.Series(s_rent ).rename_axis("date").get(latest, pd.NA)
        _y = pd.Series(s_pay  ).rename_axis("date").get(latest, pd.NA)

        price = float(_p) if pd.notna(_p) else pd.NA
        rent  = float(_r) if pd.notna(_r) else pd.NA
        pay   = float(_y) if pd.notna(_y) else pd.NA

        price_yoy = _yoy_pct(s_price, latest)
        rent_yoy  = _yoy_pct(s_rent , latest)

        rent_price_ratio = (rent / price) if (pd.notna(rent) and pd.notna(price) and price) else pd.NA
        gross_yield = (12 * rent / price) * 100 if (pd.notna(rent) and pd.notna(price) and price) else pd.NA
        opex_mo = OPEX_RATE * rent if pd.notna(rent) else pd.NA
        noi_mo  = (rent - opex_mo) if (pd.notna(rent) and pd.notna(opex_mo)) else pd.NA
        mcr = (rent / pay) if (pd.notna(rent) and pd.notna(pay) and pay) else pd.NA
        dscr = (noi_mo / pay) if (pd.notna(noi_mo) and pd.notna(pay) and pay) else pd.NA
        cap_proxy = (12 * noi_mo / price) * 100 if (pd.notna(noi_mo) and pd.notna(price) and price) else pd.NA
        cf_mo = (noi_mo - pay) if (pd.notna(noi_mo) and pd.notna(pay)) else pd.NA
        cash_invested = (DPCT + CLOSING_COST_RATE) * price if (pd.notna(price) and price) else pd.NA
        coc = (12 * cf_mo / cash_invested) * 100 if (pd.notna(cf_mo) and pd.notna(cash_invested) and cash_invested) else pd.NA

        rows_rental.append({
            "Metro": metro, "AsOf": latest.strftime("%Y-%m"),
            "ZHVI_price": price, "ZORI_rent": rent, "PAYMENT_20%down": pay,
            "OPEX_RATE": OPEX_RATE, "DOWNPAY_PCT": DPCT, "CLOSING_COST_RATE": CLOSING_COST_RATE,
            "Rent/Price": rent_price_ratio, "GrossYield_%": gross_yield, "Opex_Mo": opex_mo,
            "NOI_Mo": noi_mo, "MCR_Rent/Payment": mcr, "DSCR_NOI/Payment": dscr,
            "Cap_Proxy_%": cap_proxy, "CF_Mo": cf_mo, "Cash_Invested": cash_invested, "CoC_%": coc,
            "Price_YoY_%": price_yoy, "Rent_YoY_%": rent_yoy,
        })

        if pd.notna(price_yoy) and pd.notna(price):
            pm_perc_window = (float(price_yoy) / 12.0) * HOLD_MONTHS
            price_momentum_usd = price * (pm_perc_window / 100.0)
        else:
            pm_perc_window = pd.NA; price_momentum_usd = pd.NA

        carrying_cost_usd = (pay * HOLD_MONTHS) if pd.notna(pay) else pd.NA
        cri = (carrying_cost_usd / price) if (pd.notna(carrying_cost_usd) and pd.notna(price) and price) else pd.NA
        flip_edge_usd = (price_momentum_usd - carrying_cost_usd) if (pd.notna(price_momentum_usd) and pd.notna(carrying_cost_usd)) else pd.NA

        rows_flip.append({
            "Metro": metro, "AsOf": latest.strftime("%Y-%m"),
            "ZHVI_price": price, "PAYMENT_20%down": pay, "Hold_Months": HOLD_MONTHS, "Price_YoY_%": price_yoy,
            "PM_%_Window": pm_perc_window, "PM_USD_Window": price_momentum_usd,
            "CarryingCost_USD": carrying_cost_usd, "CRI_Carrying/Price": cri,
            "FlipEdge_USD_(PM_minus_Carrying)": flip_edge_usd,
        })

    rental_df = pd.DataFrame(rows_rental)
    flip_df   = pd.DataFrame(rows_flip)

    def _pct_rank(s, ascending=True):
        return s.rank(pct=True, ascending=ascending)

    if not rental_df.empty:
        rental_df["Rank_MCR"] = _pct_rank(rental_df["MCR_Rent/Payment"], ascending=False)
        rental_df["Rank_DSCR"] = _pct_rank(rental_df["DSCR_NOI/Payment"], ascending=False)
        rental_df["Rank_CapProxy"] = _pct_rank(rental_df["Cap_Proxy_%"], ascending=False)
        rental_df["Rank_CoC"] = _pct_rank(rental_df["CoC_%"], ascending=False)
        rental_df["Score_Rental"] = rental_df[["Rank_MCR", "Rank_DSCR", "Rank_CapProxy", "Rank_CoC"]].mean(axis=1)

    if not flip_df.empty:
        flip_df["Rank_PM_USD"] = _pct_rank(flip_df["PM_USD_Window"], ascending=False)
        flip_df["Rank_CRI"] = _pct_rank(flip_df["CRI_Carrying/Price"], ascending=True)
        flip_df["Rank_Edge"] = _pct_rank(flip_df["FlipEdge_USD_(PM_minus_Carrying)"], ascending=False)
        flip_df["Score_Flip"] = flip_df[["Rank_PM_USD", "Rank_CRI", "Rank_Edge"]].mean(axis=1)

    rental_path = str(out_dir / "rental_scores_detailed.csv")
    flip_path   = str(out_dir / "flip_scores_detailed.csv")
    if not rental_df.empty: rental_df.to_csv(rental_path, index=False)
    if not flip_df.empty:   flip_df.to_csv(flip_path, index=False)

    return rental_path if not rental_df.empty else "", flip_path if not flip_df.empty else ""

# =============================== ZIP Choropleth Heatmaps (NEW) ===============================
def _ensure_packages_for_maps():
    try:
        import geopandas as gpd  # noqa: F401
        import contextily as cx  # noqa: F401
        from shapely.geometry import Point  # noqa: F401
    except Exception:
        import subprocess, sys
        pkgs = ["geopandas", "contextily", "pyproj", "shapely", "rtree", "adjustText"]
        subprocess.run([sys.executable, "-m", "pip", "install", "-q"] + pkgs, check=False)

def _download_and_extract(url: str, dest_dir: pathlib.Path) -> pathlib.Path:
    dest_dir.mkdir(parents=True, exist_ok=True)
    import zipfile, requests
    zpath = dest_dir / url.split("/")[-1]
    if not zpath.exists():
        r = requests.get(url, timeout=60)
        r.raise_for_status()
        zpath.write_bytes(r.content)
    extract_dir = dest_dir / zpath.stem
    if not extract_dir.exists():
        with zipfile.ZipFile(zpath, "r") as zf:
            zf.extractall(extract_dir)
    return extract_dir

def _load_tiger_layers(cache_dir: pathlib.Path):
    _ensure_packages_for_maps()
    import geopandas as gpd
    county_dir = _download_and_extract(
        "https://www2.census.gov/geo/tiger/TIGER2024/COUNTY/tl_2024_us_county.zip", cache_dir
    )
    zcta_dir = _download_and_extract(
        "https://www2.census.gov/geo/tiger/TIGER2024/ZCTA520/tl_2024_us_zcta520.zip", cache_dir
    )
    gdf_county = gpd.read_file(county_dir)
    gdf_zcta = gpd.read_file(zcta_dir)
    return gdf_county, gdf_zcta

_STATE_ABBR_TO_FIPS = {
    "AL": "01", "AK": "02", "AZ": "04", "AR": "05", "CA": "06", "CO": "08", "CT": "09", "DE": "10", "DC": "11",
    "FL": "12", "GA": "13", "HI": "15", "ID": "16", "IL": "17", "IN": "18", "IA": "19", "KS": "20", "KY": "21",
    "LA": "22", "ME": "23", "MD": "24", "MA": "25", "MI": "26", "MN": "27", "MS": "28", "MO": "29", "MT": "30",
    "NE": "31", "NV": "32", "NH": "33", "NJ": "34", "NM": "35", "NY": "36", "NC": "37", "ND": "38", "OH": "39",
    "OK": "40", "OR": "41", "PA": "42", "RI": "44", "SC": "45", "SD": "46", "TN": "47", "TX": "48", "UT": "49",
    "VT": "50", "VA": "51", "WA": "53", "WV": "54", "WI": "55", "WY": "56", "PR": "72"
}

def _parse_county_state(area_county: str):
    parts = [p.strip() for p in area_county.split(",")]
    county = parts[0]
    state_abbr = parts[1] if len(parts) > 1 else ""
    return county, state_abbr

def _compute_yoy_from_wide(df_wide: pd.DataFrame) -> pd.DataFrame:
    date_cols = [c for c in df_wide.columns if re.match(r"\d{4}-\d{2}", str(c))]
    if len(date_cols) < 13:
        return pd.DataFrame(columns=["RegionName", "yoy_pct"])
    date_cols_sorted = sorted(date_cols)
    latest, last_year = date_cols_sorted[-1], date_cols_sorted[-13]
    keep_cols = [c for c in ["RegionName", "StateName", "State", "CountyName", "Metro"] if c in df_wide.columns]
    out = df_wide[keep_cols].copy()
    out["latest"]  = pd.to_numeric(df_wide[latest], errors="coerce")
    out["yearago"] = pd.to_numeric(df_wide[last_year], errors="coerce")
    out["yoy_pct"] = (out["latest"] / out["yearago"] - 1.0) * 100.0
    return out

def _load_zip_wide(dataset_key: str) -> pd.DataFrame:
    url = find_csv_url(dataset_key, "Zip")
    try:
        return load_wide_csv(url)
    except Exception as e:
        print(f"[WARN] Failed to load {dataset_key} ZIP CSV from {url}: {e}")
        fallback = FALLBACK_FILES.get((dataset_key, "Zip"), "")
        if fallback:
            try:
                return pd.read_csv(fallback, low_memory=False)
            except Exception as e2:
                print(f"[WARN] Fallback also failed: {e2}")
        return pd.DataFrame()

def _build_heatmap_for_area(area: dict, zhvi_zip: pd.DataFrame, zori_zip: pd.DataFrame, out_dir: pathlib.Path):
    _ensure_packages_for_maps()
    import geopandas as gpd, matplotlib.pyplot as plt, matplotlib.patheffects as pe, numpy as np, contextily as cx

    county_name, state_abbr = _parse_county_state(area["county"])
    fips = _STATE_ABBR_TO_FIPS.get(state_abbr, None)
    if not fips:
        print(f"[WARN] Unknown state for {area['county']}. Skipping heatmaps.")
        return []

    gdf_county, gdf_zcta = _load_tiger_layers(out_dir / "_mapcache")

    gdf_c = gdf_county[
        (gdf_county["STATEFP"] == fips) & (gdf_county["NAME"].str.fullmatch(county_name.replace(" County", "")))
    ]
    if gdf_c.empty:
        gdf_c = gdf_county[(gdf_county["STATEFP"] == fips) &
                           (gdf_county["NAMELSAD"].str.contains(county_name.split()[0], case=False, na=False))]
    if gdf_c.empty:
        print(f"[WARN] County boundary not found for {area['county']}")
        return []

    county_poly = gdf_c.to_crs(epsg=3857).unary_union

    zhvi_yoy = _compute_yoy_from_wide(zhvi_zip)
    zori_yoy = _compute_yoy_from_wide(zori_zip)

    for df in (zhvi_yoy, zori_yoy):
        df["zip"] = df["RegionName"].astype(str).str.zfill(5)
        if "CountyName" in df.columns: df["CountyName"] = df["CountyName"].astype(str)
        if "State" in df.columns: df["State"] = df["State"].astype(str)

    county_token = county_name.split()[0]
    zhvi_c = zhvi_yoy[
        (zhvi_yoy.get("CountyName", "").str.contains(county_token, case=False, na=False)) &
        (zhvi_yoy.get("State", "") == state_abbr)
    ]
    zori_c = zori_yoy[
        (zori_yoy.get("CountyName", "").str.contains(county_token, case=False, na=False)) &
        (zori_yoy.get("State", "") == state_abbr)
    ]

    gdf_zip = gdf_zcta.to_crs(epsg=3857).copy()
    gdf_zip["zip"] = gdf_zip["ZCTA5CE20"].astype(str)
    gdf_zip = gdf_zip[gdf_zip.geometry.intersects(county_poly.buffer(0))]
    gdf_zip = gdf_zip[gdf_zip.geometry.centroid.within(county_poly)]

    def _plot(gdf_zip, gdf_c, area, out_dir, layer_df, metric_name: str, cmap="Reds"):
        from matplotlib.colors import Normalize
        from adjustText import adjust_text
        import numpy as np

        g = gdf_zip.merge(layer_df[["zip", "yoy_pct"]], on="zip", how="left")
        if g["yoy_pct"].notna().sum() == 0:
            return None, None

        pos = g["yoy_pct"].astype(float).copy()
        pos[pos < 0] = 0.0
        pos_vals = pos[pos > 0]
        vmax = float(np.percentile(pos_vals, 95)) if len(pos_vals) else 1.0
        vmin = 0.0
        norm = Normalize(vmin=vmin, vmax=vmax)

        facecolors = []
        for val in g["yoy_pct"]:
            try:
                valf = float(val)
            except Exception:
                valf = float("nan")
            if (valf == valf) and (valf > 0):
                facecolors.append(plt.cm.Reds(norm(valf)))
            else:
                facecolors.append("#f0f0f0")

        fig, ax = plt.subplots(figsize=(10, 10), dpi=180)
        g.plot(ax=ax, color=facecolors, linewidth=0.4, edgecolor="#666")
        gdf_c.to_crs(epsg=3857).boundary.plot(ax=ax, color="#222", linewidth=1.0)

        sm = plt.cm.ScalarMappable(cmap="Reds", norm=norm)
        sm.set_array([])
        cbar = plt.colorbar(sm, ax=ax, fraction=0.030, pad=0.02)
        cbar.set_label(f"{metric_name} YoY % (positives only)", rotation=90)

        g_cent = g.copy()
        g_cent["centroid"] = g_cent.geometry.centroid
        for _, r in g_cent.iterrows():
            x, y = r["centroid"].x, r["centroid"].y
            ax.text(
                x, y, str(r["zip"]), fontsize=6, ha="center", va="center", alpha=0.85,
                color="#111", path_effects=[pe.withStroke(linewidth=2, foreground="white", alpha=0.85)]
            )

        N = 30
        min_area = 1.5e6
        min_abs_yoy = 0.5
        g_rank = g.copy()
        g_rank["abs_yoy"] = g_rank["yoy_pct"].abs()
        g_rank = g_rank[(g_rank["abs_yoy"] == g_rank["abs_yoy"])]
        g_rank = g_rank[g_rank.geometry.area >= min_area]
        g_rank = g_rank[g_rank["abs_yoy"] >= min_abs_yoy]
        g_rank = g_rank.sort_values("abs_yoy", ascending=False).head(N).copy()
        g_rank["centroid"] = g_rank.geometry.centroid

        texts = []
        for _, r in g_rank.iterrows():
            x, y = r["centroid"].x, r["centroid"].y
            label = f"{r['zip']}  {r['yoy_pct']:+.1f}%"
            txt = ax.text(
                x, y, label, fontsize=7.5, ha="center", va="center",
                path_effects=[pe.withStroke(linewidth=2.2, foreground="white", alpha=0.95)]
            )
            texts.append(txt)

        adjust_text(
            texts, ax=ax,
            expand_points=(1.10, 1.25), expand_text=(1.05, 1.25),
            force_text=(0.10, 0.12), lim=100,
            arrowprops=dict(arrowstyle="-", lw=0.8, color="#555", alpha=0.95, shrinkA=0, shrinkB=0)
        )

        ax.set_axis_off()
        cx.add_basemap(ax, source=cx.providers.CartoDB.Positron, attribution_size=6)
        ax.set_title(f"{area['name']} – {metric_name} YoY by ZIP (reds = higher +YoY, gray = ≤0)", fontsize=13)
        fname = out_dir / f"heatmap_{area['name'].replace(' ', '_')}_{metric_name.lower()}_yoy_by_zip.png"
        fig.tight_layout()
        fig.savefig(fname, bbox_inches="tight")
        plt.close(fig)
        return str(fname), g

    paths = []
    p1, _ = _plot(gdf_zip, gdf_c, area, out_dir, zhvi_c, "Value")
    if p1: paths.append(("ZIP Heatmap — Value YoY", p1))
    p2, _ = _plot(gdf_zip, gdf_c, area, out_dir, zori_c, "Rent", cmap="plasma")
    if p2: paths.append(("ZIP Heatmap — Rent YoY", p2))
    return paths

def build_and_attach_zip_heatmaps(areas, out_dir: pathlib.Path, charts_list: list):
    try:
        zhvi_zip = _load_zip_wide("zhvi")
        zori_zip = _load_zip_wide("zori")
        if zhvi_zip.empty or zori_zip.empty:
            print("[WARN] ZIP CSVs missing; skipping heatmaps.")
            return
        for area in areas:
            hm = _build_heatmap_for_area(area, zhvi_zip, zori_zip, out_dir)
            charts_list.extend(hm)
    except Exception as e:
        print(f"[WARN] Heatmap generation failed: {e}")

# =========================== SMART RELEASE GUARD (month-advance only) ===========================
def _latest_month_in_wide(df_wide: pd.DataFrame) -> str | None:
    if df_wide is None or df_wide.empty:
        return None
    date_cols = [c for c in df_wide.columns if re.fullmatch(r"\d{4}-\d{2}", str(c))]
    if not date_cols:
        date_cols = [c for c in df_wide.columns if re.fullmatch(r"\d{4}-\d{2}-\d{2}", str(c))]
        if not date_cols:
            return None
    latest = sorted(date_cols)[-1]
    try:
        dt = parse_date(latest)
        return f"{dt.year:04d}-{dt.month:02d}"
    except Exception:
        return latest[:7] if len(latest) >= 7 else None

def _light_fetch_latest_months_and_headers() -> dict:
    """Fetch URLs and HEAD meta for three key files, and read just enough to determine latest month."""
    keys = [
        ("zhvi", "Zip"),
        ("zori", "Zip"),
        ("payment", "Metro"),
    ]
    info = {}
    for ds, lvl in keys:
        url = find_csv_url(ds, lvl)
        meta = _head_meta(url)
        try:
            wide = load_wide_csv(url)
            latest = _latest_month_in_wide(wide)
        except Exception as e:
            latest = None
            meta["error_get"] = str(e)
        info[f"{ds}_{lvl.lower()}"] = {"url": url, "latest_month": latest, **meta}
    return info

def _is_new_release(stamp: dict, probe: dict) -> tuple[bool, str]:
    """
    TRUE only if the latest YYYY-MM advanced beyond last_sent.
    First run (no stamp) -> do NOT send (unless FORCE_SEND=1).
    """
    if os.getenv("FORCE_SEND", "").strip() == "1":
        return True, "FORCE_SEND=1"

    last_sent = (stamp or {}).get("last_sent")
    if not last_sent:
        return False, "first run without stamp (skipping by default)"

    advanced_reasons = []
    for k, cur in probe.items():
        latest = (cur or {}).get("latest_month")
        if latest and latest > last_sent:
            advanced_reasons.append(f"{k} advanced to {latest}")

    if advanced_reasons:
        return True, "; ".join(advanced_reasons)

    return False, "no new month detected"

# =============================== Main ===============================
def main():
    warnings.filterwarnings("ignore")
    out_dir = pathlib.Path(OUT_DIR)
    out_dir.mkdir(parents=True, exist_ok=True)

    # ---- SMART RELEASE PROBE (fast) ----
    # Option A: track stamp in repo under ./state/_last_sent.json
    stamp_path = str(pathlib.Path("state") / "_last_sent.json")
    prev = _read_stamp(stamp_path)
    probe = _light_fetch_latest_months_and_headers()
    should_run, reason = _is_new_release(prev, probe)

    if not should_run:
        print(f"[INFO] No new Zillow data detected — {reason}. Exiting.")
        return
    else:
        print(f"[INFO] Proceeding — {reason}")

    # Prefetch full long-format frames for processing
    prefetch_all()

    # ---- RUN-ONCE-PER-NEW-MONTH GUARD (based on data actually loaded) ----
    asof = _latest_available_month_for_guard()
    if not asof:
        print("[INFO] No latest month detected yet; exiting.")
        return

    # Proceed to generate all outputs
    charts = []
    csv_paths = []
    series_catalog = {"zhvi": {}, "zori": {}}
    html_sections = []

    for dataset in ("zhvi", "zori"):
        ylabel = "Typical Home Value ($)" if dataset == "zhvi" else "Typical Rent ($)"
        fmt_fn = fmt_home_value if dataset == "zhvi" else fmt_rent_exact

        for area in AREAS:
            # 1) County vs Metro overlay
            s_county = series_for(dataset, "County", area["county"])
            s_metro  = series_for(dataset, "Metro",  area["metro"])

            layers, labels = [], []
            if not s_county.empty:
                layers.append(s_county); labels.append(f"{area['county']} (County)")
                series_catalog[dataset][f"{area['name']} — County"] = s_county
            if not s_metro.empty:
                layers.append(s_metro); labels.append(f"{area['metro']} (Metro)")
                series_catalog[dataset][f"{area['name']} — Metro"] = s_metro

            if len(layers) < 2:
                have = ', '.join(labels) if labels else 'none'
                print(f"[WARN] Missing one layer for {area['name']} ({dataset}). Have: {have}")

            if layers:
                safe_name = re.sub(r"[^A-Za-z0-9\-]+", "_", f"overlay_{dataset}_{area['name']}_County_vs_Metro")
                out_path = str(out_dir / f"{safe_name}.png")
                title = f"{area['name']} — County vs Metro ({dataset.upper()})"
                plot_overlay_chart(layers, labels, title, ylabel, out_path, annotate_index=0, fmt_fn=fmt_fn)
                charts.append((title, out_path))

            # 2) ZIP plots + metrics + last-12 CSVs
            zip_map = zip_series_by_metro(dataset, area["metro"])
            if not zip_map:
                print(f"[WARN] No ZIP series found for {area['metro']} ({dataset}).")
                continue

            zdf = zip_metrics(zip_map)
            if zdf.empty:
                print(f"[WARN] No ZIP metrics computed for {area['metro']} ({dataset}).")
                continue

            zdf_ok = zdf[zdf["n"] >= ZIP_RANK_MIN_MONTHS].copy()
            if zdf_ok.empty:
                print(f"[WARN] Not enough ZIP history for ranking in {area['metro']} ({dataset}).")
            yoy_map = dict(zip(zdf_ok["zip"], zdf_ok["yoy_pct"]))

            top_up   = zdf_ok.sort_values("yoy_pct", ascending=False).head(ZIP_TOP_UP)["zip"].tolist()
            top_down = zdf_ok.sort_values("yoy_pct", ascending=True ).head(ZIP_TOP_DOWN)["zip"].tolist()

            if top_up:
                safe_up = re.sub(r"[^A-Za-z0-9\-]+", "_", f"zipTopUp_{dataset}_{area['name']}")
                out_up = str(out_dir / f"{safe_up}.png")
                title_up = f"{area['name']} — ZIPs Top {ZIP_TOP_UP} YoY ↑ ({dataset.upper()})"
                plot_ranked_zips(zip_map, title_up, ylabel, out_up, pick_zips=top_up, yoy_map=yoy_map,
                                 ma_months=ZIP_MA_MONTHS)
                charts.append((title_up, out_up))
            if top_down:
                safe_dn = re.sub(r"[^A-Za-z0-9\-]+", "_", f"zipTopDown_{dataset}_{area['name']}")
                out_dn = str(out_dir / f"{safe_dn}.png")
                title_dn = f"{area['name']} — ZIPs Bottom {ZIP_TOP_DOWN} YoY ↓ ({dataset.upper()})"
                plot_ranked_zips(zip_map, title_dn, ylabel, out_dn, pick_zips=top_down, yoy_map=yoy_map,
                                 ma_months=ZIP_MA_MONTHS)
                charts.append((title_dn, out_dn))

            # 12-month ZIP backup table (CSV attachment only)
            raw12, _fmt12 = build_zip_last12_table(zip_map)
            if not raw12.empty:
                safe_area = slugify_name(area['name'])
                zcsv = out_dir / f"zip_last12_{dataset}_{safe_area}.csv"
                raw12.to_csv(zcsv)
                csv_paths.append(str(zcsv))

            # metrics CSV attachment
            safe_area = slugify_name(area['name'])
            zmet_csv = out_dir / f"zip_metrics_{dataset}_{safe_area}.csv"
            zdf.sort_values("yoy_pct", ascending=False).to_csv(zmet_csv, index=False)
            csv_paths.append(str(zmet_csv))

    # -------- Summary tables (shown in body) --------
    for ds_key, ds_title in [
        ("zhvi", "Summary – ZHVI (Last 12 Months)"),
        ("zori", "Summary – ZORI (Last 12 Months)")
    ]:
        raw, fmt = build_summary_for_dataset(series_catalog.get(ds_key, {}), SUMMARY_LAST_N_MONTHS)
        if not raw.empty:
            csv_path = pathlib.Path(OUT_DIR) / f"summary_{ds_key}_last12.csv"
            save_csv(raw, csv_path)
            csv_paths.append(str(csv_path))
            html_sections.append(table_to_html(fmt, ds_title))

    # -------- Investment metrics (Metro) --------
    rental_csv, flip_csv = build_metro_investment_tables(AREAS, out_dir)
    if rental_csv: csv_paths.append(rental_csv)
    if flip_csv:   csv_paths.append(flip_csv)

    # -------- ZIP Choropleth Heatmaps --------
    build_and_attach_zip_heatmaps(AREAS, out_dir, charts)

    # Email all results, then record extended stamp
    if charts or html_sections:
        email_charts_and_tables(charts, html_sections, csv_paths)
        stamp_meta = {
            "head_meta": probe,  # store url + last-modified + etag + latest_month seen per key file (for reference)
        }
        _write_sent_extended(asof, stamp_path, stamp_meta)
    else:
        print("[WARN] No charts or tables generated.")

if __name__ == "__main__":
    main()
