"""
NSE Swing Trading Breakout Screener
====================================

WHAT THIS IS
A rule-based scanner that flags 5-day-high breakout setups on the NSE
watchlist below, sizes each trade by fixed fractional risk, and (optionally)
pushes alerts to Telegram.

WHAT THIS IS NOT
This is not financial advice and it is not a guaranteed-profit system. No
screener can make your capital "safe" — markets can gap, stop-losses can
slip, and any historical edge can stop working. What this script CAN do is
enforce discipline: risk a small, fixed % of capital per idea, avoid
obviously bad setups (illiquid, overheated, counter-trend), and keep a
written record of every signal so you can judge the system honestly over
time. Please paper-trade or use very small size for at least a few dozen
signals before trusting it with real capital, and never risk money you
can't afford to lose.

BUG FIXED IN THIS VERSION
`Vol_Avg_5` (the 5-day average volume used for the "volume confirmation"
filter) was computed as `df['Volume'].rolling(5).mean()` — i.e. it INCLUDED
today's own volume inside its own average, while the price-based filters
(`Recent_Max` / `Recent_Min`) correctly excluded today via `.shift(1)`.
That inconsistency quietly weakens the volume filter (a volume spike drags
its own baseline up, making "above average" harder to trigger honestly) and
made the volume check inconsistent with the price checks it's paired with.
Fixed by shifting Volume the same way: `df['Volume'].shift(1).rolling(5).mean()`.

OTHER CHANGES (see inline comments for the "why" of each):
  1. Intraday volume is now time-of-day normalized instead of compared raw,
     since a scan at 10:00 AM will always look "low volume" vs a full day's
     average otherwise (that was producing false negatives all morning).
  2. Added a 50-EMA trend filter and RSI band so we don't buy breakouts that
     are counter-trend or already overheated.
  3. Added a liquidity floor (avg. daily turnover) and a minimum price floor
     to keep the scanner out of stocks that are hard to exit cleanly.
  4. Added a "how extended is this breakout" cap so we don't chase moves
     that already ran too far past the trigger level.
  5. Position sizing now also caps position value at a max % of total
     capital (diversification), on top of the existing risk-based and
     cash-based caps.
  6. Every signal is scored and ranked, and only the top N per scan are
     surfaced — with a 50k account you can only actually take a couple of
     trades at once, so the tool now tells you which ones are best rather
     than firehosing every technically-valid match.
  7. Signals are appended to a local CSV (signals_log.csv) so you can review
     win rate / R multiples later instead of trusting the system blindly.
  8. yfinance downloads now retry with backoff (Yahoo rate-limits are common
     with 400+ tickers) instead of silently dropping a symbol on one hiccup.
  9. Telegram alerts now match a richer template: sector, an "entry tracker"
     showing the ideal breakout trigger you may have missed and the next
     pullback zone to watch if you did, a same-day sector-concentration
     warning, and capital that's actually left after earlier signals in the
     same scan (sized sequentially, not as if each trade had the full
     account to itself).
"""

import sys
import os
import csv
import json
import time
import argparse
import requests
from datetime import datetime
import pytz
import pandas as pd
import yfinance as yf
from concurrent.futures import ThreadPoolExecutor, as_completed

# ==============================================================================
# ⚙️ CONFIGURATION ZONE (UPDATE THESE VALUES)
# ==============================================================================
# NEW: reads from environment variables first (so this is safe to run on a
# PUBLIC GitHub repo via GitHub Actions, with real values stored as encrypted
# repo Secrets) and falls back to the literal strings below for running on
# your own PC, where the file itself isn't shared with anyone.
TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN", "PUT_YOUR_BOT_TOKEN_HERE")
TELEGRAM_CHAT_ID = os.environ.get("TELEGRAM_CHAT_ID", "PUT_YOUR_CHAT_ID_HERE")

# 💰 FIXED RISK MANAGEMENT SETTINGS
TOTAL_TRADING_CAPITAL = 50000.00   # Hardcoded fixed trading account size in INR
MAX_ACCOUNT_RISK_PCT = 1.0         # Max % of total capital to risk per trade (1.0% = ₹500)
MAX_POSITION_PCT_OF_CAPITAL = 25.0 # NEW: never put more than this % of capital in one name,
                                    # even if the risk math alone would allow more shares.
                                    # Protects against a single low-ATR stock eating your
                                    # whole account "safely" on a risk basis but not on a
                                    # concentration basis.
MAX_SIGNALS_PER_SCAN = 5           # NEW: only surface/alert the top-N ranked setups per scan.

# 🔁 SCAN SETTINGS
SCAN_INTERVAL_SECONDS = 300        # How often to rescan the watchlist while market is open
MAX_WORKERS = 8                    # Parallel download threads (kept modest to reduce Yahoo rate-limits)
DOWNLOAD_RETRIES = 3               # NEW: retry failed/empty downloads before giving up on a symbol
DOWNLOAD_RETRY_BACKOFF_SEC = 2     # NEW: base backoff between retries (grows linearly)

# 📈 SIGNAL / FILTER SETTINGS
ATR_STOP_MULTIPLIER = 1.5          # Stop-loss distance = ATR_14 * this multiplier
REWARD_RISK_RATIO = 2.0            # Fixed target = entry + (risk_per_share * this)
BREAKOUT_BUFFER_PCT = 0.2          # NEW: require close to clear the 5-day high by this % (noise filter)
MAX_EXTENSION_PCT = 5.0            # NEW: skip if close is already this far above the breakout level
VOLUME_CONFIRM_MULTIPLIER = 1.2    # NEW: require (normalized) volume >= 1.2x the 5-day average, not just ">"
RSI_PERIOD = 14
RSI_MIN = 50.0                     # NEW: want some momentum behind the breakout...
RSI_MAX = 75.0                     # ...but not already in blow-off / overbought territory
MIN_STOCK_PRICE = 50.0             # NEW: avoid ultra-low-priced / illiquid-tick stocks
MIN_AVG_DAILY_TURNOVER_INR = 3_00_00_000  # NEW: ₹3 Cr/day avg turnover floor, so exits aren't slippage traps

# 🧪 TEST / DRY-RUN SETTINGS
TEST_SAMPLE_SIZE = 15              # How many symbols to scan in --test mode (keeps it fast)

# 🗒️ LOGGING / CACHING
SIGNAL_LOG_FILE = "signals_log.csv"
SECTOR_CACHE_FILE = "sector_cache.json"   # NEW: sector lookups are cached to disk so we
                                           # only hit yfinance's info endpoint once per
                                           # symbol ever, not once per scan.

# ==============================================================================
# 📋 WATCHLIST
# ==============================================================================
RAW_SYMBOLS = [
    "360ONE", "3MINDIA", "ABB", "ACC", "ACMESOLAR", "AIAENG", "APLAPOLLO", "AUBANK", "AWL", "AADHARHFC",
    "AARTIIND", "AAVAS", "ABBOTINDIA", "ACE", "ACUTAAS", "ADANIENSOL", "ADANIENT", "ADANIGREEN", "ADANIPORTS",
    "ADANIPOWER", "ATGL", "ABCAPITAL", "ABFRL", "ABLBL", "ABREL", "ABSLAMC", "CPPLUS", "AEGISLOG", "AEGISVOPAK",
    "AFCONS", "AFFLE", "AJANTPHARM", "ALKEM", "ABDL", "ARE&M", "AMBER", "AMBUJACEM", "ANANDRATHI", "ANANTRAJ",
    "ANGELONE", "ANTHEM", "ANURAS", "APARINDS", "APOLLOHOSP", "APOLLOTYRE", "APTUS", "ASAHIINDIA", "ASHOKLEY",
    "ASIANPAINT", "ASTERDM", "ASTRAL", "ATHERENERG", "ATUL", "AUROPHARMA", "AIIL", "DMART", "AXISBANK", "BEML",
    "BLS", "BSE", "BAJAJ-AUTO", "BAJFINANCE", "BAJAJFINSV", "BAJAJHLDNG", "BAJAJHFL", "BALKRISIND", "BALRAMCHIN",
    "BANDHANBNK", "BANKBARODA", "BANKINDIA", "MAHABANK", "BATAINDIA", "BAYERCROP", "BELRISE", "BERGEPAINT", "BDL",
    "BEL", "BHARATFORG", "BHEL", "BPCL", "BHARTIARTL", "BHARTIHEXA", "BIKAJI", "GROWW", "BIOCON", "BSOFT",
    "BLUEDART", "BLUEJET", "BLUESTARCO", "BBTC", "BOSCHLTD", "FIRSTCRY", "BRIGADE", "BRITANNIA", "MAPMYINDIA",
    "CCL", "CESC", "CGPOWER", "CIEINDIA", "CRISIL", "CANFINHOME", "CANBK", "CANHLIFE", "CAPLIPOINT", "CGCL",
    "CARBORUNIV", "CARTRADE", "CASTROLIND", "CEATLTD", "CEMPRO", "CENTRALBK", "CDSL", "CHALET", "CHAMBLFERT",
    "CHENNPETRO", "CHOICEIN", "CHOLAHLDNG", "CHOLAFIN", "CIPLA", "CUB", "CLEAN", "COALINDIA", "COCHINSHIP",
    "COFORGE", "COHANCE", "COLPAL", "CAMS", "CONCORDBIO", "CONCOR", "COROMANDEL", "CRAFTSMAN", "CREDITACC",
    "CROMPTON", "CUMMINSIND", "CYIENT", "DCMSHRIRAM", "DLF", "DOMS", "DABUR", "DALBHARAT", "DATAPATTNS",
    "DEEPAKFERT", "DEEPAKNTR", "DELHIVERY", "DEVYANI", "DIVISLAB", "DIXON", "LALPATHLAB", "DRREDDY", "EIDPARRY",
    "EIHOTEL", "EICHERMOT", "ELECON", "ELGIEQUIP", "EMAMILTD", "EMCURE", "EMMVEE", "ENDURANCE", "ENGINERSIN",
    "ERIS", "ESCORTS", "ETERNAL", "EXIDEIND", "NYKAA", "FEDERALBNK", "FACT", "FINCABLES", "FSL", "FIVESTAR",
    "FORCEMOT", "FORTIS", "GAIL", "GVT&D", "GMRAIRPORT", "GABRIEL", "GALLANTT", "GRSE", "GICRE", "GILLETTE",
    "GLAND", "GLAXO", "GLENMARK", "MEDANTA", "GODIGIT", "GPIL", "GODFRYPHLP", "GODREJCP", "GODREJIND", "GODREJPROP",
    "GRANULES", "GRAPHITE", "GRASIM", "GRAVITA", "GESHIP", "FLUOROCHEM", "GMDCLTD", "HEG", "HBLENGINE", "HCLTECH",
    "HDBFS", "HDFCAMC", "HDFCBANK", "HDFCLIFE", "HFCL", "HAVELLS", "HEROMOTOCO", "HEXT", "HSCL", "HINDALCO",
    "HAL", "HINDCOPPER", "HINDPETRO", "HINDUNILVR", "HINDZINC", "POWERINDIA", "HOMEFIRST", "HONASA", "HONAUT",
    "HUDCO", "HYUNDAI", "ICICIBANK", "ICICIGI", "ICICIAMC", "ICICIPRULI", "IDBI", "IDFCFIRSTB", "IFCI", "IIFL",
    "IRB", "IRCON", "ITCHOTELS", "ITC", "ITI", "INDGN", "INDIACEM", "INDIAMART", "INDIANB", "IEX", "INDHOTEL",
    "IOC", "IOB", "IRCTC", "IRFC", "IREDA", "IGL", "INDUSTOWER", "INDUSINDBK", "NAUKRI", "INFY", "INOXWIND",
    "INTELLECT", "INDIGO", "IGIL", "IKS", "IPCALAB", "JKCEMENT", "JBMA", "JKTYRE", "JMFINANCIL", "JSWCEMENT",
    "JSWDULUX", "JSWENERGY", "JSWINFRA", "JSWSTEEL", "JAINREC", "JPPOWER", "J&KBANK", "JINDALSAW", "JSL",
    "JINDALSTEL", "JIOFIN", "JUBLFOOD", "JUBLINGREA", "JUBLPHARMA", "JWL", "JYOTICNC", "KPRMILL", "KEI", "KPITTECH",
    "KAJARIACER", "KPIL", "KALYANKJIL", "KARURVYSYA", "KAYNES", "KEC", "KFINTECH", "KIRLOSENG", "KOTAKBANK",
    "KIMS", "LTF", "LTTS", "LGEINDIA", "LICHSGFIN", "LTFOODS", "LTM", "LT", "LATENTVIEW", "LAURUSLABS", "THELEELA",
    "LEMONTREE", "LENSKART", "LICI", "LINDEINDIA", "LLOYDSME", "LODHA", "LUPIN", "MMTC", "MRF", "MGL", "M&MFIN",
    "M&M", "MANAPPURAM", "MRPL", "MANKIND", "MARICO", "MARUTI", "MFSL", "MAXHEALTH", "MAZDOCK", "MEESHO",
    "MINDACORP", "MSUMI", "MOTILALOFS", "MPHASIS", "MCX", "MUTHOOTFIN", "NATCOPHARM", "NBCC", "NCC", "NHPC",
    "NLCINDIA", "NMDC", "NSLNISP", "NTPCGREEN", "NTPC", "NH", "NATIONALUM", "NAVA", "NAVINFLUOR", "NESTLEIND",
    "NETWEB", "NEULANDLAB", "NEWGEN", "NAM-INDIA", "NIVABUPA", "NUVAMA", "NUVOCO", "OBEROIRLTY", "ONGC", "OIL",
    "OLAELEC", "OLECTRA", "PAYTM", "ONESOURCE", "OFSS", "POLICYBZR", "PCBL", "PGEL", "PIIND", "PNBHOUSING",
    "PTCIL", "PVRINOX", "PAGEIND", "PARADEEP", "PATANJALI", "PERSISTENT", "PETRONET", "PFIZER", "PHOENIXLTD",
    "PWL", "PIDILITIND", "PINELABS", "PIRAMALFIN", "PPLPHARMA", "POLYMED", "POLYCAB", "POONAWALLA", "PFC",
    "POWERGRID", "PREMIERENE", "PRESTIGE", "PFOCUS", "PNB", "RRKABEL", "RBLBANK", "RECLTD", "RHIM", "RITES",
    "RADICO", "RVNL", "RAILTEL", "RAINBOW", "RKFORGE", "REDINGTON", "RELIANCE", "RPOWER", "SBFC", "SBICARD",
    "SBILIFE", "SJVN", "SRF", "SAGILITY", "SAILIFE", "SAMMAANCAP", "MOTHERSON", "SAPPHIRE", "SARDAEN", "SAREGAMA",
    "SCHAEFFLER", "SCHNEIDER", "SCI", "SHREECEM", "SHRIRAMFIN", "SHYAMMETL", "ENRIN", "SIEMENS", "SIGNATURE",
    "SOBHA", "SOLARINDS", "SONACOMS", "SONATSOFTW", "STARHEALTH", "SBIN", "SAIL", "SUMICHEM", "SUNPHARMA",
    "SUNTV", "SUNDARMFIN", "SUPREMEIND", "SPLPETRO", "SUZLON", "SWANCORP", "SWIGGY", "SYNGENE", "SYRMA", "TBOTEK",
    "TVSMOTOR", "TATACAP", "TATACHEM", "TATACOMM", "TCS", "TATACONSUM", "TATAELXSI", "TATAINVEST", "TMCV", "TMPV",
    "TATAPOWER", "TATASTEEL", "TATATECH", "TTML", "TECHM", "TECHNOE", "TEGA", "TEJASNET", "TENNIND", "NIACL",
    "RAMCOCEM", "THERMAX", "TIMKEN", "TITAGARH", "TITAN", "TORNTPHARM", "TORNTPOWER", "TARIL", "TRAVELFOOD",
    "TRENT", "TRIDENT", "TRITURBINE", "TIINDIA", "UCOBANK", "UNOMINDA", "UPL", "UTIAMC", "ULTRACEMCO", "UNIONBANK",
    "UBL", "UNITDSPR", "URBANCO", "USHAMART", "VTL", "VBL", "VEDL", "VIJAYA", "VMM", "IDEA", "VOLTAS", "WAAREEENER",
    "WELCORP", "WELSPUNLIV", "WHIRLPOOL", "WIPRO", "WOCKPHARMA", "YESBANK", "ZFCVINDIA", "ZEEL", "ZENTEC",
    "ZENSARTECH", "ZYDUSLIFE", "ZYDUSWELL", "ECLERX"
]

# Formatting every ticker with the mandatory National Stock Exchange (.NS) suffix
WATCHLIST = [f"{ticker}.NS" for ticker in RAW_SYMBOLS]

# ==============================================================================
# 🗓️ MARKET HOUR AND HOLIDAY MANAGEMENT
# ==============================================================================
def get_nse_holidays():
    """Returns official NSE holiday boundaries.
    NOTE: this list is only valid for 2026 — remember to update it each
    January, or the market-hours check will silently treat holidays as
    open trading days once the year rolls over."""
    return {
        "2026-01-26", "2026-03-06", "2026-03-27", "2026-04-02", "2026-04-03",
        "2026-04-14", "2026-05-01", "2026-08-15", "2026-09-15", "2026-10-02",
        "2026-10-22", "2026-11-10", "2026-11-11", "2026-11-24", "2026-12-25"
    }

def get_ist_time():
    return datetime.now(pytz.timezone('Asia/Kolkata'))

def is_indian_market_open():
    now_india = get_ist_time()
    if now_india.isoweekday() > 5:
        return False, "Weekend"
    if now_india.strftime("%Y-%m-%d") in get_nse_holidays():
        return False, "NSE Trading Holiday"

    market_start = datetime.strptime("09:15:00", "%H:%M:%S").time()
    market_end = datetime.strptime("15:30:00", "%H:%M:%S").time()
    if market_start <= now_india.time() <= market_end:
        return True, "Open"
    return False, "Outside Market Hours"

def session_fraction_elapsed(now_india):
    """NEW: fraction of the 9:15-15:30 session that has elapsed, clamped to
    a floor of 0.15 so we never divide by a near-zero fraction right at the
    open (which would make projected volume explode to absurd values)."""
    market_open_dt = now_india.replace(hour=9, minute=15, second=0, microsecond=0)
    elapsed_minutes = (now_india - market_open_dt).total_seconds() / 60.0
    total_minutes = 375.0  # 9:15 -> 15:30
    fraction = elapsed_minutes / total_minutes
    return max(0.15, min(1.0, fraction))

# ==============================================================================
# 🏷️ SECTOR LOOKUP (cached — only fetched for symbols that actually signal)
# ==============================================================================
def _load_sector_cache():
    if os.path.isfile(SECTOR_CACHE_FILE):
        try:
            with open(SECTOR_CACHE_FILE, "r") as f:
                return json.load(f)
        except Exception:
            return {}
    return {}


def _save_sector_cache(cache):
    try:
        with open(SECTOR_CACHE_FILE, "w") as f:
            json.dump(cache, f)
    except Exception as e:
        print(f"⚠️ Could not save sector cache: {e}")


_SECTOR_CACHE = _load_sector_cache()


def get_sector(symbol):
    """Looks up a symbol's sector via yfinance's `.info`, with a persistent
    on-disk cache. This is deliberately called only for the handful of
    symbols that actually surface as a signal (not the full 800-symbol
    watchlist every scan) so it doesn't add meaningfully to API load or
    rate-limit risk. Sector rarely changes, so once cached it's reused
    indefinitely; delete sector_cache.json if a company gets reclassified."""
    if symbol in _SECTOR_CACHE:
        return _SECTOR_CACHE[symbol]
    sector = "Unknown"
    try:
        info = yf.Ticker(symbol).info
        sector = info.get("sector") or "Unknown"
    except Exception:
        sector = "Unknown"
    _SECTOR_CACHE[symbol] = sector
    _save_sector_cache(_SECTOR_CACHE)
    return sector

# ==============================================================================
# 🛠️ TELEGRAM OUTBOUND GATEWAY
# ==============================================================================
def send_telegram_message(message):
    url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"
    try:
        res = requests.post(
            url,
            json={"chat_id": TELEGRAM_CHAT_ID, "text": message, "parse_mode": "Markdown"},
            timeout=10,
        )
        if res.status_code != 200:
            print(f"❌ Telegram Communication Halt: {res.text}")
    except Exception as e:
        print(f"❌ Connection Error: {e}")

# ==============================================================================
# 📈 MATHEMATICAL ALGORITHMS & POSITION CALCULATORS (ATR VOLATILITY SYSTEM)
# ==============================================================================
def calculate_rsi(close_series, period=14):
    """Wilder-smoothed RSI. Used as a 'not already overheated' filter."""
    delta = close_series.diff()
    gain = delta.clip(lower=0)
    loss = -delta.clip(upper=0)
    avg_gain = gain.ewm(alpha=1.0 / period, min_periods=period, adjust=False).mean()
    avg_loss = loss.ewm(alpha=1.0 / period, min_periods=period, adjust=False).mean()
    rs = avg_gain / avg_loss.replace(0, pd.NA)
    rsi = 100 - (100 / (1 + rs))
    return rsi.fillna(100)  # if avg_loss is 0, price only went up -> RSI 100


def calculate_indicators(df):
    df['EMA_20'] = df['Close'].ewm(span=20, adjust=False).mean()
    df['EMA_50'] = df['Close'].ewm(span=50, adjust=False).mean()           # NEW: bigger-picture trend filter
    df['RSI_14'] = calculate_rsi(df['Close'], RSI_PERIOD)                  # NEW: overbought/momentum filter
    df['Recent_Max'] = df['High'].shift(1).rolling(window=5).max()
    df['Recent_Min'] = df['Low'].shift(1).rolling(window=5).min()

    # 🐛 BUG FIX: this used to be df['Volume'].rolling(5).mean() with NO
    # shift, so "today's" volume was baked into its own comparison average.
    # Shifted to match Recent_Max / Recent_Min so the average only reflects
    # the 5 days BEFORE today, same as every other lookback in this file.
    df['Vol_Avg_5'] = df['Volume'].shift(1).rolling(window=5).mean()

    # NEW: liquidity proxy — 20-day average daily rupee turnover.
    df['Turnover_Avg_20'] = (df['Close'] * df['Volume']).rolling(window=20).mean()

    # ATR Calculation Pipeline
    df['High_Low'] = df['High'] - df['Low']
    df['High_PClose'] = (df['High'] - df['Close'].shift(1)).abs()
    df['Low_PClose'] = (df['Low'] - df['Close'].shift(1)).abs()
    df['True_Range'] = df[['High_Low', 'High_PClose', 'Low_PClose']].max(axis=1)
    df['ATR_14'] = df['True_Range'].rolling(window=14).mean()
    return df


def calculate_position_size(entry_price, stop_loss):
    """
    Returns a tuple:
    (shares, risk_per_share, allowed_risk, position_value, target_price, reward_risk_ratio)
    All zeros if the trade doesn't make sense (e.g. stop above entry).

    Three independent caps are applied, and the tightest one wins:
      1. Risk-based: shares such that a stop-out loses ~MAX_ACCOUNT_RISK_PCT of capital.
      2. Cash-based: you can't spend more than TOTAL_TRADING_CAPITAL.
      3. Concentration-based (NEW): no single trade exceeds MAX_POSITION_PCT_OF_CAPITAL,
         even if #1 and #2 would otherwise allow it. This exists because a very
         tight/low-ATR stock can pass the risk check with a huge share count that
         quietly puts most of the account in one name — technically "1% risk" but
         not actually diversified or safe.
    """
    allowed_risk = TOTAL_TRADING_CAPITAL * (MAX_ACCOUNT_RISK_PCT / 100.0)
    risk_per_share = entry_price - stop_loss
    if risk_per_share <= 0 or entry_price <= 0:
        return 0, 0, 0, 0, 0, 0

    shares = int(allowed_risk // risk_per_share)

    # Cash cap
    cash_cap_shares = int(TOTAL_TRADING_CAPITAL // entry_price)
    shares = min(shares, cash_cap_shares)

    # Concentration cap (NEW)
    max_position_value = TOTAL_TRADING_CAPITAL * (MAX_POSITION_PCT_OF_CAPITAL / 100.0)
    concentration_cap_shares = int(max_position_value // entry_price)
    shares = min(shares, concentration_cap_shares)

    if shares <= 0:
        return 0, 0, 0, 0, 0, 0

    position_value = shares * entry_price
    target_price = entry_price + (risk_per_share * REWARD_RISK_RATIO)

    return (
        shares,
        round(risk_per_share, 2),
        round(shares * risk_per_share, 2),  # actual ₹ at risk for the sized position (<= allowed_risk)
        round(position_value, 2),
        round(target_price, 2),
        REWARD_RISK_RATIO,
    )

# ==============================================================================
# 🔎 SIGNAL LOGIC
# ==============================================================================
def download_with_retry(symbol, period="6mo", interval="1d",
                         retries=DOWNLOAD_RETRIES, backoff=DOWNLOAD_RETRY_BACKOFF_SEC):
    """NEW: yfinance + 400 tickers hits Yahoo's rate limits regularly. Retry
    with a small linear backoff instead of dropping the symbol on one blip."""
    last_err = None
    for attempt in range(1, retries + 1):
        try:
            df = yf.download(symbol, period=period, interval=interval,
                              progress=False, auto_adjust=True, threads=False)
            if df is not None and not df.empty:
                return df
        except Exception as e:
            last_err = e
        time.sleep(backoff * attempt)
    if last_err:
        print(f"⚠️ {symbol}: giving up after {retries} attempts ({last_err})")
    return None


def evaluate_symbol(symbol):
    """
    Downloads recent daily data for a symbol and checks for a breakout setup:
      - Close clears the prior 5-day high by BREAKOUT_BUFFER_PCT (not just barely above it)
      - Not already extended more than MAX_EXTENSION_PCT past that level (avoid chasing)
      - Price above EMA_20 AND EMA_20 above EMA_50 AND price above EMA_50 (real uptrend structure)
      - RSI_14 between RSI_MIN and RSI_MAX (momentum present, not already blown off)
      - Volume (time-of-day normalized if today's candle is still live) confirms
        at >= VOLUME_CONFIRM_MULTIPLIER x the prior 5-day average
      - Price and 20-day average turnover clear minimum liquidity floors
    Returns a dict with signal details + a ranking score, or None if no signal / bad data.
    """
    try:
        df = download_with_retry(symbol)
        if df is None or len(df) < 60:  # need real history for EMA_50/RSI/ATR to be meaningful
            return None

        # yfinance can return MultiIndex columns for single-ticker downloads in some versions
        if isinstance(df.columns, pd.MultiIndex):
            df.columns = df.columns.get_level_values(0)

        df = calculate_indicators(df)
        latest = df.iloc[-1]

        required = ['Recent_Max', 'ATR_14', 'Vol_Avg_5', 'EMA_50', 'RSI_14', 'Turnover_Avg_20']
        if any(pd.isna(latest[col]) for col in required):
            return None

        price = float(latest['Close'])
        recent_max = float(latest['Recent_Max'])

        # --- Liquidity / quality floors (capital-safety filters) ---
        if price < MIN_STOCK_PRICE:
            return None
        if float(latest['Turnover_Avg_20']) < MIN_AVG_DAILY_TURNOVER_INR:
            return None

        # --- Breakout with a noise buffer, and not already too extended ---
        breakout_level = recent_max * (1 + BREAKOUT_BUFFER_PCT / 100.0)
        if price <= breakout_level:
            return None
        extension_pct = (price - recent_max) / recent_max * 100.0
        if extension_pct > MAX_EXTENSION_PCT:
            return None

        # --- Trend structure ---
        ema20, ema50 = float(latest['EMA_20']), float(latest['EMA_50'])
        uptrend = price > ema20 and ema20 > ema50 and price > ema50
        if not uptrend:
            return None

        # --- Momentum band (avoid overbought blow-offs, avoid weak moves) ---
        rsi = float(latest['RSI_14'])
        if not (RSI_MIN <= rsi <= RSI_MAX):
            return None

        # --- Volume confirmation, time-of-day normalized for a live intraday candle ---
        open_now, _ = is_indian_market_open()
        latest_date = df.index[-1].date()
        now_india = get_ist_time()
        is_live_bar = open_now and (latest_date == now_india.date())

        raw_volume = float(latest['Volume'])
        if is_live_bar:
            fraction = session_fraction_elapsed(now_india)
            projected_volume = raw_volume / fraction
        else:
            projected_volume = raw_volume  # candle is a completed session, use as-is

        vol_avg_5 = float(latest['Vol_Avg_5'])
        volume_confirmed = projected_volume >= vol_avg_5 * VOLUME_CONFIRM_MULTIPLIER
        if not volume_confirmed:
            return None

        # --- Passed all filters: build the trade plan ---
        atr = float(latest['ATR_14'])
        entry_price = price
        stop_loss = entry_price - (atr * ATR_STOP_MULTIPLIER)

        shares, risk_per_share, allowed_risk, position_value, target_price, rr = calculate_position_size(
            entry_price, stop_loss
        )
        if shares <= 0:
            return None

        # --- Ranking score (higher = more convincing setup) ---
        # Purely for sorting which of several valid setups to prioritize with
        # limited capital; not itself a probability of profit.
        volume_ratio = projected_volume / vol_avg_5 if vol_avg_5 else 0
        trend_strength_pct = (ema20 - ema50) / ema50 * 100.0
        rsi_centering = 10 - abs(rsi - 62.5) / 2.5   # peaks near the middle of the RSI band
        extension_penalty = extension_pct            # smaller/tighter breakouts score better
        score = (volume_ratio * 5) + (trend_strength_pct * 2) + rsi_centering - extension_penalty

        return {
            "symbol": symbol,
            "entry_price": round(entry_price, 2),
            "stop_loss": round(stop_loss, 2),
            "target_price": target_price,
            "shares": shares,
            "risk_per_share": risk_per_share,
            "allowed_risk": allowed_risk,
            "position_value": position_value,
            "reward_risk_ratio": rr,
            "rsi": round(rsi, 1),
            "volume_ratio": round(volume_ratio, 2),
            "extension_pct": round(extension_pct, 2),
            "live_bar": is_live_bar,
            "score": round(score, 2),
            "timestamp_ist": now_india.strftime("%Y-%m-%d %H:%M:%S"),
            # NEW — for the "best entry you missed / next entry" alert section:
            "ideal_entry": round(recent_max, 2),   # the actual breakout trigger level
            "pullback_entry": round(ema20, 2),     # next logical entry zone (rising 20-EMA) if this is missed
        }
    except Exception as e:
        print(f"⚠️ Error evaluating {symbol}: {e}")
        return None

# ==============================================================================
# 📣 PORTFOLIO-CONTEXT ENRICHMENT (sector, sequential capital, warnings)
# ==============================================================================
def resize_for_remaining_capital(signal, remaining_capital):
    """A signal's shares/risk are originally sized against the FULL account
    (each trade evaluated independently, same as before). But if you're
    acting on several signals from the same scan in ranked order, you don't
    actually have the full account for the 2nd, 3rd... one — you have
    whatever's left. This re-caps the position against what's actually left,
    so 'Remaining Capital After This' is a real number, not fiction."""
    entry = signal["entry_price"]
    if signal["position_value"] <= remaining_capital:
        signal["insufficient_capital"] = False
        return signal, round(remaining_capital - signal["position_value"], 2)

    new_shares = int(remaining_capital // entry) if entry > 0 else 0
    if new_shares <= 0:
        signal["shares"] = 0
        signal["position_value"] = 0
        signal["allowed_risk"] = 0
        signal["insufficient_capital"] = True
        return signal, remaining_capital

    signal["shares"] = new_shares
    signal["position_value"] = round(new_shares * entry, 2)
    signal["allowed_risk"] = round(new_shares * signal["risk_per_share"], 2)
    signal["insufficient_capital"] = False
    return signal, round(remaining_capital - signal["position_value"], 2)


def enrich_signals_with_portfolio_context(signals):
    """Adds sector, a same-day sector-concentration warning, and sequential
    remaining-capital tracking across the ranked signals in THIS scan.
    (Sector duplicates across separate scans/days aren't tracked here since
    the script keeps no cross-run state beyond signals_log.csv — if you want
    true cross-day sector tracking, check that log before acting.)"""
    remaining_capital = TOTAL_TRADING_CAPITAL
    sectors_seen_today = {}
    for sig in signals:
        sig["sector"] = get_sector(sig["symbol"])
        sig, remaining_capital = resize_for_remaining_capital(sig, remaining_capital)
        sig["remaining_capital"] = remaining_capital

        sector = sig["sector"]
        if sector != "Unknown" and sectors_seen_today.get(sector):
            sig["sector_warning"] = (
                f"⚠️ Sector Warning: You already have a signal in {sector} today — "
                f"taking this one too means doubling up on the same sector's risk."
            )
        else:
            sig["sector_warning"] = None
        sectors_seen_today[sector] = sectors_seen_today.get(sector, 0) + 1
    return signals

# ==============================================================================
# 📣 ALERT FORMATTING & LOGGING
# ==============================================================================
def format_alert(signal, rank=None):
    sym_display = signal["symbol"].replace(".NS", "")
    lines = [
        f"🟢 SWING TRADE ALERT: {sym_display} 🟢",
        "━━━━━━━━━━━━━━━━━━━",
        "▪️ Action: BUY (CNC/Delivery Leg)",
        f"▪️ Sector: {signal.get('sector', 'Unknown')}",
        f"▪️ Entry Price: ₹{signal['entry_price']}",
        f"▪️ Hard Stop Loss: ₹{signal['stop_loss']}",
        f"▪️ Target (1:{int(signal['reward_risk_ratio'])} RR): ₹{signal['target_price']}",
        "━━━━━━━━━━━━━━━━━━━",
    ]

    if signal.get("insufficient_capital"):
        lines += [
            "📊 SAFE POSITION SIZING",
            "▪️ ⚠️ Not enough capital left today after earlier signals in this scan — "
            "skip or fund manually if you still want this one.",
            "━━━━━━━━━━━━━━━━━━━",
        ]
    else:
        lines += [
            "📊 SAFE POSITION SIZING",
            f"▪️ Exact Quantity to Buy: {signal['shares']} Shares",
            f"▪️ Total Fund Deployment: ₹{signal['position_value']}",
            f"▪️ Total Theoretical Risk: ₹{signal['allowed_risk']} (Max {MAX_ACCOUNT_RISK_PCT}%)",
            f"▪️ Remaining Capital After This: ₹{signal['remaining_capital']}",
            "━━━━━━━━━━━━━━━━━━━",
        ]

    # "Best entry missed" / "next available entry" section
    entry_gap_pct = signal["extension_pct"]
    if entry_gap_pct <= 0.3:
        chase_note = "you're right at the trigger"
    else:
        chase_note = f"you're chasing it by {entry_gap_pct}%"
    lines += [
        "🎯 ENTRY TRACKER",
        f"▪️ Ideal Entry (Breakout Trigger): ₹{signal['ideal_entry']}",
        f"▪️ Your Entry vs Ideal: ₹{signal['entry_price']} ({chase_note})",
        f"▪️ Next Entry Zone If You Miss This (20-EMA Pullback): ₹{signal['pullback_entry']} "
        f"— only valid if trend/volume still confirm when price gets there",
        "━━━━━━━━━━━━━━━━━━━",
    ]

    if signal.get("sector_warning"):
        lines.append(signal["sector_warning"])
    if signal.get("live_bar"):
        lines.append("⚠️ Live intraday candle — price/volume can still change before close.")
    lines.append("⏰ System Advice: Set an automatic GTT stop-loss order instantly inside your broker app!")
    lines.append("_Not financial advice — verify independently before entering._")

    if rank is not None:
        lines[0] = f"🟢 SWING TRADE ALERT: {sym_display} (#{rank}) 🟢"

    return "\n".join(lines)


def log_signals_to_csv(signals, path=SIGNAL_LOG_FILE):
    """NEW: append every surfaced signal to a CSV so results can be reviewed
    and the system's actual track record judged, instead of trusting it blindly."""
    if not signals:
        return
    fieldnames = list(signals[0].keys())
    file_exists = os.path.isfile(path)
    try:
        with open(path, "a", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            if not file_exists:
                writer.writeheader()
            for sig in signals:
                writer.writerow(sig)
    except Exception as e:
        print(f"⚠️ Could not write to {path}: {e}")

# ==============================================================================
# 🔁 MAIN SCAN LOOP
# ==============================================================================
def scan_watchlist(symbols=None):
    symbols = symbols if symbols is not None else WATCHLIST
    signals = []
    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        futures = {executor.submit(evaluate_symbol, sym): sym for sym in symbols}
        for future in as_completed(futures):
            result = future.result()
            if result:
                signals.append(result)
    # Best setups first; only the top MAX_SIGNALS_PER_SCAN get surfaced/alerted.
    signals.sort(key=lambda s: s["score"], reverse=True)
    return signals[:MAX_SIGNALS_PER_SCAN]


def run_once(symbols, send_alerts):
    """Runs a single scan pass over `symbols` and returns the signals found.
    Prints results either way; only calls Telegram if send_alerts=True."""
    print(f"🔍 Scanning {len(symbols)} symbols at {get_ist_time().strftime('%H:%M:%S')} IST...")
    signals = scan_watchlist(symbols)

    if signals:
        signals = enrich_signals_with_portfolio_context(signals)
        total_risk_pct = sum(s['allowed_risk'] for s in signals) / TOTAL_TRADING_CAPITAL * 100
        print(f"✅ {len(signals)} setup(s) passed all filters "
              f"(combined risk if you took all of them: {total_risk_pct:.2f}% of capital).")
        for i, sig in enumerate(signals, start=1):
            msg = format_alert(sig, rank=i)
            print(msg)
            if send_alerts:
                send_telegram_message(msg)
        log_signals_to_csv(signals)
    else:
        print("No signals this scan.")

    return signals


def main():
    parser = argparse.ArgumentParser(description="NSE swing-trading breakout screener")
    parser.add_argument(
        "--test", action="store_true",
        help="Dry-run mode: ignores market hours, scans a small sample once, and does NOT send Telegram alerts."
    )
    parser.add_argument(
        "--send-alerts", action="store_true",
        help="In --test mode, actually send any signals found to Telegram instead of just printing them."
    )
    parser.add_argument(
        "--symbols", type=str, default=None,
        help="Comma-separated list of raw symbols (no .NS suffix) to test with, e.g. RELIANCE,TCS,INFY."
    )
    parser.add_argument(
        "--once", action="store_true",
        help="Run a single real scan pass over the full watchlist and exit — for external "
             "schedulers like GitHub Actions/cron, which call the script repeatedly rather "
             "than expecting it to loop forever. Still respects market hours/holidays: if "
             "the market is closed when this runs, it exits quietly without scanning."
    )
    args = parser.parse_args()

    if args.once:
        open_now, reason = is_indian_market_open()
        if not open_now:
            print(f"⏸️  Market closed ({reason}). Skipping this run (nothing to do).")
            return
        print(f"🔁 Single-pass run (external scheduler) at {get_ist_time().strftime('%Y-%m-%d %H:%M:%S')} IST")
        run_once(WATCHLIST, send_alerts=True)
        return

    if args.test:
        if args.symbols:
            test_symbols = [f"{s.strip().upper()}.NS" for s in args.symbols.split(",") if s.strip()]
        else:
            test_symbols = WATCHLIST[:TEST_SAMPLE_SIZE]

        print(f"🧪 TEST MODE — market-hours check bypassed, one-shot scan of {len(test_symbols)} symbols.")
        print(f"   Symbols: {', '.join(test_symbols)}")
        if not args.send_alerts:
            print("   Telegram alerts are DISABLED for this run (use --send-alerts to enable).")

        run_once(test_symbols, send_alerts=args.send_alerts)
        return

    # Normal live mode
    print(f"🚀 Screener starting at {get_ist_time().strftime('%Y-%m-%d %H:%M:%S')} IST")
    print("   Reminder: this tool flags setups, it does not guarantee outcomes. "
          "Trade small, respect the stop-loss, and review signals_log.csv regularly.")
    while True:
        open_now, reason = is_indian_market_open()
        if not open_now:
            print(f"⏸️  Market closed ({reason}). Checking again in 5 minutes.")
            time.sleep(300)
            continue

        run_once(WATCHLIST, send_alerts=True)
        time.sleep(SCAN_INTERVAL_SECONDS)


if __name__ == "__main__":
    main()
