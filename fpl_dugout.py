#!/usr/bin/env python3
"""
FPL Dugout - a live Fantasy Premier League dashboard that runs on your own machine.

    python3 fpl_dugout.py

Then open http://localhost:8756 (it tries to open your browser for you).

Why a local server rather than a plain HTML file: the FPL API sends no CORS
headers, so a page opened from disk is not allowed to call it. This script
serves the page AND relays the API calls, which sidesteps that entirely.

No installs. Python 3.8+ standard library only.

Configure your own team below, or pass them on the command line:
    python3 fpl_dugout.py --entry 8148026 --league 1769954
"""

import argparse
import base64
import json
import math
import os
import re
import ssl
import sys
import threading
import time
import urllib.error
import urllib.request
import webbrowser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

# ----------------------------------------------------------------------------
# your details
# ----------------------------------------------------------------------------
ENTRY_ID = int(os.environ.get("FPL_ENTRY", "8148026"))     # Dcosta Dacoits
LEAGUE_ID = int(os.environ.get("FPL_LEAGUE", "1769954"))   # Box2Box Players
PORT = int(os.environ.get("PORT", "8756"))

# Hosts like Render inject PORT and expect the process to listen on every
# interface. Locally we stay on loopback so nothing is exposed to the network.
ON_HOST = bool(os.environ.get("PORT"))
HOST = os.environ.get("HOST", "0.0.0.0" if ON_HOST else "127.0.0.1")
PASSWORD = os.environ.get("FPL_PASSWORD", "").strip()

API = "https://fantasy.premierleague.com/api"
UA = ("Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/124.0 Safari/537.36")
CACHE_TTL = 90              # seconds; bootstrap-static is big, don't hammer it
MOCK_DIR = os.environ.get("FPL_MOCK")   # test hook: read fixtures from disk

_cache = {}
_lock = threading.Lock()
INSECURE = False
_ssl_ctx = None


def ssl_context():
    """Build an SSL context with working root certificates.

    The python.org macOS builds ship with an EMPTY trust store until you run
    'Install Certificates.command'. When that has not happened, fall back to
    certifi's bundle if it is importable, so the app just works.
    """
    global _ssl_ctx
    if _ssl_ctx is not None:
        return _ssl_ctx
    if INSECURE:
        ctx = ssl.create_default_context()
        ctx.check_hostname = False
        ctx.verify_mode = ssl.CERT_NONE
        _ssl_ctx = ctx
        return ctx
    ctx = ssl.create_default_context()
    try:
        empty = ctx.cert_store_stats().get("x509_ca", 0) == 0
    except Exception:
        empty = False
    if empty:
        try:
            import certifi
            ctx.load_verify_locations(certifi.where())
            print("  note: system trust store was empty; using certifi bundle.")
        except Exception:
            pass
    _ssl_ctx = ctx
    return ctx


def cert_help():
    v = "%d.%d" % (sys.version_info[0], sys.version_info[1])
    return ("Your Python has no root certificates, so it cannot verify HTTPS. "
            "This is normal for a fresh python.org install on macOS. Fix it once by "
            "running this in Terminal:\n\n"
            "    /Applications/Python\\ %s/Install\\ Certificates.command\n\n"
            "If that path does not exist, run instead:\n\n"
            "    python3 -m pip install --upgrade certifi\n\n"
            "then restart this app. As a last resort you can start it with "
            "--insecure, which skips certificate checking." % v)


# ----------------------------------------------------------------------------
# fetching
# ----------------------------------------------------------------------------
def fetch(path, ttl=CACHE_TTL):
    """GET {API}{path} as JSON, with a short TTL cache. Raises FPLError."""
    now = time.time()
    with _lock:
        hit = _cache.get(path)
        if hit and now - hit[0] < ttl:
            return hit[1]

    if MOCK_DIR:
        name = re.sub(r"[^A-Za-z0-9]+", "_", path).strip("_") + ".json"
        p = os.path.join(MOCK_DIR, name)
        if not os.path.exists(p):
            raise FPLError("mock file missing: " + name, 404)
        with open(p) as fh:
            data = json.load(fh)
    else:
        req = urllib.request.Request(API + path, headers={
            "User-Agent": UA, "Accept": "application/json"})
        try:
            with urllib.request.urlopen(req, timeout=25, context=ssl_context()) as r:
                data = json.loads(r.read().decode("utf-8"))
        except urllib.error.HTTPError as e:
            raise FPLError("FPL API returned HTTP %d for %s" % (e.code, path), e.code)
        except urllib.error.URLError as e:
            if isinstance(getattr(e, "reason", None), ssl.SSLError):
                raise FPLError(cert_help(), 526)
            raise FPLError("Could not reach the FPL API (%s). Check your internet "
                           "connection." % e.reason, 503)
        except ssl.SSLError:
            raise FPLError(cert_help(), 526)
        except json.JSONDecodeError:
            raise FPLError("FPL API sent a response that was not JSON. It is "
                           "probably down or rate-limiting.", 502)

    with _lock:
        _cache[path] = (now, data)
    return data


class FPLError(Exception):
    def __init__(self, msg, code=502):
        super().__init__(msg)
        self.code = code


def num(v, d=0.0):
    try:
        if v is None or v == "":
            return d
        return float(v)
    except (TypeError, ValueError):
        return d


def pct_ranks(values):
    """percentile rank (0-1) for each value, ties share the average rank"""
    n = len(values)
    if n == 0:
        return []
    order = sorted(range(n), key=lambda i: values[i])
    out = [0.0] * n
    i = 0
    while i < n:
        j = i
        while j + 1 < n and values[order[j + 1]] == values[order[i]]:
            j += 1
        avg = (i + j) / 2.0
        for k in range(i, j + 1):
            out[order[k]] = (avg + 1) / n
        i = j + 1
    return out


# ----------------------------------------------------------------------------
# the model  (documented in the UI's Model tab)
# ----------------------------------------------------------------------------
POS = {1: "GK", 2: "DEF", 3: "MID", 4: "FWD"}
LEAGUE_AVG_GOALS = 1.45      # goals per team per match, long-run Premier League
HORIZON = 5                  # gameweeks the planning numbers look ahead over
DC_THRESH = {"GK": 999, "DEF": 10, "MID": 12, "FWD": 12}
FIX_GWS = 6


# ---------------------------------------------------------------------------
# Betting odds as a strength signal
# ---------------------------------------------------------------------------
# The market prices in squad quality, transfers, suspensions and Friday team news
# within minutes, and published work finds bookmaker odds better calibrated than
# statistical models. Where a fixture is priced, its expected goals come from the
# market. Beyond the market's horizon the results-based ratings take over, and
# every fixture is labelled with which produced it.
ODDS_KEY = os.environ.get("ODDS_API_KEY", "").strip()
ODDS_SPORT = os.environ.get("ODDS_SPORT", "soccer_epl")
ODDS_REGION = os.environ.get("ODDS_REGION", "uk")
# 1 credit per market per region. h2h alone determines both goal expectations
# (three prices, two free parameters, two unknowns), so totals is opt-in.
ODDS_MARKETS = os.environ.get("ODDS_MARKETS", "h2h")
ODDS_TTL = int(os.environ.get("ODDS_TTL", "21600"))    # 6 hours
ODDS_HOST = "https://api.the-odds-api.com"

ODDS_CREDITS_PER_CALL = (len([x for x in ODDS_MARKETS.split(",") if x.strip()])
                         * len([x for x in ODDS_REGION.split(",") if x.strip()]))
ODDS_MAX_CALLS = int(os.environ.get("ODDS_MAX_CALLS", "300"))
_odds_state = {"status": "off", "detail": "no ODDS_API_KEY set",
               "events": 0, "remaining": None, "fetched": None}
# deliberately NOT in _cache: pressing Refresh clears that, and odds cost money
_odds_cache = {"t": 0.0, "data": [], "calls": 0, "month": ""}


def _odds_budget_ok():
    """One hard ceiling per calendar month, so nothing can run the meter away."""
    mon = time.strftime("%Y-%m")
    if _odds_cache["month"] != mon:
        _odds_cache["month"] = mon
        _odds_cache["calls"] = 0
    return _odds_cache["calls"] < ODDS_MAX_CALLS


def odds_available():
    return bool(ODDS_KEY)


def fetch_odds():
    """Upcoming priced fixtures. Costs 1 credit per market per region."""
    if MOCK_DIR:
        p = os.path.join(MOCK_DIR, "odds.json")
        if os.path.exists(p):
            with open(p) as fh:
                data = json.load(fh)
            _odds_state.update(status="on", detail="mock odds file",
                               events=len(data), fetched="mock")
            return data
        return []
    if not ODDS_KEY:
        return []
    url = ("%s/v4/sports/%s/odds/?apiKey=%s&regions=%s&markets=%s&oddsFormat=decimal"
           % (ODDS_HOST, ODDS_SPORT, ODDS_KEY, ODDS_REGION, ODDS_MARKETS))
    now = time.time()
    with _lock:
        if _odds_cache["t"] and now - _odds_cache["t"] < ODDS_TTL:
            return _odds_cache["data"]
        if not _odds_budget_ok():
            _odds_state.update(status="error", detail=(
                "monthly odds call limit of %d reached; using results instead"
                % ODDS_MAX_CALLS))
            return _odds_cache["data"]
        _odds_cache["calls"] += 1
    req = urllib.request.Request(url, headers={"User-Agent": UA,
                                               "Accept": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=20, context=ssl_context()) as r:
            data = json.loads(r.read().decode("utf-8"))
            _odds_state["remaining"] = r.headers.get("x-requests-remaining")
    except urllib.error.HTTPError as e:
        code = e.code
        _odds_state.update(status="error", detail=(
            "the odds key was rejected (HTTP 401)" if code == 401 else
            "odds quota exhausted (HTTP 429)" if code == 429 else
            "odds provider returned HTTP %d" % code))
        return []
    except Exception as e:                                  # noqa: BLE001
        _odds_state.update(status="error", detail="could not reach the odds provider (%s)" % e)
        return []
    with _lock:
        _odds_cache["t"] = now
        _odds_cache["data"] = data
    _odds_state.update(status="on", detail="", events=len(data),
                       fetched=time.strftime("%Y-%m-%d %H:%M:%S"))
    return data


# ---- prices -> probabilities -> goal expectations -------------------------
def devig(prices):
    """Strip the bookmaker margin. Decimal odds imply 1/price; those sum to more
    than 1 because the margin is baked in, so divide through by the total."""
    inv = [(1.0 / p) for p in prices if p and p > 1.0]
    if len(inv) != len(prices) or not inv:
        return None
    tot = sum(inv)
    return [x / tot for x in inv], tot - 1.0


def _poisson_probs(lh, la, maxg=10):
    ph = [math.exp(-lh) * lh ** i / math.factorial(i) for i in range(maxg + 1)]
    pa = [math.exp(-la) * la ** i / math.factorial(i) for i in range(maxg + 1)]
    home = draw = away = 0.0
    for i in range(maxg + 1):
        for j in range(maxg + 1):
            p = ph[i] * pa[j]
            if i > j:
                home += p
            elif i == j:
                draw += p
            else:
                away += p
    return home, draw, away


def goals_from_probs(p_home, p_away, total=None):
    """Find the goal expectations that reproduce the market's probabilities.

    Two prices carry two degrees of freedom and there are two unknowns, so the
    pair is determined. Parametrised as total goals and supremacy, both solved
    by bisection: supremacy is monotone in the home-win probability, and total
    goals is monotone in the draw probability.
    """
    def sup_for(T):
        lo, hi = -4.0, 4.0
        for _ in range(45):
            mid = (lo + hi) / 2.0
            h, _d, _a = _poisson_probs(max(0.02, (T + mid) / 2.0),
                                       max(0.02, (T - mid) / 2.0))
            if h < p_home:
                lo = mid
            else:
                hi = mid
        return (lo + hi) / 2.0

    if total is not None and 0.5 < total < 8:
        T = total
        S = sup_for(T)
    else:
        target_draw = max(0.01, 1.0 - p_home - p_away)
        lo, hi = 1.2, 5.5
        for _ in range(35):
            T = (lo + hi) / 2.0
            S = sup_for(T)
            _h, d, _a = _poisson_probs(max(0.02, (T + S) / 2.0),
                                       max(0.02, (T - S) / 2.0))
            if d > target_draw:      # more goals means fewer draws
                lo = T
            else:
                hi = T
        T = (lo + hi) / 2.0
        S = sup_for(T)
    return max(0.05, (T + S) / 2.0), max(0.05, (T - S) / 2.0)


def parse_event(ev):
    """One priced fixture -> expected goals for each side, or None."""
    home, away = ev.get("home_team"), ev.get("away_team")
    if not home or not away:
        return None
    h2h, totals = [], []
    for bk in ev.get("bookmakers", []):
        for mk in bk.get("markets", []):
            if mk.get("key") == "h2h":
                o = {x.get("name"): x.get("price") for x in mk.get("outcomes", [])}
                if home in o and away in o and "Draw" in o:
                    h2h.append((o[home], o["Draw"], o[away]))
            elif mk.get("key") == "totals":
                for x in mk.get("outcomes", []):
                    if x.get("point") is not None:
                        totals.append(float(x["point"]))
    if not h2h:
        return None
    # median across bookmakers is more robust than any single price
    def med(xs):
        xs = sorted(xs)
        n = len(xs)
        return xs[n // 2] if n % 2 else (xs[n // 2 - 1] + xs[n // 2]) / 2.0
    ph = med([x[0] for x in h2h]); pd_ = med([x[1] for x in h2h]); pa = med([x[2] for x in h2h])
    dv = devig([ph, pd_, pa])
    if not dv:
        return None
    probs, margin = dv
    total = med(totals) if totals else None
    lh, la = goals_from_probs(probs[0], probs[2], total)
    return {"home": home, "away": away, "ko": ev.get("commence_time"),
            "xgh": round(lh, 3), "xga": round(la, 3),
            "pHome": round(probs[0], 3), "pDraw": round(probs[1], 3),
            "pAway": round(probs[2], 3), "margin": round(margin, 4),
            "books": len(h2h), "totalLine": total}


# ---- matching bookmaker names to FPL clubs --------------------------------
ODDS_ALIASES = {
    "tottenham hotspur": "spurs", "tottenham": "spurs",
    "manchester united": "man utd", "manchester city": "man city",
    "nottingham forest": "nott'm forest", "newcastle united": "newcastle",
    "leeds united": "leeds", "west ham united": "west ham",
    "brighton and hove albion": "brighton", "brighton hove albion": "brighton",
    "wolverhampton wanderers": "wolves", "afc bournemouth": "bournemouth",
    "sheffield united": "sheffield utd", "luton town": "luton",
}


def _norm(s):
    s = (s or "").lower().strip()
    for junk in (" fc", " afc", "."):
        s = s.replace(junk, " ")
    return " ".join(s.split())


def build_team_index(teams):
    idx = {}
    for t in teams:
        idx[_norm(t["name"])] = t["id"]
        idx[_norm(t["short_name"])] = t["id"]
    return idx


def match_team(name, idx):
    n = _norm(name)
    if n in idx:
        return idx[n]
    if ODDS_ALIASES.get(n) and _norm(ODDS_ALIASES[n]) in idx:
        return idx[_norm(ODDS_ALIASES[n])]
    # last resort: the FPL name is a distinctive substring of the bookmaker's
    best, best_len = None, 0
    for k, v in idx.items():
        if len(k) >= 4 and (k in n or n in k) and len(k) > best_len:
            best, best_len = v, len(k)
    return best


def odds_by_fixture(fixtures, teams):
    """{fpl fixture id: market expectation} for everything the market has priced."""
    events = fetch_odds()
    if not events:
        return {}, []
    idx = build_team_index(teams)
    priced, unmatched = {}, []
    parsed = []
    for ev in events:
        p = parse_event(ev)
        if p:
            parsed.append(p)
    for p in parsed:
        h, a = match_team(p["home"], idx), match_team(p["away"], idx)
        if not h or not a:
            unmatched.append("%s v %s" % (p["home"], p["away"]))
            continue
        for f in fixtures:
            if is_played(f) or f["team_h"] != h or f["team_a"] != a:
                continue
            priced[f["id"]] = p
            break
    _odds_state["matched"] = len(priced)
    _odds_state["unmatched"] = unmatched
    return priced, unmatched


# ---------------------------------------------------------------------------
# Team strength, from results rather than a pre-season opinion
# ---------------------------------------------------------------------------
# The FPL difficulty rating is set before a ball is kicked and never moves. These
# ratings are rebuilt from goals actually scored and conceded, shrunk toward the
# league average so that one freak result does not dominate in August.
PRIOR_MATCHES = 6.0        # weight of the "league average" prior, in matches
HOME_ADV = 1.15            # goals multiplier at home, /1.15 away


def is_played(f):
    """Has this match been played, as far as the scoreline is concerned?

    FPL sets `finished` only once bonus points have been confirmed, which lags
    the final whistle by a day or more -- through that window a whole round of
    football has been played and `finished` is still false on every fixture of
    it. `finished_provisional` goes true at full time.

    Everything here reads scorelines, and a scoreline does not change when bonus
    is applied, so the provisional flag is the right one. Using `finished` meant
    the league table and the team ratings both ignored the most recent round
    until FPL got round to awarding three bonus points.
    """
    return bool((f.get("finished") or f.get("finished_provisional"))
                and f.get("team_h_score") is not None
                and f.get("team_a_score") is not None)


def fdr_prior(fixtures, teams):
    """Pre-season attack and defence, from FPL's own published difficulty.

    The published rating is a bad label for a single fixture -- it never issues a
    1, calls 45% of matches a 3, and often gives both sides the same number. But
    averaged over a club's whole season it is a good power ranking, which is a
    different question. Taking the difficulty FPL assigns to a club's OPPONENTS
    and regressing last season's realised attack and defence on it gives a
    correlation of 0.895 and -0.895 respectively, on these fitted lines. So it
    earns its place as the prior the ratings start from in August, rather than
    assuming all twenty clubs are identical.
    """
    seen = {t["id"]: [] for t in teams}
    for f in fixtures:
        if f["team_h"] in seen and f.get("team_a_difficulty"):
            seen[f["team_h"]].append(f["team_a_difficulty"])
        if f["team_a"] in seen and f.get("team_h_difficulty"):
            seen[f["team_a"]].append(f["team_h_difficulty"])
    out = {}
    for tid, xs in seen.items():
        if not xs:
            out[tid] = (1.0, 1.0)
            continue
        d = sum(xs) / float(len(xs))
        att = max(0.55, min(1.60, 0.267 * d + 0.186))
        dfn = max(0.55, min(1.60, -0.231 * d + 1.705))
        out[tid] = (att, dfn)
    return out


def team_strength(fixtures, teams):
    """Attack and defence multipliers per team, 1.0 = league average."""
    rec = {t["id"]: {"gf": 0.0, "ga": 0.0, "p": 0} for t in teams}
    prior = fdr_prior(fixtures, teams)
    done = [f for f in fixtures if is_played(f)]
    for f in done:
        h, a = rec.get(f["team_h"]), rec.get(f["team_a"])
        if not h or not a:
            continue
        hs, as_ = float(f["team_h_score"]), float(f["team_a_score"])
        h["gf"] += hs; h["ga"] += as_; h["p"] += 1
        a["gf"] += as_; a["ga"] += hs; a["p"] += 1
    total_goals = sum(r["gf"] for r in rec.values())
    total_games = sum(r["p"] for r in rec.values())
    avg = (total_goals / total_games) if total_games else 1.4   # goals per team per match
    out = {}
    for tid, r in rec.items():
        # shrink toward FPL's pre-season power ranking rather than toward
        # "everyone is average", which is only true before the fixtures are out
        pa, pd_ = prior.get(tid, (1.0, 1.0))
        att = (r["gf"] + avg * pa * PRIOR_MATCHES) / (r["p"] + PRIOR_MATCHES) / avg
        dfn = (r["ga"] + avg * pd_ * PRIOR_MATCHES) / (r["p"] + PRIOR_MATCHES) / avg
        out[tid] = {"att": round(att, 3), "def": round(dfn, 3),
                    "played": r["p"], "gf": r["gf"], "ga": r["ga"],
                    "priorAtt": round(pa, 3), "priorDef": round(pd_, 3)}
    out["_avg"] = avg
    out["_played"] = (total_games // 2) if total_games else 0
    return out


def match_expectation(strength, team_id, opp_id, home):
    """Expected goals for and against in one fixture, plus a clean-sheet chance.

    Poisson: the probability of conceding zero is exp(-expected goals against).
    """
    avg = strength["_avg"]
    t, o = strength.get(team_id), strength.get(opp_id)
    if not t or not o:
        return {"xgf": avg, "xga": avg, "cs": math.exp(-avg)}
    ha = HOME_ADV if home else 1.0 / HOME_ADV
    xgf = avg * t["att"] * o["def"] * ha
    xga = avg * o["att"] * t["def"] / ha
    return {"xgf": round(xgf, 3), "xga": round(xga, 3),
            "cs": round(math.exp(-xga), 3)}


# --- fixture difficulty, on one scale from end to end -----------------------
# Difficulty is the market's view of the match, expressed as the gap between
# winning and losing:
#
#     edge = P(win) - P(lose)
#
# An evenly priced match has an edge of zero and rates 3. The further the price
# tilts, the further the rating moves from the middle. Where bookmakers have
# priced a fixture the probabilities are theirs. Beyond their horizon -- they
# rarely price more than a fortnight out -- the same arithmetic runs on
# probabilities from the results-based ratings, so a 3 in six weeks' time means
# what a 3 next Saturday means.
#
# Two earlier attempts are worth recording. Fixed thresholds in goals were wrong
# because home advantage alone is worth 0.84 goals against bands 0.5 goals wide,
# so the rating mostly reported the venue. Ranking fixtures into quintiles fixed
# that but made the scale relative to whatever six weeks happened to be in view,
# so an easy run could not look easy. On the edge scale venue is worth about
# 0.37 against bands 0.25-0.30 wide: it moves a fixture one band, which is
# roughly what playing at home is actually worth.
EDGE_BANDS = (0.40, 0.15, -0.15, -0.40)


def win_probs(exp_):
    """Win, draw and lose probabilities implied by a pair of goal expectations."""
    return _poisson_probs(max(0.05, exp_["xgf"]), max(0.05, exp_["xga"]))


def difficulty_from_edge(edge):
    """1 is the kindest fixture, 3 a coin toss, 5 the hardest."""
    if edge >= EDGE_BANDS[0]:
        return 1
    if edge >= EDGE_BANDS[1]:
        return 2
    if edge >= EDGE_BANDS[2]:
        return 3
    if edge >= EDGE_BANDS[3]:
        return 4
    return 5


def rating_confidence(played):
    """How far to trust the results-based edge, given the matches behind it.

    Fitted, not guessed. Simulating seasons from known team strengths and
    regressing the true edge on the model's gives the shrinkage that minimises
    error: it levels off near 0.78. The ratings stay roughly a quarter too
    extreme even in midwinter, because a fixture's expectation multiplies two
    noisy strength numbers and the noise in both compounds, so the shrink never
    reaches 1.0.

    The August end of the curve was originally much harsher, because back then
    the ratings started from "every club is average" and knew nothing. They now
    start from FPL's published power ranking, which correlates about 0.9 with
    how clubs actually turn out, so round one is no longer a blank sheet and the
    early damping is correspondingly lighter.
    """
    return 0.78 - 0.08 / max(1.0, float(played or 0))


def difficulty_from(exp_, probs=None, conf=1.0):
    """Difficulty for one fixture. Pass market probabilities when they exist.

    The results-based edge is pulled toward even by rating_confidence(), which
    corrects for the ratings being systematically too extreme -- sharply so in
    August, mildly so all season.

    The market needs none of this. A bookmaker's price already knows who is good
    in week one, so a priced fixture passes through untouched.
    """
    if probs:
        p_win, _p_draw, p_lose = probs
    else:
        p_win, _p_draw, p_lose = win_probs(exp_)
    edge = (p_win - p_lose) * max(0.0, min(1.0, conf))
    return difficulty_from_edge(edge), round(edge, 3)


def build_fixture_map(fixtures, teams, from_gw, strength, priced=None):
    """Each team's next FIX_GWS gameweeks, priced by the market where possible.

    Every fixture is labelled on the same absolute edge scale, so no pass over
    the whole set is needed and an easy run is allowed to look easy.
    """
    priced = priced or {}
    # the season ends; do not invent gameweek 41
    last_gw = max([f.get("event") or 0 for f in fixtures] or [from_gw + FIX_GWS])
    gws = [g for g in range(from_gw, from_gw + FIX_GWS) if g <= last_gw]
    out = {}
    short = {t["id"]: t["short_name"] for t in teams}

    for t in teams:
        runs, diffs, css, atts = [], [], [], []
        for gw in gws:
            games = [f for f in fixtures if f.get("event") == gw
                     and (f["team_h"] == t["id"] or f["team_a"] == t["id"])]
            if not games:
                runs.append({"gw": gw, "opp": None, "ha": "-", "fdr": None,
                             "cs": None, "xgf": None, "src": None})
                continue
            for f in games:
                home = f["team_h"] == t["id"]
                opp = f["team_a"] if home else f["team_h"]
                mk = priced.get(f["id"])
                # always compute the results-based view, so a market-priced
                # fixture can show both numbers side by side and be audited
                form_e = match_expectation(strength, t["id"], opp, home)
                # trust the ratings in proportion to the football behind them
                played = min((strength.get(t["id"]) or {}).get("played", 0),
                             (strength.get(opp) or {}).get("played", 0))
                conf = rating_confidence(played)
                form_d, form_edge = difficulty_from(form_e, None, conf)
                if mk:
                    xgf = mk["xgh"] if home else mk["xga"]
                    xga = mk["xga"] if home else mk["xgh"]
                    e = {"xgf": xgf, "xga": xga, "cs": round(math.exp(-xga), 3)}
                    # the market's own probabilities, not a Poisson round-trip
                    probs = ((mk["pHome"], mk["pDraw"], mk["pAway"]) if home
                             else (mk["pAway"], mk["pDraw"], mk["pHome"]))
                    src = "odds"
                else:
                    e, probs, src = form_e, None, "form"
                if probs:                      # the market needs no shrinking
                    d, edge = difficulty_from(e, probs)
                else:
                    d, edge = form_d, form_edge
                # FPL's published rating, carried through for comparison only:
                # nothing downstream reads it.
                fpl_pub = f.get("team_h_difficulty" if home else "team_a_difficulty")
                runs.append({"gw": int(gw), "opp": short.get(opp, "?"),
                             "ha": "H" if home else "A", "fdr": d,
                             "edge": edge, "fplFdr": fpl_pub,
                             "cs": e["cs"], "xgf": e["xgf"], "xga": e["xga"],
                             "src": src,
                             "altXgf": (form_e["xgf"] if mk else None),
                             "altCs": (form_e["cs"] if mk else None),
                             "altEdge": (form_edge if mk else None),
                             "altFdr": (form_d if mk else None)})
                diffs.append(d); css.append(e["cs"]); atts.append(e["xgf"])
        out[t["id"]] = {
            "runs": runs,
            "avgFdr": round(sum(diffs) / len(diffs), 2) if diffs else None,
            "csNext": round(sum(css) / len(css), 3) if css else None,
            "xgfNext": round(sum(atts) / len(atts), 3) if atts else None,
        }
    return out


# ---------------------------------------------------------------------------
# Per-gameweek history -> multi-window form, hit rates, real minutes
# ---------------------------------------------------------------------------
FORM_WINDOW = 6            # how many recent gameweeks to pull


def gw_history(current_gw, window=FORM_WINDOW, fixtures=None, teams=None):
    """Per-player match logs from the live endpoint, newest gameweek last.

    One request per gameweek rather than one per player, so six calls covers the
    whole league. The endpoint carries the full scoring line, not just minutes,
    so the log records what a player actually did and who he did it against --
    which is what makes "how did he play last week" an answerable question
    rather than something to be inferred from a rolling average.

    Note `starts`: the API says outright whether a player was in the eleven.
    An earlier version inferred it from playing 60 minutes, which quietly
    mislabels every starter hooked on the hour and every substitute who came on
    early for an injury.
    """
    hist, got = {}, []
    start = max(1, current_gw - window + 1)
    opp = {}
    short = {t["id"]: t["short_name"] for t in (teams or [])}
    for f in (fixtures or []):
        ev = f.get("event")
        if not ev:
            continue
        opp[(ev, f["team_h"])] = (short.get(f["team_a"], "?"), "H")
        opp[(ev, f["team_a"])] = (short.get(f["team_h"], "?"), "A")
    for gw in range(start, current_gw + 1):
        try:
            live = fetch("/event/%d/live/" % gw, ttl=600)
        except FPLError:
            continue
        for el in live.get("elements", []):
            st = el.get("stats") or {}
            mins = num(st.get("minutes"))
            hist.setdefault(el["id"], []).append({
                "gw": gw,
                "mins": mins,
                "pts": num(st.get("total_points")),
                "dc": num(st.get("defensive_contribution")),
                "xgi": num(st.get("expected_goal_involvements")),
                "goals": num(st.get("goals_scored")),
                "assists": num(st.get("assists")),
                "cs": num(st.get("clean_sheets")),
                "gc": num(st.get("goals_conceded")),
                "saves": num(st.get("saves")),
                "bonus": num(st.get("bonus")),
                "bps": num(st.get("bps")),
                "yc": num(st.get("yellow_cards")),
                "rc": num(st.get("red_cards")),
                "og": num(st.get("own_goals")),
                # the API's own flag where it exists; only fall back to the
                # 60-minute proxy if the field is genuinely absent, never
                # because it is present and zero
                "started": (bool(num(st.get("starts"))) if st.get("starts") is not None
                            else mins >= 60),
            })
        got.append(gw)
    # attach who each match was against, once the club is known
    hist["__opp__"] = opp
    return hist, got


# Last season (2025-26) per-90 rates, keyed by the player's permanent FPL code.
# Codes are stable across seasons; element ids are not (they are reassigned every
# July, and joining on them lands on the right player 0.8% of the time). Fields:
#   code pos mins xG/90 xA/90 xGC/90 dcHitRate saves/90 bonus/90 yellow/90 start60Rate
# Only players with 180+ minutes are carried; below that the rates are noise.
PRIOR_SEASON = "2025-26"
PRIOR_TABLE = """\
15157 3 772 0.120 0.077 1.495 0.000 0.00 0.000 0.233 0.350
17761 2 3330 0.068 0.057 1.447 0.595 0.00 0.324 0.216 1.000
50175 4 2249 0.495 0.056 1.268 0.000 0.00 0.720 0.200 0.676
54469 2 1073 0.000 0.019 1.525 0.000 0.00 0.336 0.252 0.500
56979 3 1911 0.016 0.109 1.326 0.094 0.00 0.235 0.283 0.594
57328 2 592 0.065 0.091 1.587 0.000 0.00 0.304 0.152 0.600
58621 2 3095 0.004 0.038 1.964 0.111 0.00 0.087 0.262 0.944
59735 1 1980 0.000 0.002 1.289 0.000 2.86 0.136 0.045 1.000
60307 3 1636 0.076 0.217 1.120 0.105 0.00 0.550 0.110 0.947
60689 4 896 0.431 0.032 1.450 0.000 0.00 0.402 0.000 0.667
61256 3 2575 0.190 0.111 1.110 0.412 0.00 0.699 0.315 0.853
67089 1 3150 0.000 0.001 2.036 0.000 3.63 0.200 0.029 1.000
72147 1 585 0.000 0.000 1.695 0.000 2.92 0.000 0.308 0.857
75115 4 1234 0.554 0.039 1.567 0.000 0.00 0.511 0.073 0.250
76357 3 756 0.144 0.096 1.389 0.000 0.00 0.119 0.357 0.292
77794 2 1586 0.005 0.117 1.208 0.048 0.00 0.113 0.170 0.857
78916 2 2195 0.044 0.015 1.236 0.345 0.00 0.205 0.369 0.828
79602 1 270 0.000 0.000 1.700 0.000 2.33 0.000 0.000 1.000
80201 1 3420 0.000 0.001 1.388 0.000 2.58 0.211 0.079 1.000
80801 3 2094 0.086 0.079 1.344 0.200 0.00 0.172 0.043 0.960
83299 2 2837 0.058 0.018 1.329 0.242 0.00 0.159 0.317 0.939
84182 1 1800 0.000 0.000 1.765 0.000 3.85 0.100 0.000 1.000
84450 3 2901 0.031 0.116 1.417 0.382 0.00 0.248 0.248 0.941
85633 1 2667 0.000 0.002 1.523 0.000 3.21 0.101 0.067 0.935
87835 2 786 0.010 0.022 1.618 0.000 0.00 0.000 0.458 0.727
88248 1 270 0.000 0.003 1.550 0.000 2.67 0.000 0.000 1.000
88894 3 844 0.168 0.134 1.408 0.048 0.00 0.533 0.107 0.333
91889 4 407 0.206 0.046 1.900 0.000 0.00 0.000 0.000 0.500
95658 2 1649 0.061 0.027 1.253 0.348 0.00 0.273 0.164 0.826
97032 2 3420 0.099 0.038 1.253 0.421 0.00 0.263 0.105 1.000
97299 2 436 0.000 0.019 1.367 0.111 0.00 0.000 0.000 0.556
98747 1 2416 0.006 0.000 1.225 0.000 3.32 0.112 0.075 1.000
98980 1 2835 0.000 0.003 1.363 0.000 3.02 0.349 0.063 0.969
101178 3 1092 0.020 0.154 1.922 0.167 0.00 0.000 0.082 0.667
101188 2 1842 0.033 0.160 1.358 0.032 0.00 0.244 0.147 0.613
101982 1 1080 0.000 0.002 1.549 0.000 3.25 0.000 0.000 1.000
102057 4 2183 0.477 0.037 1.441 0.000 0.00 0.289 0.206 0.639
106611 2 2588 0.080 0.017 1.548 0.455 0.00 0.278 0.035 0.879
106760 2 3220 0.020 0.055 1.255 0.132 0.00 0.084 0.252 0.974
108413 3 1560 0.064 0.112 1.463 0.000 0.00 0.000 0.404 0.419
109646 2 788 0.013 0.046 1.513 0.188 0.00 0.228 0.228 0.438
110504 3 634 0.068 0.035 1.383 0.000 0.00 0.142 0.142 0.583
111234 1 3420 0.000 0.005 1.480 0.000 2.63 0.289 0.105 1.000
111317 3 1188 0.440 0.258 1.534 0.000 0.00 0.303 0.530 0.387
111478 2 1047 0.099 0.017 1.485 0.125 0.00 0.086 0.430 0.375
114243 3 1606 0.172 0.149 1.365 0.000 0.00 0.280 0.112 0.515
114283 3 1627 0.113 0.186 1.428 0.000 0.00 0.664 0.166 0.900
116216 3 1997 0.252 0.162 0.628 0.000 0.00 0.496 0.090 0.645
116535 1 2340 0.000 0.001 1.138 0.000 2.19 0.308 0.038 1.000
118748 3 2144 0.345 0.228 1.299 0.000 0.00 0.462 0.042 0.852
119471 2 1089 0.080 0.050 1.145 0.375 0.00 0.000 0.083 0.688
122798 2 1165 0.085 0.108 1.347 0.000 0.00 0.309 0.000 0.375
122806 3 2136 0.126 0.173 1.394 0.033 0.00 0.253 0.211 0.833
126184 2 686 0.094 0.070 1.292 0.056 0.00 0.131 0.131 0.389
135720 2 1489 0.037 0.017 1.218 0.500 0.00 0.060 0.484 0.625
141746 3 3065 0.317 0.361 1.304 0.143 0.00 1.204 0.147 0.971
149065 1 2070 0.000 0.002 1.532 0.000 2.83 0.348 0.087 1.000
149484 2 1322 0.089 0.029 1.591 0.235 0.00 0.272 0.068 0.824
152551 3 1722 0.096 0.077 1.312 0.129 0.00 0.157 0.366 0.516
153133 3 2420 0.071 0.175 1.328 0.034 0.00 0.483 0.112 0.966
153682 3 2674 0.198 0.161 1.351 0.028 0.00 0.707 0.236 0.833
154296 3 2192 0.112 0.027 1.339 0.364 0.00 0.698 0.328 0.636
154561 1 3330 0.000 0.002 0.745 0.000 1.62 0.297 0.027 1.000
154566 4 997 0.268 0.031 1.607 0.000 0.00 0.361 0.090 0.667
155408 3 872 0.007 0.054 1.445 0.389 0.00 0.000 0.103 0.444
155503 1 212 0.000 0.000 2.021 0.000 3.82 0.000 0.000 0.667
155511 4 1141 0.218 0.067 1.809 0.000 0.00 0.079 0.237 0.929
158499 3 978 0.167 0.073 1.761 0.038 0.00 0.184 0.276 0.269
158534 2 1378 0.074 0.024 1.804 0.087 0.00 0.000 0.131 0.609
159506 2 1587 0.023 0.048 1.435 0.111 0.00 0.284 0.170 1.000
159533 3 376 0.165 0.136 2.006 0.000 0.00 0.000 0.239 0.083
165809 3 2869 0.085 0.129 1.116 0.053 0.00 0.125 0.314 0.816
166477 2 1838 0.073 0.072 1.599 0.067 0.00 0.147 0.196 0.633
166989 3 1857 0.055 0.158 1.519 0.080 0.00 0.145 0.000 0.800
167074 2 1791 0.046 0.073 1.296 0.318 0.00 0.251 0.101 0.864
167512 2 565 0.024 0.021 1.472 0.083 0.00 0.159 0.159 0.500
167887 3 1752 0.045 0.025 2.014 0.121 0.00 0.051 0.308 0.485
168636 4 214 0.841 0.029 2.591 0.000 0.00 0.421 0.421 0.000
169528 2 1487 0.065 0.096 1.460 0.182 0.00 0.424 0.303 0.727
171287 2 594 0.042 0.097 1.411 0.000 0.00 0.303 0.606 0.238
171314 2 2139 0.024 0.027 1.097 0.192 0.00 0.168 0.126 0.885
172567 3 1513 0.056 0.081 1.933 0.333 0.00 0.476 0.119 0.944
172649 1 3330 0.000 0.003 1.389 0.000 2.86 0.189 0.135 1.000
173879 4 278 0.664 0.117 1.658 0.000 0.00 0.647 0.000 0.083
174592 3 1058 0.127 0.157 2.093 0.000 0.00 0.170 0.000 0.478
174594 4 1065 0.613 0.134 1.846 0.000 0.00 0.676 0.000 0.290
174874 2 2882 0.045 0.057 1.402 0.606 0.00 0.250 0.219 0.939
177815 4 2721 0.515 0.035 1.182 0.000 0.00 0.662 0.099 0.857
178186 4 3406 0.191 0.138 1.537 0.158 0.00 0.740 0.106 1.000
178301 4 2833 0.489 0.037 1.378 0.000 0.00 0.826 0.127 0.865
179268 2 2706 0.078 0.107 1.379 0.059 0.00 0.166 0.266 0.853
179458 3 1014 0.122 0.103 2.082 0.000 0.00 0.000 0.000 0.250
180135 3 1003 0.110 0.168 1.425 0.087 0.00 0.449 0.179 0.391
180736 2 2780 0.047 0.033 1.322 0.412 0.00 0.227 0.097 0.882
180804 2 1201 0.046 0.009 2.226 0.357 0.00 0.000 0.075 0.929
180974 3 1950 0.109 0.062 1.327 0.296 0.00 0.092 0.462 0.741
184029 3 1363 0.083 0.241 1.070 0.042 0.00 0.330 0.000 0.458
184254 1 2790 0.000 0.001 1.491 0.000 2.68 0.194 0.032 1.000
184341 3 1010 0.139 0.144 1.110 0.087 0.00 0.267 0.178 0.435
184349 3 1816 0.079 0.089 1.305 0.185 0.00 0.396 0.000 0.741
184667 2 942 0.027 0.010 1.522 0.000 0.00 0.000 0.000 0.588
184754 3 1439 0.148 0.098 1.462 0.000 0.00 0.000 0.313 0.577
191866 2 1805 0.034 0.036 1.571 0.333 0.00 0.050 0.199 0.704
194010 2 1322 0.012 0.037 1.628 0.000 0.00 0.000 0.136 0.520
195384 3 1024 0.295 0.127 0.647 0.000 0.00 0.439 0.088 0.364
195546 3 1753 0.174 0.114 1.439 0.083 0.00 0.513 0.308 0.417
198869 2 699 0.058 0.089 1.118 0.083 0.00 0.386 0.000 0.583
199598 3 3119 0.071 0.063 1.404 0.543 0.00 0.317 0.289 1.000
199796 2 3016 0.034 0.088 1.356 0.029 0.00 0.209 0.269 0.943
199798 2 3035 0.038 0.017 1.451 0.088 0.00 0.089 0.000 1.000
200089 3 972 0.117 0.099 1.651 0.000 0.00 0.000 0.278 0.333
200617 3 547 0.150 0.117 2.368 0.000 0.00 0.000 0.000 0.158
200720 1 3330 0.000 0.006 1.445 0.000 2.95 0.297 0.027 1.000
200785 3 1769 0.032 0.032 1.383 0.280 0.00 0.153 0.407 0.800
200834 2 2784 0.052 0.086 1.445 0.406 0.00 0.356 0.162 0.969
201595 1 1440 0.000 0.000 1.667 0.000 2.38 0.188 0.125 1.000
201658 3 2732 0.298 0.152 1.353 0.088 0.00 0.461 0.198 0.912
201666 3 1951 0.316 0.125 1.398 0.000 0.00 0.415 0.046 0.486
201895 2 2797 0.052 0.029 1.433 0.364 0.00 0.161 0.193 0.939
202993 3 1880 0.034 0.040 1.132 0.500 0.00 0.191 0.335 0.808
204120 2 799 0.006 0.053 1.224 0.167 0.00 0.451 0.225 0.667
204480 3 3093 0.092 0.213 0.695 0.389 0.00 0.669 0.087 0.972
204580 3 1434 0.051 0.142 1.671 0.280 0.00 0.377 0.502 0.600
204646 3 640 0.567 0.049 1.489 0.000 0.00 0.422 0.000 0.190
204716 2 3090 0.035 0.029 1.184 0.361 0.00 0.233 0.204 0.944
204936 1 3060 0.000 0.004 1.132 0.000 2.29 0.147 0.235 1.000
204968 3 602 0.073 0.055 1.280 0.045 0.00 0.000 0.449 0.136
205533 4 414 0.385 0.100 2.063 0.000 0.00 0.652 0.435 0.167
205651 4 418 0.583 0.056 0.855 0.000 0.00 0.000 0.646 0.071
206325 2 352 0.018 0.092 1.284 0.000 0.00 0.000 0.000 0.800
206915 3 1923 0.103 0.130 1.471 0.118 0.00 0.281 0.094 0.529
207189 3 2904 0.048 0.046 1.335 0.143 0.00 0.093 0.155 0.943
207283 3 2239 0.089 0.244 1.436 0.111 0.00 0.040 0.121 0.722
208706 3 2456 0.205 0.182 1.172 0.172 0.00 0.806 0.220 0.931
208912 2 496 0.015 0.004 2.119 0.273 0.00 0.000 0.000 0.364
209036 2 3150 0.116 0.068 1.274 0.314 0.00 0.400 0.171 1.000
209041 3 457 0.049 0.055 2.393 0.000 0.00 0.000 0.197 0.333
209046 3 1838 0.136 0.148 1.512 0.000 0.00 0.392 0.000 0.567
209243 3 863 0.064 0.195 1.471 0.000 0.00 0.000 0.000 0.261
209244 3 2078 0.261 0.206 1.186 0.091 0.00 0.563 0.173 0.667
209289 3 1909 0.222 0.053 1.474 0.000 0.00 0.047 0.047 0.514
209365 2 1170 0.106 0.064 1.441 0.308 0.00 0.385 0.000 1.000
209400 3 1899 0.078 0.154 1.234 0.179 0.00 0.000 0.142 0.714
210156 4 480 0.690 0.144 1.941 0.000 0.00 0.750 0.375 0.118
210462 3 2073 0.050 0.078 1.440 0.321 0.00 0.087 0.217 0.786
210494 2 180 0.050 0.015 1.710 0.500 0.00 0.000 0.000 1.000
212314 3 1730 0.116 0.099 1.438 0.115 0.00 0.208 0.468 0.654
212319 4 1954 0.398 0.067 1.181 0.000 0.00 0.783 0.230 0.594
214048 2 1559 0.032 0.014 1.921 0.286 0.00 0.000 0.231 0.810
214225 2 2952 0.043 0.017 1.480 0.286 0.00 0.152 0.091 0.914
214590 2 2080 0.000 0.043 1.533 0.320 0.00 0.000 0.173 0.920
215059 1 3040 0.000 0.001 1.440 0.000 2.90 0.207 0.089 0.971
215136 2 3203 0.056 0.112 1.443 0.108 0.00 0.421 0.169 0.919
215379 3 3332 0.079 0.129 1.449 0.684 0.00 0.432 0.216 0.974
215413 3 2629 0.149 0.183 1.382 0.161 0.00 0.616 0.205 0.935
215439 3 2190 0.235 0.021 1.581 0.057 0.00 0.370 0.123 0.657
215711 3 450 0.100 0.292 1.406 0.000 0.00 0.000 0.200 0.231
216051 2 2609 0.067 0.089 1.262 0.088 0.00 0.310 0.172 0.824
216055 3 2100 0.027 0.022 1.983 0.452 0.00 0.000 0.257 0.742
216094 2 1032 0.044 0.135 1.131 0.000 0.00 0.087 0.087 0.476
216646 4 517 0.545 0.094 1.736 0.000 0.00 0.000 0.522 0.211
218328 3 1067 0.177 0.283 1.582 0.000 0.00 0.084 0.000 0.391
219168 4 694 0.336 0.010 1.087 0.000 0.00 0.519 0.000 0.571
219249 3 202 0.539 0.080 1.127 0.000 0.00 0.891 0.000 0.333
219847 4 577 0.516 0.100 1.042 0.000 0.00 0.468 0.156 0.417
219924 2 812 0.089 0.006 1.377 0.077 0.00 0.333 0.222 0.615
220237 2 1834 0.085 0.042 1.353 0.440 0.00 0.294 0.098 0.800
220362 2 1254 0.079 0.002 1.331 0.143 0.00 0.072 0.072 1.000
220566 3 1510 0.069 0.146 1.236 0.381 0.00 0.358 0.179 0.762
220627 2 1893 0.087 0.055 1.569 0.138 0.00 0.428 0.190 0.690
221389 1 437 0.000 0.000 1.262 0.000 1.24 0.000 0.206 1.000
221399 3 262 0.096 0.079 1.312 0.000 0.00 0.000 0.000 0.091
221466 2 3288 0.042 0.129 1.499 0.703 0.00 0.383 0.219 1.000
221632 2 1869 0.067 0.060 1.364 0.391 0.00 0.482 0.433 0.870
221820 2 1229 0.011 0.044 1.115 0.222 0.00 0.220 0.000 0.667
222531 3 3101 0.314 0.084 1.442 0.027 0.00 0.522 0.029 0.946
222683 3 945 0.220 0.148 1.710 0.000 0.00 0.286 0.476 0.450
222694 2 2935 0.094 0.023 1.316 0.382 0.00 0.123 0.153 0.941
223094 4 2953 0.777 0.081 1.176 0.000 0.00 1.311 0.061 0.943
223340 3 2218 0.307 0.291 0.632 0.161 0.00 0.730 0.081 0.742
223541 3 317 0.412 0.173 1.845 0.000 0.00 0.000 0.852 0.038
223827 2 2144 0.103 0.026 1.394 0.483 0.00 0.378 0.168 0.759
224024 3 1513 0.170 0.119 1.441 0.111 0.00 0.476 0.297 1.000
224117 4 2217 0.498 0.079 0.723 0.000 0.00 0.650 0.203 0.611
224967 2 2959 0.009 0.075 1.472 0.212 0.00 0.061 0.182 1.000
225321 1 1003 0.000 0.000 1.690 0.000 2.24 0.090 0.179 0.917
225796 2 1957 0.048 0.147 1.322 0.069 0.00 0.506 0.184 0.655
226182 2 2795 0.067 0.100 1.286 0.059 0.00 0.032 0.193 0.912
226597 2 2750 0.096 0.057 0.720 0.344 0.00 0.982 0.131 0.938
226944 3 1410 0.034 0.054 1.328 0.167 0.00 0.447 0.319 0.889
227127 3 600 0.054 0.015 1.831 0.182 0.00 0.000 0.600 0.455
227444 2 3375 0.022 0.018 1.466 0.342 0.00 0.053 0.160 0.974
230001 2 977 0.018 0.032 1.197 0.050 0.00 0.553 0.276 0.500
230046 3 913 0.052 0.140 1.305 0.000 0.00 0.000 0.296 0.381
230376 3 1117 0.272 0.050 1.289 0.087 0.00 0.161 0.081 0.435
231057 3 1239 0.076 0.077 1.708 0.000 0.00 0.000 0.363 0.462
231065 2 318 0.003 0.017 1.047 0.500 0.00 0.566 0.283 1.000
231416 2 3130 0.059 0.095 1.283 0.054 0.00 0.201 0.173 0.946
231480 2 2552 0.080 0.051 1.542 0.172 0.00 0.141 0.141 0.966
231747 4 2210 0.587 0.054 1.294 0.000 0.00 0.529 0.081 0.719
232112 3 876 0.074 0.016 1.872 0.182 0.00 0.000 0.103 0.364
232185 3 2173 0.453 0.048 1.294 0.000 0.00 0.373 0.083 0.786
232413 3 1885 0.247 0.127 0.678 0.000 0.00 0.382 0.048 0.545
232653 3 1441 0.075 0.091 1.701 0.071 0.00 0.187 0.187 0.464
232787 3 1183 0.094 0.053 1.448 0.125 0.00 0.228 0.152 0.812
232826 3 1798 0.439 0.169 1.240 0.000 0.00 0.501 0.150 0.808
232859 2 2049 0.040 0.078 1.380 0.033 0.00 0.132 0.176 0.733
232892 2 2532 0.061 0.012 1.351 0.267 0.00 0.320 0.178 0.933
232928 3 3413 0.055 0.163 1.481 0.526 0.00 0.343 0.316 1.000
233963 2 2532 0.088 0.025 1.458 0.581 0.00 0.178 0.071 0.871
235826 4 244 0.332 0.048 2.512 0.000 0.00 0.000 0.000 0.062
242880 2 470 0.000 0.011 1.419 0.125 0.00 0.000 0.383 0.375
242882 2 1275 0.001 0.013 1.586 0.222 0.00 0.141 0.071 0.722
242898 3 1710 0.129 0.069 1.489 0.000 0.00 0.105 0.316 0.471
243016 3 2654 0.132 0.057 1.254 0.108 0.00 0.305 0.237 0.784
243298 3 2736 0.275 0.154 1.149 0.028 0.00 0.164 0.099 0.861
243526 2 2637 0.038 0.099 1.401 0.062 0.00 0.273 0.137 0.875
243571 2 238 0.011 0.015 1.388 0.286 0.00 0.000 0.000 0.429
244042 4 987 0.301 0.014 1.261 0.000 0.00 0.274 0.182 0.429
244723 2 3253 0.044 0.070 1.377 0.158 0.00 0.221 0.166 0.921
244850 3 3280 0.188 0.119 1.414 0.027 0.00 0.466 0.192 1.000
244851 3 1954 0.486 0.115 1.434 0.077 0.00 0.507 0.230 0.808
244954 2 1673 0.072 0.021 1.227 0.095 0.00 0.108 0.054 0.857
246301 2 935 0.005 0.051 1.415 0.467 0.00 0.096 0.578 0.667
247348 2 2400 0.092 0.148 1.286 0.241 0.00 0.337 0.263 0.897
247412 4 2301 0.207 0.044 1.409 0.000 0.00 0.117 0.156 0.639
247632 3 2629 0.157 0.234 1.285 0.000 0.00 0.308 0.068 0.882
247670 4 1384 0.374 0.053 1.284 0.000 0.00 0.325 0.390 0.944
247693 4 1655 0.113 0.089 1.373 0.000 0.00 0.054 0.163 0.567
247955 2 1681 0.042 0.046 1.655 0.071 0.00 0.000 0.107 0.607
248056 3 1307 0.099 0.096 1.480 0.107 0.00 0.275 0.069 0.429
248857 3 1205 0.092 0.214 0.954 0.000 0.00 0.672 0.000 0.423
248875 3 1773 0.146 0.297 1.178 0.000 0.00 0.761 0.000 0.600
249231 2 1960 0.138 0.115 1.549 0.000 0.00 0.230 0.046 0.583
250199 3 1168 0.113 0.059 1.788 0.037 0.00 0.231 0.231 0.296
424876 3 3232 0.133 0.190 1.271 0.278 0.00 0.585 0.223 1.000
427623 2 2825 0.077 0.050 1.312 0.394 0.00 0.159 0.127 0.939
427637 3 2449 0.166 0.132 1.362 0.081 0.00 0.184 0.110 0.757
430871 3 2493 0.249 0.121 1.291 0.030 0.00 0.505 0.144 0.848
431248 2 2356 0.085 0.057 1.539 0.107 0.00 0.038 0.115 0.964
431639 4 1764 0.405 0.021 1.891 0.000 0.00 0.561 0.255 0.690
432422 3 2534 0.062 0.102 1.285 0.114 0.00 0.071 0.142 0.771
432714 3 288 0.056 0.116 2.294 0.000 0.00 0.000 0.312 0.071
432720 1 360 0.000 0.000 1.435 0.000 3.50 0.000 0.000 1.000
432830 2 2971 0.068 0.052 1.440 0.457 0.00 0.212 0.212 0.914
433036 3 1623 0.256 0.130 1.044 0.036 0.00 0.333 0.111 0.607
433154 3 1161 0.106 0.148 1.457 0.091 0.00 0.078 0.078 0.545
433312 3 872 0.169 0.039 1.379 0.231 0.00 0.103 0.206 0.692
434399 2 1966 0.006 0.028 1.223 0.160 0.00 0.275 0.320 0.840
434752 2 1888 0.043 0.036 1.501 0.440 0.00 0.286 0.191 0.840
435973 4 1361 0.213 0.024 1.846 0.000 0.00 0.265 0.265 0.538
435997 3 1553 0.304 0.076 1.422 0.000 0.00 0.637 0.174 0.643
437499 2 3085 0.071 0.024 1.285 0.571 0.00 0.321 0.117 0.971
437505 4 1148 0.368 0.030 1.554 0.000 0.00 0.549 0.078 0.281
437730 3 3200 0.312 0.088 1.341 0.081 0.00 0.506 0.197 0.946
437738 2 429 0.042 0.002 1.827 0.083 0.00 0.000 0.210 0.333
438234 3 691 0.362 0.100 1.032 0.000 0.00 0.651 0.391 0.238
440089 3 2046 0.115 0.239 1.388 0.182 0.00 0.396 0.000 0.667
440323 4 843 0.228 0.023 2.493 0.042 0.00 0.214 0.000 0.333
440993 3 2781 0.216 0.143 1.381 0.188 0.00 0.227 0.065 1.000
441164 2 2793 0.034 0.141 1.216 0.235 0.00 0.258 0.322 0.912
441191 2 1326 0.009 0.060 1.264 0.059 0.00 0.204 0.068 0.824
441264 4 1920 0.282 0.031 1.472 0.000 0.00 0.562 0.281 0.677
441266 3 2991 0.057 0.068 1.156 0.194 0.00 0.512 0.150 0.917
441271 2 423 0.004 0.077 1.991 0.125 0.00 0.000 0.000 0.500
441302 2 1590 0.071 0.135 1.508 0.067 0.00 0.057 0.113 0.567
444102 4 2741 0.349 0.049 1.281 0.000 0.00 0.197 0.066 0.833
444145 3 1065 0.348 0.107 0.888 0.000 0.00 0.254 0.254 0.167
444180 3 2717 0.169 0.094 1.954 0.027 0.00 0.199 0.132 0.811
444463 2 1718 0.038 0.031 1.352 0.280 0.00 0.157 0.262 0.720
444765 2 2761 0.110 0.047 1.356 0.375 0.00 0.098 0.065 0.938
445122 2 2452 0.173 0.056 0.640 0.100 0.00 0.330 0.184 0.867
446008 3 2611 0.413 0.172 1.236 0.000 0.00 0.552 0.138 0.939
448047 3 3114 0.325 0.210 1.297 0.056 0.00 0.549 0.289 0.972
448089 3 2829 0.041 0.066 1.546 0.429 0.00 0.191 0.318 0.886
448104 2 1787 0.018 0.084 0.883 0.280 0.00 0.353 0.101 0.720
448514 2 971 0.049 0.186 1.135 0.059 0.00 0.834 0.185 0.588
449027 1 867 0.000 0.000 1.380 0.000 3.53 0.208 0.000 0.900
449434 3 1302 0.114 0.120 1.459 0.000 0.00 0.000 0.000 0.344
449871 3 1755 0.086 0.035 1.463 0.280 0.00 0.205 0.154 0.800
450070 3 2470 0.198 0.122 1.369 0.032 0.00 0.364 0.219 0.903
451302 1 540 0.000 0.008 1.540 0.000 2.17 0.000 0.000 1.000
451340 3 1714 0.212 0.144 1.248 0.000 0.00 0.105 0.263 0.680
456512 3 1167 0.081 0.116 1.231 0.000 0.00 0.308 0.077 0.417
457569 1 3420 0.000 0.000 1.493 0.000 2.87 0.132 0.079 1.000
458249 4 607 0.406 0.050 1.395 0.000 0.00 0.890 0.445 0.167
460028 2 225 0.000 0.048 1.344 0.667 0.00 0.000 0.000 0.667
460842 3 1535 0.113 0.141 1.333 0.000 0.00 0.410 0.176 0.895
461188 2 1574 0.024 0.039 2.018 0.300 0.00 0.057 0.343 0.900
461195 2 319 0.023 0.006 1.831 0.125 0.00 0.000 0.564 0.250
461199 3 399 0.196 0.108 1.926 0.000 0.00 0.000 0.226 0.071
462116 2 1817 0.012 0.016 1.671 0.348 0.00 0.050 0.248 0.826
462424 2 2614 0.030 0.042 0.703 0.129 0.00 0.413 0.069 0.903
463034 4 1092 0.374 0.019 1.374 0.000 0.00 0.082 0.330 0.357
463067 3 1776 0.147 0.147 1.094 0.031 0.00 0.101 0.101 0.562
463936 3 486 0.150 0.174 1.646 0.000 0.00 0.000 0.000 0.125
463981 2 2102 0.038 0.050 1.431 0.483 0.00 0.171 0.214 0.793
465247 1 2880 0.000 0.000 1.227 0.000 2.47 0.344 0.000 1.000
465351 2 2861 0.011 0.070 1.098 0.118 0.00 0.503 0.157 0.882
465527 3 1219 0.067 0.154 2.089 0.074 0.00 0.295 0.738 0.444
465642 2 2963 0.146 0.029 1.495 0.343 0.00 0.364 0.121 0.914
465694 3 1561 0.039 0.065 1.173 0.280 0.00 0.058 0.346 0.680
465730 2 1404 0.106 0.262 1.544 0.000 0.00 0.577 0.128 0.400
466052 3 1772 0.217 0.451 1.281 0.061 0.00 0.813 0.051 0.485
466075 2 1697 0.178 0.040 0.515 0.000 0.00 0.318 0.265 0.731
466525 3 2369 0.109 0.170 1.294 0.345 0.00 0.532 0.114 0.931
467189 1 1620 0.000 0.001 1.332 0.000 3.06 0.444 0.000 1.000
467779 3 1901 0.091 0.088 1.134 0.423 0.00 0.284 0.379 0.769
469142 2 3210 0.093 0.044 1.297 0.361 0.00 0.224 0.252 1.000
469272 3 1259 0.091 0.065 1.790 0.034 0.00 0.000 0.143 0.414
470313 4 1896 0.313 0.073 1.219 0.000 0.00 0.570 0.000 0.636
470315 2 353 0.000 0.105 2.007 0.143 0.00 0.000 0.000 0.429
472713 2 679 0.058 0.023 1.197 0.048 0.00 0.000 0.133 0.333
472769 2 2643 0.208 0.091 1.191 0.029 0.00 0.341 0.170 0.824
475168 4 2658 0.505 0.066 1.261 0.000 0.00 1.016 0.169 0.857
476887 3 549 0.089 0.166 1.793 0.000 0.00 0.164 0.164 0.286
477064 2 401 0.043 0.312 1.528 0.000 0.00 0.449 0.449 0.364
477424 2 1370 0.148 0.046 1.054 0.167 0.00 0.328 0.131 0.778
477555 3 1030 0.128 0.183 1.111 0.000 0.00 0.000 0.087 0.435
477717 2 2933 0.022 0.018 2.058 0.559 0.00 0.000 0.031 0.971
478969 2 1539 0.015 0.019 1.815 0.474 0.00 0.117 0.000 0.895
480455 2 678 0.045 0.015 1.252 0.300 0.00 0.000 0.133 0.700
481655 3 2991 0.085 0.068 0.785 0.184 0.00 0.271 0.120 0.842
482442 3 1388 0.106 0.072 1.729 0.154 0.00 0.130 0.195 0.500
482609 2 2255 0.062 0.119 1.482 0.000 0.00 0.279 0.120 0.676
482973 4 2293 0.254 0.049 1.522 0.000 0.00 0.510 0.078 0.649
483081 2 954 0.201 0.037 1.328 0.000 0.00 0.000 0.000 0.318
484420 3 2930 0.160 0.183 1.428 0.222 0.00 0.491 0.154 0.917
485047 2 1340 0.089 0.010 1.635 0.333 0.00 0.067 0.336 0.667
485055 1 630 0.000 0.000 0.793 0.000 1.43 0.000 0.143 1.000
485337 3 909 0.154 0.084 1.434 0.000 0.00 0.000 0.000 0.333
485711 4 1630 0.509 0.015 1.494 0.000 0.00 1.049 0.110 0.467
486385 4 1551 0.516 0.013 1.402 0.000 0.00 0.870 0.174 0.432
486520 3 1318 0.033 0.059 1.726 0.043 0.00 0.205 0.205 0.609
486672 3 2796 0.047 0.077 1.369 0.394 0.00 0.322 0.354 0.939
487053 2 1335 0.012 0.049 1.291 0.000 0.00 0.067 0.270 0.650
487676 2 3032 0.067 0.061 1.403 0.053 0.00 0.178 0.267 0.842
487838 2 2176 0.042 0.115 1.560 0.167 0.00 0.165 0.165 0.767
488024 3 2074 0.197 0.266 1.302 0.029 0.00 0.130 0.174 0.559
488213 4 1402 0.352 0.025 1.469 0.000 0.00 0.257 0.064 0.424
489639 1 3420 0.000 0.002 1.291 0.000 2.79 0.158 0.079 1.000
489706 3 785 0.273 0.045 1.686 0.048 0.00 0.000 0.000 0.333
489888 3 1074 0.218 0.136 1.527 0.032 0.00 0.335 0.168 0.258
490094 3 1477 0.033 0.043 1.501 0.241 0.00 0.061 0.548 0.552
490142 3 1162 0.016 0.082 1.654 0.045 0.00 0.000 0.077 0.455
490721 2 2359 0.033 0.133 1.533 0.086 0.00 0.153 0.114 0.686
491279 2 3041 0.083 0.011 1.272 0.086 0.00 0.296 0.266 0.943
492777 2 928 0.017 0.081 1.045 0.067 0.00 0.194 0.485 0.600
492859 3 521 0.069 0.133 2.071 0.000 0.00 0.000 0.518 0.087
493105 3 1261 0.246 0.263 1.465 0.000 0.00 0.214 0.143 0.417
493125 2 515 0.054 0.002 2.143 0.400 0.00 0.000 0.000 0.500
493250 3 2339 0.210 0.182 1.219 0.000 0.00 0.269 0.077 0.719
493362 3 1747 0.158 0.198 1.582 0.107 0.00 0.361 0.258 0.643
494521 2 3378 0.036 0.082 1.450 0.316 0.00 0.506 0.133 1.000
494595 3 2374 0.259 0.195 1.289 0.030 0.00 0.644 0.038 0.818
494960 2 1825 0.016 0.098 2.116 0.143 0.00 0.000 0.049 1.000
496221 3 2552 0.054 0.263 1.378 0.265 0.00 0.282 0.141 0.824
496661 3 349 0.052 0.036 1.715 0.071 0.00 0.000 0.516 0.143
497949 2 1042 0.011 0.094 1.756 0.000 0.00 0.000 0.086 0.455
498016 1 3150 0.000 0.003 1.430 0.000 3.11 0.343 0.114 1.000
499169 2 697 0.013 0.026 1.163 0.000 0.00 0.000 0.387 0.250
499309 4 265 0.523 0.098 2.000 0.000 0.00 0.000 0.340 0.100
499604 3 1110 0.216 0.149 1.552 0.000 0.00 0.243 0.081 0.867
500040 2 986 0.009 0.058 0.825 0.100 0.00 0.091 0.365 0.400
500151 2 1025 0.118 0.040 1.321 0.000 0.00 0.000 0.176 0.714
501837 2 2137 0.106 0.026 1.534 0.370 0.00 0.126 0.505 0.889
502500 4 3282 0.565 0.050 1.458 0.026 0.00 0.603 0.192 0.974
502697 3 679 0.155 0.072 1.797 0.000 0.00 0.000 0.530 0.350
503139 3 2848 0.120 0.093 1.486 0.405 0.00 0.284 0.158 0.892
503301 3 1676 0.108 0.208 1.311 0.032 0.00 0.161 0.054 0.484
503714 3 2330 0.097 0.016 2.040 0.114 0.00 0.193 0.039 0.743
508395 3 2652 0.041 0.047 1.368 0.297 0.00 0.034 0.238 0.784
508479 1 378 0.000 0.000 0.981 0.000 1.90 0.000 0.000 0.800
509291 3 2760 0.017 0.032 1.542 0.457 0.00 0.130 0.391 0.857
509416 3 1921 0.126 0.054 1.258 0.172 0.00 0.328 0.047 0.690
510281 3 817 0.275 0.175 1.238 0.000 0.00 0.110 0.220 0.250
510362 2 1423 0.034 0.018 1.608 0.421 0.00 0.000 0.063 0.789
510663 4 1797 0.506 0.123 1.308 0.000 0.00 1.102 0.000 0.679
511499 3 1334 0.167 0.164 1.166 0.000 0.00 0.472 0.067 0.387
512462 2 3118 0.048 0.029 1.544 0.162 0.00 0.058 0.173 0.973
513418 3 2744 0.396 0.067 1.314 0.000 0.00 0.164 0.197 0.857
513433 3 708 0.236 0.112 1.757 0.000 0.00 0.254 0.254 0.389
513466 3 675 0.089 0.047 1.775 0.062 0.00 0.267 0.000 0.375
514254 3 2117 0.265 0.073 1.248 0.094 0.00 0.383 0.383 0.719
514356 3 374 0.051 0.132 2.053 0.000 0.00 0.000 0.000 0.083
515046 1 270 0.000 0.007 1.367 0.000 3.33 1.000 0.000 1.000
515597 2 1042 0.000 0.017 1.328 0.000 0.00 0.345 0.432 0.357
515621 2 550 0.054 0.021 1.487 0.111 0.00 0.000 0.327 0.667
516895 3 1653 0.026 0.069 1.246 0.214 0.00 0.109 0.109 0.571
516939 2 1100 0.047 0.033 1.494 0.429 0.00 0.000 0.082 0.786
518030 1 270 0.000 0.000 1.607 0.000 3.33 0.000 0.000 1.000
523705 2 1834 0.016 0.079 1.506 0.065 0.00 0.000 0.147 0.548
530335 4 819 0.115 0.122 1.409 0.000 0.00 0.000 0.000 0.643
532529 3 1736 0.256 0.121 1.443 0.037 0.00 0.104 0.000 0.741
532605 3 1247 0.144 0.064 1.365 0.074 0.00 0.217 0.289 0.407
533463 3 2271 0.315 0.163 1.377 0.062 0.00 0.634 0.198 0.750
535301 3 1646 0.043 0.039 1.115 0.129 0.00 0.000 0.273 0.484
535818 3 649 0.049 0.086 1.567 0.000 0.00 0.416 0.277 0.500
536109 2 656 0.025 0.044 1.836 0.154 0.00 0.000 0.274 0.538
536661 3 401 0.173 0.027 1.629 0.000 0.00 0.000 0.224 0.625
538207 4 805 0.479 0.069 1.619 0.000 0.00 1.453 0.000 0.333
544877 2 2251 0.060 0.028 1.203 0.029 0.00 0.160 0.160 0.676
547027 3 1403 0.210 0.055 1.380 0.000 0.00 0.192 0.385 0.750
547701 3 1471 0.092 0.079 1.517 0.000 0.00 0.367 0.306 0.625
547719 3 1493 0.082 0.127 1.279 0.217 0.00 0.301 0.000 0.652
549329 2 1405 0.038 0.094 1.806 0.050 0.00 0.000 0.064 0.700
549912 3 1553 0.123 0.068 1.290 0.000 0.00 0.348 0.000 0.571
550090 2 193 0.000 0.005 2.108 0.200 0.00 0.000 0.933 0.400
550615 3 351 0.164 0.305 1.664 0.000 0.00 0.000 0.513 0.133
550839 3 972 0.178 0.112 1.319 0.000 0.00 0.556 0.000 0.333
550864 2 1730 0.070 0.031 1.396 0.094 0.00 0.052 0.052 0.531
551210 2 1139 0.024 0.048 1.462 0.045 0.00 0.000 0.553 0.455
551226 3 3017 0.059 0.088 1.441 0.417 0.00 0.209 0.209 0.944
551483 2 2315 0.042 0.067 1.598 0.065 0.00 0.078 0.389 0.806
554197 3 758 0.102 0.110 1.479 0.000 0.00 0.119 0.119 0.389
560262 4 1826 0.486 0.078 1.422 0.000 0.00 0.838 0.296 0.564
560552 3 1030 0.106 0.128 1.273 0.000 0.00 0.000 0.087 0.231
564406 4 751 0.255 0.026 1.551 0.000 0.00 0.599 0.000 0.350
564940 3 971 0.041 0.030 1.764 0.136 0.00 0.185 0.371 0.409
570526 3 955 0.116 0.041 1.287 0.043 0.00 0.000 0.188 0.391
575458 2 514 0.047 0.011 1.812 0.111 0.00 0.000 0.000 0.444
575476 2 2130 0.031 0.020 1.394 0.360 0.00 0.127 0.211 0.920
577016 2 657 0.085 0.018 2.145 0.000 0.00 0.685 0.137 0.412
577669 3 2891 0.045 0.045 1.289 0.121 0.00 0.000 0.280 1.000
577725 3 1290 0.172 0.046 1.323 0.000 0.00 0.209 0.279 0.406
578153 2 1427 0.041 0.076 1.318 0.238 0.00 0.189 0.126 0.667
586309 4 1898 0.387 0.021 1.588 0.000 0.00 0.427 0.142 0.500
592031 3 2389 0.144 0.191 1.284 0.029 0.00 0.339 0.113 0.735
596777 2 1440 0.149 0.115 1.226 0.038 0.00 0.688 0.312 0.538
606745 2 920 0.033 0.018 1.169 0.294 0.00 0.293 0.196 0.588
607464 2 3258 0.035 0.080 1.454 0.081 0.00 0.249 0.221 1.000
609873 3 524 0.136 0.038 1.877 0.077 0.00 0.000 0.000 0.385
611922 3 547 0.220 0.331 1.468 0.000 0.00 0.658 0.000 0.263
613804 2 2706 0.019 0.083 1.452 0.125 0.00 0.100 0.200 0.938
620487 2 367 0.037 0.047 1.084 0.429 0.00 0.000 0.000 0.571
624773 3 839 0.312 0.230 1.104 0.000 0.00 0.429 0.429 0.318
641221 2 257 0.123 0.130 1.590 0.000 0.00 0.000 0.000 0.222
643135 3 228 0.063 0.241 1.571 0.000 0.00 0.000 0.395 0.111
647671 4 1787 0.101 0.186 1.599 0.037 0.00 0.453 0.000 0.667
647850 4 351 0.544 0.138 1.549 0.000 0.00 0.769 0.513 0.095
651426 2 1331 0.100 0.022 1.612 0.450 0.00 0.609 0.203 0.700
"""


# ---------------------------------------------------------------------------
# Expected points
# ---------------------------------------------------------------------------
# The rating used to be a percentile index that deliberately refused to be
# compared against a -4 transfer hit. That made it useless for the two questions
# people actually ask: is this move worth a hit, and which eleven should start.
# So the model now predicts points directly, by pricing each way FPL awards them.
#
# Two things came out of testing this against 2024-25 and 2025-26 and both
# changed the design:
#
#   1. Last season predicts this season far better than a handful of new
#      matches. Previous-season expected goal involvements per 90 correlate 0.52
#      with the rest of the coming season; two rounds of the new season manage
#      0.13. So every rate starts from last season and is updated as minutes
#      accumulate, crossing over around eleven matches.
#   2. Defensive contributions are the most repeatable statistic in the game --
#      a player's hit rate correlates up to 0.98 with itself half-season to
#      half-season -- and they predict future points at 0.04 for defenders and
#      -0.05 for midfielders. Repeatable is not the same as valuable: the two
#      points reliably identify players who do not otherwise score. An earlier
#      version of this model weighted the hit rate at 30-35% of a player's
#      quality, which was actively harmful. Here it is what it really is, a
#      2-point line item.
# A goalkeeper scoring is worth 10, not 6 -- a detail this model had wrong.
GOAL_PTS = {"GK": 10, "DEF": 6, "MID": 5, "FWD": 4}
CS_PTS = {"GK": 4, "DEF": 4, "MID": 1, "FWD": 0}
ASSIST_PTS = 3
DC_PTS = 2
PRIOR_MINS = 1000.0        # minutes of new football that halve the prior's weight


def parse_prior():
    """The embedded last-season table -> {code: rates}."""
    out = {}
    for line in PRIOR_TABLE.strip().splitlines():
        f = line.split()
        if len(f) != 11:
            continue
        out[int(f[0])] = {
            "pos": POS.get(int(f[1]), "MID"), "mins": float(f[2]),
            "xg90": float(f[3]), "xa90": float(f[4]), "xgc90": float(f[5]),
            "dcHit": float(f[6]), "sv90": float(f[7]), "bonus90": float(f[8]),
            "yc90": float(f[9]), "st60": float(f[10]),
        }
    return out


PRIOR = parse_prior()


def position_defaults(els):
    """Median rates per position, for players with no Premier League history."""
    d = {}
    for pos in ("GK", "DEF", "MID", "FWD"):
        grp = [PRIOR[c] for c in PRIOR if PRIOR[c]["pos"] == pos]
        if not grp:
            continue
        def med(k):
            xs = sorted(g[k] for g in grp)
            return xs[len(xs) // 2] if xs else 0.0
        d[pos] = {k: med(k) for k in
                  ("xg90", "xa90", "xgc90", "dcHit", "sv90", "bonus90", "yc90", "st60")}
    return d


PRIOR_THIN = 400.0         # minutes before last season's own rate is trusted


def blend_rate(prior_val, prior_mins, obs_val, obs_mins, pos_median=0.0):
    """Combine last season's rate with this season's, weighted by minutes.

    Two stages, because there are two different kinds of ignorance.

    First the prior is shrunk toward the positional median by how much football
    stands behind it -- a player with 200 minutes last season barely has a rate
    of his own. Then this season is folded in at weight minutes/(K+minutes).

    K was fitted rather than chosen: blending previous-season xGI/90 with
    current-season xGI/90 and scanning K, the best value sat between 900 and
    1200 minutes at every checkpoint from round 2 to round 19, on a very flat
    optimum. 1000 is the middle of that range.

    Collapsing this into one stage was a real bug. Scaling the prior's weight
    down when the prior was thin handed the difference to whatever the new
    season had, which in August is ninety minutes of noise -- a forward with one
    bonus point off the bench came out rated at three bonus points a game. A
    thin prior is a reason to trust the positional median, not a tiny sample.
    """
    if prior_val is None and obs_val is None:
        return pos_median
    if prior_val is None:
        prior_val, prior_mins = pos_median, 0.0
    if obs_val is None or not obs_mins:
        obs_val, obs_mins = prior_val, 0.0
    conf = (prior_mins or 0.0) / ((prior_mins or 0.0) + PRIOR_THIN)
    prior_eff = conf * prior_val + (1.0 - conf) * pos_median
    w_prior = PRIOR_MINS / (PRIOR_MINS + obs_mins)
    return w_prior * prior_eff + (1.0 - w_prior) * obs_val


def expected_points(e, exp_, cs_prob, price_prior=None):
    """Expected FPL points for one player in one fixture.

    exp_ is that fixture's expectation for the player's club: goals for, goals
    against and the clean-sheet probability. Everything is per-90 and then scaled
    by the minutes he is actually expected to play.
    """
    pos = e["_pos"]
    mins = e.get("_expMins") or 0.0
    if mins <= 0:
        return 0.0
    m90 = mins / 90.0
    p_play = min(1.0, mins / 20.0) * e["_avail"]      # any appearance at all
    p_60 = min(1.0, max(0.0, (mins - 20.0) / 60.0)) * e["_avail"]

    # attacking output scales with how good a match this is for his club
    att_scale = (exp_["xgf"] / max(0.4, LEAGUE_AVG_GOALS)) if exp_ else 1.0
    att_scale = max(0.5, min(1.8, att_scale))

    xg = e["_r_xg90"] * m90 * att_scale
    xa = e["_r_xa90"] * m90 * att_scale
    pts = p_play * 1.0 + p_60 * 1.0
    pts += xg * GOAL_PTS.get(pos, 5) + xa * ASSIST_PTS
    pts += cs_prob * CS_PTS.get(pos, 0) * p_60
    if pos in ("GK", "DEF"):
        pts -= (exp_["xga"] if exp_ else LEAGUE_AVG_GOALS) * m90 / 2.0
    if pos == "GK":
        # saves track the opponent's shot volume, so scale them the same way
        sv = e["_r_sv90"] * m90 * max(0.5, min(1.8, (exp_["xga"] if exp_ else 1.4) / 1.4))
        pts += sv / 3.0
    pts += e["_r_dcHit"] * DC_PTS * p_60
    pts += e["_r_bonus90"] * m90
    pts -= e["_r_yc90"] * m90
    return round(max(0.0, pts), 3)


POS_DEFAULT = position_defaults(None)


def window_stats(log, pos):
    """Collapse a player's match log into the numbers the model actually uses."""
    thr = DC_THRESH.get(pos, 12)
    played = [g for g in log if g["mins"] > 0]

    def ppm(rows):
        return (sum(g["pts"] for g in rows) / len(rows)) if rows else None

    last3, last5 = log[-3:], log[-5:]
    # a hit rate only means something once a player has actually been on the pitch
    hits = [g for g in played if g["dc"] >= thr]
    return {
        "form3": ppm(last3), "form5": ppm(last5), "formAll": ppm(log),
        "dcHit": (len(hits) / len(played)) if played else None,
        "dcPlayed": len(played),
        "mins3": (sum(g["mins"] for g in last3) / len(last3)) if last3 else None,
        "mins5": (sum(g["mins"] for g in last5) / len(last5)) if last5 else None,
        "starts": sum(1 for g in log if g["started"]),
        "apps": len(played),
        "matches": len(log),
    }


def start_odds(log, prior, status, chance, pos):
    """How likely is he to be in the eleven, and why.

    Three inputs, in descending order of authority.

    FPL's own availability flag comes first and overrides everything: a
    suspended or injured player is not starting whatever his record says, and
    the game publishes a percentage for doubts.

    Then recent starts, weighted toward the newest matches -- a player dropped
    last week matters more than one dropped in August. Then last season's rate
    for the many players who have barely featured yet.

    What this CANNOT see is a press conference. A manager saying on Friday that
    someone is rested for Europe is the single biggest thing that moves a team
    sheet, and none of it reaches the API until the player is flagged. Treat
    this as a base rate, not a prediction.
    """
    if status == "u":
        return 0.0, "unavailable"
    if status == "s":
        return 0.0, "suspended"
    if status == "i":
        return (num(chance) / 100.0 if chance is not None else 0.05), "injured"

    played = [g for g in (log or []) if g.get("mins", 0) > 0 or g.get("started") is not None]
    recent = (log or [])[-5:]
    why = None
    if recent:
        # newest match counts most; weights 5,4,3,2,1 over the last five
        wts = list(range(1, len(recent) + 1))
        p = sum(w * (1.0 if g.get("started") else 0.0) for g, w in zip(recent, wts)) / sum(wts)
        n_start = sum(1 for g in recent if g.get("started"))
        conf = min(1.0, len(recent) / 3.0)
        if prior is not None:
            p = conf * p + (1 - conf) * prior
        if n_start == len(recent):
            why = "started all %d" % len(recent)
        elif n_start == 0:
            cameos = sum(1 for g in recent if g.get("mins", 0) > 0)
            why = ("no starts in %d, %d off the bench" % (len(recent), cameos)
                   if cameos else "no minutes in %d" % len(recent))
        else:
            why = "started %d of the last %d" % (n_start, len(recent))
    elif prior is not None:
        p = prior
        why = "no matches yet; started %d%% of last season" % round(100 * prior)
    else:
        p = 0.5
        why = "no record to go on"

    if status == "d":
        # a doubt caps it, and the game's own percentage is the better number
        cap = (num(chance) / 100.0) if chance is not None else 0.5
        if cap < p:
            p, why = cap, ("flagged as a doubt" +
                           (", %d%% chance per FPL" % num(chance) if chance is not None else ""))
    return max(0.0, min(1.0, p)), why


def model_weights(matches_played):
    """How much to trust price versus what has actually happened.

    Price is the market's season-long estimate and is the steadiest thing
    available in August, but it stops being the best guide once real matches
    accumulate. The weight on it decays from 55% to 20% over the first seven
    rounds; whatever it gives up goes to observed form.
    """
    w_prior = max(0.20, 0.55 - 0.05 * max(0, matches_played))
    w_fix = 0.20
    return round(w_prior, 3), round(1 - w_prior - w_fix, 3), w_fix


def score_players(boot, fixmap, hist, matches_played):
    els = boot["elements"]
    W_PRIOR, W_OBS, W_FIX = model_weights(matches_played)

    for e in els:
        e["_pos"] = POS.get(e["element_type"], "MID")
        mins = num(e.get("minutes"))
        m90 = mins / 90.0 if mins else 0.0
        e["_m90"] = m90
        e["_xgi"] = num(e.get("expected_goal_involvements"))
        e["_xg"] = num(e.get("expected_goals"))
        e["_xa"] = num(e.get("expected_assists"))
        e["_xgc"] = num(e.get("expected_goals_conceded"))
        e["_ict"] = num(e.get("ict_index"))
        e["_xgi90"] = (e["_xgi"] / m90) if m90 else 0.0
        e["_ict90"] = (e["_ict"] / m90) if m90 else 0.0
        e["_xgc90"] = (e["_xgc"] / m90) if m90 else None
        e["_owned"] = num(e.get("selected_by_percent"))
        e["_dc90"] = num(e.get("defensive_contribution_per_90"))

        fm = fixmap.get(e["team"], {})
        e["_avgFdr"] = fm.get("avgFdr")
        e["_csNext"] = fm.get("csNext")
        e["_xgfNext"] = fm.get("xgfNext")

        # ---- multi-window history ----
        log = hist.get(e["id"], [])
        # compact match log, newest last, only for players who have featured
        opp_map = hist.get("__opp__") or {}
        e["_log"] = [[g["gw"],
                      (opp_map.get((g["gw"], e["team"])) or ("?", "-"))[0],
                      (opp_map.get((g["gw"], e["team"])) or ("?", "-"))[1],
                      int(g["mins"]), 1 if g.get("started") else 0,
                      int(g["pts"]), int(g.get("goals") or 0), int(g.get("assists") or 0),
                      int(g.get("cs") or 0), int(g.get("bonus") or 0),
                      int(g.get("bps") or 0), int(g.get("dc") or 0)]
                     for g in log if g["mins"] > 0]
        w = window_stats(log, e["_pos"]) if log else {}
        e["_w"] = w
        e["_form3"] = w.get("form3")
        e["_form5"] = w.get("form5")
        e["_dcHit"] = w.get("dcHit")
        e["_dcPlayed"] = w.get("dcPlayed", 0)

        # recent scoring rate, leaning on the newer window but not ignoring the season
        parts, wts = [], []
        if w.get("form3") is not None:
            parts.append(w["form3"]); wts.append(0.45)
        if w.get("form5") is not None:
            parts.append(w["form5"]); wts.append(0.30)
        season_ppg = num(e.get("points_per_game"))
        parts.append(season_ppg); wts.append(0.25 if parts else 1.0)
        e["_formBlend"] = sum(p * q for p, q in zip(parts, wts)) / sum(wts)

        # ---- minutes, modelled rather than guessed ----
        exp_mins = None
        if w.get("mins3") is not None and w.get("mins5") is not None:
            exp_mins = 0.65 * w["mins3"] + 0.35 * w["mins5"]
        elif w.get("mins3") is not None:
            exp_mins = w["mins3"]
        elif mins:
            exp_mins = mins / max(1, w.get("matches") or 1)
        e["_expMins"] = exp_mins
        if exp_mins is None:
            e["_minfac"] = 0.58                       # never seen him play
        else:
            e["_minfac"] = round(0.35 + 0.65 * min(1.0, exp_mins / 90.0), 3)

        st = e.get("status", "a")
        chance = e.get("chance_of_playing_next_round")

        # ---- will he actually be in the eleven? ----
        pri_start = pri_row["st60"] if (pri_row := PRIOR.get(e.get("code"))) else None
        e["_pStart"], e["_startWhy"] = start_odds(log, pri_start, st, chance, e["_pos"])
        # minutes follow from that: a starter's typical shift, or a substitute's
        starter_mins = [g["mins"] for g in log if g.get("started")]
        sub_mins = [g["mins"] for g in log if not g.get("started") and g.get("mins", 0) > 0]
        typ_start = (sum(starter_mins) / len(starter_mins)) if starter_mins else 82.0
        typ_sub = (sum(sub_mins) / len(sub_mins)) if sub_mins else 16.0
        modelled = e["_pStart"] * typ_start + (1 - e["_pStart"]) * (
            typ_sub * (0.6 if e["_pStart"] > 0.8 else 1.0))
        if exp_mins is None:
            e["_expMins"] = modelled
        else:
            # blend the raw recent average with the start-based estimate; they
            # agree for nailed-on players and disagree exactly where it matters
            e["_expMins"] = 0.5 * exp_mins + 0.5 * modelled
        e["_minfac"] = round(0.35 + 0.65 * min(1.0, (e["_expMins"] or 0) / 90.0), 3)

        if st == "a":
            av = 1.0
        elif chance is not None:
            av = num(chance) / 100.0
        else:
            av = {"d": 0.5, "i": 0.1, "s": 0.1, "u": 0.05}.get(st, 0.5)
        e["_avail"] = av

        sp = 0.0
        if e.get("penalties_order") == 1:
            sp += 6
        elif e.get("penalties_order") == 2:
            sp += 2
        if e.get("direct_freekicks_order") == 1:
            sp += 2
        if e.get("corners_and_indirect_freekicks_order") == 1:
            sp += 2
        e["_sp"] = sp

        # ---- rates: last season updated by this one ----
        pri = PRIOR.get(e.get("code"))
        dfl = POS_DEFAULT.get(e["_pos"], {})
        pm = pri["mins"] if pri else 0.0
        e["_hasPrior"] = bool(pri)

        def blend(key, obs):
            med = dfl.get(key, 0.0)
            return blend_rate(pri[key] if pri else None, pm, obs, mins, med)

        e["_r_xg90"] = blend("xg90", (e["_xg"] / m90) if m90 else None)
        e["_r_xa90"] = blend("xa90", (e["_xa"] / m90) if m90 else None)
        e["_r_xgc90"] = blend("xgc90", e["_xgc90"])
        e["_r_dcHit"] = blend("dcHit", e["_dcHit"])
        e["_r_sv90"] = blend("sv90", (num(e.get("saves")) / m90) if m90 else None)
        e["_r_bonus90"] = blend("bonus90", (num(e.get("bonus")) / m90) if m90 else None)
        e["_r_yc90"] = blend("yc90", (num(e.get("yellow_cards")) / m90) if m90 else None)
        for k in ("_r_xg90", "_r_xa90", "_r_dcHit", "_r_sv90", "_r_bonus90", "_r_yc90"):
            if e[k] is None:
                e[k] = 0.0
        # penalty duty is a role, not a rate: it does not carry over from a
        # season when someone else was taking them
        if e.get("penalties_order") == 1 and e["_r_xg90"] < 0.35:
            e["_r_xg90"] += 0.13          # roughly a penalty every seven matches
        elif e.get("penalties_order") == 2 and e["_r_xg90"] < 0.30:
            e["_r_xg90"] += 0.04

        # Last season's minutes used to be blended in again here. That is now
        # done inside start_odds, which folds the prior into the probability of
        # starting rather than into the minutes directly -- doing both meant a
        # player who had not featured all season still came out at 85 expected
        # minutes because last season said he was nailed on.

    # ---- percentiles within position ----
    for pos in ("GK", "DEF", "MID", "FWD"):
        grp = [e for e in els if e["_pos"] == pos]
        if not grp:
            continue
        prior = pct_ranks([num(e.get("now_cost")) for e in grp])
        xgi = pct_ranks([e["_xgi90"] for e in grp])
        ict = pct_ranks([e["_ict90"] for e in grp])
        form = pct_ranks([e["_formBlend"] for e in grp])
        dc = pct_ranks([(e["_dcHit"] if e["_dcHit"] is not None else 0.0) for e in grp])
        # fixture term is position-aware: clean sheets matter at the back,
        # goals at the front
        if pos in ("GK", "DEF"):
            fixraw = [(e["_csNext"] if e["_csNext"] is not None else 0.25) for e in grp]
        else:
            fixraw = [(e["_xgfNext"] if e["_xgfNext"] is not None else 1.4) for e in grp]
        fixp = pct_ranks(fixraw)

        for i, e in enumerate(grp):
            if pos == "GK":
                obs = 0.55 * form[i] + 0.45 * ict[i]
            elif pos == "DEF":
                obs = 0.35 * form[i] + 0.35 * dc[i] + 0.30 * xgi[i]
            elif pos == "MID":
                obs = 0.40 * xgi[i] + 0.30 * form[i] + 0.30 * dc[i]
            else:
                obs = 0.55 * xgi[i] + 0.45 * form[i]
            e["_prior"] = prior[i]
            e["_obs"] = obs
            e["_fix"] = fixp[i]
            e["_index"] = round(
                100 * (W_PRIOR * prior[i] + W_OBS * obs + W_FIX * fixp[i])
                * e["_avail"] * e["_minfac"] + e["_sp"], 1)

    # ---- expected points, per fixture and over the horizon ----
    for e in els:
        runs = [r for r in fixmap.get(e["team"], {}).get("runs", []) if r.get("opp")]
        per = []
        for r in runs:
            exp_ = {"xgf": r.get("xgf") or LEAGUE_AVG_GOALS,
                    "xga": r.get("xga") or LEAGUE_AVG_GOALS}
            per.append(expected_points(e, exp_, r.get("cs") or 0.25))
        e["_xpRuns"] = per
        e["_xp1"] = round(per[0], 2) if per else 0.0
        e["_xp5"] = round(sum(per[:HORIZON]), 1)
        e["_xpAll"] = round(sum(per), 1)
        # the headline number is what he is worth over the planning horizon
        e["_score"] = e["_xp5"]
        e["_ppm"] = round(e["_xp5"] / max(0.1, num(e.get("now_cost")) / 10.0), 2)
    return els


EASE = {1: 1.30, 2: 1.15, 3: 1.00, 4: 0.85, 5: 0.70}


def run_window(team_id, fixmap, k=HORIZON):
    """The fixtures in a team's next k gameweeks. Blanks contribute nothing,
    doubles contribute twice -- both fall out of this naturally."""
    runs = fixmap.get(team_id, {}).get("runs", [])
    gws = sorted(set(r["gw"] for r in runs))[:k]
    sel = [r for r in runs if r["gw"] in gws and r.get("opp")]
    mult = sum(EASE.get(r.get("fdr"), 1.0) for r in sel)
    return sel, mult


def base_score(e, wp, wo):
    """Quality with the fixture term removed -- what he is, not who he faces."""
    wsum = wp + wo
    return (100 * (wp * e.get("_prior", 0) + wo * e.get("_obs", 0)) / wsum) \
        * e.get("_avail", 1) * e.get("_minfac", 1) + e.get("_sp", 0)


def league_table(fixtures, teams):
    """The real Premier League table, computed from finished results.

    The FPL API ships `played`, `points` and `win/draw/loss` as zeros and its
    `position` field is stale seeding, so none of it can be used.
    """
    rec = {}
    for t in teams:
        rec[t["id"]] = {"id": t["id"], "name": t["name"], "short": t["short_name"],
                        "code": int(num(t.get("code"))), "p": 0, "w": 0, "d": 0, "l": 0,
                        "gf": 0, "ga": 0, "pts": 0, "form": []}
    done = [f for f in fixtures if is_played(f)]
    done.sort(key=lambda f: (f.get("event") or 0, f.get("kickoff_time") or ""))
    for f in done:
        h, a = rec.get(f["team_h"]), rec.get(f["team_a"])
        if not h or not a:
            continue
        hs, as_ = int(f["team_h_score"]), int(f["team_a_score"])
        h["p"] += 1; a["p"] += 1
        h["gf"] += hs; h["ga"] += as_; a["gf"] += as_; a["ga"] += hs
        if hs > as_:
            h["w"] += 1; a["l"] += 1; h["pts"] += 3
            h["form"].append("W"); a["form"].append("L")
        elif hs < as_:
            a["w"] += 1; h["l"] += 1; a["pts"] += 3
            a["form"].append("W"); h["form"].append("L")
        else:
            h["d"] += 1; a["d"] += 1; h["pts"] += 1; a["pts"] += 1
            h["form"].append("D"); a["form"].append("D")
    rows = list(rec.values())
    for r in rows:
        r["gd"] = r["gf"] - r["ga"]
        r["form"] = r["form"][-5:]
    rows.sort(key=lambda r: (-r["pts"], -r["gd"], -r["gf"], r["name"]))
    for i, r in enumerate(rows, 1):
        r["pos"] = i
    return rows


def slim(e, teams):
    t = teams.get(e["team"], {})
    return {
        "id": e["id"], "name": e.get("web_name"),
        "full": ("%s %s" % (e.get("first_name", ""), e.get("second_name", ""))).strip(),
        "club": t.get("short_name", "?"), "clubFull": t.get("name", "?"),
        "teamId": e["team"], "pos": e["_pos"],
        "price": round(num(e.get("now_cost")) / 10, 1),
        "pts": int(num(e.get("total_points"))), "score": e.get("_score", 0),
        "mins": int(num(e.get("minutes"))), "starts": int(num(e.get("starts"))),
        "goals": int(num(e.get("goals_scored"))), "assists": int(num(e.get("assists"))),
        "cs": int(num(e.get("clean_sheets"))), "bonus": int(num(e.get("bonus"))),
        "bps": int(num(e.get("bps"))),
        "xg": round(e["_xg"], 2), "xa": round(e["_xa"], 2), "xgi": round(e["_xgi"], 2),
        "xgi90": round(e["_xgi90"], 2), "xgc": round(e["_xgc"], 2),
        "ict": round(e["_ict"], 1), "dc": int(num(e.get("defensive_contribution"))),
        "dc90": round(e["_dc90"], 1), "owned": e["_owned"],
        "status": e.get("status", "a"), "news": (e.get("news") or "").strip(),
        "pen": e.get("penalties_order"), "ck": e.get("corners_and_indirect_freekicks_order"),
        "fk": e.get("direct_freekicks_order"), "avgFdr": e["_avgFdr"],
        "form": num(e.get("form")), "ppg": num(e.get("points_per_game")),
        "costChange": int(num(e.get("cost_change_start"))),
        "tIn": int(num(e.get("transfers_in_event"))),
        "tOut": int(num(e.get("transfers_out_event"))),
        "epNext": num(e.get("ep_next")),
        "code": int(num(e.get("code"))),           # -> player mugshot URL
        "teamCode": int(num(t.get("code"))),       # -> club badge URL
        "pStart": round(e.get("_pStart", 0.5), 2),
        "startWhy": e.get("_startWhy"),
        # last matches as fixed-order arrays, which keeps the payload small:
        # [gw, opponent, H/A, minutes, started, points, goals, assists,
        #  clean sheet, bonus, bps, defensive actions]
        "log": e.get("_log") or [],
        "form3": (round(e["_form3"], 2) if e.get("_form3") is not None else None),
        "form5": (round(e["_form5"], 2) if e.get("_form5") is not None else None),
        "formBlend": round(e.get("_formBlend", 0), 2),
        "dcHit": (round(e["_dcHit"], 3) if e.get("_dcHit") is not None else None),
        "dcPlayed": e.get("_dcPlayed", 0),
        "expMins": (round(e["_expMins"]) if e.get("_expMins") is not None else None),
        "csNext": e.get("_csNext"), "xgfNext": e.get("_xgfNext"),
        "expl": {"prior": round(e.get("_prior", 0), 3),
                 "obs": round(e.get("_obs", 0), 3),
                 "fix": round(e.get("_fix", 0), 3),
                 "avail": round(e.get("_avail", 1), 2),
                 "minfac": round(e.get("_minfac", 1), 2),
                 "sp": e.get("_sp", 0.0),
                 "xgiR": round(e.get("_xgi90", 0), 2),
                 "ictR": round(e.get("_ict90", 0), 2),
                 "xgcR": (round(e["_xgc90"], 2) if e.get("_xgc90") is not None else None),
                 "form": round(e.get("_formBlend", 0), 2),
                 "dcHit": (round(e["_dcHit"], 3) if e.get("_dcHit") is not None else None),
                 "cs": e.get("_csNext"), "xgf": e.get("_xgfNext"),
                 "expMins": (round(e["_expMins"]) if e.get("_expMins") is not None else None)},
    }


def reasons(p):
    """Why a player rates well: plain wording, but with the number that backs it up.
    Readable without a glossary, still specific enough to argue with."""
    out = []
    if p["pen"] == 1:
        out.append("first on penalties")
    if p["xgi90"] >= 0.45:
        out.append("%.2f goals+assists expected per 90" % p["xgi90"])
    thr = DC_THRESH.get(p["pos"], 12)
    if p["pos"] != "GK" and p.get("dcHit") is not None and p["dcHit"] >= 0.5 \
            and p.get("dcPlayed", 0) >= 2:
        out.append("clears the defensive threshold in %d%% of matches"
                   % round(p["dcHit"] * 100))
    elif p["pos"] != "GK" and p["dc90"] >= thr:
        out.append("%d defensive actions per 90, needs %d" % (int(p["dc90"]), thr))
    if p["pos"] in ("GK", "DEF") and p.get("csNext") is not None and p["csNext"] >= 0.28:
        out.append("%d%% clean-sheet chance across the run" % round(p["csNext"] * 100))
    if p.get("form5") is not None and p["form5"] >= 5:
        out.append("%.1f points a game over the last five" % p["form5"])
    # 3.00 is a run of coin tosses, so only call it kind once it is clearly below
    if p["avgFdr"] is not None and p["avgFdr"] <= 2.60:
        out.append("kind run of fixtures, difficulty %.2f" % p["avgFdr"])
    if p["owned"] <= 5 and p["score"] >= 70:
        out.append("owned by just %.1f%%" % p["owned"])
    if p["mins"] >= 90 and p["starts"] >= 1:
        out.append("%d minutes, %d start%s" % (p["mins"], p["starts"],
                                               "" if p["starts"] == 1 else "s"))
    if p["ck"] == 1 or p["fk"] == 1:
        out.append("on corners or free-kicks")
    return out[:3]


# ----------------------------------------------------------------------------
# assembling the payload
# ----------------------------------------------------------------------------
# ---------------------------------------------------------------------------
# Picking an eleven out of a fifteen
# ---------------------------------------------------------------------------
# Squad selection and team selection are different problems. The transfer engine
# asks who to own over the next five weeks; this asks who to field on Saturday.
# The horizons differ, so the inputs should too -- this one runs entirely on the
# coming fixture, which is exactly the window bookmakers price. Where the market
# has priced a match, that is the number behind these calls.
FORMATIONS = [(d, mi, f)
              for d in (3, 4, 5) for mi in (2, 3, 4, 5) for f in (1, 2, 3)
              if d + mi + f == 10]
CLOSE_CALL = 0.35          # expected points apart, below which it is a coin toss


def pick_eleven(squad):
    """squad: [{id, pos, xp1, name, ...}] of fifteen. Returns the best legal side.

    Small enough to solve exactly: fifteen players, at most twelve shapes, so
    every formation is evaluated in full rather than approximated.
    """
    keepers = sorted([p for p in squad if p["pos"] == "GK"], key=lambda p: -p["xp1"])
    outfield = {po: sorted([p for p in squad if p["pos"] == po], key=lambda p: -p["xp1"])
                for po in ("DEF", "MID", "FWD")}
    if not keepers:
        return None
    best = None
    for d, mi, f in FORMATIONS:
        if len(outfield["DEF"]) < d or len(outfield["MID"]) < mi or len(outfield["FWD"]) < f:
            continue
        xi = ([keepers[0]] + outfield["DEF"][:d]
              + outfield["MID"][:mi] + outfield["FWD"][:f])
        tot = sum(p["xp1"] for p in xi)
        if best is None or tot > best["total"]:
            best = {"formation": "%d-%d-%d" % (d, mi, f), "xi": xi, "total": tot}
    if not best:
        return None

    xi_ids = set(p["id"] for p in best["xi"])
    bench = [p for p in squad if p["id"] not in xi_ids]
    bench_gk = [p for p in bench if p["pos"] == "GK"]
    bench_out = sorted([p for p in bench if p["pos"] != "GK"], key=lambda p: -p["xp1"])

    outfield_xi = sorted([p for p in best["xi"] if p["pos"] != "GK"],
                         key=lambda p: -p["xp1"])
    cap = outfield_xi[0] if outfield_xi else None
    vice = outfield_xi[1] if len(outfield_xi) > 1 else None

    # a decision is only worth presenting as a decision if it is actually close
    close = []
    for i, benched in enumerate(bench_out):
        for started in best["xi"]:
            if started["pos"] != benched["pos"] or started["pos"] == "GK":
                continue
            gap = started["xp1"] - benched["xp1"]
            if 0 <= gap < CLOSE_CALL:
                close.append({"in": started["id"], "out": benched["id"],
                              "gap": round(gap, 2)})
    if cap and vice and cap["xp1"] - vice["xp1"] < CLOSE_CALL:
        close.append({"in": cap["id"], "out": vice["id"],
                      "gap": round(cap["xp1"] - vice["xp1"], 2), "captaincy": True})

    bench_pts = sum(p["xp1"] for p in bench_out) + (bench_gk[0]["xp1"] if bench_gk else 0)
    return {
        "formation": best["formation"],
        "xi": [p["id"] for p in best["xi"]],
        "benchGk": bench_gk[0]["id"] if bench_gk else None,
        "bench": [p["id"] for p in bench_out],
        "captain": cap["id"] if cap else None,
        "vice": vice["id"] if vice else None,
        "xiPoints": round(best["total"], 1),
        "withCaptain": round(best["total"] + (cap["xp1"] if cap else 0), 1),
        "benchPoints": round(bench_pts, 1),
        "closeCalls": sorted(close, key=lambda c: c["gap"])[:5],
        "chips": {
            # a bench worth more than a typical starting eleven's weakest third
            "benchBoost": round(bench_pts, 1),
            "benchBoostWorth": bench_pts >= 12.0,
            "tripleCaptain": round(cap["xp1"], 2) if cap else 0,
            "tripleCaptainWorth": bool(cap and cap["xp1"] >= 7.5),
        },
    }


# ---------------------------------------------------------------------------
# Transfers, more than one at a time
# ---------------------------------------------------------------------------
# A single swap is trapped inside its own price bracket: a 5.5m player can only
# become another 5.5m player. Selling two mid-price players to fund one premium
# and one budget enabler is the move that bracket hides, so the search has to
# consider the whole bundle at once.
HIT_COST = 4
POOL_PER_POS = 16          # how deep to search per position
SHORTLIST = 60             # bundles kept from the cheap pass for exact scoring


def _positions_key(players):
    k = {}
    for p in players:
        k[p["_pos"]] = k.get(p["_pos"], 0) + 1
    return tuple(sorted(k.items()))


def transfer_bundles(squad_els, pool, bank, sell_price, club_count,
                     depth=2, free=1, limit=6):
    """Best combinations of `depth` simultaneous transfers.

    Outgoing players are drawn from the squad, incoming from a pruned pool. The
    position multiset has to match, because FPL fixes the squad shape at 2/5/5/3
    -- you cannot sell a midfielder and buy a defender.

    Scored in two passes. The first ranks bundles by the raw change in squad
    expected points, which is quick but wrong: it happily recommends upgrading a
    bench player who will never be picked, because it counts all fifteen. The
    survivors are then rescored properly, by rebuilding the best legal eleven
    from the new squad -- which is the only total that actually scores points.
    """
    from itertools import combinations
    out_c = sorted(squad_els, key=lambda e: e["_xp5"])[:8]      # likeliest to leave
    best = []
    hits = max(0, depth - free) * HIT_COST
    by = {e["id"]: e for e in squad_els}

    def xi_total(els15):
        got = pick_eleven([{"id": e["id"], "pos": e["_pos"], "xp1": e["_xp5"]}
                           for e in els15])
        return got["xiPoints"] if got else 0.0

    before = xi_total(squad_els)

    for outs in combinations(out_c, depth):
        need = _positions_key(outs)
        budget = sum(sell_price(e) for e in outs) + bank
        out_ids = set(e["id"] for e in outs)
        cc = dict(club_count)
        for e in outs:
            cc[e["team"]] = cc.get(e["team"], 0) - 1
        base = sum(e["_xp5"] for e in outs)

        buckets = []
        for pos, n in need:
            cands = [e for e in pool.get(pos, [])
                     if e["id"] not in out_ids and num(e.get("now_cost")) <= budget]
            if len(cands) < n:
                buckets = None
                break
            buckets.append((pos, n, cands[:POOL_PER_POS]))
        if buckets is None:
            continue

        def walk(i, chosen, spent, gain, clubs):
            if spent > budget:
                return
            if i == len(buckets):
                if gain - base > 0:
                    best.append({"outs": [e["id"] for e in outs],
                                 "ins": [e["id"] for e in chosen],
                                 "_els": list(chosen), "_raw": gain - base,
                                 "hits": hits, "spend": spent,
                                 "spare": round((budget - spent) / 10.0, 1)})
                return
            pos, n, cands = buckets[i]
            for combo in combinations(cands, n):
                if any(c["id"] in (x["id"] for x in chosen) for c in combo):
                    continue
                cost = sum(num(c.get("now_cost")) for c in combo)
                if spent + cost > budget:
                    continue
                nc = dict(clubs)
                ok = True
                for c in combo:
                    nc[c["team"]] = nc.get(c["team"], 0) + 1
                    if nc[c["team"]] > 3:
                        ok = False
                        break
                if not ok:
                    continue
                walk(i + 1, chosen + list(combo), spent + cost,
                     gain + sum(c["_xp5"] for c in combo), nc)

        walk(0, [], 0.0, 0.0, cc)

    # second pass: rescore the shortlist on the eleven that would actually play
    best.sort(key=lambda b: -b["_raw"])
    seen, shortlist = set(), []
    for b in best:
        key = tuple(sorted(b["outs"])) + tuple(sorted(b["ins"]))
        if key in seen:
            continue
        seen.add(key)
        shortlist.append(b)
        if len(shortlist) >= SHORTLIST:
            break

    out = []
    for b in shortlist:
        gone = set(b["outs"])
        new15 = [e for e in squad_els if e["id"] not in gone] + b["_els"]
        after = xi_total(new15)
        net = after - before - b["hits"]
        if net <= 0:
            continue
        # pair each departure with the arrival that takes his place, by
        # position -- the two lists are not in a meaningful order otherwise, and
        # showing a midfielder swapped for a goalkeeper is nonsense
        pool_in = list(b["_els"])
        pairs, freed = [], 0.0
        for oid in b["outs"]:
            o = by[oid]
            match = next((c for c in pool_in if c["_pos"] == o["_pos"]), None)
            if match is None:
                continue
            pool_in.remove(match)
            gap = num(match.get("now_cost")) - sell_price(o)
            if gap < 0:
                freed += -gap
            pairs.append({"out": oid, "in": match["id"], "priceGap": round(gap / 10.0, 1)})
        upgrade = max([p["priceGap"] for p in pairs] or [0])
        out.append({"outs": b["outs"], "ins": b["ins"], "pairs": pairs,
                    "hits": b["hits"], "freed": round(freed / 10.0, 1),
                    "gain": round(after - before, 1), "net": round(net, 1),
                    "squadGain": round(b["_raw"], 1),
                    # a genuine reallocation frees real money from one player and
                    # spends it on another, rather than just shuffling like for like
                    "reallocation": bool(freed >= 20 and upgrade >= 2.0),
                    "spend": b["spend"], "spare": b["spare"]})
    # Bundles that differ only in a player who would sit on the bench score
    # identically, because the eleven is what is being measured. Collapse them
    # and keep whichever leaves the most money unspent.
    out.sort(key=lambda b: (-b["net"], -b["spare"]))
    seen2, final = set(), []
    for b in out:
        key = (tuple(sorted(b["outs"])), b["net"])
        if key in seen2:
            continue
        seen2.add(key)
        final.append(b)
        if len(final) >= limit:
            break
    return final


def replacement_level(els):
    """What the cheapest genuinely-playing option gives you, per position.

    This is the baseline that makes 'is he worth the money' answerable. A 4.5m
    defender who starts every week has superb points per million and is worth
    almost nothing as an upgrade, because you could have had one anyway.
    """
    out = {}
    for pos in ("GK", "DEF", "MID", "FWD"):
        grp = [e for e in els if e["_pos"] == pos and (e.get("_expMins") or 0) >= 55]
        if not grp:
            out[pos] = 0.0
            continue
        cheap = sorted(grp, key=lambda e: num(e.get("now_cost")))[:max(6, len(grp) // 6)]
        xs = sorted(e["_xp5"] for e in cheap)
        out[pos] = xs[int(0.75 * (len(xs) - 1))]
    return out


CHIP_NAMES = {"3xc": "Triple Captain", "bboost": "Bench Boost",
              "freehit": "Free Hit", "wildcard": "Wildcard",
              "manager": "Assistant Manager"}
CHIP_ALLOWANCE = 2         # 2026-27 gives two of each, one per half of the season


def chips_used(history):
    """Which chips this manager has already spent, and in which gameweek.

    The picks endpoint only says what was active in the round you asked for, so
    on its own it cannot tell "playing a chip now" apart from "played one last
    week". The history endpoint carries the whole list, which is what makes the
    difference statable.
    """
    out = {}
    for c in ((history or {}).get("chips") or []):
        name = c.get("name")
        if not name:
            continue
        out.setdefault(name, []).append(c.get("event"))
    return [{"key": k, "name": CHIP_NAMES.get(k, k), "gws": sorted(v),
             "used": len(v), "left": max(0, CHIP_ALLOWANCE - len(v))}
            for k, v in sorted(out.items())]


# ---------------------------------------------------------------------------
# Ask a question about your own team
# ---------------------------------------------------------------------------
# A chat grounded in this app's own numbers rather than in general football
# opinion. It is given the squad, the budget, the computed bundles and the
# fixture picture, plus the rules of the game -- and, crucially, a tool that
# runs the same transfer arithmetic the Transfers tab runs. That last part is
# what keeps it honest: asked to price a combination nobody has scored yet, it
# computes the answer instead of estimating one.
ANTHROPIC_KEY = os.environ.get("ANTHROPIC_API_KEY", "").strip()
ANTHROPIC_MODEL = os.environ.get("ANTHROPIC_MODEL", "").strip()
# Identity-linked keys (personal or service-account keys not tied to one
# workspace) must name the workspace they act in on every request. A key created
# FOR a workspace does not need this. Left unset, the app tries to learn it from
# a response header before giving up and telling you where to find it.
ANTHROPIC_WORKSPACE = os.environ.get("ANTHROPIC_WORKSPACE_ID", "").strip()
# overridable so the whole path can be exercised against a stub in testing
ANTHROPIC_HOST = os.environ.get("ANTHROPIC_HOST", "https://api.anthropic.com").rstrip("/")
CHAT_MAX_MONTH = int(os.environ.get("CHAT_MAX_MONTH", "500"))
CHAT_MAX_TOKENS = int(os.environ.get("CHAT_MAX_TOKENS", "1200"))
CHAT_STATE_FILE = os.environ.get("CHAT_STATE_FILE", "/tmp/fpl_dugout_chat.json")

# Per million tokens. Published prices; override if they move.
CHAT_PRICES = {"opus": (5.0, 25.0), "sonnet": (2.0, 10.0), "haiku": (1.0, 5.0)}

_chat = {"month": "", "questions": 0, "in": 0, "out": 0,
         "cacheRead": 0, "cacheWrite": 0, "model": None, "lastError": None,
         "workspace": None}
_payload_cache = {"t": 0.0, "data": None}


def _chat_load():
    try:
        with open(CHAT_STATE_FILE) as fh:
            saved = json.load(fh)
        if isinstance(saved, dict):
            _chat.update({k: saved.get(k, _chat[k]) for k in _chat})
    except Exception:                                        # noqa: BLE001
        pass


def _chat_save():
    """Best effort. Render's disk does not survive a redeploy, so the counter can
    reset -- which is stated in the interface rather than hidden."""
    try:
        with open(CHAT_STATE_FILE, "w") as fh:
            json.dump(_chat, fh)
    except Exception:                                        # noqa: BLE001
        pass


def _chat_month():
    mon = time.strftime("%Y-%m")
    if _chat["month"] != mon:
        _chat.update(month=mon, questions=0, **{"in": 0, "out": 0},
                     cacheRead=0, cacheWrite=0)
        _chat_save()
    return mon


def chat_price(model):
    m = (model or "").lower()
    for fam, pr in CHAT_PRICES.items():
        if fam in m:
            return pr
    return CHAT_PRICES["sonnet"]


def chat_spend():
    _chat_month()
    pin, pout = chat_price(_chat["model"])
    cost = (_chat["in"] / 1e6) * pin + (_chat["out"] / 1e6) * pout
    cost += (_chat["cacheRead"] / 1e6) * pin * 0.1
    cost += (_chat["cacheWrite"] / 1e6) * pin * 1.25
    return {
        "on": bool(ANTHROPIC_KEY), "model": _chat["model"] or ANTHROPIC_MODEL or None,
        "month": _chat["month"], "questions": _chat["questions"],
        "cap": CHAT_MAX_MONTH, "left": max(0, CHAT_MAX_MONTH - _chat["questions"]),
        "inTokens": _chat["in"], "outTokens": _chat["out"],
        "cacheRead": _chat["cacheRead"], "cacheWrite": _chat["cacheWrite"],
        "cost": round(cost, 4),
        "perQuestion": round(cost / _chat["questions"], 4) if _chat["questions"] else None,
        "priceIn": pin, "priceOut": pout,
        "stateFile": CHAT_STATE_FILE, "lastError": _chat["lastError"],
    }


WORKSPACE_HEADER = "anthropic-workspace-id"


def _anthropic(path, body=None, method="POST"):
    url = ANTHROPIC_HOST + path
    data = json.dumps(body).encode("utf-8") if body is not None else None
    headers = {"x-api-key": ANTHROPIC_KEY, "anthropic-version": "2023-06-01",
               "content-type": "application/json", "accept": "application/json"}
    ws = ANTHROPIC_WORKSPACE or _chat.get("workspace")
    if ws:
        headers[WORKSPACE_HEADER] = ws
    req = urllib.request.Request(url, data=data, method=method, headers=headers)
    with urllib.request.urlopen(req, timeout=90, context=ssl_context()) as r:
        # Any successful response names the workspace it ran in, which is the
        # documented way to discover it. Remember it so an identity-linked key
        # only has to be told once -- or, with luck, never.
        seen = r.headers.get(WORKSPACE_HEADER)
        if seen and not _chat.get("workspace"):
            _chat["workspace"] = seen
            _chat_save()
        return json.loads(r.read().decode("utf-8"))


def discover_workspace():
    """Ask a cheap endpoint which workspace this key acts in.

    A successful response carries the workspace in a header even when the
    request itself needed no workspace, which is the documented way to find it
    without an admin key.
    """
    for path in ("/v1/models?limit=1", "/v1/models"):
        try:
            _anthropic(path, None, "GET")
            if _chat.get("workspace"):
                return _chat["workspace"]
        except Exception:                                    # noqa: BLE001
            continue
    return None


def chat_model():
    """Which model to call.

    Model names change. Rather than freeze one into the source and have the app
    break the day it retires, ask the API what exists and take the newest Sonnet.
    An explicit ANTHROPIC_MODEL always wins.
    """
    if ANTHROPIC_MODEL:
        return ANTHROPIC_MODEL
    if _chat["model"]:
        return _chat["model"]
    try:
        got = _anthropic("/v1/models?limit=100", None, "GET")
        ids = [m["id"] for m in got.get("data", []) if m.get("id")]
        pref = [i for i in ids if "sonnet" in i.lower()] or \
               [i for i in ids if "haiku" in i.lower()] or ids
        # ids sort chronologically because they carry a date suffix
        _chat["model"] = sorted(pref)[-1]
        _chat_save()
        return _chat["model"]
    except Exception as e:                                   # noqa: BLE001
        _chat["lastError"] = "could not list models (%s)" % e
        return "claude-sonnet-4-5"


FPL_RULES = """RULES OF THE GAME (2026-27), which you may state as fact:

SQUAD. 15 players costing at most 100.0m at purchase: 2 goalkeepers, 5 defenders,
5 midfielders, 3 forwards. No more than 3 players from any one Premier League club.

TEAM SELECTION. Eleven start. Always exactly 1 goalkeeper; at least 3 defenders,
at least 2 midfielders, at least 1 forward. The other four sit on the bench in a
set order. The captain scores double; if he plays no minutes the vice-captain
takes it; if neither plays, nobody doubles. If a starter plays no minutes an
automatic substitution brings on the first bench player who keeps the formation
legal. The bench goalkeeper only ever replaces the goalkeeper.

TRANSFERS. One free transfer a gameweek. Unused ones accumulate up to a maximum
of 5. Each transfer beyond what you have costs 4 points, deducted from that
gameweek. Maximum 20 transfers in a gameweek outside a chip.

PRICES. Prices move at midnight UK time on ownership. When you sell, you keep
half of any rise the player has made since you bought him, rounded down to 0.1m.
Falls are not cushioned.

CHIPS. Two sets. Wildcard, Free Hit, Bench Boost and Triple Captain are each
available once in the first half and once in the second. The first set expires
at the Gameweek 19 deadline and does not carry over. One chip per gameweek.
Free Hit cannot be played in Gameweek 1. Wildcard makes transfers free and
permanent; Free Hit does the same for one week and then reverts the squad.

SCORING. Playing 1-59 minutes 1, 60+ minutes 2. Goal: goalkeeper 10, defender 6,
midfielder 5, forward 4. Assist 3. Clean sheet: goalkeeper or defender 4,
midfielder 1. Every 3 saves 1. Penalty saved 5. Penalty missed -2. Every 2 goals
conceded by a goalkeeper or defender -1. Yellow card -1, red card -3, own goal
-2. Bonus 1 to 3 for the best performers in a match. Defensive contribution: 2
points for a defender reaching 10 clearances, blocks, interceptions and tackles,
or a midfielder or forward reaching 12 including recoveries.

DEADLINE. 90 minutes before the first match of the gameweek."""


CHAT_TOOLS = [
    {
        "name": "score_transfers",
        "description": (
            "Price a specific transfer combination for the manager being viewed. "
            "Give the players leaving and the players arriving BY NAME. Returns "
            "whether the move is legal (positions, budget, three-per-club), the "
            "change in expected points for the eleven that would actually play, "
            "the points hit, and the net. Use this for ANY question of the form "
            "'what if I did X' -- never estimate the answer yourself."),
        "input_schema": {
            "type": "object",
            "properties": {
                "out": {"type": "array", "items": {"type": "string"},
                        "description": "Surnames of players to sell."},
                "in": {"type": "array", "items": {"type": "string"},
                       "description": "Surnames of players to buy."},
                "free_transfers": {"type": "integer",
                                   "description": "Free transfers held. Defaults to 1."},
            },
            "required": ["out", "in"],
        },
    },
    {
        "name": "match_history",
        "description": (
            "What a player actually did in each of his recent matches: opponent, "
            "whether he started, minutes, points, goals, assists, clean sheet, "
            "bonus, BPS and defensive actions. Use this whenever the question is "
            "about recent performance, a specific game, whether someone is in or "
            "out of the side, or whether form contradicts the model."),
        "input_schema": {
            "type": "object",
            "properties": {
                "name": {"type": "string", "description": "Player surname."},
                "names": {"type": "array", "items": {"type": "string"},
                          "description": "Several players at once, to compare."},
            },
        },
    },
    {
        "name": "find_players",
        "description": (
            "Look up players by name fragment, or list the best available in a "
            "position within a price ceiling. Returns expected points for the next "
            "match and the next five, price, ownership and the fixture run."),
        "input_schema": {
            "type": "object",
            "properties": {
                "name": {"type": "string", "description": "Name fragment to search for."},
                "position": {"type": "string", "enum": ["GK", "DEF", "MID", "FWD"]},
                "max_price": {"type": "number", "description": "Ceiling in millions."},
                "limit": {"type": "integer"},
            },
        },
    },
]


# ---- the tools, run against the payload the interface is showing ----------
def _pindex(payload):
    return {p["id"]: p for p in payload["players"]}


def _match_players(payload, needles, pool=None):
    """Names to players. Surnames are how people actually refer to footballers."""
    ps = pool if pool is not None else payload["players"]
    out, missed = [], []
    for n in needles:
        key = (n or "").strip().lower()
        if not key:
            continue
        hits = [p for p in ps if key == p["name"].lower()]
        if not hits:
            hits = [p for p in ps if key in p["name"].lower()]
        if not hits:
            hits = [p for p in ps if key in (p.get("full") or p["name"]).lower()]
        if not hits:
            missed.append(n)
            continue
        hits.sort(key=lambda p: -(p.get("proj5") or 0))
        out.append(hits[0])
    return out, missed


def tool_find_players(payload, args):
    P = payload["players"]
    pool = P
    if args.get("position"):
        pool = [p for p in pool if p["pos"] == args["position"]]
    if args.get("max_price") is not None:
        pool = [p for p in pool if p["price"] <= float(args["max_price"]) + 1e-9]
    if args.get("name"):
        pool, _ = _match_players(payload, [args["name"]], pool)
        if not pool:
            return {"error": "no player matched %r" % args["name"]}
    pool = sorted(pool, key=lambda p: -(p.get("proj5") or 0))[:int(args.get("limit") or 8)]
    fx = payload.get("fixtures", {})
    rows = []
    for p in pool:
        runs = (fx.get(p["club"]) or {}).get("runs") or []
        rows.append({
            "name": p["name"], "club": p["club"], "pos": p["pos"], "price": p["price"],
            "xPtsNext": p.get("xp1"), "xPtsNext5": p.get("proj5"),
            "pointsPerMillion": p.get("ppm"), "aboveReplacement": p.get("var"),
            "owned": p.get("owned"), "status": p.get("status"),
            "expectedMinutes": p.get("expMins"),
            "fixtures": ["GW%s %s%s d%s" % (r["gw"], r.get("opp"), r.get("ha"), r.get("fdr"))
                         for r in runs if r.get("opp")][:5],
        })
    return {"players": rows}


def tool_match_history(payload, args):
    names = list(args.get("names") or [])
    if args.get("name"):
        names.append(args["name"])
    if not names:
        return {"error": "give at least one player name"}
    found, missed = _match_players(payload, names)
    if not found:
        return {"error": "no player matched %s" % ", ".join(names)}
    out = []
    for p in found:
        rows = []
        for r in (p.get("log") or []):
            rows.append({
                "gw": r[0], "opponent": r[1], "venue": r[2], "minutes": r[3],
                "started": bool(r[4]), "points": r[5], "goals": r[6],
                "assists": r[7], "cleanSheet": bool(r[8]), "bonus": r[9],
                "bps": r[10], "defensiveActions": r[11],
            })
        out.append({
            "name": p["name"], "club": p["club"], "pos": p["pos"],
            "chanceOfStarting": p.get("pStart"),
            "startingEvidence": p.get("startWhy"),
            "availability": p.get("status"),
            "fplNews": p.get("news") or None,
            "expectedMinutes": p.get("expMins"),
            "matches": rows,
            "note": ("Only gameweeks in which he was on the pitch appear. An empty "
                     "list means he has not played in the window."),
        })
    return {"players": out,
            "windowGameweeks": (payload["meta"].get("model") or {}).get("formGws"),
            "notFound": missed or None}


def tool_score_transfers(payload, entry, args):
    mm = (payload.get("managers") or {}).get(str(entry))
    if not mm:
        return {"error": "no squad loaded for this manager"}
    idx = _pindex(payload)
    squad = [dict(idx[pk["id"]], sell=pk["sell"]) for pk in mm["picks"] if pk["id"] in idx]
    outs, miss_o = _match_players(payload, args.get("out") or [], squad)
    owned = set(p["id"] for p in squad)
    pool = [p for p in payload["players"] if p["id"] not in owned]
    ins, miss_i = _match_players(payload, args.get("in") or [], pool)
    if miss_o:
        return {"error": "not in this squad: %s" % ", ".join(miss_o)}
    if miss_i:
        return {"error": "could not find, or already owned: %s" % ", ".join(miss_i)}
    if len(outs) != len(ins):
        return {"error": "%d out but %d in; a transfer is one for one"
                         % (len(outs), len(ins))}
    if not outs:
        return {"error": "no transfers given"}

    problems = []
    from collections import Counter
    if Counter(p["pos"] for p in outs) != Counter(p["pos"] for p in ins):
        problems.append("positions do not match: out %s, in %s"
                        % ("/".join(p["pos"] for p in outs), "/".join(p["pos"] for p in ins)))
    bank = mm["budget"]["bank"]
    funds = sum(p["sell"] for p in outs) + bank
    cost = sum(p["price"] for p in ins)
    if cost > funds + 1e-9:
        problems.append("costs %.1fm but only %.1fm available (%.1fm of sales plus %.1fm bank)"
                        % (cost, funds, funds - bank, bank))
    clubs = Counter(p["club"] for p in squad)
    for p in outs:
        clubs[p["club"]] -= 1
    for p in ins:
        clubs[p["club"]] += 1
    over = [c for c, n in clubs.items() if n > 3]
    if over:
        problems.append("would leave more than three from %s" % ", ".join(sorted(over)))

    out_ids = set(p["id"] for p in outs)
    new15 = [p for p in squad if p["id"] not in out_ids] + ins

    def xi(sq, key):
        got = pick_eleven([{"id": p["id"], "pos": p["pos"], "xp1": p.get(key) or 0.0}
                           for p in sq])
        return got if got else None

    b5, a5 = xi(squad, "proj5"), xi(new15, "proj5")
    b1, a1 = xi(squad, "xp1"), xi(new15, "xp1")
    free = int(args.get("free_transfers") or mm.get("freeTransfers") or 1)
    hits = max(0, len(outs) - free) * HIT_COST
    gain5 = (a5["xiPoints"] - b5["xiPoints"]) if (a5 and b5) else 0.0
    gain1 = (a1["xiPoints"] - b1["xiPoints"]) if (a1 and b1) else 0.0
    if problems:
        # Reporting an attractive gain for an impossible move invites it to be
        # quoted back at the user. Say why it cannot be done, and nothing else.
        return {"legal": False, "problems": problems,
                "out": [p["name"] for p in outs], "in": [p["name"] for p in ins],
                "note": "This move cannot be made, so it has not been scored."}
    return {
        "legal": True,
        "problems": [],
        "out": [{"name": p["name"], "pos": p["pos"], "sellFor": p["sell"],
                 "xPtsNext5": p.get("proj5")} for p in outs],
        "in": [{"name": p["name"], "pos": p["pos"], "price": p["price"],
                "xPtsNext5": p.get("proj5")} for p in ins],
        "moneyLeftOver": round(funds - cost, 1),
        "freeTransfersAssumed": free,
        "pointsHit": hits,
        "xiGainNext5": round(gain5, 1),
        "xiGainNextMatch": round(gain1, 2),
        "netAfterHit": round(gain5 - hits, 1),
        "note": ("Gains are measured on the eleven that would actually play, not on "
                 "all fifteen, so upgrading a player who would stay benched shows as "
                 "little or nothing."),
    }


def chat_context(payload, entry):
    """The compact briefing the model gets about this specific team."""
    mm = (payload.get("managers") or {}).get(str(entry)) or {}
    idx = _pindex(payload)
    L = mm.get("lineup") or {}
    nm = lambda i: (idx.get(i) or {}).get("name", "?")

    lines = ["THE TEAM YOU ARE ADVISING: %s, run by %s." % (mm.get("team"), mm.get("mgr")),
             "Gameweek %s is next. League position %s of %s, %s points."
             % (payload["meta"].get("planGw") or payload["meta"].get("gw"),
                mm.get("rank"), len(payload.get("standings") or []), mm.get("total")),
             "Budget: %.1fm squad value, %.1fm in the bank."
             % (mm["budget"]["squadValue"], mm["budget"]["bank"]) if mm.get("budget") else "",
             "Free transfers assumed: %s (the public API does not report the real number)."
             % mm.get("freeTransfers", 1),
             "", "SQUAD (xPts next match / next five / price / sells for), then his fixtures and \
his last four appearances with points scored:"]
    for pk in mm.get("picks", []):
        p = idx.get(pk["id"])
        if not p:
            continue
        tag = []
        if pk.get("isCap"):
            tag.append("captain")
        if pk.get("isVice"):
            tag.append("vice")
        tag.append("in the XI" if pk.get("starting") else "benched")
        tag.append("%d%% to start" % round(100 * (p.get("pStart") or 0)))
        if p.get("startWhy"):
            tag.append(p["startWhy"])
        if p.get("news"):
            tag.append("FPL NEWS: " + p["news"])
        elif p.get("status") and p["status"] != "a":
            tag.append("flagged (%s)" % p["status"])
        recent = " ".join("%s%s %s%dpt" % (r[1], r[2], "" if r[4] else "sub ", r[5])
                          for r in (p.get("log") or [])[-4:]) or "no minutes yet"
        runs = ((payload.get("fixtures") or {}).get(p["club"]) or {}).get("runs") or []
        fx = " ".join("%s%s(%s)" % (r.get("opp"), r.get("ha"), r.get("fdr"))
                      for r in runs if r.get("opp"))
        lines.append("  %-3s %-18s %-4s %5.2f / %5.1f / %4.1fm / %4.1fm  [%s]"
                     % (p["pos"], p["name"], p["club"], p.get("xp1") or 0,
                        p.get("proj5") or 0, p["price"], pk.get("sell") or 0,
                        ", ".join(tag)))
        lines.append("        fixtures %s | recent %s" % (fx, recent))

    if L:
        lines += ["", "WHAT THE MODEL WOULD FIELD THIS WEEK: %s, %s expected points "
                      "(%s with the captain doubled)."
                  % (L.get("formation"), L.get("xiPoints"), L.get("withCaptain")),
                  "  Captain %s, vice %s. Bench in order: %s."
                  % (nm(L.get("captain")), nm(L.get("vice")),
                     ", ".join(nm(i) for i in L.get("bench", [])) or "-"),
                  "  Against what is currently picked that is worth %s points."
                  % L.get("gain")]
        if L.get("closeCalls"):
            lines.append("  Genuinely close: " + "; ".join(
                "%s over %s by %.2f" % (nm(c["in"]), nm(c["out"]), c["gap"])
                for c in L["closeCalls"]))
        ch = L.get("chips") or {}
        lines.append("  Bench Boost would be worth %s. Triple Captain would add %s."
                     % (ch.get("benchBoost"), ch.get("tripleCaptain")))
    if mm.get("chipsUsed"):
        lines.append("  Chips already played: " + "; ".join(
            "%s in GW%s" % (c["name"], "/".join(str(g) for g in c["gws"]))
            for c in mm["chipsUsed"]))

    B = mm.get("bundles") or {}
    if B.get("2") or B.get("3"):
        lines += ["", "TRANSFER BUNDLES ALREADY COMPUTED (net is after the points hit):"]
        for k in ("2", "3"):
            for b in (B.get(k) or [])[:4]:
                pairs = "; ".join("%s -> %s" % (nm(pr["out"]), nm(pr["in"]))
                                  for pr in b.get("pairs", []))
                lines.append("  %s moves: %s | eleven gains %s, hit -%s, net %s%s"
                             % (k, pairs, b["gain"], b["hits"], b["net"],
                                " [reallocation]" if b.get("reallocation") else ""))
    tx = mm.get("transfers") or []
    if tx:
        lines += ["", "BEST SINGLE SWAPS:"]
        for t in tx[:6]:
            lines.append("  %s -> %s, gain %s over five"
                         % (nm(t["outId"]), nm(t["inId"]), t["gain5"]))

    st = payload.get("standings") or []
    if st:
        lines += ["", "MINI-LEAGUE: " + ", ".join(
            "%s %s (%s pts)" % (s.get("rank"), s.get("team") or s.get("entry_name"),
                                s.get("total")) for s in st[:10])]

    o = payload.get("odds") or {}
    lines += ["", "DATA NOTES: fixture difficulty is the betting market's win chance minus "
                  "lose chance where a match is priced (%s fixtures right now), and the "
                  "results-based model beyond that. Expected points come from last season's "
                  "per-90 rates updated by this season, crossing over around eleven matches "
                  "played. A typical model of this kind is about 5 points out on players who "
                  "haul, so treat gaps of a point or two as noise."
              % (o.get("priced") if o.get("status") == "on" else "no")]
    return "\n".join(l for l in lines if l != "")


CHAT_SYSTEM = """You are the assistant inside FPL Dugout, a Fantasy Premier League
dashboard. You are talking to the manager whose team is described below.

HOW TO BE USEFUL HERE

Answer about THIS squad, using the numbers you are given. Generic Fantasy advice
is not what this is for -- the person can read that anywhere. Quote the actual
expected points, prices and fixtures.

For any "what if" -- any combination of transfers the briefing does not already
price -- call score_transfers. Do not estimate. The tool runs the same arithmetic
the app runs, including whether the move is even legal. If someone asks about a
player not in the briefing, call find_players.

You CAN see match-by-match history. If someone says a player did well last week,
call match_history and check rather than saying you cannot. It returns the
opponent, whether he started, minutes, points, goals, assists, clean sheet,
bonus and BPS for each recent appearance. Use it whenever recent form, a
specific game, or whether someone is in the side comes up.

You also have a chance-of-starting figure for every player, built from recent
team sheets, last season's start rate and FPL's own availability flag, with the
evidence behind it. It is a base rate, not inside information: it cannot see a
press conference, and a manager resting someone for a European tie will not
appear until FPL flags him. Say so when a decision turns on it. Where FPL has
published news on a player -- an injury note, a percentage chance -- it is in
the briefing and it is real, so use it.

Recommend. When the numbers point somewhere, say so plainly rather than laying
out options and retreating. But the gaps are often inside the error bars, and
when they are, say that too: "these are within a point, so it is a coin toss and
team news should decide it" is a better answer than false precision.

WHAT THE NUMBERS ARE AND ARE NOT

Expected points are a forecast in real FPL points, so they can be weighed
directly against a 4-point hit. They are not certainty: the published research
puts even a trained model around 5 points of error on the players who actually
haul. A one or two point edge over five matches is noise, and you should say so.

The model cannot see team news, press conferences, rotation for cup or European
matches, or whether a player is genuinely nailed on. That is the single biggest
gap and it is worth naming when a decision hinges on it.

Fixture difficulty here runs 1 to 5 where 3 is an even match, derived from win
probability -- not from how good the opponent is. A strong team at home to
another strong team can read 2 while being a hard game for a clean sheet. If
that distinction matters to the answer, explain it.

STYLE

Conversational and brief. Plain prose, not headed reports. A short table only
when comparing several players on the same measures. No bullet lists of caveats.
Do not restate the question. Never invent a number: if you do not have it and no
tool gives it to you, say so.""" + "\n\n" + FPL_RULES


def chat_answer(messages, entry, payload):
    """One turn, including any tool calls the model needs. Returns (reply, meta)."""
    if not ANTHROPIC_KEY:
        return None, {"error": "No ANTHROPIC_API_KEY is set on the server, so the "
                               "assistant is switched off."}
    _chat_month()
    if _chat["questions"] >= CHAT_MAX_MONTH:
        return None, {"error": "The monthly limit of %d question%s has been reached. "
                               "It resets on the first of the month."
                               % (CHAT_MAX_MONTH, "" if CHAT_MAX_MONTH == 1 else "s")}

    model = chat_model()
    convo = [{"role": m["role"], "content": m["content"]} for m in messages
             if m.get("role") in ("user", "assistant") and m.get("content")][-16:]
    if not convo or convo[-1]["role"] != "user":
        return None, {"error": "nothing to answer"}

    system = [
        {"type": "text", "text": CHAT_SYSTEM,
         "cache_control": {"type": "ephemeral"}},
        {"type": "text", "text": chat_context(payload, entry)},
    ]
    used_tools = []
    tried_workspace = [False]
    for _ in range(6):
        body = {"model": model, "max_tokens": CHAT_MAX_TOKENS,
                "system": system, "messages": convo, "tools": CHAT_TOOLS}
        try:
            res = _anthropic("/v1/messages", body)
        except urllib.error.HTTPError as e:
            detail = ""
            try:
                detail = json.loads(e.read().decode("utf-8")).get("error", {}).get("message", "")
            except Exception:                                # noqa: BLE001
                pass
            if WORKSPACE_HEADER in (detail or "") and not tried_workspace[0]:
                # The key is identity-linked and is not tied to a workspace. If a
                # response header has already told us which one to use, retry
                # with it; otherwise say exactly what to set and where to get it.
                tried_workspace[0] = True
                if _chat.get("workspace") or ANTHROPIC_WORKSPACE:
                    continue
                found = discover_workspace()
                if found:
                    _chat["workspace"] = found
                    _chat_save()
                    continue
                msg = ("This API key is identity-linked, so every request has to say "
                       "which workspace it belongs to. Two ways to fix it: create a new "
                       "key scoped to a single workspace, which needs no extra setup; or "
                       "find the ID in the Anthropic Console under Settings then "
                       "Workspaces, in the ID column (it looks like wrkspc_01ABC...), and "
                       "set it on Render as ANTHROPIC_WORKSPACE_ID.")
                _chat["lastError"] = msg
                _chat_save()
                return None, {"error": msg}
            msg = {401: "the API key was rejected",
                   429: "rate limited by the API, try again shortly",
                   400: "the request was rejected: " + detail,
                   529: "the API is overloaded, try again shortly"}.get(
                       e.code, "the API returned HTTP %d. %s" % (e.code, detail))
            _chat["lastError"] = msg
            _chat_save()
            return None, {"error": msg}
        except Exception as e:                               # noqa: BLE001
            _chat["lastError"] = str(e)
            _chat_save()
            return None, {"error": "could not reach the API (%s)" % e}

        u = res.get("usage") or {}
        _chat["in"] += int(u.get("input_tokens") or 0)
        _chat["out"] += int(u.get("output_tokens") or 0)
        _chat["cacheRead"] += int(u.get("cache_read_input_tokens") or 0)
        _chat["cacheWrite"] += int(u.get("cache_creation_input_tokens") or 0)
        _chat["model"] = res.get("model") or model

        blocks = res.get("content") or []
        calls = [b for b in blocks if b.get("type") == "tool_use"]
        if res.get("stop_reason") == "tool_use" and calls:
            convo.append({"role": "assistant", "content": blocks})
            results = []
            for c in calls:
                try:
                    if c["name"] == "score_transfers":
                        out = tool_score_transfers(payload, entry, c.get("input") or {})
                    elif c["name"] == "match_history":
                        out = tool_match_history(payload, c.get("input") or {})
                    elif c["name"] == "find_players":
                        out = tool_find_players(payload, c.get("input") or {})
                    else:
                        out = {"error": "unknown tool"}
                except Exception as e:                       # noqa: BLE001
                    out = {"error": "%s: %s" % (type(e).__name__, e)}
                used_tools.append({"name": c["name"], "input": c.get("input")})
                results.append({"type": "tool_result", "tool_use_id": c["id"],
                                "content": json.dumps(out)})
            convo.append({"role": "user", "content": results})
            continue

        text = "\n".join(b.get("text", "") for b in blocks if b.get("type") == "text").strip()
        _chat["questions"] += 1
        _chat_save()
        return text, {"model": _chat["model"], "tools": used_tools,
                      "spend": chat_spend()}

    _chat["questions"] += 1
    _chat_save()
    return None, {"error": "gave up after five rounds of tool calls"}


_chat_load()


def season_of(events):
    """Which season these fixtures belong to, as FPL labels it (e.g. 2026-27).

    Taken from the first deadline of the campaign, which always falls in August.
    """
    firsts = [e.get("deadline_time") for e in events if e.get("deadline_time")]
    if not firsts:
        return None
    y = int(min(firsts)[:4])
    return "%d-%02d" % (y, (y + 1) % 100)


def prior_is_current(events):
    """Is the embedded last-season table still the season immediately past?

    The table is baked into this file because last season cannot change. That is
    true right up until a new season starts, at which point the priors quietly
    become a year out of date and nothing would otherwise say so. Rather than let
    that rot in silence, compare what the fixtures say the season is against what
    the table was built from.
    """
    cur = season_of(events)
    if not cur:
        return True, None, None
    want = "%d-%02d" % (int(cur[:4]) - 1, int(cur[:4]) % 100)
    return (want == PRIOR_SEASON), want, cur


def build_payload(entry_id, league_id):
    """Everything the UI needs, with a full perspective computed per manager.

    Each manager in the league gets their own squad, budget, transfer options,
    captaincy ranking and differentials, so the whole app can switch between
    them. Player records live once in `players`; everything else refers to
    them by id to keep the payload small.
    """
    boot = fetch("/bootstrap-static/", ttl=CACHE_TTL)
    fixtures = fetch("/fixtures/", ttl=600)

    events = boot["events"]
    cur = next((e for e in events if e.get("is_current")), None)
    nxt = next((e for e in events if e.get("is_next")), None)
    gw = (cur or nxt or events[0])["id"]
    plan_from = (nxt or cur or events[0])["id"]
    # Between the final whistle of one round and the deadline of the next, the
    # API still reports the finished round as current. Picks fetched then are
    # LAST week's, chip included -- so record whether that round is over and
    # never describe its chip as active.
    # Careful with the test. is_next appears the moment a deadline passes, so
    # "plan_from != gw" is true all the way through a round being played, and
    # would call a chip spent while it is still scoring. The round being over is
    # the only signal that means what it says.
    picks_gw_done = bool((cur or {}).get("finished")) or cur is None

    teams = {t["id"]: t for t in boot["teams"]}

    # strength from results, not a pre-season opinion
    strength = team_strength(fixtures, boot["teams"])
    matches_played = max([v["played"] for k, v in strength.items()
                          if not str(k).startswith("_")] or [0])
    priced, odds_unmatched = odds_by_fixture(fixtures, boot["teams"])
    fixmap = build_fixture_map(fixtures, boot["teams"], plan_from, strength, priced)

    # per-gameweek logs for multi-window form, hit rates and real minutes
    last_done = max([e["id"] for e in events if e.get("finished")] or [0])
    hist, hist_gws = ({}, [])
    if last_done:
        hist, hist_gws = gw_history(last_done, FORM_WINDOW, fixtures, boot["teams"])

    els = score_players(boot, fixmap, hist, matches_played)
    w_prior, w_obs, w_fix = model_weights(matches_played)
    by_id = {e["id"]: e for e in els}
    players = [slim(e, teams) for e in els]
    pslim = {p["id"]: p for p in players}
    repl = replacement_level(els)
    for e in els:
        sel, mult = run_window(e["team"], fixmap)
        pr = pslim[e["id"]]
        pr["base"] = round(e["_xp1"], 2)
        pr["mult5"] = round(mult, 2)
        pr["games5"] = len(sel)
        pr["proj5"] = e["_xp5"]
        pr["xp1"] = e["_xp1"]
        pr["ppm"] = e["_ppm"]
        pr["var"] = round(e["_xp5"] - repl.get(e["_pos"], 0.0), 1)
        e["_var"] = pr["var"]
        e["_proj5"] = e["_xp5"]

    def sell_price(e):
        purchase = num(e.get("now_cost")) - num(e.get("cost_change_start"))
        rise = num(e.get("now_cost")) - purchase
        return purchase + (rise // 2 if rise > 0 else 0)

    # ---------------- who is in the league ----------------
    rows, league = [], None
    try:
        lg = fetch("/leagues-classic/%d/standings/" % league_id, ttl=180)
        league = {"id": league_id, "name": lg["league"]["name"]}
        rows = lg["standings"]["results"]
    except FPLError:
        rows = []

    if not any(r["entry"] == entry_id for r in rows):
        # league unavailable, or you are not in it -- still show your own team
        try:
            me_entry = fetch("/entry/%d/" % entry_id, ttl=120)
            rows = [{"rank": 1, "entry": entry_id,
                     "entry_name": me_entry.get("name", "My team"),
                     "player_name": ("%s %s" % (me_entry.get("player_first_name", ""),
                                                me_entry.get("player_last_name", ""))).strip(),
                     "event_total": me_entry.get("summary_event_points", 0),
                     "total": me_entry.get("summary_overall_points", 0)}] + rows
        except FPLError:
            pass

    picks_by_entry, entry_by_entry, hist_by_entry = {}, {}, {}
    for r in rows:
        try:
            picks_by_entry[r["entry"]] = fetch(
                "/entry/%d/event/%d/picks/" % (r["entry"], gw), ttl=180)
        except FPLError:
            picks_by_entry[r["entry"]] = None
        try:
            entry_by_entry[r["entry"]] = fetch("/entry/%d/" % r["entry"], ttl=300)
        except FPLError:
            entry_by_entry[r["entry"]] = {}
        try:
            hist_by_entry[r["entry"]] = fetch("/entry/%d/history/" % r["entry"], ttl=300)
        except FPLError:
            hist_by_entry[r["entry"]] = {}

    def ids_of(entry):
        rp = picks_by_entry.get(entry)
        return [p["element"] for p in rp["picks"]] if rp else []

    # who owns whom, across the league
    own = {}
    for r in rows:
        for pid in ids_of(r["entry"]):
            own.setdefault(pid, []).append(r["entry_name"])

    # ---------------- one full perspective per manager ----------------
    def alts_for(pid, my_ids, bank, club_count, n=6):
        out_e = by_id[pid]
        budget = sell_price(out_e) + bank
        cc = dict(club_count)
        cc[out_e["team"]] = cc.get(out_e["team"], 0) - 1
        cands = [e for e in els
                 if e["_pos"] == out_e["_pos"] and e["id"] not in my_ids
                 and num(e.get("now_cost")) <= budget
                 and cc.get(e["team"], 0) + 1 <= 3
                 and e["_avail"] >= 0.5]
        cands.sort(key=lambda e: -e["_score"])
        opts = []
        for e in cands[:n]:
            opts.append({"id": e["id"],
                         "delta": round(e["_score"] - out_e["_score"], 1),
                         "spare": round((budget - num(e.get("now_cost"))) / 10, 1),
                         "why": reasons(pslim[e["id"]])})
        return {"budget": round(budget / 10, 1), "options": opts}

    # Render's free tier is a fraction of a CPU. The bundle search is the only
    # expensive thing here, so it gets a whole-payload budget: once it is spent,
    # later managers get two-transfer bundles only, and then none. A slower host
    # loses depth rather than timing the page out.
    search_budget = [float(os.environ.get("FPL_SEARCH_BUDGET", "12.0"))]

    managers = {}
    for r in rows:
        entry = r["entry"]
        rp = picks_by_entry.get(entry)
        ent = entry_by_entry.get(entry) or {}
        my_ids = ids_of(entry)
        eh = (rp or {}).get("entry_history", {})
        bank = num(eh.get("bank", ent.get("last_deadline_bank", 0)))
        value = num(eh.get("value", ent.get("last_deadline_value", 1000)))

        club_count = {}
        for pid in my_ids:
            t = by_id[pid]["team"]
            club_count[t] = club_count.get(t, 0) + 1

        cap = next((p["element"] for p in (rp["picks"] if rp else []) if p.get("is_captain")), None)
        vice = next((p["element"] for p in (rp["picks"] if rp else []) if p.get("is_vice_captain")), None)

        picks_out = []
        for pk in (rp["picks"] if rp else []):
            pid = pk["element"]
            picks_out.append({
                "id": pid, "starting": pk["position"] <= 11,
                "isCap": pid == cap, "isVice": pid == vice,
                "mult": pk.get("multiplier", 1),
                "sell": round(sell_price(by_id[pid]) / 10, 1),
                "alts": alts_for(pid, my_ids, bank, club_count),
            })

        # captaincy: outfield starters only, ranked, with rival ownership
        rival_own = {}
        for r2 in rows:
            if r2["entry"] == entry:
                continue
            for pid in ids_of(r2["entry"]):
                rival_own[pid] = rival_own.get(pid, 0) + 1
        rivals = max(1, len(rows) - 1)
        starters = [p for p in picks_out
                    if p["starting"] and pslim[p["id"]]["pos"] != "GK"]
        starters.sort(key=lambda p: -pslim[p["id"]]["score"])
        captaincy = [{"id": p["id"],
                      "isCap": p["isCap"], "isVice": p["isVice"],
                      "nextFix": (fixmap.get(pslim[p["id"]]["teamId"], {}).get("runs") or [{}])[0],
                      "rivalsOwning": rival_own.get(p["id"], 0),
                      "leagueSize": rivals}
                     for p in starters[:8]]

        mine = set(my_ids)
        uniques = [pid for pid in my_ids if len(own.get(pid, [])) <= 1]
        missing = sorted(
            [{"id": pid, "ownedBy": len(v), "owners": v}
             for pid, v in own.items() if pid not in mine],
            key=lambda d: (-d["ownedBy"], -pslim[d["id"]]["score"]))[:14]

        # every legal swap, ranked by what it does over the next five matches
        cand_pool = {}
        for pos in ("GK", "DEF", "MID", "FWD"):
            cand_pool[pos] = [e for e in els if e["_pos"] == pos
                              and e["id"] not in my_ids and e["_avail"] >= 0.5]
        moves = []
        for pk in picks_out:
            out_e = by_id[pk["id"]]
            budget = sell_price(out_e) + bank
            cc = dict(club_count)
            cc[out_e["team"]] = cc.get(out_e["team"], 0) - 1
            legal = [e for e in cand_pool[out_e["_pos"]]
                     if num(e.get("now_cost")) <= budget
                     and cc.get(e["team"], 0) + 1 <= 3]
            legal.sort(key=lambda e: -(e["_proj5"] - out_e["_proj5"]))
            for e in legal[:2]:          # at most two per outgoing player, for variety
                gain = e["_proj5"] - out_e["_proj5"]
                if gain <= 0:
                    continue
                moves.append({
                    "outId": pk["id"], "inId": e["id"],
                    "gain5": round(gain, 1),
                    "delta": round(e["_score"] - out_e["_score"], 1),
                    "cost": round((num(e.get("now_cost")) - sell_price(out_e)) / 10, 1),
                    "spare": round((budget - num(e.get("now_cost"))) / 10, 1),
                    "why": reasons(pslim[e["id"]]),
                })
        moves.sort(key=lambda t: -t["gain5"])

        # ---- the team sheet: who plays, who sits, who wears the armband ----
        squad_els = [by_id[pid] for pid in my_ids if pid in by_id]
        lineup = pick_eleven([{"id": e["id"], "pos": e["_pos"], "xp1": e["_xp1"]}
                              for e in squad_els]) if squad_els else None
        if lineup:
            cur_xi = set(p["id"] for p in picks_out if p["starting"])
            new_in = [i for i in lineup["xi"] if i not in cur_xi]
            new_out = [i for i in cur_xi if i not in set(lineup["xi"])]
            lineup["changes"] = [{"in": a, "out": b} for a, b in zip(new_in, new_out)]
            lineup["currentPoints"] = round(
                sum(by_id[i]["_xp1"] for i in cur_xi if i in by_id), 1)
            lineup["gain"] = round(lineup["xiPoints"] - lineup["currentPoints"], 1)
            lineup["marketBacked"] = sum(
                1 for e in squad_els
                if ((fixmap.get(e["team"], {}).get("runs") or [{}])[0] or {}).get("src") == "odds")
            lineup["squadSize"] = len(squad_els)
            lineup["capIsCurrent"] = (lineup.get("captain") == cap)

        # ---- more than one transfer at a time ----
        # The public API does not report how many free transfers you are holding;
        # event_transfers is how many you made last week, which is a different
        # thing. So assume one, the common case, and say so in the interface
        # rather than quietly guessing.
        free = 1
        bundles = {}
        try:
            t0 = time.time()
            for depth in (2, 3):
                if search_budget[0] <= 0 or (depth == 3 and search_budget[0] < 3.0):
                    bundles["trimmed"] = True
                    break
                bundles[str(depth)] = transfer_bundles(
                    squad_els, cand_pool, bank, sell_price, club_count,
                    depth=depth, free=min(depth, free), limit=5)
            bundles["ms"] = int((time.time() - t0) * 1000)
            search_budget[0] -= (time.time() - t0)
        except Exception as exc:                              # noqa: BLE001
            bundles = {"error": str(exc)}

        managers[str(entry)] = {
            "lineup": lineup, "bundles": bundles, "freeTransfers": free,
            "entry": entry, "team": r["entry_name"], "mgr": r["player_name"],
            "rank": r["rank"], "total": r["total"], "gw": r["event_total"],
            "overallRank": ent.get("summary_overall_rank"),
            "value": value, "bank": bank, "chip": (rp or {}).get("active_chip"),
            "chipGw": gw, "chipSpent": picks_gw_done,
            "chipsUsed": chips_used(hist_by_entry.get(entry)),
            "budget": {"squadValue": round(value / 10, 1), "bank": round(bank / 10, 1),
                       "total": round((value + bank) / 10, 1)},
            "clubCounts": {teams[k]["short_name"]: v for k, v in club_count.items()},
            "clubCountsById": {str(k): v for k, v in club_count.items()},
            "picks": picks_out, "captaincy": captaincy, "transfers": moves[:20],
            "uniques": uniques, "missing": missing,
            "hasPicks": bool(rp),
        }

    clubs = []
    for t in sorted(boot["teams"], key=lambda x: x["name"]):
        roster = sorted([p for p in players if p["teamId"] == t["id"]],
                        key=lambda p: -p["score"])
        clubs.append({
            "id": t["id"], "name": t["name"], "short": t["short_name"],
            "code": int(num(t.get("code"))),
            "strength": t.get("strength"),
            "atkH": t.get("strength_attack_home"), "atkA": t.get("strength_attack_away"),
            "defH": t.get("strength_defence_home"), "defA": t.get("strength_defence_away"),
            "avgFdr": fixmap.get(t["id"], {}).get("avgFdr"),
            "squad": [p["id"] for p in roster],
        })

    return {
        "meta": {
            "planGw": plan_from,
            "gw": gw, "planFrom": plan_from,
            "gwName": (cur or nxt or events[0]).get("name"),
            "deadline": (nxt or {}).get("deadline_time"),
            "fetched": time.strftime("%Y-%m-%d %H:%M:%S"),
            "live": not bool(MOCK_DIR),
            "model": {"wPrior": w_prior, "wObs": w_obs, "wFix": w_fix,
                      "matchesPlayed": matches_played,
                      "formGws": hist_gws, "formWindow": FORM_WINDOW,
                      "priorMatches": PRIOR_MATCHES, "homeAdv": HOME_ADV,
                      "priorSeason": PRIOR_SEASON,
                      "season": season_of(events),
                      "priorStale": (lambda t: None if t[0] else
                                     {"have": PRIOR_SEASON, "want": t[1], "season": t[2]})(
                                        prior_is_current(events)),
                      "priorCoverage": sum(1 for e in els if e.get("_hasPrior")),
                      "priorMins": PRIOR_MINS, "horizon": HORIZON},
            "chat": chat_spend(),
        },
        "myEntry": entry_id,
        "league": league,
        "standings": [{"rank": r["rank"], "entry": r["entry"], "team": r["entry_name"],
                       "mgr": r["player_name"], "gw": r["event_total"], "total": r["total"],
                       "value": managers[str(r["entry"])]["value"],
                       "bank": managers[str(r["entry"])]["bank"],
                       "chip": managers[str(r["entry"])]["chip"],
                       "chipSpent": picks_gw_done, "chipGw": gw}
                      for r in rows if str(r["entry"]) in managers],
        "managers": managers,
        "players": players,
        "clubs": clubs,
        "allFixtures": [
            {"gw": f.get("event"), "ko": f.get("kickoff_time"),
             "h": f["team_h"], "a": f["team_a"],
             "hs": f.get("team_h_score"), "as": f.get("team_a_score"),
             "fin": is_played(f),
             "prov": bool(f.get("finished_provisional") and not f.get("finished")),
             "hd": f.get("team_h_difficulty"), "ad": f.get("team_a_difficulty")}
            for f in sorted(fixtures, key=lambda x: ((x.get("event") or 99),
                                                     x.get("kickoff_time") or ""))
            if f.get("event")],
        "table": league_table(fixtures, boot["teams"]),
        "odds": {"status": _odds_state.get("status"),
                 "detail": _odds_state.get("detail"),
                 "priced": len(priced), "unmatched": odds_unmatched,
                 "remaining": _odds_state.get("remaining"),
                 "callsThisMonth": _odds_cache["calls"],
                 "perCall": ODDS_CREDITS_PER_CALL,
                 "markets": ODDS_MARKETS,
                 "creditsThisMonth": _odds_cache["calls"] * ODDS_CREDITS_PER_CALL,
                 "maxCalls": ODDS_MAX_CALLS,
                 "fetched": _odds_state.get("fetched"),
                 "ttlHours": round(ODDS_TTL / 3600.0, 1)},
        "strength": {str(k): v for k, v in strength.items() if not str(k).startswith("_")},
        "leagueAvgGoals": round(strength["_avg"], 3),
        "horizon": HORIZON,
        "fixtures": {teams[k]["short_name"]: v for k, v in fixmap.items()},
    }


# ----------------------------------------------------------------------------
# http
# ----------------------------------------------------------------------------
class Handler(BaseHTTPRequestHandler):
    entry_id = ENTRY_ID
    league_id = LEAGUE_ID

    def log_message(self, fmt, *args):
        sys.stderr.write("  %s\n" % (fmt % args))

    def _send(self, code, body, ctype):
        raw = body.encode("utf-8") if isinstance(body, str) else body
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(raw)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        try:
            self.wfile.write(raw)
        except BrokenPipeError:
            pass

    def _authed(self):
        """Optional shared password. Unset -> wide open, which is fine for a
        laptop but not for a public URL."""
        if not PASSWORD:
            return True
        hdr = self.headers.get("Authorization", "")
        if hdr.startswith("Basic "):
            try:
                raw = base64.b64decode(hdr[6:]).decode("utf-8", "replace")
                if raw.split(":", 1)[-1] == PASSWORD:
                    return True
            except Exception:
                pass
        self.send_response(401)
        self.send_header("WWW-Authenticate", 'Basic realm="FPL Dugout"')
        self.send_header("Content-Length", "0")
        self.end_headers()
        return False

    def do_GET(self):
        path = self.path.split("?")[0]
        if path == "/healthz":
            # answers instantly and never touches the FPL API, so a host's
            # health probe cannot be starved by a slow upstream
            return self._send(200, json.dumps({"ok": True}), "application/json")
        if not self._authed():
            return
        if path in ("/", "/index.html"):
            return self._send(200, PAGE, "text/html; charset=utf-8")
        if path == "/api/data":
            try:
                data = build_payload(self.entry_id, self.league_id)
                with _lock:
                    _payload_cache["t"] = time.time()
                    _payload_cache["data"] = data
                return self._send(200, json.dumps(data), "application/json")
            except FPLError as e:
                return self._send(200, json.dumps({"error": str(e)}), "application/json")
            except Exception as e:  # noqa: BLE001 - surface anything to the UI
                return self._send(200, json.dumps(
                    {"error": "%s: %s" % (type(e).__name__, e)}), "application/json")
        if path == "/favicon.ico":
            return self._send(204, b"", "image/x-icon")
        if path == "/api/refresh":
            with _lock:
                _cache.clear()
                _payload_cache["t"] = 0.0
            return self._send(200, json.dumps({"ok": True}), "application/json")
        self._send(404, "not found", "text/plain; charset=utf-8")

    def _payload(self):
        """The chat reuses whatever the interface last rendered rather than
        rebuilding the model on every message, which would add seconds and, on a
        free-tier host, rather more."""
        with _lock:
            hit = _payload_cache["data"]
            fresh = hit is not None and time.time() - _payload_cache["t"] < 300
        if fresh:
            return hit
        data = build_payload(self.entry_id, self.league_id)
        with _lock:
            _payload_cache["t"] = time.time()
            _payload_cache["data"] = data
        return data

    def do_POST(self):
        path = self.path.split("?")[0]
        if not self._authed():
            return
        if path != "/api/chat":
            return self._send(404, "not found", "text/plain; charset=utf-8")
        try:
            n = int(self.headers.get("Content-Length") or 0)
            if n > 200000:
                return self._send(200, json.dumps(
                    {"error": "message too long"}), "application/json")
            req = json.loads(self.rfile.read(n).decode("utf-8") or "{}")
        except Exception as e:                               # noqa: BLE001
            return self._send(200, json.dumps(
                {"error": "bad request (%s)" % e}), "application/json")
        try:
            payload = self._payload()
            entry = req.get("entry") or payload.get("myEntry")
            reply, meta = chat_answer(req.get("messages") or [], entry, payload)
            body = {"reply": reply}
            body.update(meta or {})
            return self._send(200, json.dumps(body), "application/json")
        except Exception as e:                               # noqa: BLE001
            return self._send(200, json.dumps(
                {"error": "%s: %s" % (type(e).__name__, e)}), "application/json")


PAGE = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>FPL Dugout</title>
<link rel="icon" href="data:image/svg+xml,<svg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 32 32'><text y='26' font-size='26'>&#9917;</text></svg>">
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Archivo:wght@600;700;800&family=Barlow:wght@400;500;600&family=IBM+Plex+Mono:wght@400;500;600&display=swap">
<style>
:root{
  --paper:#EFF1F4; --card:#FFFFFF; --sunk:#E4E8ED; --line:#D3D9E1;
  --ink:#0F1319; --ink2:#39424F; --muted:#5C6675;
  --accent:#2F5FD0; --accent-soft:#E2E9FA;
  --good:#1F8A5B; --warn:#C98A16; --bad:#C4453C;
  --good-bg:#DFF0E7; --warn-bg:#F8EDD5; --bad-bg:#F7E0DE;
  --pitch:#1B5340; --pitch2:#1F604A; --chalk:rgba(255,255,255,.24);
  --shadow:0 1px 2px rgba(15,19,25,.06),0 4px 14px rgba(15,19,25,.06); --r:10px;
}
@media (prefers-color-scheme:dark){:root:not([data-theme="light"]){
  --paper:#10141A; --card:#171D26; --sunk:#1E2530; --line:#2A3340;
  --ink:#E8ECF2; --ink2:#B9C3D0; --muted:#8B97A8;
  --accent:#5B8DEF; --accent-soft:#1C2942;
  --good:#3FB27F; --warn:#E0A93A; --bad:#E0685E;
  --good-bg:#12312580; --warn-bg:#33280C80; --bad-bg:#3A1D1B80;
  --pitch:#123B2E; --pitch2:#164837; --chalk:rgba(255,255,255,.18);
  --shadow:0 1px 2px rgba(0,0,0,.4),0 6px 18px rgba(0,0,0,.35);
}}
:root[data-theme="dark"]{
  --paper:#10141A; --card:#171D26; --sunk:#1E2530; --line:#2A3340;
  --ink:#E8ECF2; --ink2:#B9C3D0; --muted:#8B97A8;
  --accent:#5B8DEF; --accent-soft:#1C2942;
  --good:#3FB27F; --warn:#E0A93A; --bad:#E0685E;
  --good-bg:#12312580; --warn-bg:#33280C80; --bad-bg:#3A1D1B80;
  --pitch:#123B2E; --pitch2:#164837; --chalk:rgba(255,255,255,.18);
  --shadow:0 1px 2px rgba(0,0,0,.4),0 6px 18px rgba(0,0,0,.35);
}
*{box-sizing:border-box}
[hidden]{display:none!important}
body{margin:0;background:var(--paper);color:var(--ink);
  font-family:Barlow,"Helvetica Neue",Arial,sans-serif;font-size:15px;line-height:1.5;
  -webkit-font-smoothing:antialiased}
h1,h2,h3,h4{font-family:Archivo,"Helvetica Neue",Arial,sans-serif;margin:0;
  text-wrap:balance;letter-spacing:-.01em}
.mono{font-family:"IBM Plex Mono",ui-monospace,Menlo,monospace;font-variant-numeric:tabular-nums}
.wrap{max-width:1280px;margin:0 auto;padding:0 20px}
:focus-visible{outline:2px solid var(--accent);outline-offset:2px;border-radius:4px}
@media (prefers-reduced-motion:reduce){*{animation:none!important;transition:none!important}}

.top{background:var(--card);border-bottom:1px solid var(--line);position:sticky;top:0;z-index:30}
.topin{display:flex;align-items:center;gap:14px;flex-wrap:wrap;padding:14px 0 11px}
.eyebrow{font-family:"IBM Plex Mono",monospace;font-size:10.5px;letter-spacing:.14em;
  text-transform:uppercase;color:var(--muted)}
h1{font-size:24px;font-weight:800}
.byline{color:var(--muted);font-size:13px}
.spacer{flex:1}
.btn{appearance:none;font-family:Archivo,sans-serif;font-weight:600;font-size:13px;
  background:var(--accent);color:#fff;border:0;border-radius:7px;padding:8px 14px;cursor:pointer}
.btn:hover{filter:brightness(1.08)}
.btn.ghost{background:var(--sunk);color:var(--ink2);border:1px solid var(--line)}
.livedot{display:inline-flex;align-items:center;gap:6px;font-family:"IBM Plex Mono",monospace;
  font-size:10.5px;color:var(--muted)}
.livedot b{width:7px;height:7px;border-radius:50%;background:var(--good);display:block}
.livedot.stale b{background:var(--warn)}
.strip{display:grid;grid-template-columns:repeat(6,1fr);gap:1px;background:var(--line);
  border:1px solid var(--line);border-radius:var(--r);overflow:hidden;margin-bottom:13px}
.tile{background:var(--card);padding:9px 13px 10px}
.tile .k{font-family:"IBM Plex Mono",monospace;font-size:9.5px;letter-spacing:.12em;
  text-transform:uppercase;color:var(--muted);display:block;margin-bottom:2px}
.tile .v{font-family:Archivo,sans-serif;font-weight:700;font-size:20px;letter-spacing:-.02em;
  font-variant-numeric:tabular-nums;display:block;line-height:1.15}
.tile .s{font-size:11.5px;color:var(--muted);font-variant-numeric:tabular-nums}
.tile .v.pos{color:var(--good)} .tile .v.neg{color:var(--bad)}
@media(max-width:900px){.strip{grid-template-columns:repeat(3,1fr)}}
@media(max-width:480px){.strip{grid-template-columns:repeat(2,1fr)}h1{font-size:20px}}
.tabs{display:flex;gap:2px;border-bottom:1px solid var(--line);overflow-x:auto}
.tab{appearance:none;background:none;border:0;border-bottom:2px solid transparent;
  font-family:Archivo,sans-serif;font-weight:600;font-size:14px;color:var(--muted);
  padding:9px 13px;cursor:pointer;margin-bottom:-1px;white-space:nowrap}
.tab:hover{color:var(--ink)}
.tab[aria-selected="true"]{color:var(--accent);border-bottom-color:var(--accent)}
.panel[hidden]{display:none}
main{padding-top:24px}

.msg{border-radius:var(--r);padding:14px 16px;margin-bottom:18px;font-size:14px}
.msg.err{background:var(--bad-bg);border:1px solid var(--bad);color:var(--ink)}
.msg.info{background:var(--warn-bg);border:1px solid var(--warn);color:var(--ink2)}
.loading{display:grid;place-items:center;padding:80px 20px;color:var(--muted);
  font-family:"IBM Plex Mono",monospace;font-size:13px;letter-spacing:.06em}

.squadgrid{display:grid;grid-template-columns:minmax(0,1.05fr) minmax(0,1fr);gap:18px;align-items:start}
@media(max-width:980px){.squadgrid{grid-template-columns:minmax(0,1fr)}}
@media(max-width:430px){
  .chip{width:78px;padding:5px 3px 4px}
  .chip .nm{font-size:11px}
  .pw{width:34px;height:34px}
  .row{gap:5px}
  .wrap{padding:0 13px}
}
.pitch{background:repeating-linear-gradient(180deg,var(--pitch) 0 34px,var(--pitch2) 34px 68px);
  border:1px solid var(--line);border-radius:var(--r);padding:16px 12px 12px;position:relative;
  box-shadow:var(--shadow);overflow:hidden}
.field{position:relative;border:1.5px solid var(--chalk);border-radius:4px;
  padding:26px 7px 4px;margin-bottom:11px}
.field::before{content:"";position:absolute;left:30%;right:30%;top:-1.5px;height:34px;
  border:1.5px solid var(--chalk);border-top:0;border-radius:0 0 4px 4px}
.row{display:flex;justify-content:center;gap:7px;flex-wrap:wrap;position:relative;z-index:2;margin-bottom:12px}
.chipwrap{position:relative}
.chip{appearance:none;background:var(--card);border:1px solid rgba(255,255,255,.5);
  border-radius:8px;padding:6px 4px 5px;width:88px;cursor:pointer;text-align:center;
  display:flex;flex-direction:column;gap:1px;box-shadow:0 2px 6px rgba(0,0,0,.28);
  transition:transform .12s ease}
.chip:hover{transform:translateY(-2px)}
.chip[aria-pressed="true"]{outline:2.5px solid var(--accent);outline-offset:1px}
.chip .nm{font-family:Archivo,sans-serif;font-weight:700;font-size:12px;color:var(--ink);
  white-space:nowrap;overflow:hidden;text-overflow:ellipsis;line-height:1.25}
.chip .meta{font-family:"IBM Plex Mono",monospace;font-size:9px;color:var(--muted);
  font-variant-numeric:tabular-nums;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.chip .bar{height:3px;border-radius:2px;background:var(--sunk);overflow:hidden;margin-top:3px}
.chip .bar i{display:block;height:100%;background:var(--accent);border-radius:2px}
.badge{position:absolute;top:-6px;right:-6px;width:19px;height:19px;border-radius:50%;
  font-family:Archivo,sans-serif;font-weight:800;font-size:10px;display:grid;place-items:center;
  color:#fff;border:1.5px solid var(--card);z-index:3}
.b-c{background:var(--accent)} .b-v{background:var(--muted)}
.flag{position:absolute;top:-6px;left:-6px;width:19px;height:19px;border-radius:50%;
  display:grid;place-items:center;font-size:10px;font-weight:700;color:#fff;z-index:3;
  border:1.5px solid var(--card);background:var(--bad);font-family:Archivo,sans-serif}
.flag.d{background:var(--warn)}
.benchlab{display:flex;align-items:center;gap:9px;margin:4px 0 9px;position:relative;z-index:2}
.benchlab span{font-family:"IBM Plex Mono",monospace;font-size:9.5px;letter-spacing:.14em;
  text-transform:uppercase;color:rgba(255,255,255,.72)}
.benchlab i{flex:1;height:1px;background:var(--chalk)}

.card{background:var(--card);border:1px solid var(--line);border-radius:var(--r);box-shadow:var(--shadow)}
.dt{padding:16px 17px}
.dthead{display:flex;justify-content:space-between;align-items:flex-start;gap:12px;
  border-bottom:1px solid var(--line);padding-bottom:12px;margin-bottom:13px}
.dthead h2{font-size:21px;font-weight:800;line-height:1.15}
.dthead .sub{color:var(--muted);font-size:13px;margin-top:2px}
.scorebox{text-align:right;flex:none}
.scorebox .n{font-family:Archivo,sans-serif;font-weight:800;font-size:26px;line-height:1;
  font-variant-numeric:tabular-nums;color:var(--accent)}
.scorebox .l{font-family:"IBM Plex Mono",monospace;font-size:9px;letter-spacing:.12em;
  text-transform:uppercase;color:var(--muted);margin-top:3px}
.pills{display:flex;gap:6px;flex-wrap:wrap;margin-bottom:13px}
.pill{font-family:"IBM Plex Mono",monospace;font-size:10.5px;padding:3px 8px;border-radius:20px;
  border:1px solid var(--line);color:var(--ink2);background:var(--sunk);white-space:nowrap}
.pill.good{background:var(--good-bg);border-color:var(--good);color:var(--good)}
.pill.warn{background:var(--warn-bg);border-color:var(--warn);color:var(--warn)}
.pill.bad{background:var(--bad-bg);border-color:var(--bad);color:var(--bad)}
.stats{display:grid;grid-template-columns:repeat(4,1fr);gap:1px;background:var(--line);
  border:1px solid var(--line);border-radius:8px;overflow:hidden;margin-bottom:14px}
.st{background:var(--card);padding:8px 9px}
.st .k{font-family:"IBM Plex Mono",monospace;font-size:9px;letter-spacing:.09em;
  text-transform:uppercase;color:var(--muted);display:block}
.st .v{font-family:Archivo,sans-serif;font-weight:700;font-size:16px;
  font-variant-numeric:tabular-nums;display:block;line-height:1.3}
@media(max-width:540px){.stats{grid-template-columns:repeat(3,1fr)}}
.seclab{font-family:"IBM Plex Mono",monospace;font-size:9.5px;letter-spacing:.14em;
  text-transform:uppercase;color:var(--muted);margin:0 0 8px;display:flex;align-items:center;gap:8px}
.seclab i{flex:1;height:1px;background:var(--line)}
.fixrow{display:flex;gap:4px;margin-bottom:15px;overflow-x:auto;padding-bottom:2px}
.fx{flex:1;min-width:56px;border-radius:6px;padding:5px 4px;text-align:center;border:1px solid var(--line)}
.fx .g{display:block;font-family:"IBM Plex Mono",monospace;font-size:8.5px;color:var(--muted);line-height:1.5}
.fx .o{display:block;font-family:Archivo,sans-serif;font-weight:700;font-size:12.5px;line-height:1.35}
.fx .n{display:block;font-family:"IBM Plex Mono",monospace;font-size:9px;font-weight:600;line-height:1.4}
.fdr1,.fdr2{background:var(--good-bg);border-color:var(--good)} .fdr1 .n,.fdr2 .n{color:var(--good)}
.fdr3{background:var(--sunk)} .fdr3 .n{color:var(--ink2)}
.fdr4,.fdr5{background:var(--bad-bg);border-color:var(--bad)} .fdr4 .n,.fdr5 .n{color:var(--bad)}
.tsgrid{display:grid;grid-template-columns:1.15fr 1fr;gap:14px;align-items:start}
@media(max-width:900px){.tsgrid{grid-template-columns:1fr}}
.tsmeta{font-family:"IBM Plex Mono",monospace;font-size:11px;color:var(--muted);margin:-4px 0 12px}
.tsline{display:flex;gap:7px;align-items:center;margin-bottom:8px;flex-wrap:wrap}
.tslab{font-family:"IBM Plex Mono",monospace;font-size:9px;color:var(--muted);width:26px;flex:none}
.tscard{position:relative;flex:1 1 74px;min-width:74px;max-width:104px;background:var(--card);
  border:1px solid var(--line);border-radius:8px;padding:7px 4px 5px;text-align:center;cursor:pointer}
.tscard:hover{border-color:var(--accent)}
.tscard .n{display:block;font-family:Archivo,sans-serif;font-weight:700;font-size:11px;
  line-height:1.25;margin-top:3px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.tscard .x{display:block;font-family:"IBM Plex Mono",monospace;font-size:10.5px;color:var(--accent);font-weight:600}
.capnote{margin-top:12px;padding-top:10px;border-top:1px solid var(--line);font-size:12.5px}
.tsrow{display:flex;gap:9px;align-items:center;padding:7px 0;border-bottom:1px solid var(--line)}
.tsn{flex:1;min-width:0}
.tsn b{display:block;font-size:12.5px}
.tsn small{color:var(--muted);font-family:"IBM Plex Mono",monospace;font-size:9.5px}
.tsx{font-family:"IBM Plex Mono",monospace;font-size:13px;font-weight:600;text-align:right}
.tsx small{display:block;font-size:8px;color:var(--muted);font-weight:400}
.tsord{width:44px;text-align:right;font-family:"IBM Plex Mono",monospace;font-size:12px;color:var(--muted)}
.tsord small{display:block;font-size:8px}
.ccrow{padding:6px 0;font-size:12.5px;border-bottom:1px dashed var(--line)}
.ccrow .vs{color:var(--muted);font-size:10px;margin:0 3px}
.ccrow .gap{float:right;font-family:"IBM Plex Mono",monospace;font-size:10px;color:var(--muted)}
.chipgrid{display:grid;grid-template-columns:1fr 1fr;gap:9px;margin-top:8px}
.chipcard{border:1px solid var(--line);border-radius:8px;padding:9px 10px;background:var(--sunk)}
.chipcard.on{border-color:var(--good);background:var(--good-bg)}
.chipcard b{display:block;font-size:12px}
.chipcard .cv{display:block;font-family:"IBM Plex Mono",monospace;font-size:19px;font-weight:700;margin:2px 0}
.chipcard small{color:var(--muted);font-size:10.5px;line-height:1.4;display:block}
.bmove .up{color:var(--good);font-family:"IBM Plex Mono",monospace;font-size:10px}
.bmove .dn{color:var(--warn);font-family:"IBM Plex Mono",monospace;font-size:10px}
.tsrow{overflow:hidden}
.tsord{width:52px;flex:none;white-space:nowrap}
.tsord small{white-space:nowrap;font-size:7.5px}
.sechead{font-size:17px;margin:22px 0 4px}
.subhead{font-size:13px;margin:16px 0 7px;font-family:"IBM Plex Mono",monospace;
  text-transform:uppercase;letter-spacing:.06em;color:var(--muted);font-weight:600}
.chipused{display:block;margin-top:6px;font-style:normal;font-family:"IBM Plex Mono",monospace;
  font-size:9.5px;color:var(--muted);border-top:1px solid var(--line);padding-top:5px}
.bundle{border:1px solid var(--line);border-radius:9px;padding:11px 12px;margin-bottom:9px;background:var(--card)}
.bundle.realloc{border-color:var(--accent)}
.bhead{display:flex;justify-content:space-between;align-items:baseline;gap:10px;margin-bottom:7px}
.bnet{font-family:"IBM Plex Mono",monospace;font-size:17px;font-weight:700}
.bnet small{display:block;font-size:8.5px;color:var(--muted);font-weight:400;text-align:right}
.bmove{display:grid;grid-template-columns:1fr auto 1fr;gap:8px;align-items:center;
  padding:5px 0;border-top:1px dashed var(--line);font-size:12.5px}
.bmove .ar{color:var(--muted)}
.bsum{margin-top:7px;font-family:"IBM Plex Mono",monospace;font-size:10.5px;color:var(--muted)}
.rtag{display:inline-block;font-family:"IBM Plex Mono",monospace;font-size:8.5px;
  letter-spacing:.06em;text-transform:uppercase;color:var(--accent);border:1px solid var(--accent);
  border-radius:4px;padding:1px 5px;margin-left:6px;vertical-align:2px}
.chatpanel{position:fixed;top:0;right:0;width:min(460px,100vw);height:100vh;z-index:60;
  background:var(--card);border-left:1px solid var(--line);display:flex;flex-direction:column;
  box-shadow:-14px 0 40px rgba(0,0,0,.14)}
.chathead{display:flex;justify-content:space-between;align-items:flex-start;gap:10px;
  padding:13px 14px;border-bottom:1px solid var(--line);flex:none}
.chathead b{display:block;font-size:14px}
.chathead small{display:block;color:var(--muted);font-family:"IBM Plex Mono",monospace;font-size:9.5px;margin-top:2px}
.chatbody{flex:1;overflow-y:auto;padding:13px 14px;display:flex;flex-direction:column;gap:10px}
.cmsg{max-width:100%;font-size:13px;line-height:1.5}
.cmsg.you{align-self:flex-end;background:var(--accent);color:#fff;border-radius:11px 11px 3px 11px;
  padding:8px 11px;max-width:85%;white-space:pre-wrap}
.cmsg.bot{background:var(--sunk);border:1px solid var(--line);border-radius:11px 11px 11px 3px;padding:9px 12px}
.cmsg.bot p{margin:0 0 7px} .cmsg.bot p:last-child{margin:0}
.cmsg.bot code{font-family:"IBM Plex Mono",monospace;font-size:11.5px;background:var(--card);padding:1px 4px;border-radius:3px}
.cmsg.thinking{color:var(--muted);font-style:italic}
.chattbl{border-collapse:collapse;font-size:11.5px;margin:6px 0;width:100%}
.chattbl th{text-align:left;font-family:"IBM Plex Mono",monospace;font-size:9px;text-transform:uppercase;
  letter-spacing:.05em;color:var(--muted);border-bottom:1px solid var(--line);padding:2px 8px 3px 0}
.chattbl td{padding:3px 8px 3px 0;border-bottom:1px solid var(--line)}
.ctool{margin-top:7px;padding-top:6px;border-top:1px dashed var(--line);
  font-family:"IBM Plex Mono",monospace;font-size:9px;color:var(--muted)}
.chatempty p{font-size:12.5px;color:var(--ink2);margin:0 0 11px}
.seeds{display:flex;flex-direction:column;gap:6px}
.seed{text-align:left;background:var(--sunk);border:1px solid var(--line);border-radius:8px;
  padding:8px 10px;font-size:12px;cursor:pointer;font-family:inherit;color:var(--ink)}
.seed:hover{border-color:var(--accent);color:var(--accent)}
.chatform{flex:none;display:flex;gap:7px;padding:11px 14px;border-top:1px solid var(--line);align-items:flex-end}
.chatform textarea{flex:1;resize:none;font:inherit;font-size:13px;padding:8px 10px;border-radius:8px;
  border:1px solid var(--line);background:var(--bg);color:var(--ink)}
.chatform textarea:focus{outline:none;border-color:var(--accent)}
@media(max-width:640px){.chatpanel{width:100vw}}
.spendgrid{display:grid;grid-template-columns:repeat(auto-fit,minmax(130px,1fr));gap:9px;margin:10px 0 6px}
.spendcell{border:1px solid var(--line);border-radius:8px;padding:9px 10px;background:var(--sunk)}
.spendcell b{display:block;font-family:"IBM Plex Mono",monospace;font-size:9px;letter-spacing:.05em;
  text-transform:uppercase;color:var(--muted);font-weight:600}
.spendcell span{display:block;font-family:"IBM Plex Mono",monospace;font-size:19px;font-weight:700;margin-top:3px}
.spendbar{height:7px;border-radius:4px;background:var(--sunk);border:1px solid var(--line);overflow:hidden;margin:4px 0 2px}
.spendbar i{display:block;height:100%;background:var(--accent)}
.mlog{margin-top:12px;padding-top:10px;border-top:1px solid var(--line)}
.mlog h6{font-family:"IBM Plex Mono",monospace;font-size:9px;letter-spacing:.06em;
  text-transform:uppercase;color:var(--muted);margin:0 0 6px;font-weight:600}
table.mltbl{border-collapse:collapse;width:100%;font-size:11.5px}
table.mltbl th{text-align:left;font-family:"IBM Plex Mono",monospace;font-size:8.5px;
  letter-spacing:.05em;text-transform:uppercase;color:var(--muted);font-weight:600;
  padding:0 6px 3px 0;border-bottom:1px solid var(--line)}
table.mltbl th.num,table.mltbl td.num{text-align:right;padding-right:0}
table.mltbl td{padding:4px 6px 4px 0;border-bottom:1px solid var(--line)}
table.mltbl tr.sub td{color:var(--muted)}
table.mltbl td small{font-family:"IBM Plex Mono",monospace;font-size:8.5px;color:var(--muted);margin-left:2px}
table.mltbl td em{font-style:normal;font-family:"IBM Plex Mono",monospace;font-size:8.5px;color:var(--warn)}
.rotrisk{display:inline-block;margin-left:6px;font-family:"IBM Plex Mono",monospace;
  font-size:8.5px;color:var(--warn);border:1px solid var(--warn);border-radius:4px;padding:0 4px}
table.bands{border-collapse:collapse;margin:10px 0 14px;font-size:13px}
table.bands th{text-align:left;font-family:"IBM Plex Mono",monospace;font-size:9.5px;
  letter-spacing:.06em;text-transform:uppercase;color:var(--muted);font-weight:600;
  padding:0 18px 5px 0;border-bottom:1px solid var(--line)}
table.bands td{padding:5px 18px 5px 0;border-bottom:1px solid var(--line);color:var(--ink2)}
.fdrpill{display:inline-block;min-width:20px;text-align:center;padding:1px 5px;margin-right:6px;
  border:1px solid var(--line);border-radius:5px;font-family:"IBM Plex Mono",monospace;
  font-size:11px;font-weight:700;color:var(--ink)}
.fdrpill.fdr1,.fdrpill.fdr2{color:var(--good)} .fdrpill.fdr4,.fdrpill.fdr5{color:var(--bad)}
.alt{display:flex;gap:11px;align-items:flex-start;padding:10px 11px;border:1px solid var(--line);
  border-radius:8px;margin-bottom:7px;background:var(--card);width:100%;text-align:left;
  cursor:pointer;font:inherit;color:inherit}
.alt:hover{border-color:var(--accent);background:var(--accent-soft)}
.alt .d{flex:none;width:54px;text-align:center;font-family:Archivo,sans-serif;font-weight:800;
  font-size:16px;font-variant-numeric:tabular-nums;padding-top:1px}
.alt .d.up{color:var(--good)} .alt .d.dn{color:var(--muted)}
.alt .d small{display:block;font-family:"IBM Plex Mono",monospace;font-size:8px;font-weight:500;
  letter-spacing:.09em;text-transform:uppercase;color:var(--muted)}
.alt .body{flex:1;min-width:0}
.alt .t{font-family:Archivo,sans-serif;font-weight:700;font-size:14px;display:flex;gap:7px;
  align-items:baseline;flex-wrap:wrap}
.alt .t em{font-style:normal;font-family:"IBM Plex Mono",monospace;font-size:11px;
  color:var(--muted);font-weight:500}
.alt .w{font-size:12.5px;color:var(--ink2);margin-top:2px}
.emptynote{color:var(--muted);font-size:13px;padding:8px 0}

.tblwrap{overflow-x:auto;border:1px solid var(--line);border-radius:var(--r);background:var(--card)}
table{border-collapse:collapse;width:100%;font-size:13.5px}
th{font-family:"IBM Plex Mono",monospace;font-size:9.5px;letter-spacing:.11em;
  text-transform:uppercase;color:var(--muted);text-align:left;padding:9px 11px;
  border-bottom:1px solid var(--line);white-space:nowrap;font-weight:600;
  position:sticky;top:0;background:var(--card);z-index:2}
th.sortable{cursor:pointer} th.sortable:hover{color:var(--ink)}
th[aria-sort]{color:var(--accent)}
td{padding:8px 11px;border-bottom:1px solid var(--line);vertical-align:middle}
tbody tr:last-child td{border-bottom:0}
tbody tr.clickable{cursor:pointer} tbody tr.clickable:hover td{background:var(--accent-soft)}
td.num,th.num{text-align:right;font-family:"IBM Plex Mono",monospace;font-variant-numeric:tabular-nums}
tr.me td{background:var(--accent-soft)}
tr.me td:first-child{box-shadow:inset 3px 0 0 var(--accent)}
.pname{font-family:Archivo,sans-serif;font-weight:700}
.dim{color:var(--muted)}
.mgrbtn{appearance:none;background:none;border:0;font:inherit;color:var(--accent);cursor:pointer;
  font-family:Archivo,sans-serif;font-weight:700;padding:0;text-align:left}
.sqdrop{background:var(--sunk);border:1px solid var(--line);border-radius:var(--r);
  padding:13px 14px;margin:10px 0 16px}
.mini{display:flex;gap:6px;flex-wrap:wrap}
.mp{background:var(--card);border:1px solid var(--line);border-radius:6px;padding:4px 8px;
  font-size:12px;display:flex;gap:6px;align-items:baseline}
.mp b{font-family:Archivo,sans-serif;font-weight:700}
.mp em{font-style:normal;font-family:"IBM Plex Mono",monospace;font-size:10px;color:var(--muted)}
.mp.bench{opacity:.6} .mp.shared{border-color:var(--accent)}

.filters{display:flex;gap:9px;flex-wrap:wrap;align-items:flex-end;margin-bottom:14px}
.fgroup{display:flex;flex-direction:column;gap:4px}
.fgroup label{font-family:"IBM Plex Mono",monospace;font-size:9.5px;letter-spacing:.11em;
  text-transform:uppercase;color:var(--muted)}
input[type=search],input[type=number],select{font:inherit;font-size:13.5px;padding:7px 9px;
  border:1px solid var(--line);border-radius:7px;background:var(--card);color:var(--ink);
  min-width:0}
input[type=search]{min-width:210px}
.count{font-family:"IBM Plex Mono",monospace;font-size:11.5px;color:var(--muted);padding-bottom:8px}

.clubgrid{display:grid;grid-template-columns:repeat(auto-fill,minmax(96px,1fr));gap:7px;margin-bottom:18px}
.clubbtn{appearance:none;background:var(--card);border:1px solid var(--line);border-radius:8px;
  padding:9px 6px;cursor:pointer;font:inherit;text-align:center;display:flex;flex-direction:column;gap:2px}
.clubbtn:hover{border-color:var(--accent)}
.clubbtn[aria-pressed="true"]{border-color:var(--accent);background:var(--accent-soft)}
.clubbtn b{font-family:Archivo,sans-serif;font-weight:800;font-size:14px}
.clubbtn em{font-style:normal;font-family:"IBM Plex Mono",monospace;font-size:9.5px;color:var(--muted)}
.clubhead{display:flex;gap:16px;flex-wrap:wrap;align-items:flex-start;
  justify-content:space-between;margin-bottom:14px}
.capgrid{display:grid;grid-template-columns:repeat(auto-fill,minmax(268px,1fr));gap:12px}
.capcard{padding:14px 15px}
.capcard .rank{font-family:"IBM Plex Mono",monospace;font-size:9.5px;letter-spacing:.12em;
  text-transform:uppercase;color:var(--muted)}
.capcard h3{font-size:18px;margin:2px 0 1px}
.capcard .sub{color:var(--muted);font-size:12.5px;margin-bottom:10px}
.capbars{display:flex;flex-direction:column;gap:6px;margin-bottom:10px}
.cb{display:grid;grid-template-columns:74px 1fr 44px;gap:8px;align-items:center;font-size:12px}
.cb span:first-child{font-family:"IBM Plex Mono",monospace;font-size:9.5px;
  letter-spacing:.08em;text-transform:uppercase;color:var(--muted)}
.cb .track{height:7px;background:var(--sunk);border-radius:4px;overflow:hidden}
.cb .track i{display:block;height:100%;border-radius:4px;background:var(--accent)}
.cb .val{font-family:"IBM Plex Mono",monospace;font-variant-numeric:tabular-nums;
  text-align:right;font-size:11.5px}
.two{display:grid;grid-template-columns:1fr 1fr;gap:16px}
@media(max-width:860px){.two{grid-template-columns:1fr}}
.prose{max-width:66ch;color:var(--ink2)}
.prose h3{font-size:16px;color:var(--ink);margin:20px 0 7px}
.prose p{margin:0 0 11px}
.prose ul{margin:0 0 12px;padding-left:19px}
.prose li{margin-bottom:5px}
.prose code{font-family:"IBM Plex Mono",monospace;font-size:12.5px;background:var(--sunk);
  padding:1px 5px;border-radius:4px}
.wbar{display:flex;height:26px;border-radius:6px;overflow:hidden;gap:2px;margin:6px 0 5px}
.wseg{display:grid;place-items:center;font-family:"IBM Plex Mono",monospace;font-size:10.5px;
  font-weight:600;color:#fff}
/* player photos */
.pw{position:relative;display:block;width:40px;height:40px;margin:0 auto 3px;
  border-radius:8px;overflow:hidden;background:var(--sunk);flex:none}
.pw img{width:100%;height:100%;object-fit:cover;object-position:center top;display:block}
.pfb{display:none;position:absolute;inset:0;place-items:center;font-family:Archivo,sans-serif;
  font-weight:800;font-size:13px;color:var(--muted);background:var(--sunk);letter-spacing:-.02em}
.pw.big{width:78px;height:78px;border-radius:10px;margin:0}
.pw.big .pfb{font-size:26px}
.dthead .lead{display:flex;gap:13px;align-items:flex-start;min-width:0}
/* landing picker */
.pickwrap{max-width:780px;margin:22px auto 60px}
.pickwrap h2{font-size:25px;margin-bottom:5px}
.pickwrap .lede{color:var(--muted);margin-bottom:18px;font-size:14px}
.pickgrid{display:grid;grid-template-columns:repeat(auto-fill,minmax(236px,1fr));gap:9px}
.pickcard{appearance:none;text-align:left;background:var(--card);border:1px solid var(--line);
  border-radius:var(--r);padding:12px 14px;cursor:pointer;font:inherit;color:inherit;
  display:flex;gap:11px;align-items:center;box-shadow:var(--shadow)}
.pickcard:hover{border-color:var(--accent);background:var(--accent-soft)}
.pickcard .pos{font-family:Archivo,sans-serif;font-weight:800;font-size:18px;color:var(--muted);
  width:24px;flex:none;text-align:center;font-variant-numeric:tabular-nums}
.pickcard .who b{font-family:Archivo,sans-serif;font-weight:700;font-size:15px;display:block;
  line-height:1.25}
.pickcard .who em{font-style:normal;color:var(--muted);font-size:12.5px;display:block}
.pickcard .pts{margin-left:auto;font-family:"IBM Plex Mono",monospace;font-weight:600;
  font-variant-numeric:tabular-nums;text-align:right;font-size:13px;flex:none}
.viewbar{display:flex;align-items:center;gap:9px;font-size:13px;color:var(--muted)}
.viewbar b{font-family:Archivo,sans-serif;font-weight:700;color:var(--ink);font-size:14px}
.pitchhead{display:flex;justify-content:space-between;align-items:baseline;gap:10px;
  margin-bottom:11px;flex-wrap:wrap;position:relative;z-index:2}
.pitchhead h3{color:#fff;font-size:16px;letter-spacing:-.01em}
.pitchhead .meta{font-family:"IBM Plex Mono",monospace;font-size:10.5px;
  color:rgba(255,255,255,.78);letter-spacing:.04em;font-variant-numeric:tabular-nums}
/* club badges */
.bw{display:inline-flex;align-items:center;justify-content:center;width:26px;height:26px;flex:none}
.bw img{width:100%;height:100%;object-fit:contain;display:block}
.bw.lg{width:44px;height:44px}
.bfb{display:none;font-family:Archivo,sans-serif;font-weight:800;font-size:10px;color:var(--muted)}
.bw.lg .bfb{font-size:14px}
.clubbtn .bw{margin:0 auto 3px}
.clubtitle{display:flex;gap:12px;align-items:center}
/* alternatives: the ? explainer */
.altrow{position:relative;margin-bottom:7px}
.altrow .alt{margin-bottom:0;padding-right:46px}
.qmark{position:absolute;right:9px;bottom:9px;width:24px;height:24px;border-radius:6px;
  border:1px solid var(--line);background:var(--sunk);color:var(--muted);cursor:pointer;
  font-family:Archivo,sans-serif;font-weight:800;font-size:12px;line-height:1;
  display:grid;place-items:center;padding:0}
.qmark:hover{border-color:var(--accent);color:var(--accent);background:var(--accent-soft)}
.qmark[aria-expanded="true"]{background:var(--accent);color:#fff;border-color:var(--accent)}
.explain{border:1px solid var(--accent);border-top:0;border-radius:0 0 8px 8px;
  background:var(--accent-soft);padding:11px 13px;margin-top:-1px}
.explain h5{font-family:"IBM Plex Mono",monospace;font-size:9.5px;letter-spacing:.12em;
  text-transform:uppercase;color:var(--muted);margin:0 0 7px;font-weight:600}
table.calc{width:100%;font-size:12.5px;border-collapse:collapse;margin-bottom:8px}
table.calc td{padding:2px 0;border:0;font-variant-numeric:tabular-nums}
table.calc td:first-child{color:var(--ink2)}
table.calc td.n{text-align:right;font-family:"IBM Plex Mono",monospace;width:96px;
  color:var(--muted);white-space:nowrap;font-size:11.5px}
table.calc td.r{text-align:right;font-family:"IBM Plex Mono",monospace;width:62px;font-weight:600}
table.calc tr.sum td{border-top:1px solid var(--line);padding-top:4px}
table.calc tr.tot td{font-family:Archivo,sans-serif;font-weight:800;color:var(--ink);
  border-top:1px solid var(--line);padding-top:4px}
.explain p{margin:0;font-size:12.5px;color:var(--ink2)}
/* players tab: inline expansion */
tr.exp td{background:var(--sunk);padding:0}
.expbox{padding:14px 15px}
.expgrid{display:grid;grid-template-columns:auto 1fr;gap:14px;align-items:start;margin-bottom:12px}
.expname h3{font-size:19px;line-height:1.2}
.expname .sub{color:var(--muted);font-size:13px;margin-top:1px}
.exptwo{display:grid;grid-template-columns:1fr 1fr;gap:16px;align-items:start}
@media(max-width:900px){.exptwo{grid-template-columns:1fr}}
tbody tr.open td{background:var(--accent-soft)}
.chev{display:inline-block;width:9px;color:var(--muted);font-size:10px}
/* transfers */
.tcard{position:relative;background:var(--card);border:1px solid var(--line);
  border-radius:var(--r);padding:13px 15px;margin-bottom:9px;box-shadow:var(--shadow)}
.tmove{display:flex;align-items:center;gap:11px;flex-wrap:wrap;margin-bottom:10px}
.tside{display:flex;align-items:center;gap:9px;min-width:0}
.tside .nm{font-family:Archivo,sans-serif;font-weight:700;font-size:15px;line-height:1.2}
.tside .sub{font-family:"IBM Plex Mono",monospace;font-size:10.5px;color:var(--muted)}
.tside.out .nm{color:var(--muted)}
.tarrow{font-family:Archivo,sans-serif;font-weight:800;color:var(--accent);font-size:18px;flex:none}
.tgain{margin-left:auto;text-align:right;flex:none;padding-right:30px}
.tgain b{font-family:Archivo,sans-serif;font-weight:800;font-size:22px;color:var(--good);
  font-variant-numeric:tabular-nums;display:block;line-height:1}
.tgain span{font-family:"IBM Plex Mono",monospace;font-size:8.5px;letter-spacing:.1em;
  text-transform:uppercase;color:var(--muted)}
.tmeta{display:flex;gap:6px;flex-wrap:wrap;margin-bottom:10px}
.tfix{display:grid;grid-template-columns:1fr 1fr;gap:14px}
@media(max-width:780px){.tfix{grid-template-columns:1fr}}
.tfix h6{font-family:"IBM Plex Mono",monospace;font-size:9px;letter-spacing:.12em;
  text-transform:uppercase;color:var(--muted);margin:0 0 5px;font-weight:600}
.tfix .fixrow{margin-bottom:0}
.tcard .qmark{top:13px;bottom:auto}
.tcard .explain{margin-top:11px;border-radius:8px;border-top-width:1px}
/* league table */
.formrow{display:flex;gap:3px}
.fchip{width:17px;height:17px;border-radius:4px;display:grid;place-items:center;
  font-family:Archivo,sans-serif;font-weight:800;font-size:9.5px;color:#fff}
.fW{background:var(--good)} .fD{background:var(--muted)} .fL{background:var(--bad)}
.clubcell{display:flex;align-items:center;gap:9px}
.clubcell .bw{width:22px;height:22px}
.capcard .caphead{display:flex;gap:11px;align-items:center;margin-bottom:9px}
.capcard .caphead .pw{margin:0}
/* orientation line at the top of every tab */
.tabintro{color:var(--muted);font-size:13.5px;margin:4px 0 18px;max-width:78ch;line-height:1.55}
.tabintro b{color:var(--ink2);font-weight:600}
/* home */
.hero{background:var(--card);border:1px solid var(--line);border-radius:var(--r);
  padding:18px 20px;margin-bottom:14px;box-shadow:var(--shadow);
  display:flex;gap:18px;align-items:baseline;flex-wrap:wrap}
.hero h2{font-size:23px;line-height:1.15}
.hero .when{font-family:"IBM Plex Mono",monospace;font-size:12.5px;color:var(--muted)}
.hero .standing{margin-left:auto;font-size:13.5px;color:var(--ink2)}
.hero .standing b{font-family:Archivo,sans-serif;font-size:17px;color:var(--ink)}
.acts{display:grid;grid-template-columns:repeat(auto-fit,minmax(310px,1fr));gap:12px}
.act{background:var(--card);border:1px solid var(--line);border-radius:var(--r);
  padding:15px 17px;box-shadow:var(--shadow);display:flex;flex-direction:column}
.act .kicker{font-family:"IBM Plex Mono",monospace;font-size:9.5px;letter-spacing:.13em;
  text-transform:uppercase;color:var(--accent);margin-bottom:7px;font-weight:600}
.act h3{font-size:17px;line-height:1.25;margin-bottom:5px}
.act .body{font-size:13.5px;color:var(--ink2);flex:1;margin-bottom:12px}
.act .faces{display:flex;align-items:center;gap:9px;margin-bottom:9px}
.act .faces .pw{margin:0;width:34px;height:34px}
.act .arrow{color:var(--accent);font-family:Archivo,sans-serif;font-weight:800}
.act .go{align-self:flex-start;appearance:none;background:var(--sunk);border:1px solid var(--line);
  border-radius:7px;padding:7px 12px;font-family:Archivo,sans-serif;font-weight:600;
  font-size:13px;color:var(--accent);cursor:pointer}
.act .go:hover{background:var(--accent-soft);border-color:var(--accent)}
.act.warn{border-color:var(--warn)}
.act.warn .kicker{color:var(--warn)}
.act.calm{border-color:var(--good)}
.act.calm .kicker{color:var(--good)}
.flaglist{list-style:none;margin:0;padding:0}
.flaglist li{padding:5px 0;border-bottom:1px solid var(--line);font-size:13.5px}
.flaglist li:last-child{border-bottom:0}
.flaglist b{font-family:Archivo,sans-serif}
/* fixtures */
.gwbar{display:flex;align-items:center;gap:10px;margin-bottom:12px;flex-wrap:wrap}
.gwbar .nav{appearance:none;width:32px;height:32px;border-radius:7px;border:1px solid var(--line);
  background:var(--card);cursor:pointer;font-size:14px;color:var(--ink2);display:grid;place-items:center}
.gwbar .nav:hover{border-color:var(--accent);color:var(--accent)}
.gwbar .nav[disabled]{opacity:.35;cursor:default}
.gwbar .lbl{font-family:Archivo,sans-serif;font-weight:800;font-size:17px;min-width:118px}
.gwbar .sub{font-family:"IBM Plex Mono",monospace;font-size:11px;color:var(--muted)}
.fixlist{display:grid;grid-template-columns:repeat(auto-fill,minmax(290px,1fr));gap:8px;
  margin-bottom:20px}
.fxrow{background:var(--card);border:1px solid var(--line);border-radius:8px;padding:9px 12px;
  display:flex;align-items:center;gap:9px;font-size:13.5px}
.fxrow .side{display:flex;align-items:center;gap:7px;flex:1;min-width:0}
.fxrow .side.away{flex-direction:row-reverse;text-align:right}
.fxrow .side .bw{width:20px;height:20px}
.fxrow .side b{font-family:Archivo,sans-serif;font-weight:700;white-space:nowrap;
  overflow:hidden;text-overflow:ellipsis}
.fxrow .mid{font-family:"IBM Plex Mono",monospace;font-variant-numeric:tabular-nums;
  font-weight:600;flex:none;text-align:center;min-width:56px}
.fxrow .mid small{display:block;font-size:9.5px;font-weight:400;color:var(--muted)}
.fxrow.done .mid{font-size:15px}
/* fixtures priced by the betting market carry a top edge */
.fx.mkt{box-shadow:inset 0 2.5px 0 var(--accent)}
.oddsbadge{display:inline-flex;align-items:center;gap:5px;font-family:"IBM Plex Mono",monospace;
  font-size:10px;letter-spacing:.1em;text-transform:uppercase;color:var(--accent);
  background:var(--accent-soft);border:1px solid var(--accent);border-radius:20px;
  padding:2px 8px}
.oddsbadge.off{color:var(--muted);background:var(--sunk);border-color:var(--line)}
footer{color:var(--muted);font-size:12.5px;padding:24px 0 34px;border-top:1px solid var(--line);margin-top:28px}
</style>
</head>
<body>
<div class="top">
  <div class="wrap">
    <div class="topin">
      <div>
        <div class="eyebrow" id="eyebrow">Fantasy Premier League</div>
        <h1 id="teamname">FPL Dugout</h1>
      </div>
      <div class="byline" id="byline"></div>
      <span class="spacer"></span>
      <span class="viewbar" id="viewbar" hidden>viewing <b id="viewname"></b>
        <button class="btn ghost" id="changeteam" type="button">Change</button></span>
      <span class="livedot" id="livedot"></span>
      <button class="btn ghost" id="chatbtn" type="button"
        title="Ask a question about this squad">Ask</button>
      <button class="btn ghost" id="refresh" type="button">Refresh</button>
    </div>
    <div class="strip" id="strip"></div>
    <div class="tabs" role="tablist" id="tabs">
      <button class="tab" role="tab" aria-selected="true" data-p="home"
        title="What to do this week, at a glance">Home</button>
      <button class="tab" role="tab" aria-selected="false" data-p="squad"
        title="Your squad on the pitch. Click any player for his stats and who could replace him.">My Team</button>
      <button class="tab" role="tab" aria-selected="false" data-p="sheet"
        title="Who should start this weekend, who sits, and who takes the armband">Team Sheet</button>
      <button class="tab" role="tab" aria-selected="false" data-p="tx"
        title="Single swaps and multi-transfer bundles, scored on the eleven that would actually play">Transfers</button>
      <button class="tab" role="tab" aria-selected="false" data-p="clubs"
        title="League table, all fixtures, and every club's players">Clubs &amp; Fixtures</button>
      <button class="tab" role="tab" aria-selected="false" data-p="players"
        title="Search and compare every player in the game">Players</button>
      <button class="tab" role="tab" aria-selected="false" data-p="cap"
        title="Who to give the armband to this week">Captain</button>
      <button class="tab" role="tab" aria-selected="false" data-p="league"
        title="Your mini-league table, everyone's teams, and who owns what">My League</button>
      <button class="tab" role="tab" aria-selected="false" data-p="model"
        title="How the ratings are worked out, in plain English">How it works</button>
    </div>
  </div>
</div>
<main class="wrap">
  <div id="boot" class="loading">Fetching live data from the FPL API...</div>
  <div id="app" hidden>
    <div id="banner"></div>
    <aside class="chatpanel" id="chatpanel" hidden></aside>
    <section id="picker" hidden></section>
    <section class="panel" id="p-home"></section>
    <section class="panel" id="p-squad" hidden>
      <div id="squadintro"></div>
      <div class="squadgrid">
        <div><div class="pitch" id="pitch"></div></div>
        <div class="card dt" id="detail"></div>
      </div>
    </section>
    <section class="panel" id="p-sheet" hidden></section>
    <section class="panel" id="p-tx" hidden></section>
    <section class="panel" id="p-clubs" hidden></section>
    <section class="panel" id="p-players" hidden></section>
    <section class="panel" id="p-cap" hidden></section>
    <section class="panel" id="p-league" hidden></section>
    <section class="panel" id="p-model" hidden></section>
  </div>
  <footer id="foot"></footer>
</main>
<script>
(function(){
"use strict";
var TABS=["home","squad","sheet","tx","clubs","players","cap","league","model"];
var D=null, byId={}, viewEntry=null, curClub=null, gwView=null,
    sortKey="score", sortDir=-1, openPlayer=null;

function $(s,r){return (r||document).querySelector(s)}
function all(s,r){return Array.prototype.slice.call((r||document).querySelectorAll(s))}
function esc(s){return String(s==null?"":s).replace(/[&<>"']/g,function(c){
  return {"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]})}
function m(x){return "£"+Number(x).toFixed(1)+"m"}
function fdrCls(f){return "fdr"+(f==null?3:f)}
function M(){return D.managers[String(viewEntry)]}
function P(id){return byId[id]}
function squadOf(){
  var mm=M(); if(!mm) return [];
  return mm.picks.map(function(pk){
    var base=P(pk.id)||{}, o={};
    for(var k in base) o[k]=base[k];
    for(var k2 in pk) o[k2]=pk[k2];
    return o;
  });
}
function inSquad(id){
  var mm=M(); if(!mm) return null;
  for(var i=0;i<mm.picks.length;i++) if(mm.picks[i].id===id) return mm.picks[i];
  return null;
}

/* ---------------- images with graceful fallback ---------------- */
var PHOTO="https://resources.premierleague.com/premierleague/photos/players/";
var BADGE="https://resources.premierleague.com/premierleague/badges/70/t";
function initials(nm){
  var parts=String(nm||"").replace(/[^A-Za-zÀ-ɏ .'-]/g,"").split(/[ .'-]+/).filter(Boolean);
  if(!parts.length) return "?";
  return (parts[0].charAt(0)+(parts.length>1?parts[parts.length-1].charAt(0):"")).toUpperCase();
}
function photoHTML(p,big){
  var cls="pw"+(big?" big":"");
  if(!p||!p.code) return '<span class="'+cls+'"><span class="pfb imgfb" style="display:grid">'+
    esc(initials(p&&p.name))+'</span></span>';
  return '<span class="'+cls+'"><img class="fbimg" src="'+PHOTO+(big?"250x250":"110x140")+
    '/p'+p.code+'.png" alt=""><span class="pfb imgfb">'+esc(initials(p.name))+'</span></span>';
}
function badgeHTML(code,short,lg){
  // the club's name always sits next to the badge, so the no-image fallback is a single
  // letter rather than the code -- otherwise it reads as "ARSARS"
  var cls="bw"+(lg?" lg":"");
  var fb=esc(String(short||"?").charAt(0));
  if(!code) return '<span class="'+cls+'"><span class="bfb imgfb" style="display:block" '+
    'title="'+esc(short)+'">'+fb+'</span></span>';
  return '<span class="'+cls+'"><img class="fbimg" src="'+BADGE+code+'.png" alt="">'+
    '<span class="bfb imgfb" title="'+esc(short)+'">'+fb+'</span></span>';
}
function wireImgs(root){
  all("img.fbimg",root||document).forEach(function(im){
    if(im.getAttribute("data-wired")) return;
    im.setAttribute("data-wired","1");
    function fail(){
      im.style.display="none";
      var fb=im.nextElementSibling;
      if(fb&&fb.className.indexOf("imgfb")>=0)
        fb.style.display=fb.className.indexOf("pfb")>=0?"grid":"block";
    }
    im.addEventListener("error",fail);
    if(im.complete&&im.naturalWidth===0) fail();
    setTimeout(function(){ if(!im.complete||im.naturalWidth===0) fail(); },6000);
  });
}

/* ---------------- load ---------------- */
function load(){
  $("#boot").hidden=false;
  $("#boot").textContent="Fetching live data from the FPL API...";
  $("#app").hidden=true;
  fetch("/api/data",{cache:"no-store"}).then(function(r){return r.json()}).then(function(d){
    if(d.error){
      $("#boot").innerHTML='<div class="msg err" style="white-space:pre-wrap">'+
        '<b>Could not load data.</b><br>'+esc(d.error)+
        '<br><br>The app is running fine — this is the FPL API not answering. '+
        'Wait a moment and press Refresh.</div>';
      return;
    }
    D=d; byId={};
    D.players.forEach(function(p){byId[p.id]=p});
    bootUI();
    $("#boot").hidden=true; $("#app").hidden=false;
  }).catch(function(e){
    $("#boot").innerHTML='<div class="msg err"><b>Request failed.</b><br>'+esc(e.message)+'</div>';
  });
}

/* ---------------- shared pieces ---------------- */
function fixStrip(short,n){
  var f=D.fixtures[short]; if(!f) return "";
  var runs=f.runs;
  if(n){
    var gws=[]; runs.forEach(function(r){if(gws.indexOf(r.gw)<0) gws.push(r.gw)});
    gws=gws.sort(function(a,b){return a-b}).slice(0,n);
    runs=runs.filter(function(r){return gws.indexOf(r.gw)>=0});
  }
  return '<div class="fixrow">'+runs.map(function(r){
    if(!r.opp) return '<div class="fx fdr3"><span class="g">GW'+r.gw+'</span>'+
      '<span class="o">—</span><span class="n">no game</span></div>';
    var mkt=r.src==="odds";
    var eg=function(x){return x==null?'?':(x>0?'+':'')+x.toFixed(2)};
    var tip = mkt
      ? ('BETTING MARKET (in use): win chance minus lose chance '+eg(r.edge)+
         ' → difficulty '+r.fdr+
         '\nExpected goals '+(r.xgf==null?'?':r.xgf.toFixed(2))+
         ', clean sheet '+(r.cs==null?'?':Math.round(r.cs*100)+'%')+
         '\nResults model would say: edge '+eg(r.altEdge)+', difficulty '+
         (r.altFdr==null?'?':r.altFdr)+' ('+(r.altXgf==null?'?':r.altXgf.toFixed(2))+
         ' goals, '+(r.altCs==null?'?':Math.round(r.altCs*100)+'%')+' clean sheet)')
      : ('RESULTS MODEL (in use): win chance minus lose chance '+eg(r.edge)+
         ' → difficulty '+r.fdr+
         '\nExpected goals '+(r.xgf==null?'?':r.xgf.toFixed(2))+
         ', clean sheet '+(r.cs==null?'?':Math.round(r.cs*100)+'%')+
         '\nNot priced by the market yet');
    if(r.fplFdr!=null) tip += '\nFPL’s own pre-season rating: '+r.fplFdr+
      (r.fplFdr===r.fdr?' (agrees)':' (differs)');
    return '<div class="fx '+fdrCls(r.fdr)+(mkt?' mkt':'')+'" title="'+esc(tip)+'">'+
      '<span class="g">GW'+r.gw+' '+r.ha+'</span>'+
      '<span class="o">'+esc(r.opp)+'</span><span class="n">Diff '+r.fdr+'</span></div>'
  }).join("")+'</div>';
}
function matchLog(p){
  var L=p.log||[];
  if(!L.length) return '<div class="mlog"><h6>Recent matches</h6>'+
    '<p class="dim" style="font-size:11.5px;margin:0">No minutes in the last '+
    (((D.meta.model||{}).formGws||[]).length||6)+' gameweeks.</p></div>';
  return '<div class="mlog"><h6>Recent matches</h6><table class="mltbl"><thead><tr>'+
    '<th>GW</th><th>Opp</th><th class="num">Min</th><th class="num">Pts</th>'+
    '<th class="num">G</th><th class="num">A</th><th class="num">BPS</th>'+
    '<th class="num">Def</th></tr></thead><tbody>'+
    L.slice().reverse().map(function(r){
      return '<tr'+(r[4]?'':' class="sub"')+'><td>'+r[0]+'</td><td><b>'+esc(r[1])+'</b>'+
        '<small>'+r[2]+'</small>'+(r[4]?'':'<em title="Came off the bench"> sub</em>')+
        '</td><td class="num">'+r[3]+'</td><td class="num"><b>'+r[5]+'</b></td>'+
        '<td class="num">'+(r[6]||"")+'</td><td class="num">'+(r[7]||"")+'</td>'+
        '<td class="num">'+r[10]+'</td><td class="num">'+r[11]+'</td></tr>';
    }).join("")+'</tbody></table></div>';
}
function statGrid(p){
  var rows=[["Pts",p.pts],["Mins",p.mins],["Starts",p.starts],
    ["Last 3",p.form3==null?"—":p.form3.toFixed(1)],
    ["Last 5",p.form5==null?"—":p.form5.toFixed(1)],
    ["Pts/game",p.ppg.toFixed(1)],
    ["Exp. mins",p.expMins==null?"—":p.expMins],
    ["Starts XI",p.pStart==null?"—":Math.round(p.pStart*100)+"%"],
    ["Goals",p.goals],["Assists",p.assists],["Bonus",p.bonus],
    ["xG",p.xg.toFixed(2)],["xA",p.xa.toFixed(2)],["xGI/90",p.xgi90.toFixed(2)],
    ["Def. hit rate",p.dcHit==null?"—":Math.round(p.dcHit*100)+"%"],
    ["Clean sheet",p.csNext==null?"—":Math.round(p.csNext*100)+"%"],
    ["ICT",p.ict],["BPS",p.bps],["Owned",p.owned+"%"]];
  return '<div class="stats">'+rows.map(function(r){
    return '<div class="st"><span class="k">'+esc(r[0])+'</span><span class="v">'+
      esc(r[1])+'</span></div>'}).join("")+'</div>'+matchLog(p);
}
function pillsFor(p){
  var o=[];
  if(p.status!=="a") o.push('<span class="pill '+(p.status==="d"?"warn":"bad")+'">'+
    esc(p.news||"unavailable")+'</span>');
  if(p.pStart!=null) o.push('<span class="pill'+(p.pStart>=0.85?" good":p.pStart<0.6?" bad":" warn")+
    '" title="Chance of being in the starting eleven, from recent team sheets, last '+
    'season\u2019s start rate and FPL\u2019s availability flag. It cannot see press '+
    'conferences.">'+Math.round(p.pStart*100)+'% to start'+
    (p.startWhy?' · '+esc(p.startWhy):'')+'</span>');
  if(p.pen===1) o.push('<span class="pill good">Penalties · 1st</span>');
  else if(p.pen===2) o.push('<span class="pill">Penalties · 2nd</span>');
  if(p.ck===1) o.push('<span class="pill">Corners · 1st</span>');
  if(p.fk===1) o.push('<span class="pill">Free-kicks · 1st</span>');
  if(p.avgFdr!=null) o.push('<span class="pill'+(p.avgFdr<=2.6?" good":p.avgFdr>=3.4?" bad":"")+
    '" title="Average difficulty of the next six matches. 3.00 means a run of coin tosses; below that is kind, above it is hard.">Next 6 · difficulty '+p.avgFdr.toFixed(2)+'</span>');
  if(p.owned<=5) o.push('<span class="pill">Differential · '+p.owned+'% owned</span>');
  if(p.costChange!==0) o.push('<span class="pill">Price '+(p.costChange>0?"+":"")+
    (p.costChange/10).toFixed(1)+'m since start</span>');
  if(inSquad(p.id)) o.push('<span class="pill good">In this squad</span>');
  return o.length?'<div class="pills">'+o.join("")+'</div>':"";
}

/* ---------------- the score, explained ---------------- */
function obsSentence(p){
  var hit=p.dcHit==null?"not enough matches yet":Math.round(p.dcHit*100)+"% of matches";
  var f=p.expl.form.toFixed(2);
  if(p.pos==="GK") return "For keepers: 55% recent scoring rate ("+f+
    " points a game, weighted toward the last three) and 45% ICT.";
  if(p.pos==="DEF") return "For defenders: 35% recent scoring rate ("+f+
    " a game), 35% how often he clears the defensive threshold ("+hit+
    ") and 30% attacking threat ("+p.xgi90.toFixed(2)+" goals+assists expected per 90).";
  if(p.pos==="MID") return "For midfielders: 40% goals+assists expected per 90 ("+
    p.xgi90.toFixed(2)+"), 30% recent scoring rate ("+f+
    " a game) and 30% how often he clears the defensive threshold ("+hit+").";
  return "For forwards: 55% goals+assists expected per 90 ("+p.xgi90.toFixed(2)+
    ") and 45% recent scoring rate ("+f+" a game).";
}
function oddsNote(){
  var o=D.odds||{};
  if(o.status==="on"&&o.priced)
    return " "+o.priced+" of the coming fixtures are priced by the betting market, and "+
      "those use the market's numbers instead — fixtures with a blue top edge.";
  if(o.status==="error")
    return " Betting odds are configured but unavailable right now ("+esc(o.detail||"")+
      "), so every fixture is using results.";
  return "";
}
function fixSentence(p){
  if(p.pos==="GK"||p.pos==="DEF")
    return "Because clean sheets are what pays at the back, the fixture term is his chance "+
      "of keeping one across the next six — "+
      (p.csNext==null?"not yet computed":Math.round(p.csNext*100)+"%")+
      " on average, from a Poisson model of both clubs\u2019 records so far."+oddsNote();
  return "Because goals are what pays further forward, the fixture term is how many goals "+
    "his side is expected to score across the next six — "+
    (p.xgfNext==null?"not yet computed":p.xgfNext.toFixed(2)+" a game")+
    ", from both clubs\u2019 records so far plus home advantage."+oddsNote();
}
function explainHTML(p){
  var w=D.meta.model, x=p.expl;
  var a=100*w.wPrior*x.prior, b=100*w.wObs*x.obs, c=100*w.wFix*x.fix;
  var sub=a+b+c, av=sub*x.avail, mn=av*x.minfac, tot=mn+x.sp;
  function row(lab,inp,res,cls){
    return '<tr'+(cls?' class="'+cls+'"':'')+'><td>'+lab+'</td><td class="n">'+inp+
      '</td><td class="r">'+res+'</td></tr>';
  }
  var h='<h5>How this score was built</h5><table class="calc">';
  h+=row("Price signal",x.prior.toFixed(2)+" × "+Math.round(w.wPrior*100)+"%",a.toFixed(1));
  h+=row("Recent form",x.obs.toFixed(2)+" × "+Math.round(w.wObs*100)+"%",b.toFixed(1));
  h+=row("Fixtures",x.fix.toFixed(2)+" × "+Math.round(w.wFix*100)+"%",c.toFixed(1));
  h+=row("Subtotal","",sub.toFixed(1),"sum");
  h+=row("× availability","× "+x.avail.toFixed(2),av.toFixed(1));
  h+=row("× minutes played","× "+x.minfac.toFixed(2),mn.toFixed(1));
  h+=row("+ set pieces","+ "+x.sp.toFixed(1),tot.toFixed(1));
  h+=row("Expected points","",Number(tot).toFixed(1),"tot");
  var mp=(D.meta.model.matchesPlayed||0);
  h+='</table><p><b>Price signal '+x.prior.toFixed(2)+'</b> means he is priced above '+
    Math.round(x.prior*100)+'% of '+esc(p.pos)+'s. Price is the market\u2019s season-long '+
    'estimate and the steadiest thing available early, so it starts at 55% of the score and '+
    'falls to 20% by the seventh round. '+mp+' round'+(mp===1?' has':'s have')+' been played, so '+
    'it currently carries '+Math.round(D.meta.model.wPrior*100)+'%. '+
    '<b>Recent form '+x.obs.toFixed(2)+'</b> is where he ranks against others in his '+
    'position. '+esc(obsSentence(p))+' <b>Fixtures '+x.fix.toFixed(2)+'</b>: '+
    esc(fixSentence(p));
  if(x.avail<1) h+=' Availability is below 1.00 because he is flagged, which scales the whole '+
    'score down.';
  if(x.minfac<1) h+=' Minutes security is '+x.minfac.toFixed(2)+
    (p.expMins!=null?', from an expected '+p.expMins+' minutes based on his recent matches'
                    :', because he has barely played')+'.';
  if(x.sp>0) h+=' The set-piece bonus of '+x.sp.toFixed(1)+' is added flat, after the multipliers.';
  h+='</p>';
  return h;
}

/* ---------------- My Team ---------------- */
function altBlock(o,ownerLabel){
  var p=P(o.id), up=o.delta>0;
  return '<div class="altrow"><button class="alt" data-look="'+o.id+'">'+
    '<span class="d '+(up?"up":"dn")+'">'+(up?"+":"")+o.delta.toFixed(1)+
    '<small>rating</small></span><span class="body"><span class="t">'+esc(p.name)+
    ' <em>'+esc(p.club)+' · '+m(p.price)+(o.spare>0?' · '+m(o.spare)+' left':'')+
    '</em></span><span class="w">'+esc(plainWhy(o.why||[]).join(" · ")||"rated higher overall")+
    '</span></span></button>'+
    '<button class="qmark" data-explain="'+o.id+'" aria-expanded="false" '+
    'title="How this score was calculated" aria-label="Explain the score for '+esc(p.name)+'">?</button>'+
    '<div class="explain" id="ex-'+o.id+'" hidden></div></div>';
}
function detailFor(id){
  var pk=inSquad(id), p=P(id); if(!p) return;
  var mm=M();
  var h='<div class="dthead"><div class="lead">'+photoHTML(p,true)+
    '<div style="min-width:0"><h2>'+esc(p.full||p.name)+'</h2>'+
    '<div class="sub">'+esc(p.clubFull)+' · '+esc(p.pos)+' · '+m(p.price)+
    (pk?' · sells for '+m(pk.sell):'')+'</div></div></div>'+
    '<div class="scorebox"><div class="n">'+Number(p.score).toFixed(1)+'</div>'+
    '<div class="l">xPts next '+D.horizon+'</div></div></div>';
  h+=pillsFor(p)+statGrid(p);
  h+='<h4 class="seclab">Next six fixtures<i></i></h4>'+fixStrip(p.club);
  if(pk&&pk.alts){
    h+='<h4 class="seclab">Alternatives for '+esc(mm.team)+' within '+m(pk.alts.budget)+
      '<i></i></h4>';
    h+=pk.alts.options.length? pk.alts.options.map(function(o){return altBlock(o)}).join("")
      : '<p class="emptynote">No affordable, available replacement in this position.</p>';
  } else {
    h+='<h4 class="seclab">Transfer options<i></i></h4><p class="emptynote">'+
      esc(p.name)+' is not in '+esc(mm.team)+'’s squad, so there is no slot to swap out. '+
      'Open one of their players to see replacements costed against their bank.</p>';
  }
  $("#detail").innerHTML=h;
  wireImgs($("#detail"));
  all(".chip").forEach(function(c){
    c.setAttribute("aria-pressed",String(Number(c.dataset.id)===id))});
}
function renderSquad(){
  var sq=squadOf(), mm=M();
  if(!sq.length){$("#pitch").innerHTML='<p class="emptynote">No squad data for this manager.</p>';
    $("#detail").innerHTML=""; return}
  var st=sq.filter(function(p){return p.starting});
  var bn=sq.filter(function(p){return !p.starting});
  function chip(p){
    var badge=p.isCap?'<span class="badge b-c" title="Captain">C</span>':
      p.isVice?'<span class="badge b-v" title="Vice-captain">V</span>':"";
    var flag=p.status!=="a"?'<span class="flag '+(p.status==="d"?"d":"")+'" title="'+
      esc(p.news||p.status)+'">!</span>':"";
    return '<div class="chipwrap">'+badge+flag+'<button class="chip" data-id="'+p.id+
      '" aria-pressed="false" aria-label="'+esc(p.name+", "+p.club+", "+p.pos+", "+m(p.price))+
      '">'+photoHTML(p,false)+'<span class="nm">'+esc(p.name)+'</span><span class="meta">'+
      esc(p.club)+' · '+m(p.price)+'</span><span class="bar"><i style="width:'+
      Math.max(4,Math.min(100,p.score))+'%"></i></span></button></div>';
  }
  var h='<div class="pitchhead"><h3>'+esc(mm.team)+'</h3><span class="meta">'+
    esc(mm.mgr)+' · '+mm.total+' pts · '+m(mm.budget.squadValue)+' squad · '+
    m(mm.budget.bank)+' bank'+(chipActive(mm)?' · '+esc(chipLabel(mm.chip))+
    ' active':'')+'</span></div>';
  h+='<div class="field">';
  ["GK","DEF","MID","FWD"].forEach(function(pos){
    var r=st.filter(function(p){return p.pos===pos});
    if(r.length) h+='<div class="row">'+r.map(chip).join("")+'</div>';
  });
  h+='</div><div class="benchlab"><i></i><span>Bench</span><i></i></div>';
  h+='<div class="row">'+bn.map(chip).join("")+'</div>';
  $("#pitch").innerHTML=h;
  wireImgs($("#pitch"));
  var g=$("#squadintro");
  if(g) g.innerHTML=intro('The fifteen '+esc(mm.team)+' picked, in formation. '+
    '<b>Click any player</b> to see his numbers and the players you could afford to '+
    'bring in instead. C is the captain, V the vice-captain, and a red or amber dot '+
    'means a fitness doubt.');
  detailFor(sq[0].id);
}

/* ---------------- picker ---------------- */
function renderPicker(){
  $("#picker").innerHTML='<div class="pickwrap"><h2>Whose team are you looking at?</h2>'+
    '<p class="lede">Pick a manager from '+esc(D.league?D.league.name:"the league")+
    '. Every tab — squad, transfer options, captaincy and differentials — is then '+
    'calculated from their squad, budget and bank.</p><div class="pickgrid">'+
    D.standings.map(function(s){
      return '<button class="pickcard" data-pick="'+s.entry+'">'+
        '<span class="pos">'+s.rank+'</span><span class="who"><b>'+esc(s.team)+'</b>'+
        '<em>'+esc(s.mgr)+'</em></span>'+
        '<span class="pts">'+s.total+'<br><span class="dim">pts</span></span></button>'
    }).join("")+'</div></div>';
}
function showPicker(){
  renderPicker();
  $("#picker").hidden=false; $("#tabs").hidden=true;
  $("#strip").hidden=true; $("#viewbar").hidden=true;
  TABS.forEach(function(k){
    document.getElementById("p-"+k).hidden=true});
}
function showApp(entry){
  viewEntry=entry; openPlayer=null; curClub=null;
  $("#picker").hidden=true; $("#tabs").hidden=false; $("#strip").hidden=false;
  $("#viewname").textContent=M()?M().team:"";
  $("#viewbar").hidden=false;
  renderAll();
  all(".tab").forEach(function(x){
    x.setAttribute("aria-selected",String(x.dataset.p==="home"))});
  TABS.forEach(function(k){
    document.getElementById("p-"+k).hidden=(k!=="home")});
}
function goTab(k){
  all(".tab").forEach(function(x){
    x.setAttribute("aria-selected",String(x.dataset.p===k))});
  TABS.forEach(function(t){document.getElementById("p-"+t).hidden=(t!==k)});
  $("#picker").hidden=true;
  window.scrollTo({top:0,behavior:"smooth"});
}

/* ---------------- Clubs ---------------- */
function tableHTML(){
  var t=D.table||[];
  if(!t.length) return "";
  var played=t.reduce(function(a,r){return a+r.p},0);
  var prov=(D.allFixtures||[]).filter(function(f){return f.prov}).length;
  return '<h4 class="seclab">Premier League table<i></i></h4>'+
    '<p class="emptynote" style="padding-top:0">Built from '+(played/2)+
    ' completed matches. The FPL API returns zeros for played, won and points, and its '+
    '"position" field is stale seeding, so this is computed from actual results.'+
    (prov?' <b>'+prov+' of them finished in the last day or so</b> and FPL has not awarded '+
     'bonus points yet — the scorelines are final, so they are counted here, but the game '+
     'itself still lists those fixtures as unfinished.':'')+'</p>'+
    '<div class="tblwrap" style="margin-bottom:20px"><table><thead><tr>'+
    '<th class="num">#</th><th>Club</th><th class="num">P</th><th class="num">W</th>'+
    '<th class="num">D</th><th class="num">L</th><th class="num">GF</th>'+
    '<th class="num">GA</th><th class="num">GD</th><th class="num">Pts</th>'+
    '<th>Form</th></tr></thead><tbody>'+
    t.map(function(r){
      return '<tr class="clickable" data-club="'+r.id+'"><td class="num">'+r.pos+'</td>'+
        '<td><span class="clubcell">'+badgeHTML(r.code,r.short,false)+
        '<b class="pname">'+esc(r.name)+'</b></span></td>'+
        '<td class="num">'+r.p+'</td><td class="num">'+r.w+'</td><td class="num">'+r.d+
        '</td><td class="num">'+r.l+'</td><td class="num">'+r.gf+'</td><td class="num">'+
        r.ga+'</td><td class="num">'+(r.gd>0?"+":"")+r.gd+'</td>'+
        '<td class="num"><b>'+r.pts+'</b></td><td><span class="formrow">'+
        (r.form.length?r.form.map(function(f){
          return '<span class="fchip f'+f+'" title="'+
            (f==="W"?"Win":f==="D"?"Draw":"Loss")+'">'+f+'</span>'}).join("")
          :'<span class="dim">—</span>')+
        '</span></td></tr>'
    }).join("")+'</tbody></table></div>';
}
function fixturesHTML(){
  var all=D.allFixtures||[];
  if(!all.length) return "";
  var gws=[]; all.forEach(function(f){if(gws.indexOf(f.gw)<0) gws.push(f.gw)});
  gws.sort(function(a,b){return a-b});
  if(gwView==null||gws.indexOf(gwView)<0) gwView=D.meta.planFrom;
  if(gws.indexOf(gwView)<0) gwView=gws[0];
  var i=gws.indexOf(gwView);
  var rows=all.filter(function(f){return f.gw===gwView});
  var tm={}; D.clubs.forEach(function(c){tm[c.id]=c});
  var done=rows.filter(function(f){return f.fin}).length;
  return '<h4 class="seclab">All fixtures<i></i></h4>'+
    '<div class="gwbar">'+
    '<button class="nav" data-gw="'+(i>0?gws[i-1]:"")+'"'+(i>0?"":" disabled")+
      ' aria-label="Previous gameweek">‹</button>'+
    '<span class="lbl">Gameweek '+gwView+'</span>'+
    '<button class="nav" data-gw="'+(i<gws.length-1?gws[i+1]:"")+'"'+
      (i<gws.length-1?"":" disabled")+' aria-label="Next gameweek">›</button>'+
    '<span class="sub">'+rows.length+' match'+(rows.length===1?"":"es")+
    (done?' · '+done+' played':'')+(gwView===D.meta.planFrom?' · next up':'')+'</span></div>'+
    '<div class="fixlist">'+rows.map(function(f){
      var H=tm[f.h]||{}, A=tm[f.a]||{};
      var mid = f.fin && f.hs!=null
        ? '<span class="mid">'+f.hs+' – '+f.as+'</span>'
        : '<span class="mid">v<small>'+(f.ko
            ? new Date(f.ko).toLocaleString(undefined,{weekday:"short",hour:"2-digit",
                minute:"2-digit"})
            : "TBC")+'</small></span>';
      return '<div class="fxrow'+(f.fin?" done":"")+'">'+
        '<span class="side">'+badgeHTML(H.code,H.short,false)+'<b>'+esc(H.short||"?")+
        '</b></span>'+mid+'<span class="side away">'+badgeHTML(A.code,A.short,false)+
        '<b>'+esc(A.short||"?")+'</b></span></div>'
    }).join("")+'</div>';
}
function renderClubs(){
  var counts=M().clubCountsById||{};
  $("#p-clubs").innerHTML=intro('Three things here: the <b>league table</b> worked out from '+
    'results so far, <b>every fixture</b> gameweek by gameweek, and each club\u2019s players '+
    'ranked by rating. Click a club to see who is worth owning there.'+
    ((D.odds&&D.odds.status==="on"&&D.odds.priced)
      ? ' Fixtures with a blue top edge are priced by the betting market.' : ''))+
    fixturesHTML()+tableHTML()+
    '<h4 class="seclab">Squads<i></i></h4><div class="clubgrid">'+D.clubs.map(function(c){
    var owned=counts[String(c.id)]||0;
    return '<button class="clubbtn" data-club="'+c.id+'" aria-pressed="'+(curClub===c.id)+'">'+
      badgeHTML(c.code,c.short,false)+'<b>'+esc(c.short)+'</b><em>'+esc(c.name)+'</em>'+
      '<em title="Average difficulty of this club\u2019s next six matches. 3.00 is a run of coin tosses; below that is kind, above it is hard.">Diff '+(c.avgFdr==null?"—":c.avgFdr.toFixed(2))+(owned?' · '+owned+' owned':'')+
      '</em></button>'
  }).join("")+'</div><div id="clubdetail"></div>';
  wireImgs($("#p-clubs"));
  if(curClub!=null) renderClubDetail(curClub);
  else $("#clubdetail").innerHTML='<p class="emptynote">Pick a club to see every '+
    'player that club has in the game, ranked by rating.</p>';
}
function renderClubDetail(cid){
  var c=null; D.clubs.forEach(function(x){if(x.id===cid) c=x});
  if(!c) return;
  var mm=M(), owned=(mm.clubCountsById||{})[String(c.id)]||0;
  var h='<div class="card dt"><div class="clubtitle" style="margin-bottom:12px">'+
    badgeHTML(c.code,c.short,true)+'<div><h2 style="font-size:22px">'+esc(c.name)+'</h2>'+
    '<div class="sub dim">'+c.squad.length+' players listed · '+esc(mm.team)+' owns '+
    owned+' · attack '+c.atkH+'/'+c.atkA+' (H/A) · defence '+c.defH+'/'+c.defA+
    '</div></div></div>'+
    '<h4 class="seclab">Fixture run<i></i></h4>'+fixStrip(c.short)+
    '<h4 class="seclab">Squad, ranked by model score<i></i></h4>'+
    '<div class="tblwrap"><table><thead><tr><th>Player</th><th>Pos</th>'+
    '<th class="num">Price</th><th class="num">Pts</th><th class="num">Mins</th>'+
    '<th class="num">xGI/90</th><th class="num" title="Tackles, blocks, interceptions, clearances and recoveries per 90 minutes. Hit the threshold in a match and it is worth 2 points.">Def. actions /90</th><th class="num">Owned</th>'+
    '<th class="num">Score</th><th>Notes</th></tr></thead><tbody>'+
    c.squad.map(function(pid){
      var p=P(pid), notes=[];
      if(p.pen===1) notes.push("pens");
      if(p.ck===1) notes.push("corners");
      if(p.fk===1) notes.push("FKs");
      if(p.status!=="a") notes.push(p.status==="d"?"doubt":"out");
      if(inSquad(pid)) notes.push("in squad");
      return '<tr class="clickable" data-look="'+pid+'"><td class="pname">'+esc(p.name)+
        '</td><td class="dim">'+esc(p.pos)+'</td><td class="num">'+m(p.price)+
        '</td><td class="num">'+p.pts+'</td><td class="num">'+p.mins+'</td><td class="num">'+
        p.xgi90.toFixed(2)+'</td><td class="num">'+p.dc90.toFixed(1)+'</td><td class="num">'+
        p.owned+'%</td><td class="num"><b>'+Number(p.score).toFixed(1)+'</b></td><td class="dim">'+
        esc(notes.join(", "))+'</td></tr>'
    }).join("")+'</tbody></table></div></div>';
  $("#clubdetail").innerHTML=h;
  wireImgs($("#clubdetail"));
}

/* ---------------- Players ---------------- */
var COLS=[["name","Player",0],["club","Club",0],["pos","Pos",0],["price","Price",1],
  ["pts","Pts",1],["mins","Mins",1],["form","Form",1],["xgi90","xGI/90",1],
  ["dc90","Def. actions /90",1],["owned","Owned",1],["score","Score",1]];
function renderPlayersShell(){
  $("#p-players").innerHTML=intro('Every player in the game. Narrow the list with the '+
    'filters, sort by tapping any column heading, then <b>click a row</b> to open that '+
    'player without leaving this page.')+
    '<div class="filters">'+
    '<div class="fgroup"><label for="q">Search</label>'+
    '<input type="search" id="q" placeholder="name or club"></div>'+
    '<div class="fgroup"><label for="fpos">Position</label><select id="fpos">'+
    '<option value="">All</option><option>GK</option><option>DEF</option>'+
    '<option>MID</option><option>FWD</option></select></div>'+
    '<div class="fgroup"><label for="fmax">Max price</label>'+
    '<input type="number" id="fmax" step="0.1" min="3.5" placeholder="any" style="width:96px"></div>'+
    '<div class="fgroup"><label for="favail">Availability</label><select id="favail">'+
    '<option value="all">All</option><option value="fit" selected>Fit only</option></select></div>'+
    '<div class="fgroup"><label for="fsquad">Squad</label><select id="fsquad">'+
    '<option value="all">Everyone</option><option value="in">In this squad</option>'+
    '<option value="out">Not in this squad</option></select></div>'+
    '<span class="count" id="pcount"></span></div>'+
    '<div class="tblwrap" style="max-height:70vh;overflow-y:auto"><table id="ptable">'+
    '<thead><tr>'+COLS.map(function(c){
      return '<th class="sortable'+(c[2]?" num":"")+'" data-k="'+c[0]+'">'+esc(c[1])+'</th>'
    }).join("")+'</tr></thead><tbody id="pbody"></tbody></table></div>';
  ["q","fpos","fmax","favail","fsquad"].forEach(function(id){
    var el=document.getElementById(id);
    el.addEventListener("input",renderPlayerRows);
    el.addEventListener("change",renderPlayerRows);
  });
  all("#ptable th.sortable").forEach(function(th){
    th.addEventListener("click",function(){
      var k=th.dataset.k;
      if(sortKey===k) sortDir=-sortDir;
      else {sortKey=k; sortDir=(k==="name"||k==="club"||k==="pos")?1:-1}
      renderPlayerRows();
    });
  });
  renderPlayerRows();
}
function playerExpansion(p){
  return '<div class="expbox"><div class="expgrid">'+photoHTML(p,true)+
    '<div class="expname"><h3>'+esc(p.full||p.name)+'</h3>'+
    '<div class="sub">'+esc(p.clubFull)+' · '+esc(p.pos)+' · '+m(p.price)+
    ' · '+Number(p.score).toFixed(1)+' xPts/'+D.horizon+'</div>'+pillsFor(p)+'</div></div>'+
    statGrid(p)+
    '<div class="exptwo"><div><h4 class="seclab">Next six fixtures<i></i></h4>'+
    fixStrip(p.club)+'</div><div class="explain" style="border-radius:8px;border-top-width:1px">'+
    explainHTML(p)+'</div></div></div>';
}
function renderPlayerRows(){
  var q=($("#q").value||"").toLowerCase().trim();
  var pos=$("#fpos").value, mx=parseFloat($("#fmax").value),
      av=$("#favail").value, sq=$("#fsquad").value;
  var rows=D.players.filter(function(p){
    if(pos&&p.pos!==pos) return false;
    if(!isNaN(mx)&&p.price>mx+1e-9) return false;
    if(av==="fit"&&p.status!=="a") return false;
    if(sq==="in"&&!inSquad(p.id)) return false;
    if(sq==="out"&&inSquad(p.id)) return false;
    if(q&&(p.name+" "+p.full+" "+p.clubFull+" "+p.club).toLowerCase().indexOf(q)<0) return false;
    return true;
  });
  rows.sort(function(a,b){
    var x=a[sortKey],y=b[sortKey];
    if(typeof x==="string") return sortDir*x.localeCompare(y);
    return sortDir*((x||0)-(y||0));
  });
  all("#ptable th.sortable").forEach(function(th){
    if(th.dataset.k===sortKey) th.setAttribute("aria-sort",sortDir>0?"ascending":"descending");
    else th.removeAttribute("aria-sort");
  });
  $("#pcount").textContent=rows.length+" of "+D.players.length+" players";
  var show=rows.slice(0,300);
  $("#pbody").innerHTML=show.map(function(p){
    var open=openPlayer===p.id;
    var tr='<tr class="clickable'+(open?" open":"")+'" data-row="'+p.id+'">'+
      '<td class="pname"><span class="chev">'+(open?"▾":"▸")+'</span> '+esc(p.name)+
      (p.status!=="a"?' <span class="dim">⚠</span>':'')+
      (inSquad(p.id)?' <span class="dim">•</span>':'')+
      '</td><td class="dim">'+esc(p.club)+'</td><td class="dim">'+esc(p.pos)+
      '</td><td class="num">'+m(p.price)+'</td><td class="num">'+p.pts+
      '</td><td class="num">'+p.mins+'</td><td class="num">'+p.form.toFixed(1)+
      '</td><td class="num">'+p.xgi90.toFixed(2)+'</td><td class="num">'+p.dc90.toFixed(1)+
      '</td><td class="num">'+p.owned+'%</td><td class="num"><b>'+Number(p.score).toFixed(1)+
      '</b></td></tr>';
    if(open) tr+='<tr class="exp"><td colspan="'+COLS.length+'">'+playerExpansion(p)+'</td></tr>';
    return tr;
  }).join("")+(rows.length>300?'<tr><td colspan="'+COLS.length+
    '" class="dim" style="text-align:center">showing the first 300 — narrow the filters '+
    'to see the rest</td></tr>':"");
  wireImgs($("#pbody"));
}

/* ---------------- Captaincy ---------------- */
function renderCap(){
  var mm=M(), caps=mm.captaincy||[];
  if(!caps.length){$("#p-cap").innerHTML='<p class="emptynote">No squad data.</p>';return}
  var sc=caps.map(function(c){return P(c.id).score});
  var maxScore=Math.max.apply(null,sc);
  var maxX=Math.max.apply(null,caps.map(function(c){return P(c.id).xgi90}))||1;
  var maxF=Math.max.apply(null,caps.map(function(c){return P(c.id).form}))||1;
  $("#p-cap").innerHTML=intro('Your captain scores double, so this is usually the biggest '+
    'single decision of the week. Options are ranked from the players already in '+
    esc(mm.team)+'\u2019s starting eleven. <b>Rivals own</b> tells you whether a big score '+
    'would gain you ground or simply keep pace.')+
    '<div class="msg info">Ranked from '+esc(mm.team)+
    '’s current starting XI for GW'+D.meta.planFrom+'. Bars are relative to the best '+
    'candidate in that squad, not the whole game — this answers "who of theirs", not '+
    '"who in FPL".</div><div class="capgrid">'+caps.map(function(c,i){
      var p=P(c.id), f=c.nextFix||{};
      function bar(lab,val,max,txt){
        return '<div class="cb"><span>'+lab+'</span><span class="track"><i style="width:'+
          Math.max(3,Math.round(100*val/(max||1)))+'%"></i></span><span class="val">'+
          txt+'</span></div>';
      }
      return '<div class="card capcard"><div class="rank">Option '+(i+1)+
        (c.isCap?' · current captain':c.isVice?' · current vice':'')+'</div>'+
        '<div class="caphead">'+photoHTML(p,false)+'<div style="min-width:0">'+
        '<h3>'+esc(p.name)+'</h3><div class="sub" style="margin-bottom:0">'+
        esc(p.clubFull)+' · '+esc(p.pos)+' · '+m(p.price)+'</div></div></div>'+
        '<div class="fixrow" style="margin-bottom:11px"><div class="fx '+fdrCls(f.fdr)+
        '" style="min-width:0"><span class="g">GW'+(f.gw||"")+' '+(f.ha||"")+'</span>'+
        '<span class="o">'+esc(f.opp||"—")+'</span><span class="n">Diff '+
        (f.fdr==null?"—":f.fdr)+'</span></div></div><div class="capbars">'+
        bar("xPts / "+D.horizon,p.score,maxScore,Number(p.score).toFixed(1))+
        bar("xGI / 90",p.xgi90,maxX,p.xgi90.toFixed(2))+
        bar("Form",p.form,maxF,p.form.toFixed(1))+
        bar("Rivals own",c.rivalsOwning,c.leagueSize,c.rivalsOwning+"/"+c.leagueSize)+
        '</div><p class="emptynote" style="padding:0;font-size:12.5px">'+
        (c.rivalsOwning>=Math.ceil(c.leagueSize*0.6)
          ? 'Widely owned in this league — captaining him mostly protects the position.'
          : 'Owned by '+c.rivalsOwning+' of '+c.leagueSize+
            ' — a haul here gains real ground.')+'</p></div>'
    }).join("")+'</div>';
  wireImgs($("#p-cap"));
}

/* ---------------- plain English ---------------- */
function plainWhy(list){
  // reasons now arrive readable and with their numbers; this only rewrites the few
  // shorthand forms an older build could still be serving
  return (list||[]).map(function(w){
    if(/first-choice penalties/.test(w)) return "first on penalties";
    if(/cleared DEFCON \((\d+)/.test(w))
      return w.replace(/cleared DEFCON \((\d+) vs (\d+)\)/,
                       "$1 defensive actions per 90, threshold is $2");
    if(/^kind run \(/.test(w)) return w.replace(/^kind run \((?:FDR |difficulty )?/, "easy run, difficulty ")
                                        .replace(/\)$/, " over six");
    if(/^low xGC/.test(w)) return w.replace(/^low xGC \(([\d.]+)\/90\)/,
      "tight defence, $1 goals conceded expected per 90");
    if(/^differential \(([\d.]+)% owned\)/.test(w))
      return w.replace(/^differential \(([\d.]+)% owned\)/, "owned by just $1%");
    if(/^xGI\/90 ([\d.]+)/.test(w))
      return w.replace(/^xGI\/90 ([\d.]+)/, "$1 goals+assists expected per 90");
    if(/on set pieces/.test(w)) return "on corners or free-kicks";
    if(/^frees/.test(w)) return w.replace("frees","frees up");
    return w;
  });
}
function intro(text){return '<p class="tabintro">'+text+'</p>'}
function deadlineText(){
  if(!D.meta.deadline) return {text:"Deadline not published yet", when:""};
  var d=new Date(D.meta.deadline), now=new Date(), ms=d-now;
  var when=d.toLocaleString(undefined,{weekday:"long",day:"numeric",month:"short",
    hour:"2-digit",minute:"2-digit"});
  if(ms<=0) return {text:"Deadline has passed — this gameweek is under way", when:when};
  var hrs=ms/3600000, days=Math.round(hrs/24);
  var left=hrs<1?"in "+Math.round(ms/60000)+" minutes"
    :hrs<24?"in "+Math.round(hrs)+" hours"
    :"in "+days+" day"+(days===1?"":"s");
  return {text:"Deadline "+left, when:when};
}

/* ---------------- Home ---------------- */
function renderHome(){
  var _pw=priorWarning();
  var mm=M(), sq=squadOf(), dl=deadlineText();
  var lead=D.standings[0], gap=lead?lead.total-mm.total:null;
  var h=intro('Everything worth doing this week, in one place. Each card links to the '+
    'tab with the full detail. You are looking at <b>'+esc(mm.team)+'</b> — use '+
    '<b>Change</b> at the top to switch to someone else in the league.');

  h+='<div class="hero"><div><h2>Planning Gameweek '+D.meta.planFrom+'</h2>'+
     '<div class="when">'+esc(dl.text)+(dl.when?' · '+esc(dl.when):'')+'</div></div>'+
     '<div class="standing">'+(gap===null?'':(gap===0
        ? '<b>Top</b> of '+esc(D.league?D.league.name:"your league")
        : '<b>'+mm.rank+getOrdinal(mm.rank)+'</b> of '+D.standings.length+
          ' · '+gap+' point'+(gap===1?'':'s')+' behind '+esc(lead.team)))+'</div></div>';

  h+='<div class="acts">';

  // 1. the transfer
  var t=(mm.transfers||[])[0];
  if(t){
    var o1=P(t.outId), i1=P(t.inId);
    h+='<div class="act"><div class="kicker">Best transfer</div>'+
      '<div class="faces">'+photoHTML(o1,false)+'<b>'+esc(o1.name)+'</b>'+
      '<span class="arrow">→</span>'+photoHTML(i1,false)+'<b>'+esc(i1.name)+'</b></div>'+
      '<h3>Swap '+esc(o1.name)+' for '+esc(i1.name)+'</h3>'+
      '<div class="body">'+
      (t.cost>0?'Costs '+m(t.cost)+'. ':t.cost<0?'Frees up '+m(-t.cost)+'. ':'Same price. ')+
      esc(i1.name)+' — '+esc(plainWhy(t.why).join(" · ")||"rates higher over the coming games")+
      '. Biggest single gain available over the next '+D.horizon+' matches.</div>'+
      '<button class="go" data-go="tx">See all transfer ideas</button></div>';
  } else {
    h+='<div class="act calm"><div class="kicker">Transfers</div>'+
      '<h3>No change needed</h3><div class="body">Nothing affordable improves this squad '+
      'over the next '+D.horizon+' matches. Save the transfer.</div>'+
      '<button class="go" data-go="tx">Look anyway</button></div>';
  }

  // 2. the captain
  var c=(mm.captaincy||[])[0];
  if(c){
    var cp=P(c.id), f=c.nextFix||{};
    h+='<div class="act"><div class="kicker">Captain</div>'+
      '<div class="faces">'+photoHTML(cp,false)+'<b>'+esc(cp.name)+'</b></div>'+
      '<h3>Give the armband to '+esc(cp.name)+'</h3>'+
      '<div class="body">'+esc(cp.clubFull)+
      (f.opp?' play '+esc(f.opp)+(f.ha==="H"?" at home":" away")+
        ', which is '+(f.fdr<=2?"a kind fixture":f.fdr>=4?"a tough one":"about average"):'')+
      '. '+(c.rivalsOwning>=Math.ceil(c.leagueSize*0.6)
        ? 'Most of your league own him, so this mainly protects your position.'
        : 'Only '+c.rivalsOwning+' of '+c.leagueSize+' rivals own him — a big score gains ground.')+
      (c.isCap?' He is already your captain.':'')+'</div>'+
      '<button class="go" data-go="cap">Compare captain options</button></div>';
  }

  // 3. anything to worry about
  var flagged=sq.filter(function(p){return p.starting&&p.status!=="a"});
  var benchFit=sq.filter(function(p){return !p.starting&&p.status==="a"});
  if(flagged.length){
    h+='<div class="act warn"><div class="kicker">Needs a look</div>'+
      '<h3>'+flagged.length+' player'+(flagged.length===1?'':'s')+
      ' in your line-up '+(flagged.length===1?'has':'have')+' a fitness flag</h3>'+
      '<div class="body"><ul class="flaglist">'+flagged.map(function(p){
        return '<li><b>'+esc(p.name)+'</b> — '+esc(p.news||"not fully fit")+'</li>'
      }).join("")+'</ul>'+(benchFit.length?'<p style="margin:9px 0 0">You have '+
        benchFit.length+' fit player'+(benchFit.length===1?'':'s')+
        ' on the bench to swap in.</p>':'')+'</div>'+
      '<button class="go" data-go="squad">Open my team</button></div>';
  } else {
    h+='<div class="act calm"><div class="kicker">Fitness</div>'+
      '<h3>Everyone in your line-up is fit</h3>'+
      '<div class="body">No injury or doubt flags in the starting eleven. Worth checking '+
      'again after the Friday press conferences — this only knows what the game has published.'+
      '</div><button class="go" data-go="squad">Open my team</button></div>';
  }
  h+='</div>';
  $("#p-home").innerHTML=_pw+h;
  wireImgs($("#p-home"));
}
function getOrdinal(n){
  var s=["th","st","nd","rd"], v=n%100;
  return s[(v-20)%10]||s[v]||s[0];
}

/* ---------------- Transfers ---------------- */
function explainTransfer(t){
  var i=P(t.inId), o=P(t.outId);
  function line(p,lab){
    return '<tr><td>'+lab+' '+esc(p.name)+'</td><td class="n">'+p.base.toFixed(2)+
      ' next match · '+p.games5+' fixture'+(p.games5===1?'':'s')+' in the window</td>'+
      '<td class="r">'+p.proj5.toFixed(1)+'</td></tr>';
  }
  var h='<h5>How this was worked out</h5><table class="calc">'+
    line(i,"In —")+line(o,"Out —")+
    '<tr class="tot"><td>Gain over next 5</td><td class="n"></td><td class="r">'+
    (t.gain5>0?"+":"")+t.gain5.toFixed(1)+'</td></tr></table>'+
    '<p>The right-hand column is <b>expected points over the next '+D.horizon+' matches</b>: '+
    'each fixture priced separately from that club’s attack and defence in that specific game, '+
    'then added up. A blank gameweek contributes nothing and a double counts twice, which is '+
    'why the fixture count is shown — it falls out of the arithmetic rather than being '+
    'corrected for.</p>'+
    '<p><b>These are points, so you can compare them with a −4 hit directly.</b> Treat the '+
    'precision with suspicion though: even a properly trained model sits around 5 points of '+
    'error on the players who actually haul, so a gap of a point or two is noise.</p>';
  return h;
}
function xp(v){return (v==null?"—":Number(v).toFixed(2))}
function miniRow(p,extra,tag){
  return '<div class="tsrow'+(tag?' '+tag:'')+'">'+photoHTML(p)+
    '<div class="tsn"><b>'+esc(p.name)+'</b><small>'+esc(p.club)+' · '+p.pos+' · '+
    m(p.price)+'</small></div><div class="tsx">'+xp(p.xp1)+'<small>xPts</small></div>'+
    (extra||'')+'</div>';
}
function renderSheet(){
  var mm=M(), L=mm.lineup;
  if(!L){ $("#p-sheet").innerHTML=intro('No squad available for this manager yet.'); return; }
  var mk=L.marketBacked||0;
  var head=intro('The best eleven the model can build out of '+esc(mm.team)+'’s fifteen, '+
    'for <b>this gameweek only</b>. Every number here is expected points for the next match — '+
    'not the five-match view the Transfers tab uses, because who to field is a question about '+
    'Saturday.'+(mk?' <b>'+mk+' of '+L.squadSize+'</b> of these fixtures are priced by the '+
    'betting market, so those calls come from the odds rather than from form.':''));

  var chg=(L.changes||[]);
  var verdict = chg.length
    ? '<div class="msg warn"><b>'+chg.length+' change'+(chg.length===1?'':'s')+' suggested</b> — '+
      chg.map(function(c){var a=P(c["out"]),z=P(c["in"]);
        return (a?esc(a.name):'?')+' out, '+(z?esc(z.name):'?')+' in'}).join('; ')+
      '. Worth about <b>'+(L.gain>0?"+":"")+L.gain+' points</b> this week.</div>'
    : '<div class="msg good"><b>Your eleven is already the best one available.</b> No changes '+
      'suggested — you are picking '+L.currentPoints+' expected points and that is the maximum '+
      'this squad can field.</div>';

  var cap=P(L.captain), vice=P(L.vice);
  var curCapPick=(mm.picks||[]).filter(function(p){return p.isCap})[0];
  var curCap=curCapPick?P(curCapPick.id):null;
  var capNote = L.capIsCurrent
    ? 'This is already your captain.'
    : '<b>Different from your current pick'+(curCap?', '+esc(curCap.name):'')+'.</b>'+
      ((cap&&curCap)
        ? ' Worth '+(cap.xp1-curCap.xp1).toFixed(2)+' points on the armband alone, because '+
          'the captain scores twice.'
        : '');

  var pos={GK:[],DEF:[],MID:[],FWD:[]};
  L.xi.forEach(function(id){var p=P(id); if(p&&pos[p.pos]) pos[p.pos].push(p)});
  var pitch=Object.keys(pos).map(function(k){
    if(!pos[k].length) return "";
    return '<div class="tsline"><span class="tslab">'+k+'</span>'+pos[k].map(function(p){
      var b=p.id===L.captain?'<span class="badge b-c" title="Captain">C</span>':
            p.id===L.vice?'<span class="badge b-v" title="Vice-captain">V</span>':'';
      if(p.pStart!=null&&p.pStart<0.7) b+='<span class="rotrisk" title="'+
        esc((p.startWhy||'')+'. Expected points already allow for this, but it is the '+
        'kind of call team news should settle.')+'">'+Math.round(p.pStart*100)+'%</span>';
      return '<button class="tscard" data-open="'+p.id+'">'+photoHTML(p)+b+
        '<span class="n">'+esc(p.name)+'</span><span class="x">'+xp(p.xp1)+'</span></button>';
    }).join("")+'</div>';
  }).join("");

  var bench=(L.bench||[]).map(function(id,i){
    var p=P(id); if(!p) return '';
    return miniRow(p,'<div class="tsord">'+(i+1)+'<small>on first</small></div>');
  }).join("")+((L.benchGk&&P(L.benchGk))?
    miniRow(P(L.benchGk),'<div class="tsord">GK<small>separate</small></div>'):"");

  var close=(L.closeCalls||[]).length
    ? '<h4>Too close to call</h4><p class="dim">These are within '+
      'a fifth of a point of each other. The model has an opinion; it is not a strong one, '+
      'and team news should override it.</p>'+
      L.closeCalls.map(function(c){
        var a=P(c["in"]), z=P(c.out); if(!a||!z) return '';
        return '<div class="ccrow"><b>'+esc(a.name)+'</b> '+xp(a.xp1)+
          ' <span class="vs">vs</span> <b>'+esc(z.name)+'</b> '+xp(z.xp1)+
          ' <span class="gap">'+c.gap.toFixed(2)+' apart'+(c.captaincy?' · for the armband':'')+
          '</span></div>';
      }).join("")
    : '';

  var ch=L.chips||{};
  function spent(key){
    var r=(mm.chipsUsed||[]).filter(function(c){return c.key===key})[0];
    if(!r) return '';
    return '<em class="chipused">'+r.used+' of 2 used'+
      (r.gws&&r.gws.length?' (GW'+r.gws.join(', GW')+')':'')+
      (r.left?'':' — none left')+'</em>';
  }
  var chips='<h4>Chips</h4><div class="chipgrid">'+
    '<div class="chipcard'+(ch.benchBoostWorth?' on':'')+'"><b>Bench Boost</b>'+
    '<span class="cv">'+ch.benchBoost+'</span><small>expected points sitting on your bench'+
    (ch.benchBoostWorth?'. That is a strong bench — worth considering.':
     '. Below the ~12 points that usually makes this chip worthwhile.')+'</small>'+
    spent("bboost")+'</div>'+
    '<div class="chipcard'+(ch.tripleCaptainWorth?' on':'')+'"><b>Triple Captain</b>'+
    '<span class="cv">'+ch.tripleCaptain+'</span><small>expected from '+
    (cap?esc(cap.name):'your captain')+'. The third multiplier adds that much again'+
    (ch.tripleCaptainWorth?' — a genuinely big week.':'. Usually worth holding for a better fixture.')+
    '</small>'+spent("3xc")+'</div></div>'+
    ((mm.chipsUsed||[]).length
      ? '<p class="dim" style="margin-top:8px">Already played: '+
        mm.chipsUsed.map(function(c){return esc(c.name)+' in GW'+c.gws.join(' and GW')}).join('; ')+
        '. The 2026-27 game gives two of each, so these are counted against an allowance of two.</p>'
      : '');

  $("#p-sheet").innerHTML=head+verdict+
    '<div class="tsgrid"><div class="card"><h4>Starting eleven · '+L.formation+'</h4>'+
    '<div class="tsmeta">'+L.xiPoints+' expected points, <b>'+L.withCaptain+
    '</b> with the captain doubled</div>'+pitch+
    '<div class="capnote"><b>Captain:</b> '+(cap?esc(cap.name):'—')+' · <b>Vice:</b> '+
    (vice?esc(vice.name):'—')+'<br><span class="dim">'+capNote+'</span></div></div>'+
    '<div class="card"><h4>Bench, in the order they come on</h4>'+
    '<p class="dim">If a starter does not play, FPL brings on the first eligible name here. '+
    'The order is yours to set in the FPL app.</p>'+bench+close+chips+'</div></div>';
}

function bundlesHTML(mm){
  var B=mm.bundles||{}, out='';
  var have=(B["2"]||[]).length+(B["3"]||[]).length;
  var lead='<h3 class="sechead">More than one at a time</h3>'+
    '<p class="dim">A 5.5m player can only be swapped for another 5.5m player. Selling two '+
    'at once pools the money, which is how you reach a premium — and these are scored on the '+
    '<b>eleven that would actually play</b>, not on all fifteen, so upgrading a bench player '+
    'who never gets picked counts for nothing. Assumes <b>'+(mm.freeTransfers||1)+
    ' free transfer</b>; every extra move costs 4 points and that is already subtracted.</p>';
  if(B.error) return lead+'<div class="msg warn">Could not work these out: '+esc(B.error)+'</div>';
  if(B.trimmed) lead+='<div class="msg info">This server ran out of its search budget, so '+
    'only the shorter combinations were explored for this manager. Press Refresh to try again.</div>';
  if(!have) return lead+'<p class="emptynote">No combination of two or three transfers beats '+
    'the points it would cost in hits. Holding is the right move.</p>';
  ["2","3"].forEach(function(k){
    var list=B[k]||[];
    if(!list.length) return;
    out+='<h4 class="subhead">'+(k==="2"?"Two":"Three")+' transfers</h4>';
    out+=list.map(function(b){
      var rows=(b.pairs||[]).map(function(pr){
        var o=P(pr["out"]), i=P(pr["in"]);
        if(!o||!i) return '';
        var g=pr.priceGap;
        return '<div class="bmove"><span>'+esc(o.name)+' <span class="dim">'+o.pos+' · '+
          m(o.price)+'</span></span><span class="ar">→</span><span><b>'+esc(i.name)+
          '</b> <span class="dim">'+m(i.price)+
          (g>0?' <span class="up">+'+m(g).slice(1)+'</span>':g<0?' <span class="dn">−'+m(-g).slice(1)+'</span>':'')+
          '</span></span></div>';
      }).join("");
      return '<div class="bundle'+(b.reallocation?' realloc':'')+'"><div class="bhead"><div>'+
        '<b>'+b.outs.length+' moves</b>'+(b.reallocation?'<span class="rtag">reallocation</span>':'')+
        '<div class="dim" style="font-size:11.5px">'+
        (b.reallocation?'Downgrades one player to free '+m(b.freed)+' and spends it on an '+
         'upgrade elsewhere — this is the “is he worth his price” move.':
         'Straight upgrades within the pooled budget.')+'</div></div>'+
        '<div class="bnet">'+(b.net>0?"+":"")+b.net.toFixed(1)+'<small>net, after hits</small></div>'+
        '</div>'+rows+'<div class="bsum">eleven gains '+b.gain.toFixed(1)+
        ' · hits −'+b.hits+' · '+m(b.spare)+' left over'+
        (Math.abs(b.squadGain-b.gain)>=0.5?' · counting all fifteen would have claimed '+
          b.squadGain.toFixed(1)+', which is why that is not the measure used':'')+'</div></div>';
    }).join("");
  });
  return lead+out;
}
function renderTx(){
  var mm=M(), tx=mm.transfers||[];
  var head=intro('Swaps worth making, best first, judged over the <b>next '+
    D.horizon+' matches</b>. Everything here fits '+esc(mm.team)+'\u2019s budget and keeps '+
    'you inside the three-players-per-club rule. Tap <b>?</b> on any card to see the working.')+
    bundlesHTML(mm)+
    '<h3 class="sechead">One transfer at a time</h3>'+
    '<p class="dim">A single swap can only reach players in the same price bracket. The '+
    'bundles above exist because pooling two sales breaks out of it.</p>';
  if(!tx.length){
    $("#p-tx").innerHTML=head+'<p class="emptynote">No single swap improves this squad over '+
      'the next '+D.horizon+' matches within budget.</p>';
    wireImgs($("#p-tx")); return;
  }
  $("#p-tx").innerHTML=head+tx.map(function(t,idx){
    var i=P(t.inId), o=P(t.outId);
    function side(p,cls){
      return '<span class="tside '+cls+'">'+photoHTML(p,false)+'<span style="min-width:0">'+
        '<span class="nm">'+esc(p.name)+'</span><span class="sub" style="display:block">'+
        esc(p.club)+' · '+esc(p.pos)+' · '+m(p.price)+'</span></span></span>';
    }
    return '<div class="tcard"><div class="tmove">'+side(o,"out")+
      '<span class="tarrow">→</span>'+side(i,"in")+
      '<span class="tgain"><b>'+(t.gain5>0?"+":"")+t.gain5.toFixed(1)+'</b>'+
      '<span>gain over next '+D.horizon+'</span></span></div>'+
      '<div class="tmeta"><span class="pill" title="Expected points for the very next match">Next match '+
      (i.xp1-o.xp1>0?"+":"")+(i.xp1-o.xp1).toFixed(2)+'</span><span class="pill'+(t.cost<=0?" good":"")+'">'+
      (t.cost>0?'Costs '+m(t.cost):t.cost<0?'Frees '+m(-t.cost):'Same price')+'</span>'+
      '<span class="pill">'+m(t.spare)+' left over</span>'+
      (t.why&&t.why.length?'<span class="pill">'+esc(plainWhy(t.why).join(" · "))+'</span>':'')+
      '</div><div class="tfix"><div><h6>Out — '+esc(o.name)+' · next '+D.horizon+
      '</h6>'+fixStrip(o.club,D.horizon)+'</div><div><h6>In — '+esc(i.name)+' · next '+
      D.horizon+'</h6>'+fixStrip(i.club,D.horizon)+'</div></div>'+
      '<button class="qmark" data-tx="'+idx+'" aria-expanded="false" '+
      'title="How this was calculated" aria-label="Explain this transfer">?</button>'+
      '<div class="explain" id="tx-'+idx+'" hidden></div></div>'
  }).join("");
  wireImgs($("#p-tx"));
}

/* ---------------- League ---------------- */
function renderLeague(){
  if(!D.standings.length){
    $("#p-league").innerHTML='<p class="emptynote">League data unavailable.</p>';return}
  var mm=M(), lead=D.standings[0], n=D.standings.length;
  function mp(pid,pk,ownedBy){
    var p=P(pid);
    return '<span class="mp'+(pk.starting?"":" bench")+(ownedBy>=4?" shared":"")+'">'+
      '<b>'+esc(p.name)+(pk.isCap?" (C)":pk.isVice?" (V)":"")+'</b><em>'+esc(p.club)+
      ' · '+ownedBy+'/'+n+'</em></span>';
  }
  var ownCount={};
  D.standings.forEach(function(s){
    (D.managers[String(s.entry)].picks||[]).forEach(function(pk){
      ownCount[pk.id]=(ownCount[pk.id]||0)+1});
  });
  var h=intro('Where everyone stands. <b>Click a team name</b> to see their squad, or use '+
    'the button inside to view the whole app as them. Below, the two lists show who '+
    esc(mm.team)+' owns that nobody else does, and who the rest of the league owns that '+
    'they do not.')+
    '<div class="tblwrap"><table><thead><tr><th class="num">#</th><th>Team</th>'+
    '<th>Manager</th><th class="num">GW</th><th class="num">Total</th><th class="num">Gap</th>'+
    '<th class="num">Value</th><th class="num">Bank</th></tr></thead><tbody>'+
    D.standings.map(function(s){
      var sm=D.managers[String(s.entry)];
      return '<tr'+(s.entry===viewEntry?' class="me"':'')+'><td class="num">'+s.rank+'</td>'+
        '<td><button class="mgrbtn" data-entry="'+s.entry+'">'+esc(s.team)+'</button>'+
        ((s.chip&&!s.chipSpent)?' <span class="pill warn" title="Playing this chip '+
          'in the current gameweek">'+esc(chipLabel(s.chip))+'</span>':'')+
        '</td><td>'+esc(s.mgr)+
        '</td><td class="num">'+s.gw+'</td><td class="num"><b>'+s.total+'</b></td>'+
        '<td class="num">'+(s.total-lead.total===0?"—":(s.total-lead.total))+'</td>'+
        '<td class="num">'+m(s.value/10)+'</td><td class="num">'+m(s.bank/10)+'</td></tr>'+
        '<tr id="sq-'+s.entry+'" hidden><td colspan="8" style="padding:0 11px"><div class="sqdrop">'+
        '<h4 class="seclab">'+esc(s.team)+' — starting XI<i></i></h4><div class="mini">'+
        sm.picks.filter(function(pk){return pk.starting}).map(function(pk){
          return mp(pk.id,pk,ownCount[pk.id]||1)}).join("")+'</div>'+
        '<h4 class="seclab" style="margin-top:11px">Bench<i></i></h4><div class="mini">'+
        sm.picks.filter(function(pk){return !pk.starting}).map(function(pk){
          return mp(pk.id,pk,ownCount[pk.id]||1)}).join("")+
        '</div><p style="margin:11px 0 0"><button class="btn ghost" data-pick="'+s.entry+
        '">View the whole app as '+esc(s.team)+'</button></p></div></td></tr>'
    }).join("")+'</tbody></table></div>';
  h+='<div class="two" style="margin-top:20px">'+
    '<div class="card dt"><h4 class="seclab">'+esc(mm.team)+' alone owns<i></i></h4>'+
    (mm.uniques.length?mm.uniques.map(function(pid){
      var p=P(pid);
      return '<button class="alt" data-look="'+pid+'"><span class="d '+
        (p.var>=0?"up":"dn")+'">'+Number(p.score).toFixed(1)+'<small>xPts/'+D.horizon+'</small></span>'+
        '<span class="body"><span class="t">'+esc(p.name)+' <em>'+esc(p.club)+' · '+
        esc(p.pos)+' · '+m(p.price)+'</em></span><span class="w">'+p.pts+
        ' pts · '+p.owned+'% owned overall</span></span></button>'
    }).join(""):'<p class="emptynote">Nothing unique right now.</p>')+'</div>'+
    '<div class="card dt"><h4 class="seclab">Rivals own, '+esc(mm.team)+' does not<i></i></h4>'+
    mm.missing.map(function(x){
      var p=P(x.id);
      return '<button class="alt" data-look="'+x.id+'"><span class="d '+
        (x.ownedBy>=4?"up":"dn")+'">'+x.ownedBy+'/'+n+'<small>own</small></span>'+
        '<span class="body"><span class="t">'+esc(p.name)+' <em>'+esc(p.club)+' · '+
        esc(p.pos)+' · '+m(p.price)+'</em></span><span class="w">Score '+
        Number(p.score).toFixed(1)+' xPts · '+p.pts+' pts · '+esc((x.owners||[]).join(", "))+
        '</span></span></button>'
    }).join("")+'</div></div>';
  $("#p-league").innerHTML=h;
}

/* ---------------- Model ---------------- */
function priorWarning(){
  var s=(D.meta.model||{}).priorStale;
  if(!s) return '';
  return '<div class="msg warn"><b>The last-season data in this app is out of date.</b> '+
    'It holds '+esc(s.have)+' rates, but the season now running is '+esc(s.season)+
    ', so the priors should come from '+esc(s.want)+'. Player ratings will lean on figures '+
    'a year older than they should until the table is rebuilt. Everything else — fixtures, '+
    'results, prices, odds — is still live.</div>';
}
/* ---------------- ask a question about your own team ---------------- */
var chatLog=[], chatBusy=false;
function chatOpen(seed){
  $("#chatpanel").hidden=false;
  document.body.classList.add("chaton");
  if(seed){ $("#chatinput").value=seed; }
  setTimeout(function(){ $("#chatinput").focus() },60);
  renderChat();
}
function chatClose(){ $("#chatpanel").hidden=true; document.body.classList.remove("chaton"); }
function mdLite(s){
  // deliberately small: bold, code, tables and paragraphs. No HTML passes through.
  s=esc(s);
  var out=[], rows=null;
  s.split("\n").forEach(function(line){
    if(/^\s*\|.*\|\s*$/.test(line)){
      var cells=line.replace(/^\s*\|/,"").replace(/\|\s*$/,"").split("|").map(function(c){return c.trim()});
      if(cells.every(function(c){return /^:?-{2,}:?$/.test(c)})) return;
      rows=rows||[]; rows.push(cells); return;
    }
    if(rows){ out.push(tbl(rows)); rows=null; }
    if(!line.trim()){ out.push(""); return; }
    out.push("<p>"+line+"</p>");
  });
  if(rows) out.push(tbl(rows));
  function tbl(r){
    return '<table class="chattbl"><thead><tr>'+r[0].map(function(c){return "<th>"+c+"</th>"}).join("")+
      '</tr></thead><tbody>'+r.slice(1).map(function(row){
        return "<tr>"+row.map(function(c){return "<td>"+c+"</td>"}).join("")+"</tr>"}).join("")+
      '</tbody></table>';
  }
  return out.join("").replace(/\*\*([^*]+)\*\*/g,"<b>$1</b>").replace(/`([^`]+)`/g,"<code>$1</code>");
}
function renderChat(){
  var mm=M();
  var sp=(D.meta&&D.meta.chat)||{};
  var head='<div class="chathead"><div><b>Ask about '+esc(mm?mm.team:"this team")+'</b>'+
    '<small>'+(sp.on?('grounded in this squad · '+sp.left+' of '+sp.cap+' questions left this month')
                    :'no API key set on the server')+'</small></div>'+
    '<button class="btn ghost" id="chatx" type="button">Close</button></div>';
  var body;
  if(!sp.on){
    body='<div class="msg warn">The assistant is switched off because no '+
      '<code>ANTHROPIC_API_KEY</code> is set on the server. Add one in the Render dashboard '+
      'and restart the service.</div>';
  } else if(!chatLog.length){
    body='<div class="chatempty"><p>Ask anything about this squad. It can see your fifteen, '+
      'your budget, the fixtures, the odds and every bundle it has computed — and it will run '+
      'the real arithmetic for combinations it has not scored yet.</p>'+
      '<div class="seeds">'+
      ['Should I take the three-transfer bundle or hold?',
       'What do I actually lose by selling Haaland?',
       'Who should captain this week and how close is it?',
       'Is my bench strong enough for Bench Boost?',
       'Explain why it wants me to bench my defender'
      ].map(function(q){return '<button class="seed" type="button">'+esc(q)+'</button>'}).join("")+
      '</div></div>';
  } else {
    body=chatLog.map(function(m){
      if(m.role==="user") return '<div class="cmsg you">'+esc(m.content)+'</div>';
      if(m.error) return '<div class="msg warn">'+esc(m.error)+'</div>';
      return '<div class="cmsg bot">'+mdLite(m.content||"")+
        (m.tools&&m.tools.length?'<div class="ctool">ran '+m.tools.map(function(t){
          return esc(t.name)}).join(", ")+' against the live model</div>':'')+'</div>';
    }).join("");
  }
  if(chatBusy) body+='<div class="cmsg bot thinking">thinking…</div>';
  $("#chatpanel").innerHTML=head+'<div class="chatbody" id="chatbody">'+body+'</div>'+
    '<form class="chatform" id="chatform"><textarea id="chatinput" rows="2" '+
    'placeholder="'+(sp.on?"Ask about transfers, captaincy, who to bench…":"Unavailable")+'"'+
    (sp.on?"":" disabled")+'></textarea>'+
    '<button class="btn" type="submit"'+(sp.on&&!chatBusy?"":" disabled")+'>Ask</button></form>';
  var b=$("#chatbody"); if(b) b.scrollTop=b.scrollHeight;
}
function chatSend(text){
  if(!text||chatBusy) return;
  chatLog.push({role:"user",content:text});
  chatBusy=true; renderChat();
  fetch("/api/chat",{method:"POST",headers:{"content-type":"application/json"},
    body:JSON.stringify({entry:viewEntry,
      messages:chatLog.filter(function(m){return !m.error}).map(function(m){
        return {role:m.role,content:m.content}})})})
  .then(function(r){return r.json()})
  .then(function(d){
    chatBusy=false;
    if(d.error) chatLog.push({role:"assistant",error:d.error});
    else {
      chatLog.push({role:"assistant",content:d.reply||"(no answer)",tools:d.tools});
      if(d.spend&&D.meta) D.meta.chat=d.spend;
    }
    renderChat();
    // the spend tracker lives on a tab that is probably hidden right now, so
    // re-render it regardless -- otherwise it shows the count as of page load
    if($("#p-model")) renderModel();
  })
  .catch(function(e){ chatBusy=false;
    chatLog.push({role:"assistant",error:"Could not reach the server: "+e});
    renderChat(); });
}
document.addEventListener("click",function(e){
  if(e.target.id==="chatbtn"||e.target.closest("#chatbtn")) return chatOpen();
  if(e.target.id==="chatx") return chatClose();
  var s=e.target.closest(".seed");
  if(s){ chatSend(s.textContent); }
});
document.addEventListener("submit",function(e){
  if(e.target.id!=="chatform") return;
  e.preventDefault();
  var v=$("#chatinput").value.trim();
  $("#chatinput").value="";
  chatSend(v);
});
document.addEventListener("keydown",function(e){
  if(e.key==="Escape"&&!$("#chatpanel").hidden) chatClose();
  if(e.target&&e.target.id==="chatinput"&&e.key==="Enter"&&!e.shiftKey){
    e.preventDefault();
    var v=e.target.value.trim(); e.target.value=""; chatSend(v);
  }
});

function renderModel(){
  var w=D.meta.model, mm=M(), b=mm.budget;
  var capped=Object.keys(mm.clubCounts).filter(function(k){return mm.clubCounts[k]>=3});
  var mp=w.matchesPlayed||0;
  $("#p-model").innerHTML=priorWarning()+intro('Every player carries a number of <b>expected points</b> — '+
    'a forecast of what he will actually score, in the same units FPL awards. That is the '+
    'point of it: you can weigh a move against the −4 you pay for an extra transfer, and you '+
    'can add eleven of them up and compare formations. Tap <b>?</b> on any transfer, or open '+
    'a row on the Players tab, for one specific player’s arithmetic.')+
  '<div class="prose">'+
  '<h3>How a player’s points are built</h3>'+
  '<p>Each way FPL pays is priced separately and then added up, for one fixture:</p>'+
  '<table class="bands"><tr><th>Component</th><th>How it is worked out</th></tr>'+
  '<tr><td>Appearance</td><td>1 point for playing, 1 more for reaching 60 minutes, each '+
  'weighted by how likely that is</td></tr>'+
  '<tr><td>Goals</td><td>expected goals per 90 × minutes × 6, 6, 5 or 4 by position</td></tr>'+
  '<tr><td>Assists</td><td>expected assists per 90 × minutes × 3</td></tr>'+
  '<tr><td>Clean sheet</td><td>the Poisson chance of the opponent scoring none, × 4 for '+
  'keepers and defenders, × 1 for midfielders</td></tr>'+
  '<tr><td>Goals conceded</td><td>−1 for every 2 the club is expected to concede</td></tr>'+
  '<tr><td>Saves</td><td>saves per 90 ÷ 3, scaled by how much shooting the opponent does</td></tr>'+
  '<tr><td>Defensive actions</td><td>his hit rate × 2</td></tr>'+
  '<tr><td>Bonus and cards</td><td>his own historical rate per 90</td></tr></table>'+
  '<p>Goals and assists are scaled by how good the fixture is for his club, so the same '+
  'player is worth more at home to a poor side than away at a good one. The whole thing is '+
  'scaled by expected minutes and by whether he is fit.</p>'+
  '<p class="dim">Checked against 339 players who logged 900+ minutes last season: feeding '+
  'the formula their own realised rates reproduces their actual season points with a bias of '+
  '−0.03 points per appearance and a correlation of 0.974. The arithmetic is sound. Predicting '+
  '<i>next</i> season’s rates is the hard part, and that is the next section.</p>'+

  '<h3>Where the rates come from</h3>'+
  '<p><b>Last season, updated by this one.</b> Every rate starts from what the player did in '+
  w.priorSeason+' and moves toward this season as minutes accumulate, crossing over at about '+
  'eleven matches played.</p>'+
  '<p>This is not a guess. Testing on two full seasons, predicting a player’s points per 90 '+
  'across the rest of a season:</p>'+
  '<table class="bands"><tr><th>Predictor</th><th>Correlation</th></tr>'+
  '<tr><td>Previous season, expected goal involvements per 90</td><td><b>0.52</b></td></tr>'+
  '<tr><td>Previous season, points per 90</td><td>0.41</td></tr>'+
  '<tr><td>First two rounds of the new season, xGI per 90</td><td>0.37</td></tr>'+
  '<tr><td>First two rounds of the new season, points per 90</td><td><b>0.13</b></td></tr></table>'+
  '<p>Two things follow. Early-season form is nearly worthless and last season is not, which '+
  'is the opposite of how most people play in August. And <b>rates beat points</b> — expected '+
  'goal involvements predict better than points scored, because points carry finishing luck '+
  'and bonus noise while the underlying rate does not.</p>'+
  '<p>A related test: predicting the last nine rounds of a season, the whole season to date '+
  'beat the previous ten rounds on both measures (0.33 against 0.31 for points, 0.39 against '+
  '0.30 for xGI). <b>The longer window wins.</b> "Form over fixtures" is folk wisdom the data '+
  'does not support.</p>'+
  '<p>'+(w.priorCoverage||0)+' of the players in the game have Premier League history to draw '+
  'on. Promoted clubs, overseas signings and academy graduates do not, and they fall back to '+
  'the median for their position until they have played enough to speak for themselves.</p>'+

  '<h3>The defensive-contribution mistake</h3>'+
  '<p>An earlier version of this model weighted a defender’s defensive-actions hit rate at 35% '+
  'of his quality, and a midfielder’s at 30%, on the reasoning that it is the most repeatable '+
  'statistic in the game. It is: a player’s hit rate correlates between 0.68 and 0.98 with '+
  'itself from one half-season to the next. Nothing else comes close.</p>'+
  '<p>But repeatable is not the same as valuable. Tested against what those players went on '+
  'to score:</p>'+
  '<table class="bands"><tr><th>Position</th><th>Hit rate → future hit rate</th>'+
  '<th>Hit rate → future points</th></tr>'+
  '<tr><td>Defenders</td><td>0.684</td><td>0.043</td></tr>'+
  '<tr><td>Midfielders</td><td>0.810</td><td>−0.052</td></tr>'+
  '<tr><td>Forwards</td><td>0.980</td><td>0.041</td></tr></table>'+
  '<p>It predicts nothing, and for midfielders it points slightly the wrong way — because it '+
  'reliably identifies players who do the defensive work instead of scoring. The two points '+
  'do not make up for the goals. Here it is priced at exactly what it is worth: a hit rate '+
  'multiplied by 2 points, added to the total, and nothing more.</p>'+

  '<h3>Fixtures</h3>'+
  '<p>This no longer uses the difficulty rating printed before the season. Attacking and '+
  'defensive strength are rebuilt from goals actually scored and conceded, shrunk toward the '+
  'league average with the weight of '+w.priorMatches+' matches so one freak result in August '+
  'does not distort everything. Home advantage is a '+w.homeAdv+'× multiplier.</p>'+
  '<p>From those, each upcoming match gets an expected goals for and against, and the chance '+
  'of a clean sheet is the Poisson probability of conceding zero. The fixture term is then '+
  '<b>position-aware</b>: clean-sheet chance for goalkeepers and defenders, expected goals '+
  'scored for midfielders and forwards.</p>'+
  '<h3>The 1–5 on fixture strips</h3>'+
  '<p>Difficulty is the betting market’s view of the match, boiled down to one number: '+
  '<b>the chance of winning minus the chance of losing</b>. A match priced evenly has an '+
  'edge of zero and rates 3. The further the price tilts, the further the rating moves '+
  'from the middle.</p>'+
  '<table class="bands"><tr><th>Win chance − lose chance</th><th>Rating</th></tr>'+
  '<tr><td>+40 points or more</td><td><span class="fdrpill fdr1">1</span> kind</td></tr>'+
  '<tr><td>+15 to +40</td><td><span class="fdrpill fdr2">2</span></td></tr>'+
  '<tr><td>−15 to +15</td><td><span class="fdrpill fdr3">3</span> even</td></tr>'+
  '<tr><td>−40 to −15</td><td><span class="fdrpill fdr4">4</span></td></tr>'+
  '<tr><td>−40 or worse</td><td><span class="fdrpill fdr5">5</span> brutal</td></tr></table>'+
  '<p><b>The model’s edge is deliberately damped, and by a fitted amount.</b> After one round '+
  'a club that won 3–0 rates as the best in the league on the evidence available, which is '+
  'nonsense — so early edges are pulled toward even. The size of the correction was measured '+
  'rather than guessed: simulating seasons from known team strengths and regressing the true '+
  'edge on the model’s gives the damping that minimises error. It comes out at about 0.62 '+
  'after one round, rising to roughly 0.78 and staying there.</p>'+
  '<p>That second number is the surprising one. Even in midwinter the ratings are about a '+
  'quarter too extreme, because a fixture’s expectation multiplies two noisy strength numbers '+
  'together and the noise in both compounds. So the damping never fully lifts. An earlier '+
  'version of this app removed it entirely by the sixth round and was overconfident from then '+
  'on; a version before that damped far too hard in August and reported 3 for almost '+
  'everything. Both were wrong in measurable ways.</p>'+
  '<p>None of this touches the betting market. A bookmaker’s price already knew who was good '+
  'in week one, so priced fixtures pass through undamped and show their real number.</p>'+
  '<p>Bookmakers rarely price more than a fortnight ahead, so beyond their horizon the '+
  'same arithmetic runs on win, draw and lose probabilities taken from the ratings above. '+
  '<b>Same scale either way</b>, which is the point: a 3 in six weeks’ time means what '+
  'a 3 next Saturday means. Hover any fixture to see which source produced it, the edge '+
  'behind it, and — where the market has priced the game — what the results model would '+
  'have said instead.</p>'+
  '<p><b>Why not FPL’s own difficulty rating?</b> It is set before a ball is kicked and '+
  'barely moves. This season it never issues a 1 at all, 45% of all fixtures are labelled '+
  '3, and it frequently gives both sides of a match the same number, so the venue does not '+
  'register. It is shown in the fixture tooltip purely as a cross-check; nothing in this '+
  'app calculates with it.</p>'+
  '<p><b>Two earlier versions were wrong</b>, and it is worth saying how. Fixed thresholds '+
  'measured in goals failed because home advantage alone is worth 0.84 goals against bands '+
  '0.5 goals wide — so the rating largely reported where the match was being played. '+
  'Ranking every fixture into quintiles fixed that but made the scale relative to whichever '+
  'six weeks were in view, so a genuinely easy run could never look easy. On the edge scale '+
  'the venue is worth about 0.37 against bands 0.25–0.30 wide: it shifts a fixture one '+
  'band, which is about what playing at home is really worth.</p>'+

  '<h3>Betting odds</h3>'+
  (function(){
    var o=D.odds||{};
    if(o.status==="on"&&o.priced)
      return '<p><span class="oddsbadge">market on</span> '+o.priced+' upcoming fixture'+
        (o.priced===1?'':'s')+' are priced by the betting market, and those use the '+
        'market\u2019s expected goals rather than the ratings above. Fixtures beyond the '+
        'market\u2019s horizon fall back to results. Prices are refreshed every '+
        o.ttlHours+' hours, costing '+o.perCall+' credit'+(o.perCall===1?'':'s')+' a time'+(o.remaining?', '+esc(o.remaining)+' left on the provider\u2019s counter':'')+
        '. This app has spent <b>'+(o.creditsThisMonth||0)+' credit'+
        ((o.creditsThisMonth||0)===1?'':'s')+'</b> this month against a free allowance of '+
        '500, and cannot exceed '+(o.maxCalls*o.perCall)+' whatever happens. The Refresh button '+
        'deliberately cannot buy new odds.</p>';
    if(o.status==="error")
      return '<p><span class="oddsbadge off">market unavailable</span> Odds are configured '+
        'but could not be read ('+esc(o.detail||"")+'), so every fixture is priced from '+
        'results. Nothing is broken — this is the intended fallback.</p>';
    return '<p><span class="oddsbadge off">market off</span> No odds key is configured, so '+
      'fixtures are priced entirely from results. Betting markets absorb squad quality, '+
      'transfers and team news within minutes, and published work finds them better '+
      'calibrated than statistical models — so adding a key would improve this most in '+
      'August, when there are barely any results to learn from.</p>';
  })()+
  (function(){
    var o=D.odds||{};
    if(!(o.status==="on"&&o.priced)) return "";
    var rows=[];
    Object.keys(D.fixtures).forEach(function(sh){
      (D.fixtures[sh].runs||[]).forEach(function(r){
        if(r.src==="odds"&&r.ha==="H") rows.push({home:sh,away:r.opp,gw:r.gw,
          mk:r.xgf,fm:r.altXgf,mcs:r.cs,fcs:r.altCs,md:r.fdr,fd:r.altFdr});
      });
    });
    rows.sort(function(a,b){return a.gw-b.gw});
    if(!rows.length) return "";
    return '<h4 class="seclab" style="margin-top:18px">Check it yourself<i></i></h4>'+
      '<p>Every priced fixture below, with the number in use and what the results model '+
      'would have said instead. If the two columns differ, the market is what the ratings '+
      'are built on.</p>'+
      '<div class="tblwrap" style="margin-bottom:14px"><table><thead><tr>'+
      '<th class="num">GW</th><th>Fixture</th>'+
      '<th class="num">Market goals</th><th class="num">Results goals</th>'+
      '<th class="num">Market clean sheet</th><th class="num">Results clean sheet</th>'+
      '<th class="num">Difficulty</th></tr></thead><tbody>'+
      rows.map(function(r){
        var same = r.fm!=null && Math.abs(r.mk-r.fm)<0.005;
        return '<tr><td class="num">'+r.gw+'</td><td class="pname">'+esc(r.home)+
          ' v '+esc(r.away)+'</td>'+
          '<td class="num"><b>'+(r.mk==null?'—':r.mk.toFixed(2))+'</b></td>'+
          '<td class="num dim">'+(r.fm==null?'—':r.fm.toFixed(2))+'</td>'+
          '<td class="num"><b>'+(r.mcs==null?'—':Math.round(r.mcs*100)+'%')+'</b></td>'+
          '<td class="num dim">'+(r.fcs==null?'—':Math.round(r.fcs*100)+'%')+'</td>'+
          '<td class="num">'+r.md+(r.fd!=null&&r.fd!==r.md?' <span class="dim">(was '+
            r.fd+')</span>':'')+'</td></tr>'
      }).join("")+'</tbody></table></div>'+
      '<p class="emptynote" style="padding-top:0">Figures are for the home side. '+
      'Bold is in use.</p>';
  })()+
  '<p>Where the market is used, the three prices for a match are stripped of the '+
  'bookmaker\u2019s margin, then the pair of goal expectations that reproduces those '+
  'probabilities is solved for. Two prices carry two degrees of freedom and there are two '+
  'unknowns, so the answer is determined rather than fitted. Clean-sheet chance follows '+
  'from the same numbers.</p>'+

  '<h3>Minutes</h3>'+
  '<p>Minutes are the most reliable thing in fantasy football: they happen every week, so '+
  'they settle down long before goals do. Expected minutes come from the recent match log '+
  '(65% the last three, 35% the last five) and scale the whole rating, so a genuine starter '+
  'is never confused with someone getting twenty minutes off the bench.</p>'+

  '<h3>Where this comes from</h3>'+
  '<p>The structure follows the published work on forecasting this game. <b>OpenFPL</b> '+
  '(arXiv 2508.09992, trained on 2020-21 to 2023-24 and tested on 2024-25) uses '+
  'position-specific models fed by player, own-team and opponent features across several '+
  'lookback windows — which is why this model separates the three windows and models team '+
  'strength on both sides of a fixture. That expected goals beats raw goals as a predictor '+
  'is established in the football-analytics literature. And the Premier League’s own data '+
  'shows defensive-actions hit rates near 70% for the best specialists against roughly 40% '+
  'for attacking midfielders, which is a far more repeatable signal than goalscoring.</p>'+
  '<p>On the market: a 2026 study comparing simple models with bookmaker prices in the '+
  'Bundesliga found the odds better calibrated on both log-loss and Brier scores, which is '+
  'why they take precedence here wherever a fixture has been priced.</p>'+
  '<p><b>An honest ceiling.</b> OpenFPL is a trained ensemble on four seasons and still has '+
  'a root-mean-square error of about 5 points on the players who actually haul. This is a '+
  'hand-built heuristic, not a trained model, so treat it as a way of ranking options and '+
  'surfacing things you might miss — not as a points forecast.</p>'+

  '<h3>The assistant, and what it costs</h3>'+
  (function(){
    var c=(D.meta&&D.meta.chat)||{};
    if(!c.on) return '<p>The <b>Ask</b> button is switched off: no <code>ANTHROPIC_API_KEY</code> '+
      'is set on the server. With one, the assistant can answer questions about this squad and '+
      'run real transfer arithmetic for combinations the app has not already scored.</p>';
    var pct=Math.min(100,Math.round(100*c.questions/Math.max(1,c.cap)));
    return '<p>The <b>Ask</b> button opens an assistant that can see this squad, the fixtures, '+
      'the odds and every bundle computed here, and knows the rules of the game. When you ask '+
      'about a combination it has not scored, it calls back into the same transfer engine the '+
      'Transfers tab uses rather than guessing — so its numbers are the app’s numbers.</p>'+
      '<div class="spendgrid">'+
      '<div class="spendcell"><b>Questions this month</b><span>'+c.questions+'</span></div>'+
      '<div class="spendcell"><b>Spent</b><span>$'+(c.cost||0).toFixed(2)+'</span></div>'+
      '<div class="spendcell"><b>Per question</b><span>'+
        (c.perQuestion==null?'—':'$'+c.perQuestion.toFixed(3))+'</span></div>'+
      '<div class="spendcell"><b>Left in the cap</b><span>'+c.left+'</span></div></div>'+
      '<div class="spendbar"><i style="width:'+pct+'%"></i></div>'+
      '<p class="dim">'+c.questions+' of '+c.cap+' questions used in '+esc(c.month)+
      '. The cap is a hard stop: at '+c.cap+' the assistant switches off until the month rolls '+
      'over. Tokens so far: '+(c.inTokens||0).toLocaleString()+' in, '+
      (c.outTokens||0).toLocaleString()+' out'+
      ((c.cacheRead||0)?', '+c.cacheRead.toLocaleString()+' read from cache at a tenth of the price':'')+
      '. Priced at $'+c.priceIn+' per million in and $'+c.priceOut+' per million out'+
      (c.model?' for <code>'+esc(c.model)+'</code>':'')+'.</p>'+
      '<p class="dim">This counter lives on the server’s disk, which Render wipes on every '+
      'redeploy — so after you push an update it restarts from zero even though your real bill '+
      'does not. The Anthropic console is the authority on what you have actually spent.'+
      (c.lastError?' Last error: <b>'+esc(c.lastError)+'</b>.':'')+'</p>';
  })()+

  '<h3>Budget — '+esc(mm.team)+'</h3><p>Spending power is <b>'+m(b.total)+'</b> — '+
  m(b.squadValue)+' of squad plus '+m(b.bank)+' banked. A swap is offered only if the incoming '+
  'price fits the outgoing player’s selling price plus the bank, and the three-per-club '+
  'limit still holds.'+(capped.length?' At the cap for <b>'+esc(capped.join(", "))+'</b>.':'')+
  '</p><p>Selling price is reconstructed as purchase price plus half of any rise, which '+
  'assumes the player was bought at the season-start price. Someone bought after a rise will '+
  'really sell for less, so treat any move hinging on the last 0.2m as unconfirmed.</p>'+

  '<h3>Will he actually start?</h3>'+
  '<p>Every player carries a <b>chance of starting</b>, built from three things in order of '+
  'authority: FPL’s own availability flag, which overrides everything — a suspended player is '+
  'not starting whatever his record says; then his recent team sheets, weighted toward the '+
  'newest matches, because being dropped last week matters more than being dropped in August; '+
  'then last season’s start rate, for players who have barely featured yet.</p>'+
  '<p>Expected minutes follow from that rather than from a rolling average, which matters for '+
  'exactly the players where it is hard to call. Someone who has not featured all season no '+
  'longer shows 85 expected minutes just because last season says he was nailed on.</p>'+
  '<p>The API states outright whether a player was in the eleven, so this is his real start '+
  'record — not inferred from whether he passed 60 minutes, which mislabels every starter '+
  'hooked on the hour and every substitute brought on early for an injury.</p>'+

  '<h3>What it cannot know</h3><ul>'+
  '<li><b>Press conferences.</b> Still the single biggest lever. A manager saying on Friday '+
  'that someone is rested for a European tie does not reach the API until the player is '+
  'flagged, and by then the price has moved. The chance of starting is a base rate, not '+
  'inside information.</li>'+
  '<li>Rotation for cup and European fixtures, for the same reason.</li>'+
  '<li>Chip plans beyond what the game reports.</li>'+
  '<li>Anything tactical: a new manager, a formation change, a role change.</li></ul></div>';
}

/* ---------------- top strip + orchestration ---------------- */
function chipLabel(k){
  return {"3xc":"Triple Captain","bboost":"Bench Boost","freehit":"Free Hit",
          "wildcard":"Wildcard","manager":"Assistant Manager"}[k]||k;
}
function chipActive(mm){
  // A chip only counts as in force while the round it was played in is still
  // running. Once that round is over it is history, and history belongs on the
  // Team Sheet with the rest of the chip record -- not in a header cell that is
  // meant to say what is true right now.
  return !!(mm && mm.chip && !mm.chipSpent);
}
function chipCell(mm){
  if(chipActive(mm)) return ["Chip",chipLabel(mm.chip),"active this gameweek",""];
  var used=(mm.chipsUsed||[]).reduce(function(a,c){return a+c.used},0);
  return ["Chip","None", used?used+" played so far this season":"none played yet",""];
}
function renderStrip(){
  var mm=M(), lead=D.standings[0], gap=lead?lead.total-mm.total:null;
  $("#strip").innerHTML=[
    ["League rank",mm.rank+" / "+D.standings.length,
      gap===null?"":(gap===0?"leading":gap+" behind "+lead.team),gap===0?"pos":""],
    ["Total points",mm.total,"GW: "+mm.gw+" pts",""],
    ["Overall rank",mm.overallRank?mm.overallRank.toLocaleString():"—","worldwide",""],
    ["Squad value",m(mm.budget.squadValue),"selling prices",""],
    ["In the bank",m(mm.budget.bank),"spendable now",mm.budget.bank<1?"neg":""],
    chipCell(mm)
  ].map(function(t){return '<div class="tile"><span class="k">'+esc(t[0])+
    '</span><span class="v '+t[3]+'">'+esc(t[1])+'</span><span class="s">'+esc(t[2])+
    '</span></div>'}).join("");
}
function renderAll(){
  renderStrip(); renderHome(); renderSquad(); renderSheet(); renderTx(); renderClubs();
  renderPlayersShell(); renderCap(); renderLeague(); renderModel();
}
function bootUI(){
  $("#eyebrow").textContent=(D.meta.gwName||("Gameweek "+D.meta.gw))+
    " · Fantasy Premier League";
  $("#teamname").textContent="FPL Dugout";
  $("#byline").textContent=D.league?D.league.name:"";
  $("#livedot").innerHTML='<b></b>'+(D.meta.live?"live":"mock data")+" · "+
    esc(D.meta.fetched);
  $("#livedot").className=D.meta.live?"livedot":"livedot stale";
  $("#foot").innerHTML="Live from the official FPL API · fetched "+esc(D.meta.fetched)+
    " · cached briefly to avoid hammering their servers. Press Refresh for a new pull.";
  if(D.standings.length>1) showPicker();
  else showApp(D.myEntry);
}

/* ---------------- events ---------------- */
$("#refresh").addEventListener("click",function(){
  fetch("/api/refresh").then(load).catch(load);
});
$("#changeteam").addEventListener("click",function(){
  showPicker(); window.scrollTo({top:0});
});
document.addEventListener("click",function(e){
  if(!e.target.closest) return;
  var go=e.target.closest("[data-go]");
  if(go){goTab(go.dataset.go); return}
  var pk=e.target.closest("[data-pick]");
  if(pk){showApp(Number(pk.dataset.pick)); window.scrollTo({top:0}); return}
  var qm=e.target.closest("[data-explain]");
  if(qm){
    var box=document.getElementById("ex-"+qm.dataset.explain);
    if(box){
      var opening=box.hidden;
      if(opening&&!box.innerHTML) box.innerHTML=explainHTML(P(Number(qm.dataset.explain)));
      box.hidden=!opening;
      qm.setAttribute("aria-expanded",String(opening));
    }
    return;
  }
  var tq=e.target.closest("[data-tx]");
  if(tq){
    var tbox=document.getElementById("tx-"+tq.dataset.tx);
    if(tbox){
      var opening=tbox.hidden;
      if(opening&&!tbox.innerHTML)
        tbox.innerHTML=explainTransfer(M().transfers[Number(tq.dataset.tx)]);
      tbox.hidden=!opening;
      tq.setAttribute("aria-expanded",String(opening));
    }
    return;
  }
  var row=e.target.closest("[data-row]");
  if(row){
    var id=Number(row.dataset.row);
    openPlayer=(openPlayer===id)?null:id;
    renderPlayerRows();
    return;
  }
  var c=e.target.closest(".chip");
  if(c){detailFor(Number(c.dataset.id)); return}
  var lk=e.target.closest("[data-look]");
  if(lk){
    detailFor(Number(lk.dataset.look));
    all(".tab").forEach(function(x){
      x.setAttribute("aria-selected",String(x.dataset.p==="squad"))});
    TABS.forEach(function(k){
      document.getElementById("p-"+k).hidden=(k!=="squad")});
    $("#picker").hidden=true;
    window.scrollTo({top:0,behavior:"smooth"});
    return;
  }
  var gwb=e.target.closest("[data-gw]");
  if(gwb&&gwb.dataset.gw){gwView=Number(gwb.dataset.gw); renderClubs(); return}
  var cb=e.target.closest("[data-club]");
  if(cb){
    curClub=Number(cb.dataset.club); renderClubs();
    var d=$("#clubdetail"); if(d) d.scrollIntoView({behavior:"smooth",block:"start"});
    return;
  }
  var mg=e.target.closest(".mgrbtn");
  if(mg){var r=document.getElementById("sq-"+mg.dataset.entry); if(r) r.hidden=!r.hidden}
});
all(".tab").forEach(function(t){
  t.addEventListener("click",function(){
    all(".tab").forEach(function(x){x.setAttribute("aria-selected",String(x===t))});
    TABS.forEach(function(k){
      document.getElementById("p-"+k).hidden=(k!==t.dataset.p)});
    $("#picker").hidden=true;
  });
});
load();
})();
</script>
</body>
</html>
"""


def warm(entry_id, league_id):
    """Pre-fetch in the background. A cold start makes ~20 upstream calls; doing
    them before anyone asks keeps the first page load quick."""
    try:
        t0 = time.time()
        build_payload(entry_id, league_id)
        print("  warmed cache in %.1fs" % (time.time() - t0))
    except Exception as e:  # noqa: BLE001
        print("  warm-up failed (%s) - the app still runs, it will retry on "
              "the first request" % e)


def main():
    ap = argparse.ArgumentParser(description="Live FPL dashboard.")
    ap.add_argument("--entry", type=int, default=ENTRY_ID, help="your FPL team ID")
    ap.add_argument("--league", type=int, default=LEAGUE_ID, help="classic league ID")
    ap.add_argument("--port", type=int, default=PORT)
    ap.add_argument("--host", default=HOST)
    ap.add_argument("--no-browser", action="store_true")
    ap.add_argument("--insecure", action="store_true",
                    help="skip HTTPS certificate verification (last resort)")
    a = ap.parse_args()

    global INSECURE
    INSECURE = a.insecure
    if INSECURE:
        print("\n  WARNING: certificate verification is OFF (--insecure).")

    Handler.entry_id, Handler.league_id = a.entry, a.league
    url = "http://localhost:%d" % a.port
    try:
        srv = ThreadingHTTPServer((a.host, a.port), Handler)
    except OSError as e:
        print("Could not start on port %d (%s)." % (a.port, e))
        print("Something else is using it. Try:  python3 %s --port %d"
              % (os.path.basename(__file__), a.port + 1))
        return 1

    print("\n  FPL Dugout")
    print("  entry %d  ·  league %d" % (a.entry, a.league))
    print("  listening on %s:%d" % (a.host, a.port))
    if not ON_HOST:
        print("  %s" % url)
    print("  password protection: %s" % ("on" if PASSWORD else "off"))
    print("  Data is fetched live from the FPL API and cached for %ds.\n" % CACHE_TTL)
    threading.Thread(target=warm, args=(a.entry, a.league), daemon=True).start()
    if not a.no_browser and not ON_HOST:
        threading.Timer(0.8, lambda: webbrowser.open(url)).start()
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        print("\n  stopped.\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
