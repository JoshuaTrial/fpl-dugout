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
W_PRIOR, W_OBS, W_FIX = 0.55, 0.25, 0.20
POS = {1: "GK", 2: "DEF", 3: "MID", 4: "FWD"}
DC_THRESH = {"GK": 999, "DEF": 10, "MID": 12, "FWD": 12}
FIX_GWS = 6


def build_fixture_map(fixtures, teams, from_gw):
    gws = list(range(from_gw, from_gw + FIX_GWS))
    out = {}
    short = {t["id"]: t["short_name"] for t in teams}
    for t in teams:
        runs, diffs = [], []
        for gw in gws:
            games = [f for f in fixtures if f.get("event") == gw
                     and (f["team_h"] == t["id"] or f["team_a"] == t["id"])]
            if not games:
                runs.append({"gw": gw, "opp": None, "ha": "-", "fdr": None})
                continue
            for f in games:
                home = f["team_h"] == t["id"]
                opp = short.get(f["team_a"] if home else f["team_h"], "?")
                fdr = f.get("team_h_difficulty" if home else "team_a_difficulty") or 3
                runs.append({"gw": gw, "opp": opp, "ha": "H" if home else "A",
                             "fdr": int(fdr)})
                diffs.append(int(fdr))
        out[t["id"]] = {"runs": runs,
                        "avgFdr": round(sum(diffs) / len(diffs), 2) if diffs else None}
    return out


def score_players(boot, fixmap):
    els = boot["elements"]
    teams = {t["id"]: t for t in boot["teams"]}

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
        e["_dc90"] = num(e.get("defensive_contribution_per_90"))
        e["_owned"] = num(e.get("selected_by_percent"))
        fm = fixmap.get(e["team"], {})
        e["_avgFdr"] = fm.get("avgFdr")

        st = e.get("status", "a")
        chance = e.get("chance_of_playing_next_round")
        if st == "a":
            av = 1.0
        elif chance is not None:
            av = num(chance) / 100.0
        else:
            av = {"d": 0.5, "i": 0.1, "s": 0.1, "u": 0.05}.get(st, 0.5)
        e["_avail"] = av

        if mins >= 90:
            mf = 1.0
        elif mins >= 60:
            mf = 0.92
        elif mins >= 20:
            mf = 0.78
        elif mins > 0:
            mf = 0.68
        else:
            mf = 0.58
        e["_minfac"] = mf

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

    # percentiles are computed within position
    for pos in ("GK", "DEF", "MID", "FWD"):
        grp = [e for e in els if e["_pos"] == pos]
        if not grp:
            continue
        worst_xgc = max([e["_xgc90"] for e in grp if e["_xgc90"] is not None] or [0])
        prior = pct_ranks([num(e.get("now_cost")) for e in grp])
        xgi = pct_ranks([e["_xgi90"] for e in grp])
        ict = pct_ranks([e["_ict90"] for e in grp])
        dc = pct_ranks([min(e["_dc90"] / DC_THRESH[pos], 1.5) for e in grp])
        safe = pct_ranks([(e["_xgc90"] if e["_xgc90"] is not None else worst_xgc)
                          for e in grp])
        for i, e in enumerate(grp):
            defsafe = 1 - safe[i]
            if pos == "GK":
                obs = 0.35 * ict[i] + 0.65 * defsafe
            elif pos == "DEF":
                obs = 0.25 * xgi[i] + 0.30 * dc[i] + 0.45 * defsafe
            elif pos == "MID":
                obs = 0.55 * xgi[i] + 0.25 * dc[i] + 0.20 * ict[i]
            else:
                obs = 0.70 * xgi[i] + 0.30 * ict[i]
            fixp = 0.5 if e["_avgFdr"] is None else max(0.0, min(1.0, (5 - e["_avgFdr"]) / 4))
            e["_prior"] = prior[i]
            e["_obs"] = obs
            e["_fix"] = fixp
            e["_score"] = round(
                100 * (W_PRIOR * prior[i] + W_OBS * obs + W_FIX * fixp)
                * e["_avail"] * e["_minfac"] + e["_sp"], 1)
    return els


# Fixture ease multiplier per match. An average run of five FDR-3 games sums to 5.0,
# so the normalised factor is 1.0 and a player's projection equals his base quality.
EASE = {1: 1.30, 2: 1.15, 3: 1.00, 4: 0.85, 5: 0.70}
HORIZON = 5


def run_window(team_id, fixmap, k=HORIZON):
    """The fixtures in a team's next k gameweeks. Blanks contribute nothing,
    doubles contribute twice -- both fall out of this naturally."""
    runs = fixmap.get(team_id, {}).get("runs", [])
    gws = sorted(set(r["gw"] for r in runs))[:k]
    sel = [r for r in runs if r["gw"] in gws and r.get("opp")]
    mult = sum(EASE.get(r.get("fdr"), 1.0) for r in sel)
    return sel, mult


def base_score(e):
    """Quality with the fixture term removed -- what the player is, not who he plays."""
    wsum = W_PRIOR + W_OBS
    return (100 * (W_PRIOR * e.get("_prior", 0) + W_OBS * e.get("_obs", 0)) / wsum) \
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
    done = [f for f in fixtures
            if f.get("finished") and f.get("team_h_score") is not None
            and f.get("team_a_score") is not None]
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
        "expl": {"prior": round(e.get("_prior", 0), 3),
                 "obs": round(e.get("_obs", 0), 3),
                 "fix": round(e.get("_fix", 0), 3),
                 "avail": round(e.get("_avail", 1), 2),
                 "minfac": round(e.get("_minfac", 1), 2),
                 "sp": e.get("_sp", 0.0),
                 "xgiR": round(e.get("_xgi90", 0), 2),
                 "ictR": round(e.get("_ict90", 0), 2),
                 "xgcR": (round(e["_xgc90"], 2) if e.get("_xgc90") is not None else None)},
    }


def reasons(p):
    out = []
    if p["pen"] == 1:
        out.append("first-choice penalties")
    if p["xgi90"] >= 0.45:
        out.append("xGI/90 %.2f" % p["xgi90"])
    thr = DC_THRESH.get(p["pos"], 12)
    if p["pos"] != "GK" and p["dc90"] >= thr:
        out.append("cleared DEFCON (%d vs %d)" % (int(p["dc90"]), thr))
    if p["avgFdr"] is not None and p["avgFdr"] <= 2.85:
        out.append("kind run (FDR %.2f)" % p["avgFdr"])
    if p["owned"] <= 5 and p["score"] >= 70:
        out.append("differential (%.1f%% owned)" % p["owned"])
    if p["mins"] >= 90 and p["starts"] >= 1:
        out.append("%d mins, %d start%s" % (p["mins"], p["starts"],
                                            "" if p["starts"] == 1 else "s"))
    if p["ck"] == 1 or p["fk"] == 1:
        out.append("on set pieces")
    return out[:3]


# ----------------------------------------------------------------------------
# assembling the payload
# ----------------------------------------------------------------------------
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

    teams = {t["id"]: t for t in boot["teams"]}
    fixmap = build_fixture_map(fixtures, boot["teams"], plan_from)
    els = score_players(boot, fixmap)
    by_id = {e["id"]: e for e in els}
    players = [slim(e, teams) for e in els]
    pslim = {p["id"]: p for p in players}
    for e in els:
        sel, mult = run_window(e["team"], fixmap)
        bs = base_score(e)
        pr = pslim[e["id"]]
        pr["base"] = round(bs, 1)
        pr["mult5"] = round(mult, 2)
        pr["games5"] = len(sel)
        pr["proj5"] = round(bs * mult / HORIZON, 1)
        e["_proj5"] = bs * mult / HORIZON

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

    picks_by_entry, entry_by_entry = {}, {}
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

        managers[str(entry)] = {
            "entry": entry, "team": r["entry_name"], "mgr": r["player_name"],
            "rank": r["rank"], "total": r["total"], "gw": r["event_total"],
            "overallRank": ent.get("summary_overall_rank"),
            "value": value, "bank": bank, "chip": (rp or {}).get("active_chip"),
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
            "gw": gw, "planFrom": plan_from,
            "gwName": (cur or nxt or events[0]).get("name"),
            "deadline": (nxt or {}).get("deadline_time"),
            "fetched": time.strftime("%Y-%m-%d %H:%M:%S"),
            "live": not bool(MOCK_DIR),
            "model": {"wPrior": W_PRIOR, "wObs": W_OBS, "wFix": W_FIX},
        },
        "myEntry": entry_id,
        "league": league,
        "standings": [{"rank": r["rank"], "entry": r["entry"], "team": r["entry_name"],
                       "mgr": r["player_name"], "gw": r["event_total"], "total": r["total"],
                       "value": managers[str(r["entry"])]["value"],
                       "bank": managers[str(r["entry"])]["bank"],
                       "chip": managers[str(r["entry"])]["chip"]}
                      for r in rows if str(r["entry"]) in managers],
        "managers": managers,
        "players": players,
        "clubs": clubs,
        "table": league_table(fixtures, boot["teams"]),
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
            return self._send(200, json.dumps({"ok": True}), "application/json")
        self._send(404, "not found", "text/plain; charset=utf-8")


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
main{padding-top:20px}

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
      <button class="btn ghost" id="refresh" type="button">Refresh</button>
    </div>
    <div class="strip" id="strip"></div>
    <div class="tabs" role="tablist" id="tabs">
      <button class="tab" role="tab" aria-selected="true" data-p="squad">My Team</button>
      <button class="tab" role="tab" aria-selected="false" data-p="tx">Transfers</button>
      <button class="tab" role="tab" aria-selected="false" data-p="clubs">Clubs</button>
      <button class="tab" role="tab" aria-selected="false" data-p="players">Players</button>
      <button class="tab" role="tab" aria-selected="false" data-p="cap">Captaincy</button>
      <button class="tab" role="tab" aria-selected="false" data-p="league">League</button>
      <button class="tab" role="tab" aria-selected="false" data-p="model">Model</button>
    </div>
  </div>
</div>
<main class="wrap">
  <div id="boot" class="loading">Fetching live data from the FPL API...</div>
  <div id="app" hidden>
    <div id="banner"></div>
    <section id="picker" hidden></section>
    <section class="panel" id="p-squad">
      <div class="squadgrid">
        <div><div class="pitch" id="pitch"></div></div>
        <div class="card dt" id="detail"></div>
      </div>
    </section>
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
var TABS=["squad","tx","clubs","players","cap","league","model"];
var D=null, byId={}, viewEntry=null, curClub=null,
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
  var cls="bw"+(lg?" lg":"");
  if(!code) return '<span class="'+cls+'"><span class="bfb imgfb" style="display:block">'+
    esc(short)+'</span></span>';
  return '<span class="'+cls+'"><img class="fbimg" src="'+BADGE+code+'.png" alt="">'+
    '<span class="bfb imgfb">'+esc(short)+'</span></span>';
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
      '<span class="o">—</span><span class="n">blank</span></div>';
    return '<div class="fx '+fdrCls(r.fdr)+'"><span class="g">GW'+r.gw+' '+r.ha+'</span>'+
      '<span class="o">'+esc(r.opp)+'</span><span class="n">FDR '+r.fdr+'</span></div>'
  }).join("")+'</div>';
}
function statGrid(p){
  var rows=[["Pts",p.pts],["Mins",p.mins],["Starts",p.starts],["Form",p.form.toFixed(1)],
    ["PPG",p.ppg.toFixed(1)],["Goals",p.goals],["Assists",p.assists],["Bonus",p.bonus],
    ["xG",p.xg.toFixed(2)],["xA",p.xa.toFixed(2)],["xGI/90",p.xgi90.toFixed(2)],
    ["xGC",p.xgc.toFixed(2)],["ICT",p.ict],["BPS",p.bps],["DefCon",p.dc],
    ["Owned",p.owned+"%"]];
  return '<div class="stats">'+rows.map(function(r){
    return '<div class="st"><span class="k">'+esc(r[0])+'</span><span class="v">'+
      esc(r[1])+'</span></div>'}).join("")+'</div>';
}
function pillsFor(p){
  var o=[];
  if(p.status!=="a") o.push('<span class="pill '+(p.status==="d"?"warn":"bad")+'">'+
    esc(p.news||"unavailable")+'</span>');
  if(p.pen===1) o.push('<span class="pill good">Penalties · 1st</span>');
  else if(p.pen===2) o.push('<span class="pill">Penalties · 2nd</span>');
  if(p.ck===1) o.push('<span class="pill">Corners · 1st</span>');
  if(p.fk===1) o.push('<span class="pill">Free-kicks · 1st</span>');
  if(p.avgFdr!=null) o.push('<span class="pill'+(p.avgFdr<=2.8?" good":p.avgFdr>=3.4?" bad":"")+
    '">Next 6 · FDR '+p.avgFdr.toFixed(2)+'</span>');
  if(p.owned<=5) o.push('<span class="pill">Differential · '+p.owned+'% owned</span>');
  if(p.costChange!==0) o.push('<span class="pill">Price '+(p.costChange>0?"+":"")+
    (p.costChange/10).toFixed(1)+'m since start</span>');
  if(inSquad(p.id)) o.push('<span class="pill good">In this squad</span>');
  return o.length?'<div class="pills">'+o.join("")+'</div>':"";
}

/* ---------------- the score, explained ---------------- */
function obsSentence(p){
  var x=p.expl;
  if(p.pos==="GK") return "For keepers that is 65% how few chances the club concedes ("+
    (x.xgcR==null?"no minutes yet":"xGC "+x.xgcR.toFixed(2)+" per 90")+") and 35% ICT.";
  if(p.pos==="DEF") return "For defenders that is 45% clean-sheet likelihood ("+
    (x.xgcR==null?"no minutes yet":"xGC "+x.xgcR.toFixed(2)+" per 90")+
    "), 30% defensive contribution rate ("+p.dc90.toFixed(1)+" per 90 against a threshold of 10) "+
    "and 25% attacking threat.";
  if(p.pos==="MID") return "For midfielders that is 55% xGI per 90 ("+p.xgi90.toFixed(2)+
    "), 25% defensive contribution ("+p.dc90.toFixed(1)+" per 90 against a threshold of 12) "+
    "and 20% ICT.";
  return "For forwards that is 70% xGI per 90 ("+p.xgi90.toFixed(2)+") and 30% ICT.";
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
  h+=row("Price prior",x.prior.toFixed(2)+" × "+Math.round(w.wPrior*100)+"%",a.toFixed(1));
  h+=row("Observed form",x.obs.toFixed(2)+" × "+Math.round(w.wObs*100)+"%",b.toFixed(1));
  h+=row("Fixtures",x.fix.toFixed(2)+" × "+Math.round(w.wFix*100)+"%",c.toFixed(1));
  h+=row("Subtotal","",sub.toFixed(1),"sum");
  h+=row("× availability","× "+x.avail.toFixed(2),av.toFixed(1));
  h+=row("× minutes played","× "+x.minfac.toFixed(2),mn.toFixed(1));
  h+=row("+ set pieces","+ "+x.sp.toFixed(1),tot.toFixed(1));
  h+=row("Model score","",Math.round(tot),"tot");
  h+='</table><p><b>Price prior '+x.prior.toFixed(2)+'</b> means he is priced above '+
    Math.round(x.prior*100)+'% of '+esc(p.pos)+'s. With so little football played, price is '+
    'the steadiest signal available, so it carries the most weight. '+
    '<b>Observed form '+x.obs.toFixed(2)+'</b> is his percentile on what actually matters for '+
    'his position. '+esc(obsSentence(p))+' <b>Fixtures '+x.fix.toFixed(2)+'</b> comes from an '+
    'average FDR of '+(p.avgFdr==null?"—":p.avgFdr.toFixed(2))+' over the next six.';
  if(x.avail<1) h+=' Availability is below 1.00 because he is flagged, which scales the whole '+
    'score down.';
  if(x.minfac<1) h+=' Minutes security is '+x.minfac.toFixed(2)+' because he has played '+
    p.mins+' minutes so far.';
  if(x.sp>0) h+=' The set-piece bonus of '+x.sp.toFixed(1)+' is added flat, after the multipliers.';
  h+='</p>';
  return h;
}

/* ---------------- My Team ---------------- */
function altBlock(o,ownerLabel){
  var p=P(o.id), up=o.delta>0;
  return '<div class="altrow"><button class="alt" data-look="'+o.id+'">'+
    '<span class="d '+(up?"up":"dn")+'">'+(up?"+":"")+o.delta.toFixed(1)+
    '<small>score</small></span><span class="body"><span class="t">'+esc(p.name)+
    ' <em>'+esc(p.club)+' · '+m(p.price)+(o.spare>0?' · '+m(o.spare)+' left':'')+
    '</em></span><span class="w">'+esc((o.why||[]).join(" · ")||"ranked on model score")+
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
    '<div class="scorebox"><div class="n">'+Math.round(p.score)+'</div>'+
    '<div class="l">Model score</div></div></div>';
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
    m(mm.budget.bank)+' bank'+(mm.chip?' · '+esc(mm.chip):'')+'</span></div>';
  h+='<div class="field">';
  ["GK","DEF","MID","FWD"].forEach(function(pos){
    var r=st.filter(function(p){return p.pos===pos});
    if(r.length) h+='<div class="row">'+r.map(chip).join("")+'</div>';
  });
  h+='</div><div class="benchlab"><i></i><span>Bench</span><i></i></div>';
  h+='<div class="row">'+bn.map(chip).join("")+'</div>';
  $("#pitch").innerHTML=h;
  wireImgs($("#pitch"));
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
    x.setAttribute("aria-selected",String(x.dataset.p==="squad"))});
  TABS.forEach(function(k){
    document.getElementById("p-"+k).hidden=(k!=="squad")});
}

/* ---------------- Clubs ---------------- */
function tableHTML(){
  var t=D.table||[];
  if(!t.length) return "";
  var played=t.reduce(function(a,r){return a+r.p},0);
  return '<h4 class="seclab">Premier League table<i></i></h4>'+
    '<p class="emptynote" style="padding-top:0">Built from '+(played/2)+
    ' completed matches. The FPL API returns zeros for played, won and points, and its '+
    '"position" field is stale seeding, so this is computed from actual results.</p>'+
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
function renderClubs(){
  var counts=M().clubCountsById||{};
  $("#p-clubs").innerHTML=tableHTML()+
    '<h4 class="seclab">Squads<i></i></h4><div class="clubgrid">'+D.clubs.map(function(c){
    var owned=counts[String(c.id)]||0;
    return '<button class="clubbtn" data-club="'+c.id+'" aria-pressed="'+(curClub===c.id)+'">'+
      badgeHTML(c.code,c.short,false)+'<b>'+esc(c.short)+'</b><em>'+esc(c.name)+'</em>'+
      '<em>FDR '+(c.avgFdr==null?"—":c.avgFdr.toFixed(2))+(owned?' · '+owned+' owned':'')+
      '</em></button>'
  }).join("")+'</div><div id="clubdetail"></div>';
  wireImgs($("#p-clubs"));
  if(curClub!=null) renderClubDetail(curClub);
  else $("#clubdetail").innerHTML='<p class="emptynote">Pick a club to see every FPL-listed '+
    'player in that squad, ranked by model score.</p>';
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
    '<th class="num">xGI/90</th><th class="num">DefCon/90</th><th class="num">Owned</th>'+
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
        p.owned+'%</td><td class="num"><b>'+Math.round(p.score)+'</b></td><td class="dim">'+
        esc(notes.join(", "))+'</td></tr>'
    }).join("")+'</tbody></table></div></div>';
  $("#clubdetail").innerHTML=h;
  wireImgs($("#clubdetail"));
}

/* ---------------- Players ---------------- */
var COLS=[["name","Player",0],["club","Club",0],["pos","Pos",0],["price","Price",1],
  ["pts","Pts",1],["mins","Mins",1],["form","Form",1],["xgi90","xGI/90",1],
  ["dc90","DefCon/90",1],["owned","Owned",1],["score","Score",1]];
function renderPlayersShell(){
  $("#p-players").innerHTML=
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
    ' · model score '+Math.round(p.score)+'</div>'+pillsFor(p)+'</div></div>'+
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
      '</td><td class="num">'+p.owned+'%</td><td class="num"><b>'+Math.round(p.score)+
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
  $("#p-cap").innerHTML='<div class="msg info">Ranked from '+esc(mm.team)+
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
        '<span class="o">'+esc(f.opp||"—")+'</span><span class="n">FDR '+
        (f.fdr==null?"—":f.fdr)+'</span></div></div><div class="capbars">'+
        bar("Model score",p.score,maxScore,Math.round(p.score))+
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

/* ---------------- Transfers ---------------- */
function explainTransfer(t){
  var i=P(t.inId), o=P(t.outId);
  function line(p,lab){
    return '<tr><td>'+lab+' '+esc(p.name)+'</td><td class="n">base '+p.base.toFixed(1)+
      ' × '+p.mult5.toFixed(2)+'/'+D.horizon+'</td><td class="r">'+p.proj5.toFixed(1)+'</td></tr>';
  }
  var h='<h5>How the five-match impact was built</h5><table class="calc">'+
    line(i,"In —")+line(o,"Out —")+
    '<tr class="tot"><td>Five-match impact</td><td class="n"></td><td class="r">'+
    (t.gain5>0?"+":"")+t.gain5.toFixed(1)+'</td></tr></table>'+
    '<p><b>Base</b> is the model score with the fixture term stripped out — what the player is, '+
    'independent of who he faces. <b>The multiplier</b> weights each of the next '+D.horizon+
    ' matches by difficulty (FDR 1 counts 1.30, 3 counts 1.00, 5 counts 0.70), so a blank '+
    'gameweek adds nothing and a double counts twice. Divided by '+D.horizon+
    ', an ordinary run of five average fixtures leaves the base untouched.</p>'+
    '<p><b>This number is an index, not points.</b> It says which move is worth more than '+
    'which, not how many FPL points you would gain — so do not weigh it directly against '+
    'the −4 cost of an extra transfer.</p>';
  return h;
}
function renderTx(){
  var mm=M(), tx=mm.transfers||[];
  var head='<div class="msg info"><b>Ranked by what each swap does over the next '+D.horizon+
    ' matches</b>, not just raw quality. A player\u2019s rating is stripped of its fixture '+
    'term, then re-weighted by the actual difficulty of his next '+D.horizon+
    ' games — so an easy run lifts a move and a blank gameweek drags it down. Every swap '+
    'shown is affordable on '+esc(mm.team)+'\u2019s bank and keeps the three-per-club limit. '+
    'The impact figure is a relative index, not a points forecast.</div>';
  if(!tx.length){
    $("#p-tx").innerHTML=head+'<p class="emptynote">No swap improves this squad over the '+
      'next '+D.horizon+' matches within budget. That is a good sign.</p>';
    return;
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
      '<span>'+D.horizon+'-match impact</span></span></div>'+
      '<div class="tmeta"><span class="pill">Model score '+(t.delta>0?"+":"")+
      t.delta.toFixed(1)+'</span><span class="pill'+(t.cost<=0?" good":"")+'">'+
      (t.cost>0?'Costs '+m(t.cost):t.cost<0?'Frees '+m(-t.cost):'Same price')+'</span>'+
      '<span class="pill">'+m(t.spare)+' left over</span>'+
      (t.why&&t.why.length?'<span class="pill">'+esc(t.why.join(" · "))+'</span>':'')+
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
  var h='<div class="tblwrap"><table><thead><tr><th class="num">#</th><th>Team</th>'+
    '<th>Manager</th><th class="num">GW</th><th class="num">Total</th><th class="num">Gap</th>'+
    '<th class="num">Value</th><th class="num">Bank</th></tr></thead><tbody>'+
    D.standings.map(function(s){
      var sm=D.managers[String(s.entry)];
      return '<tr'+(s.entry===viewEntry?' class="me"':'')+'><td class="num">'+s.rank+'</td>'+
        '<td><button class="mgrbtn" data-entry="'+s.entry+'">'+esc(s.team)+'</button>'+
        (s.chip?' <span class="pill warn">'+esc(s.chip)+'</span>':'')+'</td><td>'+esc(s.mgr)+
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
        (p.score>=70?"up":"dn")+'">'+Math.round(p.score)+'<small>score</small></span>'+
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
        Math.round(p.score)+' · '+p.pts+' pts · '+esc((x.owners||[]).join(", "))+
        '</span></span></button>'
    }).join("")+'</div></div>';
  $("#p-league").innerHTML=h;
}

/* ---------------- Model ---------------- */
function renderModel(){
  var w=D.meta.model, mm=M(), b=mm.budget;
  var capped=Object.keys(mm.clubCounts).filter(function(k){return mm.clubCounts[k]>=3});
  $("#p-model").innerHTML='<div class="prose">'+
  '<h3>What the score means</h3><p>Every player gets a 0-100 score. It ranks fit against what '+
  'predicts FPL returns — it is not a points projection. Click the <b>?</b> on any '+
  'transfer suggestion, or open any row on the Players tab, to see the arithmetic for that '+
  'specific player.</p>'+
  '<div class="wbar"><span class="wseg" style="flex:'+w.wPrior+';background:var(--accent)">'+
  'Price prior '+Math.round(w.wPrior*100)+'%</span><span class="wseg" style="flex:'+w.wObs+
  ';background:var(--good)">Observed form '+Math.round(w.wObs*100)+'%</span>'+
  '<span class="wseg" style="flex:'+w.wFix+';background:var(--warn)">Fixtures '+
  Math.round(w.wFix*100)+'%</span></div>'+
  '<p>That result is multiplied by availability and minutes security, then a set-piece bonus '+
  'is added: 6 for first-choice penalties, 2 for second, 2 each for first-choice corners or '+
  'direct free-kicks.</p>'+
  '<h3>Observed form, by position</h3><ul>'+
  '<li><b>GK</b> — 65% team defensive solidity (xGC per 90), 35% ICT.</li>'+
  '<li><b>DEF</b> — 45% solidity, 30% defensive contribution, 25% attacking threat.</li>'+
  '<li><b>MID</b> — 55% xGI per 90, 25% defensive contribution, 20% ICT.</li>'+
  '<li><b>FWD</b> — 70% xGI per 90, 30% ICT.</li></ul>'+
  '<p>Defensive contribution uses the 2026/27 thresholds: 10 combined clearances, blocks, '+
  'interceptions and tackles for a defender; 12 including recoveries for a midfielder or '+
  'forward. Either is worth 2 points, once per match.</p>'+
  '<h3>Why price carries the most weight early</h3>'+
  '<p>Price encodes the market’s season-long expectation and is far steadier than a few '+
  'matches of xG, so observed rates are shrunk toward it. Because alternatives are filtered to '+
  'what the budget reaches, you are comparing similarly priced players and the prior largely '+
  'cancels — the visible gap comes from form, fixtures and availability. Shift weight '+
  'toward observed rates around GW6-8.</p>'+
  '<h3>The Transfers tab</h3><p>That tab ranks swaps by a different number. A player\u2019s '+
  'rating has its fixture term stripped out, leaving base quality; that is then re-weighted '+
  'by the difficulty of his next '+D.horizon+' matches (FDR 1 counts 1.30, 3 counts 1.00, '+
  '5 counts 0.70), with blanks adding nothing and doubles counting twice. The gap between '+
  'the incoming and outgoing player is the impact. It is an index for comparing moves — '+
  '<b>not a points forecast</b>, so it should not be weighed against the −4 cost of an '+
  'extra transfer.</p>'+
  '<h3>Budget — '+esc(mm.team)+'</h3><p>Spending power is <b>'+m(b.total)+'</b> — '+
  m(b.squadValue)+' of squad plus '+m(b.bank)+' banked. A swap is offered only if the incoming '+
  'price fits the outgoing player’s selling price plus the bank, and the three-per-club '+
  'limit still holds.'+(capped.length?' At the cap for <b>'+esc(capped.join(", "))+'</b>.':'')+
  '</p><p>Selling price is reconstructed as purchase price plus half of any rise, which assumes '+
  'the player was bought at the season-start price. Someone bought after a rise will really '+
  'sell for less than shown, so treat any move hinging on the last 0.2m as unconfirmed.</p>'+
  '<h3>What it cannot know</h3><ul>'+
  '<li>Press-conference team news — always check before the deadline.</li>'+
  '<li>Rotation for cup and European fixtures.</li>'+
  '<li>Whether a player is genuinely nailed on.</li>'+
  '<li>Chip plans beyond what the API reports.</li></ul></div>';
}

/* ---------------- top strip + orchestration ---------------- */
function renderStrip(){
  var mm=M(), lead=D.standings[0], gap=lead?lead.total-mm.total:null;
  $("#strip").innerHTML=[
    ["League rank",mm.rank+" / "+D.standings.length,
      gap===null?"":(gap===0?"leading":gap+" behind "+lead.team),gap===0?"pos":""],
    ["Total points",mm.total,"GW: "+mm.gw+" pts",""],
    ["Overall rank",mm.overallRank?mm.overallRank.toLocaleString():"—","worldwide",""],
    ["Squad value",m(mm.budget.squadValue),"selling prices",""],
    ["In the bank",m(mm.budget.bank),"spendable now",mm.budget.bank<1?"neg":""],
    ["Chip",mm.chip?mm.chip:"None",mm.chip?"active this GW":"none active",""]
  ].map(function(t){return '<div class="tile"><span class="k">'+esc(t[0])+
    '</span><span class="v '+t[3]+'">'+esc(t[1])+'</span><span class="s">'+esc(t[2])+
    '</span></div>'}).join("");
}
function renderAll(){
  renderStrip(); renderSquad(); renderTx(); renderClubs(); renderPlayersShell();
  renderCap(); renderLeague(); renderModel();
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
