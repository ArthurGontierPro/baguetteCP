#!/usr/bin/env python3
"""Several ARMS of one Challenge series, side by side: per-edition counts, then pairwise readings.

Written for M10-search-strategy-T5 (the measurement that chose the search defaults) and
M9-no-proof-T3 (the measurement of runs without proof logging).

    arms_compare.py <repo> NAME=DIR[@SOLVER] [NAME=DIR[@SOLVER] ...]
                    [--pair X Y ...] [--trust NAME] [--tsv OUT]

<repo> is a baguette checkout: its bench/challenge/<YEAR>.lst give each instance its family.
An arm is a directory holding one scripts/compare_run.sh output per edition
(<arm>/<YEAR>/results.tsv, log/<id>.baguette.{err,rss}), all arms over the same instance lists
and the same .fzn files. The arm wrappers of D-0185 (the sixteen editions run in three arms of
one binary) and their successor bench/series/solver_wrap.sh run the solver under a small RSS
recorder that writes `rss_kb=N` to <proof base>.rss, and pass `--stats`, so the node count is
on stderr.

An arm reads the rows of one solver of compare_run.sh, `baguette` unless `@SOLVER` names another
(`@gcs`, `@chuffed`: the proof-logging and speed references added by M17-bench-series-T4,
D-0211, which ranks them verified answer for verified answer), its logs being
log/<id>.<SOLVER>.{err,rss}. A GCS arm's complete answers count only VERIFIED, as baguette's;
a Chuffed arm has no proof, so it must be named by --trust.

Prints, for each arm, per edition and in total: complete answers (OPT/UNSAT), how many of them
are VERIFIED, satisfaction problems solved (SAT on a model without an objective), incumbents (an
objective VALUE present; `min:-` is not one, by the addendum of D-0125, the re-run of the
sixteen editions that first counted incumbents), and the statuses. Then, for each --pair X Y
(Y read against X):

  * the status transitions X -> Y;
  * complete in one arm only, and incumbent in one arm only (id, family, both statuses);
  * on the instances complete in both: wall time ratio Y/X (median, quartiles, sums);
  * peak RSS ratio Y/X where both are >= 64 MB, and nodes per second ratio Y/X;
  * "attempts gained" by Y: X REFUSED, CAPPED or ERROR, and Y not (it searched to its limit or
    answered), the measure M9-no-proof-T3 asks for;
  * a per-instance verdict in the Challenge's ORDER (complete > better objective > nothing; two
    complete answers by time, ties within 5 % or 1 s), summed by family, so "where does Y win".

In the pairwise reading a complete answer counts only when VERIFIED (an unverified one falls back
to its incumbent, as challenge_rank.py demotes it), except in an arm named by --trust: an arm run
with --no-proof has no proof, so its complete answers are trusted, UNVERIFIED, and the caller must
say so. The per-arm table counts every OPT/UNSAT and, beside it, the VERIFIED ones.

--tsv OUT also writes one row per instance and pair (both statuses, objectives, wall times,
nodes, peak RSS and Y's verdict). Exit 0 once the tables are printed; with no arm, or -h, it
prints this text and exits 0; a malformed argument stops on a Python exception (status 1).
Standard library only; read-only over the run directories.
"""
import os, re, statistics, sys
from collections import Counter, defaultdict

YEARS = [str(y) for y in range(2011, 2027)]
R_NODES = re.compile(r"^stats: nodes\s+(\d+)", re.M)
R_LIMNODES = re.compile(r"^limit: .*?\bnodes=(\d+)", re.M)
R_RSS = re.compile(r"rss_kb=(\d+)")
INPUT = ("FLATTEN-FAIL", "NO-DATA", "INPUT-INVALID")
DIED = ("REFUSED", "CAPPED", "ERROR")


def families(repo):
    fam = {}
    for y in YEARS:
        p = os.path.join(repo, "bench/challenge/%s.lst" % y)
        if not os.path.exists(p):
            continue
        for line in open(p):
            if line.startswith("#"):
                continue
            f = line.rstrip("\n").split("\t")
            if len(f) >= 3:
                fam[f[0]] = "%s_%s" % (y, os.path.basename(os.path.dirname(f[1])))
    return fam


def read_arm(root, trust, solver="baguette"):
    rows, done = {}, {}
    for y in YEARS:
        d = os.path.join(root, y)
        tsv = os.path.join(d, "results.tsv")
        done[y] = None
        if not os.path.exists(tsv):
            continue
        done[y] = False
        for line in open(tsv, errors="replace"):
            if line.startswith("DONE-"):
                done[y] = True
                continue
            f = line.rstrip("\n").split("\t")
            if len(f) < 12 or f[1] != solver:
                continue
            r = dict(id=f[0], year=y, status=f[2], wall=f[3], obj=f[4], nsols=f[5], pbp=f[8],
                     verdict=f[9], detail=f[11], trust=trust)
            L = os.path.join(d, "log", f[0] + "." + solver)
            try:
                err = open(L + ".err", errors="replace").read()
            except OSError:
                err = ""
            m = R_NODES.findall(err) or R_LIMNODES.findall(err)
            r["nodes"] = int(m[-1]) if m else None
            try:
                r["rss"] = int(R_RSS.search(open(L + ".rss").read()).group(1))
            except (OSError, AttributeError):
                r["rss"] = None
            try:
                r["t"] = float(r["wall"])
            except ValueError:
                r["t"] = None
            rows[f[0]] = r
    return rows, done


def has_value(r):
    o = r["obj"]
    return ":" in o and o.split(":", 1)[1] not in ("-", "")


def complete(r):
    """A complete answer; in an arm not named by --trust, only a VERIFIED one (as challenge_rank)."""
    c = r["status"] in ("OPT", "UNSAT") or (r["status"] == "SAT" and r["obj"] == "-")
    return c and (r["trust"] or r["verdict"] == "VERIFIED")


def objval(r):
    k, v = r["obj"].split(":", 1)
    return k, int(v)


def q(v, fmt="%.2f"):
    v = sorted(v)
    if not v:
        return "-"
    return (fmt + " [" + fmt + ", " + fmt + "] n=%d") % (
        statistics.median(v), v[len(v) // 4], v[(3 * len(v)) // 4], len(v))


def counts(rows):
    c = Counter()
    for r in rows.values():
        s = r["status"]
        c["rows"] += 1
        c["opt_unsat"] += s in ("OPT", "UNSAT")
        c["opt_unsat_verified"] += s in ("OPT", "UNSAT") and r["verdict"] == "VERIFIED"
        c["sat_solved"] += s == "SAT" and r["obj"] == "-"
        c["sat_solved_verified"] += s == "SAT" and r["obj"] == "-" and r["verdict"] == "VERIFIED"
        c["incumbent"] += has_value(r)
        c["incumbent_not_opt"] += has_value(r) and s != "OPT"
        c["rejected"] += r["verdict"] == "REJECTED" or s == "REJECTED"
        # CHECK-ERROR is not a refused proof: on these runs it is veripb dying against the
        # harness's MEM_KB (`ulimit -v` covers the checker too), rc 134. Kept apart from REJECTED.
        # M6-T24 (D-0225): a check of a STOPPED run's proof is counted apart from a check of
        # an answer's, so check_error and timeout_check keep meaning what they meant.
        stopped = not (s in ("OPT", "UNSAT") or (s == "SAT" and r["obj"] == "-"))
        c["check_error"] += r["verdict"] == "CHECK-ERROR" and not stopped
        c["timeout_check"] += r["verdict"] == "TIMEOUT-CHECK" and not stopped
        c["incumbent_verified"] += r["verdict"] == "VERIFIED-INCUMBENT"
        c["incumbent_check_unfinished"] += stopped and r["verdict"] in ("CHECK-ERROR", "TIMEOUT-CHECK")
        c[s] += 1
    return c


COLS = ["opt_unsat", "opt_unsat_verified", "sat_solved", "sat_solved_verified", "incumbent",
        "incumbent_not_opt", "TIMEOUT", "CAPPED", "REFUSED", "ERROR", "UNKNOWN", "FLATTEN-FAIL",
        "rejected", "check_error", "timeout_check", "incumbent_verified",
        "incumbent_check_unfinished"]


def verdict(x, y):
    """+1 if y is better than x in the Challenge's order, -1 if worse, 0 if tied."""
    cx, cy = complete(x), complete(y)
    if cx != cy:
        return 1 if cy else -1
    if cx and cy:
        if x["t"] is None or y["t"] is None:
            return 0
        if abs(x["t"] - y["t"]) <= max(1.0, 0.05 * min(x["t"], y["t"])):
            return 0
        return 1 if y["t"] < x["t"] else -1
    hx, hy = has_value(x), has_value(y)
    if hx != hy:
        return 1 if hy else -1
    if hx and hy:
        (k, vx), (_, vy) = objval(x), objval(y)
        if vx == vy:
            return 0
        return 1 if (vy < vx) == (k == "min") else -1
    return 0


def pair(nx, X, ny, Y, fam, out):
    P = lambda *a: print(*a)
    P("\n== %s against %s (ratios are %s / %s)" % (ny, nx, ny, nx))
    trans = Counter()
    only = {nx: [], ny: []}
    inc_only = {nx: [], ny: []}
    tratio, tsum, rss, nps = [], [0.0, 0.0], [], []
    gained, lost = [], []
    byfam = defaultdict(Counter)
    tot = Counter()
    for i in sorted(set(X) & set(Y)):
        x, y = X[i], Y[i]
        if x["status"] in INPUT and y["status"] in INPUT:
            continue
        trans[(x["status"], y["status"])] += 1
        f = fam.get(i, "?")
        cx, cy = complete(x), complete(y)
        if cx and not cy:
            only[nx].append((i, x["status"], y["status"], y["obj"]))
        if cy and not cx:
            only[ny].append((i, x["status"], y["status"], x["obj"]))
        if has_value(x) and not has_value(y):
            inc_only[nx].append((i, x["obj"], y["status"]))
        if has_value(y) and not has_value(x):
            inc_only[ny].append((i, y["obj"], x["status"]))
        if cx and cy and x["t"] and y["t"]:
            tratio.append(y["t"] / max(x["t"], 0.01))
            tsum[0] += x["t"]
            tsum[1] += y["t"]
        if x["rss"] and y["rss"] and x["rss"] >= 65536 and y["rss"] >= 65536:
            rss.append(y["rss"] / x["rss"])
        if x["nodes"] and y["nodes"] and x["t"] and y["t"]:
            nps.append((y["nodes"] / y["t"]) / (x["nodes"] / x["t"]))
        if x["status"] in DIED and y["status"] not in DIED + INPUT:
            gained.append((i, x["status"], y["status"], y["obj"]))
        if y["status"] in DIED and x["status"] not in DIED + INPUT:
            lost.append((i, x["status"], y["status"], x["obj"]))
        v = verdict(x, y)
        k = {1: "win", -1: "loss", 0: "tie"}[v]
        byfam[f][k] += 1
        tot[k] += 1
        if out:
            out.write("\t".join(str(z) for z in (
                nx, ny, i, f, x["status"], y["status"], x["obj"], y["obj"], x["wall"], y["wall"],
                x["nodes"], y["nodes"], x["rss"], y["rss"], k)) + "\n")
    P("status transitions (%s -> %s), the changed ones:" % (nx, ny))
    for (a, b), n in sorted(trans.items(), key=lambda kv: -kv[1]):
        if a != b:
            P("   %-12s -> %-12s %d" % (a, b, n))
    P("   unchanged: %d" % sum(n for (a, b), n in trans.items() if a == b))
    P("wall ratio on the %d complete in both: %s; sums %.0f s -> %.0f s" % (
        len(tratio), q(tratio), tsum[0], tsum[1]))
    P("peak RSS ratio (both >= 64 MB):", q(rss))
    P("nodes/s ratio:", q(nps))
    P("%s's verdict over %s, per instance: %s" % (ny, nx, dict(tot)))
    for n in (nx, ny):
        P("complete in %s only (%d):" % (n, len(only[n])))
        for t in only[n]:
            P("   ", fam.get(t[0], "?"), *t)
        P("incumbent in %s only (%d):" % (n, len(inc_only[n])))
        for t in inc_only[n]:
            P("   ", fam.get(t[0], "?"), *t)
    P("attempts gained by %s (%s REFUSED/CAPPED/ERROR, %s not): %d" % (ny, nx, ny, len(gained)))
    for t in gained:
        P("   ", fam.get(t[0], "?"), *t)
    P("attempts lost by %s (the reverse): %d" % (ny, len(lost)))
    for t in lost:
        P("   ", fam.get(t[0], "?"), *t)
    P("by family, %s's wins / losses against %s (families with a win or a loss):" % (ny, nx))
    for f, c in sorted(byfam.items(), key=lambda kv: (kv[1]["loss"] - kv[1]["win"], kv[0])):
        if c["win"] or c["loss"]:
            P("   %-45s +%d -%d =%d" % (f, c["win"], c["loss"], c["tie"]))


def main(argv):
    if len(argv) < 3 or argv[1] in ("-h", "--help"):
        print(__doc__)
        return 0
    repo = argv[1]
    arms, pairs, tsv, trusted, solvers = [], [], None, set(), {}
    i = 2
    while i < len(argv):
        a = argv[i]
        if a == "--pair":
            pairs.append((argv[i + 1], argv[i + 2]))
            i += 3
            continue
        if a == "--trust":
            trusted.add(argv[i + 1])
            i += 2
            continue
        if a == "--tsv":
            tsv = argv[i + 1]
            i += 2
            continue
        n, d = a.split("=", 1)
        d, _, sv = d.partition("@")
        arms.append((n, d))
        solvers[n] = sv or "baguette"
        i += 1
    fam = families(repo)
    data = {}
    print("== per edition: opt+unsat (verified) / sat-solved (verified) / incumbents / TIMEOUT / CAPPED / REFUSED / ERROR / FLATTEN-FAIL / rejected / check-error / timeout-check")
    tot = {n: Counter() for n, _ in arms}
    allrows = {n: {} for n, _ in arms}
    done = {}
    for n, d in arms:
        allrows[n], done[n] = read_arm(d, n in trusted, solvers[n])
    for y in YEARS:
        cells = []
        for n, _ in arms:
            rows = {k: r for k, r in allrows[n].items() if r["year"] == y}
            c = counts(rows)
            tot[n].update(c)
            st = done[n][y]
            tag = "" if st else (" (absent)" if st is None else " (PARTIAL %d)" % len(rows))
            cells.append("%s%s %d (%d) / %d (%d) / %d / %d / %d / %d / %d / %d / %d / %d / %d" % (
                n, tag, c["opt_unsat"], c["opt_unsat_verified"], c["sat_solved"],
                c["sat_solved_verified"], c["incumbent"], c["TIMEOUT"], c["CAPPED"], c["REFUSED"],
                c["ERROR"], c["FLATTEN-FAIL"], c["rejected"], c["check_error"], c["timeout_check"]))
        print(y, " | ".join(cells))
    for n, _ in arms:
        print("TOTAL", n, " ".join("%s=%d" % (k, tot[n][k]) for k in COLS + ["rows"]))
    out = open(tsv, "w") if tsv else None
    if out:
        out.write("x\ty\tid\tfamily\tstatus_x\tstatus_y\tobj_x\tobj_y\twall_x\twall_y\tnodes_x\tnodes_y"
                  "\trss_kb_x\trss_kb_y\ty_verdict\n")
    for nx, ny in pairs:
        pair(nx, allrows[nx], ny, allrows[ny], fam, out)
    if out:
        out.close()
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
