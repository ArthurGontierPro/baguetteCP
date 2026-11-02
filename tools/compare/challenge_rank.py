#!/usr/bin/env python3
"""M7-T26. Baguette's theoretical rank in a MiniZinc Challenge edition, offline.

    challenge_rank.py <results.json> <YEAR.lst> [<out-dir> ...] [options]

<results.json> is the edition's official per-instance results (the results page's data,
~/mznc-archive/results/<YEAR>.json), <YEAR.lst> the instance list the run used
(bench/challenge/<YEAR>.lst, whose `idx` column is the join key into results.json), and
each <out-dir> a scripts/compare_run.sh output directory (results.tsv + flatten.tsv) of
a run over that list. With no <out-dir> the script only validates the scoring.

What it does, in order:

  1. REPRODUCES THE EDITION'S SCORING from its own data. The page's `scores[A][B][i]`
     is the pairwise score of A against B on instance i; this script recomputes every
     one of them from `results`, `times`, `objectives` and `kind`, and reports how
     many differ. That number must be 0 (it is, on all sixteen editions, with the
     per-year rules below); it is the proof that the ranking printed afterwards is the
     organisers' procedure and not an approximation of it.
  2. INSERTS the run's solver as an extra entrant (`--as`, default `baguette-fd`) in a
     category (`--category fd|free`, default fd: the harness runs without free search),
     mapping the harness's statuses onto the Challenge's (below), and recomputes the
     category's pairwise scores with it in. The official entrants' recomputed ranks are
     printed beside their official ones (they agree, by step 1).
  3. If the run also has Chuffed rows, inserts them too (`chuffed-ours-fd`) as the
     CALIBRATION: same instances, same solver, our machine vs the Challenge's. Its
     rank next to the official `chuffed-fd`, and the time ratio on the instances both
     completed, are the scale factor to read baguette's rank with.

The pairwise rule (the "complete" procedure of the rules, per the data):
  quality: complete (SC; C; UC in 2011; S on a SAT problem) > S with an objective on an
  optimisation problem, better objective first > nothing (UNK, ERR, INC, MZN).
  A better quality scores 1, a worse one 0 -- except 2021-2025, where the WORSE of two
  incomplete answers scores 0.5 (the editions that gave half a point for a solution).
  Equal quality splits the point by time, t_B / (t_A + t_B):
    2011-2012  times are whole seconds and the split is all-or-nothing (faster 1,
               slower 0, equal 0.5); the stored scores are on a 0..2 scale
    2013-2017  milliseconds, exact
    2018-2026  seconds, floored (floor(ms/1000)); equal floors 0.5
  All measured against the stored matrices on 2026-10-30; a new edition is validated
  by step 1 before anything is read from it.

Our statuses -> the Challenge's (compare_run.sh's vocabulary, see its header):
  OPT -> SC          UNSAT -> C          SAT -> S (complete on a SAT problem, else the
  incumbent)         TIMEOUT with solutions -> S          ERROR -> ERR
  TIMEOUT without, UNKNOWN, REFUSED, FLATTEN-FAIL, CAPPED, INPUT-INVALID, NO-DATA, and an
  instance with no row -> UNK. A REFUSED is a UNK in the Challenge's terms, scored, never
  skipped.
  time = wall_s + flatten_s (the Challenge counts compile time) for a complete answer;
  the limit (`--timeout`, default 1200 s) otherwise, as the official data does.
  A baguette completeness claim (OPT, UNSAT) whose proof is not VERIFIED is DEMOTED
  (OPT -> S, UNSAT -> UNK) unless --trust-unverified; both counts are printed. Chuffed
  and GCS rows are taken as printed.

Python 3.8+, standard library only (imports compare.py from its own directory).
"""
import json
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import compare  # noqa: E402

COMPLETE = ("SC", "C", "UC")
NOTHING = ("UNK", "ERR", "INC", "MZN", "")


# ------------------------------------------------------------------ the rule

def rule_for(year, R):
    mx = max(v for a in R["scores"] for b in a for v in b)
    return {
        "year": year,
        "scale": 2.0 if mx > 1.0001 else 1.0,
        "time": "sec-allornothing" if year <= 2012 else ("ms" if year <= 2017 else "floorsec"),
        "worse_incomplete": 0.5 if 2021 <= year <= 2025 else 0.0,
    }


def quality(status, kind, obj):
    """(rank, objective) -- rank 2 complete, 1 incumbent, 0 nothing."""
    s = (status or "").strip()
    if s in COMPLETE or (kind == "SAT" and s == "S"):
        return 2, None
    if s == "S":
        try:
            return 1, int(str(obj).strip())
        except ValueError:
            return 1, None
    return 0, None


def to_ms(t, rule):
    t = str(t).strip()
    if t == "":
        return None
    v = float(t)
    return v * 1000.0 if rule["time"] == "sec-allornothing" else v


def time_split(ta, tb, rule):
    if ta is None or tb is None:
        return 0.5
    if rule["time"] == "floorsec":
        ta, tb = math.floor(ta / 1000.0), math.floor(tb / 1000.0)
    elif rule["time"] == "sec-allornothing":
        return 0.5 if ta == tb else (1.0 if ta < tb else 0.0)
    if ta == tb:
        return 0.5
    return tb / (ta + tb)


def pair_score(a, b, kind, rule):
    """a, b = (status, time_ms, objective). The score of a against b."""
    (qa, oa), (qb, ob) = quality(a[0], kind, a[2]), quality(b[0], kind, b[2])
    if qa != qb:
        if qa > qb:
            return 1.0
        return rule["worse_incomplete"] if (qa == 1 and qb == 1) else 0.0
    if qa == 0:
        return 0.0
    if qa == 1:
        if oa is not None and ob is not None and oa != ob:
            if (oa < ob) == (kind == "MIN"):
                return 1.0
            return rule["worse_incomplete"]
        return 0.5
    return time_split(a[1], b[1], rule)


# ------------------------------------------------------------------ the data

def load_results(path):
    with open(path) as f:
        doc = json.load(f)
    R = doc["results"]
    for i in range(len(R["solvers"])):
        R["results"][i] = [s.strip() for s in R["results"][i]]
    return R


def kind_of(R):
    k = {}
    for pi, kind in enumerate(R["kind"]):
        for i in R["instances"][pi]:
            k[i] = (kind, R["problems"][pi])
    return k


def official_answer(R, s, i, rule):
    return (R["results"][s][i], to_ms(R["times"][s][i], rule), R["objectives"][s][i])


def validate(R, rule):
    """Recompute every stored pairwise score. Returns (pairs, mismatches, examples)."""
    kinds = kind_of(R)
    S = len(R["solvers"])
    pairs = mism = 0
    ex = {}
    for i in range(len(R["benchmarks"])):
        kind = kinds[i][0]
        ans = [official_answer(R, s, i, rule) for s in range(S)]
        for a in range(S):
            for b in range(S):
                if a == b:
                    continue
                got = pair_score(ans[a], ans[b], kind, rule)
                want = R["scores"][a][b][i] / rule["scale"]
                pairs += 1
                if abs(got - want) > 1e-6:
                    mism += 1
                    key = (kind, ans[a][0], ans[b][0], round(got, 2), round(want, 2))
                    ex.setdefault(key, (R["solvers"][a], R["solvers"][b], R["benchmarks"][i],
                                        ans[a], ans[b]))
    return pairs, mism, ex


def load_list(path):
    rows = {}
    with open(path) as f:
        for l in f:
            if l.startswith("#") or not l.strip():
                continue
            fld = l.rstrip("\n").split("\t")
            rows[int(fld[3])] = {"id": fld[0], "model": fld[1], "data": fld[2],
                                 "problem": fld[4], "kind": fld[5], "bench": fld[6]}
    return rows


def load_runs(outdirs):
    """(id, solver) -> row, with flatten_s merged in. Later directories win."""
    rows = {}
    for od in outdirs:
        rs, done = compare.load(od)
        if not done:
            print("WARNING: %s has no DONE marker -- a partial run; its missing rows score UNK" % od)
        flat = {}
        for l in compare.read(os.path.join(od, "flatten.tsv")).splitlines():
            f = l.split("\t")
            if len(f) >= 8 and f[2] == "OK":
                try:
                    flat[(f[0], f[1])] = float(f[7])
                except ValueError:
                    pass
        for r in rs:
            r["flatten_s"] = flat.get((r["id"], r["solver"]), 0.0)
            rows[(r["id"], r["solver"])] = r
    return rows


def verified(r):
    """The proof establishes what the solver printed. Tables written before compare.py
    read the checker's optimisation wording of infeasibility (`BOUNDS INF <= obj <= INF`)
    file that sound UNSAT as VERIFIED-WEAK; it is accepted here on the same wording."""
    v = r.get("check_verdict")
    return v == "VERIFIED" or (v == "VERIFIED-WEAK" and r["status"] == "UNSAT"
                               and compare.INF_BOUNDS_RE.search(r.get("detail") or ""))


def our_answer(r, kind, timeout_s, rule, demote):
    """-> (status, time_ms, objective, note). note names a demotion, else ''."""
    if r is None:
        return ("UNK", to_ms(timeout_s if rule["time"] == "sec-allornothing"
                            else timeout_s * 1000, rule), " ", "no row")
    st = r["status"]
    sense, val = compare.objval(r)
    obj = str(val) if val is not None else " "
    n = compare.nsols(r)
    note = ""
    if demote and st in ("OPT", "UNSAT") and not verified(r):
        note = "%s demoted: proof %s" % (st, r.get("check_verdict") or "-")
        st = "SAT" if st == "OPT" else "UNKNOWN"
    if st == "OPT":
        cs = "SC"
    elif st == "UNSAT":
        cs = "C"
    elif st == "SAT" or (st == "TIMEOUT" and n > 0):
        cs = "S"
    elif st == "ERROR":
        cs = "ERR"
    else:
        cs = "UNK"
    complete = cs in COMPLETE or (kind == "SAT" and cs == "S")
    if complete and st != "TIMEOUT":
        secs = float(r["wall_s"] or 0) + float(r.get("flatten_s") or 0)
        secs = min(secs, float(timeout_s))
    else:
        secs = float(timeout_s)
    if rule["time"] == "sec-allornothing":
        t = to_ms(int(round(secs)), rule)
    else:
        t = int(round(secs * 1000))
    return (cs, t, obj if cs == "S" and kind != "SAT" else " ", note)


# ------------------------------------------------------------------ ranking

def rank_category(R, rule, mask, extra):
    """extra: name -> {idx: (status, ms, obj)}. Returns rows sorted by score."""
    kinds = kind_of(R)
    names = [R["solvers"][s] for s in range(len(R["solvers"])) if R[mask][s]]
    official = {}
    for s, name in enumerate(R["solvers"]):
        if R[mask][s]:
            official[name] = sum(R["scores"][s][b][i] / rule["scale"]
                                 for b in range(len(R["solvers"])) if R[mask][b] and b != s
                                 for i in range(len(R["benchmarks"])))
    answers = {}
    for name in names:
        s = R["solvers"].index(name)
        answers[name] = {i: official_answer(R, s, i, rule) for i in range(len(R["benchmarks"]))}
    for name, a in extra.items():
        answers[name] = a
    allnames = names + list(extra)
    score = {n: 0.0 for n in allnames}
    byprob = {n: {} for n in allnames}
    for i in range(len(R["benchmarks"])):
        kind, prob = kinds[i]
        for a in allnames:
            for b in allnames:
                if a == b:
                    continue
                p = pair_score(answers[a][i], answers[b][i], kind, rule)
                score[a] += p
                byprob[a][prob] = byprob[a].get(prob, 0.0) + p
    order = sorted(allnames, key=lambda n: -score[n])
    off_order = sorted(official, key=lambda n: -official[n])
    off_rank = {n: k + 1 for k, n in enumerate(off_order)}
    # Recomputed rank among the OFFICIAL entrants only (must equal off_rank).
    re_order = sorted(names, key=lambda n: -sum(
        pair_score(answers[n][i], answers[b][i], kinds[i][0], rule)
        for b in names if b != n for i in range(len(R["benchmarks"]))))
    re_rank = {n: k + 1 for k, n in enumerate(re_order)}
    return order, score, official, off_rank, re_rank, byprob, len(allnames)


def fmt(x):
    return "%.2f" % x


# ------------------------------------------------------------------ main

def main(argv):
    args = [a for a in argv[1:] if not a.startswith("--")]
    opts = [a for a in argv[1:] if a.startswith("--")]
    if len(args) < 2:
        sys.stderr.write(__doc__)
        return 2

    def opt(name, default=None):
        for o in opts:
            if o.startswith("--" + name + "="):
                return o.split("=", 1)[1]
            if o == "--" + name:
                return True
        return default
    results_path, list_path, outdirs = args[0], args[1], args[2:]
    solver = opt("solver", "baguette")
    category = opt("category", "fd")
    mask = {"fd": "fd_solvers", "free": "free_solvers"}[category]
    entrant = opt("as", "%s-%s" % (solver, category) if solver == "baguette"
                  else "%s-ours-%s" % (solver, category))
    timeout_s = int(opt("timeout", "1200"))
    demote = not opt("trust-unverified")
    showall = opt("all")

    R = load_results(results_path)
    lst = load_list(list_path)
    year = int(os.path.basename(list_path).split(".")[0]) if os.path.basename(list_path)[:4].isdigit() \
        else int(opt("year", "0"))
    rule = rule_for(year, R)
    print("== %d: %d entrants, %d instances; rule: time %s, worse incomplete %.1f, scale %g"
          % (year, len(R["solvers"]), len(R["benchmarks"]), rule["time"],
             rule["worse_incomplete"], rule["scale"]))
    pairs, mism, ex = validate(R, rule)
    print("scoring reproduced: %d of %d stored pairwise scores match%s"
          % (pairs - mism, pairs, "" if mism == 0 else " -- %d DO NOT; the ranking below is NOT "
             "the organisers' procedure until this is 0" % mism))
    for key, e in sorted(ex.items(), key=lambda kv: kv[0])[:8]:
        print("   mismatch", key, e)
    if len(lst) != len(R["benchmarks"]):
        print("NOTE: the list has %d of the %d instances (the rest score UNK)"
              % (len(lst), len(R["benchmarks"])))

    extra = {}
    if outdirs:
        runs = load_runs(outdirs)
        for s in [solver] + (["chuffed"] if solver != "chuffed" and not opt("no-chuffed") else []):
            name = entrant if s == solver else "chuffed-ours-%s" % category
            ours, hs, cs, notes, verdicts, missing = {}, {}, {}, [], {}, []
            for i in range(len(R["benchmarks"])):
                kind = kind_of(R)[i][0]
                li = lst.get(i)
                r = runs.get((li["id"], s)) if li else None
                if li is None:
                    missing.append("idx %d" % i)
                elif r is None:
                    missing.append(li["id"])
                a = our_answer(r, kind, timeout_s, rule, demote and s == "baguette")
                ours[i] = a[:3]
                if r is not None:
                    hs[r["status"]] = hs.get(r["status"], 0) + 1
                    v = r.get("check_verdict") or "-"
                    verdicts[v] = verdicts.get(v, 0) + 1
                cs[a[0]] = cs.get(a[0], 0) + 1
                if a[3] and a[3] != "no row":
                    notes.append("%s: %s" % (li["id"] if li else i, a[3]))
            if not any(runs.get((li["id"], s)) for li in lst.values()):
                if s == solver:
                    print("no %s rows in %s" % (s, " ".join(outdirs)))
                    return 1
                continue
            extra[name] = ours
            print("\n== %s: harness statuses %s" % (name, " ".join(
                "%s %d" % kv for kv in sorted(hs.items(), key=lambda kv: -kv[1]))))
            print("   challenge statuses %s; %d instance(s) without a row%s" % (
                " ".join("%s %d" % kv for kv in sorted(cs.items(), key=lambda kv: -kv[1])),
                len(missing), ": " + " ".join(missing[:6]) if missing else ""))
            if s in compare.PROOF_SOLVERS:
                print("   proof verdicts %s" % " ".join(
                    "%s %d" % kv for kv in sorted(verdicts.items(), key=lambda kv: -kv[1])))
            for n in notes[:20]:
                print("   " + n)
            if len(notes) > 20:
                print("   ... %d demotions in all" % len(notes))

    order, score, official, off_rank, re_rank, byprob, n = rank_category(R, rule, mask, extra)
    print("\n== %s category, %d entrants (%d official + %d inserted); pairwise complete score"
          % (category, n, n - len(extra), len(extra)))
    print("%4s  %-40s %9s   %-9s %s" % ("rank", "entrant", "score", "official", "official rank -> recomputed"))
    for k, name in enumerate(order):
        if name in extra:
            print("%4d  %-40s %9s   %-9s %s" % (k + 1, name, fmt(score[name]), "-", "INSERTED"))
        elif showall or k < 12 or any(abs(order.index(e) - k) <= 2 for e in extra):
            flag = "" if off_rank[name] == re_rank[name] else "  <-- DISAGREES"
            print("%4d  %-40s %9s   %-9s %d -> %d%s" % (k + 1, name, fmt(score[name]),
                                                      fmt(official[name]), off_rank[name], re_rank[name], flag))
        elif k == 12:
            print("      ...")
    bad = [nm for nm in off_rank if off_rank[nm] != re_rank[nm]]
    print("official ranks reproduced: %s" % ("all %d" % len(off_rank) if not bad else
                                              "NO -- %s" % ", ".join(bad)))

    for name in extra:
        bp = byprob[name]
        per = n - 1  # opponents per instance
        tops = sorted(bp.items(), key=lambda kv: -kv[1])
        print("\n== %s by problem (points / max %d per problem of 5 instances x %d opponents):"
              % (name, 5 * per, per))
        print("   " + "; ".join("%s %s" % (p, fmt(v)) for p, v in tops if v > 0) or "   none")
        zero = [p for p, v in tops if v == 0]
        if zero:
            print("   zero: " + " ".join(zero))

    cal = "chuffed-ours-%s" % category
    # The official name is `Chuffed-fd` in 2014-2016 and `chuffed-fd` elsewhere.
    offs = [k for k, n in enumerate(R["solvers"]) if n.lower() == "chuffed-%s" % category]
    if cal in extra and offs:
        s = offs[0]
        agree = {}
        ratios = []
        for i in range(len(R["benchmarks"])):
            off = official_answer(R, s, i, rule)
            ours = extra[cal][i]
            key = "%s/%s" % (off[0] or "-", ours[0])
            agree[key] = agree.get(key, 0) + 1
            kind = kind_of(R)[i][0]
            if quality(off[0], kind, off[2])[0] == 2 and quality(ours[0], kind, ours[2])[0] == 2 \
                    and off[1] and ours[1] and off[1] > 0 and ours[1] > 0:
                ratios.append(ours[1] / off[1])
        print("\n== calibration, official chuffed-%s vs ours (official/ours status counts): %s"
              % (category, " ".join("%s %d" % kv for kv in sorted(agree.items(), key=lambda kv: -kv[1]))))
        if ratios:
            g = math.exp(sum(math.log(x) for x in ratios) / len(ratios))
            print("   time ratio ours/official on %d instances both completed: geometric mean %.2f, "
                  "median %.2f" % (len(ratios), g, sorted(ratios)[len(ratios) // 2]))
    return 0 if mism == 0 and not bad else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
