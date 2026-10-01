#!/usr/bin/env python3
"""M6-T4. The comparison harness's judgement, in one reviewable place.

scripts/compare_run.sh does the orchestration (flatten, ulimit, timeout, the files);
this file does every step that DECIDES something, so the decisions are written once
and the self-test exercises the same code the node runs:

  prep FZN             validate a JSON FlatZinc file, read the solve item, and make the
                       objective an output variable (text and JSON), so that "the last
                       printed objective" exists for every solver alike. Prints
                       `sense<TAB>objname`, sense in sat|min|max.
  classify ...         a solver's exit code + stdout/stderr -> status, nsols, objective
  verdict ...          veripb's exit code + output -> check verdict
  report OUT...        the report: DISAGREE first
  answers OUT...       the agreed answer per instance (bench/corpus/answers.tsv)
  shared OUT...        the ids every solver's library flattened (shared_set.lst)

Python 3.8+, standard library only: the node has 3.14 and the laptop 3.10.
"""
import json
import os
import re
import statistics
import sys

SOLVERS = ("baguette", "chuffed", "gcs")
PROOF_SOLVERS = ("baguette", "gcs")
COLS = ("id", "solver", "status", "wall_s", "objective", "nsols", "fzn_bytes",
        "opb_bytes", "pbp_bytes", "check_verdict", "check_s", "detail")
PROVED = ("SAT", "UNSAT", "OPT")

# ------------------------------------------------------------------ prep

SOLVE_RE = re.compile(r"\b(minimize|maximize)\s+([A-Za-z_][A-Za-z0-9_]*)\s*;\s*$")


def prep(path):
    with open(path, "rb") as f:
        raw = f.read()
    head = raw.lstrip()[:1]
    if head == b"{":
        return prep_json(path, raw)
    return prep_text(path, raw.decode("utf-8", errors="replace"))


def prep_json(path, raw):
    try:
        d = json.loads(raw)
    except ValueError as e:
        print("the JSON FlatZinc does not parse (%s) -- truncated or torn" % e)
        return 1
    if not isinstance(d, dict) or "solve" not in d or "variables" not in d:
        print("the JSON FlatZinc has no solve item or no variables -- incomplete capture")
        return 1
    s = d["solve"]
    method = s.get("method", "satisfy")
    if method == "satisfy":
        print("sat\t-")
        return 0
    obj = s.get("objective")
    sense = "min" if method == "minimize" else "max"
    if isinstance(obj, str):
        out = d.setdefault("output", [])
        if obj not in out:
            out.append(obj)
            tmp = path + ".prep"
            with open(tmp, "w") as f:
                json.dump(d, f)
            os.replace(tmp, path)
        print("%s\t%s" % (sense, obj))
    else:
        print("%s\t-" % sense)
    return 0


def prep_text(path, txt):
    lines = txt.split("\n")
    solve = [l for l in lines if l.lstrip().startswith("solve")]
    if not solve:
        print("the .fzn has no solve item")
        return 1
    m = SOLVE_RE.search(solve[-1].strip())
    if not m:
        print("sat\t-")
        return 0
    sense = "min" if m.group(1) == "minimize" else "max"
    name = m.group(2)
    decl = re.compile(r"^(\s*var\b[^;]*?:\s*" + re.escape(name) + r")(?=\s*(::|=|;))")
    changed = False
    for i, l in enumerate(lines):
        mm = decl.match(l)
        if mm:
            if "output_var" not in l:
                lines[i] = mm.group(1) + " :: output_var" + l[mm.end(1):]
                changed = True
            break
    if changed:
        tmp = path + ".prep"
        with open(tmp, "w") as f:
            f.write("\n".join(lines))
        os.replace(tmp, path)
    print("%s\t%s" % (sense, name))
    return 0

# ------------------------------------------------------------------ classify

# A refusal is the solver saying "I do not support this model", which is a statement
# about coverage, not an answer. baguette says it by exit code (2 front end, 3 a declared
# limit, 5 a declared budget -- corpus_run.sh); the others only in words.
REFUSAL_RE = re.compile(r"unsupported|not supported|unknown constraint|no propagator|"
                        r"not implemented|unimplemented", re.I)


def classify(solver, rc, outf, errf, sense, objname, cap_rc):
    rc = int(rc)
    out = read(outf)
    err = read(errf)
    lines = [l.strip() for l in out.splitlines()]
    nsols = sum(1 for l in lines if l == "----------")
    unsat = "=====UNSATISFIABLE=====" in lines
    done = "==========" in lines
    obj = None
    if objname not in ("", "-"):
        pat = re.compile(r"^" + re.escape(objname) + r"\s*=\s*(-?\d+)\s*;")
        for l in lines:
            m = pat.match(l)
            if m:
                obj = m.group(1)
    detail = ""
    if rc in (124, 137):
        status = "TIMEOUT"
        detail = "killed at the solve timeout"
        if unsat or done:
            detail += " (a final marker WAS printed; not counted as proved)"
    elif rc == int(cap_rc):
        # SIGXFSZ: the harness's own file-size cap (PROOF_CAP_KB) stopped it. A cap we
        # imposed is not an answer and not a solver error; it gets its own name.
        status = "CAPPED"
        detail = "SIGXFSZ: a file exceeded the harness's PROOF_CAP_KB cap"
    elif rc == 0:
        if unsat and nsols > 0:
            status = "ERROR"
            detail = "printed solutions AND =====UNSATISFIABLE====="
        elif unsat:
            status = "UNSAT"
        elif sense in ("min", "max"):
            status = "OPT" if (done and nsols > 0) else ("SAT" if nsols > 0 else "UNKNOWN")
        else:
            status = "SAT" if nsols > 0 else "UNKNOWN"
    else:
        msg = (err.strip() or out.strip())[:180]
        if solver == "baguette" and rc in (2, 3, 5):
            status = "REFUSED"
        elif solver != "baguette" and REFUSAL_RE.search(err + "\n" + out):
            status = "REFUSED"
        else:
            status = "ERROR"
        detail = "rc=%d %s" % (rc, msg)
    if sense in ("min", "max"):
        objective = "%s:%s" % (sense, obj if obj is not None else "-")
    else:
        objective = "-"
    print("%s\t%s\t%d\t%s" % (status, objective, nsols, flat(detail)))
    return 0

# ------------------------------------------------------------------ verdict

BOUNDS_RE = re.compile(r"BOUNDS\s+(\S+)\s*<=\s*obj\s*<=\s*(\S+)")
GRAMMAR_RE = re.compile(r"pars(e|ing)|syntax|unexpected|expected .* found|unknown rule", re.I)


def verdict(rc, vpf, status):
    rc = int(rc)
    t = read(vpf)
    if rc == 124 or rc == 137:
        print("TIMEOUT-CHECK\tveripb exceeded the check timeout")
        return 0
    slines = [l.strip() for l in t.splitlines() if l.startswith("s VERIFIED")]
    if rc == 0 and slines:
        s = slines[-1]
        # VERIFIED means the checker accepted; VERIFIED-WEAK means it accepted a proof
        # whose CONCLUSION does not establish what the solver printed. The second is a
        # soundness-relevant finding about the solver's output, not about the proof.
        weak = False
        if status == "UNSAT" and "UNSATISFIABLE" not in s:
            weak = True
        if status == "OPT":
            m = BOUNDS_RE.search(s)
            if not m or m.group(1) != m.group(2):
                weak = True
        if status == "SAT" and not ("SATISFIABLE" in s or "BOUNDS" in s):
            weak = True
        print("%s\t%s" % ("VERIFIED-WEAK" if weak else "VERIFIED", flat(s)))
        return 0
    caused = ""
    ls = t.splitlines()
    for i, l in enumerate(ls):
        if l.strip().startswith("Caused by"):
            caused = " ".join(x.strip() for x in ls[i + 1:i + 3])
            break
    # The JUDGEMENT wording of 3.0.2 is "Verification error at <file>:<line>" followed by
    # "Caused by: <reason>". A reason that is about the grammar is a parse failure and
    # says nothing about soundness (M2-T14), so it is CHECK-ERROR, not REJECTED.
    if "Verification error" in t and caused and not GRAMMAR_RE.search(caused):
        print("REJECTED\t%s" % flat(caused))
        return 0
    first = next((l for l in ls if l.strip().startswith("Error")), ls[-1] if ls else "")
    print("CHECK-ERROR\trc=%d %s %s" % (rc, flat(first), flat(caused)))
    return 0

# ------------------------------------------------------------------ tables


def read(p):
    try:
        with open(p, "r", errors="replace") as f:
            return f.read()
    except OSError:
        return ""


def flat(s):
    return re.sub(r"[\t\r\n]+", " ", s or "").strip()[:200]


def load(outdir):
    res = os.path.join(outdir, "results.tsv")
    rows, done, ids = [], None, {}
    for l in read(res).splitlines():
        if not l.strip():
            continue
        if l.startswith("DONE-"):
            done = l
            continue
        f = l.split("\t")
        if len(f) < len(COLS):
            f += [""] * (len(COLS) - len(f))
        r = dict(zip(COLS, f))
        rows.append(r)
    return rows, done


def load_conf(outdir):
    c = {}
    for l in read(os.path.join(outdir, "run.conf")).splitlines():
        if "=" in l:
            k, v = l.split("=", 1)
            c[k] = v
    return c


def load_pairs(outdir):
    p = {}
    for l in read(os.path.join(outdir, "pair.tsv")).splitlines():
        f = l.split("\t")
        if len(f) >= 4:
            p[f[0]] = {"model": f[1], "result": f[2], "data": f[3]}
    return p


def objval(r):
    o = r.get("objective", "-")
    if ":" in o:
        s, v = o.split(":", 1)
        try:
            return s, int(v)
        except ValueError:
            return s, None
    return None, None


def better(sense, a, b):
    return a < b if sense == "min" else a > b


def nsols(r):
    try:
        return int(r.get("nsols") or 0)
    except ValueError:
        return 0


def sat_evidence(r):
    return r["status"] in ("SAT", "OPT") or (r["status"] != "UNSAT" and nsols(r) > 0)


def agreement(rs):
    """rs: rows of one instance, one per solver. Returns (verdict, reason)."""
    reasons = []
    sats = [r for r in rs if sat_evidence(r)]
    unsats = [r for r in rs if r["status"] == "UNSAT"]
    for a in sats:
        for b in unsats:
            reasons.append("%s found a solution, %s says UNSAT" % (a["solver"], b["solver"]))
    opts = [(r, objval(r)) for r in rs if r["status"] == "OPT"]
    opts = [(r, s, v) for r, (s, v) in opts if v is not None]
    for i in range(len(opts)):
        for j in range(i + 1, len(opts)):
            if opts[i][2] != opts[j][2]:
                reasons.append("%s proves optimum %d, %s proves %d" % (
                    opts[i][0]["solver"], opts[i][2], opts[j][0]["solver"], opts[j][2]))
    for a in rs:
        s, v = objval(a)
        if v is None or nsols(a) == 0:
            continue
        for b, sb, vb in opts:
            if b is a:
                continue
            if better(sb, v, vb):
                reasons.append("%s has incumbent %d, better than %s's proved optimum %d" % (
                    a["solver"], v, b["solver"], vb))
    if reasons:
        return "DISAGREE", "; ".join(reasons)
    answered = [r for r in rs if r["status"] in PROVED]
    if len(answered) >= 2:
        return "AGREE", ""
    return "INCOMPLETE", "%d answer(s)" % len(answered)


def solved(r):
    s = r["status"]
    if s == "UNSAT" or s == "OPT":
        return True
    return s == "SAT" and not r.get("objective", "-").startswith(("min:", "max:"))


def fnum(x):
    try:
        return float(x)
    except (TypeError, ValueError):
        return None


def report(outdirs, pinned=None, timeout=None):
    ok = True
    allrows = []
    # Duplicates are judged WITHIN one table: the same (id, solver) in two runs passed
    # together is two measurements, not a collision.
    dups = 0
    for od in outdirs:
        rows, done = load(od)
        conf = load_conf(od)
        print("== %s" % od)
        if done:
            print("run: COMPLETE (%s)" % done.replace("\t", " "))
        else:
            print("run: ***PARTIAL*** -- no DONE marker. Every count below is a lower bound")
            print("     and must not be reported as a total.")
        for k in ("solvers", "solve_timeout", "baguette_md5", "chuffed_md5", "gcs_md5",
                  "minizinc_md5", "veripb", "harness_commit", "baguette_commit", "gcs_commit", "compat"):
            if k in conf:
                print("  %s = %s" % (k, conf[k]))
        if timeout is None and conf.get("solve_timeout"):
            timeout = float(conf["solve_timeout"])
        k = [(r["id"], r["solver"]) for r in rows]
        dups += len(k) - len(set(k))
        allrows += rows
    if timeout is None:
        timeout = 300.0
    by, every = {}, {}
    for r in allrows:
        by.setdefault(r["id"], {})[r["solver"]] = r
        every.setdefault(r["id"], []).append(r)
    solvers = [s for s in SOLVERS if any(s in v for v in by.values())]
    # Agreement over EVERY row of an instance, so tables passed together are judged
    # together (the pilot's chuffed row and the Chuffed pass's both count).
    verdicts = {i: agreement(every[i]) for i in by}

    dis = sorted(i for i, (v, _) in verdicts.items() if v == "DISAGREE")
    print()
    print("== DISAGREE: %d instance(s)%s" % (len(dis), "" if dis else
          " -- the oracle found nothing on this run"))
    for i in dis:
        tag = "SOUNDNESS(baguette)" if "baguette" in by[i] and \
            "baguette" in verdicts[i][1] else "external"
        st = " ".join("%s=%s/%s" % (s, by[i][s]["status"], by[i][s]["objective"])
                      for s in solvers if s in by[i])
        print("  %-12s %s  %s  -- %s" % (tag, i, st, verdicts[i][1]))

    bad = [r for r in allrows if r["check_verdict"] in ("REJECTED", "VERIFIED-WEAK",
                                                         "CHECK-ERROR")]
    print()
    print("== proofs not cleanly verified: %d" % len(bad))
    for r in sorted(bad, key=lambda r: (r["id"], r["solver"])):
        print("  %s %s %s %s -- %s" % (r["check_verdict"], r["id"], r["solver"],
                                       r["status"], r["detail"][:120]))

    if pinned:
        pins = load_answers(pinned)
        mism = []
        for i, v in by.items():
            if i not in pins:
                continue
            for s, r in v.items():
                m = pin_mismatch(pins[i], r)
                if m:
                    mism.append((i, s, m))
        print()
        print("== against the pinned answers in %s: %d mismatch(es)" % (pinned, len(mism)))
        for i, s, m in sorted(mism):
            print("  PIN-MISMATCH %s %s -- %s" % (i, s, m))

    statuses = ["SAT", "UNSAT", "OPT", "UNKNOWN", "TIMEOUT", "CAPPED", "REFUSED", "ERROR",
                "FLATTEN-FAIL", "NO-DATA", "INPUT-INVALID"]
    print()
    print("== status by solver")
    print("  %-14s" % "status" + "".join("%10s" % s for s in solvers))
    for st in statuses:
        cnt = [sum(1 for r in allrows if r["solver"] == s and r["status"] == st)
               for s in solvers]
        if any(cnt):
            print("  %-14s" % st + "".join("%10d" % c for c in cnt))
    print("  %-14s" % "total" + "".join(
        "%10d" % sum(1 for r in allrows if r["solver"] == s) for s in solvers))

    print()
    print("== proofs by solver")
    vs = ["VERIFIED", "VERIFIED-WEAK", "REJECTED", "TIMEOUT-CHECK", "CHECK-ERROR",
          "NO-PROOF", "NOT-CHECKED"]
    ps = [s for s in solvers if s in PROOF_SOLVERS]
    print("  %-14s" % "verdict" + "".join("%10s" % s for s in ps))
    for v in vs:
        cnt = [sum(1 for r in allrows if r["solver"] == s and r["check_verdict"] == v)
               for s in ps]
        if any(cnt):
            print("  %-14s" % v + "".join("%10d" % c for c in cnt))

    print()
    vc = {}
    for v, _ in verdicts.values():
        vc[v] = vc.get(v, 0) + 1
    print("== agreement: " + "  ".join("%s %d" % (k, vc.get(k, 0))
                                        for k in ("AGREE", "DISAGREE", "INCOMPLETE")))

    common = [i for i, v in by.items()
              if all(s in v and solved(v[s]) for s in solvers)]
    print()
    print("== on the %d instance(s) every listed solver solved (%s); PAR2 over all %d, "
          "timeout %gs" % (len(common), ",".join(solvers), len(by), timeout))
    print("  %-10s %10s %10s %10s %14s %12s" % ("solver", "median_s", "mean_s", "PAR2",
                                               "median_pbp_B", "median_chk_s"))
    for s in solvers:
        w = [fnum(by[i][s]["wall_s"]) for i in common]
        w = [x for x in w if x is not None]
        par2 = []
        for i, v in by.items():
            r = v.get(s)
            if r is None:
                continue
            x = fnum(r["wall_s"])
            par2.append(x if (solved(r) and x is not None) else 2 * timeout)
        pb = [fnum(by[i][s]["pbp_bytes"]) for i in common]
        pb = [x for x in pb if x is not None]
        ck = [fnum(by[i][s]["check_s"]) for i in common]
        ck = [x for x in ck if x is not None]
        print("  %-10s %10s %10s %10s %14s %12s" % (
            s, "%.2f" % statistics.median(w) if w else "-",
            "%.2f" % statistics.mean(w) if w else "-",
            "%.1f" % statistics.mean(par2) if par2 else "-",
            "%d" % statistics.median(pb) if pb else "-",
            "%.2f" % statistics.median(ck) if ck else "-"))
    print()
    print("distinct instances: %d   rows: %d" % (len(by), len(allrows)))
    if dups:
        print("FAIL: %d (id, solver) pairs appear more than once. Two jobs shared an output"
              % dups)
        print("      path; these rows are NOT results (D-0069).")
        ok = False
    return 0 if ok else 1

# ------------------------------------------------------------------ answers


def load_answers(path):
    a = {}
    for l in read(path).splitlines():
        if not l.strip() or l.startswith("#") or l.startswith("id\t"):
            continue
        f = l.split("\t")
        a[f[0]] = {"answer": f[1], "objective": f[2], "by": f[3],
                   "data": f[4] if len(f) > 4 else ""}
    return a


def pin_mismatch(pin, r):
    ans = pin["answer"]
    st = r["status"]
    s, v = objval(r)
    po = pin["objective"]
    if ans == "UNSAT" and sat_evidence(r):
        return "pinned UNSAT, this run found a solution (%s)" % r["objective"]
    if ans in ("SAT", "OPT") and st == "UNSAT":
        return "pinned %s, this run says UNSAT" % ans
    if ans == "OPT" and ":" in po:
        ps, pv = po.split(":", 1)
        pv = int(pv)
        if st == "OPT" and v is not None and v != pv:
            return "pinned optimum %d, this run proves %d" % (pv, v)
        if v is not None and nsols(r) > 0 and better(ps, v, pv):
            return "pinned optimum %d, this run has a better incumbent %d" % (pv, v)
    if ans == "SAT" and ":" in po and po.split(":", 1)[1].startswith("best="):
        ps = po.split(":", 1)[0]
        bv = int(po.split("best=", 1)[1])
        if st == "OPT" and v is not None and better(ps, bv, v):
            return "a solution with objective %d is known, this run proves optimum %d" % (bv, v)
    return ""


def answers(outdirs, outpath):
    by, data = {}, {}
    for od in outdirs:
        rows, _ = load(od)
        for r in rows:
            by.setdefault(r["id"], []).append(r)
        for i, p in load_pairs(od).items():
            data.setdefault(i, set()).add(p["data"])
    lines = ["# M6-T4 / M5-T3: the pinned answer per instance. A later run that disagrees",
             "# with a row here is a FINDING (compare_run.sh --report OUT --pinned THIS).",
             "# answer: SAT | UNSAT | OPT | DISPUTED.  objective: '-' for satisfaction,",
             "# min:V / max:V a proved optimum, min:best=V a best-known incumbent (answer SAT).",
             "# by: the solver(s) whose PROVED result establishes it.  data: the data file",
             "# (pairing is a function of the instance only; '<none>' = the bare model).",
             "id\tanswer\tobjective\tby\tdata"]
    n = 0
    for i in sorted(by):
        rs = by[i]
        v, why = agreement(rs)
        d = ",".join(sorted(data.get(i, {"?"})))
        if len(data.get(i, set())) > 1:
            v, why = "DISAGREE", "the runs paired different data files: " + d
        if v == "DISAGREE":
            lines.append("%s\tDISPUTED\t-\t%s\t%s" % (i, flat(why)[:150], d))
            n += 1
            continue
        unsat = [r for r in rs if r["status"] == "UNSAT"]
        opt = [r for r in rs if r["status"] == "OPT" and objval(r)[1] is not None]
        sat = [r for r in rs if sat_evidence(r)]
        if unsat and not sat:
            ans, obj, who = "UNSAT", "-", unsat
        elif opt:
            s, val = objval(opt[0])
            ans, obj, who = "OPT", "%s:%d" % (s, val), opt
        elif sat:
            senses = [objval(r) for r in sat if objval(r)[0]]
            vals = [vv for ss, vv in senses if vv is not None]
            if senses:
                ss = senses[0][0]
                if not vals:
                    continue
                best = min(vals) if ss == "min" else max(vals)
                ans, obj = "SAT", "%s:best=%d" % (ss, best)
            else:
                ans, obj = "SAT", "-"
            who = sat
        else:
            continue
        lines.append("%s\t%s\t%s\t%s\t%s" % (
            i, ans, obj, ",".join(sorted({r["solver"] for r in who})), d))
        n += 1
    with open(outpath, "w") as f:
        f.write("\n".join(lines) + "\n")
    print("answers: %d instance(s) pinned -> %s" % (n, outpath))
    return 0


def shared(outdirs):
    ok = {}
    for od in outdirs:
        for l in read(os.path.join(od, "flatten.tsv")).splitlines():
            f = l.split("\t")
            if len(f) >= 3:
                ok.setdefault(f[0], {}).setdefault(f[1], set()).add(f[2])
    # Shared = every library flattened it in EVERY table that tried: a flatten that
    # crossed FLATTEN_TIMEOUT in one run and not another is not dependably shared.
    for i in sorted(ok):
        if all(ok[i].get(s) == {"OK"} for s in SOLVERS):
            print(i)
    return 0


def main(a):
    if not a:
        print(__doc__)
        return 2
    cmd, rest = a[0], a[1:]
    if cmd == "prep":
        return prep(rest[0])
    if cmd == "classify":
        return classify(*rest[:7])
    if cmd == "verdict":
        return verdict(*rest[:3])
    if cmd == "report":
        pinned = None
        if "--pinned" in rest:
            k = rest.index("--pinned")
            pinned = rest[k + 1]
            rest = rest[:k] + rest[k + 2:]
        return report(rest, pinned)
    if cmd == "answers":
        return answers(rest[:-1], rest[-1])
    if cmd == "shared":
        return shared(rest)
    print("unknown command %s" % cmd, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
