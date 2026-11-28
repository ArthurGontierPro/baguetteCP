#!/usr/bin/env python3
"""Differential fuzz: baguette against Gecode, both through MiniZinc, on small random models.
This is the harness of docs/reports/2026-11-23-code-review.md section 1.3, as it ran (milestone
M22-review, the fixes that code review found).

Usage: fuzz.py OUTDIR SEED N [baguette flags...]
  FUZZ_BIN   the binary under test (default: _build/default/bin/main.exe of this clone)
  FUZZ_NMAX, FUZZ_CMAX   at most this many variables / constraints per model (6, 5)

Each model is small (domains within -4..4). For each: Gecode's answer, baguette's answer,
VeriPB on baguette's proof, and Gecode re-checking baguette's solution. Every disagreement
is kept in OUTDIR/bad/<seed>_<i>_<verdict>/ with the model, the proof and both outputs
(note.txt); a refusal's reason is appended to OUTDIR/refusals.txt; the solver configuration
MiniZinc runs baguette through is written to OUTDIR/fuzz.msc. The stream ends by printing one
line, the seed and the tally of verdicts. The exit status is 0 whatever was found (read
OUTDIR/bad/); a missing argument stops it on a Python exception (status 1). fuzz2.py is the
search-heavy stream (3-SAT near the threshold, small integer optimisation).

RUN IT ON A NODE, NEVER ON THE LAPTOP (scripts/README.md section 1). Each run is under
`ulimit -v 4000000` and a timeout; launch a stream under systemd-run's MemoryMax.
"""
import os, random, re, subprocess, sys, shutil

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
MSC = None  # written by ensure_msc into the output directory


def ensure_msc(outdir):
    """A solver configuration for the binary under test, with --bits-above declared so a
    stream can pass it (tools/baguette.msc does not declare it)."""
    global MSC
    import json
    binary = os.environ.get("FUZZ_BIN", os.path.join(ROOT, "_build", "default", "bin", "main.exe"))
    cfg = {
        "id": "org.baguette.fuzz", "name": "baguette-fuzz", "version": "0.1.0",
        "mznlib": os.path.join(ROOT, "mznlib"), "executable": binary,
        "supportsMzn": False, "supportsFzn": True, "needsSolns2Out": True,
        "stdFlags": ["-i", "-f", "-n", "-p", "-r", "-s", "-t", "-v"],
        "extraFlags": [["--proof", "proof prefix", "string", ""],
                       ["--no-proof", "no proof", "bool", "false"],
                       ["--bits-above", "bits threshold", "string", "0"],
                       # M19-config-T1 (D-0261): the fixed search, a flag since the free
                       # search became the default; the streams without -f pass it
                       ["--fixed-search", "the fixed search", "bool", "false"]],
    }
    os.makedirs(outdir, exist_ok=True)
    MSC = os.path.join(outdir, "fuzz.msc")
    with open(MSC, "w") as f:
        json.dump(cfg, f, indent=2)
VERIPB = os.path.expanduser("~/.cargo/bin/veripb")
LIMIT = "ulimit -v 4000000; "


def run(cmd, timeout):
    try:
        p = subprocess.run(["bash", "-c", LIMIT + cmd], capture_output=True, text=True,
                           timeout=timeout)
        return p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired:
        return None, "", "TIMEOUT"


def status(out):
    if "=====UNSATISFIABLE=====" in out:
        return "UNSAT", None, None
    if "=====ERROR=====" in out:
        return "ERROR", None, None
    sols = out.split("----------")
    if len(sols) < 2:
        return "UNKNOWN", None, None
    last = sols[-2]
    m = re.search(r"obj=(-?\d+)", last)
    vals = dict(re.findall(r"(\w+)=(-?\d+|true|false)", last))
    if "==========" in out:
        return "OPT", (int(m.group(1)) if m else None), vals
    return "SAT", (int(m.group(1)) if m else None), vals


class Gen:
    def __init__(self, r):
        self.r = r
        self.n = r.randint(3, int(os.environ.get('FUZZ_NMAX', '6')))
        self.k = r.randint(1, 3)
        self.decls = []
        self.cons = []
        self.doms = {}
        for i in range(self.n):
            lo = r.randint(-4, 2)
            hi = r.randint(lo, lo + r.randint(0, 5))
            if r.random() < 0.15 and hi - lo >= 2:
                vals = sorted(set(r.sample(range(lo, hi + 1), r.randint(2, hi - lo + 1))))
                self.decls.append("var {%s}: x%d;" % (",".join(map(str, vals)), i))
                self.doms[i] = (min(vals), max(vals))
            else:
                self.decls.append("var %d..%d: x%d;" % (lo, hi, i))
                self.doms[i] = (lo, hi)
        for j in range(self.k):
            self.decls.append("var bool: b%d;" % j)

    def x(self):
        return "x%d" % self.r.randrange(self.n)

    def xs(self, m):
        idx = self.r.sample(range(self.n), min(m, self.n))
        return ["x%d" % i for i in idx]

    def b(self):
        return "b%d" % self.r.randrange(self.k)

    def lin(self):
        r = self.r
        terms = []
        for v in self.xs(r.randint(1, 3)):
            c = r.choice([-3, -2, -1, 1, 1, 2, 3])
            terms.append("%d*%s" % (c, v))
        return " + ".join(terms)

    def constraint(self):
        r = self.r
        kind = r.randrange(26)
        rel = r.choice(["<=", ">=", "=", "!=", "<", ">"])
        k = r.randint(-6, 6)
        if kind == 0:
            return "%s %s %d" % (self.lin(), rel, k)
        if kind == 1:
            a, b_, c = self.x(), self.x(), self.x()
            return "%s * %s = %s" % (a, b_, c)
        if kind == 2:
            a, b_, c = self.x(), self.x(), self.x()
            return "%s div %s = %s" % (a, b_, c)
        if kind == 3:
            a, b_, c = self.x(), self.x(), self.x()
            return "%s mod %s = %s" % (a, b_, c)
        if kind == 4:
            return "abs(%s) = %s" % (self.x(), self.x())
        if kind == 5:
            return "max([%s]) = %s" % (",".join(self.xs(r.randint(2, 3))), self.x())
        if kind == 6:
            return "min([%s]) = %s" % (",".join(self.xs(r.randint(2, 3))), self.x())
        if kind == 7:
            arr = [r.randint(-4, 4) for _ in range(r.randint(2, 5))]
            return "[%s][%s] = %s" % (",".join(map(str, arr)), self.x(), self.x())
        if kind == 8:
            return "[%s][%s] = %s" % (",".join(self.xs(r.randint(2, 3))), self.x(), self.x())
        if kind == 9:
            return "alldifferent([%s])" % ",".join(self.xs(r.randint(2, 4)))
        if kind == 10:
            xs = self.xs(r.randint(2, 4))
            cover = sorted(r.sample(range(-3, 4), r.randint(1, 3)))
            cnts = [self.x() for _ in cover]
            return "global_cardinality([%s],[%s],[%s])" % (
                ",".join(xs), ",".join(map(str, cover)), ",".join(cnts))
        if kind == 11:
            return "%s <-> (%s %s %s)" % (self.b(), self.x(), rel, self.x())
        if kind == 12:
            return "%s <-> (%s %s %d)" % (self.b(), self.lin(), rel, k)
        if kind == 13:
            op = r.choice(["\\/", "/\\", "->", "<->", "xor", "!="])
            if op == "!=":
                return "%s != %s" % (self.b(), self.b())
            return "%s = (%s %s %s)" % (self.b(), self.b(), op, self.b())
        if kind == 14:
            return "bool2int(%s) + bool2int(%s) %s %s" % (self.b(), self.b(), rel, self.x())
        if kind == 15:
            s = sorted(r.sample(range(-4, 5), r.randint(1, 4)))
            return "%s in {%s}" % (self.x(), ",".join(map(str, s)))
        if kind == 16:
            s = sorted(r.sample(range(-4, 5), r.randint(1, 4)))
            return "%s <-> (%s in {%s})" % (self.b(), self.x(), ",".join(map(str, s)))
        if kind == 17:
            return "member([%s], %s)" % (",".join(self.xs(r.randint(1, 3))), self.x())
        if kind == 18:
            m = r.randint(2, 3)
            f = ["f%d" % i for i in range(m)]
            g = ["g%d" % i for i in range(m)]
            self.decls.append("array[1..%d] of var 1..%d: F%d;" % (m, m, len(self.cons)))
            self.decls.append("array[1..%d] of var 1..%d: G%d;" % (m, m, len(self.cons)))
            tag = len(self.cons)
            link = " /\\ ".join("F%d[%d] %s %s" % (tag, i + 1, r.choice(["<=", ">=", "!="]), self.x())
                                for i in range(r.randint(0, 2))) or "true"
            return "inverse(F%d, G%d) /\\ %s" % (tag, tag, link)
        if kind == 19:
            m = r.randint(2, 3)
            ss = self.xs(m)
            d = [r.randint(0, 3) for _ in ss]
            rr = [r.randint(0, 3) for _ in ss]
            cap = r.randint(0, 4)
            return "cumulative([%s],[%s],[%s],%d)" % (",".join(ss), ",".join(map(str, d)),
                                                      ",".join(map(str, rr)), cap)
        if kind == 20:
            ss = self.xs(r.randint(2, 3))
            d = [r.randint(0, 3) for _ in ss]
            return "disjunctive([%s],[%s])" % (",".join(ss), ",".join(map(str, d)))
        if kind == 21:
            # regular over values 1..2 with a random 3-state DFA, on fresh vars
            tag = len(self.cons)
            m = r.randint(2, 4)
            self.decls.append("array[1..%d] of var 1..2: R%d;" % (m, tag))
            rows = []
            for q in range(3):
                rows.append(",".join(str(r.randint(0, 3)) for _ in range(2)))
            fin = sorted(r.sample(range(1, 4), r.randint(1, 3)))
            link = "R%d[1] %s %s" % (tag, r.choice(["<=", ">=", "=", "!="]), self.x()) \
                if r.random() < 0.6 else "true"
            return "regular(R%d, 3, 2, [|%s|], 1, {%s}) /\\ %s" % (
                tag, "|".join(rows), ",".join(map(str, fin)), link)
        if kind == 22:
            return "count([%s], %d) %s %s" % (",".join(self.xs(r.randint(2, 4))),
                                              r.randint(-2, 2), rel, self.x())
        if kind == 23:
            return "%s %s %s" % (self.x(), rel, self.x())
        if kind == 24:
            return "lex_less([%s],[%s])" % (",".join(self.xs(2)), ",".join(self.xs(2)))
        return "table([%s], [|%s|])" % (
            ",".join(self.xs(2)),
            "|".join("%d,%d" % (r.randint(-3, 3), r.randint(-3, 3)) for _ in range(r.randint(1, 5))))

    def model(self):
        r = self.r
        for _ in range(r.randint(1, int(os.environ.get('FUZZ_CMAX', '5')))):
            self.cons.append(self.constraint())
        head = 'include "globals.mzn";\n' + "\n".join(self.decls) + "\n"
        body = "".join("constraint %s;\n" % c for c in self.cons)
        outs = ['"x%d=\\(x%d) "' % (i, i) for i in range(self.n)]
        outs += ['"b%d=\\(b%d) "' % (j, j) for j in range(self.k)]
        kind = r.random()
        if kind < 0.5:
            solve = "solve satisfy;\n"
            obj = ""
        else:
            obj = "var -200..200: obj;\nconstraint obj = %s;\n" % self.lin()
            solve = "solve %s obj;\n" % r.choice(["minimize", "maximize"])
            outs.append('"obj=\\(obj)"')
        out = "output [%s, \"\\n\"];\n" % ", ".join(outs)
        return head + body + obj + solve + out


def main():
    outdir, seed, n = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    extra = " ".join(sys.argv[4:])
    os.makedirs(os.path.join(outdir, "bad"), exist_ok=True)
    ensure_msc(outdir)
    r = random.Random(seed)
    tally = {}
    for it in range(n):
        g = Gen(r)
        mzn = g.model()
        path = os.path.join(outdir, "m.mzn")
        open(path, "w").write(mzn)
        rc_g, out_g, err_g = run("minizinc --solver gecode %s" % path, 30)
        st_g, obj_g, _ = status(out_g) if rc_g is not None else ("TIMEOUT", None, None)
        prefix = os.path.join(outdir, "p")
        for ext in (".opb", ".pbp"):
            if os.path.exists(prefix + ext):
                os.remove(prefix + ext)
        rc_b, out_b, err_b = run("minizinc --solver %s %s --proof %s %s" % (MSC, path, prefix, extra), 30)
        st_b, obj_b, vals_b = status(out_b) if rc_b is not None else ("TIMEOUT", None, None)
        verdict = "ok"
        note = ""
        if st_b in ("ERROR", "UNKNOWN", "TIMEOUT") or rc_b not in (0,):
            if "not supported" in err_b or "not implemented" in err_b or "refus" in err_b.lower():
                verdict = "refused"
            else:
                verdict = "bag-error"
            note = (err_b or out_b)[-600:]
        elif st_g in ("TIMEOUT", "ERROR", "UNKNOWN"):
            verdict = "gecode-" + st_g
        else:
            same = (st_g == st_b) or ({st_g, st_b} <= {"SAT", "OPT"})
            if not same:
                verdict = "STATUS-MISMATCH"
                note = "gecode=%s baguette=%s" % (st_g, st_b)
            elif st_b == "OPT" and obj_g != obj_b:
                verdict = "OBJ-MISMATCH"
                note = "gecode=%s baguette=%s" % (obj_g, obj_b)
            # proof check
            if verdict == "ok" and os.path.exists(prefix + ".pbp"):
                rc_v, out_v, err_v = run("%s %s.opb %s.pbp" % (VERIPB, prefix, prefix), 60)
                txt = (out_v or "") + (err_v or "")
                if rc_v != 0 or "VERIFIED" not in txt:
                    verdict = "PROOF-REJECTED"
                    note = txt[-800:]
            # solution re-check
            if verdict == "ok" and st_b in ("SAT", "OPT") and vals_b:
                fix = "".join("constraint %s = %s;\n" % (k, v) for k, v in vals_b.items()
                              if k != "obj")
                chk = mzn.replace("solve satisfy;", "").replace("solve minimize obj;", "").replace(
                    "solve maximize obj;", "") + fix + "solve satisfy;\n"
                cpath = os.path.join(outdir, "chk.mzn")
                open(cpath, "w").write(chk)
                rc_c, out_c, _ = run("minizinc --solver gecode %s" % cpath, 30)
                if "=====UNSATISFIABLE=====" in out_c:
                    verdict = "BAD-SOLUTION"
                    note = str(vals_b)
        tally[verdict] = tally.get(verdict, 0) + 1
        if verdict not in ("ok", "refused") and not verdict.startswith("gecode-"):
            d = os.path.join(outdir, "bad", "%d_%d_%s" % (seed, it, verdict))
            os.makedirs(d, exist_ok=True)
            shutil.copy(path, os.path.join(d, "m.mzn"))
            for ext in (".opb", ".pbp"):
                if os.path.exists(prefix + ext):
                    shutil.copy(prefix + ext, os.path.join(d, "p" + ext))
            open(os.path.join(d, "note.txt"), "w").write(
                "%s\n%s\n--- gecode\n%s\n--- baguette\n%s\n%s\n" % (verdict, note, out_g, out_b, err_b[-2000:]))
        if verdict == "refused":
            m = re.search(r"(not supported|not implemented|[Rr]efus)[^\n]{0,120}", err_b)
            key = m.group(0)[:100] if m else "?"
            rf = os.path.join(outdir, "refusals.txt")
            open(rf, "a").write(key + "\n")
    print(seed, tally, flush=True)


if __name__ == "__main__":
    main()
