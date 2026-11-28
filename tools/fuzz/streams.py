#!/usr/bin/env python3
"""The fuzz lane's second-generation streams (M22-review-T7, D-0258). Each stream is a function
of its seed: the same (stream, seed, N, binary, mznlib) gives the same models and the same runs.

Usage: streams.py STREAM OUTDIR SEED N

  globals   random small models over the globals baguette routes through mznlib/ or handles
            natively (global_cardinality in all five forms with covers that REPEAT a value or
            miss one, all_different, alldifferent_except_0, nvalue, table, regular, element,
            inverse, circuit, cumulative, disjunctive, bin_packing*, lex_less(eq) over int and
            bool, value_precede, count, member, maximum/minimum), with repeated variables,
            constants mixed in and degenerate sizes (empty arrays, one element)
  configs   one model (globals, fuzz.py's Gen, fuzz2's 3-SAT and integer optimisation) under
            every search configuration of CONFIGS below, the default and the opt-in ones, the
            retention policies forced to evict early among them; every configuration must agree
            with Gecode and with each other
  incr      optimisation models under -i: each printed objective strictly improves on the
            last, every printed solution is re-checked, the final answer is the non-`-i` run's
  limit     runs CUT by BAGUETTE_NODE_LIMIT or a tiny --time-limit: a stopped run (its stderr
            `limit:` line) must claim neither optimality nor unsatisfiability, its printed
            solutions must hold, and its partial proof must be accepted for what it claims
            (NO CONCLUSION, or BOUNDS that contain Gecode's optimum)
  e2e       models over the builtins cake_pb_cp covers, through tools/e2e/chain.sh both ways
            (bridged, and E2E_SOLVER=1, baguette --e2e): VERIFIED must agree with Gecode;
            SKIPPED (a construct the chain does not cover) is counted, FAIL is kept
  wide      FRONT END ONLY: domains wider than 2^20. The run must answer (and agree with
            Gecode when Gecode answers) or refuse (exit 3, or 5 for the heap budget), within
            `ulimit -v 4000000` and the timeout; never crash. Proofs are written, not checked.

What every stream checks on a baguette run (`check_run`): the status and objective against
Gecode's; VeriPB on the proof, and its `s VERIFIED` conclusion against the claim (a proof that
verifies a different conclusion than the answer printed is PROOF-CONCLUSION); Gecode on the model
with baguette's printed solution fixed (BAD-SOLUTION when that is unsatisfiable).

Baguette runs on the FlatZinc MiniZinc flattens once per model with mznlib/ (FUZZ_MZNLIB
overrides it: the acceptance test of `globals` flattens with the mznlib of 99d0e39~1), not
through MiniZinc, so the many configurations of one model share one flattening.

Outputs: OUTDIR/bad/<seed>_<i>_<verdict>[_<config>]/ for every disagreement (m.mzn, m.fzn, the
proof, note.txt), OUTDIR/slow/ for timeouts (note only), OUTDIR/refusals.txt, and ONE final line
on stdout: the stream, the seed and the tally of verdicts. Proofs of agreeing runs are deleted.
Exit 0 whatever was found (the lane reads bad/); a bad argument exits 2.

Env: FUZZ_BIN (the binary, default this clone's), FUZZ_MZNLIB, CAKE_PB_CP (e2e only).
RUN IT ON A NODE, NEVER ON THE LAPTOP (scripts/README.md section 1): each solver call is under
`ulimit -v 4000000` and a timeout.
"""
import glob, json, os, random, re, shutil, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import fuzz as fz  # noqa: E402  (Gen, status; importing it runs nothing)
import fuzz2 as fz2  # noqa: E402  (sat3, intopt)

BIN = os.environ.get("FUZZ_BIN", os.path.join(ROOT, "_build", "default", "bin", "main.exe"))
MZNLIB = os.environ.get("FUZZ_MZNLIB", os.path.join(ROOT, "mznlib"))
VERIPB = os.path.expanduser("~/.cargo/bin/veripb")
LIMIT = "ulimit -v 4000000; "
T_SOLVE, T_CHECK, T_GECODE = 30, 120, 30

# The search configurations of the `configs` stream: (name, flags, env). The retention ones force
# an eviction early: fifo:1 and lbd:1 keep one learned constraint, and the tiered parameters are
# the ones D-0257's test uses for "an eviction at every learned constraint" (core 0, mid 0,
# first 1, inc 0, mid_every 1). Every opt-in knob runs under the default search and under --cdcl.
EVICT = "tiered:core=0,mid=0,first=1,inc=0,mid_every=1"
# Since D-0261 (M19-config-T1) the default is the free search; `fixed` and `cdcl-fixed` keep the
# fixed search, the default before it, among the configurations compared.
CONFIGS = [("default", [], {}), ("fixed", ["--fixed-search"], {}), ("cdcl", ["--cdcl"], {}),
           ("cdcl-fixed", ["--cdcl", "--fixed-search"], {}),
           ("cdcl-chrono5", ["--cdcl", "--chrono", "5"], {}), ("free", ["-f"], {})]
for _name, _env in [("minimise-rec", {"BAGUETTE_MINIMISE": "rec"}),
                    ("priority-classes", {"BAGUETTE_PRIORITY": "classes"}),
                    ("probe-root", {"BAGUETTE_PROBE": "root"}),
                    ("ret-keep_all", {"BAGUETTE_RETENTION": "keep_all"}),
                    ("ret-fifo1", {"BAGUETTE_RETENTION": "fifo:1"}),
                    ("ret-lbd1", {"BAGUETTE_RETENTION": "lbd:1"}),
                    ("ret-evict", {"BAGUETTE_RETENTION": EVICT})]:
    CONFIGS.append((_name, [], _env))
    CONFIGS.append(("cdcl-" + _name, ["--cdcl"], _env))


def sh(cmd, timeout, env=None, cwd=None, stdin=None, cap=True):
    """bash -c under the memory cap (unless cap is False: cake_pb_cp reserves its heap up front,
    and chain.sh caps baguette itself); (rc, out, err), rc None on timeout."""
    e = dict(os.environ)
    if env:
        e.update(env)
    try:
        p = subprocess.run(["bash", "-c", (LIMIT if cap else "") + cmd], capture_output=True, text=True,
                           timeout=timeout, env=e, cwd=cwd, input=stdin)
        return p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired:
        return None, "", "TIMEOUT"


def q(s):
    return "'" + s.replace("'", "'\\''") + "'"


# ---------------------------------------------------------------------------------------------
# The globals generator. DO NOT REORDER ITS RANDOM CALLS: every seed in D-0258 depends on them.

class GlobGen:
    KINDS = ["gcc", "gcc_closed", "gcc_lu", "gcc_lu_closed", "alldiff", "alldiff0", "nvalue",
             "table", "regular", "element", "inverse", "circuit", "cumulative", "disjunctive",
             "bin_packing", "lex_int", "lex_bool", "value_precede", "count", "member", "maxmin"]

    def __init__(self, r, kinds=None, side=True):
        self.r = r
        self.kinds = kinds or self.KINDS
        self.side = side
        self.n = r.randint(2, 6)
        self.nb = r.randint(1, 3)
        self.decls, self.outs, self.cons = [], [], []
        self.dom = {}
        for i in range(self.n):
            lo = r.randint(-1, 1)
            hi = lo + r.randint(0, 3)
            self.decls.append("var %d..%d: x%d;" % (lo, hi, i))
            self.outs.append("x%d" % i)
            self.dom["x%d" % i] = (lo, hi)
        for j in range(self.nb):
            self.decls.append("var bool: b%d;" % j)
            self.outs.append("b%d" % j)
        self.decls.append("array[1..0] of var -1..4: E;")
        self.fresh = 0

    def var(self):
        return "x%d" % self.r.randrange(self.n)

    def val(self, t):
        """A value term t can take: a value of its domain, or the constant itself."""
        if t in self.dom:
            return self.r.randint(*self.dom[t])
        return int(t)

    def term(self):
        return str(self.r.randint(-1, 4)) if self.r.random() < 0.15 else self.var()

    def items(self, lo, hi):
        """lo..hi terms: distinct variables mostly, a REPEATED one a quarter of the time, a
        constant now and then."""
        r = self.r
        m = r.randint(lo, hi)
        vs = r.sample(range(self.n), min(m, self.n))
        out = ["x%d" % v for v in vs] + [self.var() for _ in range(m - len(vs))]
        if m >= 2 and r.random() < 0.25:
            out[r.randrange(m)] = r.choice(out)
        return [str(r.randint(-1, 4)) if r.random() < 0.12 else t for t in out]

    def arr(self, lo=0, hi=4):
        its = self.items(lo, hi)
        if not its:
            return "E" if self.r.random() < 0.5 else "[]", []
        return "[%s]" % ",".join(its), its

    def barr(self, lo=0, hi=3):
        r = self.r
        m = r.randint(lo, hi)
        items = [(r.choice(["true", "false"]) if r.random() < 0.15
                  else "b%d" % r.randrange(self.nb)) for _ in range(m)]
        return "[%s]" % ",".join(items) if items else "[]"

    def new_array(self, m, lo, hi, prefix):
        name = "%s%d" % (prefix, self.fresh)
        self.fresh += 1
        self.decls.append("array[1..%d] of var %d..%d: %s;" % (m, lo, hi, name))
        if m > 0:
            self.outs.append(name)
        return name

    def new_var(self, lo, hi, prefix="c"):
        name = "%s%d" % (prefix, self.fresh)
        self.fresh += 1
        self.decls.append("var %d..%d: %s;" % (lo, hi, name))
        self.outs.append(name)
        self.dom[name] = (lo, hi)
        return name

    def link(self, name, m):
        r = self.r
        cs = []
        for _ in range(r.randint(0, 2) if m else 0):
            cs.append("%s[%d] %s %s" % (name, r.randint(1, m), r.choice(["=", "!=", "<=", ">="]),
                                        self.var()))
        return cs

    def cover(self, its):
        """1..3 values (0 now and then), mostly ones the array can take, sometimes one it
        cannot, and a REPEATED value 40% of the time (D-0255)."""
        r = self.r
        k = r.randint(0, 3) if r.random() < 0.1 else r.randint(1, 3)
        vals = [self.val(r.choice(its)) if its and r.random() < 0.8 else r.randint(-1, 4)
                for _ in range(k)]
        if k >= 1 and r.random() < 0.4:
            vals.insert(r.randrange(len(vals) + 1), r.choice(vals))
        return vals

    def gcc(self, closed, lu):
        r = self.r
        xs, its = self.arr(1, 4)
        cv = self.cover(its)
        name = "global_cardinality%s" % ("_closed" if closed else "")
        # a witness assignment of the array, so that the counts are often satisfiable
        wit = [self.val(t) for t in its]
        if closed and r.random() < 0.7:  # a closed cover holds every value the witness takes
            cv = cv + [v for v in sorted(set(wit)) if v not in cv]
            r.shuffle(cv)
        k = len(cv)
        occ = [wit.count(v) for v in cv]
        if lu:
            lb = [max(0, o - r.randint(0, 1)) if r.random() < 0.8 else r.randint(0, 2) for o in occ]
            ub = [l + r.randint(0, 2) for l in lb]
            return "%s(%s, [%s], [%s], [%s])" % (name, xs, ",".join(map(str, cv)),
                                                 ",".join(map(str, lb)), ",".join(map(str, ub)))
        if r.random() < 0.3:
            cn = "[%s]" % ",".join(str(o if r.random() < 0.8 else r.randint(0, 3)) for o in occ)
        else:
            cs = []
            for _ in range(k):
                cs.append(self.new_var(0, r.randint(1, len(its) + 1)) if r.random() < 0.7 else self.var())
            cn = "[%s]" % ",".join(cs)
        return "%s(%s, [%s], %s)" % (name, xs, ",".join(map(str, cv)), cn)

    def glob(self):
        r = self.r
        kind = r.choice(self.kinds)
        if kind == "gcc":
            return [self.gcc(False, False)]
        if kind == "gcc_closed":
            return [self.gcc(True, False)]
        if kind == "gcc_lu":
            return [self.gcc(False, True)]
        if kind == "gcc_lu_closed":
            return [self.gcc(True, True)]
        if kind == "alldiff":
            return ["all_different(%s)" % self.arr(0, 4)[0]]
        if kind == "alldiff0":
            return ["alldifferent_except_0(%s)" % self.arr(0, 4)[0]]
        if kind == "nvalue":
            nv = self.new_var(0, r.randint(1, 4), "n")
            return ["nvalue(%s, %s)" % (nv, self.arr(0, 4)[0])]
        if kind == "table":
            w = r.randint(1, 3)
            xs = self.items(w, w)
            t = [[self.val(x) if r.random() < 0.85 else r.randint(-1, 3) for x in xs]
                 for _ in range(r.randint(0, 6))]
            body = "array2d(1..%d, 1..%d, [%s])" % (len(t), w, ",".join(str(v) for row in t for v in row))
            return ["table([%s], %s)" % (",".join(xs), body)]
        if kind == "regular":
            qn, sn, ln = r.randint(1, 4), r.randint(1, 3), r.randint(0, 4)
            name = self.new_array(ln, 1, sn, "R")
            d = [[r.randint(1, qn) if r.random() < 0.8 else 0 for _ in range(sn)] for _ in range(qn)]
            fin = sorted(set(r.randint(1, qn) for _ in range(r.randint(0, qn + 1))))
            body = "array2d(1..%d, 1..%d, [%s])" % (qn, sn, ",".join(str(v) for row in d for v in row))
            return ["regular(%s, %d, %d, %s, %d, {%s})" % (
                name, qn, sn, body, r.randint(1, qn), ",".join(map(str, fin)))] + self.link(name, ln)
        if kind == "element":
            a, its = self.arr(1, 4)
            y = self.term() if r.random() < 0.3 else str(self.val(r.choice(its)))
            if r.random() < 0.7 and y.lstrip("-").isdigit():
                y = self.var()
            return ["%s[%s] = %s" % (a, self.var(), y)]
        if kind == "inverse":
            m = r.randint(1, 3)
            f = self.new_array(m, 1, m, "F")
            g = f if r.random() < 0.2 else self.new_array(m, 1, m, "G")
            return ["inverse(%s, %s)" % (f, g)] + self.link(f, m)
        if kind == "circuit":
            m = r.randint(2, 4)  # not 1: std says false (xs[1] != 1), Gecode says true (D-0258)
            c = self.new_array(m, 1, m, "C")
            return ["circuit(%s)" % c] + self.link(c, m)
        if kind in ("cumulative", "disjunctive"):
            m = r.randint(0, 3)
            ss = self.items(m, m)
            nonneg = [v for v in self.dom if self.dom[v][0] >= 0]
            def dur():
                return r.choice(nonneg) if nonneg and r.random() < 0.2 else str(r.randint(0, 3))
            dd = [dur() for _ in range(m)]
            if kind == "disjunctive":
                op = r.choice(["disjunctive", "disjunctive_strict"])
                return ["%s([%s], [%s])" % (op, ",".join(ss), ",".join(dd))]
            rr = [dur() for _ in range(m)]
            # Gecode 6.4.0 answers UNSAT on a task of duration 0 whose resource exceeds the
            # capacity (`cumulative([x],[0],[1],0)`; Chuffed, CP-SAT, HiGHS and std: SAT, D-0258),
            # so the capacity is at least every task's largest resource.
            top = max([self.dom[t][1] if t in self.dom else int(t) for t in rr] + [0])
            cap = str(r.randint(top, top + 2))
            return ["cumulative([%s], [%s], [%s], %s)" % (",".join(ss), ",".join(dd), ",".join(rr), cap)]
        if kind == "bin_packing":
            m, nbins = r.randint(0, 3), r.randint(1, 3)
            b = self.new_array(m, 1, nbins, "P")
            w = "[%s]" % ",".join(str(r.randint(0, 3)) for _ in range(m))
            op = r.randrange(3)
            if op == 0:
                return ["bin_packing(%d, %s, %s)" % (r.randint(0, 5), b, w)] + self.link(b, m)
            if op == 1:
                cap = "[%s]" % ",".join(str(r.randint(0, 5)) for _ in range(nbins))
                return ["bin_packing_capa(%s, %s, %s)" % (cap, b, w)] + self.link(b, m)
            ld = self.new_array(nbins, 0, r.randint(0, 6), "L")
            return ["bin_packing_load(%s, %s, %s)" % (ld, b, w)] + self.link(b, m)
        if kind == "lex_int":
            return ["%s(%s, %s)" % (r.choice(["lex_lesseq", "lex_less"]), self.arr(0, 3)[0], self.arr(0, 3)[0])]
        if kind == "lex_bool":
            return ["%s(%s, %s)" % (r.choice(["lex_lesseq", "lex_less"]), self.barr(), self.barr())]
        if kind == "value_precede":
            return ["value_precede(%d, %d, %s)" % (r.randint(-1, 3), r.randint(-1, 3), self.arr(0, 4)[0])]
        if kind == "count":
            a, its = self.arr(0, 4)
            c = self.new_var(0, r.randint(0, len(its)), "k")
            return ["count_eq(%s, %s, %s)" % (a, self.term(), c)]
        if kind == "member":
            return ["member(%s, %s)" % (self.arr(1, 3)[0], self.var())]
        # maxmin
        return ["%s(%s, %s)" % (r.choice(["maximum", "minimum"]), self.var(), self.arr(1, 4)[0])]

    def sidecon(self):
        r = self.r
        k = r.randrange(3)
        if k == 0:
            return "%s != %s" % (self.var(), self.var())
        if k == 1:
            return "%d*%s + %d*%s <= %d" % (r.choice([-2, -1, 1, 2]), self.var(), r.choice([-1, 1, 2]),
                                             self.var(), r.randint(-2, 6))
        return "b%d <-> (%s <= %s)" % (r.randrange(self.nb), self.var(), self.var())

    def model(self, force_opt=False):
        r = self.r
        for _ in range(r.randint(1, 3)):
            self.cons += self.glob()
        if self.side:
            for _ in range(r.randint(0, 2)):
                self.cons.append(self.sidecon())
        opt = force_opt or r.random() < 0.4
        body = "".join("constraint %s;\n" % c for c in self.cons)
        outs = ['"%s=\\(%s) "' % (v, v) for v in self.outs]
        if opt:
            terms = " + ".join("%d*x%d" % (r.choice([-2, -1, 1, 2, 3]), i) for i in range(self.n))
            body += "var -60..60: obj;\nconstraint obj = %s;\n" % terms
            body += "solve %s obj;\n" % r.choice(["minimize", "maximize"])
            outs.append('"obj=\\(obj)"')
        else:
            body += "solve satisfy;\n"
        return ('include "globals.mzn";\n' + "\n".join(self.decls) + "\n" + body +
                "output [%s, \"\\n\"];\n" % ", ".join(outs))


# The e2e stream's builtins: what fzn2scp.py covers once MiniZinc has flattened them.
E2E_KINDS = ["gcc", "alldiff", "element", "inverse", "member", "maxmin", "regular", "cumulative"]


def e2e_model(r):
    """A model over the builtins the end-to-end chain covers (tools/e2e/fzn2scp.py's COVERED)."""
    g = GlobGen(r, kinds=E2E_KINDS, side=False)
    for _ in range(r.randint(1, 3)):
        g.cons += g.glob()
    for _ in range(r.randint(0, 3)):
        k = r.randrange(5)
        a, b = g.var(), g.var()
        if k == 0:
            g.cons.append("%s != %s" % (a, b))
        elif k == 1:
            g.cons.append("%d*%s + %d*%s %s %d" % (r.choice([-2, -1, 1, 3]), a, r.choice([-1, 1, 2]), b,
                                                   r.choice(["<=", "=", "!="]), r.randint(-2, 6)))
        elif k == 2:
            g.cons.append("abs(%s) = %s" % (a, b))
        elif k == 3:
            g.cons.append("b%d <-> (%s %s %s)" % (r.randrange(g.nb), a, r.choice(["<=", "=", "!="]), b))
        else:
            g.cons.append("b%d \\/ b%d \\/ not b%d" % (r.randrange(g.nb), r.randrange(g.nb), r.randrange(g.nb)))
    return g.model()


def wide_model(r):
    """Domains wider than 2^20, a few arithmetic and global constraints. Front end only."""
    n = r.randint(2, 4)
    decls, cons = [], []
    for i in range(n):
        e = r.choice([21, 24, 28, 30, 31, 32, 40, 50, 62])
        lo = -r.randint(0, 2 ** e) if r.random() < 0.5 else r.randint(-5, 5)
        hi = lo + 2 ** e + r.randint(0, 9)
        decls.append("var %d..%d: x%d;" % (lo, hi, i))
    for _ in range(r.randint(1, 4)):
        a, b, c = ("x%d" % r.randrange(n) for _ in range(3))
        k = r.randrange(8)
        big = r.randint(-2 ** 22, 2 ** 22)
        if k == 0:
            cons.append("%d*%s + %d*%s <= %d" % (r.randint(-9, 9), a, r.randint(-9, 9), b, big))
        elif k == 1:
            cons.append("%s + %s = %s" % (a, b, c))
        elif k == 2:
            cons.append("%s != %s" % (a, b))
        elif k == 3:
            cons.append("%s * %s = %s" % (a, b, c))
        elif k == 4:
            cons.append("abs(%s) >= %d" % (a, abs(big)))
        elif k == 5:
            cons.append("max([%s,%s]) = %s" % (a, b, c))
        elif k == 6:
            cons.append("%s div %d = %s" % (a, r.randint(1, 999), b))
        else:
            cons.append("[%d,%d,%d][%s] = %s" % (big, -big, 2 ** 21, "x%d" % r.randrange(n), b))
    if r.random() < 0.3:
        cons.append("alldifferent([%s])" % ",".join("x%d" % i for i in range(n)))
    solve = r.choice(["solve satisfy;", "solve minimize x0;", "solve maximize x%d;" % (n - 1)])
    obj = ""
    if solve != "solve satisfy;":
        v = solve.split()[-1].rstrip(";")
        obj = "var int: obj = %s;\n" % v
        solve = solve.replace(v, "obj")
    outs = ['"x%d=\\(x%d) "' % (i, i) for i in range(n)]
    if obj:
        outs.append('"obj=\\(obj)"')
    return ('include "globals.mzn";\n' + "\n".join(decls) + "\n" +
            "".join("constraint %s;\n" % c for c in cons) + obj + solve + "\n" +
            "output [%s, \"\\n\"];\n" % ", ".join(outs))


def any_model(r, force_opt=False):
    """The `configs`/`incr`/`limit` model mix: globals, fuzz.py's Gen, fuzz2's two families."""
    k = r.random()
    if force_opt:
        if k < 0.4:
            return GlobGen(r).model(force_opt=True)
        if k < 0.7:
            return fz2.intopt(r)
        for _ in range(20):
            m = fz.Gen(r).model()
            if "solve satisfy" not in m:
                return m
        return fz2.intopt(r)
    if k < 0.35:
        return GlobGen(r).model()
    if k < 0.6:
        return fz.Gen(r).model()
    if k < 0.8:
        return fz2.sat3(r)
    return fz2.intopt(r)


# ---------------------------------------------------------------------------------------------
# Running and judging.

def write_msc(outdir):
    cfg = {"id": "org.baguette.fuzz", "name": "baguette-fuzz", "version": "0.1.0",
           "mznlib": MZNLIB, "executable": BIN, "supportsMzn": False, "supportsFzn": True,
           "needsSolns2Out": True, "stdFlags": ["-i", "-f", "-n", "-p", "-r", "-s", "-t", "-v"],
           "extraFlags": [["--fixed-search", "the fixed search (D-0261)", "bool", "false"]]}
    path = os.path.join(outdir, "fuzz.msc")
    with open(path, "w") as f:
        json.dump(cfg, f, indent=2)
    return path


def parse_mzn(out):
    """baguette's output after solns2out (the model's own output item, `name=value ` items):
    (status, [solution dicts]); status SAT/OPT/UNSAT/UNKNOWN/ERROR. Through the .ozn rather than
    the raw FlatZinc because a variable MiniZinc fixed at flattening is not in the .fzn's output,
    the objective among them."""
    if "=====ERROR=====" in out:
        return "ERROR", []
    if "=====UNSATISFIABLE=====" in out:
        return "UNSAT", []
    sols, cur = [], {}
    for line in out.splitlines():
        if line.strip() == "----------":
            sols.append(cur)
            cur = {}
            continue
        for k, v in re.findall(r"(\w+)=(\[[^\]]*\]|-?\d+|true|false)", line):
            cur[k] = v
    if "==========" in out and sols:
        return "OPT", sols
    if sols:
        return "SAT", sols
    return "UNKNOWN", []


def direction(fzn_text):
    m = re.search(r"^solve\s.*\b(minimize|maximize)\b", fzn_text, re.M)
    return m.group(1) if m else None


def objval(sol):
    v = sol.get("obj")
    return int(v) if v is not None and re.match(r"^-?\d+$", v) else None


def better(a, b, d):
    return a < b if d == "minimize" else a > b


def pbval(v, d):
    """An objective value as VeriPB's BOUNDS state it: negated for maximize (the PB objective is
    minimised)."""
    return v if d == "minimize" else -v


def parse_inf(tok):
    if tok.lstrip("+") == "INF":
        return float("inf")
    if tok == "-INF":
        return float("-inf")
    return int(tok)


class Model:
    """One model: its MiniZinc text, Gecode's answer, its FlatZinc for baguette."""

    def __init__(self, ctx, mzn, it, gecode_timeout=T_GECODE):
        self.ctx, self.mzn, self.it = ctx, mzn, it
        d = ctx.outdir
        self.mzn_path = os.path.join(d, "m.mzn")
        self.fzn_path = os.path.join(d, "m.fzn")
        open(self.mzn_path, "w").write(mzn)
        if os.path.exists(self.fzn_path):
            os.remove(self.fzn_path)
        rc_g, out_g, err_g = sh("minizinc --solver gecode %s" % q(self.mzn_path), gecode_timeout)
        self.g_out = out_g + err_g[-400:]
        self.st_g, self.obj_g, _ = fz.status(out_g) if rc_g is not None else ("TIMEOUT", None, None)
        if rc_g not in (0, None) and self.st_g == "UNKNOWN":
            self.st_g = "ERROR"
        self.ozn_path = os.path.join(d, "m.ozn")
        rc_c, _, err_c = sh("minizinc -c --solver %s %s -o %s --ozn %s" % (
            q(ctx.msc), q(self.mzn_path), q(self.fzn_path), q(self.ozn_path)), 60)
        self.flat_ok = rc_c == 0 and os.path.exists(self.fzn_path)
        self.flat_err = err_c[-600:]
        self.fzn = open(self.fzn_path).read() if self.flat_ok else ""
        self.dir = direction(self.fzn)


class Ctx:
    def __init__(self, stream, outdir, seed):
        self.stream, self.outdir, self.seed = stream, outdir, seed
        os.makedirs(os.path.join(outdir, "bad"), exist_ok=True)
        self.msc = write_msc(outdir)
        self.tally = {}

    def count(self, v):
        self.tally[v] = self.tally.get(v, 0) + 1

    def keep(self, model, verdict, note, cfg=None, prefix=None, sub="bad"):
        name = "%d_%d_%s%s" % (self.seed, model.it, verdict, ("_" + cfg) if cfg else "")
        if "MISMATCH" in verdict:
            # two more opinions, for the triage only: never a tie-break (Chuffed shares std's
            # repeated-cover row with mznlib before D-0255, and would have outvoted Gecode)
            for s in ("chuffed", "cp-sat"):
                _, o, _ = sh("minizinc --solver %s %s" % (s, q(model.mzn_path)), T_GECODE)
                st, ob, _ = fz.status(o)
                note += "\n%s: %s %s" % (s, st, "" if ob is None else ob)
        d = os.path.join(self.outdir, sub, name)
        os.makedirs(d, exist_ok=True)
        shutil.copy(model.mzn_path, os.path.join(d, "m.mzn"))
        if model.flat_ok and os.path.getsize(model.fzn_path) < 20 * 2 ** 20:  # m.mzn regenerates it
            shutil.copy(model.fzn_path, os.path.join(d, "m.fzn"))
        if prefix and sub == "bad":
            for ext in (".opb", ".pbp"):
                if os.path.exists(prefix + ext):
                    shutil.copy(prefix + ext, os.path.join(d, "p" + ext))
        open(os.path.join(d, "note.txt"), "w").write(
            "%s %s\nconfig: %s\n%s\n--- gecode\n%s\n" % (verdict, self.stream, cfg or "default", note, model.g_out))

    def refusal(self, err):
        m = re.search(r"(not supported|not implemented|unsupported|[Rr]efus)[^\n]{0,120}", err)
        open(os.path.join(self.outdir, "refusals.txt"), "a").write((m.group(0)[:110] if m else err.strip()[-110:]) + "\n")


class Run:
    def __init__(self, model, rc, out, err, prefix):
        self.rc, self.raw, self.err, self.prefix = rc, out, err, prefix
        self.out = out
        if rc == 0 and out.strip():
            p = model.ozn_path
            r2, o2, e2 = sh("minizinc --ozn-file %s" % q(p), 60, stdin=out)
            self.out = o2 if r2 == 0 else out + "\n(solns2out failed: %s)" % e2[-200:]
        self.status, self.sols = parse_mzn(self.out) if rc is not None else ("TIMEOUT", [])
        self.stopped = bool(re.search(r"^limit: ", err, re.M))

    def last_obj(self):
        return objval(self.sols[-1]) if self.sols else None


def clean(prefix):
    """Remove every file of a run's proof prefix: PREFIX.opb, .pbp, and what a run killed by the
    timeout or the memory cap leaves (PREFIX.opb.rows reached 5 GB on a wide domain)."""
    for f in glob.glob(glob.escape(prefix) + ".*"):
        os.remove(f)


def bag(model, flags, env, prefix, timeout=T_SOLVE):
    clean(prefix)
    cmd = "%s %s --proof %s %s" % (q(BIN), q(model.fzn_path), q(prefix), " ".join(q(f) for f in flags))
    rc, out, err = sh(cmd, timeout, env=env)
    return Run(model, rc, out, err, prefix)


def classify_exit(run):
    """None for a normal answer; else (verdict, keep?)."""
    if run.rc is None:
        return "bag-timeout", "slow"
    if run.rc == 0:
        return None
    if run.rc == 3:
        return "refused", None
    if run.rc == 5:
        return "resource", None
    if "Out_of_memory" in run.err or "allocation failure" in run.err:
        return "MEMCAP", "bad"
    if run.rc == 4:
        return "INTERNAL", "bad"
    if run.rc == 2 and "Fatal error" not in run.err and "exception" not in run.err:
        return "refused-parse", None  # exit 2 with a positioned diagnostic (a literal past 2^62)
    return "CRASH", "bad"


def veripb(prefix):
    rc, out, err = sh("%s %s %s" % (q(VERIPB), q(prefix + ".opb"), q(prefix + ".pbp")), T_CHECK)
    txt = (out or "") + (err or "")
    if rc is None:
        return "TIMEOUT", txt
    m = re.search(r"^s VERIFIED (.*)$", txt, re.M)
    if rc != 0 or not m:
        return "REJECTED", txt
    return m.group(1).strip(), txt


def concl_ok(run, concl, d, obj_ref):
    """Does VeriPB's conclusion state what the run printed? obj_ref is Gecode's optimum or None."""
    if d is None:
        if run.status == "UNSAT":
            return concl == "UNSATISFIABLE"
        if run.status in ("SAT", "OPT"):
            return concl == "SATISFIABLE"
        return concl == "NO CONCLUSION"
    m = re.match(r"^BOUNDS (\S+) <= \S+ <= (\S+)$", concl)
    if not m:
        return False
    lo, hi = parse_inf(m.group(1)), parse_inf(m.group(2))
    if run.status == "UNSAT":
        return lo == float("inf")
    if run.status == "OPT":
        v = pbval(run.last_obj(), d)
        return lo == v and hi == v
    if run.status == "SAT":
        if hi != pbval(run.last_obj(), d):
            return False
    elif hi != float("inf"):
        return False
    return obj_ref is None or lo <= pbval(obj_ref, d)


def recheck(model, sol):
    fix = "".join("constraint %s = %s;\n" % (k, v) for k, v in sol.items() if k != "obj" and v != "[]")
    chk = re.sub(r"solve [a-z]+( obj)?;", "", model.mzn) + fix + "solve satisfy;\n"
    cpath = os.path.join(model.ctx.outdir, "chk.mzn")
    open(cpath, "w").write(chk)
    _, out_c, _ = sh("minizinc --solver gecode %s" % q(cpath), T_GECODE)
    return "=====UNSATISFIABLE=====" not in out_c


def answer_mismatch(st_ref, obj_ref, st, obj):
    """The status/objective disagreement between two DEFINITIVE runs, or None."""
    if st_ref in ("TIMEOUT", "ERROR", "UNKNOWN") or st in ("TIMEOUT", "ERROR", "UNKNOWN"):
        return None
    if not ((st_ref == st) or ({st_ref, st} <= {"SAT", "OPT"})):
        return "STATUS-MISMATCH", "reference=%s baguette=%s" % (st_ref, st)
    if st == "OPT" and st_ref == "OPT" and obj_ref != obj:
        return "OBJ-MISMATCH", "reference=%s baguette=%s" % (obj_ref, obj)
    return None


def check_run(ctx, model, run, cfg=None, all_sols=False):
    """Judge one baguette run against Gecode: (verdict, note). Keeps a disagreement."""
    ex = classify_exit(run)
    if ex is not None:
        v, where = ex
        if v == "refused":
            ctx.refusal(run.err)
        if where:
            ctx.keep(model, v, run.err[-1500:], cfg, run.prefix, sub=where)
        clean(run.prefix)
        return v, run.err[-300:]
    verdict, note = "ok", ""
    if run.status in ("ERROR",):
        verdict, note = "CRASH", run.out[-300:] + run.err[-600:]
    if verdict == "ok":
        if run.stopped and run.status in ("OPT", "UNSAT"):
            verdict, note = "LIMIT-CLAIM", "stopped by a limit but printed %s" % run.status
        elif not run.stopped and run.status == "UNKNOWN":
            verdict, note = "NO-ANSWER", "not stopped, no answer"
    if verdict == "ok":
        mm = answer_mismatch(model.st_g, model.obj_g, run.status, run.last_obj())
        if mm:
            verdict, note = mm
        elif run.stopped and run.status == "SAT" and model.dir and model.st_g == "OPT":
            if better(run.last_obj(), model.obj_g, model.dir):
                verdict, note = "OBJ-MISMATCH", "stopped run printed %s, better than Gecode's optimum %s" % (
                    run.last_obj(), model.obj_g)
        elif run.stopped and run.status == "SAT" and model.st_g == "UNSAT":
            verdict, note = "STATUS-MISMATCH", "stopped run printed a solution, Gecode says UNSAT"
    if verdict == "ok":
        if not os.path.exists(run.prefix + ".pbp"):
            verdict, note = "NO-PROOF", ""
        else:
            concl, txt = veripb(run.prefix)
            if concl == "TIMEOUT":
                verdict, note = "checker-timeout", ""
            elif concl == "REJECTED":
                verdict, note = "PROOF-REJECTED", txt[-1200:]
            elif not concl_ok(run, concl, model.dir, model.obj_g if model.st_g == "OPT" else None):
                verdict, note = "PROOF-CONCLUSION", "printed %s (obj %s), VeriPB: %s" % (
                    run.status, run.last_obj(), concl)
    if verdict == "ok" and run.sols:
        for s in (run.sols if all_sols else run.sols[-1:]):
            if not recheck(model, s):
                verdict, note = "BAD-SOLUTION", str(s)
                break
    if verdict == "checker-timeout":
        ctx.keep(model, verdict, run.err[-300:], cfg, run.prefix, sub="slow")
    elif verdict != "ok":
        ctx.keep(model, verdict, note + "\n--- baguette stdout\n" + run.out[-1500:] +
                 "\n--- stderr\n" + run.err[-1500:], cfg, run.prefix)
    clean(run.prefix)
    return verdict, note


def pre(ctx, model):
    """Gecode or flattening trouble that makes the model useless; the verdict, or None."""
    if not model.flat_ok:
        if model.st_g in ("ERROR",):
            return "mzn-error"
        if model.flat_err.strip() == "TIMEOUT":
            return "flatten-timeout"  # MiniZinc itself, 60 s (a wide domain's arithmetic)
        if "not supported" in model.flat_err or "unsupported" in model.flat_err.lower():
            ctx.refusal(model.flat_err)
            return "refused-flatten"
        ctx.keep(model, "FLATTEN-ERROR", model.flat_err)
        return "FLATTEN-ERROR"
    return None


# ---------------------------------------------------------------------------------------------
# The streams.

def s_globals(ctx, r, it):
    model = Model(ctx, GlobGen(r).model(), it)
    v = pre(ctx, model)
    if v:
        return [v]
    run = bag(model, [], {}, os.path.join(ctx.outdir, "p"))
    return [check_run(ctx, model, run)[0], "st_" + run.status]


def s_configs(ctx, r, it):
    mzn = any_model(r)
    heavy = "bool_clause" in mzn or "var -500..500: obj" in mzn
    model = Model(ctx, mzn, it, gecode_timeout=60 if heavy else T_GECODE)
    v = pre(ctx, model)
    if v:
        return [v]
    out, answers = [], []
    for name, flags, env in CONFIGS:
        run = bag(model, flags, env, os.path.join(ctx.outdir, "p"), timeout=60 if heavy else T_SOLVE)
        verdict, _ = check_run(ctx, model, run, cfg=name)
        out.append(verdict)
        if verdict == "ok":
            answers.append((name, run.status, run.last_obj()))
    # agreement between the configurations themselves (what matters when Gecode has no answer)
    for name, st, ob in answers[1:]:
        mm = answer_mismatch(answers[0][1], answers[0][2], st, ob)
        if mm:
            ctx.keep(model, "CONFIG-MISMATCH", "%s: %s=%s/%s against %s=%s/%s" % (
                mm[0], name, st, ob, answers[0][0], answers[0][1], answers[0][2]), cfg=name)
            out.append("CONFIG-MISMATCH")
    return out


def s_incr(ctx, r, it):
    model = Model(ctx, any_model(r, force_opt=True), it, gecode_timeout=60)
    v = pre(ctx, model)
    if v:
        return [v]
    p = os.path.join(ctx.outdir, "p")
    base = bag(model, [], {}, p, timeout=60)
    vb, _ = check_run(ctx, model, base, cfg="plain")
    run = bag(model, ["-i"], {}, p, timeout=60)
    objs = [objval(s) for s in run.sols]
    bad = None
    if model.dir and run.rc == 0:
        for a, b in zip(objs, objs[1:]):
            if a is None or b is None or not better(b, a, model.dir):
                bad = "objectives printed in order: %s" % objs
                break
        if bad is None and vb == "ok" and run.status != base.status:
            bad = "-i ends %s, the plain run %s" % (run.status, base.status)
        if bad is None and vb == "ok" and base.status == "OPT" and run.last_obj() != base.last_obj():
            bad = "-i ends at %s, the plain run at %s" % (run.last_obj(), base.last_obj())
    if bad:
        ctx.keep(model, "INCR-ORDER", bad + "\n--- -i stdout\n" + run.out[-1500:], cfg="i", prefix=p)
        clean(p)
        return [vb, "INCR-ORDER"]
    vi, _ = check_run(ctx, model, run, cfg="i", all_sols=True)
    return [vb, vi]


def s_limit(ctx, r, it):
    model = Model(ctx, any_model(r), it, gecode_timeout=60)
    v = pre(ctx, model)
    if v:
        return [v]
    p = os.path.join(ctx.outdir, "p")
    out = []
    k = r.choice([1, 2, 3, 5, 8, 13, 21, 50])
    cdcl = ["--cdcl"] if r.random() < 0.3 else []
    run = bag(model, cdcl, {"BAGUETTE_NODE_LIMIT": str(k)}, p, timeout=60)
    out.append(check_run(ctx, model, run, cfg="nodes%d%s" % (k, "-cdcl" if cdcl else ""), all_sols=True)[0])
    out.append("stopped" if run.stopped else "finished")
    ms = r.choice([1, 2, 5, 20])
    run = bag(model, ["-t", str(ms)], {}, p, timeout=60)
    out.append(check_run(ctx, model, run, cfg="t%dms" % ms, all_sols=True)[0])
    out.append("stopped" if run.stopped else "finished")
    return out


def s_e2e(ctx, r, it):
    model = Model(ctx, e2e_model(r), it)
    v = pre(ctx, model)
    if v:
        return [v]
    out = []
    chain = os.path.join(ROOT, "tools", "e2e", "chain.sh")
    for path, env in (("bridged", {}), ("solver", {"E2E_SOLVER": "1"})):
        d = os.path.join(ctx.outdir, "e2e")
        if os.path.isdir(d):
            shutil.rmtree(d)
        env = dict(env, BAGUETTE=BIN, E2E_TIMEOUT="60", CAKE_PB_CP=os.environ.get(
            "CAKE_PB_CP", "/cluster/arthur/baguette-results/wave55-e2e/cake_pb_cp-438b8f83"))
        rc, so, se = sh("bash %s %s %s" % (q(chain), q(model.fzn_path), q(d)), 400, env=env, cap=False)
        line = so.strip().splitlines()[-1] if so.strip() else "TIMEOUT" if rc is None else se[-300:]
        f = line.split(None, 2)
        verdict = f[1] if len(f) > 1 else "FAIL"
        detail = f[2] if len(f) > 2 else ""
        if verdict == "SKIPPED":
            out.append("skipped-" + path)
            continue
        if verdict != "VERIFIED":
            ctx.keep(model, "E2E-FAIL", path + ": " + line + "\n" + se[-800:], cfg=path)
            out.append("E2E-FAIL")
            continue
        st, ob = "SAT", None
        if detail.startswith("UNSAT"):
            st = "UNSAT"
        elif detail.startswith("OPT="):
            st, ob = "OPT", int(detail[4:].split()[0])
        mm = answer_mismatch(model.st_g, model.obj_g, st, ob)
        if mm:
            ctx.keep(model, "E2E-" + mm[0], path + ": " + line + "; " + mm[1], cfg=path)
            out.append("E2E-" + mm[0])
        else:
            out.append("verified-" + path)
    return out


def s_wide(ctx, r, it):
    model = Model(ctx, wide_model(r), it)
    v = pre(ctx, model)
    if v:
        return [v]
    p = os.path.join(ctx.outdir, "p")
    run = bag(model, ["--time-limit", "10"], {}, p)
    ex = classify_exit(run)
    verdict = "ok"
    if ex is not None:
        verdict, where = ex
        if verdict == "refused":
            ctx.refusal(run.err)
        if where:
            ctx.keep(model, verdict, run.err[-1500:], prefix=None, sub=where)
    else:
        mm = answer_mismatch(model.st_g, model.obj_g, run.status, run.last_obj())
        if run.status == "ERROR" or (run.status == "UNKNOWN" and not run.stopped):
            verdict = "CRASH"
            ctx.keep(model, verdict, run.out[-500:] + run.err[-1000:])
        elif mm:
            verdict = mm[0]
            ctx.keep(model, verdict, mm[1] + "\n" + run.out[-800:])
        elif run.sols and not recheck(model, run.sols[-1]):
            verdict = "BAD-SOLUTION"
            ctx.keep(model, verdict, str(run.sols[-1]))
    clean(p)
    return [verdict]


STREAMS = {"globals": s_globals, "configs": s_configs, "incr": s_incr, "limit": s_limit,
           "e2e": s_e2e, "wide": s_wide}


def main():
    if len(sys.argv) != 5 or sys.argv[1] not in STREAMS:
        print("usage: streams.py {%s} OUTDIR SEED N" % ",".join(STREAMS), file=sys.stderr)
        sys.exit(2)
    stream, outdir, seed, n = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    ctx = Ctx(stream, outdir, seed)
    r = random.Random("%s-%d" % (stream, seed))
    for it in range(n):
        for v in STREAMS[stream](ctx, r, it):
            ctx.count(v)
    print(stream, seed, dict(sorted(ctx.tally.items())), flush=True)


if __name__ == "__main__":
    main()
