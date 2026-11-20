#!/usr/bin/env python3
r"""M4-T6 spike (D-0184): in-proof tabulation of int_times(x, y, z) over baguette's ORDER
encoding, and a GAC search whose every pruning is one `rup` against the table.

NOT part of the solver. It reads the .opb baguette wrote for a model (so the .opb is
byte-for-byte the solver's: no OPB change) and writes a VeriPB 3.0 .pbp of its own:

  1. TABULATION, at the root, from the declared domains of x and y:
       per pair (a, b) with c = a*b inside z's declared box, a fresh selector s_ab and
         red  k ~s +l1 .. +lk >= k : s -> 0 ;      (DEF1)  s -> each literal of x=a, y=b, z=c
         red  s +~l1 .. +~lk >= 1  : s -> 1 ;      (DEF2)  all literals -> s
       where x=a is the pair x_ge_a /\ ~x_ge_(a+1), constants dropped (k <= 6);
         rup  [x<>a] [y<>b] z_ge_c               (ZLO)  from D-0060's guarded rows
         rup  [x<>a] [y<>b] ~z_ge_(c+1)          (ZHI)
         rup  [x<>a] [y<>b] s_ab                 (CAB)
       per pair with c outside z's box: rup [x<>a] [y<>b]   (DEAD)
       per a:  rup  sum_b s_ab + [x<>a] >= 1                 (PERA)
       once:   rup  sum s >= 1                               (ALO)
       then the ZLO/ZHI/CAB/DEAD/PERA lemmas are deleted: what stays is DEF1, DEF2, ALO.
  2. SEARCH: GAC on the table plus the model's unary side constraints, DFS on x=v / x<>v.
     Every removal is one line
         rup  [w<>u] ~F >= 1
     F the facts that kill each tuple supporting w=u: a bound literal of another variable,
     or, for a tuple killed by an interior HOLE, the hole line's own facts, cited through a
     KILL line  rup ~s_t ~F_hole >= 1  written first. A failed node writes the nogood over
     its left decisions; the root failure writes `rup >= 1` and concludes UNSAT; a solution
     writes `sol` over the model's literals and concludes SAT.

Mutations (run_spike.sh asserts what the checker says about each):
  wrong-def        the selector of the first tuple that is part of a SOLUTION is defined with
                   z = c+1 (both reds still pass: a fresh definition is always sound); its
                   CAB must be refused
  flip-witness     that tuple's DEF2 gets the witness s -> 0; refused
  unsupported      after the root fixpoint, claim the removal of a SUPPORTED value; refused
  alo-direct       ALO straight after the definitions, without the lemmas: a MEASUREMENT
                   (ALO is not RUP from D-0060's rows alone), refused
  cab-no-zlemma    every CAB without its ZLO/ZHI lemmas: a measurement, refused
  no-kill          the KILL lines omitted: a measurement; refused where a removed value
                   has two or more hole-killed supports the model rows cannot split on
                   (tab_times_holes_sat: z = 2, supports (1,2) and (2,1))
"""

import argparse
import itertools
import re
import sys


def fmt(v):
    return f"m{-v}" if v < 0 else str(v)


class Model:
    def __init__(self, path):
        self.decl = {}  # name -> (lo, hi)
        self.order = []
        self.times = None
        self.unary = []  # (op, var, const)
        txt = open(path).read()
        for m in re.finditer(r"^var\s+(-?\d+)\.\.(-?\d+)\s*:\s*(\w+)", txt, re.M):
            lo, hi, name = int(m.group(1)), int(m.group(2)), m.group(3)
            self.decl[name] = (lo, hi)
            self.order.append(name)
        for m in re.finditer(r"^constraint\s+(\w+)\(([^)]*)\)", txt, re.M):
            op, args = m.group(1), [a.strip() for a in m.group(2).split(",")]
            if op == "int_times":
                assert self.times is None, "one int_times per spike model"
                self.times = tuple(args)
            elif op in ("int_le", "int_ne", "int_eq"):
                if op == "int_le" and re.fullmatch(r"-?\d+", args[0]):
                    self.unary.append(("ge", args[1], int(args[0])))
                else:
                    self.unary.append((op[4:], args[0], int(args[1])))
            else:
                raise SystemExit(f"unsupported constraint {op}")
        assert self.times, "no int_times"


class Proof:
    def __init__(self, n_opb):
        self.lines = ["pseudo-Boolean proof version 3.0", f"f {n_opb} ;"]
        self.n = 0
        self.counts = {}
        self.kinds = []  # (label, kind), written beside the proof for no_table.py

    def label(self):
        self.n += 1
        return f"@t{self.n}"

    def emit(self, kind, body):
        lab = self.label()
        self.lines.append(f"{lab} {body}")
        self.counts[kind] = self.counts.get(kind, 0) + 1
        self.kinds.append((lab, kind))
        return lab

    def raw(self, s):
        self.lines.append(s)


def pb(terms, degree):
    """terms: list of (coeff, (name, positive))."""
    s = " ".join(f"+{c} {'' if pos else '~'}{n}" for c, (n, pos) in terms)
    return f"{s} >= {degree} ;"


def neg(l):
    return (l[0], not l[1])


class Spike:
    def __init__(self, model, n_opb, mutate):
        self.m = model
        self.p = Proof(n_opb)
        self.mutate = mutate
        self.x, self.y, self.z = model.times
        self.kills = {}  # (tuple, facts) -> label
        self.nodes = 0
        self.depth = 0
        self.root = None  # w -> (lo, hi) once the root fixpoint is reached

    # ---- literals over the ORDER encoding ------------------------------------------
    def ge(self, w, v):
        """[w >= v] as a literal, or True/False when it is a constant."""
        lo, hi = self.m.decl[w]
        if v <= lo:
            return True
        if v > hi:
            return False
        return (f"{w}_ge_{fmt(v)}", True)

    def eq_lits(self, w, v):
        """the literals whose conjunction is w = v (constants dropped)."""
        out = []
        a, b = self.ge(w, v), self.ge(w, v + 1)
        if a is not True:
            out.append(a)
        if b is not False:
            out.append(neg(b))
        return out

    def ne_clause(self, w, v):
        return [neg(l) for l in self.eq_lits(w, v)]

    def sel(self, a, b):
        return (f"tab_s_{fmt(a)}_{fmt(b)}", True)

    # ---- 1. tabulation --------------------------------------------------------------
    def tabulate(self):
        p, (xl, xh), (yl, yh), (zl, zh) = (
            self.p,
            self.m.decl[self.x],
            self.m.decl[self.y],
            self.m.decl[self.z],
        )
        self.tuples = []
        lemmas = []
        # The mutations corrupt a tuple that is part of a SOLUTION of the model. Corrupting
        # one the model refutes anyway is vacuous: its CAB (or its red's proof goal) closes
        # by refuting the tuple, not by reading the definition -- measured, the first draft
        # of this spike corrupted (0,-3,0) under z <= -5 and the checker accepted both.
        target = None
        for a in range(xl, xh + 1):
            for b in range(yl, yh + 1):
                c = a * b
                if zl <= c <= zh and target is None and self.feasible({self.x: a, self.y: b, self.z: c}):
                    target = (a, b)
        self.target = target
        for a in range(xl, xh + 1):
            for b in range(yl, yh + 1):
                c = a * b
                if zl <= c <= zh:
                    self.tuples.append((a, b, c))
                    first = (a, b) == target
                    cz = (c + 1 if c + 1 <= zh else c - 1) if (self.mutate == "wrong-def" and first) else c
                    lits = self.eq_lits(self.x, a) + self.eq_lits(self.y, b) + self.eq_lits(self.z, cz)
                    s = self.sel(a, b)
                    k = len(lits)
                    p.emit("red", f"red {pb([(k, neg(s))] + [(1, l) for l in lits], k)[:-2]} : {s[0]} -> 0 ;")
                    w2 = "0" if (self.mutate == "flip-witness" and first) else "1"
                    p.emit("red", f"red {pb([(1, s)] + [(1, neg(l)) for l in lits], 1)[:-2]} : {s[0]} -> {w2} ;")
        if self.mutate == "alo-direct":
            self.alo = p.emit("rup", f"rup {pb([(1, self.sel(a, b)) for a, b, _ in self.tuples], 1)}")
            return
        for a in range(xl, xh + 1):
            for b in range(yl, yh + 1):
                c = a * b
                pre = self.ne_clause(self.x, a) + self.ne_clause(self.y, b)
                if not (zl <= c <= zh):
                    lemmas.append(p.emit("rup", f"rup {pb([(1, l) for l in pre], 1)}"))
                    continue
                if self.mutate != "cab-no-zlemma":
                    lo_l, hi_l = self.ge(self.z, c), self.ge(self.z, c + 1)
                    if lo_l is not True:
                        lemmas.append(p.emit("rup", f"rup {pb([(1, l) for l in pre + [lo_l]], 1)}"))
                    if hi_l is not False:
                        lemmas.append(p.emit("rup", f"rup {pb([(1, l) for l in pre + [neg(hi_l)]], 1)}"))
                lemmas.append(p.emit("rup", f"rup {pb([(1, l) for l in pre + [self.sel(a, b)]], 1)}"))
            row = [(1, self.sel(a, b)) for (aa, b, _) in self.tuples if aa == a]
            row += [(1, l) for l in self.ne_clause(self.x, a)]
            lemmas.append(p.emit("rup", f"rup {pb(row, 1)}"))
        self.alo = p.emit("rup", f"rup {pb([(1, self.sel(a, b)) for a, b, _ in self.tuples], 1)}")
        p.raw("del id " + " ".join(lemmas) + " ;")

    def feasible(self, val):
        for op, w, k in self.m.unary:
            u = val[w]
            if (op == "le" and u > k) or (op == "ge" and u < k) or (op == "ne" and u == k) or (op == "eq" and u != k):
                return False
        return True

    # ---- 2. GAC search ----------------------------------------------------------------
    def fact_for_tuple(self, t, dom, removed, skip):
        """why tuple t is dead: ('lit', l) for a bound, ('hole', facts) for a hole."""
        names = (self.x, self.y, self.z)
        best = None
        for w, u in zip(names, t):
            if w == skip or u in dom[w]:
                continue
            lo, hi = min(dom[w]) if dom[w] else None, max(dom[w]) if dom[w] else None
            if lo is not None and u < lo:
                return ("lit", self.ge(w, lo))
            if hi is not None and u > hi:
                return ("lit", neg(self.ge(w, hi + 1)))
            if best is None:
                best = ("hole", removed[(w, u)])
        return best

    def root_implied(self, l):
        """a bound literal the root already established: a level-0 fact, cited by nothing."""
        if self.depth == 0:
            return True
        if self.root is None:
            return False
        name, pos = l
        w, v = name.rsplit("_ge_", 1)
        v = -int(v[1:]) if v.startswith("m") else int(v)
        lo, hi = self.root[w]
        return (pos and v <= lo) or (not pos and v > hi)

    def remove(self, w, u, dom, removed):
        """one removal line; returns its facts."""
        names = (self.x, self.y, self.z)
        i = names.index(w)
        facts = set()
        for t in self.tuples:
            if t[i] != u:
                continue
            kind, f = self.fact_for_tuple(t, dom, removed, w)
            if kind == "lit":
                if f is not True and not self.root_implied(f):
                    facts.add(f)
            else:
                facts |= f
                key = (t, frozenset(f))
                if key not in self.kills and self.mutate != "no-kill":
                    s = self.sel(t[0], t[1])
                    self.kills[key] = self.p.emit(
                        "kill", f"rup {pb([(1, neg(s))] + [(1, neg(l)) for l in sorted(f)], 1)}"
                    )
        clause = self.ne_clause(w, u) + [neg(l) for l in sorted(facts)]
        self.p.emit("prune", f"rup {pb([(1, l) for l in clause], 1)}")
        dom[w].discard(u)
        removed[(w, u)] = frozenset(facts)
        return facts

    def gac(self, dom, removed):
        names = (self.x, self.y, self.z)
        changed = True
        while changed:
            changed = False
            live = [t for t in self.tuples if all(v in dom[w] for w, v in zip(names, t))]
            for i, w in enumerate(names):
                sup = {t[i] for t in live}
                for u in sorted(dom[w]):
                    if u not in sup:
                        self.remove(w, u, dom, removed)
                        changed = True
                if not dom[w]:
                    return False
            for w in self.m.decl:
                if w not in names and not dom[w]:
                    return False
        return True

    def root_unary(self, dom, removed):
        """the unary side constraints: one line per removal, from the .opb row alone."""
        for op, w, k in self.m.unary:
            lo, hi = self.m.decl[w]
            claims = []
            if op in ("le", "eq") and k < hi:
                claims.append([neg(self.ge(w, k + 1))])
            if op in ("ge", "eq") and k > lo:
                claims.append([self.ge(w, k)])
            if op == "ne":
                claims.append(self.ne_clause(w, k))
            for cl in claims:
                self.p.emit("unary", f"rup {pb([(1, l) for l in cl], 1)}")
            for u in sorted(dom[w]):
                bad = (op == "le" and u > k) or (op == "ge" and u < k) or (op == "ne" and u == k) or (
                    op == "eq" and u != k
                )
                if bad:
                    dom[w].discard(u)
                    removed[(w, u)] = frozenset()

    def dlits(self, d):
        w, v = d
        return self.eq_lits(w, v)

    def search(self, dom, removed, decisions):
        """returns a solution dict or None. On None the nogood over `decisions` is written."""
        self.nodes += 1
        self.depth = len(decisions)
        ok = self.gac(dom, removed)
        if ok and not decisions and self.root is None:
            self.root = {w: (min(d), max(d)) for w, d in dom.items()}
        if ok and self.mutate == "unsupported" and not decisions:
            self.mutate = None
            names = (self.x, self.y, self.z)
            for w in names:
                if len(dom[w]) > 1:
                    u = max(dom[w])
                    self.p.emit("prune", f"rup {pb([(1, l) for l in self.ne_clause(w, u)], 1)}")
                    break
        if not ok:
            lits = [l for d in decisions for l in self.dlits(d)]
            lab = self.p.emit("nogood", f"rup {pb([(1, neg(l)) for l in lits], 1)}")
            return None, lab
        free = [w for w in self.m.order if len(dom[w]) > 1]
        if not free:
            return {w: min(dom[w]) for w in self.m.order}, None
        w = min(free, key=lambda v: (len(dom[v]), self.m.order.index(v)))
        v = min(dom[w])
        d2, r2 = {k: set(s) for k, s in dom.items()}, dict(removed)
        for u in list(d2[w]):
            if u != v:
                d2[w].discard(u)
                r2[(w, u)] = frozenset(self.dlits((w, v)))
        sol, _ = self.search(d2, r2, decisions + [(w, v)])
        if sol:
            return sol, None
        # right branch: w <> v, its facts being the earlier decisions'
        prev = frozenset(l for d in decisions for l in self.dlits(d))
        dom[w].discard(v)
        removed[(w, v)] = prev
        if not dom[w]:
            lab = self.p.emit("nogood", f"rup {pb([(1, neg(l)) for l in sorted(prev)], 1)}")
            return None, lab
        return self.search(dom, removed, decisions)

    def run(self):
        self.tabulate()
        dom = {w: set(range(lo, hi + 1)) for w, (lo, hi) in self.m.decl.items()}
        removed = {}
        self.root_unary(dom, removed)
        sol, lab = self.search(dom, removed, [])
        p = self.p
        if sol:
            lits = []
            for w in self.m.order:
                lo, hi = self.m.decl[w]
                for v in range(lo + 1, hi + 1):
                    lits.append(("" if sol[w] >= v else "~") + f"{w}_ge_{fmt(v)}")
            p.raw("sol " + " ".join(lits) + " ;")
            p.raw("output NONE ;")
            p.raw("conclusion SAT ;")
        else:
            p.raw("output NONE ;")
            p.raw(f"conclusion UNSAT : {lab} ;")
        p.raw("end pseudo-Boolean proof ;")
        return sol


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("fzn")
    ap.add_argument("opb")
    ap.add_argument("out")
    ap.add_argument("--mutate", default=None)
    a = ap.parse_args()
    n = None
    for line in open(a.opb):
        m = re.search(r"#constraint=\s*(\d+)", line)
        if m:
            n = int(m.group(1))
            break
    sp = Spike(Model(a.fzn), n, a.mutate)
    sol = sp.run()
    open(a.out, "w").write("\n".join(sp.p.lines) + "\n")
    open(a.out + ".kinds", "w").write("".join(f"{l} {k}\n" for l, k in sp.p.kinds))
    c = sp.p.counts
    print(
        f"tuples={len(sp.tuples)} nodes={sp.nodes} answer={'SAT' if sol else 'UNSAT'} "
        + " ".join(f"{k}={v}" for k, v in sorted(c.items()))
        + f" lines={len(sp.p.lines)}"
    )


if __name__ == "__main__":
    main()
