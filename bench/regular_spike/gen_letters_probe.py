#!/usr/bin/env python3
"""M7-T28 (D-0151 section 1): checker probes for `regular`'s reasons ON THE LETTERS, written
before the OCaml. A small reference of lib/core/prop/regular.ml's filtering (fixed flags,
forward, backward, values, singletons), run on random automata under random bound decisions,
whose every pruning gets the D-0151 reason:

  - a flag that dies FORWARD: per value v of the letter's declared hull, its predecessors on
    v all dead -> RECURSE (the tail of each predecessor's own line is added), else the value
    must be outside the letter's domain -> the weakest bound literal that excludes it (or a
    hole's remover facts);
  - a flag that dies BACKWARD: per value v, the successor 0 -> nothing; the successor dead ->
    recurse; else the bound literal / the hole;
  - a letter value v: per state q with d[q,v] = t > 0, s(i,q) dead or s(i+1,t) dead, the side
    whose tail adds fewer new facts (ties: the source side), plus the letter's bound fact when
    v is a bound;
  - a flag fixed to 1: the tails of the rest of its layer; a flag killed because another one of
    its layer is 1: that one's tail; START/ACCEPT kills: no tail;
  - a decision on a flag (not exercised here) would be cited as itself.

So no tail names a flag. Each line is RUP against the .opb, the backward-chain lemmas and the
EARLIER lines, because every tail contains the tails of the lines it recurses through (kept as
the strongest fact per letter and direction). The proof is written in trail order, as
lib/core/trace.ml writes it, ending `conclusion NONE`.

Writes, per scenario k: m<k>.opb; ok<k>.pbp (every line); and the negatives
  nf<k>_<j>.pbp  the proof up to line j with the LAST fact of line j's tail dropped;
  nl<k>.pbp      every flag line removed (root lemmas and letter lines kept), cut after the
                 first letter or conflict line whose tail is non-empty.
Usage: gen_letters_probe.py <outdir> [n_scenarios] [seed]
"""
import os
import random
import sys

out = sys.argv[1]
NS = int(sys.argv[2]) if len(sys.argv) > 2 else 40
seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
os.makedirs(out, exist_ok=True)


def neg(l):
    return l[1:] if l.startswith("~") else "~" + l


def cl(ls):
    return " ".join("+1 " + l for l in ls) + " >= 1"


class Inst:
    def __init__(self, rng, nonogram=None):
        if nonogram is not None:
            blocks, n = nonogram
            self.lo, self.hi = 0, 1
            d = {}
            cur = 1
            for bi, b in enumerate(blocks):
                for k in range(b):
                    d[(cur, 1)] = cur + 1
                    if k == 0:
                        d[(cur, 0)] = cur  # the start (or a gap) loops on 0
                    cur += 1
                if bi < len(blocks) - 1:
                    d[(cur, 0)] = cur + 1  # the mandatory gap
                    cur += 1
            d[(cur, 0)] = cur  # trailing zeros
            self.Q, self.n, self.q0, self.F = cur, n, 1, {cur}
            self.d = d
        else:
            self.Q = rng.choice([3, 4, 5])
            self.lo = 0
            self.hi = rng.choice([1, 2, 3])
            self.n = rng.choice([4, 5, 6])
            self.q0 = 1
            self.F = set(rng.sample(range(1, self.Q + 1), rng.choice([1, 2])))
            self.d = {}
            for q in range(1, self.Q + 1):
                for v in range(self.lo, self.hi + 1):
                    if rng.random() < 0.75:
                        self.d[(q, v)] = rng.randint(1, self.Q)

    def delta(self, q, v):
        return self.d.get((q, v), 0)

    def s(self, i, q):
        return "s%dq%d" % (i, q)

    def x(self, i):
        return "x%d" % i

    def ge(self, i, v):
        return "x%d_ge_%d" % (i, v)

    def not_in(self, i, a, b):
        lits = []
        if a > self.lo:
            lits.append(neg(self.ge(i, a)))
        if b < self.hi:
            lits.append(self.ge(i, b + 1))
        return lits

    def opb(self, path):
        rows = []
        for i in range(self.n):
            for v in range(self.lo + 2, self.hi + 1):
                rows.append(cl([neg(self.ge(i, v)), self.ge(i, v - 1)]))
        for i in range(self.n + 1):
            rows.append(" ".join("+1 " + self.s(i, q) for q in range(1, self.Q + 1)) + " >= 1")
            rows.append(" ".join("+1 ~" + self.s(i, q) for q in range(1, self.Q + 1))
                        + " >= %d" % (self.Q - 1))
        rows.append(cl([self.s(0, self.q0)]))
        rows.append(cl([self.s(self.n, f) for f in sorted(self.F)]))
        for i in range(self.n):
            for q in range(1, self.Q + 1):
                for v in range(self.lo, self.hi + 1):
                    t = self.delta(q, v)
                    rows.append(cl([neg(self.s(i, q))] + self.not_in(i, v, v)
                                   + ([self.s(i + 1, t)] if t else [])))
        nv = self.n * (self.hi - self.lo) + (self.n + 1) * self.Q
        with open(path, "w") as f:
            f.write("* #variable= %d #constraint= %d\n" % (nv, len(rows)))
            for k, r in enumerate(rows, 1):
                f.write("@c%d %s ;\n" % (k, r))
        self.nrows = len(rows)

    def lemmas(self):
        res = []
        for i in range(self.n):
            for qp in range(1, self.Q + 1):
                for v in range(self.lo, self.hi + 1):
                    P = [q for q in range(1, self.Q + 1) if self.delta(q, v) == qp]
                    res.append("rup " + cl([neg(self.s(i + 1, qp))] + self.not_in(i, v, v)
                                           + [self.s(i, q) for q in P]) + " ;")
        return res


class Conflict(Exception):
    pass


class Solver:
    """Letters and flags as sets of values. A fact is ((name, dir), value), dir '>=' or '<=';
    an accumulator is a dict keeping the STRONGEST value per (name, dir), in insertion order."""

    def __init__(self, I):
        self.I = I
        self.dom = {}
        for i in range(I.n):
            self.dom[I.x(i)] = set(range(I.lo, I.hi + 1))
        for i in range(I.n + 1):
            for q in range(1, I.Q + 1):
                self.dom[I.s(i, q)] = {0, 1}
        self.trail = []  # (name, kind, claim_lits, facts, who)
        self.killer = {}
        self.setter = {}
        self.remover = {}

    def lit_of(self, f):
        (name, dr), v = f
        if name.startswith("s"):
            return ("~" + name) if dr == "<=" else name
        if dr == ">=":
            return self.I.ge(int(name[1:]), v) if v > self.I.lo else None
        return neg(self.I.ge(int(name[1:]), v + 1)) if v < self.I.hi else None

    def D(self, flag):
        return self.killer[flag]

    def S(self, flag):
        return self.setter[flag]

    @staticmethod
    def union(acc, facts):
        for (key, v) in facts:
            if key in acc:
                old = acc[key]
                acc[key] = max(old, v) if key[1] == ">=" else min(old, v)
            else:
                acc[key] = v

    @staticmethod
    def new_count(acc, facts):
        c = 0
        for (key, v) in facts:
            if key not in acc:
                c += 1
            elif key[1] == ">=" and v > acc[key]:
                c += 1
            elif key[1] == "<=" and v < acc[key]:
                c += 1
        return c

    def dead(self, i, q):
        return self.dom[self.I.s(i, q)] == {0}

    def isset(self, i, q):
        return self.dom[self.I.s(i, q)] == {1}

    def kill(self, i, q, acc):
        nm = self.I.s(i, q)
        if self.isset(i, q):
            a = dict(acc)
            self.union(a, self.S(nm))
            raise Conflict(list(a.items()))
        facts = list(acc.items())
        self.dom[nm] = {0}
        self.killer[nm] = facts
        self.trail.append((nm, "kill", ["~" + nm], facts, "reg"))

    def setf(self, i, q, acc):
        nm = self.I.s(i, q)
        facts = list(acc.items())
        self.dom[nm] = {1}
        self.setter[nm] = facts
        self.trail.append((nm, "set", [nm], facts, "reg"))

    def remove(self, i, v, acc):
        I = self.I
        nm = I.x(i)
        d = self.dom[nm]
        if d == {v}:
            raise Conflict(list(acc.items()))
        lo, hi = min(d), max(d)
        d.discard(v)
        a = dict(acc)
        if v == lo:
            u = min(d)
            claim = [I.ge(i, u)]
            for w in range(v + 1, u):  # the settle walked over holes: Trace cites them
                self.union(a, self.remover[(nm, w)])
        elif v == hi:
            u = max(d)
            claim = [neg(I.ge(i, u + 1))]
            for w in range(u + 1, v):
                self.union(a, self.remover[(nm, w)])
        else:
            claim = [neg(I.ge(i, v)), I.ge(i, v + 1)]
        self.remover[(nm, v)] = list(acc.items())
        self.trail.append((nm, "rm%d" % v, claim, list(a.items()), "reg"))

    def decide(self, i, dr, v):
        nm = self.I.x(i)
        d = self.dom[nm]
        keep = {w for w in d if (w >= v if dr == ">=" else w <= v)}
        for w in d - keep:
            self.remover[(nm, w)] = [((nm, dr), v)]
        self.dom[nm] = keep
        self.trail.append((nm, "dec", [], [], "dec"))

    def out_of_dom(self, acc, i, vs):
        """Values vs of letter i, none in its domain: the weakest bound literals, the holes."""
        nm = self.I.x(i)
        d = self.dom[nm]
        lo, hi = min(d), max(d)
        below = [v for v in vs if v < lo]
        above = [v for v in vs if v > hi]
        inside = [v for v in vs if lo < v < hi]
        if below:
            self.union(acc, [((nm, ">="), max(below) + 1)])
        if above:
            self.union(acc, [((nm, "<="), min(above) - 1)])
        for v in inside:
            assert v not in d
            self.union(acc, self.remover[(nm, v)])

    def forward_reason(self, i, qp):
        I = self.I
        acc = {}
        need = []
        for v in range(I.lo, I.hi + 1):
            P = [q for q in range(1, I.Q + 1) if I.delta(q, v) == qp]
            if all(self.dead(i, q) for q in P):
                for q in P:
                    self.union(acc, self.D(I.s(i, q)))
            else:
                assert v not in self.dom[I.x(i)]
                need.append(v)
        self.out_of_dom(acc, i, need)
        return acc

    def backward_reason(self, i, q):
        I = self.I
        acc = {}
        need = []
        for v in range(I.lo, I.hi + 1):
            t = I.delta(q, v)
            if t == 0:
                continue
            if self.dead(i + 1, t):
                self.union(acc, self.D(I.s(i + 1, t)))
            else:
                assert v not in self.dom[I.x(i)]
                need.append(v)
        self.out_of_dom(acc, i, need)
        return acc

    def layer_conflict(self, i):
        I = self.I
        if all(self.dead(i, q) for q in range(1, I.Q + 1)):
            acc = {}
            for q in range(1, I.Q + 1):
                self.union(acc, self.D(I.s(i, q)))
            raise Conflict(list(acc.items()))

    def propagate(self):
        I = self.I
        while True:
            before = len(self.trail)
            for i in range(I.n + 1):
                setq = [q for q in range(1, I.Q + 1) if self.isset(i, q)]
                if len(setq) > 1:
                    acc = {}
                    self.union(acc, self.S(I.s(i, setq[0])))
                    self.union(acc, self.S(I.s(i, setq[1])))
                    raise Conflict(list(acc.items()))
                if setq:
                    for r in range(1, I.Q + 1):
                        if r != setq[0] and not self.dead(i, r):
                            acc = {}
                            self.union(acc, self.S(I.s(i, setq[0])))
                            self.kill(i, r, acc)
            for q in range(1, I.Q + 1):
                if q != I.q0 and not self.dead(0, q):
                    self.kill(0, q, {})
            for q in range(1, I.Q + 1):
                if q not in I.F and not self.dead(I.n, q):
                    self.kill(I.n, q, {})
            self.layer_conflict(0)
            for i in range(I.n):  # forward
                dom = self.dom[I.x(i)]
                reach = set()
                for q in range(1, I.Q + 1):
                    if not self.dead(i, q):
                        for v in dom:
                            t = I.delta(q, v)
                            if t:
                                reach.add(t)
                for qp in range(1, I.Q + 1):
                    if qp not in reach and not self.dead(i + 1, qp):
                        self.kill(i + 1, qp, self.forward_reason(i, qp))
                self.layer_conflict(i + 1)
            for i in range(I.n - 1, -1, -1):  # backward
                dom = self.dom[I.x(i)]
                for q in range(1, I.Q + 1):
                    if not self.dead(i, q):
                        live = any(I.delta(q, v) and not self.dead(i + 1, I.delta(q, v))
                                   for v in dom)
                        if not live:
                            self.kill(i, q, self.backward_reason(i, q))
                self.layer_conflict(i)
            for i in range(I.n):  # values
                nm = I.x(i)
                for v in sorted(self.dom[nm]):
                    sup = any(not self.dead(i, q) and I.delta(q, v)
                              and not self.dead(i + 1, I.delta(q, v))
                              for q in range(1, I.Q + 1))
                    if sup:
                        continue
                    acc = {}
                    for q in range(1, I.Q + 1):
                        t = I.delta(q, v)
                        if not t:
                            continue
                        src = self.D(I.s(i, q)) if self.dead(i, q) else None
                        dst = self.D(I.s(i + 1, t)) if self.dead(i + 1, t) else None
                        if src is not None and (dst is None or self.new_count(acc, src)
                                                <= self.new_count(acc, dst)):
                            self.union(acc, src)
                        else:
                            self.union(acc, dst)
                    d = self.dom[nm]
                    if v == min(d):
                        self.union(acc, [((nm, ">="), v)])
                    if v == max(d):
                        self.union(acc, [((nm, "<="), v)])
                    self.remove(i, v, acc)
            for i in range(I.n + 1):  # singletons
                live = [q for q in range(1, I.Q + 1) if not self.dead(i, q)]
                if len(live) == 1 and not self.isset(i, live[0]):
                    acc = {}
                    for r in range(1, I.Q + 1):
                        if r != live[0]:
                            self.union(acc, self.D(I.s(i, r)))
                    self.setf(i, live[0], acc)
            if len(self.trail) == before:
                return

    def line(self, claim, facts):
        lits = list(claim) + [neg(l) for l in (self.lit_of(f) for f in facts) if l is not None]
        return "rup " + cl(lits) + " ;" if lits else "rup >= 1 ;"


def scenario(k, I, rng):
    I.opb(os.path.join(out, "m%d.opb" % k))
    S = Solver(I)
    conflict = None
    try:
        S.propagate()
        for _ in range(12):
            free = [i for i in range(I.n) if len(S.dom[I.x(i)]) > 1]
            if not free:
                break
            # one or two bound decisions before the propagator runs again: two at once is
            # another constraint pruning two letters in one fixpoint, which is what makes a
            # domain-consistent propagator meet a conflict below the root
            for _ in range(rng.choice([1, 2])):
                free = [i for i in range(I.n) if len(S.dom[I.x(i)]) > 1]
                if not free:
                    break
                i = rng.choice(free)
                d = sorted(S.dom[I.x(i)])
                v = rng.choice(d[1:])
                if rng.random() < 0.5:
                    S.decide(i, ">=", v)
                else:
                    S.decide(i, "<=", v - 1)
            S.propagate()
    except Conflict as c:
        conflict = c.args[0]
    lines = []  # (text, kind, facts)
    for (nm, kind, claim, facts, who) in S.trail:
        if who != "dec":
            lines.append((S.line(claim, facts), kind, facts))
    if conflict is not None:
        lines.append((S.line([], conflict), "conflict", conflict))
    head = ["pseudo-Boolean proof version 3.0", "f %d ;" % I.nrows] + I.lemmas()
    tail = ["output NONE ;", "conclusion NONE ;", "end pseudo-Boolean proof ;"]

    def write(name, body):
        with open(os.path.join(out, name), "w") as f:
            f.write("\n".join(head + body + tail) + "\n")

    write("ok%d.pbp" % k, [l[0] for l in lines])
    nneg = 0
    for j, (txt, kind, facts) in enumerate(lines):
        lits = [S.lit_of(f) for f in facts if S.lit_of(f) is not None]
        if not lits:
            continue
        toks = txt[len("rup "):txt.index(">=")].split()[:-2]  # the last fact's literal dropped
        body = ("rup " + " ".join(toks) + " >= 1 ;") if toks else "rup >= 1 ;"
        write("nf%d_%d.pbp" % (k, j), [l[0] for l in lines[:j]] + [body])
        nneg += 1
    kept, cut = [], False
    for (txt, kind, facts) in lines:
        if kind in ("kill", "set"):
            continue
        kept.append(txt)
        if any(S.lit_of(f) is not None for f in facts):
            cut = True
            break
    if cut:
        write("nl%d.pbp" % k, kept)
    tails = [len([f for f in l[2] if S.lit_of(f) is not None]) for l in lines]
    return len(lines), nneg, cut, conflict is not None, max(tails or [0])


rng = random.Random(seed)
insts = [Inst(rng, nonogram=([2, 1], 6)), Inst(rng, nonogram=([1, 2], 7)),
         Inst(rng, nonogram=([3], 6))]
while len(insts) < NS:
    insts.append(Inst(rng))
with open(os.path.join(out, "summary.tsv"), "w") as f:
    for k, I in enumerate(insts):
        nl, nneg, has_nl, confl, mt = scenario(k, I, rng)
        f.write("%d\tQ=%d\tn=%d\tw=%d\tlines=%d\tneg=%d\tnl=%s\tconflict=%s\tmaxtail=%d\n"
                % (k, I.Q, I.n, I.hi - I.lo + 1, nl, nneg, has_nl, confl, mt))
