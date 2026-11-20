#!/usr/bin/env python3
"""Every solution of a .scp, under the semantics of CakeML's cpScript.sml (M14-e2e-verification-T2).

Usage: python3 -I scpsem.py MODEL.scp NAMES [MAX_NODES]

The translator (fzn2scp.py) is the one trusted link of the chain that no theorem covers
(D-0174 section 5), and a wrong translation verifies. This is half of its test: it reads
ONLY the .scp (not the FlatZinc, not the translator's code) and enumerates the assignments
cake's semantics admit, by backtracking with interval pruning. The other half is Gecode's
FlatZinc interpreter on the .fzn, which `scripts/e2e_lane.sh` runs and compares with this.

The semantics, transcribed from cpScript.sml (CakeML master, 2026-11):
  valid_assignment   every variable within its (name lb ub)
  lin_<cmp> (c1 X1 ...) Y      cmpop_val cmp (sum ci * Xi) Y      (lin_sem, Zr = NONE)
  <cmp> X Y                    cmpop_val cmp X Y                  (cmpop_sem, Zr = NONE)
     cmp: equals =, not_equals !=, less_equal <=, less_than <, greater_equal >=, greater_than >
  all_different (X1 ...)       ALL_DISTINCT (MAP (varc w) Xs)     (AllDifferentExcept Xs [])
  in (X1 ...) Y                MEM (varc w Y) (MAP (varc w) Xs)   (in_sem)
  and the T4 forms (D-0178), a reify tuple (Z op v) meaning `varc Z op v`, op in = != >= > <= <:
  <cmp>_iff R X Y              R <=> cmpop_val cmp X Y            (cmpop_sem, Zr = INR R)
  lin_<cmp>_iff R (c1 X1 ...) Y   R <=> cmpop_val cmp (sum ...) Y  (lin_sem, Zr = INR R)
  or (R1 ...) R                R <=> EXISTS Ri                    (or_sem)
  and (R1 ...) R               R <=> EVERY Ri                     (and_sem)
Any other keyword, a one-sided `_if` form or a prob_type other than `decide` is refused (exit 2).

Prints `count N` then one line per solution, `name=value ...` over the FlatZinc names of
NAMES, sorted; or `toobig` when MAX_NODES (default 2,000,000) is exceeded.
"""
import operator
import re
import sys

CMP = {"equals": operator.eq, "not_equals": operator.ne, "less_equal": operator.le,
       "less_than": operator.lt, "greater_equal": operator.ge, "greater_than": operator.gt}
SYM = {"=": operator.eq, "!=": operator.ne, "<=": operator.le, "<": operator.lt,
       ">=": operator.ge, ">": operator.gt}


def sexp(text):
    toks = re.findall(r"\(|\)|[^\s()]+", text)
    stack = [[]]
    for t in toks:
        if t == "(":
            stack.append([])
        elif t == ")":
            e = stack.pop()
            stack[-1].append(e)
        else:
            stack[-1].append(t)
    if len(stack) != 1 or len(stack[0]) != 1:
        raise SystemExit("scpsem: unbalanced s-expression")
    return stack[0][0]


def isint(a):
    return re.fullmatch(r"-?\d+", a) is not None


class Refused(Exception):
    pass


def load(path):
    top = sexp(open(path).read())
    sec = {s[0]: s[1:] for s in top}
    if sec.get("version") != ["1"]:
        raise Refused("version")
    if sec.get("prob_type") != ["decide"]:
        raise Refused(f"prob_type {sec.get('prob_type')}")
    bounds = {v: (int(lo), int(hi)) for v, lo, hi in sec["variables"]}
    cons = []
    for c in sec["constraints"]:
        name, kw, args = c[0], c[1], c[2:]
        term = (lambda a: ("c", int(a)) if isint(a) else ("v", a))

        def reify(r):
            if not (isinstance(r, list) and len(r) == 3 and r[1] in SYM and isint(r[2])):
                raise Refused(f"{name}: reify tuple {r}")
            return (term(r[0]), SYM[r[1]], int(r[2]))
        reif = None
        if kw.endswith("_iff"):
            kw = kw[:-4]
            reif, args = reify(args[0]), args[1:]
        if kw.startswith("lin_") and kw[4:] in CMP:
            (lst, y) = args
            if len(lst) % 2:
                raise Refused(f"{name}: odd linear term")
            pairs = [(int(lst[i]), term(lst[i + 1])) for i in range(0, len(lst), 2)]
            cons.append(("lin", CMP[kw[4:]], pairs, term(y), reif))
        elif kw in CMP:
            x, y = args
            cons.append(("lin", CMP[kw], [(1, term(x))], term(y), reif))
        elif kw in ("or", "and") and reif is None:
            lst, y = args
            cons.append(("log", any if kw == "or" else all, [reify(r) for r in lst], reify(y)))
        elif kw == "all_different":
            (lst,) = args
            cons.append(("alldiff", [term(a) for a in lst]))
        elif kw == "in":
            lst, y = args
            cons.append(("in", [term(a) for a in lst], term(y)))
        else:
            raise Refused(f"keyword {kw}")
    for c in cons:
        for t in terms_of(c):
            if t[0] == "v" and t[1] not in bounds:
                raise Refused(f"undeclared variable {t[1]}")
    return bounds, cons


def terms_of(c):
    if c[0] == "lin":
        return [t for _, t in c[2]] + [c[3]] + ([c[4][0]] if c[4] else [])
    if c[0] == "log":
        return [r[0] for r in c[2]] + [c[3][0]]
    if c[0] == "alldiff":
        return c[1]
    return c[1] + [c[2]]


def solve(bounds, cons, max_nodes):
    order = list(bounds)
    pos = {v: i for i, v in enumerate(order)}
    # a constraint is checked at the depth where its last variable is assigned, and its
    # linear interval is checked at every depth from its first
    w = {}
    sols = []
    nodes = [0]

    def val(t):
        return t[1] if t[0] == "c" else w.get(t[1])

    def holds(r):
        """A reify tuple's truth value, or None while its variable is unassigned."""
        v = val(r[0])
        return None if v is None else r[1](v, r[2])

    def feasible(c):
        if c[0] == "log":
            vals = [holds(r) for r in c[2]]
            y = holds(c[3])
            if y is None or any(v is None for v in vals):
                return True
            return y == c[1](vals)
        if c[0] == "lin" and c[4] is not None:
            # reified: checked once everything is assigned (the enumeration is exhaustive)
            vals = [val(t) for t in terms_of(c)]
            if any(v is None for v in vals):
                return True
            total = sum(a * val(t) for a, t in c[2])
            return holds(c[4]) == c[1](total, val(c[3]))
        if c[0] == "lin":
            op, pairs, y = c[1], c[2], c[3]
            lo = hi = 0
            for a, t in pairs:
                v = val(t)
                if v is None:
                    blo, bhi = bounds[t[1]]
                    lo += min(a * blo, a * bhi)
                    hi += max(a * blo, a * bhi)
                else:
                    lo += a * v
                    hi += a * v
            yv = val(y)
            if yv is None:
                ylo, yhi = bounds[y[1]]
            else:
                ylo = yhi = yv
            if lo == hi and ylo == yhi:
                return op(lo, ylo)
            if op is operator.le:
                return lo <= yhi
            if op is operator.lt:
                return lo < yhi
            if op is operator.ge:
                return hi >= ylo
            if op is operator.gt:
                return hi > ylo
            if op is operator.eq:
                return lo <= yhi and ylo <= hi
            return True
        vals = [val(t) for t in terms_of(c)]
        if c[0] == "alldiff":
            got = [v for v in vals if v is not None]
            return len(got) == len(set(got))
        if any(v is None for v in vals):
            return True
        return vals[-1] in vals[:-1]

    watch = {v: [] for v in order}
    for c in cons:
        vs = {t[1] for t in terms_of(c) if t[0] == "v"}
        for v in vs:
            watch[v].append(c)
    ground = [c for c in cons if not any(t[0] == "v" for t in terms_of(c))]
    if not all(feasible(c) for c in ground):
        return [], False

    def rec(i):
        if i == len(order):
            sols.append(dict(w))
            return True
        x = order[i]
        lo, hi = bounds[x]
        for v in range(lo, hi + 1):
            nodes[0] += 1
            if nodes[0] > max_nodes:
                return False
            w[x] = v
            if all(feasible(c) for c in watch[x]):
                if not rec(i + 1):
                    return False
        del w[x]
        return True

    ok = rec(0)
    return sols, not ok


def main(argv):
    if len(argv) not in (3, 4):
        print("usage: scpsem.py MODEL.scp NAMES [MAX_NODES]", file=sys.stderr)
        return 64
    fzn_of = dict(l.split() for l in open(argv[2]) if l.strip())
    try:
        bounds, cons = load(argv[1])
    except Refused as e:
        print(f"REFUSED: {e}", file=sys.stderr)
        return 2
    sols, toobig = solve(bounds, cons, int(argv[3]) if len(argv) == 4 else 2_000_000)
    if toobig:
        print("toobig")
        return 0
    lines = sorted(" ".join(f"{fzn_of[v]}={s[v]}" for v in sorted(s, key=lambda v: fzn_of[v]))
                   for s in sols)
    print(f"count {len(lines)}")
    print("\n".join(lines))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
