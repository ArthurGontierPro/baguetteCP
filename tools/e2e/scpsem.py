#!/usr/bin/env python3
"""Every solution of a .scp, under the semantics of CakeML's cpScript.sml. Written for
M14-e2e-verification-T2, the first end-to-end lane.

Usage: python3 -I scpsem.py MODEL.scp NAMES [MAX_NODES]

The translator (fzn2scp.py) is the one trusted link of the chain that no theorem covers
(D-0174 section 5, in the record that chose CakeML's cake_pb_cp as the verified encoder),
and a wrong translation verifies. This is half of its test: it reads
ONLY the .scp (not the FlatZinc, not the translator's code) and enumerates the assignments
cake's semantics admit, by backtracking with interval pruning. The other half is Gecode's
FlatZinc interpreter on the .fzn (fzn_solutions.py), which `scripts/e2e_lane.sh` runs and
compares with this through validate.py.

The semantics, transcribed from cpScript.sml (CakeML master, 2026-11):
  valid_assignment   every variable within its (name lb ub)
  lin_<cmp> (c1 X1 ...) Y      cmpop_val cmp (sum ci * Xi) Y      (lin_sem, Zr = NONE)
  <cmp> X Y                    cmpop_val cmp X Y                  (cmpop_sem, Zr = NONE)
     cmp: equals =, not_equals !=, less_equal <=, less_than <, greater_equal >=, greater_than >
  all_different (X1 ...)       ALL_DISTINCT (MAP (varc w) Xs)     (AllDifferentExcept Xs [])
  in (X1 ...) Y                MEM (varc w Y) (MAP (varc w) Xs)   (in_sem)
  and the T4 forms (M14-e2e-verification-T4, D-0178: the Boolean and reified families),
  a reify tuple (Z op v) meaning `varc Z op v`, op in = != >= > <= <:
  <cmp>_iff R X Y              R <=> cmpop_val cmp X Y            (cmpop_sem, Zr = INR R)
  lin_<cmp>_iff R (c1 X1 ...) Y   R <=> cmpop_val cmp (sum ...) Y  (lin_sem, Zr = INR R)
  or (R1 ...) R                R <=> EXISTS Ri                    (or_sem)
  and (R1 ...) R               R <=> EVERY Ri                     (and_sem)
  and the T5 forms (D-0180, the globals):
  <cmp>_if R X Y               R ==> cmpop_val cmp X Y            (cmpop_sem, Zr = INL R)
  element (A0 ...) (Y off) Z   0 <= Y-off < n and Z = A[Y-off]    (element_sem)
  gacglobalcardinality (X1 ...) (v1 ...) (C1 ...)
                               each Cj = #{i : Xi = vj}           (global_cardinality_sem, open)
  array_max (X1 ...) Y         Y is some Xi and every Xi <= Y     (array_max_sem)
  array_min (X1 ...) Y         Y is some Xi and every Xi >= Y     (array_min_sem)
  max X Y Z, min X Y Z         max(X, Y) = Z, min(X, Y) = Z      (binop_sem)
  inverse ((X1 ...) ox) ((Y1 ...) oy)
                               same length n; every Xi - oy and Yj - ox in [0, n);
                               X[i-ox] = j <=> Y[j-oy] = i over i in ox.., j in oy..  (inverse_sem)
  and the T6 forms (D-0195, the far families):
  abs X Y                      ABS X = Y                          (unop_sem Abs)
  cumulative (X1 ...) (W1 ...) (H1 ...) C
                               equal lengths, every Hi >= 0, C >= 0, and at every t the Hi
                               of the i with Xi <= t < Xi + Wi sum to at most C  (cumulative_sem)
  regular (X1 ...) n ((edges_0) ...) (f ...)
                               some run from state 0 along edges (v q') of EL q trans, every
                               state < n, ends in a final state      (regular_sem, nfa_accepts)
  and, for baguette's own .scp reader (lib/scp/, M23-inputs, D-0230), each checked once its
  variables are assigned:
  gacglobalcardinalityclosed, boundsglobalcardinality[closed]   the gcc above, closed: every
                               Xi is one of the vi                (global_cardinality_sem)
  count (X1 ...) Y Z           Z = #{i : Xi = Y}                  (count_sem)
  plus X Y Z, minus X Y Z      X + Y = Z, X - Y = Z               (binop_sem)
  neg X Y                      -X = Y                             (unop_sem Negative)
  multiply X Y Z               X * Y = Z                          (nlop_sem Mult)
  divide X Y Z                 Y != 0 and X quot Y = Z, truncated (nlop_sem Div)
  increasing, strictly_increasing, decreasing, strictly_decreasing (X1 ...)
                               SORTED by <=, <, >=, >             (sorted_sem)
  table ((t11 ...) ...) (X1 ...)   every row of length n, some row matches, `*` any value
                                                                  (table_sem)
  circuit (X1 ...)             every Xi in 0..n-1, and from every i the successors return
                               to i after n steps and not before  (circuit_sem)
  `enumerate` is read as `decide`: the set of solutions is the same.
Any other keyword, or a `_if` form other than a comparison's, is refused (exit 2). The
prob_type is `decide`, or `(minimize X)` / `(maximize X)` (T8, D-0182, objectives), whose
solutions are the same set: the objective only adds the line
`objective minimize|maximize NAME` at the end, NAME the FlatZinc name of X, for validate.py to
take the optimum over the set.

Prints `count N` then one line per solution, `name=value ...` over the FlatZinc names of
NAMES, sorted; or `toobig` when MAX_NODES (default 2,000,000) is exceeded. Exit 0 in both
cases; 2 with a `REFUSED:` line on stderr when the .scp is refused; 64 with a usage line on
stderr when the argument count is wrong; 1 on an unbalanced s-expression.
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
    pt = sec.get("prob_type")
    objective = None
    if (pt and len(pt) == 1 and isinstance(pt[0], list) and len(pt[0]) == 2
            and pt[0][0] in ("minimize", "maximize") and isinstance(pt[0][1], str)):
        objective = (pt[0][0], pt[0][1])
    elif pt not in (["decide"], ["enumerate"]):
        raise Refused(f"prob_type {pt}")
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
        elif kw.endswith("_if") and kw[:-3] in CMP:
            # one-sided: R ==> X cmp Y (reify_sem's INL)
            kw = kw[:-3]
            x, y = args[1:]
            cons.append(("imp", reify(args[0]), CMP[kw], term(x), term(y)))
            continue
        if kw == "element":
            lst, (y, off), z = args
            cons.append(("elem", [term(a) for a in lst], term(y), int(off), term(z)))
            continue
        fn = FN.get(kw)
        if fn is not None:
            arity, flat, check = fn
            if len(args) != arity:
                raise Refused(f"{name}: {kw} takes {arity} arguments")
            ts, shape = flat(args, term)
            cons.append(("fn", check, ts, shape))
            continue
        if kw == "gacglobalcardinality":
            xs, vs, cs = args
            if len(vs) != len(cs):
                raise Refused(f"{name}: {len(vs)} values for {len(cs)} counts")
            cons.append(("gcc", [term(a) for a in xs], [int(v) for v in vs],
                         [term(a) for a in cs]))
            continue
        if kw in ("array_max", "array_min", "max", "min"):
            if kw.startswith("array_"):
                lst, y = args
                xs = [term(a) for a in lst]
            else:
                xs, y = [term(args[0]), term(args[1])], args[2]
            cons.append(("ext", max if kw.endswith("max") else min, xs, term(y)))
            continue
        if kw == "abs":
            x, y = args
            cons.append(("abs", term(x), term(y)))
            continue
        if kw == "cumulative":
            xs, ws, hs, cap = args
            cons.append(("cumul", [term(a) for a in xs], [term(a) for a in ws],
                         [term(a) for a in hs], term(cap)))
            continue
        if kw == "regular":
            xs, n, trans, fin = args
            cons.append(("reg", [term(a) for a in xs], int(n),
                         [[(int(v), int(q)) for v, q in es] for es in trans],
                         [int(f) for f in fin]))
            continue
        if kw == "inverse":
            (xs, ox), (ys, oy) = args
            cons.append(("inv", [term(a) for a in xs], int(ox), [term(a) for a in ys], int(oy)))
            continue
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
    return bounds, cons, objective


def _quot(x, y):
    q = abs(x) // abs(y)
    return q if (x >= 0) == (y >= 0) else -q


def _circuit(xs):
    n = len(xs)
    if not all(0 <= x < n for x in xs):
        return False
    for i in range(n):
        j = i
        for k in range(1, n):
            j = xs[j]
            if j == i:
                return False
    return True


def _table(rows, xs):
    return all(len(r) == len(xs) for r in rows) and any(
        all(t is None or t == x for t, x in zip(r, xs)) for r in rows)


def _list(a, term):
    return [term(x) for x in a]


# keyword -> (arity, args -> (terms, shape), (values, shape) -> bool). The terms are
# flattened; the shape is what the check needs to cut them back up.
FN = {
    "plus": (3, lambda a, t: (_list(a, t), None), lambda v, _: v[0] + v[1] == v[2]),
    "minus": (3, lambda a, t: (_list(a, t), None), lambda v, _: v[0] - v[1] == v[2]),
    "neg": (2, lambda a, t: (_list(a, t), None), lambda v, _: -v[0] == v[1]),
    "multiply": (3, lambda a, t: (_list(a, t), None), lambda v, _: v[0] * v[1] == v[2]),
    "divide": (3, lambda a, t: (_list(a, t), None),
               lambda v, _: v[1] != 0 and _quot(v[0], v[1]) == v[2]),
    "count": (3, lambda a, t: (_list(a[0], t) + [t(a[1]), t(a[2])], None),
              lambda v, _: v[-1] == sum(1 for x in v[:-2] if x == v[-2])),
    "circuit": (1, lambda a, t: (_list(a[0], t), None), lambda v, _: _circuit(v)),
    "table": (2, lambda a, t: (_list(a[1], t),
                               [[None if e == "*" else int(e) for e in r] for r in a[0]]),
              lambda v, rows: _table(rows, v)),
}
for _kw, _op in (("increasing", operator.le), ("strictly_increasing", operator.lt),
                 ("decreasing", operator.ge), ("strictly_decreasing", operator.gt)):
    FN[_kw] = (1, lambda a, t: (_list(a[0], t), None),
               (lambda op: lambda v, _: all(op(x, y) for x, y in zip(v, v[1:])))(_op))
for _kw in ("gacglobalcardinalityclosed", "boundsglobalcardinality",
            "boundsglobalcardinalityclosed"):
    FN[_kw] = (3, lambda a, t: (_list(a[0], t) + _list(a[2], t),
                                ([int(x) for x in a[1]], len(a[0]))),
               (lambda closed: lambda v, sh: len(sh[0]) == len(v) - sh[1] and all(
                   c == sum(1 for x in v[:sh[1]] if x == val)
                   for val, c in zip(sh[0], v[sh[1]:]))
                and (not closed or all(x in sh[0] for x in v[:sh[1]])))(
                   _kw.endswith("closed")))


def terms_of(c):
    if c[0] == "fn":
        return c[2]
    if c[0] == "imp":
        return [c[1][0], c[3], c[4]]
    if c[0] == "elem":
        return c[1] + [c[2], c[4]]
    if c[0] == "gcc":
        return c[1] + c[3]
    if c[0] == "ext":
        return c[2] + [c[3]]
    if c[0] == "inv":
        return c[1] + c[3]
    if c[0] == "abs":
        return [c[1], c[2]]
    if c[0] == "cumul":
        return c[1] + c[2] + c[3] + [c[4]]
    if c[0] == "reg":
        return c[1]
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
        if c[0] in ("imp", "elem", "gcc", "ext", "inv", "abs", "cumul", "reg", "fn"):
            # T5's forms are checked once every variable they name is assigned
            if any(v is None for v in vals):
                return True
            return global_holds(c)
        if c[0] == "alldiff":
            got = [v for v in vals if v is not None]
            return len(got) == len(set(got))
        if any(v is None for v in vals):
            return True
        return vals[-1] in vals[:-1]

    def global_holds(c):
        if c[0] == "fn":
            return c[1]([val(t) for t in c[2]], c[3])
        if c[0] == "imp":
            return (not holds(c[1])) or c[2](val(c[3]), val(c[4]))
        if c[0] == "elem":
            xs, y, z = [val(t) for t in c[1]], val(c[2]) - c[3], val(c[4])
            return 0 <= y < len(xs) and z == xs[y]
        if c[0] == "gcc":
            xs = [val(t) for t in c[1]]
            return all(val(cj) == sum(1 for x in xs if x == v) for v, cj in zip(c[2], c[3]))
        if c[0] == "ext":
            xs, y = [val(t) for t in c[2]], val(c[3])
            return y in xs and c[1](xs + [y]) == y
        if c[0] == "inv":
            xs, ox, ys, oy = [val(t) for t in c[1]], c[2], [val(t) for t in c[3]], c[4]
            n = len(xs)
            if len(ys) != n:
                return False
            if not all(0 <= x - oy < n for x in xs) or not all(0 <= y - ox < n for y in ys):
                return False
            return all((xs[i] == oy + j) == (ys[j] == ox + i) for i in range(n) for j in range(n))
        if c[0] == "abs":
            return abs(val(c[1])) == val(c[2])
        if c[0] == "cumul":
            xs, ws, hs = ([val(t) for t in c[i]] for i in (1, 2, 3))
            cap = val(c[4])
            if not len(xs) == len(ws) == len(hs) or min(hs, default=0) < 0 or cap < 0:
                return False
            # the sum only changes where a task starts, so those t are enough
            return all(sum(h for x, w, h in zip(xs, ws, hs) if x <= t < x + w) <= cap
                       for t in xs)
        if c[0] == "reg":
            xs, n, trans, fin = [val(t) for t in c[1]], c[2], c[3], c[4]
            states = {0} if 0 < n else set()
            for v in xs:
                states = {q2 for q in states if q < len(trans)
                          for (sym, q2) in trans[q] if sym == v and q2 < n}
            return any(q in fin for q in states)
        raise AssertionError(c[0])

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
        bounds, cons, objective = load(argv[1])
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
    if objective:
        print(f"objective {objective[0]} {fzn_of[objective[1]]}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
