#!/usr/bin/env python3
"""M7-T28 (D-0159): how many .opb rows compile.ml's [post_member] writes for each
baguette_member call of a flattened model, from the declared hulls alone (the same
threshold ranges as post_member), against what std's decomposition costs (n int_eq_reif).
Usage: member_rows.py <model.fzn>   prints: calls, positions, rows, widest union hull.

M7-T34 (D-0169): also what the big-M encoding writes -- OR, and per position over the
overlap [a, b] of the declared hulls the four bound clauses a constant does not fold and
the two big-M rows over the overlap's rungs (the single row ~b_k for disjoint hulls; none
for a position that IS y) -- as rows and literals, next to the threshold rows' literals;
and the first version's rows over the WHOLE hulls (x_k - y + M ~b_k >= 0), as literals.
"""
import re
import sys

text = open(sys.argv[1]).read()
dom = {}
for m in re.finditer(r"^var (-?\d+)\.\.(-?\d+): (\w+)", text, re.M):
    dom[m.group(3)] = (int(m.group(1)), int(m.group(2)))
for m in re.finditer(r"^var \{([-\d,]+)\}: (\w+)", text, re.M):
    vs = [int(v) for v in m.group(1).split(",")]
    dom[m.group(2)] = (min(vs), max(vs))
for m in re.finditer(r"^var bool: (\w+)", text, re.M):
    dom[m.group(1)] = (0, 1)
arrays = {}
for m in re.finditer(r"^array \[1\.\.\d+\] of var [^:]*: (\w+)[^=]*= \[([^\]]*)\]", text, re.M):
    arrays[m.group(1)] = [s.strip() for s in m.group(2).split(",") if s.strip()]


def hull(tok):
    if re.fullmatch(r"-?\d+", tok):
        return (int(tok), int(tok))
    return dom.get(tok, (0, 0))


calls = positions = rows = widest = 0
lits = big_rows = big_lits = full_lits = 0
for m in re.finditer(r"^constraint baguette_member(?:_bool)?\((\[[^\]]*\]|\w+),\s*([-\w]+),", text, re.M):
    a = m.group(1)
    xs = [s.strip() for s in a.strip("[]").split(",") if s.strip()] if a.startswith("[") else arrays.get(a, [])
    ly, hy = hull(m.group(2))
    calls += 1
    for x in xs:
        positions += 1
        lx, hx = hull(x)
        lo, hi = min(lx, ly), max(hx, hy)
        widest = max(widest, hi - lo)
        def ge(l, h, v):  # [z >= v]: 1 true, 0 false, None a literal
            return 1 if v <= l else 0 if v > h else None

        def written(parts):  # a row with a true part is not written
            global lits
            if any(p == 1 for p in parts):
                return 0
            lits += 1 + sum(1 for p in parts if p is None)  # ~b_k and the literals left
            return 1

        if x != m.group(2):
            for mb in (hy - lx, hx - ly):  # the whole-hull rows, built first
                if mb > 0:
                    full_lits += 1 + (hx - lx) + (hy - ly)
            a, b = max(lx, ly), min(hx, hy)
            if a > b:
                big_rows += 1
                big_lits += 1
            else:
                for written_clause in (a > lx, b < hx, a > ly, b < hy):
                    if written_clause:
                        big_rows += 1
                        big_lits += 2
                if b > a:
                    big_rows += 2
                    big_lits += 2 * (2 * (b - a) + 1)

        for v in range(max(ly, lo + 1), min(hx + 1, hi) + 1):
            g = ge(ly, hy, v)
            rows += written([None if g is None else 1 - g, ge(lx, hx, v)])
        if ly > hx + 1:
            rows += 1
            lits += 1
        for v in range(max(lx, lo + 1), min(hy + 1, hi) + 1):
            g = ge(lx, hx, v)
            rows += written([None if g is None else 1 - g, ge(ly, hy, v)])
        if lx > hy + 1:
            rows += 1
            lits += 1
    rows += 1
    lits += len(xs)
    big_rows += 1
    big_lits += len(xs)
print("calls=%d positions=%d rows=%d widest_union=%d lits=%d bigm_rows=%d bigm_lits=%d "
      "fullhull_lits=%d" % (calls, positions, rows, widest, lits, big_rows, big_lits, full_lits))
