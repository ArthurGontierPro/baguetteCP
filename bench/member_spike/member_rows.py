#!/usr/bin/env python3
"""M7-T28 (D-0159): how many .opb rows compile.ml's [post_member] writes for each
baguette_member call of a flattened model, from the declared hulls alone (the same
threshold ranges as post_member), against what std's decomposition costs (n int_eq_reif).
Usage: member_rows.py <model.fzn>   prints: calls, positions, rows, widest union hull."""
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
            return 0 if any(p == 1 for p in parts) else 1

        for v in range(max(ly, lo + 1), min(hx + 1, hi) + 1):
            g = ge(ly, hy, v)
            rows += written([None if g is None else 1 - g, ge(lx, hx, v)])
        rows += 1 if ly > hx + 1 else 0
        for v in range(max(lx, lo + 1), min(hy + 1, hi) + 1):
            g = ge(lx, hx, v)
            rows += written([None if g is None else 1 - g, ge(ly, hy, v)])
        rows += 1 if lx > hy + 1 else 0
    rows += 1
print("calls=%d positions=%d rows=%d widest_union=%d" % (calls, positions, rows, widest))
