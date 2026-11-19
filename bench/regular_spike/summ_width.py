#!/usr/bin/env python3
"""M7-T28 (D-0151): summarise meas_width.sh's widths.tsv per tag.
Usage: summ_width.py <widths.tsv>
Per tag: complete answers (SAT/UNSAT/OPT), the wall summed over all instances (a time-out
counts its limit), nodes/s, learned clauses and their width: the mean of every clause (all
runs pooled, weighted by count) and the median of the per-run medians. Then the instances
whose kind of answer differs between tags."""
import sys
from collections import defaultdict

rows = defaultdict(dict)
tags = []
for line in open(sys.argv[1]):
    c = line.rstrip("\n").split("\t")
    if len(c) < 9:
        continue
    iid, tag, st, wall, nodes, n, mean, med, p90 = c[:9]
    if tag not in tags:
        tags.append(tag)
    rows[iid][tag] = dict(st=st, wall=float(wall), nodes=int(nodes or 0), n=int(n),
                          mean=float(mean) if mean != "-" else None,
                          med=int(med) if med != "-" else None)
done = [i for i in rows if all(t in rows[i] for t in tags)]
print("instances with every tag: %d" % len(done))
for t in tags:
    rs = [rows[i][t] for i in done]
    comp = sum(1 for r in rs if r["st"] in ("SAT", "UNSAT", "OPT"))
    wall = sum(r["wall"] for r in rs)
    nodes = sum(r["nodes"] for r in rs)
    n = sum(r["n"] for r in rs)
    tot = sum(r["n"] * r["mean"] for r in rs if r["mean"] is not None)
    meds = sorted(r["med"] for r in rs if r["med"] is not None)
    print("%-6s complete %2d  wall %6.0f s  nodes/s %6.1f  learned %7d  width mean %6.1f  "
          "median of medians %s"
          % (t, comp, wall, nodes / wall if wall else 0, n, tot / n if n else 0,
             meds[len(meds) // 2] if meds else "-"))
print("differs:")
for i in sorted(done):
    ks = [rows[i][t]["st"] for t in tags]
    if len(set(k in ("SAT", "UNSAT", "OPT") for k in ks)) > 1:
        print("  %-40s %s" % (i, "  ".join("%s=%s/%.0fs/%dn" % (t, rows[i][t]["st"], rows[i][t]["wall"],
                                                          rows[i][t]["nodes"]) for t in tags)))
