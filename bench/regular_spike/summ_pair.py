#!/usr/bin/env python3
"""M7-T28 (D-0151): summarise a meas_reasons.sh / meas_pair.sh results.tsv.
Usage: summ_pair.py <results.tsv> [tag ...]   (default tags: before after)
Prints per tag: complete answers (SAT/UNSAT/OPT), incumbents, no answer, verdicts; the
nodes/s summed over the instances every tag finished or timed out on; the learned-clause
width (mean and median over all learned clauses, from the histogram -- the stock
histogram's last bucket is >= 16, so the mean is a LOWER bound there and the share of
clauses at 16 or more is printed beside it); and the instances whose kind of answer moved."""
import sys
from collections import defaultdict

path = sys.argv[1]
tags = sys.argv[2:] or ["before", "after"]
rows = defaultdict(dict)
for line in open(path):
    c = line.rstrip("\n").split("\t")
    if len(c) < 9:
        continue
    iid, tag, st, wall, nodes, confl, learned, width, verdict = c[:9]
    inc = c[9] if len(c) > 9 else "-"
    rows[iid][tag] = dict(st=st, wall=float(wall) if wall not in ("-", "") else 0.0,
                          nodes=int(nodes) if nodes.isdigit() else 0, width=width,
                          verdict=verdict, inc=inc)


def kind(r):
    if r["st"] in ("SAT", "UNSAT", "OPT"):
        return "complete"
    if r["st"] == "INCUMBENT":
        return "incumbent"
    return "none"


def widths(h):
    out = []
    if h in ("-", "") or ":" not in h:
        return out
    for part in h.split(","):
        w, n = part.split(":")
        out += [int(w)] * int(n)
    return out


both = [i for i in rows if all(t in rows[i] for t in tags)]
print("instances with every tag: %d of %d" % (len(both), len(rows)))
for t in tags:
    rs = [rows[i][t] for i in both]
    k = defaultdict(int)
    for r in rs:
        k[kind(r)] += 1
    ver = defaultdict(int)
    for r in rs:
        if kind(r) == "complete":
            ver[r["verdict"].split(":")[0]] += 1
    ws = []
    for r in rs:
        ws += widths(r["width"])
    ws.sort()
    nodes = sum(r["nodes"] for r in rs)
    wall = sum(r["wall"] for r in rs)
    mean = sum(ws) / len(ws) if ws else 0
    med = ws[len(ws) // 2] if ws else 0
    ge16 = sum(1 for w in ws if w >= 16) / len(ws) if ws else 0
    print("%-8s complete %3d  incumbent %3d  none %3d  verdicts %s  nodes/s %.1f  "
          "learned %d  width mean %.1f median %d  >=16 %.0f%%"
          % (t, k["complete"], k["incumbent"], k["none"], dict(ver), nodes / wall if wall else 0,
             len(ws), mean, med, 100 * ge16))
print("moved (kind of answer):")
for i in sorted(both):
    ks = [kind(rows[i][t]) for t in tags]
    if len(set(ks)) > 1:
        print("  %-50s %s" % (i, "  ".join("%s=%s/%.0fs" % (t, rows[i][t]["st"], rows[i][t]["wall"])
                                          for t in tags)))
