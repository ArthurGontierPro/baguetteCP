#!/usr/bin/env python3
"""Join the D-0146 instance list with the D-0122 baseline (wave43run, 1200 s) and the
after run (300 s). Usage: join.py <inst.lst> <wave43run-dir> <after-dir>
Prints per group: before -> after status transitions, and the instances that changed."""
import collections
import glob
import os
import sys

lst, before_dir, after_dir = sys.argv[1], sys.argv[2], sys.argv[3]
groups = {}
for line in open(lst):
    if line.startswith("#") or not line.strip():
        continue
    c = line.rstrip("\n").split("\t")
    groups[c[0]] = c[3]


def load(path):
    res = {}
    for f in glob.glob(path):
        for line in open(f):
            c = line.rstrip("\n").split("\t")
            if len(c) > 2 and c[1] == "baguette":
                res[c[0]] = (c[2], c[9] if len(c) > 9 else "-", c[3], c[4] if len(c) > 4 else "-", c[5] if len(c) > 5 else "0")
    return res


before = load(os.path.join(before_dir, "*", "results.tsv"))
after = load(os.path.join(after_dir, "results.tsv"))


def cls(st):
    if st is None:
        return "MISSING"
    s = st[0]
    if s in ("OPT", "UNSAT") or (s == "SAT" and st[1] == "VERIFIED" and False):
        return "complete"
    return s


def bucket(st, sat_complete):
    if st is None:
        return "not-run"
    s, chk = st[0], st[1]
    if s in ("OPT", "UNSAT"):
        return "complete"
    if s == "SAT":
        return "complete" if sat_complete else "incumbent"
    return s


# a SAT answer on a satisfaction problem is complete; on an optimisation problem an incumbent.
# The list does not say which; the result row's 5th column carries the objective ('-' for
# satisfaction), so read it from the row itself.
def kind(st):
    return st


trans = collections.Counter()
per_group = collections.defaultdict(collections.Counter)
verified = collections.Counter()
changed = []
for iid, g in sorted(groups.items()):
    b, a = before.get(iid), after.get(iid)
    if a is None:
        continue
    def b2(st):
        if st is None:
            return "not-run"
        s = st[0]
        if s in ("OPT", "UNSAT"):
            return "COMPLETE"
        if s == "SAT":
            return "COMPLETE" if st[3] in ("-", "") else "INCUMBENT"
        if s == "TIMEOUT" and st[4] not in ("0", "-", ""):
            return "INCUMBENT"
        return s
    tb, ta = b2(b), b2(a)
    trans[(g, tb, ta)] += 1
    per_group[g][ta] += 1
    if a and a[0] in ("SAT", "OPT", "UNSAT"):
        verified[(g, a[1])] += 1
    if tb != ta:
        changed.append((iid, g, tb, ta, a[1] if a else "-", a[2] if a else "-"))
print("instances with an after result:", sum(1 for i in groups if i in after), "of", len(groups))
for (g, tb, ta), k in sorted(trans.items()):
    print("%-22s %-10s -> %-10s %3d" % (g, tb, ta, k))
print("after-answer check verdicts:", dict(verified))
print("changed:")
for r in changed:
    print("  " + "\t".join(r))
