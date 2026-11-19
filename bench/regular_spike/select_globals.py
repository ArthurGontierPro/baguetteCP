#!/usr/bin/env python3
"""Select the Challenge instances whose model calls regular, global_cardinality_closed /
_low_up_closed, or is community-detection (the gcc repeat), from bench/challenge/<Y>.lst.
Usage: select_instances.py <lists-dir> <corpus-root> <out.lst>
Writes a compare_run.sh INSTANCES list (id model data group) and prints counts."""
import os
import re
import sys

lists, root, out = sys.argv[1], sys.argv[2], sys.argv[3]
PAT = {
    "regular": re.compile(r"\bregular\s*\("),
    "gcc_closed": re.compile(r"\bglobal_cardinality(_low_up)?_closed\s*\("),
}
INCLUDE = re.compile(r'include\s+"([^"]+)"')


def strip_comments(s):
    s = re.sub(r"/\*.*?\*/", "", s, flags=re.S)
    return "\n".join(l.split("%", 1)[0] for l in s.splitlines())


def source(model):
    path = os.path.join(root, model)
    try:
        text = strip_comments(open(path, errors="replace").read())
    except OSError:
        return ""
    d = os.path.dirname(path)
    for inc in INCLUDE.findall(text):
        p = os.path.join(d, inc)
        if os.path.isfile(p):
            text += "\n" + strip_comments(open(p, errors="replace").read())
    return text


rows = []
counts = {}
for y in range(2011, 2027):
    f = os.path.join(lists, "%d.lst" % y)
    if not os.path.isfile(f):
        continue
    for line in open(f):
        if line.startswith("#") or not line.strip():
            continue
        cols = line.rstrip("\n").split("\t")
        iid, model, data = cols[0], cols[1], cols[2]
        src = source(model)
        groups = [g for g, p in PAT.items() if p.search(src)]
        if "community-detection" in model:
            groups.append("gcc_repeat")
        for g in groups:
            counts[g] = counts.get(g, 0) + 1
        if groups:
            rows.append((iid, model, data, "+".join(groups)))
with open(out, "w") as o:
    o.write("# M7-T28/T29 (D-0146): Challenge instances using regular, gcc_closed, or community-detection\n")
    for r in rows:
        o.write("\t".join(r) + "\n")
print(len(rows), counts)
