#!/usr/bin/env python3
"""M7-T28 (D-0159): the Challenge instances whose model calls `member`, from
bench/challenge/<Y>.lst -- the selection D-0122 counts (its census reads model sources).
Which of them REACH `baguette_member` once flattened is member_routes.sh's question.
Usage: select_member.py <lists-dir> <corpus-root> <out.lst>
Writes a compare_run.sh INSTANCES list (id model data) and prints the count."""
import os
import re
import sys

lists, root, out = sys.argv[1], sys.argv[2], sys.argv[3]
PAT = re.compile(r"\bmember\s*\(")
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
for y in range(2011, 2027):
    f = os.path.join(lists, "%d.lst" % y)
    if not os.path.isfile(f):
        continue
    for line in open(f):
        if line.startswith("#") or not line.strip():
            continue
        cols = line.rstrip("\n").split("\t")
        if PAT.search(source(cols[1])):
            rows.append(cols[:3])
with open(out, "w") as o:
    o.write("# M7-T28 (D-0159): Challenge instances whose model calls member\n")
    for r in rows:
        o.write("\t".join(r) + "\n")
print(len(rows))
