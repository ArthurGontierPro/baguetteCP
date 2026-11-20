#!/usr/bin/env python3
"""M4-T6 spike (D-0184), the control experiment: how many of the GAC removal lines are RUP
against the solver's .opb (D-0060's guarded rows) WITHOUT the table?

For each removal line i that tabulate.py wrote (search lines, not the tabulation), build a
one-line proof `rup <line i>` against the .opb plus every EARLIER search line appended to it
as an axiom (they are true -- the tabulated proof derived them -- so adding them is sound for
the measurement and isolates line i), and ask veripb. Prints `rup_without_table=K/N`.

  no_table.py MODEL.opb TAB.pbp WORKDIR
"""

import os
import re
import subprocess
import sys

opb, pbp, work = sys.argv[1], sys.argv[2], sys.argv[3]
veripb = os.environ.get("VERIPB", os.path.expanduser("~/.cargo/bin/veripb"))
os.makedirs(work, exist_ok=True)
base = open(opb).read().splitlines()
hdr = [i for i, l in enumerate(base) if l.startswith("* #variable=")][0]
nvar = int(re.search(r"#variable=\s*(\d+)", base[hdr]).group(1))
ncon = int(re.search(r"#constraint=\s*(\d+)", base[hdr]).group(1))
lines = open(pbp).read().splitlines()
# search lines: everything after the tabulation's `del id` line, rup only, no selector
start = max(i for i, l in enumerate(lines) if l.startswith("del id")) + 1
kinds = dict(l.split() for l in open(pbp + ".kinds"))
search = []
for l in lines[start:]:
    m = re.match(r"(@t\d+) rup (.*;)$", l)
    if m and "tab_s_" not in m.group(2):
        search.append((m.group(2), kinds[m.group(1)]))
ok, refused, n = 0, [], 0
for i, (c, kind) in enumerate(search):
    if kind != "prune":
        continue
    n += 1
    extra = [e for e, _ in search[:i]]
    hdr_line = f"* #variable= {nvar} #constraint= {ncon + len(extra)}"
    body = [hdr_line] + [l for j, l in enumerate(base) if j != hdr] + extra
    o = os.path.join(work, f"n{i}.opb")
    p = os.path.join(work, f"n{i}.pbp")
    open(o, "w").write("\n".join(body) + "\n")
    open(p, "w").write(
        f"pseudo-Boolean proof version 3.0\nf {ncon + len(extra)} ;\nrup {c}\noutput NONE ;\nconclusion NONE ;\nend pseudo-Boolean proof ;\n"
    )
    r = subprocess.run([veripb, o, p], capture_output=True, text=True, timeout=300)
    if "VERIFIED" in r.stdout:
        ok += 1
    elif "reverse unit propagation" in r.stdout + r.stderr:
        refused.append(c)
    else:
        sys.exit(f"unexpected checker output on line {i}: {(r.stdout + r.stderr)[:300]}")
print(f"rup_without_table={ok}/{n}")
for c in refused:
    print("  refused:", c)
