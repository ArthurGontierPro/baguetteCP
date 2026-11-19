#!/usr/bin/env python3
"""M7-T28 (D-0159): checker probes for the ROWS of `member`, before any member code.

D-0151 section 3.1 designed the rows as the VALUE form, per position i and value v of y's
declared domain:   ~b_i \\/ y <> v \\/ x_i >= v     ~b_i \\/ y <> v \\/ x_i <= v
D-0151's probes (bench/regular_spike/gen_member_probe.py) never put two HOLES of x_i inside
y's range under one selector death, nor two hole-excluded positions under one value
removal of y. This file does both, against the value form and against the BOUND form (the
order encoding's own equality, per position i and threshold v):
                   ~b_i \\/ ~[y >= v] \\/ [x_i >= v]     ~b_i \\/ ~[x_i >= v] \\/ [y >= v]
with every constant literal folded at a declared bound.

Instance: x1, x2, x3, y in 1..5, model rows (the page's holes, facts []) x1 <> 2, x1 <> 4,
x2 <> 2 and y <> 3, plus the OR row b1 \\/ b2 \\/ b3. Writes memV.opb, memB.opb and q*.pbp
into argv[1]; probe_rows.sh runs veripb on every (opb, probe) pair."""
import os
import sys

out = sys.argv[1]
LO, HI = 1, 5
XS = ["x1", "x2", "x3"]
HOLES = [("x1", 2), ("x1", 4), ("x2", 2), ("y", 3)]


def ge(x, v):
    return "%s_ge_%d" % (x, v)


def neg(l):
    return l[1:] if l.startswith("~") else "~" + l


# A literal over the ladder: None for the constant true, False for the constant false.
def lit_ge(x, v):
    if v <= LO:
        return None
    if v > HI:
        return False
    return ge(x, v)


def lit_not(l):
    if l is None:
        return False
    if l is False:
        return None
    return neg(l)


def ne(x, v):
    return [l for l in (lit_not(lit_ge(x, v)), lit_ge(x, v + 1)) if l not in (None, False)]


def clause(lits):
    return " ".join("+1 " + l for l in lits) + " >= 1"


def row(parts):
    """A disjunction of literals; None (true) drops the row, False drops the literal."""
    if any(p is None for p in parts):
        return None
    return clause([p for p in parts if p is not False])


base = []
for x in XS + ["y"]:
    for v in range(LO + 2, HI + 1):
        base.append(clause([neg(ge(x, v)), ge(x, v - 1)]))
for x, v in HOLES:
    base.append(clause(ne(x, v)))
base.append(clause(["b%d" % (i + 1) for i in range(len(XS))]))
OR_ID = len(base)


def value_rows():
    rows = []
    for i, x in enumerate(XS):
        b = "~b%d" % (i + 1)
        for v in range(LO, HI + 1):
            if v > LO:
                rows.append(clause([b] + ne("y", v) + [ge(x, v)]))
            if v < HI:
                rows.append(clause([b] + ne("y", v) + [neg(ge(x, v + 1))]))
    return rows


def bound_rows():
    rows = []
    for i, x in enumerate(XS):
        b = "~b%d" % (i + 1)
        for v in range(LO + 1, HI + 1):
            rows.append(row([b, lit_not(lit_ge("y", v)), lit_ge(x, v)]))
            rows.append(row([b, lit_not(lit_ge(x, v)), lit_ge("y", v)]))
    return [r for r in rows if r]


def opb(name, rows):
    allr = base + rows
    with open(os.path.join(out, name), "w") as f:
        f.write("* #variable= %d #constraint= %d\n" % (4 * (HI - LO) + 3, len(allr)))
        for r in allr:
            f.write("%s ;\n" % r)
    return len(allr)


NV = opb("memV.opb", value_rows())
NB = opb("memB.opb", bound_rows())


def rup(claim, facts, label=""):
    return "%srup %s ;" % (label, clause(claim + [neg(f) for f in facts]))


def write(name, lines, concl="conclusion NONE ;"):
    # the f line is filled per .opb by probe_rows.sh (@F@), and so is the OR row's id
    with open(os.path.join(out, name), "w") as f:
        f.write("\n".join(["pseudo-Boolean proof version 3.0", "f @F@ ;"] + lines
                          + ["output NONE ;", concl, "end pseudo-Boolean proof ;"]) + "\n")


# q1: a SELECTOR DEATH across two holes of x1 inside y's range. x1 in {1,3,5} (model
#     holes), y in 2..4 by facts, y <> 3 a model hole: no common value. The value form
#     cannot chase y past 2 (y = 2 forces x1 = 2, and x1 <> 2 is a two-literal clause),
#     nor past 4 from above; the bound form alternates x1 and y upward through the holes.
write("q1.pbp", [rup(["~b1"], [ge("y", 2), neg(ge("y", 5))])])
# q1w: the same death with the fact y <= 4 dropped (y = 5 = x1 is a match) -> REFUSED
write("q1w.pbp", [rup(["~b1"], [ge("y", 2)])])
# q2: a VALUE REMOVAL y <> 2 with TWO live positions excluded from 2 by a hole only
#     (x1, x2: model holes at 2) and x3 by a bound (x3 >= 3). Not RUP in one line in
#     either form: each of b1, b2 needs its own case split.
CLAIM2 = ne("y", 2)
write("q2.pbp", [rup(CLAIM2, [ge("x3", 3)])])
# q2a: the same line after one lemma per hole-excluded position, ~b_i \/ y <> 2.
write("q2a.pbp", [rup(CLAIM2 + ["~b1"], []), rup(CLAIM2 + ["~b2"], []),
                  rup(CLAIM2, [ge("x3", 3)])])
# q2p: the derivation member.ml writes ahead in that case: one lemma per position
#      (A_i = ~b_i \/ y <> 2 \/ ~F_i), the OR row plus the lemmas, divided by their count,
#      pinned by `ia` to the claim clause, then the trace line.
write("q2p.pbp", [
    rup(CLAIM2 + ["~b1"], [], "@a1 "),
    rup(CLAIM2 + ["~b2"], [], "@a2 "),
    rup(CLAIM2 + ["~b3"], [ge("x3", 3)], "@a3 "),
    "@d pol @OR@ @a1 + @a2 + @a3 + 3 d ;",
    "ia %s : @d ;" % clause(CLAIM2 + [neg(ge("x3", 3))]),
    rup(CLAIM2, [ge("x3", 3)])])
# q2w: q2p's lemmas with x3's fact dropped from its own (x3 = 2 matches) -> a3 REFUSED
write("q2w.pbp", [
    rup(CLAIM2 + ["~b1"], [], "@a1 "),
    rup(CLAIM2 + ["~b2"], [], "@a2 "),
    rup(CLAIM2 + ["~b3"], [], "@a3 ")])
# q2c: the control -- ONE hole-excluded position (x1), x2 and x3 excluded by bounds: the
#      OR row forces b1 and its hole refutes it, one line, both forms
write("q2c.pbp", [rup(CLAIM2, [ge("x2", 3), ge("x3", 3)])])
# q3: D-0151's m5 (x1 <= 2 from y <= 2 and x2, x3 >= 3, the selectors replaced by what
#     killed them), WITHOUT the selector lines: refused in the value form (m5), and in the
#     bound form each selector dies by unit propagation from the bound facts
write("q3.pbp", [rup([neg(ge("x1", 3))], [neg(ge("y", 3)), ge("x2", 3), ge("x3", 3)])])
# q4: one position fixed: b1 as a fact, y in 2..4 by facts: x1 <> 5 (above y). And the
#     interior case: x2 <> 3 under b2, y's model hole at 3
write("q4.pbp", [rup([neg(ge("x1", 5))], ["b1", neg(ge("y", 5))])])
write("q4h.pbp", [rup(ne("x2", 3), ["b2"])])
# q5: a WRONG pruning: y <> 5 with every position free -> REFUSED
write("q5.pbp", [rup(ne("y", 5), [])])
# q6: a solution, y = 5 = x1 with b1
SOL = ["x1_ge_2", "x1_ge_3", "x1_ge_4", "x1_ge_5", "~x2_ge_2", "~x2_ge_3", "~x2_ge_4",
       "~x2_ge_5", "~x3_ge_2", "~x3_ge_3", "~x3_ge_4", "~x3_ge_5", "y_ge_2", "y_ge_3",
       "y_ge_4", "y_ge_5", "b1", "~b2", "~b3"]
write("q6.pbp", ["sol " + " ".join(SOL) + " ;"], "conclusion SAT ;")
# q7: a WRONG solution, the same with b1 swapped for b2 (x2 = 1 <> 5) -> REFUSED
SWAP = {"b1": "~b1", "~b2": "b2"}
write("q7.pbp", ["sol " + " ".join(SWAP.get(l, l) for l in SOL) + " ;"], "conclusion SAT ;")
with open(os.path.join(out, "ids"), "w") as f:
    f.write("memV.opb %d %d\nmemB.opb %d %d\n" % (NV, OR_ID, NB, OR_ID))
