#!/usr/bin/env python3
"""M7-T28 (D-0151 section 3): checker probes for a `member` design, before any code.
member(x, y): y equals some x_i. The .opb in the design: one SELECTOR Boolean b_i per
position (introduced by the mznlib `let`, as regular's flags are), the clause OR_i b_i, and
per position i and value v of y's declared domain the two halves of "b_i /\\ y = v -> x_i = v"
over order literals:  ~b_i \\/ y <> v \\/ x_i >= v   and   ~b_i \\/ y <> v \\/ x_i <= v
(a half with a constant literal folded). Instance: x1, x2, x3, y in 1..4, plus the model
row x3 <> 2 (an int_ne clause) so a HOLE is available as a fact the page holds.
Writes mem.opb and m*.pbp into argv[1]; probe_member.sh runs veripb on them."""
import os
import sys

out = sys.argv[1]
lo, hi = 1, 4
xs = ["x1", "x2", "x3"]


def ge(x, v):
    return "%s_ge_%d" % (x, v)


def neg(l):
    return l[1:] if l.startswith("~") else "~" + l


def ne(x, v):
    lits = []
    if v > lo:
        lits.append(neg(ge(x, v)))
    if v < hi:
        lits.append(ge(x, v + 1))
    return lits


def clause(lits):
    return " ".join("+1 " + l for l in lits) + " >= 1"


rows = []
for x in xs + ["y"]:
    for v in range(lo + 2, hi + 1):
        rows.append(clause([neg(ge(x, v)), ge(x, v - 1)]))
rows.append(clause(["b%d" % (i + 1) for i in range(len(xs))]))
for i, x in enumerate(xs):
    b = "b%d" % (i + 1)
    for v in range(lo, hi + 1):
        if v > lo:
            rows.append(clause(["~" + b] + ne("y", v) + [ge(x, v)]))
        if v < hi:
            rows.append(clause(["~" + b] + ne("y", v) + [neg(ge(x, v + 1))]))
rows.append(clause(ne("x3", 2)))  # a model hole: x3 <> 2
with open(os.path.join(out, "mem.opb"), "w") as f:
    f.write("* #variable= %d #constraint= %d\n" % (4 * (hi - lo) + 3, len(rows)))
    for k, r in enumerate(rows, 1):
        f.write("@c%d %s ;\n" % (k, r))
HEAD = ["pseudo-Boolean proof version 3.0", "f %d ;" % len(rows)]
TAIL = ["output NONE ;", "conclusion NONE ;", "end pseudo-Boolean proof ;"]


def write(name, lines, concl="conclusion NONE ;"):
    with open(os.path.join(out, name), "w") as f:
        f.write("\n".join(HEAD + lines + ["output NONE ;", concl, "end pseudo-Boolean proof ;"])
                + "\n")


def rup(claim, facts):
    return "rup " + clause(claim + [neg(f) for f in facts]) + " ;"


# m1: y <> 2 (an interior value) when 2 is out of every x_i: x1 >= 3 and x2 <= 1 as facts,
#     x3's hole from the model row
write("m1.pbp", [rup(ne("y", 2), [ge("x1", 3), neg(ge("x2", 2))])])
# m2: the same with the fact x1 >= 3 dropped: x1 = 2 can still match y = 2 -> REFUSED
write("m2.pbp", [rup(ne("y", 2), [neg(ge("x2", 2))])])
# m3: y's bound: y <= 3 (removing 4) when every x_i <= 3 (facts on x1 and x2, x3 too)
write("m3.pbp", [rup([neg(ge("y", 4))], [neg(ge("x1", 4)), neg(ge("x2", 4)), neg(ge("x3", 4))])])
# m4: ONE position left: b2 and b3 false as facts, y <= 2 as a fact -> x1 <= 2
write("m4.pbp", [rup([neg(ge("x1", 3))], [neg(ge("y", 3)), "~b2", "~b3"])])
# m5: the same claim on the LETTERS only, the selectors replaced by what killed them:
#     x2 >= 3 and x3 >= 3 exclude both from y <= 2 -> x1 <= 2. Written ALONE it is not RUP
#     (a selector's death is a case split over y's two values); see m5b
write("m5.pbp", [rup([neg(ge("x1", 3))], [neg(ge("y", 3)), ge("x2", 3), ge("x3", 3)])])
# m5b: m5 with the two SELECTOR deaths written first, each with its letter tail: b2 dies
#      because y <= 2 and x2 >= 3 leave no value they share (a sweep over y's values), the
#      same for b3. Then m5's line is RUP against them -- regular's D-0151 recursion.
sel = [rup(["~b2"], [neg(ge("y", 3)), ge("x2", 3)]), rup(["~b3"], [neg(ge("y", 3)), ge("x3", 3)])]
write("m5b.pbp", sel + [rup([neg(ge("x1", 3))], [neg(ge("y", 3)), ge("x2", 3), ge("x3", 3)])])
# m7b: m7 after the same two selector lines
write("m7b.pbp", sel + [rup(["b1"], [neg(ge("y", 3)), ge("x2", 3), ge("x3", 3)])])
# m6: a WRONG pruning: with x2 free, y <> 2 does not follow from x1 >= 3 -> REFUSED
write("m6.pbp", [rup(ne("y", 2), [ge("x1", 3)])])
# m7: a selector fixed as the last one able to match: b1 when x2 and x3 are excluded
write("m7.pbp", [rup(["b1"], [neg(ge("y", 3)), ge("x2", 3), ge("x3", 3)])])
# m8: a solution, y = 3 = x2 with b2, the others' selectors off
sol = ["~x1_ge_2", "~x1_ge_3", "~x1_ge_4", "x2_ge_2", "x2_ge_3", "~x2_ge_4", "x3_ge_2",
       "x3_ge_3", "x3_ge_4", "y_ge_2", "y_ge_3", "~y_ge_4", "~b1", "b2", "~b3"]
write("m8.pbp", ["sol " + " ".join(sol) + " ;"], "conclusion SAT ;")
# m9: a WRONG solution: y = 2 with no x_i at 2 (b1 claims x1 = 1 matches) -> REFUSED
bad = ["~x1_ge_2", "~x1_ge_3", "~x1_ge_4", "x2_ge_2", "x2_ge_3", "~x2_ge_4", "x3_ge_2",
       "x3_ge_3", "x3_ge_4", "y_ge_2", "~y_ge_3", "~y_ge_4", "b1", "~b2", "~b3"]
write("m9.pbp", ["sol " + " ".join(bad) + " ;"], "conclusion SAT ;")
