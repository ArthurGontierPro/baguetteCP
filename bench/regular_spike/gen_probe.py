#!/usr/bin/env python3
"""M7-T28 (D-0146): the hand-built checker probes for `regular`, written before any solver
code. Generates the .opb of a small instance in the encoding D-0146 designs, and the proofs
p1..p10, into the directory given as argv[1]. probe_regular.sh runs veripb on them.

Instance: Q = 3 states, alphabet S = {1, 2}, q0 = 1, F = {3}, n = 3, x_i in 1..3 (the value 3
is outside the alphabet, so its column is all-fail). Transitions:
  d[1,1] = 1  d[1,2] = 2
  d[2,1] = 3  d[2,2] = 0
  d[3,1] = 3  d[3,2] = 0
The language is 1* 2 1+ ; over 3 letters: 211 and 121.
"""
import os
import sys

out = sys.argv[1]
Q, n, lo, hi, q0, F = 3, 3, 1, 3, 1, {3}
d = {(1, 1): 1, (1, 2): 2, (2, 1): 3, (2, 2): 0, (3, 1): 3, (3, 2): 0}


def delta(q, v):
    return d.get((q, v), 0)


def s(i, q):
    return "s%dq%d" % (i, q)


def ge(i, v):
    return "x%d_ge_%d" % (i, v)


def neg(lit):
    return lit[1:] if lit.startswith("~") else "~" + lit


def not_in(i, a, b):
    """x_i outside [a, b], as order literals (the constant halves dropped)."""
    lits = []
    if a > lo:
        lits.append(neg(ge(i, a)))
    if b < hi:
        lits.append(ge(i, b + 1))
    return lits


def clause(lits):
    return " ".join("+1 " + x for x in lits) + " >= 1"


rows = []
for i in range(n):  # the ladders
    for v in range(lo + 2, hi + 1):
        rows.append(clause([neg(ge(i, v)), ge(i, v - 1)]))
for i in range(n + 1):
    rows.append(" ".join("+1 " + s(i, q) for q in range(1, Q + 1)) + " >= 1")  # ALO
    rows.append(" ".join("+1 ~" + s(i, q) for q in range(1, Q + 1)) + " >= %d" % (Q - 1))  # AMO
rows.append(clause([s(0, q0)]))  # start
rows.append(clause([s(n, f) for f in sorted(F)]))  # accept
for i in range(n):  # forward rows F(i,q,v)
    for q in range(1, Q + 1):
        for v in range(lo, hi + 1):
            t = delta(q, v)
            rows.append(clause([neg(s(i, q))] + not_in(i, v, v) + ([s(i + 1, t)] if t else [])))
nvars = n * (hi - lo) + (n + 1) * Q
with open(os.path.join(out, "m.opb"), "w") as f:
    f.write("* #variable= %d #constraint= %d\n" % (nvars, len(rows)))
    for k, r in enumerate(rows, 1):
        f.write("@c%d %s ;\n" % (k, r))


def B(i, qp, v):
    P = [q for q in range(1, Q + 1) if delta(q, v) == qp]
    return clause([neg(s(i + 1, qp))] + not_in(i, v, v) + [s(i, q) for q in P])


def blemmas(skip=None, mutate=None):
    out_lines = []
    for i in range(n):
        for qp in range(1, Q + 1):
            for v in range(lo, hi + 1):
                if skip == (i, qp, v):
                    continue
                c = B(i, qp, v)
                if mutate == (i, qp, v):  # the predecessor literals dropped: too strong
                    c = clause([neg(s(i + 1, qp))] + not_in(i, v, v))
                out_lines.append("rup " + c + " ;")
    return out_lines


HEAD = ["pseudo-Boolean proof version 3.0", "f %d ;" % len(rows)]


def tail(concl):
    return ["output NONE ;", concl, "end pseudo-Boolean proof ;"]


def write(name, lines):
    with open(os.path.join(out, name), "w") as f:
        f.write("\n".join(lines) + "\n")


root = [
    "rup +1 ~s0q2 >= 1 ;",  # P6 start + AMO_0
    "rup +1 ~s0q3 >= 1 ;",
    "rup +1 ~s3q1 >= 1 ;",  # P7 accept + AMO_3
    "rup +1 ~s3q2 >= 1 ;",
    "rup +1 ~s1q3 >= 1 ;",  # P1 forward death: B(0,3,*) and the two s0 lines
    "rup +1 ~s2q1 >= 1 ;",  # P2 backward death: F(2,1,*) and the two s3 lines
    "rup +1 ~x2_ge_3 >= 1 ;",  # P3 at the top bound, no fact: F(2,q,3) all fail
    "rup +1 ~x2_ge_2 >= 1 ;",  # P3 at the new top bound: the line above and ~s2q1
]
below = [
    "rup +1 ~s1q1 +1 ~x0_ge_2 >= 1 ;",  # P1 under the fact x0 >= 2
    "rup +1 s1q2 +1 ~x0_ge_2 >= 1 ;",  # P4: the last state alive at layer 1, by ALO_1
]
run = {(0, 1), (1, 2), (2, 3), (3, 3)}
sol = "sol " + " ".join(
    ["x0_ge_2", "~x0_ge_3", "~x1_ge_2", "~x1_ge_3", "~x2_ge_2", "~x2_ge_3"]
    + ["%s%s" % ("" if (i, q) in run else "~", s(i, q)) for i in range(n + 1) for q in range(1, Q + 1)]
) + " ;"
# p1: the root fixpoint, a decision x0 = 2 below it, then the solution 2 1 1 and SAT.
write("p1.pbp", HEAD + blemmas() + root + below + [sol] + tail("conclusion SAT ;"))
# p2: a B lemma too strong: B(1,3,1) with its predecessors s1q2 s1q3 dropped says "s2q3 -> x1 <> 1",
#     which the solution 2 1 1 falsifies. (At layer 0 the same mutation is IMPLIED -- s0q2 and s0q3
#     are false by the start row -- and the checker rightly accepts it; measured, not a negative.)
write("p2.pbp", HEAD + blemmas(mutate=(1, 3, 1)) + tail("conclusion NONE ;"))
# p3: a forward death BELOW the root that needs its B lemmas: under x0 >= 2 layer 1 holds q2 only,
#     and s2q2 has no live predecessor (its only edge in is q1 -2-> q2). Its fact is s1q1 dead.
#     p3 drops B(1,2,1) and B(1,2,2) and must be REFUSED; p3b keeps them and must verify. Dropping
#     only one is NOT a negative: the sweep from the top fixes x1 and the forward rows finish it.
p3_line = ["rup +1 ~s2q2 +1 s1q1 >= 1 ;"]
def drop2(lines):
    return [x for x in lines if x not in ("rup " + B(1, 2, 1) + " ;", "rup " + B(1, 2, 2) + " ;")]
write("p3.pbp", HEAD + drop2(blemmas()) + root + below + p3_line + tail("conclusion NONE ;"))
write("p3b.pbp", HEAD + blemmas() + root + below + p3_line + tail("conclusion NONE ;"))
# p4: P1 below the root with its fact dropped
write("p4.pbp", HEAD + blemmas() + root + ["rup +1 ~s1q1 >= 1 ;"] + tail("conclusion NONE ;"))
# p5: P3 at the second bound without the first bound's line
write("p5.pbp", HEAD + blemmas() + root[:6] + ["rup +1 ~x2_ge_2 >= 1 ;"] + tail("conclusion NONE ;"))
# p6: the same line with the first bound carried as a FACT on its tail instead
write("p6.pbp", HEAD + blemmas() + root[:6] + ["rup +1 ~x2_ge_2 +1 x2_ge_3 >= 1 ;"]
      + tail("conclusion NONE ;"))
# p7: a negative control: under x0 >= 2, x1 = 1 IS supported (q2 -1-> q3, q3 -1-> q3 in F), so
#     the bound move x1 >= 2 is false and must be REFUSED
write("p7.pbp", HEAD + blemmas() + root + below + ["rup +1 x1_ge_2 +1 ~x0_ge_2 >= 1 ;"]
      + tail("conclusion NONE ;"))
# p8: an interior hole that IS supported by the rows: under x0 >= 2 (so layer 1 holds q2 only),
#     x1 = 2 needs d[2,2] = 0 -> fail, so x1 <> 2: ~x1_ge_2 \/ x1_ge_3 with the facts on the tail
write("p8.pbp", HEAD + blemmas() + root + below + ["rup +1 ~x1_ge_2 +1 x1_ge_3 +1 ~x0_ge_2 >= 1 ;"]
      + tail("conclusion NONE ;"))
# p9: a sol that omits the state flags: does the checker fill them by propagation?
sol_x = "sol " + " ".join(["x0_ge_2", "~x0_ge_3", "~x1_ge_2", "~x1_ge_3", "~x2_ge_2", "~x2_ge_3"]) + " ;"
write("p9.pbp", HEAD + [sol_x] + tail("conclusion SAT ;"))
# p10: a WRONG solution (1 1 1, which the DFA rejects) with its honest state run
sol_bad = "sol " + " ".join(
    ["~x0_ge_2", "~x0_ge_3", "~x1_ge_2", "~x1_ge_3", "~x2_ge_2", "~x2_ge_3"]
    + ["%s%s" % ("" if q == 1 else "~", s(i, q)) for i in range(n + 1) for q in range(1, Q + 1)]
) + " ;"
write("p10.pbp", HEAD + [sol_bad] + tail("conclusion SAT ;"))
# p11: UNSAT at the root: refute x0 = 3 and x1 = 3 (F(i,q,3) all fail), then x0 = 1 AND x0 = 2
#      both live, so no refutation of the instance exists -- a conclusion UNSAT must be REFUSED
write("p11.pbp", HEAD + blemmas() + root + ["rup >= 1 ;"] + tail("conclusion UNSAT ;"))
