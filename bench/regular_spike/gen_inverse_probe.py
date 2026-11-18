#!/usr/bin/env python3
"""M7-T28 (D-0146 section 7): the checker probes for an `inverse` design, before any code.
Instance: f, g (= invf) of size 3 on 1..3, inverse(f, g): f[i] = j <-> g[j] = i. The .opb
holds std's semantics as the channel rows CH(i,j): f_i = j -> g_j = i and CH'(j,i):
g_j = i -> f_i = j, each as two clauses over order literals. Writes inv.opb and i*.pbp to
argv[1]; probe_regular.sh-style verdicts come from probe_inverse.sh."""
import os
import sys

out = sys.argv[1]
n, lo, hi = 3, 1, 3


def ge(x, v):
    return "%s_ge_%d" % (x, v)


def neg(lit):
    return lit[1:] if lit.startswith("~") else "~" + lit


def ne(x, v):
    """x <> v as order literals, constant halves dropped."""
    lits = []
    if v > lo:
        lits.append(neg(ge(x, v)))
    if v < hi:
        lits.append(ge(x, v + 1))
    return lits


def eq_parts(x, v):
    """x = v as the conjunction of its order literals (each a separate clause head)."""
    parts = []
    if v > lo:
        parts.append(ge(x, v))
    if v < hi:
        parts.append(neg(ge(x, v + 1)))
    return parts


def clause(lits):
    return " ".join("+1 " + x for x in lits) + " >= 1"


rows = []
for x in ["f%d" % i for i in range(1, n + 1)] + ["g%d" % j for j in range(1, n + 1)]:
    for v in range(lo + 2, hi + 1):
        rows.append(clause([neg(ge(x, v)), ge(x, v - 1)]))
for i in range(1, n + 1):
    for j in range(1, n + 1):
        for p in eq_parts("g%d" % j, i):  # f_i = j -> g_j = i
            rows.append(clause(ne("f%d" % i, j) + [p]))
        for p in eq_parts("f%d" % i, j):  # g_j = i -> f_i = j
            rows.append(clause(ne("g%d" % j, i) + [p]))
with open(os.path.join(out, "inv.opb"), "w") as f:
    f.write("* #variable= %d #constraint= %d\n" % (2 * n * (hi - lo), len(rows)))
    for k, r in enumerate(rows, 1):
        f.write("@c%d %s ;\n" % (k, r))
HEAD = ["pseudo-Boolean proof version 3.0", "f %d ;" % len(rows)]
TAIL = ["output NONE ;", "conclusion NONE ;", "end pseudo-Boolean proof ;"]


def write(name, lines):
    with open(os.path.join(out, name), "w") as f:
        f.write("\n".join(HEAD + lines + TAIL) + "\n")


# i1: a channel prune at a bound: f1 >= 2 (fact) -> g1 <> 1, claimed as g1 >= 2
write("i1.pbp", ["rup +1 g1_ge_2 +1 ~f1_ge_2 >= 1 ;"])
# i2: an interior hole: f2 <= 1 (fact) -> g2 <> 2
write("i2.pbp", ["rup +1 ~g2_ge_2 +1 g2_ge_3 +1 f2_ge_2 >= 1 ;"])
# i3: a WRONG channel prune: f1 >= 2 does not exclude g2 = 1
write("i3.pbp", ["rup +1 g2_ge_2 +1 ~f1_ge_2 >= 1 ;"])
# i4: the pairwise disequality all_different would cite, f1 = 2 and f2 = 2 exclusive, as a
#     ROOT LEMMA: rup from CH(1,2), CH(2,2)
write("i4.pbp", ["rup " + clause(ne("f1", 2) + ne("f2", 2)) + " ;"])
# i5: a HALL prune with f1, f2 confined to {1, 2}: f3 >= 3. Not one channel row's
#     consequence -- a counting argument -- so stated as a bare rup it should be REFUSED
write("i5.pbp", ["rup +1 f3_ge_3 +1 f1_ge_3 +1 f2_ge_3 >= 1 ;"])
