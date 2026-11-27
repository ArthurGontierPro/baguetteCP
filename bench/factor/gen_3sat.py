#!/usr/bin/env python3
"""Planted random 3-SAT as FlatZinc, for the per-node factor lane (M17-bench-series-T6, D-0256).

    python3 -I bench/factor/gen_3sat.py N RATIO SEED > bench/factor/sat3_N_SEED.fzn

N Boolean variables and round(RATIO * N) clauses of three distinct variables. A hidden
assignment is drawn first (each variable true with probability 1/2), and every clause is drawn
uniformly among the 3-clauses it SATISFIES (a clause it falsifies is redrawn), so the instance is
satisfiable by construction: the planted assignment is a model. That is the "planted" or "1-hidden"
distribution; its literals lean towards the hidden assignment (a variable agrees with it in 4 of 7
of its occurrences on average), so it is easier than uniform random 3-SAT at the same ratio, and it
is the probe of the 2026-11-23 code review (170 variables, ratio 4.26) made certain to be SAT.

The output is plain FlatZinc that baguette, Gecode and Chuffed all read unchanged (no flattening):
`bool_clause` per clause and a complete `bool_search` in input order, false first, so the three
solvers walk the same tree when none of them learns. The planted assignment is written as a comment
so that any reader can check it against the clauses.

Deterministic: Python's `random.Random(seed)` with `randrange` only, whose sequence is stable across
Python 3 versions. The committed .fzn files are the reference; regenerating must give the same bytes.
"""
import random
import sys


def main():
    if len(sys.argv) != 4:
        sys.exit(__doc__)
    n, ratio, seed = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
    m = round(ratio * n)
    rng = random.Random(seed)
    hidden = [rng.randrange(2) == 1 for _ in range(n)]
    clauses = []
    while len(clauses) < m:
        vs = []
        while len(vs) < 3:
            v = rng.randrange(n)
            if v not in vs:
                vs.append(v)
        signs = [rng.randrange(2) == 1 for _ in vs]  # True: the positive literal
        if any(hidden[v] == s for v, s in zip(vs, signs)):
            clauses.append(list(zip(vs, signs)))
    out = sys.stdout
    out.write("%% planted 3-SAT: gen_3sat.py %d %s %d (bench/factor, D-0256)\n" % (n, sys.argv[2], seed))
    out.write("%% %d variables, %d clauses, satisfiable by construction\n" % (n, m))
    out.write("%% planted: %s\n" % "".join("1" if h else "0" for h in hidden))
    for i in range(n):
        out.write("var bool: x%d :: output_var;\n" % (i + 1))
    for c in clauses:
        pos = ",".join("x%d" % (v + 1) for v, s in c if s)
        neg = ",".join("x%d" % (v + 1) for v, s in c if not s)
        out.write("constraint bool_clause([%s],[%s]);\n" % (pos, neg))
    xs = ",".join("x%d" % (i + 1) for i in range(n))
    out.write("solve :: bool_search([%s],input_order,indomain_min,complete) satisfy;\n" % xs)


if __name__ == "__main__":
    main()
