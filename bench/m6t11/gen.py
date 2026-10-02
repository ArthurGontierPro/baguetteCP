#!/usr/bin/env python3
"""M6-T11 local reproducers, GENERATED, never committed as models (CLAUDE.md, D-0028).

  gen.py ne N PAD          N+1 pigeons into 1..N by pairwise int_ne, PAD unconstrained
                           0..1 variables declared FIRST (so a name lookup that scans
                           the store walks past them), searched input_order/indomain_min
  gen.py wide NV W NE      NV variables 0..W on an int_lin_le chain, int_lin_ne on the
                           first NE neighbour pairs: COMPILE cost (lever #6)
  gen.py knap NV D K SEED  multi-dimensional knapsack, maximise; learned PB rows and their
                           combination are the hot path (lever #4). Its objective is
                           declared 0..45*NV*D, a WIDE domain: /tmp only.

Write the output under /tmp and run it under `ulimit -v 4000000`.
"""
import random, sys

def ne(n, pad):
    p = n + 1
    for i in range(pad): print(f"var 0..1: pad{i};")
    print(f"array [1..{p}] of var 1..{n}: x;")
    for i in range(p):
        for j in range(i + 1, p): print(f"constraint int_ne(x[{i+1}],x[{j+1}]);")
    print("solve :: int_search(x, input_order, indomain_min, complete) satisfy;")

def wide(nv, w, nne):
    for i in range(nv): print(f"var 0..{w}: v{i};")
    for i in range(nv - 1): print(f"constraint int_lin_le([1,-1],[v{i},v{i+1}],0);")
    for i in range(min(nne, nv - 1)): print(f"constraint int_lin_ne([1,1],[v{i},v{i+1}],{w});")
    print("solve satisfy;")

def knap(nv, d, k, seed):
    random.seed(seed)
    xs = ",".join(f"x{i}" for i in range(nv))
    for i in range(nv): print(f"var 0..{d}: x{i};")
    print(f"var 0..{45 * nv * d}: obj :: output_var;")
    for _ in range(k):
        w = [random.randint(1, 9) for _ in range(nv)]
        print(f"constraint int_lin_le([{','.join(map(str, w))}],[{xs}],{sum(w) * d // 3});")
    c = [random.randint(1, 9) for _ in range(nv)]
    print(f"constraint int_lin_eq([{','.join(map(str, c))},-1],[{xs},obj],0);")
    print(f"solve :: int_search([{xs}], input_order, indomain_max, complete) maximize obj;")

kind, args = sys.argv[1], [int(a) for a in sys.argv[2:]]
{"ne": ne, "wide": wide, "knap": knap}[kind](*args)
