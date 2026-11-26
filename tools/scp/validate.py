#!/usr/bin/env python3
"""baguette's answer on a .scp, judged against the .scp alone (M23-inputs-T5, D-0230).

Usage: python3 -I validate.py MODEL.scp BAGUETTE_STDOUT [NAMES] [MAX_NODES]

Reads the .scp with tools/e2e/scpsem.py (the semantics of CakeML's cpScript.sml,
transcribed independently of lib/scp/), enumerates every solution, and grades the answer
baguette printed:
  UNSAT      `=====UNSATISFIABLE=====` and the .scp has no solution;
  SAT        the last solution printed is one of the .scp's;
  OPT        the same, `==========` printed, and its objective is the optimum of the set.
NAMES maps a .scp name to the FlatZinc name scpsem prints (tools/e2e/fzn2scp.py writes
it); without it, every name is its own.

Prints one line, `OK <kind>`, `WRONG <why>`, `TOOBIG` (the enumeration ran past
MAX_NODES, default 2 000 000: no verdict) or `REFUSED <why>` (scpsem does not read the
file), and exits 0 on OK and TOOBIG, 1 on WRONG, 2 on REFUSED.
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "e2e"))
import scpsem  # noqa: E402


def answer(path):
    blocks, cur, status = [], {}, None
    for line in open(path):
        line = line.rstrip("\n")
        if line == "----------":
            blocks.append(cur)
            cur = {}
        elif line == "==========":
            status = "opt"
        elif line == "=====UNSATISFIABLE=====":
            status = "unsat"
        elif " = " in line and line.endswith(";"):
            k, v = line[:-1].split(" = ", 1)
            cur[k] = int(v)
        elif line.startswith("%") or not line:
            pass
        else:
            status = status or f"unparsed: {line[:60]}"
    return blocks, status


def main(argv):
    if len(argv) not in (3, 4, 5):
        print(__doc__, file=sys.stderr)
        return 64
    scp, out = argv[1], argv[2]
    names = {}
    if len(argv) >= 4 and argv[3] != "-":
        names = dict(l.split() for l in open(argv[3]) if l.strip())
    max_nodes = int(argv[4]) if len(argv) == 5 else 2_000_000
    try:
        bounds, cons, objective = scpsem.load(scp)
    except scpsem.Refused as e:
        print(f"REFUSED {e}")
        return 2
    fzn = (lambda v: names.get(v, v))
    sols, toobig = scpsem.solve(bounds, cons, max_nodes)
    if toobig:
        print("TOOBIG")
        return 0
    blocks, status = answer(out)
    if status == "unsat":
        if blocks:
            print("WRONG solutions printed before UNSATISFIABLE")
            return 1
        if sols:
            print(f"WRONG baguette says UNSAT, the .scp has {len(sols)} solution(s)")
            return 1
        print("OK unsat")
        return 0
    if not blocks:
        print(f"WRONG no solution and no UNSAT ({status})")
        return 1
    last = blocks[-1]
    got = {fzn(k): v for k, v in last.items()}
    want = [{fzn(v): s[v] for v in s} for s in sols]
    if got not in want:
        print(f"WRONG the solution printed is not one of the .scp's {len(sols)}")
        return 1
    if objective:
        if status != "opt":
            print("WRONG an optimisation run that did not print ==========")
            return 1
        kind, x = objective
        vals = [s[x] for s in sols]
        best = min(vals) if kind == "minimize" else max(vals)
        if last[x] != best:
            print(f"WRONG objective {last[x]}, the optimum is {best}")
            return 1
        print(f"OK opt {best}")
        return 0
    print("OK sat")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
