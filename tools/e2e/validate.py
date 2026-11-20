#!/usr/bin/env python3
"""Compare the translator's .scp with the reference reading of the .fzn (M14-e2e-verification-T2).

Usage: python3 -I validate.py SCPSEM.out NAMES BAGUETTE.out REF.out [REF.out ...]

SCPSEM.out is tools/e2e/scpsem.py on the .scp (cake's semantics, read from the .scp alone);
each REF.out is tools/e2e/fzn_solutions.py on the .fzn (a MiniZinc reference solver). The
translator passes on this model when every reference that finished gives exactly the
solution set the .scp admits, over every translated variable, and baguette's printed
solution (its output variables only) extends to one of them, or baguette said UNSAT and the
set is empty. Prints one line: `AGREE n=N refs=...`, `DIFFER ...`, or `UNCHECKED ...`.
"""
import re
import sys


def read_set(path):
    lines = open(path).read().splitlines()
    if not lines or not lines[0].startswith("count "):
        return None, (lines[0] if lines else "empty")
    n = int(lines[0].split()[1])
    # a model with no variable has one solution, the empty assignment, printed as ""
    return set((lines[1:] + [""])[:n]), None


def baguette_solution(path):
    """baguette's printed assignment, as {fzn name: value}; None when it said UNSAT."""
    text = open(path).read()
    if "=====UNSATISFIABLE=====" in text:
        return None
    sol = {}
    for l in text.splitlines():
        m = re.fullmatch(r"(\S+) = array1d\(1\.\.\d+, ?\[(.*)\]\);", l.strip())
        if m:
            for i, v in enumerate(m.group(2).split(","), 1):
                sol[f"{m.group(1)}[{i}]"] = v.strip()
            continue
        m = re.fullmatch(r"(\S+) = (\S+);", l.strip())
        if m:
            sol[m.group(1)] = m.group(2)
    conv = {"true": "1", "false": "0"}
    return {k: conv.get(v, v) for k, v in sol.items()}


def main(scpsem, names, bag_out, *refs):
    mine, why = read_set(scpsem)
    if mine is None:
        print(f"UNCHECKED scpsem: {why}")
        return 0
    used, notes = [], []
    for r in refs:
        theirs, why = read_set(r)
        tag = re.sub(r".*\.(\w+)\.ref$", r"\1", r)
        if theirs is None:
            notes.append(f"{tag}: {why}")
            continue
        if theirs != mine:
            only_scp = sorted(mine - theirs)[:1]
            only_ref = sorted(theirs - mine)[:1]
            print(f"DIFFER {tag}: scp admits {len(mine)}, {tag} {len(theirs)}; "
                  f"scp only {only_scp}, {tag} only {only_ref}")
            return 0
        used.append(tag)
    if not used:
        print(f"UNCHECKED no reference finished ({'; '.join(notes)})")
        return 0
    want = {l.split()[1] for l in open(names) if l.strip()}
    sol = baguette_solution(bag_out)
    if sol is None:
        if mine:
            print(f"DIFFER baguette said UNSAT, the .scp admits {len(mine)} solutions")
            return 0
    else:
        part = {k: v for k, v in sol.items() if k in want}
        if not any(all(f"{k}={v}" in s.split() for k, v in part.items()) for s in mine):
            print(f"DIFFER baguette's solution {part} is not one the .scp admits")
            return 0
    extra = f" ({'; '.join(notes)})" if notes else ""
    print(f"AGREE n={len(mine)} refs={','.join(used)}{extra}")
    return 0


if __name__ == "__main__":
    if len(sys.argv) < 5:
        print(__doc__.splitlines()[2], file=sys.stderr)
        sys.exit(64)
    sys.exit(main(*sys.argv[1:]))
