#!/usr/bin/env python3
"""Compare the translator's .scp with the reference reading of the .fzn (M14-e2e-verification-T2).

Usage: python3 -I validate.py SCPSEM.out NAMES BAGUETTE.out REF.out [REF.out ...]

SCPSEM.out is tools/e2e/scpsem.py on the .scp (cake's semantics, read from the .scp alone);
each REF.out is tools/e2e/fzn_solutions.py on the .fzn (a MiniZinc reference solver). The
translator passes on this model when every reference that finished gives exactly the
solution set the .scp admits, over every translated variable, and baguette's printed
solution (its output variables only) extends to one of them, or baguette said UNSAT and the
set is empty. Prints one line: `AGREE n=N refs=...`, `DIFFER ...`, or `UNCHECKED ...`.

With an objective (T8, D-0182) both sides end with `objective DIR NAME`: the .scp's
prob_type read by scpsem.py (NAME by the names table), and the .fzn's solve item read by the
reference script. They must name the same direction and variable, and baguette's printed
solution (its last, the one it claims optimal) must reach the optimum of the set under it.
The solution sets alone cannot see a swapped direction or objective variable, which is why
the objective is compared as text AND by its optimum. AGREE then ends with `opt=V`.
"""
import re
import sys


def objective_of(path):
    """(direction, FlatZinc name) from a trailing `objective DIR NAME` line, else None."""
    for l in open(path).read().splitlines()[::-1]:
        m = re.fullmatch(r"objective (minimize|maximize) (\S+)", l.strip())
        if m:
            return m.group(1), m.group(2)
    return None


def read_set(path):
    lines = open(path).read().splitlines()
    if lines and lines[-1].startswith("objective "):
        lines = lines[:-1]
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
        if objective_of(r) != objective_of(scpsem):
            print(f"DIFFER {tag}: the .scp's objective is {objective_of(scpsem)}, "
                  f"the .fzn's {objective_of(r)}")
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
    opt = ""
    obj = objective_of(scpsem)
    if obj and mine:
        d, name = obj
        vals = [int(dict(kv.split("=") for kv in s.split())[name]) for s in mine]
        best = min(vals) if d == "minimize" else max(vals)
        got = sol.get(name) if sol else None
        if got is None:
            notes.append(f"baguette printed no {name}")
        elif int(got) != best:
            print(f"DIFFER baguette's {d[:3]} {name} = {got}, the .scp's optimum is {best}")
            return 0
        opt = f" opt={best}"
    extra = f" ({'; '.join(notes)})" if notes else ""
    print(f"AGREE n={len(mine)} refs={','.join(used)}{opt}{extra}")
    return 0


if __name__ == "__main__":
    if len(sys.argv) < 5:
        print(__doc__.splitlines()[2], file=sys.stderr)
        sys.exit(64)
    sys.exit(main(*sys.argv[1:]))
