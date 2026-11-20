#!/usr/bin/env python3
"""Every solution of a FlatZinc model, by Gecode's FlatZinc interpreter (M14-e2e-verification-T2).

Usage: python3 -I fzn_solutions.py FZN_GECODE MODEL.fzn NAMES WORKDIR [TIMEOUT_S]

The reference half of the translator's test (tools/e2e/scpsem.py is the other half): the
model as MiniZinc's reference CP solver reads it, so neither baguette's front end nor the
translator is involved. Every declared decision variable is made an output (a copy of the
model with `:: output_var` / `:: output_array([1..n])` added where it was missing), then
`fzn-gecode -a` enumerates. Prints `count N` and one line per solution over the variables
of NAMES (the translator's variables, by FlatZinc name), in scpsem.py's format; `timeout`
when Gecode did not finish.

baguette's own predicates (T5, D-0180). A .fzn flattened against baguette's mznlib calls
`baguette_global_cardinality`, `baguette_inverse`, `baguette_member(_bool)`, and the test
models call `fzn_global_cardinality` directly; neither reference knows those names as
FlatZinc builtins ("Registry: Constraint ... not found", measured). Such a model is turned
back into MiniZinc instead (FlatZinc is MiniZinc syntax): the predicate declarations are
replaced by the definitions below, `globals.mzn` is included, every decision variable gets
`:: add_to_output`, and `minizinc --solver <gecode|cp-sat> -a --output-mode dzn` flattens it
against the REFERENCE solver's own library and enumerates. The definitions are the
standard library's globals where one exists (global_cardinality, inverse over the two index
sets), and SPEC 2.1's sentence for member, which has no standard global with selectors.
They share nothing with tools/e2e/fzn2scp.py; member's reading of SPEC is the one place the
two are written from the same sentence.
"""
import re
import subprocess
import sys

DECL = re.compile(r"^(\s*var\s+[^:=;]+:\s*)([A-Za-z_][A-Za-z0-9_]*)([^=;]*);\s*$")
ADECL = re.compile(r"^(\s*array\s*\[\s*1\s*\.\.\s*(\d+)\s*\]\s*of\s+var\s+[^:=;]+:\s*)"
                   r"([A-Za-z_][A-Za-z0-9_]*)([^=;]*);\s*$")


REFERENCE = {
    "baguette_global_cardinality":
        "predicate baguette_global_cardinality(array [int] of var int: x, array [int] of int: cover,"
        " array [int] of var int: counts) = global_cardinality(x, cover, counts);",
    "baguette_inverse":
        "predicate baguette_inverse(array [int] of var int: f, int: fmin, array [int] of var int: g,"
        " int: gmin) = inverse(array1d(fmin..fmin + length(f) - 1, f),"
        " array1d(gmin..gmin + length(g) - 1, g));",
    "baguette_member":
        "predicate baguette_member(array [int] of var int: x, var int: y, array [int] of var bool: b)"
        " = exists(b) /\\ forall (k in index_set(b)) (b[k] -> x[k] = y);",
    "baguette_member_bool":
        "predicate baguette_member_bool(array [int] of var bool: x, var bool: y,"
        " array [int] of var bool: b) = exists(b) /\\ forall (k in index_set(b)) (b[k] -> x[k] = y);",
}
NOT_BUILTIN = set(REFERENCE) | {"fzn_global_cardinality"}


def as_minizinc(text):
    """The .fzn as a MiniZinc model the reference flattens itself (see the header)."""
    out = ['include "globals.mzn";'] + [REFERENCE[n] for n in REFERENCE if n + "(" in text]
    for line in text.splitlines():
        if re.match(r"\s*predicate\s+(baguette_\w+|fzn_global_cardinality)\s*\(", line):
            continue
        out.append(line)
    return "\n".join(out) + "\n"


def main(gecode, fzn, names, work, timeout=120):
    want = {l.split()[1] for l in open(names) if l.strip()}
    text = open(fzn).read()
    mzn = any(re.search(rf"\bconstraint\s+{n}\s*\(", text) for n in NOT_BUILTIN)
    out = []
    for line in text.splitlines():
        m = ADECL.match(line)
        if m and mzn:
            line = f"{m.group(1)}{m.group(3)}{m.group(4)} :: add_to_output;"
        elif m and "output_array" not in m.group(4):
            line = f"{m.group(1)}{m.group(3)}{m.group(4)} :: output_array([1..{m.group(2)}]);"
        else:
            m = DECL.match(line)
            if m and mzn:
                line = f"{m.group(1)}{m.group(2)}{m.group(3)} :: add_to_output;"
            elif m and "output_var" not in m.group(3):
                line = f"{m.group(1)}{m.group(2)}{m.group(3)} :: output_var;"
        out.append(line)
    if mzn:
        copy = f"{work}.allout.mzn"
        open(copy, "w").write(as_minizinc("\n".join(out)))
        solver = {"fzn-gecode": "gecode", "fzn-cp-sat": "cp-sat"}[gecode.rsplit("/", 1)[-1]]
        cmd = [gecode.rsplit("/", 1)[0] + "/minizinc", "--solver", solver, "-a",
               "--output-mode", "dzn", copy]
    else:
        copy = f"{work}.allout.fzn"
        open(copy, "w").write("\n".join(out) + "\n")
        cmd = [gecode, "-a", copy]
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=float(timeout))
    except subprocess.TimeoutExpired:
        print("timeout")
        return 0
    if r.returncode != 0:
        print(f"{gecode.rsplit('/', 1)[-1]} exited {r.returncode}: {r.stderr.strip()[:200]}", file=sys.stderr)
        return 1
    sols, cur = [], {}
    for l in r.stdout.splitlines():
        l = l.strip()
        if l == "----------":
            sols.append(cur)
            cur = {}
            continue
        m = (re.fullmatch(r"(\S+) = array1d\(1\.\.\d+, ?\[(.*)\]\);", l)
             or re.fullmatch(r"(\S+) = \[(.*)\];", l))
        if m:
            for i, v in enumerate(m.group(2).split(","), 1):
                cur[f"{m.group(1)}[{i}]"] = v.strip()
            continue
        m = re.fullmatch(r"(\S+) = (\S+);", l)
        if m:
            cur[m.group(1)] = m.group(2)
    conv = {"true": "1", "false": "0"}
    lines = set()
    for s in sols:
        missing = want - set(s)
        if missing:
            print(f"gecode printed no value for {sorted(missing)[:3]}", file=sys.stderr)
            return 1
        lines.add(" ".join(f"{n}={conv.get(s[n], s[n])}" for n in sorted(want)))
    if len(lines) != len(sols):
        print(f"gecode printed {len(sols)} solutions, {len(lines)} distinct", file=sys.stderr)
        return 1
    print(f"count {len(lines)}")
    print("\n".join(sorted(lines)))
    return 0


if __name__ == "__main__":
    if len(sys.argv) not in (5, 6):
        print("usage: fzn_solutions.py FZN_GECODE MODEL.fzn NAMES WORKDIR [TIMEOUT_S]", file=sys.stderr)
        sys.exit(64)
    sys.exit(main(*sys.argv[1:]))
