#!/usr/bin/env python3
"""Every solution of a FlatZinc model, by a reference FlatZinc interpreter (Gecode's, or
OR-Tools' CP-SAT). Written for M14-e2e-verification-T2, the first end-to-end lane.

Usage: python3 -I fzn_solutions.py FZN_GECODE MODEL.fzn NAMES WORKDIR [TIMEOUT_S]

FZN_GECODE is the path of `fzn-gecode` or `fzn-cp-sat`; `minizinc` is looked up in the same
directory. WORKDIR is a path PREFIX: the model's copy is written to WORKDIR.allout.fzn (or
.mzn). TIMEOUT_S defaults to 120. Exit 0 when the solutions, or `timeout`, are printed; 1 when
the reference exits non-zero or prints a solution that lacks a variable of NAMES or repeats
one (the reason on stderr); 64 with a usage line on stderr when the argument count is wrong.

The reference half of the translator's test (tools/e2e/scpsem.py is the other half): the
model as MiniZinc's reference CP solver reads it, so neither baguette's front end nor the
translator is involved. Every declared decision variable is made an output (a copy of the
model with `:: output_var` / `:: output_array([1..n])` added where it was missing), then
`fzn-gecode -a` (or `fzn-cp-sat -a`) enumerates. Prints `count N` and one line per solution
over the variables of NAMES (the translator's variables, by FlatZinc name), in scpsem.py's
format; `timeout`
when Gecode did not finish.

baguette's own predicates (the globals of M14-e2e-verification-T5, D-0180, and the far
families of T6, regular and cumulative, D-0195). A .fzn flattened against baguette's mznlib calls
`baguette_global_cardinality`, `baguette_inverse`, `baguette_member(_bool)`, and the test
models call `fzn_global_cardinality` directly; neither reference knows those names as
FlatZinc builtins ("Registry: Constraint ... not found", measured). Such a model is turned
back into MiniZinc instead (FlatZinc is MiniZinc syntax): the predicate declarations are
replaced by the definitions below, `globals.mzn` is included, every decision variable gets
`:: add_to_output`, and `minizinc --solver <gecode|cp-sat> -a --output-mode dzn` flattens it
against the REFERENCE solver's own library and enumerates. The definitions are the
standard library's globals where one exists (inverse over the two index sets), and SPEC
2.1's sentence for member, which has no standard global with selectors. global_cardinality is
its sentence too, each count the number of x equal to its cover value (D-0262): CP-SAT's own
global_cardinality admits NO solution when the cover repeats a value (gcc([1,1], [1,1],
[2,2]), test/models/gcc_low_up_closed_dupcover_src_sat: Gecode and cake's semantics admit
x = [1,1]), which the validation reported as DIFFER against a right translation.
They share nothing with tools/e2e/fzn2scp.py; member's reading of SPEC is the one place the
two are written from the same sentence.

An objective (M14-e2e-verification-T8, D-0182, objectives in the end-to-end chain).
`solve [ann] minimize|maximize ID;` is replaced by `solve satisfy;` so that `-a` enumerates
EVERY solution rather than the improving ones, and the line `objective minimize|maximize ID`
is printed at the end, ID read from the .fzn as the
reference has it: validate.py takes the optimum over the set from it, independently of the
translator's prob_type.
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
        " array [int] of var int: counts) = forall (j in index_set(cover)) (counts[j] ="
        " sum (i in index_set(x)) (bool2int(x[i] = cover[j])));",
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
    # T6 (D-0195): std's cumulative; the DFA run made explicit as states a[0..n], with the state
    # flags PINNED to it (mznlib's sentence: s[i*Q + q] is "after i letters the automaton is in
    # q"), so that each word is one solution and the flags cannot hide a difference
    "baguette_cumulative":
        "predicate baguette_cumulative(array [int] of var int: s, array [int] of int: d,"
        " array [int] of int: r, int: b) = cumulative(s, d, r, b);",
    "baguette_regular":
        "predicate baguette_regular(array [int] of var int: x, int: Q, int: smin,"
        " array [int] of int: d, int: q0, array [int] of int: F, array [int] of var bool: s) ="
        " let { int: n = length(x); int: w = length(d) div Q; array [0..n] of var 1..Q: a;"
        " array [1..n] of var int: xx = array1d(x); array [1..length(d)] of int: dd = array1d(d);"
        " array [1..length(s)] of var bool: ss = array1d(s); } in"
        " a[0] = q0 /\\ exists (f in F) (a[n] = f)"
        " /\\ forall (i in 1..n) (xx[i] >= smin /\\ xx[i] <= smin + w - 1"
        " /\\ dd[(a[i - 1] - 1) * w + xx[i] - smin + 1] = a[i])"
        " /\\ forall (i in 0..n, q in 1..Q) (ss[i * Q + q] <-> a[i] = q);",
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
    objective = None
    m = re.search(r"^\s*solve\b[^;]*?\b(minimize|maximize)\s+([A-Za-z_][A-Za-z0-9_]*)\s*;",
                  text, re.M)
    if m:
        objective = (m.group(1), m.group(2))
        text = text[:m.start()] + "solve satisfy;" + text[m.end():]
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
    if objective:
        print(f"objective {objective[0]} {objective[1]}")
    return 0


if __name__ == "__main__":
    if len(sys.argv) not in (5, 6):
        print("usage: fzn_solutions.py FZN_GECODE MODEL.fzn NAMES WORKDIR [TIMEOUT_S]", file=sys.stderr)
        sys.exit(64)
    sys.exit(main(*sys.argv[1:]))
