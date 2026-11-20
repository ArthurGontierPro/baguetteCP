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
"""
import re
import subprocess
import sys

DECL = re.compile(r"^(\s*var\s+[^:=;]+:\s*)([A-Za-z_][A-Za-z0-9_]*)([^=;]*);\s*$")
ADECL = re.compile(r"^(\s*array\s*\[\s*1\s*\.\.\s*(\d+)\s*\]\s*of\s+var\s+[^:=;]+:\s*)"
                   r"([A-Za-z_][A-Za-z0-9_]*)([^=;]*);\s*$")


def main(gecode, fzn, names, work, timeout=120):
    want = {l.split()[1] for l in open(names) if l.strip()}
    out = []
    for line in open(fzn).read().splitlines():
        m = ADECL.match(line)
        if m and "output_array" not in m.group(4):
            line = f"{m.group(1)}{m.group(3)}{m.group(4)} :: output_array([1..{m.group(2)}]);"
        else:
            m = DECL.match(line)
            if m and "output_var" not in m.group(3):
                line = f"{m.group(1)}{m.group(2)}{m.group(3)} :: output_var;"
        out.append(line)
    copy = f"{work}.allout.fzn"
    open(copy, "w").write("\n".join(out) + "\n")
    try:
        r = subprocess.run([gecode, "-a", copy], capture_output=True, text=True,
                           timeout=float(timeout))
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
        m = re.fullmatch(r"(\S+) = array1d\(1\.\.\d+, \[(.*)\]\);", l)
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
