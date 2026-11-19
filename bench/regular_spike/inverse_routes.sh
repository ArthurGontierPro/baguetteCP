#!/bin/bash
# M7-T28 (D-0151 section 2): which Challenge instances REACH `baguette_inverse` once
# flattened with a checkout's mznlib (the selection reads model sources, which D-0146
# section 6 found can disagree with the flattened model), and how big each call is.
# Flattens each listed instance, KEEPS the .fzn under <out>/fzn for the measurement, and
# prints: id, baguette_inverse calls, the longest f array, all_different_int calls, status.
# Usage: inverse_routes.sh <checkout> <instances.lst> <corpus-root> <out> [par]  (on the node)
set -u
SRC=$1; LST=$2; ROOT=$3; OUT=$4; PAR=${5:-8}
MZN=${MZN:-/scratch/arthur/mzn/MiniZincIDE-2.10.1-x86_64-linux-gnu/bin/minizinc}
export MZN_SOLVER_PATH=$SRC/tools
mkdir -p "$OUT/fzn"
one() {
  id=$1; model=$2; data=$3
  out=$OUT/fzn/$id.fzn
  args=("$ROOT/$model")
  [ "$data" != "<none>" ] && [ -n "$data" ] && args+=("$ROOT/$data")
  if timeout 1200 $MZN -c --solver baguette "${args[@]}" -o "$out" > "$OUT/fzn/$id.err" 2>&1; then
    # the first argument is a literal [..] or the name of an array declared 1..N
    longest=$(python3 -I -c '
import re, sys
text = open(sys.argv[1]).read()
decl = {m.group(2): int(m.group(1)) for m in re.finditer(r"^array \[1\.\.(\d+)\] of var [^:]*: (\w+)", text, re.M)}
best = 0
for m in re.finditer(r"^constraint baguette_inverse\((\[[^]]*\]|\w+),", text, re.M):
    a = m.group(1)
    n = len(a.strip("[]").split(",")) if a.startswith("[") else decl.get(a, 0)
    best = max(best, n)
print(best)' "$out")
    printf "%s\t%d\t%d\t%d\tOK\n" "$id" "$(grep -c '^constraint baguette_inverse(' "$out")" \
      "$longest" "$(grep -c '^constraint all_different_int(' "$out")"
  else
    printf "%s\t-\t-\t-\tFLATTEN-FAIL\n" "$id"
  fi
}
export -f one; export OUT MZN ROOT SRC
grep -v '^#' "$LST" | cut -f1-3 | xargs -P "$PAR" -L 1 bash -c 'one "$0" "$1" "$2"'
