#!/bin/bash
# M7-T28 (D-0159), on fataepyc-06: the search side of the member measurement, without the
# proof. For each listed instance, flatten with main's mznlib (std's decomposition) and run
# main's binary, and run the branch's binary on the branch's flattening (member_routes.sh's
# fzn), both --no-proof --stats for <secs> seconds; print the stats lines that count nodes.
# Usage: meas_stats.sh <main-checkout> <branch-checkout> <routes-fzn-dir> <corpus> <lst> <secs> <out>
set -u
MAIN=$1; BR=$2; RF=$3; ROOT=$4; LST=$5; SECS=$6; OUT=$7
MZN=${MZN:-/scratch/arthur/mzn/MiniZincIDE-2.10.1-x86_64-linux-gnu/bin/minizinc}
mkdir -p "$OUT"
one() {
  id=$1; model=$2; data=$3
  args=("$ROOT/$model"); [ "$data" != "<none>" ] && args+=("$ROOT/$data")
  MZN_SOLVER_PATH=$MAIN/tools timeout 1200 $MZN -c --solver baguette "${args[@]}" -o "$OUT/$id.main.fzn" > /dev/null 2>&1
  for side in main branch; do
    if [ $side = main ]; then B=$MAIN/_build/default/bin/main.exe; F=$OUT/$id.main.fzn
    else B=$BR/_build/default/bin/main.exe; F=$RF/$id.fzn; fi
    ( ulimit -v 16000000; /usr/bin/time -f "peak_rss %M kB" timeout $((SECS + 60)) "$B" --no-proof --stats --time-limit "$SECS" "$F" ) > "$OUT/$id.$side.out" 2> "$OUT/$id.$side.err"
  done
}
export -f one; export OUT MZN ROOT MAIN BR RF SECS
grep -v '^#' "$LST" | cut -f1-3 | xargs -P 6 -L 1 bash -c 'one "$0" "$1" "$2"'
