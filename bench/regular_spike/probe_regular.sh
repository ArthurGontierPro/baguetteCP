#!/bin/bash
# M7-T28 (D-0146): the hand-built checker probes for `regular`, run on fataepyc-06 against
# VeriPB 3.0.2 (d5644ca4) before any solver code was written. gen_probe.py's docstring states
# the instance and each probe's intent; the verdicts are recorded in D-0146.
# Usage: bash probe_regular.sh [outdir]   (writes m.opb and p*.pbp there, runs veripb on each)
set -u
here="$(cd "$(dirname "$0")" && pwd)"
out="${1:-$here/out}"
mkdir -p "$out"
python3 -I "$here/gen_probe.py" "$out"
VERIPB="${VERIPB:-$HOME/.cargo/bin/veripb}"
for p in $(ls "$out"/p*.pbp | sort -V); do
  b=$(basename "$p" .pbp)
  msg=$("$VERIPB" "$out/m.opb" "$p" 2>&1)
  rc=$?
  echo "== $b rc=$rc :: $(echo "$msg" | grep -E -i 'verif|error|reverse|contradict|solution|warning|fail' | head -4 | tr '\n' ' ')"
done
