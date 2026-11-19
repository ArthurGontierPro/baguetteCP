#!/bin/bash
# M7-T28 (D-0151 section 3): the checker probes for a `member` design, run on fataepyc-06
# against VeriPB 3.0.2 before any member code exists. gen_member_probe.py states each probe.
# Usage: bash probe_member.sh [outdir]
set -u
here="$(cd "$(dirname "$0")" && pwd)"
out="${1:-$here/out-member}"
mkdir -p "$out"
python3 -I "$here/gen_member_probe.py" "$out"
VERIPB="${VERIPB:-$HOME/.cargo/bin/veripb}"
for p in $(ls "$out"/m*.pbp | sort -V); do
  b=$(basename "$p" .pbp)
  msg=$("$VERIPB" "$out/mem.opb" "$p" 2>&1)
  rc=$?
  echo "== $b rc=$rc :: $(echo "$msg" | grep -E -i 'verif|error|reverse|falsif|contradict' | head -2 | tr '\n' ' ')"
done
