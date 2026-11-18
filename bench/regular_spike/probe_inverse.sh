#!/bin/bash
# M7-T28 (D-0146 section 7): the checker probes for the `inverse` design, run on
# fataepyc-06 against VeriPB 3.0.2 (d5644ca4) before any inverse code exists.
# Usage: bash probe_inverse.sh [outdir]
set -u
here="$(cd "$(dirname "$0")" && pwd)"
out="${1:-$here/out-inverse}"
mkdir -p "$out"
python3 -I "$here/gen_inverse_probe.py" "$out"
VERIPB="${VERIPB:-$HOME/.cargo/bin/veripb}"
for p in $(ls "$out"/i*.pbp | sort -V); do
  b=$(basename "$p" .pbp)
  msg=$("$VERIPB" "$out/inv.opb" "$p" 2>&1)
  rc=$?
  echo "== $b rc=$rc :: $(echo "$msg" | grep -E -i 'verif|error|reverse|contradict' | head -3 | tr '\n' ' ')"
done
