#!/bin/bash
# M7-T28 (D-0159): gen_rows_probe.py's probes against both row forms, VeriPB 3.0.2 on
# fataepyc-06. Prints one verdict line per (form, probe).
# Usage: bash probe_rows.sh [outdir]
set -u
here="$(cd "$(dirname "$0")" && pwd)"
out="${1:-$here/out-rows}"
mkdir -p "$out"
python3 -I "$here/gen_rows_probe.py" "$out" || exit 1
VERIPB="${VERIPB:-$HOME/.cargo/bin/veripb}"
while read -r opb n orid; do
  for p in $(ls "$out"/q*.pbp | grep -v '\.opb\.' | sort -V); do
    b=$(basename "$p" .pbp)
    sed -e "s/@F@/$n/" -e "s/@OR@/$orid/" "$p" > "$out/$opb.$b.pbp"
    msg=$("$VERIPB" "$out/$opb" "$out/$opb.$b.pbp" 2>&1)
    rc=$?
    echo "== ${opb%.opb} $b rc=$rc :: $(echo "$msg" | grep -E -i 'verif|error|reverse|falsif|contradict|implied' | head -2 | tr '\n' ' ')"
  done
done < "$out/ids"
