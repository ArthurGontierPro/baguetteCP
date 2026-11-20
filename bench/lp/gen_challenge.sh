#!/bin/bash
# gen_challenge.sh SEL.tsv OUT [PAR] -- flatten each selected Challenge instance with tools/baguette.msc
# and let the release binary write its .opb at --time-limit 0 (M13-codes-leads-T1, D-0183).
# SEL.tsv: instance id (YEAR_family_instance) in column 1; the model and data come from
# /scratch/arthur/m7t26/YEAR/all.lst. At most PAR (default 8) at once, each under a 32G scope and
# a 900 s timeout per step. OUT/pid holds this launcher's PID.
set -u
SEL=${1:?SEL}; OUT=${2:?OUT}; PAR=${3:-8}
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../.." && pwd)
MZN=${MZN:-/scratch/arthur/mzn/MiniZincIDE-2.10.1-x86_64-linux-gnu/bin/minizinc}
BAG=${BAGUETTE:-$ROOT/_build_release/default/bin/main.exe}
mkdir -p "$OUT"; echo $$ > "$OUT/pid"
one() {
  local id=$1 y=${1%%_*} line m d
  line=$(awk -F'\t' -v id="$id" '$2==id' "/scratch/arthur/m7t26/$y/all.lst")
  m=$(echo "$line" | cut -f1); d=$(echo "$line" | cut -f3)
  [ "$d" = "<none>" ] && d="" || d="/scratch/arthur/mznc/$d"
  systemd-run --user --scope -q -p MemoryMax=32G timeout 900 \
    "$MZN" -c --solver "$ROOT/tools/baguette.msc" "$m" $d -o "$OUT/$id.fzn" > "$OUT/$id.flat.log" 2>&1
  echo "flatten rc=$?" >> "$OUT/$id.flat.log"
  [ -s "$OUT/$id.fzn" ] || return
  systemd-run --user --scope -q -p MemoryMax=32G timeout 900 \
    "$BAG" --proof "$OUT/$id" --time-limit 0 "$OUT/$id.fzn" > "$OUT/$id.bag.log" 2>&1
  echo "baguette rc=$?" >> "$OUT/$id.bag.log"
  rm -f "$OUT/$id.pbp"
}
export -f one; export MZN BAG ROOT OUT
while IFS=$'\t' read -r id _; do
  while [ "$(jobs -rp | wc -l)" -ge "$PAR" ]; do wait -n; done
  one "$id" &
done < <(grep -v '^#' "$SEL")
wait
touch "$OUT/done"
