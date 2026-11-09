#!/bin/bash
# diag.sh -- time one `pol` operator kind at a time (see diag_pol.py). NODE ONLY.
#   diag.sh <run-out-dir> [widths] [variants]     reads <run-out-dir>/w<w>/order/pol/model.opb
set -u
OUT=${1:?usage: diag.sh <run-out-dir> [widths] [variants]}
WIDTHS=${2:-100000,1000000}
VARIANTS=${3:-weaken,sum,fold,foldT}
VERIPB=${VERIPB:-$HOME/.cargo/bin/veripb}
HERE=$(cd "$(dirname "$0")" && pwd)
ulimit -v 16777216
mkdir -p "$OUT/diag"
printf 'width\tvariant\tops\tpbp_bytes\trc\tveripb_self_s\twall_s\trss_kb\n' > "$OUT/diag/results.tsv"
for w in ${WIDTHS//,/ }; do
  for v in ${VARIANTS//,/ }; do
    d="$OUT/w$w/order/pol"
    read -r _ bytes ops < <(python3 -I "$HERE/diag_pol.py" "$d" "$w" "$v")
    ( cd "$d" && timeout 7200 /usr/bin/time -f '%e %M' -o "$OUT/diag/$w-$v.time" \
        "$VERIPB" --stats model.opb "diag-$v.pbp" > "$OUT/diag/$w-$v.out" 2> "$OUT/diag/$w-$v.err" )
    rc=$?
    self=$(awk '/time total/{print $(NF-1)}' "$OUT/diag/$w-$v.out")
    read -r wall rss < "$OUT/diag/$w-$v.time"
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$w" "$v" "$ops" "$bytes" "$rc" "${self:--}" "$wall" "$rss" | tee -a "$OUT/diag/results.tsv"
  done
done
echo "done: $(date -Is)"
