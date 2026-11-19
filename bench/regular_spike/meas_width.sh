#!/bin/bash
# M7-T28 (D-0151 section 1): the LEARNED-CLAUSE WIDTHS of several binaries on the same .fzn.
# The stock --stats histogram stops at a ">= 16" bucket, which is where nearly every
# nonogram clause lands, so the binaries are built with that bucket widened to 4096 (a
# two-line edit of lib/core/search.ml's [width_hist] in throwaway clones, nothing else: the
# search is the committed one) and run without the proof, LIMIT s each. Prints per run the
# status, wall, nodes, learned clauses and their width mean / median / p90.
# Usage: meas_width.sh <list.tsv> <fzn-dir> <out> <tag>=<exe> ...   (on the node)
set -u
LST=$1; FZN=$2; OUT=$3; shift 3
SPECS="$*"
PAR=${PAR:-3}; LIMIT=${LIMIT:-120}
mkdir -p "$OUT/runs"
for spec in $SPECS; do echo "${spec%%=*} $(md5sum < "${spec#*=}" | cut -c1-8)" >> "$OUT/binaries.txt"; done
one() {
  id=$1
  [ -s "$FZN/$id.fzn" ] || return
  for spec in $SPECS; do
    tag=${spec%%=*}; bin=${spec#*=}
    L=$OUT/runs/$id.$tag
    t0=$(date +%s.%N)
    ( ulimit -v 16777216; exec timeout -k 30 $((LIMIT + 60)) "$bin" --max-heap-mb 8192 --stats \
      --no-proof --time-limit "$LIMIT" "$FZN/$id.fzn" ) > "$L.out" 2> "$L.err"
    wall=$(echo "$(date +%s.%N) - $t0" | bc)
    if grep -q '^=====UNSATISFIABLE=====' "$L.out"; then st=UNSAT
    elif grep -q '^==========' "$L.out"; then st=OPT
    elif grep -q '^----------' "$L.out" && ! grep -q '^limit:' "$L.err"; then st=SAT
    elif grep -q '^----------' "$L.out"; then st=INCUMBENT
    else st=NONE; fi
    nodes=$(grep -m1 '^stats: nodes ' "$L.err" | awk '{print $3}')
    hist=$(grep -m1 '^stats: width ' "$L.err" | awk '{print $3}')
    w=$(python3 -I -c '
import sys
h = sys.argv[1]
ws = []
if ":" in h:
    for p in h.split(","):
        a, b = p.split(":"); ws += [int(a)] * int(b)
ws.sort(); n = len(ws)
print("%d\t%.1f\t%d\t%d" % (n, sum(ws) / n, ws[n // 2], ws[9 * n // 10]) if n else "0\t-\t-\t-")' "$hist")
    printf "%s\t%s\t%s\t%.1f\t%s\t%s\n" "$id" "$tag" "$st" "$wall" "${nodes:-0}" "$w" >> "$OUT/widths.tsv"
  done
}
export -f one; export OUT FZN LIMIT SPECS
grep -v '^#' "$LST" | cut -f1 | xargs -P "$PAR" -L 1 bash -c 'one "$0"'
echo "DONE $(date -Is)" > "$OUT/DONE"
