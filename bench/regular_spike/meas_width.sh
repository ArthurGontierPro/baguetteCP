#!/bin/bash
# M7-T28 (D-0151 section 1): the LEARNED-CLAUSE WIDTHS before/after regular's letter reasons.
# The stock --stats histogram stops at a ">= 16" bucket, which is where nearly every
# nonogram clause lands, so this runs two binaries built with that bucket widened to 4096
# (a two-line edit of lib/core/search.ml's [width_hist] in throwaway clones, nothing else:
# the search is the committed one) without the proof, LIMIT s each, and prints per run the
# status, nodes, learned clauses and their width mean / median / p90.
# Usage: meas_width.sh <list.tsv> <before.exe> <after.exe> <fzn-dir> <out>   (on the node)
set -u
LST=$1; BEFORE=$2; AFTER=$3; FZN=$4; OUT=$5
PAR=${PAR:-3}; LIMIT=${LIMIT:-120}
mkdir -p "$OUT/runs"
md5sum "$BEFORE" "$AFTER" > "$OUT/binaries.md5"
one() {
  id=$1
  [ -s "$FZN/$id.fzn" ] || return
  for tag in before after; do
    bin=$BEFORE; [ $tag = after ] && bin=$AFTER
    L=$OUT/runs/$id.$tag
    ( ulimit -v 16777216; exec timeout -k 30 $((LIMIT + 60)) "$bin" --max-heap-mb 8192 --stats \
      --no-proof --time-limit "$LIMIT" "$FZN/$id.fzn" ) > "$L.out" 2> "$L.err"
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
    printf "%s\t%s\t%s\t%s\t%s\n" "$id" "$tag" "$st" "${nodes:-0}" "$w" >> "$OUT/widths.tsv"
  done
}
export -f one; export OUT BEFORE AFTER FZN LIMIT
grep -v '^#' "$LST" | cut -f1 | xargs -P "$PAR" -L 1 bash -c 'one "$0"'
echo "DONE $(date -Is)" > "$OUT/DONE"
