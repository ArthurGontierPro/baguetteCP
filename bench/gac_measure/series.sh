#!/bin/bash
# M4-T6b (D-0194): the three measurements of the record, as they were run on fataepyc-06.
#   series.sh census  RUN           root census over every flattened Challenge .fzn that
#                                   posts int_times/int_div/int_abs (census.py)
#   series.sh gecode  RUN LIST      bounds against GAC in Gecode, one line per instance of
#                                   LIST (id, mzn, dzn [, -D params]) (gecode_pair.sh)
#   series.sh bag     RUN LIST BIN  bounds against GAC inside baguette, LIST lines (id, fzn)
#                                   or (id, mzn, dzn [, -D params]) (bag_pair.sh)
# At most 8 runs at a time (two Challenge series share the node), every solver run under a
# 32G systemd scope (in the pair scripts), the launcher's PID in RUN/pid. Kill by that PID
# and its children only, never by name.
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
FLAT=${FLAT:-/scratch/arthur/m8t4/flat}
P=${P:-8}
mode=$1 RUN=$2; mkdir -p "$RUN"; echo $$ > "$RUN/pid"
pairs() {  # $1 = pair script; reads LIST, one instance per line, tab-separated
  tr '\t' '\037' < "$LIST" | xargs -P "$P" -I{} -d '\n' \
    bash -c 'IFS=$'"'"'\037'"'"' read -r a b c d <<< "$1"; '"$1"' "$a" "$b" "$c" "$d"' _ {}
}
case "$mode" in
  census)
    grep -l 'constraint int_\(times\|div\|abs\)(' "$FLAT"/*/work/*.fzn > "$RUN/files.lst"
    mkdir -p "$RUN/parts"
    xargs -P "$P" -n 1 sh -c 'b=$(basename "$1" .baguette.fzn); timeout 1800 python3 '"$HERE"'/census.py "$1" > '"$RUN"'/parts/$b.tsv' _ < "$RUN/files.lst"
    { head -1 "$(ls "$RUN"/parts/*.tsv | head -1)"; for f in "$RUN"/parts/*.tsv; do tail -n +2 "$f"; done; } > "$RUN/census.tsv" ;;
  gecode)
    LIST=$3; export OUT=$RUN LIMIT_MS=${LIMIT_MS:-150000}; pairs "$HERE/gecode_pair.sh" ;;
  bag)
    LIST=$3; export OUT=$RUN BIN=$4 LIMIT_MS=${LIMIT_MS:-240000}; md5sum "$BIN" > "$RUN/binary.md5"
    pairs "$HERE/bag_pair.sh" ;;
  *) echo "usage: series.sh census|gecode|bag RUN [LIST [BIN]]" >&2; exit 2 ;;
esac
echo done > "$RUN/done"
