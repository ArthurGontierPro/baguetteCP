#!/bin/bash
# M7-T28 (D-0151 section 1): regular's reasons on the letters, measured. Runs TWO binaries
# (the "before" and the "after") over the same flattened instances, 300 s each with the
# proof on and --stats, and checks every complete answer's proof with veripb. Records per
# run: status, wall, nodes, conflicts, learned clauses and their width histogram, the
# checker's verdict. On fataepyc-06, detached by the caller.
#
# Usage: meas_reasons.sh <list.tsv: id model data> <before.exe> <after.exe> <mznlib-checkout> <out>
# Env: PAR (10), LIMIT (300), MZN, CORPUS (/scratch/arthur/mznc)
set -u
LST=$1; BEFORE=$2; AFTER=$3; SRC=$4; OUT=$5
PAR=${PAR:-10}; LIMIT=${LIMIT:-300}
CORPUS=${CORPUS:-/scratch/arthur/mznc}
MZN=${MZN:-/scratch/arthur/mzn/MiniZincIDE-2.10.1-x86_64-linux-gnu/bin/minizinc}
VERIPB=${VERIPB:-$HOME/.cargo/bin/veripb}
mkdir -p "$OUT/fzn" "$OUT/runs"
md5sum "$BEFORE" "$AFTER" > "$OUT/binaries.md5"
export MZN_SOLVER_PATH=$SRC/tools

one() {
  id=$1; model=$2; data=$3
  fzn=$OUT/fzn/$id.fzn
  if [ ! -s "$fzn" ]; then
    args=("$CORPUS/$model")
    [ "$data" != "<none>" ] && [ -n "$data" ] && args+=("$CORPUS/$data")
    timeout 1200 "$MZN" -c --solver baguette "${args[@]}" -o "$fzn" > "$OUT/fzn/$id.flat.err" 2>&1 \
      || { printf "%s\tflatten-fail\n" "$id" >> "$OUT/flatten-fail.tsv"; return; }
  fi
  sense=sat; grep -q '^solve .*\(minimize\|maximize\)' "$fzn" && sense=opt
  for tag in before after; do
    bin=$BEFORE; [ $tag = after ] && bin=$AFTER
    L=$OUT/runs/$id.$tag
    t0=$(date +%s.%N)
    (
      ulimit -v 16777216 -f 16000000
      exec timeout -k 30 $((LIMIT + 60)) "$bin" --max-heap-mb 8192 --stats \
        --time-limit "$LIMIT" --proof "$L" "$fzn"
    ) > "$L.out" 2> "$L.err"
    rc=$?
    t1=$(date +%s.%N)
    wall=$(echo "$t1 - $t0" | bc)
    if grep -q '^=====UNSATISFIABLE=====' "$L.out"; then st=UNSAT
    elif grep -q '^==========' "$L.out"; then st=OPT
    elif grep -q '^----------' "$L.out" && [ $sense = sat ] && ! grep -q '^limit:' "$L.err"; then st=SAT
    elif grep -q '^----------' "$L.out"; then st=INCUMBENT
    elif grep -q '^limit:' "$L.err"; then st=TIMEOUT
    else st=ERROR-rc$rc
    fi
    num() { grep -m1 "^stats: $1 " "$L.err" | awk '{print $3}'; }
    width=$(grep -m1 '^stats: width ' "$L.err" | awk '{print $3}')
    verdict=-
    case $st in
      SAT | UNSAT | OPT)
        if [ $rc -eq 0 ] && [ -s "$L.pbp" ]; then
          v=$( (ulimit -v 64000000; timeout 3600 "$VERIPB" "$L.opb" "$L.pbp") 2>&1 | tail -3)
          case "$v" in
            *"s VERIFIED"*) verdict=VERIFIED ;;
            *) verdict="REJECTED:$(printf '%s' "$v" | tr '\n\t' '  ' | cut -c1-120)" ;;
          esac
        else verdict=NOT-CHECKED; fi ;;
    esac
    printf "%s\t%s\t%s\t%.1f\t%s\t%s\t%s\t%s\t%s\n" "$id" "$tag" "$st" "$wall" \
      "$(num nodes)" "$(num conflicts)" "$(num learned)" "${width:--}" "$verdict" \
      >> "$OUT/results.tsv"
    rm -f "$L.pbp" "$L.opb" "$L.pbp".* "$L.opb".*
  done
}
export -f one
export OUT BEFORE AFTER LIMIT CORPUS MZN VERIPB
grep -v '^#' "$LST" | cut -f1-3 | xargs -P "$PAR" -L 1 bash -c 'one "$0" "$1" "$2"'
echo "DONE $(date -Is)" > "$OUT/DONE"
