#!/bin/bash
# M7-T28 (D-0151): several binaries over the same instances, each on the .fzn its OWN
# checkout's mznlib flattens (so a new route is measured against the decomposition it
# replaces; two tags with the same checkout flatten once), 300 s each with the proof on and
# --stats, every complete answer's proof checked with veripb. meas_reasons.sh is the
# two-binary, one-flattening case of this. Records per run: status, wall, nodes, conflicts,
# learned clauses and their width histogram, the verdict, the incumbent at the limit.
# On fataepyc-06, detached by the caller.
#
# Usage: meas_pair.sh <list.tsv: id model data> <out> <tag>=<exe>@<checkout> ...
# Env: PAR (10), LIMIT (300), MZN, CORPUS (/scratch/arthur/mznc)
set -u
LST=$1; OUT=$2; shift 2
SPECS="$*"
PAR=${PAR:-10}; LIMIT=${LIMIT:-300}
CORPUS=${CORPUS:-/scratch/arthur/mznc}
MZN=${MZN:-/scratch/arthur/mzn/MiniZincIDE-2.10.1-x86_64-linux-gnu/bin/minizinc}
VERIPB=${VERIPB:-$HOME/.cargo/bin/veripb}
mkdir -p "$OUT/runs"
for spec in $SPECS; do
  tag=${spec%%=*}; rest=${spec#*=}; exe=${rest%%@*}; src=${rest#*@}
  echo "$tag $(md5sum < "$exe" | cut -c1-8) $(git -C "$src" log --oneline -1 | cut -c1-80)" >> "$OUT/binaries.txt"
done

one() {
  id=$1; model=$2; data=$3
  for spec in $SPECS; do
    tag=${spec%%=*}; rest=${spec#*=}; bin=${rest%%@*}; src=${rest#*@}
    flat=$OUT/fzn/$(echo "$src" | md5sum | cut -c1-8)
    mkdir -p "$flat"
    fzn=$flat/$id.fzn
    if [ ! -s "$fzn" ]; then
      args=("$CORPUS/$model")
      [ "$data" != "<none>" ] && [ -n "$data" ] && args+=("$CORPUS/$data")
      if ! MZN_SOLVER_PATH=$src/tools timeout 1200 "$MZN" -c --solver baguette "${args[@]}" \
        -o "$fzn" > "$flat/$id.flat.err" 2>&1; then
        printf "%s\t%s\tFLATTEN-FAIL\t-\t-\t-\t-\t-\t-\n" "$id" "$tag" >> "$OUT/results.tsv"
        continue
      fi
    fi
    sense=sat; grep -q '^solve .*\(minimize\|maximize\)' "$fzn" && sense=opt
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
    inc=$(grep -m1 '^limit:' "$L.err" | sed -n 's/.* incumbent=\([^ ]*\).*/\1/p')
    printf "%s\t%s\t%s\t%.1f\t%s\t%s\t%s\t%s\t%s\t%s\n" "$id" "$tag" "$st" "$wall" \
      "$(num nodes)" "$(num conflicts)" "$(num learned)" "${width:--}" "$verdict" "${inc:--}" \
      >> "$OUT/results.tsv"
    rm -f "$L.pbp" "$L.opb" "$L.pbp".* "$L.opb".*
  done
}
export -f one
export OUT SPECS LIMIT CORPUS MZN VERIPB
grep -v '^#' "$LST" | cut -f1-3 | xargs -P "$PAR" -L 1 bash -c 'one "$0" "$1" "$2"'
echo "DONE $(date -Is)" > "$OUT/DONE"
