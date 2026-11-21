#!/bin/bash
# M4-T6b (D-0194): bounds against GAC arithmetic on ONE instance, INSIDE baguette.
#   bag_pair.sh ID FZN                 (a baguette-flattened .fzn), or
#   bag_pair.sh ID MZN DZN [DPARAMS]   (flattened here through tools/baguette.msc)
# Env: OUT=<run dir>, BIN=<main.exe>, LIMIT_MS=<per arm>, PROOF=1 to write and check the
# proofs (default --no-proof: the proof does not move the search).
# Writes the GAC twin with bag_twin.py (small int_times/int_div/int_abs as a DFA through
# baguette_regular, DOMAIN consistent), runs baguette -s on both arms under a 32G scope,
# and appends one TSV line to $OUT/bag.tsv:
#   id twin arith flags  B_status B_nodes B_fail B_time B_obj  G_status ... G_obj
# status: OPT / UNSAT (search closed), SAT (satisfaction, first solution), LIMIT, ERR.
set -u
ID=$1
OUT=${OUT:?} BIN=${BIN:?} LIMIT_MS=${LIMIT_MS:-300000} PROOF=${PROOF:-0}
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
MB=/scratch/arthur/mzn/MiniZincIDE-2.10.1-x86_64-linux-gnu/bin
D=$OUT/runs/$ID; mkdir -p "$D"
scope() { systemd-run --user --scope -q -p MemoryMax=32G "$@"; }
case "$2" in
  *.fzn) cp "$2" "$D/b.fzn" ;;
  *) if ! scope timeout -k 10 900 "$MB/minizinc" -c --no-output-ozn --solver "$ROOT/tools/baguette.msc" \
          "$2" ${3:+"$3"} ${4:+-D "$4"} -o "$D/b.fzn" > "$D/flat.err" 2>&1; then
       printf '%s\tFLATTEN-FAIL\n' "$ID" >> "$OUT/bag.tsv"; exit 0
     fi ;;
esac
python3 "$HERE/bag_twin.py" "$D/b.fzn" "$D/g.fzn" 64 400000 2> "$D/twin.log"
tw=$(sed -n 's/.*twin=\([0-9]*\).*/\1/p' "$D/twin.log"); ar=$(sed -n 's/.*arith=\([0-9]*\).*/\1/p' "$D/twin.log")
fl=$(sed -n 's/.*flags=\([0-9]*\).*/\1/p' "$D/twin.log")
if [ "${tw:-0}" = 0 ]; then
  printf '%s\t0\t%s\t0\tNOTWIN\n' "$ID" "${ar:-0}" >> "$OUT/bag.tsv"; rm -f "$D/b.fzn" "$D/g.fzn"; exit 0
fi
if [ "${fl:-0}" -gt 3000000 ]; then
  printf '%s\t%s\t%s\t%s\tTOO-BIG\n' "$ID" "$tw" "$ar" "$fl" >> "$OUT/bag.tsv"; rm -f "$D/b.fzn" "$D/g.fzn"; exit 0
fi
arm() {
  local f=$1 tag=$2 st nodes fail tm o pr
  pr=--no-proof; [ "$PROOF" = 1 ] && pr="--proof $D/$tag"
  ( cd "$D" && scope timeout -k 10 $((LIMIT_MS / 1000 + 120)) "$BIN" "$f" $pr -s -t "$LIMIT_MS" \
      > "$D/$tag.out" 2> "$D/$tag.err" )
  if grep -q '^=====UNSATISFIABLE=====' "$D/$tag.out"; then st=UNSAT
  elif grep -q '^==========' "$D/$tag.out"; then st=OPT
  elif ! grep -q "mzn-stat: nodes=" "$D/$tag.out"; then st=ERR
  elif grep -q 'objective=' "$D/$tag.out"; then st=LIMIT
  elif grep -q '^----------' "$D/$tag.out"; then st=SAT
  elif grep -q 'mzn-stat: nodes=' "$D/$tag.out"; then st=LIMIT; else st=ERR; fi
  nodes=$(sed -n 's/^%%%mzn-stat: nodes=//p' "$D/$tag.out" | tail -1)
  fail=$(sed -n 's/^%%%mzn-stat: failures=//p' "$D/$tag.out" | tail -1)
  tm=$(sed -n 's/^%%%mzn-stat: solveTime=//p' "$D/$tag.out" | tail -1)
  o=$(sed -n 's/^%%%mzn-stat: objective=//p' "$D/$tag.out" | tail -1)
  if [ "$PROOF" = 1 ] && [ -s "$D/$tag.pbp" ]; then
    ( . "$ROOT/scripts/checker.sh"; baguette_resolve_veripb && \
      timeout 1200 "$VERIPB" "$D/$tag.opb" "$D/$tag.pbp" ) > "$D/$tag.check" 2>&1
    st="$st/$(grep -o -m1 'VERIFIED[A-Z ]*\|error' "$D/$tag.check" | head -1 | tr ' ' '_')"
  fi
  printf '%s\t%s\t%s\t%s\t%s' "$st" "${nodes:--}" "${fail:--}" "${tm:--}" "${o:--}"
}
b=$(arm "$D/b.fzn" b); g=$(arm "$D/g.fzn" g)
printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$ID" "$tw" "$ar" "$fl" "$b" "$g" >> "$OUT/bag.tsv"
rm -f "$D/b.fzn" "$D/g.fzn" "$D"/*.pbp "$D"/*.opb
