#!/bin/bash
# M4-T6b (D-0194): bounds against GAC arithmetic on ONE instance, with Gecode as the
# search engine and the model's own search annotations.
#   gecode_pair.sh ID MZN DZN [DPARAMS]       (OUT=<run dir>, LIMIT_MS=<per arm>)
# Flattens with Gecode's library (plus baguette's compat shims), marks the objective as an
# output variable, writes the GAC twin with gac_rewrite.py (small int_times/div/mod/abs as
# gecode_table_int), runs fzn-gecode -a -s on both arms under a 32G scope, and appends one
# TSV line to $OUT/gecode.tsv:
#   id tabulated arith  B_status B_nodes B_fail B_time B_obj B_nsol  G_status ... G_nsol
# status: OPT (optimum proved), SAT (satisfaction: first solution found), UNSAT, LIMIT
# (time limit first), ERR. Satisfaction problems run for one solution, optimisation with -a.
set -u
ID=$1 MZN=$2 DZN=$3 DP=${4:-}
OUT=${OUT:?} LIMIT_MS=${LIMIT_MS:-150000}
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
MB=/scratch/arthur/mzn/MiniZincIDE-2.10.1-x86_64-linux-gnu/bin
D=$OUT/runs/$ID; mkdir -p "$D"
scope() { systemd-run --user --scope -q -p MemoryMax=32G "$@"; }
if ! scope timeout -k 10 900 "$MB/minizinc" -c --no-output-ozn --solver gecode "$MZN" \
     "$ROOT/mznlib/compat_mzn1.mzn" ${DZN:+"$DZN"} ${DP:+-D "$DP"} -o "$D/b.fzn" > "$D/flat.err" 2>&1; then
  printf '%s\tFLATTEN-FAIL\n' "$ID" >> "$OUT/gecode.tsv"; exit 0
fi
obj=$(grep -E '^solve ' "$D/b.fzn" | grep -o -E '(minimize|maximize) +[A-Za-z_][A-Za-z0-9_]* *;' | awk '{print $2}' | tr -d ';')
if [ -n "$obj" ]; then
  sed -i -E "/^var [^:]*: *$obj( |;|::)/{/output_var/!s/;\s*\$/ :: output_var;/}" "$D/b.fzn"
fi
# STATIC=1: a model with no search annotation gets Gecode's default branching, which is
# DYNAMIC (it reads the propagators' failure counts), so a stronger propagator changes the
# branching as well as the pruning. STATIC=1 replaces `solve satisfy;` by an input-order,
# min-value search over every integer variable no constraint defines, the same in both arms.
if [ "${STATIC:-0}" = 1 ] && grep -q '^solve *satisfy;' "$D/b.fzn"; then
  vs=$(grep -E '^var -?[0-9]+\.\.-?[0-9]+: *[A-Za-z]' "$D/b.fzn" | grep -v 'is_defined_var' \
       | sed -E 's/^var [^:]*: *([A-Za-z0-9_]+).*/\1/' | paste -sd, -)
  [ -n "$vs" ] && sed -i "s/^solve *satisfy;/solve :: int_search([$vs],input_order,indomain_min,complete) satisfy;/" "$D/b.fzn"
fi
python3 "$HERE/gac_rewrite.py" "$D/b.fzn" "$D/g.fzn" 64 2> "$D/rewrite.log"
tab=$(sed -n 's/.*tabulated=\([0-9]*\).*/\1/p' "$D/rewrite.log"); ar=$(sed -n 's/.*arith=\([0-9]*\).*/\1/p' "$D/rewrite.log")
if [ "${tab:-0}" = 0 ]; then
  printf '%s\t0\t%s\tNOTAB\n' "$ID" "${ar:-0}" >> "$OUT/gecode.tsv"; rm -f "$D/g.fzn"; exit 0
fi
arm() {
  local f=$1 log=$2 st nodes fail tm o ns
  scope timeout -k 10 $((LIMIT_MS / 1000 + 120)) "$MB/fzn-gecode" ${obj:+-a} -s -time "$LIMIT_MS" "$f" > "$log" 2>&1
  if grep -q '^=====UNSATISFIABLE=====' "$log"; then st=UNSAT
  elif grep -q '^==========' "$log"; then st=OPT
  elif [ -z "$obj" ] && grep -q '^----------' "$log"; then st=SAT
  elif grep -q 'mzn-stat: nodes=' "$log"; then st=LIMIT; else st=ERR; fi
  nodes=$(sed -n 's/^%%%mzn-stat: nodes=//p' "$log" | tail -1)
  fail=$(sed -n 's/^%%%mzn-stat: failures=//p' "$log" | tail -1)
  tm=$(sed -n 's/^%%%mzn-stat: solveTime=//p' "$log" | tail -1)
  ns=$(grep -c '^----------' "$log")
  o=-; [ -n "$obj" ] && o=$(sed -n "s/^$obj = \(-\?[0-9]*\);/\1/p" "$log" | tail -1)
  printf '%s\t%s\t%s\t%s\t%s\t%s' "$st" "${nodes:--}" "${fail:--}" "${tm:--}" "${o:--}" "$ns"
}
b=$(arm "$D/b.fzn" "$D/b.log"); g=$(arm "$D/g.fzn" "$D/g.log")
printf '%s\t%s\t%s\t%s\t%s\n' "$ID" "$tab" "$ar" "$b" "$g" >> "$OUT/gecode.tsv"
gzip -f "$D/b.fzn" "$D/g.fzn" 2>/dev/null
