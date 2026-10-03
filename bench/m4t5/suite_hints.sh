#!/bin/bash
# M4-T5 / D-0102. Per suite model: solve with the BUILT bin/main.exe, let veripb
# ELABORATE the proof (its output carries the checker's own RUP trail as hints), splice
# those hints back into the solver's proof (splice_hints.py), and time veripb on the
# unhinted and the hinted proof, minimum of 3. Measurement only, never a gate.
# Output: model  pbp_bytes  rup_lines  unhinted_s  hinted_s  splice-summary
ROOT=${ROOT:-$(cd "$(dirname "$0")/../.." && pwd)}; OUT=${OUT:-/tmp/m4t5-suite}; mkdir -p "$OUT"
ulimit -v 4000000
VP=$HOME/.cargo/bin/veripb; B=$ROOT/_build/default/bin/main.exe; cd "$OUT"
t() { local best=999; for i in 1 2 3; do s=$(date +%s.%N); $VP $1 $2 >/dev/null 2>&1 || { echo FAIL; return; }; e=$(date +%s.%N); x=$(echo "$e - $s" | bc); best=$(echo "if ($x < $best) $x else $best" | bc); done; echo $best; }
for fzn in $ROOT/test/models/*.fzn; do m=$(basename $fzn .fzn)
  timeout 60 $B $fzn --proof $m >/dev/null 2>&1 || true
  [ -s $m.pbp ] || { echo -e "$m\tNOPROOF"; continue; }
  nr=$(grep -c '^\(@[^ ]* \)\?rup ' $m.pbp)
  $VP $m.opb $m.pbp -e $m.elab.pbp >/dev/null 2>&1 || { echo -e "$m\tELABFAIL"; continue; }
  rm -f $m.h.pbp; sp=$(python3 $ROOT/bench/m4t5/splice_hints.py $m.pbp $m.elab.pbp $m.h.pbp 2>&1 | tail -1)
  u=$(t $m.opb $m.pbp); h=$(t $m.opb $m.h.pbp)
  echo -e "$m\t$(stat -c%s $m.pbp)\t$nr\t$u\t$h\t$sp"
done
