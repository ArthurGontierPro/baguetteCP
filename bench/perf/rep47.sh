#!/usr/bin/env bash
# M11-complexity-T1 (D-0140): CYCLES under a shared node are noisy (+-30 % between two runs of
# the same binary at different loads), so a cycles comparison is made in PAIRS run at the
# same time, repeated. usage: rep47.sh INST BUDGET REPS VARIANT...   (no-proof only)
# Each repetition starts every variant at once and waits for all of them.
export PATH=$HOME/.cargo/bin:$HOME/.local/bin:$PATH
R=/scratch/arthur/wave47-inventory-runs; O=$R/rep; mkdir -p $O
inst=$1; nl=$2; reps=$3; shift 3
ulimit -v 32000000
export BAGUETTE_NODE_LIMIT=$nl
for r in $(seq 1 "$reps"); do
  for v in "$@"; do
    if [ "$v" = base ]; then B=$R/main.exe; else B=$R/main-$v.exe; fi
    perf stat -x, -e instructions:u,cycles:u -o $O/${v}_${inst}_${nl}_r$r.perfstat \
      $B --no-proof $R/inst/$inst.fzn > /dev/null 2>&1 &
  done
  wait
done
touch $O/${inst}_${nl}.done
