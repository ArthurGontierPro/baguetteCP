#!/usr/bin/env bash
# M6-T9 config e: frozen2 (pb fix) + the proposed justify memo patch, harness from frozen2.
export PATH=$HOME/.local/bin:$HOME/.cargo/bin:$PATH
until grep -q "all done" /scratch/arthur/perf-bin/sweep2.driver.log; do sleep 30; done
B=/scratch/arthur/perf-frozen3/_build/default/bin/main.exe
md5sum "$B"
mkdir -p /scratch/arthur/perf-out-e
echo "e start $(date)"
CORPUS=/scratch/arthur/mzn-challenge PAR=64 SOLVE_TIMEOUT=300 RSS=1 \
  MZN=/scratch/arthur/mzn/MiniZincIDE-2.10.1-x86_64-linux-gnu/bin/minizinc \
  VERIPB=$HOME/.cargo/bin/veripb BAGUETTE=$B \
  ONLY=/scratch/arthur/perf-out-lists/sweep.ids \
  SOLVER_ARGS="--time-limit 280 --stats --time" \
  OUT=/scratch/arthur/perf-out-e /scratch/arthur/perf-frozen2/scripts/corpus_run.sh > /scratch/arthur/perf-out-e.log 2>&1
echo "e done $(date)"
