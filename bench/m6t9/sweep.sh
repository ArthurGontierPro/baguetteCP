#!/usr/bin/env bash
# M6-T9 sweep driver: four configs back to back, each its own OUT, 64 jobs.
export PATH=$HOME/.local/bin:$HOME/.cargo/bin:$PATH
B=/scratch/arthur/perf-frozen/_build/default/bin/main.exe
md5sum "$B"
common() {
  CORPUS=/scratch/arthur/mzn-challenge PAR=64 SOLVE_TIMEOUT=300 RSS=1 \
  MZN=/scratch/arthur/mzn/MiniZincIDE-2.10.1-x86_64-linux-gnu/bin/minizinc \
  VERIPB=$HOME/.cargo/bin/veripb BAGUETTE=$B \
  ONLY=/scratch/arthur/perf-out-lists/sweep.ids \
  SOLVER_ARGS="--time-limit 280 --stats --time" \
  OUT="$1" /scratch/arthur/perf-frozen/scripts/corpus_run.sh > "$1.log" 2>&1
}
for c in a b c d; do mkdir -p /scratch/arthur/perf-out-$c; done
echo "a start $(date)"; common /scratch/arthur/perf-out-a
echo "b start $(date)"; NO_PROOF=1 common /scratch/arthur/perf-out-b
echo "c start $(date)"; BAGUETTE_RETENTION=lbd:16 common /scratch/arthur/perf-out-c
echo "d start $(date)"; BAGUETTE_PB_ANALYSIS=off common /scratch/arthur/perf-out-d
echo "all done $(date)"
