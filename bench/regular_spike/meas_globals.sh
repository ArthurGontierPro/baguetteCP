#!/bin/bash
# On fataepyc-06: a FROZEN clone of wave49-globals at its current head, built, then
# compare_run.sh over the selected Challenge instances (regular, gcc_closed,
# community-detection) at 300 s with proof, baguette only, 10-way. Detached by the caller.
set -u
export PATH=$HOME/.cargo/bin:$HOME/.local/bin:$PATH
eval "$(opam env --switch=baguette)"
TAG=${1:-after}
SRC=/scratch/arthur/wave49-globals-meas-src-$TAG
OUT=/scratch/arthur/wave49-globals-meas-$TAG
rm -rf $SRC
git clone -q -b wave49-globals /scratch/arthur/baguette.git $SRC || exit 1
cd $SRC && git log --oneline -1 > $OUT.head 2>/dev/null || true
mkdir -p $OUT
git -C $SRC log --oneline -1 > $OUT/head.txt
(cd $SRC && dune build --root . bin/ 2>&1 | tail -5) || exit 1
md5sum $SRC/_build/default/bin/main.exe > $OUT/binary.md5
export INSTANCES=/scratch/arthur/wave49-globals-inst.lst
export SOLVERS=baguette PAR=10 SOLVE_TIMEOUT=300 MEM_KB=16777216 PROOF_CAP_KB=16000000
export CHECK_TIMEOUT=3600 FLATTEN_TIMEOUT=1200 COMPAT=1
export MZN=/scratch/arthur/mzn/MiniZincIDE-2.10.1-x86_64-linux-gnu/bin/minizinc
export CHUFFED=/scratch/arthur/mzn/MiniZincIDE-2.10.1-x86_64-linux-gnu/bin/fzn-chuffed
export GCS=/scratch/arthur/gcs/build/fzn-glasgow
export BAGUETTE=$SRC/_build/default/bin/main.exe
cd $SRC && ./scripts/compare_run.sh /scratch/arthur/mznc $OUT
echo "DONE $(date -Is)" > $OUT/DONE
