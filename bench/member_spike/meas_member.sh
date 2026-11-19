#!/bin/bash
# M7-T28 (D-0159), on fataepyc-06: a FROZEN clone of <branch> at its current head, built,
# then compare_run.sh over the Challenge instances that reach `baguette_member` once
# flattened (member_routes.sh), 300 s with proof, baguette only, <par>-way. Each side
# flattens with ITS OWN mznlib: "before" is main, where member is std's decomposition.
# Usage: meas_member.sh <tag> <branch> <instances.lst> [par]   (detached by the caller)
set -u
export PATH=$HOME/.cargo/bin:$HOME/.local/bin:$PATH
eval "$(opam env --switch=baguette)"
TAG=$1; BRANCH=$2; LST=$3; PAR=${4:-12}
SRC=/scratch/arthur/wave53-member-meas-src-$TAG
OUT=/scratch/arthur/wave53-member-meas-$TAG
rm -rf "$SRC" "$OUT"
git clone -q -b "$BRANCH" /scratch/arthur/baguette.git "$SRC" || exit 1
mkdir -p "$OUT"
git -C "$SRC" log --oneline -1 > "$OUT/head.txt"
(cd "$SRC" && dune build --root . bin/ 2>&1 | tail -5) || exit 1
md5sum "$SRC/_build/default/bin/main.exe" > "$OUT/binary.md5"
export INSTANCES=$LST
export SOLVERS=baguette PAR SOLVE_TIMEOUT=300 MEM_KB=16777216 PROOF_CAP_KB=16000000
export CHECK_TIMEOUT=3600 FLATTEN_TIMEOUT=1200 COMPAT=1
export MZN=/scratch/arthur/mzn/MiniZincIDE-2.10.1-x86_64-linux-gnu/bin/minizinc
export CHUFFED=/scratch/arthur/mzn/MiniZincIDE-2.10.1-x86_64-linux-gnu/bin/fzn-chuffed
export GCS=/scratch/arthur/gcs/build/fzn-glasgow
export BAGUETTE=$SRC/_build/default/bin/main.exe
cd "$SRC" && ./scripts/compare_run.sh /scratch/arthur/mznc "$OUT"
echo "DONE $(date -Is)" > "$OUT/DONE"
