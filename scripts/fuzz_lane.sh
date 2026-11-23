#!/bin/bash
# The differential fuzz lane (M22-review-T7, docs/reports/2026-11-23-code-review.md 1.4).
#
# Random small models through MiniZinc, baguette against Gecode (tools/fuzz/fuzz.py and
# fuzz2.py): every baguette proof is checked by VeriPB, every baguette solution is re-checked
# by Gecode, and every disagreement is kept with its model, proof and both outputs. It found
# M22-review-T2 within its first 150 models. NOT a gate: a disagreement becomes a regression
# model in test/models/ and a fix.
#
# RUN IT ON A NODE, NEVER ON THE LAPTOP (scripts/README.md section 1).
#
#   scripts/fuzz_lane.sh [-j N] [-n MODELS] [--seed S] [--bin BINARY] OUTDIR
#
#   -j N        parallel jobs, at most 16 (default 16; the node rules of scripts/README.md 3)
#   -n MODELS   models per stream (default 100), split over the jobs
#   --seed S    base seed (default 1); a run is a function of the seed and the binary
#   --bin B     the solver under test (default: this clone's _build/default/bin/main.exe)
#
# The six streams: default; `-f --bits-above none`; larger models (FUZZ_NMAX=10,
# FUZZ_CMAX=12); then fuzz2's search-heavy models (3-SAT near the threshold, small
# integer optimisation) under default, `-f` and `--bits-above none`. Each solver call
# runs under `ulimit -v 4000000` and a timeout (fuzz.py). MiniZinc is taken from PATH, or
# from the node's bundle (bench/challenge/README.md) when it is not on PATH.
#
# Exit status: 0 when every model agreed, 1 when a disagreement was kept, 2 on a usage
# or setup error. Summary in OUTDIR/summary.txt, disagreements in OUTDIR/*/bad/.
set -u
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
JOBS=16
N=100
SEED=1
BIN="${ROOT}/_build/default/bin/main.exe"
OUT=""
die() { echo "fuzz_lane: $*" >&2; exit 2; }
while [ $# -gt 0 ]; do
  case "$1" in
    -j) JOBS="${2:?}"; shift 2 ;;
    -n) N="${2:?}"; shift 2 ;;
    --seed) SEED="${2:?}"; shift 2 ;;
    --bin) BIN="${2:?}"; shift 2 ;;
    -*) die "unknown option $1" ;;
    *) OUT="$1"; shift ;;
  esac
done
[ -n "$OUT" ] || die "usage: fuzz_lane.sh [-j N] [-n MODELS] [--seed S] [--bin BINARY] OUTDIR"
[ "$JOBS" -ge 1 ] && [ "$JOBS" -le 16 ] || die "-j must be between 1 and 16"
[ -x "$BIN" ] || die "no solver at $BIN (build it first: dune build bin/main.exe)"
export PATH="$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
if ! command -v minizinc >/dev/null 2>&1; then
  MZN="${MZN_BIN:-/scratch/arthur/mzn/MiniZincIDE-2.10.1-x86_64-linux-gnu/bin}"
  [ -x "$MZN/minizinc" ] || die "minizinc is not on PATH and not in $MZN"
  export PATH="$MZN:$PATH"
fi
[ -x "$HOME/.cargo/bin/veripb" ] || die "no checker at \$HOME/.cargo/bin/veripb"
export FUZZ_BIN="$BIN"
mkdir -p "$OUT"
OUT="$(cd "$OUT" && pwd)"

# One job = one chunk of one stream: "<dir> <script> <seed> <models> <env> <flags...>".
CHUNKS=$(( JOBS < 2 ? 1 : JOBS / 2 ))
PER=$(( (N + CHUNKS - 1) / CHUNKS ))
plan="$OUT/plan.txt"; : > "$plan"
IDX=0
stream() { # name script env flags; seeds: SEED*1000 + stream*100 + chunk
  local name="$1" script="$2" env="$3"; shift 3
  IDX=$((IDX + 1))
  for k in $(seq 0 $((CHUNKS - 1))); do
    echo "$OUT/$name-$k $script $((SEED * 1000 + IDX * 100 + k)) $PER $env${*:+ $*}" >> "$plan"
  done
}
stream default fuzz.py -
stream free-order fuzz.py - -f --bits-above none
stream larger fuzz.py FUZZ_NMAX=10,FUZZ_CMAX=12
stream search fuzz2.py -
stream search-free fuzz2.py - -f
stream search-order fuzz2.py - --bits-above none

# One plan line per call. The line is split here, not by xargs: `xargs -L 1` joins a line
# that ends in a blank with the next one, which ran two chunks as one with the second's
# fields as solver flags (found on this script's first run, 2026-11-23).
run_chunk() {
  local -a f envs=()
  read -r -a f <<< "$1"
  local dir="${f[0]}" script="${f[1]}" seed="${f[2]}" n="${f[3]}" env="${f[4]}"
  local -a flags=("${f[@]:5}")
  [ "$env" != "-" ] && IFS=',' read -r -a envs <<< "$env"
  env "${envs[@]+"${envs[@]}"}" python3 -I "$ROOT/tools/fuzz/$script" "$dir" "$seed" "$n" \
    "${flags[@]+"${flags[@]}"}" > "$dir.log" 2>&1
}
export -f run_chunk
export ROOT
start=$(date +%s)
xargs -d '\n' -n 1 -P "$JOBS" bash -c 'run_chunk "$1"' _ < "$plan"
secs=$(( $(date +%s) - start ))

bad=$(find "$OUT" -mindepth 3 -maxdepth 3 -path '*/bad/*' -type d | sort)
nbad=$(printf '%s' "$bad" | grep -c . || true)
{
  echo "fuzz_lane: binary $BIN ($(md5sum "$BIN" | cut -c1-8)), seed $SEED, $N models per stream, -j $JOBS, ${secs}s"
  for log in "$OUT"/*.log; do echo "$(basename "$log" .log): $(tail -1 "$log")"; done
  echo "disagreements: $nbad"
  [ -n "$bad" ] && echo "$bad"
} > "$OUT/summary.txt"
cat "$OUT/summary.txt"
[ "$nbad" -eq 0 ]
