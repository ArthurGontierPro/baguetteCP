#!/bin/bash
# The differential fuzz lane (M22-review-T7, docs/reports/2026-11-23-code-review.md 1.4; the
# second-generation streams are D-0258).
#
# Random small models through MiniZinc, baguette against Gecode: every baguette proof is checked
# by VeriPB, every baguette solution is re-checked by Gecode, and every disagreement is kept
# with its model, proof and both outputs. It found M22-review-T2 within its first 150 models.
# NOT a gate: a disagreement becomes a model in bench/fuzz/found/ and a fix, and the fixed
# model a regression model in test/models/.
#
# RUN IT ON A NODE, NEVER ON THE LAPTOP (scripts/README.md section 1).
#
#   scripts/fuzz_lane.sh [-j N] [-n MODELS] [--seed S] [--bin BINARY] [--streams LIST]
#                        [--mznlib DIR] OUTDIR
#
#   -j N         parallel jobs, at most 16 (default 16; the node rules of scripts/README.md 3)
#   -n MODELS    models per stream (default 100), split over the jobs
#   --seed S     base seed (default 1); a run is a function of the seed, the binary and mznlib
#   --bin B      the solver under test (default: this clone's _build/default/bin/main.exe)
#   --streams L  a comma-separated subset of the stream names below (default: all twelve)
#   --mznlib D   flatten the new streams with this mznlib/ (default: this clone's); how the
#                globals stream's acceptance test runs the mznlib of 99d0e39~1
#
# The streams (bench/fuzz/README.md has each one's model space and acceptance test):
#   tools/fuzz/fuzz.py and fuzz2.py, the first six (2026-11-23):
#     default       fuzz.py, the default flags
#     free-order    fuzz.py, `-f --bits-above none`
#     larger        fuzz.py, FUZZ_NMAX=10 FUZZ_CMAX=12
#     search        fuzz2.py (3-SAT near the threshold, small integer optimisation), default
#     search-free   fuzz2.py, `-f`
#     search-order  fuzz2.py, `--bits-above none`
#   tools/fuzz/streams.py, the six of D-0258, which flatten once and run baguette on the .fzn;
#   besides the status, objective, proof and solution, they check that VeriPB's conclusion is
#   the one the run printed (PROOF-CONCLUSION):
#     globals   the global constraints in all their forms, covers that repeat a value, repeated
#               variables, constants, empty and one-element arrays. Acceptance: with the mznlib
#               of 99d0e39~1 it finds the wrong UNSAT of D-0255
#     configs   one model under 18 search configurations (--cdcl, --chrono 5, -f,
#               BAGUETTE_MINIMISE=rec, BAGUETTE_PRIORITY=classes, BAGUETTE_PROBE=root, and the
#               retention policies keep_all, fifo:1, lbd:1 and tiered forced to evict at every
#               learned constraint, each under dfs and --cdcl); all agree with Gecode and with
#               each other. Acceptance: before D-0257 it finds a REJECTED proof under --cdcl
#     incr      -i: each printed objective improves, the last equals the plain run's optimum
#     limit     BAGUETTE_NODE_LIMIT and -t cut runs: no optimality or UNSAT claimed, the partial
#               proof VERIFIED for what it says (NO CONCLUSION, or BOUNDS around the optimum)
#     e2e       the builtins cake_pb_cp covers, tools/e2e/chain.sh bridged and E2E_SOLVER=1
#     wide      domains wider than 2^20, front end only: answer or refuse, never crash or
#               leave the memory cap
# Each solver call runs under `ulimit -v 4000000` and a timeout (fuzz.py, streams.py). MiniZinc
# is taken from PATH, or from the node's bundle (bench/challenge/README.md) when it is not on PATH.
#
# Exit status: 0 when every model agreed, 1 when a disagreement was kept (OUTDIR/*/bad/), 2 on a
# usage or setup error. Timeouts (baguette's or VeriPB's) are kept in OUTDIR/*/slow/ and do not
# make the status 1. Summary in OUTDIR/summary.txt.
set -u
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
JOBS=16
N=100
SEED=1
BIN="${ROOT}/_build/default/bin/main.exe"
OUT=""
STREAMS=""
MZNLIB=""
ALL="default free-order larger search search-free search-order globals configs incr limit e2e wide"
die() { echo "fuzz_lane: $*" >&2; exit 2; }
while [ $# -gt 0 ]; do
  case "$1" in
    -j) JOBS="${2:?}"; shift 2 ;;
    -n) N="${2:?}"; shift 2 ;;
    --seed) SEED="${2:?}"; shift 2 ;;
    --bin) BIN="${2:?}"; shift 2 ;;
    --streams) STREAMS="${2:?}"; shift 2 ;;
    --mznlib) MZNLIB="${2:?}"; shift 2 ;;
    -*) die "unknown option $1" ;;
    *) OUT="$1"; shift ;;
  esac
done
[ -n "$OUT" ] || die "usage: fuzz_lane.sh [-j N] [-n MODELS] [--seed S] [--bin BINARY] [--streams LIST] [--mznlib DIR] OUTDIR"
STREAMS="${STREAMS:-${ALL// /,}}"
for s in ${STREAMS//,/ }; do
  case " $ALL " in *" $s "*) ;; *) die "unknown stream $s (the streams: $ALL)" ;; esac
done
if [ -n "$MZNLIB" ]; then
  [ -d "$MZNLIB" ] || die "no mznlib directory at $MZNLIB"
  export FUZZ_MZNLIB="$(cd "$MZNLIB" && pwd)"
fi
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
  case ",$STREAMS," in *",$name,"*) ;; *) return ;; esac
  for k in $(seq 0 $((CHUNKS - 1))); do
    echo "$OUT/$name-$k $script $((SEED * 1000 + IDX * 100 + k)) $PER $env${*:+ $*}" >> "$plan"
  done
}
stream default fuzz.py -
stream free-order fuzz.py - -f --bits-above none
stream larger fuzz.py 'FUZZ_NMAX=10;FUZZ_CMAX=12'
stream search fuzz2.py -
stream search-free fuzz2.py - -f
stream search-order fuzz2.py - --bits-above none
# D-0258's six: the script field is streams.py:<stream>, whose own argument comes first. The env
# field separates its assignments with `;` (a retention policy's own parameters contain commas).
for s in globals configs incr limit e2e wide; do stream "$s" "streams.py:$s" -; done

# One plan line per call. The line is split here, not by xargs: `xargs -L 1` joins a line
# that ends in a blank with the next one, which ran two chunks as one with the second's
# fields as solver flags (found on this script's first run, 2026-11-23).
run_chunk() {
  local -a f envs=()
  read -r -a f <<< "$1"
  local dir="${f[0]}" script="${f[1]}" seed="${f[2]}" n="${f[3]}" env="${f[4]}"
  local -a flags=("${f[@]:5}")
  local -a pre=()
  [ "$env" != "-" ] && IFS=';' read -r -a envs <<< "$env"
  case "$script" in streams.py:*) pre=("${script#streams.py:}"); script=streams.py ;; esac
  env "${envs[@]+"${envs[@]}"}" python3 -I "$ROOT/tools/fuzz/$script" "${pre[@]+"${pre[@]}"}" \
    "$dir" "$seed" "$n" "${flags[@]+"${flags[@]}"}" > "$dir.log" 2>&1
}
export -f run_chunk
export ROOT
[ -s "$plan" ] || die "no stream selected"
start=$(date +%s)
xargs -d '\n' -n 1 -P "$JOBS" bash -c 'run_chunk "$1"' _ < "$plan"
secs=$(( $(date +%s) - start ))

bad=$(find "$OUT" -mindepth 3 -maxdepth 3 -path '*/bad/*' -type d | sort)
nbad=$(printf '%s' "$bad" | grep -c . || true)
nslow=$(find "$OUT" -mindepth 3 -maxdepth 3 -path '*/slow/*' -type d | grep -c . || true)
{
  echo "fuzz_lane: binary $BIN ($(md5sum "$BIN" | cut -c1-8)), mznlib ${FUZZ_MZNLIB:-$ROOT/mznlib}, seed $SEED, $N models per stream, -j $JOBS, ${secs}s"
  for log in "$OUT"/*.log; do echo "$(basename "$log" .log): $(tail -1 "$log")"; done
  echo "timeouts kept in slow/: $nslow"
  echo "disagreements: $nbad"
  [ -n "$bad" ] && echo "$bad"
} > "$OUT/summary.txt"
cat "$OUT/summary.txt"
[ "$nbad" -eq 0 ]
