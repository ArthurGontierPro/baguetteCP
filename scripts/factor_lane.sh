#!/usr/bin/env bash
# M17-bench-series-T6 (D-0256). THE PER-NODE FACTOR LANE: how many times the instructions of a
# reference solver does baguette spend per search node, on the same instance and, where it can
# be had, the same tree?
#
# D-0207 built this measurement once by hand (five families, baguette against Gecode and
# Chuffed, /cluster/arthur/baguette-results/pernode2/). This lane repeats its core at every
# series, so that the factor is a number with a history and not a one-off.
#
# INPUTS. bench/factor/plan.tsv (one line per instance: family, baguette's node budget, the
# reference solver and its budget, the two flattenings) and the files of bench/factor/fzn/.
#
# WHAT IS RUN, per instance:
#   baguette in four configurations, each twice (a BASE run stopped at one node by
#   BAGUETTE_NODE_LIMIT=1, and the measured run at the plan's budget):
#     pf    default, --proof            np    default, --no-proof
#     cdpf  --cdcl, --proof             cdnp  --cdcl, --no-proof
#   the reference, twice as well (gecode: -node 1, then -node N or none; chuffed-nolazy:
#   -t 1, then -t N or none).
# Every run is `perf stat -e instructions:u` under `systemd-run --user --scope -p
# MemoryMax=32G` (when systemd-run works), `ulimit -v $BAGUETTE_MEM_CAP_KB` and a timeout,
# with every BAGUETTE_* variable of the caller's environment unset.
#
# THE MEASURE. Cost per unit = (I - I_base) / (U - U_base), I the instructions, U the nodes or
# the failures, so that parsing, compiling and writing the .opb are out (D-0207 section 1).
# The unit is the NODE when the two trees are the same, i.e. baguette's node count and
# failure count are both within 2 % of the reference's; otherwise the FAILURE, on each solver's
# own tree, and the table says so (`unit` and `tree`). The --cdcl rows are always per failure:
# the CDCL loop counts an implied right branch as no node, as Chuffed's LCG does.
# factor = baguette's cost per unit / the reference's. Per family, the geometric mean of the
# factors of its instances, per configuration.
#
# Instructions retired in user mode are a property of the binary and its input, not of the
# node's load (scaling_lane.sh measured 0.05 % between two whole runs at load 50), so this lane
# runs on a loaded node. It cannot see a cost bound by memory rather than work (D-0207 section 7).
#
# PROOFS. Every proof the lane writes, base runs included, is checked by the checker
# scripts/checker.sh resolves (the one verify_proof.sh uses), its `s VERIFIED ...` line kept
# in the table, and then deleted. A proof cut at a node budget concludes NONE and checks as
# `s VERIFIED NO CONCLUSION`: every line before the cut is still checked.
#
# OUTPUTS, in OUTDIR (default: a new directory under ${TMPDIR:-/tmp}, printed, and kept):
#   factor.tsv     one line per (instance, configuration): counts, costs, unit, tree, factor,
#                  answer, the checker's verdict
#   factor.txt     the readable table, also printed: per instance, per family (geometric mean),
#                  then the comparison with the recorded reference and the HISTORY row
#   runs/          per run: out, err, perf.txt, rc (the proofs are gone)
#   lane.pid       this script's PID while it runs; every run writes its own runs/<run>/pid
# `--record` also writes bench/factor/reference.tsv (factor.tsv with a header naming the binary,
# the commit, the host and the date), refused if a run broke or with --only. A proof that was not
# verified does not stop the record (its counts were measured, its verdict is in the file), and
# the lane still exits 1.
# Without --record, each line is compared with the recorded reference AS INFORMATION.
#
# NOT A GATE. A factor that moves never fails the lane. EXIT STATUS:
#   0  every run finished and every proof was VERIFIED
#   1  a run crashed, timed out or printed no count; a proof was rejected or not checked; no
#      checker was found (a missing checker is a failure, never a skip)
#   2  usage, or a missing tool: the solver binary, perf, fzn-gecode or fzn-chuffed
#
#   scripts/factor_lane.sh [-j N] [--bin PATH] [--record] [--only ID[,ID...]] [OUTDIR]
#
# Environment: FACTOR_PAR (default 8 runs at once), FACTOR_TIMEOUT (default 900 s per run),
# FACTOR_CHECK_CAP_KB (ulimit -v for the checker, default 33554432: veripb died at 4 GB on
# jr63's --cdcl proof, 2.3 GB, as on openshop in the diff lane), BIN (the solver, default _build_release/default/bin/main.exe: D-0207 measured the release
# build, `make release`; `make factor` builds it), MZN_BIN (the MiniZinc 2.10.1 bundle's bin/,
# for fzn-gecode and fzn-chuffed), BAGUETTE_MEM_CAP_KB (ulimit -v per run, default 4000000),
# VERIPB (as checker.sh). On fataepyc-06 it takes 6.5 to 8 minutes at -j 8 (D-0256),
# most of it the longest chain: jr63 with --cdcl and proof, then the check of its 2.3 GB proof.
set -u
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
FD="$ROOT/bench/factor"
BIN="${BIN:-$ROOT/_build_release/default/bin/main.exe}"
MZN_BIN="${MZN_BIN:-/scratch/arthur/mzn/MiniZincIDE-2.10.1-x86_64-linux-gnu/bin}"
PAR="${FACTOR_PAR:-8}"
TMO="${FACTOR_TIMEOUT:-900}"
CAP_KB="${BAGUETTE_MEM_CAP_KB:-4000000}"
CHECK_CAP_KB="${FACTOR_CHECK_CAP_KB:-33554432}"
RECORD=0
ONLY=""
OUT=""

die() { echo "factor_lane: $*" >&2; exit 2; }
usage() { sed -n '2,/^set -u/p' "$0" | sed '$d' | sed 's/^# \{0,1\}//'; exit 2; }
while [ $# -gt 0 ]; do
  case "$1" in
    --record) RECORD=1 ;;
    -j) [ $# -ge 2 ] || usage; PAR="$2"; shift ;;
    --bin) [ $# -ge 2 ] || usage; BIN="$2"; shift ;;
    --only) [ $# -ge 2 ] || usage; ONLY="$2"; shift ;;
    -h|--help) usage ;;
    -*) die "unknown argument $1 (try --help)" ;;
    *) [ -z "$OUT" ] || die "one OUTDIR only"; OUT="$1" ;;
  esac
  shift
done
[ "$RECORD" = 0 ] || [ -z "$ONLY" ] || die "--record measures the whole plan; drop --only"
[ -x "$BIN" ] || die "no solver at $BIN (build it first: make release)"
BIN="$(cd "$(dirname "$BIN")" && pwd)/$(basename "$BIN")"
[ -x "$MZN_BIN/fzn-gecode" ] || die "no fzn-gecode in $MZN_BIN (set MZN_BIN)"
[ -x "$MZN_BIN/fzn-chuffed" ] || die "no fzn-chuffed in $MZN_BIN (set MZN_BIN)"
PERF="${PERF:-$(command -v perf 2>/dev/null || true)}"
[ -n "$PERF" ] && "$PERF" stat -x, -e instructions:u true 2>&1 | grep -q '^[0-9]' ||
  die "perf cannot count instructions:u here (${PERF:-not installed}; perf_event_paranoid is \
$(cat /proc/sys/kernel/perf_event_paranoid 2>/dev/null || echo '?')). This lane has no fallback."
# shellcheck source=checker.sh
. "$ROOT/scripts/checker.sh"
if ! baguette_resolve_veripb; then
  echo "factor_lane: FAIL -- no checker, so no proof could be checked." >&2
  baguette_veripb_diagnostic
  exit 1
fi
SR=()
if systemd-run --user --scope -q -p MemoryMax=32G true >/dev/null 2>&1; then
  SR=(systemd-run --user --scope -q -p MemoryMax=32G)
else
  echo "factor_lane: systemd-run --user --scope does not work here; runs are capped by ulimit only"
fi
case "$CAP_KB" in none|unlimited|0) CAPCMD=":" ;; *) CAPCMD="ulimit -v $CAP_KB" ;; esac
case "$CHECK_CAP_KB" in none|unlimited|0) CHECK_CAPCMD=":" ;; *) CHECK_CAPCMD="ulimit -v $CHECK_CAP_KB" ;; esac

[ -n "$OUT" ] || OUT="$(mktemp -d "${TMPDIR:-/tmp}/factor_lane.XXXXXX")"
mkdir -p "$OUT/runs" || die "cannot create $OUT"
OUT="$(cd "$OUT" && pwd)"
echo $$ > "$OUT/lane.pid"
MD5="$(md5sum < "$BIN" | cut -d' ' -f1)"
COMMIT="$(git -C "$ROOT" rev-parse --short HEAD 2>/dev/null || echo unknown)"
HOST="$(hostname -s)"
echo "factor_lane: solver $BIN md5 $MD5 (commit $COMMIT), $PAR at once, output in $OUT"
echo "factor_lane: load $(cut -d' ' -f1-3 /proc/loadavg), checker $VERIPB"

# One measured process: run_cmd DIR ENV... -- CMD...  ->  DIR/{out,err,perf.txt,rc,pid}
run_cmd() {
  local d="$1"; shift
  local -a envs=()
  while [ "$1" != -- ]; do envs+=("$1"); shift; done
  shift
  mkdir -p "$d"
  (
    cd "$d" || exit 1
    for v in $(compgen -e | grep '^BAGUETTE_'); do unset "$v"; done
    $CAPCMD
    exec env "${envs[@]}" "${SR[@]}" timeout -k 10 "$TMO" \
      "$PERF" stat -x, -e instructions:u -o perf.txt "$@" > out 2> err
  ) &
  echo $! > "$d/pid"
  wait $!
  echo $? > "$d/rc"
  rm -f "$d/pid"
}

# The checker on DIR/p.opb + DIR/p.pbp -> DIR/verdict ("s VERIFIED ..." or REJECTED/MISSING), then
# the proof is deleted whatever the verdict.
check_proof() {
  local d="$1" v
  if [ ! -s "$d/p.opb" ] || [ ! -s "$d/p.pbp" ]; then
    echo MISSING > "$d/verdict"
  else
    ( $CHECK_CAPCMD; exec "${SR[@]}" timeout -k 10 "$TMO" "$VERIPB" "$d/p.opb" "$d/p.pbp" ) > "$d/veripb.out" 2>&1
    local vrc=$?
    v="$(grep -m1 '^s VERIFIED' "$d/veripb.out")"
    if [ "$vrc" = 0 ] && [ -n "$v" ]; then echo "$v" > "$d/verdict"; else echo "REJECTED (rc $vrc)" > "$d/verdict"; fi
    ls -l "$d/p.pbp" | awk '{print $5}' > "$d/pbpsize"
  fi
  rm -f "$d/p.opb" "$d/p.pbp"
}

fzn_of() { # gz-or-plain file in bench/factor/fzn -> a plain copy in $OUT/fzn
  local f="$1" o="$OUT/fzn/${1%.gz}"
  mkdir -p "$OUT/fzn"
  if [ ! -f "$o" ]; then
    case "$f" in *.gz) gzip -dc "$FD/fzn/$f" > "$o" ;; *) cp "$FD/fzn/$f" "$o" ;; esac
  fi
  echo "$o"
}

bag_job() { # id config blimit bfzn
  local id="$1" c="$2" lim="$3" f="$4" d="$OUT/runs/$1.$2" stage
  local -a a=()
  # M19-config-T1 (D-0261): the reference solver follows the model's annotation and the
  # factor wants the same tree, so every arm is the fixed search.
  case "$c" in
    pf) a=(--fixed-search --proof p) ;; np) a=(--fixed-search --no-proof) ;;
    cdpf) a=(--fixed-search --cdcl --proof p) ;; cdnp) a=(--fixed-search --cdcl --no-proof) ;;
  esac
  for stage in base full; do
    local -a e=()
    if [ "$stage" = base ]; then e=(BAGUETTE_NODE_LIMIT=1)
    elif [ "$lim" != 0 ]; then e=(BAGUETTE_NODE_LIMIT="$lim"); fi
    run_cmd "$d/$stage" "${e[@]}" -- "$BIN" "${a[@]}" --stats "$f"
    case "$c" in *pf) check_proof "$d/$stage" ;; esac
  done
}

ref_job() { # id ref rlimit rfzn
  local id="$1" r="$2" lim="$3" f="$4" d="$OUT/runs/$1.ref"
  if [ "$r" = gecode ]; then
    run_cmd "$d/base" -- "$MZN_BIN/fzn-gecode" -s -node 1 "$f"
    if [ "$lim" != 0 ]; then run_cmd "$d/full" -- "$MZN_BIN/fzn-gecode" -s -node "$lim" "$f"
    else run_cmd "$d/full" -- "$MZN_BIN/fzn-gecode" -s "$f"; fi
  else
    run_cmd "$d/base" -- "$MZN_BIN/fzn-chuffed" -s --restart none --lazy off -t 1 "$f"
    if [ "$lim" != 0 ]; then
      run_cmd "$d/full" -- "$MZN_BIN/fzn-chuffed" -s --restart none --lazy off -t "$lim" "$f"
    else run_cmd "$d/full" -- "$MZN_BIN/fzn-chuffed" -s --restart none --lazy off "$f"; fi
  fi
}

START=$(date +%s)
LINES=()
while IFS=$'\t' read -r id fam blim ref rlim bf rf; do
  case "$id" in ''|'#'*) continue ;; esac
  if [ -n "$ONLY" ] && ! [[ ",$ONLY," == *",$id,"* ]]; then continue; fi
  case "$ref" in gecode|chuffed-nolazy) ;; *) die "plan: $id has reference '$ref'" ;; esac
  [ -f "$FD/fzn/$bf" ] && [ -f "$FD/fzn/$rf" ] || die "plan: $id names a file missing from bench/factor/fzn/"
  LINES+=("$id	$fam	$blim	$ref	$rlim	$(fzn_of "$bf")	$(fzn_of "$rf")")
done < "$FD/plan.tsv"
[ "${#LINES[@]}" -gt 0 ] || die "no plan line selected"

# The longest runs first: --cdcl with proof (the largest proofs), the default with proof, then
# the runs without proof, then the references.
for c in cdpf pf cdnp np ref; do
  for l in "${LINES[@]}"; do
    IFS=$'\t' read -r id fam blim ref rlim bf rf <<< "$l"
    while [ "$(jobs -rp | wc -l)" -ge "$PAR" ]; do wait -n; done
    if [ "$c" = ref ]; then ref_job "$id" "$ref" "$rlim" "$rf" &
    else bag_job "$id" "$c" "$blim" "$bf" & fi
  done
done
wait
WALL=$(( $(date +%s) - START ))
printf '%s\n' "${LINES[@]}" > "$OUT/plan.selected"

python3 -I "$FD/table.py" "$OUT" "$FD/reference.tsv" "$MD5" "$COMMIT" "$HOST" "$(date -u +%Y-%m-%d)" \
  "$RECORD" "$WALL"
RC=$?
rm -f "$OUT/lane.pid"
exit "$RC"
