#!/usr/bin/env bash
# M11-complexity-T2 (D-0141). THE DIFFERENTIAL LANE.
#
# Real instances, each at a FIXED NODE BUDGET (BAGUETTE_NODE_LIMIT, M6-T9: deterministic,
# never a time limit), in the configurations of bench/diff/configs.tsv that its line in
# bench/diff/corpus.tsv names. What each run shows -- exit code, stdout, the --stats/limit
# counters minus clocks and prose, and the sha256 of the .opb and .pbp -- must equal the
# reference recorded in bench/diff/reference/<config>/<name>.obs. One differing item fails
# the lane, and the failure names the instance, the configuration and the first item that
# differs, and says whether it is a SEARCH or a WORK counter (bench/diff/observe.py).
#
# WHY IT EXISTS. The test models are tiny: they never build a learned database of
# thousands of constraints or a long trail, so they cannot see a change that alters the
# search only once the database is large, and they barely reach the non-default paths.
# The M11 pass replaces every operation whose cost grows with the run (D-0140), and each
# replacement must keep the search and the proof byte for byte. This lane is how a batch
# shows it. D-0140 section 7 lists what it must contain, batch by batch.
#
# TIERS AND PASSES.
#   fast   (default) 21 instances, 1 to 10 s a run: what a batch agent runs after each
#          change, about three minutes at -j 16 on fataepyc-06
#   slow   D-0140's six measured instances at 10 000 nodes (cyclic and openshop lower):
#          deep searches, learned PB rows, integer learned clauses; about five minutes
#   --debug  every selected run again under BAGUETTE_DEBUG=1 at min(budget, 1500) nodes,
#          against bench/diff/reference-debug/: check_watched, check_skip and the I-P7
#          advise check are what catch a lost wake (D-0138), and they only run in debug
#   --full   = --tier all, then the same under --debug. The gate runs the two passes as
#          two commands, so that the debug pass, RED on a8d2924 (D-0141 s5: the I-P7 advise
#          check fires on 16 integer instances), is reported apart from the plain one.
#
#   scripts/diff_lane.sh [--tier fast|slow|all] [--debug | --full] [-j N]
#   scripts/diff_lane.sh --update ...         RE-RECORD the reference (see the rule below)
#   scripts/diff_lane.sh --only NAME          one instance (repeatable)
#   scripts/diff_lane.sh --config NAME        one configuration (repeatable)
#   scripts/diff_lane.sh --bin PATH           the solver under test (default: the dune build)
#   scripts/diff_lane.sh --keep DIR           keep every run's files under DIR
#   scripts/diff_lane.sh --self-test          the comparator's self-test only
#
# Environment: DIFF_PAR (runs in parallel, default 8; -j wins), DIFF_TIMEOUT (seconds per
# run, default 900), BAGUETTE_MEM_CAP_KB (ulimit -v per run, default 4000000, as the
# Makefile).
#
# CLASSES. Every instance is `bool` (learned clauses over Boolean variables: the codes
# models) or `int` (learned clauses over integer order literals). The summary reports the
# two separately, because a wake index by direction is exact on the first and can reorder
# runs on the second (D-0140 E1).
#
# THE REFERENCE RULE (D-0141). The reference is re-recorded ONLY after a GATED merge that
# changes the default search, the proof bytes or a recorded counter ON PURPOSE, in its
# own commit whose message gives the reason. NEVER to make a failing lane pass: a diff is
# a finding about the change under test, exactly as a failing model test is (CLAUDE.md,
# "never weaken a test to make it pass"). --update also runs the checker over every
# proof it records, and refuses to record one the checker does not accept.
#
# PINNED ENVIRONMENT. BAGUETTE_* variables of the caller's shell are unset for each run
# except the memory cap, so a stray BAGUETTE_RETENTION in a terminal cannot silently
# become the default, and BAGUETTE_PROOF_AUDIT is the CLI default (on) except in the
# `audit0` configuration: the end sweep's `del` lines exist only under the audit (D-0140
# W8), so the .pbp depends on it. Every run is in its own directory with the model linked
# in as `model.fzn` and the proof prefix `p`: the .opb names the model path it was given
# (`* baguette: model.fzn`), so an absolute path would make the hash depend on where the
# lane ran.
set -u
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
D="$ROOT/bench/diff"
OBS="$D/observe.py"
BIN="${BIN:-$ROOT/_build/default/bin/main.exe}"
PAR="${DIFF_PAR:-8}"
TMO="${DIFF_TIMEOUT:-900}"
CAP_KB="${BAGUETTE_MEM_CAP_KB:-4000000}"
DEBUG_BUDGET=1500
UPDATE=0
DEBUG=0
FULL=0
TIER=fast
KEEP=""
ONLY_IDS=()
ONLY_CFGS=()
ARGV=("$@")

die() { echo "diff_lane: $*" >&2; exit 2; }
usage() { sed -n '2,/^set -u/p' "$0" | sed '$d' | sed 's/^# \{0,1\}//'; exit 2; }

while [ $# -gt 0 ]; do
  case "$1" in
    --update) UPDATE=1 ;;
    --debug) DEBUG=1 ;;
    --full) FULL=1 ;;
    --tier) [ $# -ge 2 ] || usage; TIER="$2"; shift ;;
    -j) [ $# -ge 2 ] || usage; PAR="$2"; shift ;;
    --only) [ $# -ge 2 ] || usage; ONLY_IDS+=("$2"); shift ;;
    --config) [ $# -ge 2 ] || usage; ONLY_CFGS+=("$2"); shift ;;
    --bin) [ $# -ge 2 ] || usage; BIN="$2"; shift ;;
    --keep) [ $# -ge 2 ] || usage; KEEP="$2"; shift ;;
    --self-test) exec python3 -I "$OBS" --self-test ;;
    -h|--help) usage ;;
    *) die "unknown argument $1 (try --help)" ;;
  esac
  shift
done
case "$TIER" in fast|slow|all) ;; *) die "--tier is fast, slow or all, not $TIER" ;; esac

# --full is two passes of this script: every tier, then every tier under debug.
if [ "$FULL" = 1 ]; then
  rest=()
  for a in "${ARGV[@]}"; do [ "$a" = --full ] || rest+=("$a"); done
  "$0" "${rest[@]}" --tier all; r1=$?
  "$0" "${rest[@]}" --tier all --debug; r2=$?
  echo "diff_lane --full: plain pass rc $r1, debug pass rc $r2"
  [ "$r1" = 0 ] && [ "$r2" = 0 ]; exit $?
fi

# The comparator proves it can fail before it is trusted to pass (the `lint` discipline).
python3 -I "$OBS" --self-test || die "the comparator's self-test failed; nothing was run"

[ -x "$BIN" ] || die "no solver at $BIN (build it first: dune build bin/)"
case "$CAP_KB" in none|unlimited|0) CAPCMD=":" ;; *) CAPCMD="ulimit -v $CAP_KB" ;; esac
REFDIR="$D/reference"
[ "$DEBUG" = 1 ] && REFDIR="$D/reference-debug"

if [ "$UPDATE" = 1 ]; then
  # shellcheck source=checker.sh
  . "$ROOT/scripts/checker.sh"
  baguette_resolve_veripb || { baguette_veripb_diagnostic; die "--update verifies every proof it records; no checker"; }
fi

in_list() { local x="$1"; shift; [ $# -eq 0 ] && return 0; for y in "$@"; do [ "$x" = "$y" ] && return 0; done; return 1; }

# ------------------------------------------------------------------ what to run
CFG_NAMES=(); CFG_ENV=(); CFG_FLAGS=(); CFG_PROOF=()
while IFS=$'\t' read -r name env flags proof; do
  case "$name" in ''|'#'*) continue ;; esac
  CFG_NAMES+=("$name"); CFG_ENV+=("$env"); CFG_FLAGS+=("$flags"); CFG_PROOF+=("$proof")
done < "$D/configs.tsv"
for c in "${ONLY_CFGS[@]+"${ONLY_CFGS[@]}"}"; do in_list "$c" "${CFG_NAMES[@]}" || die "no configuration named $c"; done

# The debug pass's named exclusions: bench/diff/debug-skip.tsv, `name<TAB>config<TAB>reason`
# (config `*` for every configuration of that instance).
# A run listed there is NOT run under --debug, and the lane prints it with its reason on
# every debug pass, so an exclusion can never become silent. Never a way to hide a failure:
# an entry says why the run cannot be afforded under BAGUETTE_DEBUG, with the measurement.
declare -A DSKIP=()
if [ "$DEBUG" = 1 ] && [ -f "$D/debug-skip.tsv" ]; then
  while IFS=$'\t' read -r sn sc sr; do
    case "$sn" in ''|'#'*) continue ;; esac
    DSKIP["$sn|$sc"]="$sr"
  done < "$D/debug-skip.tsv"
fi
SKIPPED=()

# JOBS: "name file budget class cfg-index", one per (instance, configuration).
JOBS=()
declare -A CLASS_OF=()
ALL_NAMES=()
while IFS=$'\t' read -r name file budget tier class cfgs _rest; do
  case "$name" in ''|'#'*) continue ;; esac
  ALL_NAMES+=("$name")
  [ "$TIER" = all ] || [ "$TIER" = "$tier" ] || continue
  in_list "$name" "${ONLY_IDS[@]+"${ONLY_IDS[@]}"}" || continue
  [ -f "$D/corpus/$file.fzn.gz" ] || die "corpus file bench/diff/corpus/$file.fzn.gz missing"
  [ "$DEBUG" = 1 ] && [ "$budget" -gt "$DEBUG_BUDGET" ] && budget=$DEBUG_BUDGET
  CLASS_OF[$name]="$class"
  for ci in "${!CFG_NAMES[@]}"; do
    c="${CFG_NAMES[$ci]}"
    in_list "$c" "${ONLY_CFGS[@]+"${ONLY_CFGS[@]}"}" || continue
    [ "$cfgs" = all ] || in_list "$c" ${cfgs//,/ } || continue
    if [ -n "${DSKIP["$name|$c"]+x}" ]; then
      SKIPPED+=("$name [$c, debug]: ${DSKIP["$name|$c"]}"); continue
    elif [ -n "${DSKIP["$name|*"]+x}" ]; then
      SKIPPED+=("$name [$c, debug]: ${DSKIP["$name|*"]}"); continue
    fi
    JOBS+=("$name $file $budget $class $ci")
  done
done < "$D/corpus.tsv"
for i in "${ONLY_IDS[@]+"${ONLY_IDS[@]}"}"; do in_list "$i" "${ALL_NAMES[@]}" || die "no instance named $i"; done
[ ${#JOBS[@]} -gt 0 ] || die "nothing selected (tier $TIER)"

WORK="${KEEP:-$(mktemp -d "${TMPDIR:-/tmp}/diff_lane.XXXXXX")}"
mkdir -p "$WORK/fzn" "$WORK/res"
[ -n "$KEEP" ] || trap 'rm -rf "$WORK"' EXIT

MD5="$(md5sum < "$BIN" | cut -d' ' -f1)"
echo "diff_lane: solver $BIN md5 $MD5"
echo "diff_lane: reference recorded by: $(grep -v '^#' "$REFDIR/BINARY" 2>/dev/null | tail -1)"
echo "diff_lane: tier $TIER$([ "$DEBUG" = 1 ] && echo ", DEBUG pass (BAGUETTE_DEBUG=1, at most $DEBUG_BUDGET nodes)"), ${#JOBS[@]} runs, $PAR in parallel, ${TMO}s and ulimit -v $CAP_KB per run$([ "$UPDATE" = 1 ] && echo ', RECORDING')"

for k in "${SKIPPED[@]+"${SKIPPED[@]}"}"; do echo "diff_lane: SKIPPED by bench/diff/debug-skip.tsv: $k"; done
for j in "${JOBS[@]}"; do
  read -r _n file _b _c _ci <<< "$j"
  [ -f "$WORK/fzn/$file.fzn" ] || gzip -dc "$D/corpus/$file.fzn.gz" > "$WORK/fzn/$file.fzn" || die "cannot decompress $file"
done

# ------------------------------------------------------------------ one run
run_one() { # name file budget class cfg-index
  local name="$1" file="$2" n="$3" ci="$5"
  local cfg="${CFG_NAMES[$ci]}" env="${CFG_ENV[$ci]}" flags="${CFG_FLAGS[$ci]}" proof="${CFG_PROOF[$ci]}"
  local dir="$WORK/run/$cfg/$name" label="$name [$cfg$([ "$DEBUG" = 1 ] && echo ', debug')]"
  local res="$WORK/res/$cfg.$name" ref="$REFDIR/$cfg/$name.obs"
  mkdir -p "$dir"
  ln -sf "$WORK/fzn/$file.fzn" "$dir/model.fzn"
  local -a envv=() flagv=() proofv=()
  [ "$env" = "-" ] || read -r -a envv <<< "$env"
  [ "$flags" = "-" ] || read -r -a flagv <<< "$flags"
  [ "$proof" = "yes" ] && proofv=(--proof p)
  [ "$DEBUG" = 1 ] && envv+=(BAGUETTE_DEBUG=1)
  (
    cd "$dir" || exit 1
    for v in $(compgen -e | grep '^BAGUETTE_' | grep -v '^BAGUETTE_MEM_CAP_KB$'); do unset "$v"; done
    $CAPCMD
    env "${envv[@]+"${envv[@]}"}" BAGUETTE_NODE_LIMIT="$n" \
      timeout -k 10 "$TMO" "$BIN" model.fzn --stats "${flagv[@]+"${flagv[@]}"}" "${proofv[@]+"${proofv[@]}"}" \
      > out 2> err
    echo $? > rc
  )
  local rcv; rcv="$(cat "$dir/rc")"
  # A non-zero exit is quoted with the solver's last stderr line (an invariant under
  # BAGUETTE_DEBUG, the memory cap, a crash), and it is NEVER recorded as a reference:
  # the lane must not bless a failure.
  local why=""
  [ "$rcv" = 0 ] || why="   [exit $rcv: $(grep -v '^\(stats\|limit\|time\):' "$dir/err" | tail -1 | cut -c1-240)]"
  if [ "$proof" = "yes" ]; then
    if [ ! -f "$dir/p.opb" ] || [ ! -f "$dir/p.pbp" ]; then
      echo "DIFF $label: no proof written (rc $rcv)$why" > "$res"; return
    fi
    python3 -I "$OBS" observe "$rcv" "$dir/out" "$dir/err" "$dir/p.opb" "$dir/p.pbp" > "$dir/obs"
  else
    python3 -I "$OBS" observe "$rcv" "$dir/out" "$dir/err" > "$dir/obs"
  fi
  if [ "$UPDATE" = 1 ]; then
    if [ "$rcv" != 0 ]; then
      echo "REFUSED $label: not recorded$why" > "$res"
      [ -n "$KEEP" ] || rm -f "$dir/p.opb" "$dir/p.pbp"
      return
    fi
    if [ "$proof" = "yes" ]; then
      local v; v="$(timeout 3600 "$VERIPB" "$dir/p.opb" "$dir/p.pbp" 2>&1)"
      if [ $? -ne 0 ] || ! grep -q '^s VERIFIED' <<< "$v"; then
        echo "REFUSED $label: the checker does not accept this proof, not recorded: $(tail -1 <<< "$v")" > "$res"
        return
      fi
    fi
    mkdir -p "$REFDIR/$cfg"
    cp "$dir/obs" "$ref"
    echo "recorded $label (rc $rcv)" > "$res"
  elif [ ! -f "$ref" ]; then
    echo "DIFF $label: NO REFERENCE at ${ref#"$ROOT"/} -- record it with --update (see the rule)$why" > "$res"
  else
    python3 -I "$OBS" compare "$ref" "$dir/obs" "$label" > "$res"
    if [ -n "$why" ] && grep -q '^DIFF' "$res"; then
      { head -1 "$res" | tr -d '\n'; printf '%s\n' "$why"; } > "$res.tmp" && mv "$res.tmp" "$res"
    fi
  fi
  [ -n "$KEEP" ] || rm -f "$dir/p.opb" "$dir/p.pbp"
}

START=$(date +%s)
for j in "${JOBS[@]}"; do
  while [ "$(jobs -r | wc -l)" -ge "$PAR" ]; do wait -n; done
  # shellcheck disable=SC2086
  run_one $j &
done
wait
WALL=$(( $(date +%s) - START ))

TOTAL=${#JOBS[@]}
NRES=$(ls "$WORK/res" | wc -l)
BAD=$(cat "$WORK/res"/* 2>/dev/null | grep -c '^\(DIFF\|REFUSED\)')
cat "$WORK/res"/* 2>/dev/null | grep '^\(DIFF\|REFUSED\)' | sort
cat "$WORK/res"/* 2>/dev/null | grep -o '(note:.*' | sort -u | sed 's/^/diff_lane: /'
# The two learning classes, reported separately (D-0140 section 7, E1).
for cls in bool int; do
  n=0; b=0
  for j in "${JOBS[@]}"; do
    read -r name _f _b class ci <<< "$j"
    [ "$class" = "$cls" ] || continue
    n=$((n + 1))
    grep -q '^\(DIFF\|REFUSED\)' "$WORK/res/${CFG_NAMES[$ci]}.$name" 2>/dev/null && b=$((b + 1))
  done
  [ "$n" = 0 ] || echo "diff_lane: class $cls (learned clauses over $([ "$cls" = bool ] && echo 'Boolean variables' || echo 'integer order literals')): $((n - b)) of $n runs equal"
done
if [ "$NRES" -ne "$TOTAL" ]; then
  echo "diff_lane: FAIL -- only $NRES of $TOTAL runs reported (a run died before writing its result)"
  exit 1
fi
if [ "$UPDATE" = 1 ]; then
  if [ "$BAD" -ne 0 ]; then echo "diff_lane: FAIL -- $BAD run(s) not recorded"; exit 1; fi
  mkdir -p "$REFDIR"
  {
    [ -f "$REFDIR/BINARY" ] || echo "# Who recorded ${REFDIR#"$ROOT"/}/: one line per --update, newest last (D-0141)."
    echo "$(date -u +%Y-%m-%dT%H:%MZ) md5=$MD5 commit=$(git -C "$ROOT" rev-parse --short HEAD 2>/dev/null || echo '?') host=$(hostname -s) tier=$TIER runs=$TOTAL"
  } >> "$REFDIR/BINARY"
  echo "diff_lane: recorded $TOTAL reference(s) in ${WALL}s, every proof accepted by $VERIPB"
  exit 0
fi
if [ "$BAD" -ne 0 ]; then
  echo "diff_lane: FAIL -- $BAD of $TOTAL runs differ from the reference (${WALL}s). Each line above names"
  echo "           the instance, the configuration and the FIRST differing item. Do not re-record to make"
  echo "           this pass (D-0141): the change under test altered the search, the proof or a counter."
  exit 1
fi
echo "diff_lane: ok -- $TOTAL of $TOTAL runs equal the reference (${WALL}s)"
