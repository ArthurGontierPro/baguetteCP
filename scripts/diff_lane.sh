#!/usr/bin/env bash
# M11-complexity-T2 (D-0141). THE DIFFERENTIAL LANE.
#
# Real instances, each at a FIXED NODE BUDGET (BAGUETTE_NODE_LIMIT, M6-T9: deterministic,
# never a time limit), in every configuration of bench/diff/configs.tsv. What each run
# shows -- exit code, stdout, the --stats/limit counters minus clocks and prose, and the
# sha256 of the .opb and .pbp -- must equal the reference recorded in
# bench/diff/reference/<config>/<instance>.obs. One differing item fails the lane, and
# the failure names the instance, the configuration and the first item that differs.
#
# WHY IT EXISTS. The 173 models of test/models/ are tiny: they never build a learned
# database of thousands of constraints or a long trail, so they cannot see a change that
# alters the search only once the database is large, and they barely reach the
# non-default paths (retention policies, PB analysis on/off, the bits arm). The M11
# pass replaces every operation whose cost grows with the run, and each replacement
# must keep the search and the proof byte for byte. This lane is how a batch shows it.
#
#   scripts/diff_lane.sh                      compare against the reference; exit 1 on a diff
#   scripts/diff_lane.sh --update             RE-RECORD the reference (see the rule below)
#   scripts/diff_lane.sh --only ID            one instance (repeatable), any mode
#   scripts/diff_lane.sh --config NAME        one configuration (repeatable), any mode
#   scripts/diff_lane.sh --bin PATH           the solver under test (default: the dune build)
#   scripts/diff_lane.sh --keep DIR           keep every run's files under DIR
#   scripts/diff_lane.sh --self-test          the comparator's self-test only
#
# Environment: DIFF_PAR (parallel runs, default 8), DIFF_TIMEOUT (seconds per run,
# default 300), BAGUETTE_MEM_CAP_KB (ulimit -v per run, default 4000000, as the Makefile).
#
# THE REFERENCE RULE (D-0141). The reference is re-recorded ONLY after a GATED merge that
# changes the default search, the proof bytes or a recorded counter ON PURPOSE, in its
# own commit whose message gives the reason. NEVER to make a failing lane pass: a diff is
# a finding about the change under test, exactly as a failing model test is (CLAUDE.md,
# "never weaken a test to make it pass"). --update also runs the checker over every
# proof it records, and refuses to record one the checker does not accept.
#
# Every run is in its own directory with the model linked in as `model.fzn` and the proof
# prefix `p`: the .opb names the model path it was given (`* baguette: model.fzn`), so an
# absolute path would make the hash depend on where the lane ran. BAGUETTE_* variables of
# the caller's shell are unset for each run except the memory cap: a stray
# BAGUETTE_RETENTION in a terminal would otherwise silently become the default.
set -u
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
D="$ROOT/bench/diff"
OBS="$D/observe.py"
BIN="${BIN:-$ROOT/_build/default/bin/main.exe}"
PAR="${DIFF_PAR:-8}"
TMO="${DIFF_TIMEOUT:-300}"
CAP_KB="${BAGUETTE_MEM_CAP_KB:-4000000}"
UPDATE=0
KEEP=""
ONLY_IDS=()
ONLY_CFGS=()

die() { echo "diff_lane: $*" >&2; exit 2; }
usage() { sed -n '2,/^set -u/p' "$0" | sed '$d' | sed 's/^# \{0,1\}//'; exit 2; }

while [ $# -gt 0 ]; do
  case "$1" in
    --update) UPDATE=1 ;;
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

# The comparator proves it can fail before it is trusted to pass (the `lint` discipline).
python3 -I "$OBS" --self-test || die "the comparator's self-test failed; nothing was run"

[ -x "$BIN" ] || die "no solver at $BIN (build it first: dune build bin/)"
case "$CAP_KB" in none|unlimited|0) CAPCMD=":" ;; *) CAPCMD="ulimit -v $CAP_KB" ;; esac

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
  in_list "$name" "${ONLY_CFGS[@]+"${ONLY_CFGS[@]}"}" || continue
  CFG_NAMES+=("$name"); CFG_ENV+=("$env"); CFG_FLAGS+=("$flags"); CFG_PROOF+=("$proof")
done < "$D/configs.tsv"
IDS=(); BUDGETS=()
while IFS=$'\t' read -r id budget _rest; do
  case "$id" in ''|'#'*) continue ;; esac
  in_list "$id" "${ONLY_IDS[@]+"${ONLY_IDS[@]}"}" || continue
  IDS+=("$id"); BUDGETS+=("$budget")
done < "$D/corpus.tsv"
[ ${#CFG_NAMES[@]} -gt 0 ] || die "no configuration selected"
[ ${#IDS[@]} -gt 0 ] || die "no instance selected"
for c in "${ONLY_CFGS[@]+"${ONLY_CFGS[@]}"}"; do in_list "$c" "${CFG_NAMES[@]}" || die "no configuration named $c"; done
for i in "${ONLY_IDS[@]+"${ONLY_IDS[@]}"}"; do in_list "$i" "${IDS[@]}" || die "no instance named $i"; done

WORK="${KEEP:-$(mktemp -d "${TMPDIR:-/tmp}/diff_lane.XXXXXX")}"
mkdir -p "$WORK/fzn" "$WORK/res"
[ -n "$KEEP" ] || trap 'rm -rf "$WORK"' EXIT

MD5="$(md5sum < "$BIN" | cut -d' ' -f1)"
echo "diff_lane: solver $BIN md5 $MD5"
echo "diff_lane: reference recorded by: $(grep -v '^#' "$D/reference/BINARY" 2>/dev/null | tail -1)"
echo "diff_lane: ${#IDS[@]} instance(s) x ${#CFG_NAMES[@]} configuration(s), $PAR in parallel, ${TMO}s and ulimit -v $CAP_KB per run$([ "$UPDATE" = 1 ] && echo ', RECORDING')"

for id in "${IDS[@]}"; do
  [ -f "$D/corpus/$id.fzn.gz" ] || die "corpus file $D/corpus/$id.fzn.gz missing"
  gzip -dc "$D/corpus/$id.fzn.gz" > "$WORK/fzn/$id.fzn" || die "cannot decompress $id"
done

# ------------------------------------------------------------------ one run
run_one() { # cfg-index id budget
  local ci="$1" id="$2" n="$3"
  local cfg="${CFG_NAMES[$ci]}" env="${CFG_ENV[$ci]}" flags="${CFG_FLAGS[$ci]}" proof="${CFG_PROOF[$ci]}"
  local dir="$WORK/run/$cfg/$id" label="$id [$cfg]" res="$WORK/res/$cfg.$id"
  local ref="$D/reference/$cfg/$id.obs"
  mkdir -p "$dir"
  ln -sf "$WORK/fzn/$id.fzn" "$dir/model.fzn"
  local -a envv=() flagv=() proofv=()
  [ "$env" = "-" ] || read -r -a envv <<< "$env"
  [ "$flags" = "-" ] || read -r -a flagv <<< "$flags"
  [ "$proof" = "yes" ] && proofv=(--proof p)
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
  if [ "$proof" = "yes" ]; then
    if [ ! -f "$dir/p.opb" ] || [ ! -f "$dir/p.pbp" ]; then
      echo "DIFF $label: no proof written (rc $rcv)" > "$res"; return
    fi
    python3 -I "$OBS" observe "$rcv" "$dir/out" "$dir/err" "$dir/p.opb" "$dir/p.pbp" > "$dir/obs"
  else
    python3 -I "$OBS" observe "$rcv" "$dir/out" "$dir/err" > "$dir/obs"
  fi
  if [ "$UPDATE" = 1 ]; then
    if [ "$proof" = "yes" ]; then
      local v; v="$(timeout 3600 "$VERIPB" "$dir/p.opb" "$dir/p.pbp" 2>&1)"
      if [ $? -ne 0 ] || ! grep -q '^s VERIFIED' <<< "$v"; then
        echo "REFUSED $label: the checker does not accept this proof, not recorded: $(tail -1 <<< "$v")" > "$res"
        return
      fi
    fi
    mkdir -p "$D/reference/$cfg"
    cp "$dir/obs" "$ref"
    echo "recorded $label (rc $rcv)" > "$res"
  elif [ ! -f "$ref" ]; then
    echo "DIFF $label: NO REFERENCE at ${ref#"$ROOT"/} -- record it with --update (see the rule)" > "$res"
  else
    python3 -I "$OBS" compare "$ref" "$dir/obs" "$label" > "$res"
  fi
  [ -n "$KEEP" ] || rm -f "$dir/p.opb" "$dir/p.pbp"
}

START=$(date +%s)
for i in "${!IDS[@]}"; do
  for ci in "${!CFG_NAMES[@]}"; do
    while [ "$(jobs -r | wc -l)" -ge "$PAR" ]; do wait -n; done
    run_one "$ci" "${IDS[$i]}" "${BUDGETS[$i]}" &
  done
done
wait
WALL=$(( $(date +%s) - START ))

TOTAL=$(( ${#IDS[@]} * ${#CFG_NAMES[@]} ))
NRES=$(ls "$WORK/res" | wc -l)
BAD=$(cat "$WORK/res"/* 2>/dev/null | grep -c '^\(DIFF\|REFUSED\)')
cat "$WORK/res"/* 2>/dev/null | grep '^\(DIFF\|REFUSED\)' | sort
cat "$WORK/res"/* 2>/dev/null | grep -o '(note:.*' | sort -u | sed 's/^/diff_lane: /'
if [ "$NRES" -ne "$TOTAL" ]; then
  echo "diff_lane: FAIL -- only $NRES of $TOTAL runs reported (a run died before writing its result)"
  exit 1
fi
if [ "$UPDATE" = 1 ]; then
  if [ "$BAD" -ne 0 ]; then echo "diff_lane: FAIL -- $BAD run(s) not recorded"; exit 1; fi
  {
    [ -f "$D/reference/BINARY" ] || echo "# Who recorded bench/diff/reference/: one line per --update, newest last (D-0141)."
    echo "$(date -u +%Y-%m-%dT%H:%MZ) md5=$MD5 commit=$(git -C "$ROOT" rev-parse --short HEAD 2>/dev/null || echo '?') host=$(hostname -s) configs=$(IFS=,; echo "${CFG_NAMES[*]}") instances=${#IDS[@]}"
  } >> "$D/reference/BINARY"
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
