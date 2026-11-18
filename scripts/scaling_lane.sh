#!/usr/bin/env bash
# M11-complexity-T2 (D-0141). THE SCALING LANE: does the cost of the search grow with the
# learned database?
#
# Each line of bench/scaling/plan.tsv names an instance of the differential corpus, a
# mode (proof or noproof) and four node budgets N0 < N1 <= N2 < N3. The instance is run at
# each budget (BAGUETTE_NODE_LIMIT, deterministic) and a COST is read off each run. Then
#
#     early = (cost(N1) - cost(N0)) / (props(N1) - props(N0))     small database
#     late  = (cost(N3) - cost(N2)) / (props(N3) - props(N2))     large database
#     ratio = late / early
#
# where props is the number of propagator runs (`stats: props`). A build in which every
# operation costs the same whatever the size of the database has a ratio that does not
# move when an M11 batch lands; an operation linear in the database, run per conflict,
# per node or per propagation, raises the late segment and not the early one.
#
# WHY PER PROPAGATOR RUN AND NOT PER NODE. The number of propagator runs per node grows
# with the database ON PURPOSE: more learned constraints, more of them waking (QR48:
# 316 runs per node over nodes 1000-2000, 694 over 16000-23000; parity-learning: x4).
# That growth is the search, not its implementation, and it is identical in every build
# that passes the differential lane, which checks `props` byte for byte. Per node, the
# lane would read the search's own shape as a regression; per propagator run it reads
# what each unit of work costs. The per-node ratio is printed beside it.
#
# THE COST. `perf stat -e instructions:u` when perf works here: user-mode instructions
# retired are a property of the binary and its input, not of the machine's load, so a
# node at load 50 gives the same count as an idle one (measured: 0.05 % between two runs).
# Otherwise the OCaml GC's allocated words (OCAMLRUNPARAM=v=0x400), which are exactly
# deterministic but blind to a cost that does not allocate (a List.mem); the lane says
# which one it used, and compares a line only against a baseline of the same metric.
#
# Instructions UNDERSTATE a cost that is bound by memory rather than by work: a walk over a
# list strewn across the major heap retires few instructions per cache miss. D-0138
# measured `Retention.reduce`'s copy at 13 % of the CYCLES on QR48; in instructions the
# same kind of copy is a few per cent. So `cycles:u` is read too and printed beside the
# enforced ratio, as information: cycles move with the load on a shared node, and a gate
# on them would be a flaky gate.
#
# THE THRESHOLD. bench/scaling/baseline.tsv holds each line's ratio as recorded; the lane
# enforces ratio <= baseline x (1 + margin), margin 1 % by default (ten times the run-to-run
# jitter of the ratio, measured at <= 0.1 %). It is a RATCHET: a
# batch that lowers a ratio re-records it (--update, in its own commit, after the gated
# merge), and nothing re-records it upward.
#
# REPORT-ONLY UNTIL M11-complexity-T6. Main still carries known linear costs owned by
# rows in flight, so the lane prints its verdict and exits 0. `--enforce` (or
# SCALING_ENFORCE=1) makes an OVER line fail; T6 makes that the default.
#
#   scripts/scaling_lane.sh [--enforce] [--update] [-j N] [--bin PATH] [--keep DIR]
#
# Environment: SCALING_PAR (default 8), SCALING_TIMEOUT (default 900 s per run),
# SCALING_MARGIN (default 0.01), BAGUETTE_MEM_CAP_KB (ulimit -v per run, default 4000000).
set -u
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
S="$ROOT/bench/scaling"
CORPUS="$ROOT/bench/diff/corpus"
BIN="${BIN:-$ROOT/_build/default/bin/main.exe}"
PAR="${SCALING_PAR:-8}"
TMO="${SCALING_TIMEOUT:-900}"
MARGIN="${SCALING_MARGIN:-0.01}"
CAP_KB="${BAGUETTE_MEM_CAP_KB:-4000000}"
ENFORCE="${SCALING_ENFORCE:-0}"
UPDATE=0
KEEP=""

die() { echo "scaling_lane: $*" >&2; exit 2; }
usage() { sed -n '2,/^set -u/p' "$0" | sed '$d' | sed 's/^# \{0,1\}//'; exit 2; }
while [ $# -gt 0 ]; do
  case "$1" in
    --enforce) ENFORCE=1 ;;
    --update) UPDATE=1 ;;
    -j) [ $# -ge 2 ] || usage; PAR="$2"; shift ;;
    --bin) [ $# -ge 2 ] || usage; BIN="$2"; shift ;;
    --keep) [ $# -ge 2 ] || usage; KEEP="$2"; shift ;;
    -h|--help) usage ;;
    *) die "unknown argument $1 (try --help)" ;;
  esac
  shift
done
[ -x "$BIN" ] || die "no solver at $BIN (build it first: dune build bin/)"
case "$CAP_KB" in none|unlimited|0) CAPCMD=":" ;; *) CAPCMD="ulimit -v $CAP_KB" ;; esac

PERF="${PERF:-$(command -v perf 2>/dev/null || true)}"
METRIC=gcwords
if [ -n "$PERF" ] && "$PERF" stat -x, -e instructions:u -o /dev/null true >/dev/null 2>&1 \
   && "$PERF" stat -x, -e instructions:u true 2>&1 | grep -q '^[0-9]'; then
  METRIC=instructions
else
  echo "scaling_lane: perf cannot count instructions:u here (${PERF:-not installed};"
  echo "              kernel.perf_event_paranoid is $(cat /proc/sys/kernel/perf_event_paranoid 2>/dev/null || echo '?'))."
  echo "              FALLING BACK to the GC's allocated words: deterministic, but blind to a cost"
  echo "              that does not allocate. Lines whose baseline is in instructions are REPORTED only."
fi

WORK="${KEEP:-$(mktemp -d "${TMPDIR:-/tmp}/scaling_lane.XXXXXX")}"
mkdir -p "$WORK"
[ -n "$KEEP" ] || trap 'rm -rf "$WORK"' EXIT
MD5="$(md5sum < "$BIN" | cut -d' ' -f1)"
echo "scaling_lane: solver $BIN md5 $MD5, metric $METRIC, $PAR in parallel"

run_one() { # id mode budget -> $WORK/<id>.<mode>.<budget>/{cost,nodes,props}
  local id="$1" mode="$2" n="$3" d="$WORK/$1.$2.$3"
  mkdir -p "$d"
  [ -f "$WORK/$id.fzn" ] || return 1
  ln -sf "$WORK/$id.fzn" "$d/model.fzn"
  local -a pf=(--no-proof)
  [ "$mode" = proof ] && pf=(--proof p)
  (
    cd "$d" || exit 1
    for v in $(compgen -e | grep '^BAGUETTE_' | grep -v '^BAGUETTE_MEM_CAP_KB$'); do unset "$v"; done
    $CAPCMD
    if [ "$METRIC" = instructions ]; then
      OCAMLRUNPARAM=v=0x400 BAGUETTE_NODE_LIMIT="$n" timeout -k 10 "$TMO" \
        "$PERF" stat -x, -e instructions:u,cycles:u -o perf.txt "$BIN" model.fzn --stats "${pf[@]}" > out 2> err
    else
      OCAMLRUNPARAM=v=0x400 BAGUETTE_NODE_LIMIT="$n" timeout -k 10 "$TMO" \
        "$BIN" model.fzn --stats "${pf[@]}" > out 2> err
    fi
    echo $? > rc
  )
  rm -f "$d/p.opb" "$d/p.pbp"
  awk '/^allocated_words:/ {print $2}' "$d/err" > "$d/gcwords"
  [ -f "$d/perf.txt" ] && grep 'instructions' "$d/perf.txt" | cut -d, -f1 > "$d/instructions"
  [ -f "$d/perf.txt" ] && grep 'cycles' "$d/perf.txt" | cut -d, -f1 > "$d/cycles"
  awk '$1=="stats:" && $2=="nodes" {print $3; exit}' "$d/err" > "$d/nodes"
  awk '$1=="stats:" && $2=="props" {print $3; exit}' "$d/err" > "$d/props"
}

START=$(date +%s)
LINES=()
while IFS=$'\t' read -r id mode n0 n1 n2 n3 _why; do
  case "$id" in ''|'#'*) continue ;; esac
  [ -f "$CORPUS/$id.fzn.gz" ] || die "$id is not in bench/diff/corpus/"
  [ -f "$WORK/$id.fzn" ] || gzip -dc "$CORPUS/$id.fzn.gz" > "$WORK/$id.fzn"
  LINES+=("$id $mode $n0 $n1 $n2 $n3")
  for n in "$n0" "$n1" "$n2" "$n3"; do
    while [ "$(jobs -r | wc -l)" -ge "$PAR" ]; do wait -n; done
    run_one "$id" "$mode" "$n" &
  done
done < "$S/plan.tsv"
wait
WALL=$(( $(date +%s) - START ))

OVER=0; BROKEN=0; NEWBASE=""
for l in "${LINES[@]}"; do
  read -r id mode n0 n1 n2 n3 <<< "$l"
  get() { cat "$WORK/$id.$mode.$1/$2" 2>/dev/null; }
  ok=1
  for n in "$n0" "$n1" "$n2" "$n3"; do
    rc="$(get "$n" rc)"; nodes="$(get "$n" nodes)"
    if [ "$rc" != 0 ] || [ -z "$(get "$n" "$METRIC")" ] || [ -z "$(get "$n" props)" ]; then
      echo "scaling: BROKEN $id [$mode] at $n nodes: rc ${rc:-?}, no $METRIC or props count"; ok=0
    elif [ "$nodes" != "$((n + 1))" ]; then
      echo "scaling: BROKEN $id [$mode] at $n nodes: the search ended at $nodes nodes, not at the budget"
      echo "         (the instance closed or stopped early; lower N3 in bench/scaling/plan.tsv)"; ok=0
    fi
  done
  [ "$ok" = 1 ] || { BROKEN=$((BROKEN + 1)); continue; }
  read -r ratio early late node_ratio < <(python3 -I - \
    "$(get "$n0" "$METRIC")" "$(get "$n1" "$METRIC")" "$(get "$n2" "$METRIC")" "$(get "$n3" "$METRIC")" \
    "$(get "$n0" props)" "$(get "$n1" props)" "$(get "$n2" props)" "$(get "$n3" props)" \
    "$n0" "$n1" "$n2" "$n3" <<'PY'
import sys
c0, c1, c2, c3, p0, p1, p2, p3, n0, n1, n2, n3 = map(int, sys.argv[1:])
early, late = (c1 - c0) / (p1 - p0), (c3 - c2) / (p3 - p2)
node_early, node_late = (c1 - c0) / (n1 - n0), (c3 - c2) / (n3 - n2)
print("%.4f %.1f %.1f %.4f" % (late / early, early, late, node_late / node_early))
PY
)
  cyc=""
  if [ "$METRIC" = instructions ] && [ -n "$(get "$n0" cycles)" ] && [ -n "$(get "$n3" cycles)" ]; then
    cyc="$(python3 -I -c 'import sys; c=list(map(int, sys.argv[1:5])); p=list(map(int, sys.argv[5:9])); print("%.4f" % (((c[3]-c[2])/(p[3]-p[2])) / ((c[1]-c[0])/(p[1]-p[0]))))' \
      "$(get "$n0" cycles)" "$(get "$n1" cycles)" "$(get "$n2" cycles)" "$(get "$n3" cycles)" \
      "$(get "$n0" props)" "$(get "$n1" props)" "$(get "$n2" props)" "$(get "$n3" props)" 2>/dev/null)"
  fi
  base="$(awk -F'\t' -v i="$id" -v m="$mode" -v k="$METRIC" '$1==i && $2==m && $3==k {r=$4} END {print r}' "$S/baseline.tsv" 2>/dev/null)"
  NEWBASE+="$id	$mode	$METRIC	$ratio	$(hostname -s)	$MD5	$(date -u +%Y-%m-%d)"$'\n'
  if [ -z "$base" ]; then
    verdict="NO BASELINE for metric $METRIC (report only)"
  else
    thr="$(python3 -I -c "print('%.4f' % ($base * (1 + $MARGIN)))")"
    if python3 -I -c "import sys; sys.exit(0 if $ratio <= $thr else 1)"; then
      verdict="ok (baseline $base, threshold $thr)"
    else
      verdict="OVER (baseline $base, threshold $thr)"; OVER=$((OVER + 1))
    fi
  fi
  printf 'scaling: %-32s [%-7s] per-prop late/early = %s (%s -> %s %s/run); per-node %s -- %s\n' \
    "$id" "$mode" "$ratio" "$early" "$late" "$METRIC" "$node_ratio" "$verdict"
  [ -z "$cyc" ] || printf 'scaling: %-32s [%-7s]   cycles:u per-prop late/early = %s (load-sensitive: information, never enforced)\n' \
    "$id" "$mode" "$cyc"
done

if [ "$UPDATE" = 1 ]; then
  [ "$BROKEN" = 0 ] || die "not recording a baseline with $BROKEN broken line(s)"
  {
    echo "# M11-complexity-T2 (D-0141). The scaling lane's baseline ratios, per (instance, mode, metric)."
    echo "# A RATCHET: re-recorded by \`scripts/scaling_lane.sh --update\` only after a gated merge that"
    echo "# LOWERS a ratio (an M11 batch, or T6), in its own commit; never upward to make a line pass."
    printf '%s' "$NEWBASE"
  } > "$S/baseline.tsv"
  echo "scaling_lane: baseline recorded in bench/scaling/baseline.tsv (${WALL}s)"
  exit 0
fi
if [ "$BROKEN" -gt 0 ]; then
  echo "scaling_lane: FAIL -- $BROKEN line(s) could not be measured (${WALL}s)"
  exit 1
fi
if [ "$OVER" -gt 0 ]; then
  if [ "$ENFORCE" = 1 ]; then
    echo "scaling_lane: FAIL -- $OVER line(s) over threshold: the cost per propagator run grows with the"
    echo "              learned database more than the recorded baseline (${WALL}s)"
    exit 1
  fi
  echo "scaling_lane: REPORT-ONLY -- $OVER line(s) over threshold, NOT failing (M11-complexity-T6 makes"
  echo "              this a gate; --enforce fails now) (${WALL}s)"
  exit 0
fi
echo "scaling_lane: ok -- every line within its threshold$([ "$ENFORCE" = 1 ] || echo ' (report-only until M11-complexity-T6)') (${WALL}s)"
