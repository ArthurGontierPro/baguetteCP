#!/usr/bin/env bash
# The proof benchmark (M3-T5, absorbing M3-T3). Read bench/README.md first; it says
# what these numbers mean and, more importantly, what they do not.
#
# Four numbers, never one score:
#
#     .opb bytes      how big the problem statement is
#     .pbp bytes      how big the proof of it is
#     verify seconds  how long a checker takes to believe it
#     peak RSS        how much memory the two of them needed
#
# The first three are reported in separate columns because they do not have to move
# together. GCS measured a 5.9x SMALLER proof that took 3.5x LONGER to check at an
# identical search tree (docs/GCS-COMPARISON.md section 4), so a benchmark that adds
# them up, or that reports only size, will approve a change that made checking three
# times slower. There is deliberately no total column and no score.
#
# The fourth is here because on this machine memory is the resource that fails first:
# 15 GB of RAM, four sessions building at once, and a wide-domain model's in-memory
# cost is far above its file size -- measured, at the bottom of bench/README.md, at
# roughly 1.5 kB of peak RSS per unit of declared domain width, against 63 bytes of
# .opb. A benchmark that watched bytes and seconds would have reported a run that was
# swapping the box as merely slow.
#
# Two more, for the same reason at one remove: solve time is reported apart from
# verify time, and a search-tree proxy is reported apart from both. Without them a
# proof that grew because the SEARCH changed is indistinguishable from one that grew
# because each pruning now costs more lines -- and those two have opposite fixes.
#
# And, since M1-T35, a SECOND TABLE of the solver's own internal timings, read back
# from `baguette --time`. The first table's "solve ms" is wall time around a whole
# process and always will be; M3-T5 measured a 4.0 ms floor to start this binary and
# found 15 of 18 models sitting at it, which is why that table alone could not support
# a speed claim in either direction. The second table says how much of each of those
# numbers the solver actually spent inside itself, and on which phase. The two tables
# are printed side by side rather than one replacing the other, because the COMPARISON
# between them is the measurement: it is what shows how much was `exec`.
#
# This is a measurement tool, not a gate. It is not wired into `make check` and must
# not be: it takes minimums over repeated runs, which is slow by construction, and a
# timing number has no business failing a build.
#
# Honesty rules, which this project has paid for twice (D-0023 and D-0025 both had to
# retract a speed claim, and M1-T24 produced a null result that was correctly reported
# as one):
#
#   * MINIMUMS, never means. A mean mixes in whatever else the machine was doing;
#     the minimum is the closest this harness gets to the work itself.
#   * ONE AT A TIME. Nothing here runs in parallel, and it warns when the machine is
#     already busy, because several Claude sessions build in this checkout at once.
#   * The SPREAD of each timing is printed next to it. A difference no larger than
#     the spread is noise, and the footer says so in those words.
#   * Byte counts are checked for reproducibility across the repeats. If a model's
#     proof is not byte-identical every time, its size numbers are announced as
#     unreliable rather than quietly averaged.
#   * A proof the checker REJECTS is never reported as a row of timings. Timing an
#     unaccepted proof measures nothing.
#   * A model whose declared widths put it over the memory estimate REFUSES to run
#     rather than taking the machine down with it. See "the guard" below.
#   * The instrument checks ITSELF before it measures anything. See "self-checks"
#     below: two properties this harness's own columns rest on, both of which were
#     broken in this tree until M1-T35/M1-T37, both verified against the binary that
#     is about to be measured rather than assumed of it.

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=../scripts/checker.sh
. "${ROOT}/scripts/checker.sh"

REPEATS=5
WARMUP=1
OUTDIR="${ROOT}/bench/out"
SCDIR="${OUTDIR}/selfcheck"
TSV=""
KEEP=0
SOLVER_A="${BAGUETTE:-${ROOT}/_build/default/bin/main.exe}"
SOLVER_B=""
FORMAT_A=""
FORMAT_B=""
LABEL_A="A"
LABEL_B="B"
COMPARE=0
FORCE=0
TIMEOUT=300

# ------------------------------------------------------------------ the guard
#
# Two caps, both measured rather than guessed (bench/README.md, "the resource that
# fails first"). Either one refuses the model; -Y overrides both and says so.
#
# WIDTH_CAP is the ceiling the orchestrator set for this round while four sessions
# share a 15 GB box: no single declared domain wider than 10^5, whatever the estimate
# says. D-0028's own table stops being runnable here shortly after that -- w = 10^6 is
# a 156 MB .opb and about 2.8 GB of peak RSS to produce it.
#
# MEM_CAP_MB is the estimate: about 1.5 kB of peak RSS per unit of TOTAL declared
# width, summed over the model's variables, which is the number measured at
# w = 10^4 and w = 5*10^4 and extrapolated. An estimate is not a measurement, so it is
# deliberately conservative and it is a refusal to start, not a limit that would kill
# the process partway.
WIDTH_CAP=100000
MEM_CAP_MB=2048
RSS_PER_UNIT_B=1500

usage() {
  cat <<'EOF'
usage: bench/run_bench.sh [options] [MODEL.fzn ...]

With no models named, every .fzn in test/models/ is measured.

  -r N     repeats per measurement, minimum reported   (default 5)
  -w N     warmup runs discarded before the repeats    (default 1)
  -s BIN   solver binary for configuration A           (default _build/default/bin/main.exe)
  -f FMT   BAGUETTE_PROOF_FORMAT for configuration A   (default: the solver's own, 3.0)
  -a NAME  label for configuration A
  -S BIN   solver binary for configuration B           -- naming either -S or -F
  -F FMT   BAGUETTE_PROOF_FORMAT for configuration B      turns on comparison mode
  -b NAME  label for configuration B
  -o FILE  also write the raw measurements as TSV. The solver's internal timings go
           to FILE.internal -- a separate file because they are a different clock
           (CPU, not wall) taken on different runs, and two clocks in one row get
           subtracted from each other by whoever reads it next.
  -t SECS  per-invocation timeout                      (default 300)
  -k       keep the .opb/.pbp artefacts under bench/out/
  -Y       run a model the width/memory guard refused. Says what it estimated.
  -h       this

Examples:

  bench/run_bench.sh                      every model, one configuration
  bench/run_bench.sh -r 9 test/models/width_root_unsat.fzn
  bench/run_bench.sh -F 2.0 -b 'format 2.0'    3.0 against 2.0, four columns each
  bench/run_bench.sh -S /path/to/other/main.exe -b layered
                                          two solver builds -- this is the shape the
                                          D-0026 falsifier needs; see bench/README.md
                                          for why it cannot be run yet.
EOF
  exit "${1:-2}"
}

while getopts "r:w:s:f:a:S:F:b:o:t:kYh" opt; do
  case "${opt}" in
    r) REPEATS="${OPTARG}" ;;
    w) WARMUP="${OPTARG}" ;;
    s) SOLVER_A="${OPTARG}" ;;
    f) FORMAT_A="${OPTARG}" ;;
    a) LABEL_A="${OPTARG}" ;;
    S) SOLVER_B="${OPTARG}"; COMPARE=1 ;;
    F) FORMAT_B="${OPTARG}"; COMPARE=1 ;;
    b) LABEL_B="${OPTARG}" ;;
    o) TSV="${OPTARG}" ;;
    t) TIMEOUT="${OPTARG}" ;;
    k) KEEP=1 ;;
    Y) FORCE=1 ;;
    h) usage 0 ;;
    *) usage 2 ;;
  esac
done
shift $((OPTIND - 1))

[ "${COMPARE}" -eq 1 ] && [ -z "${SOLVER_B}" ] && SOLVER_B="${SOLVER_A}"

# ------------------------------------------------------------------ the clock
#
# EPOCHREALTIME is a bash builtin, so reading it forks nothing; `date +%s%N` in a
# command substitution costs a process, which on the models here is a sizeable
# fraction of what is being measured. The decimal separator follows the locale, so
# both spellings are stripped.
if [ -n "${EPOCHREALTIME:-}" ]; then
  now_us() { local t="${EPOCHREALTIME/,/.}"; printf '%s' "${t/./}"; }
else
  now_us() { local t; t="$(date +%s%N)"; printf '%s' "$((t / 1000))"; }
fi

# Integer milliseconds with one decimal, from microseconds. No floating point in the
# whole script: a benchmark whose own arithmetic needs a second opinion is no use.
ms() { printf '%d.%01d' $(( $1 / 1000 )) $(( ($1 % 1000) / 100 )); }

# Percent, rounded, of $1 relative to $2. Guards $2 = 0.
pct() { if [ "$2" -le 0 ]; then printf 'n/a'; else printf '%d' $(( ($1 * 100 + ($2 / 2)) / $2 )); fi; }

# Peak RSS of one command, in kB, or the empty string if /usr/bin/time is not here.
# It is measured on its own dedicated run, NOT on the timed repeats, so that the
# wrapper's own cost never lands in a number this harness reports as solve or verify
# time. One extra solve and one extra verify per model per configuration.
HAVE_TIME=0
[ -x /usr/bin/time ] && HAVE_TIME=1
peak_rss_kb() {
  [ "${HAVE_TIME}" -eq 0 ] && { printf ''; return 0; }
  /usr/bin/time -f '%M' "$@" 2>&1 >/dev/null | tail -1 | grep -E '^[0-9]+$' || printf ''
}
mb() { if [ -z "$1" ]; then printf 'n/a'; else printf '%d' $(( ($1 + 512) / 1024 )); fi; }

# ------------------------------------------------------------------ preflight

if ! baguette_resolve_veripb; then
  echo "run_bench.sh: no checker, so nothing can be verified and no verify time exists." >&2
  baguette_veripb_diagnostic
  exit 2
fi

for bin in "${SOLVER_A}" ${SOLVER_B:+"${SOLVER_B}"}; do
  if [ ! -x "${bin}" ]; then
    echo "run_bench.sh: solver not executable: ${bin}" >&2
    echo "  build it first:  dune build --root ." >&2
    exit 2
  fi
done

MODELS=("$@")
if [ "${#MODELS[@]}" -eq 0 ]; then
  mapfile -t MODELS < <(ls "${ROOT}"/test/models/*.fzn)
fi

mkdir -p "${OUTDIR}"
rm -rf "${SCDIR}"
mkdir -p "${SCDIR}"

# ------------------------------------------------------------------ self-checks
#
# Two properties of the binary about to be measured. Both are properties THIS
# HARNESS'S OWN COLUMNS rest on, both were false in this tree until M1-T35/M1-T37, and
# both are cheap to check, so they are checked against the binary rather than assumed
# of it. A benchmark that trusts its instrument is how a retracted speed claim starts,
# and this project has two (D-0023, D-0025).
#
#   1. .opb BYTES ARE A PROPERTY OF THE MODEL, not of the path you typed. The .opb
#      carries a `* baguette: <name>` comment; while that name was the full path, the
#      same model measured as test/models/x.fzn and as /tmp/x.fzn produced .opb files
#      about 16 bytes apart. .opb bytes are the one column M3-T5 found trustworthy at
#      every row, so a size that moves with the caller's directory undermines the one
#      reliable measurement here. Checked by solving the same model through a short
#      path and a long one and comparing the bytes.
#
#      A failure here is LOUD and makes the run exit non-zero, but it does not stop the
#      measurement: within one invocation both configurations use the same path, so the
#      .opb DELTA is still sound, and `-S old/main.exe` against a build from before
#      M1-T37 has to stay possible. What breaks is comparing these bytes with someone
#      else's, and the warning says exactly that.
#
#   2. --time IS INVISIBLE TO EVERYTHING ELSE. SPEC 2.2 pins solution output byte for
#      byte and test/expected/*.out is ground truth (I-M1), so the timing report must
#      appear on stderr only, must not move one byte of stdout, and must not change the
#      proof. The internal table below is measured on ITS OWN runs with --time, so if
#      --time perturbed the artefacts the two tables would silently be about different
#      things. A failure here is FATAL: it means the solver is contaminating stdout,
#      and no number should be taken from a binary doing that.
#
# A binary that does not know --time at all is not a failure: it is an older build,
# the internal table is skipped with a notice, and the wall-clock table is unaffected.
# That is the "where they are available" half of M1-T35.

SELFCHECK_OPB_PATH_DEP=0 # set when check 1 fails
HAVE_TIME_FLAG=0         # set when the solver understands --time

# Does $1 REJECT --time as an unknown option? That, and only that, is an older binary.
#
# The distinction has to be drawn here and it has to be drawn on the ARGUMENT PARSER's
# answer, not on where the output turned up. The first draft of this function asked
# instead "is there a `time: process` line on stderr?" and treated its absence as "no
# --time support" -- and a deliberate break that sent the whole report to STDOUT was
# then reported as a benign `note  this binary has no working --time`, the quietness
# check below was skipped as inapplicable, and the run exited 0. The worst failure this
# file can have -- the solver contaminating the stdout that SPEC 2.2 pins byte for byte
# -- came out as the mildest message it can print. That is this project's signature
# failure mode (D-0025, D-0030, D-0032) inside the check written to prevent it, and it
# was found by breaking the thing rather than by reading the code.
#
# So: unknown option means old binary, ANYTHING else means the flag was accepted and
# everything it then does is this harness's business.
time_flag_unknown() {
  local bin="$1" fzn="$2" err rc
  err="$(timeout "${TIMEOUT}" "${bin}" "${fzn}" --proof "${SCDIR}/t" --time 2>&1 >/dev/null)"
  rc=$?
  [ "${rc}" -ne 0 ] && printf '%s\n' "${err}" | grep -q 'unknown option: --time'
}

opb_path_independence() {
  local bin="$1" fzn="$2" base short long a b
  base="$(basename "${fzn}")"
  short="${SCDIR}/s"
  long="${SCDIR}/a/considerably/longer/directory/chain/than/the/other/one"
  mkdir -p "${short}" "${long}"
  cp "${fzn}" "${short}/${base}"
  cp "${fzn}" "${long}/${base}"
  timeout "${TIMEOUT}" "${bin}" "${short}/${base}" --proof "${SCDIR}/short" \
    >/dev/null 2>&1 || return 2
  timeout "${TIMEOUT}" "${bin}" "${long}/${base}" --proof "${SCDIR}/long" \
    >/dev/null 2>&1 || return 2
  a="$(stat -c%s "${SCDIR}/short.opb")"
  b="$(stat -c%s "${SCDIR}/long.opb")"
  sc_a="${a}"; sc_b="${b}"
  sc_short_len="${#short}"; sc_long_len="${#long}"
  [ "${a}" = "${b}" ] || return 1
  cmp -s "${SCDIR}/short.opb" "${SCDIR}/long.opb" || return 1
  return 0
}

time_flag_is_quiet() {
  local bin="$1" fzn="$2"
  timeout "${TIMEOUT}" "${bin}" "${fzn}" --proof "${SCDIR}/q1" \
    > "${SCDIR}/q1.out" 2> "${SCDIR}/q1.err" || return 2
  timeout "${TIMEOUT}" "${bin}" "${fzn}" --proof "${SCDIR}/q2" --time \
    > "${SCDIR}/q2.out" 2> "${SCDIR}/q2.err" || return 2
  # The report has to BE somewhere, and that somewhere has to be stderr. Checked
  # first, so that "the report went to stdout" cannot be mistaken for "there is no
  # report" -- see the note on time_flag_unknown.
  grep -q '^time: process ' "${SCDIR}/q2.err" ||
    { sc_why="--time was accepted but no 'time: process' line reached stderr"; return 1; }
  # The solution must not move by one byte (SPEC 2.2, I-M1).
  cmp -s "${SCDIR}/q1.out" "${SCDIR}/q2.out" || { sc_why="stdout differs"; return 1; }
  # Nor may a timing line reach stdout by any route.
  grep -q '^time:' "${SCDIR}/q2.out" && { sc_why="a time: line reached stdout"; return 1; }
  # It must be off unless asked.
  grep -q '^time:' "${SCDIR}/q1.err" && { sc_why="timings appear without --time"; return 1; }
  # And it must not change the proof either, or the two tables are about two runs.
  cmp -s "${SCDIR}/q1.opb" "${SCDIR}/q2.opb" || { sc_why=".opb differs"; return 1; }
  cmp -s "${SCDIR}/q1.pbp" "${SCDIR}/q2.pbp" || { sc_why=".pbp differs"; return 1; }
  return 0
}

# The declared widths of a model, as "widest total". Both numbers are read out of the
# .fzn text rather than out of a solved model, because the whole point is to decide
# whether to start the solver at all.
declared_widths() {
  awk '{
         s = $0
         while (match(s, /var *-?[0-9]+\.\.-?[0-9]+/)) {
           d = substr(s, RSTART, RLENGTH)
           s = substr(s, RSTART + RLENGTH)
           sub(/var */, "", d)
           split(d, p, /\.\./)
           w = p[2] - p[1]
           if (w > maxw) maxw = w
           tot += w
         }
       }
       END { printf "%d %d\n", maxw + 0, tot + 0 }' "$1"
}

# Returns 1, and explains, when the model is over either cap.
guard() {
  local fzn="$1" maxw tot est
  read -r maxw tot < <(declared_widths "${fzn}")
  g_maxw="${maxw}"; g_tot="${tot}"
  est=$(( (tot * RSS_PER_UNIT_B) / 1048576 ))
  g_est="${est}"
  if [ "${maxw}" -gt "${WIDTH_CAP}" ] || [ "${est}" -gt "${MEM_CAP_MB}" ]; then
    return 1
  fi
  return 0
}

# ------------------------------------------------------------------ the floor
#
# The control every per-model timing has to be read against. Both numbers this
# harness reports are wall time around a whole process, so each carries one exec, one
# dynamic link and one runtime start-up. Measured here: the solver invoked with no
# arguments (it prints its usage and exits) and the checker asked for its version.
# Nothing below these is a measurement of solving or of checking, and on the small
# models in test/models/ almost the entire "solve ms" column IS this floor -- which
# is a fact about the instrument, and belongs at the top of its output rather than in
# a footnote nobody reads.
floor_of() {
  local i t0 t1 d best=0
  for ((i = 0; i < REPEATS; i++)); do
    t0="$(now_us)"
    "$@" > /dev/null 2>&1
    t1="$(now_us)"
    d=$((t1 - t0))
    if [ "${i}" -eq 0 ] || [ "${d}" -lt "${best}" ]; then best="${d}"; fi
  done
  printf '%s' "${best}"
}

checker_version="$("${VERIPB}" --version 2>&1 | head -1)"
load="$(cut -d' ' -f1-3 /proc/loadavg 2>/dev/null || echo '?')"
memtotal="$(awk '/MemTotal/ { printf "%d MB", $2 / 1024 }' /proc/meminfo 2>/dev/null || echo '?')"

echo "proof benchmark -- M3-T5. Four numbers, reported separately, never summed."
echo
echo "  date          $(date -Is)"
echo "  host          $(uname -sr) / $(nproc 2>/dev/null || echo '?') cpu / ${memtotal} RAM"
echo "  load average  ${load}"
echo "  checker       ${VERIPB}"
echo "                ${checker_version}"
echo "  repeats       ${REPEATS} (minimum reported), ${WARMUP} warmup discarded, run one at a time"
echo "  peak RSS      $([ "${HAVE_TIME}" -eq 1 ] && echo 'measured on a dedicated extra run, not on the timed repeats' || echo 'NOT AVAILABLE -- /usr/bin/time is missing')"
echo "  guard         refuse a declared width above ${WIDTH_CAP}, or an estimate above ${MEM_CAP_MB} MB$([ "${FORCE}" -eq 1 ] && echo ' -- OVERRIDDEN BY -Y')"
echo "  timeout       ${TIMEOUT}s per invocation"
solver_floor="$(floor_of "${SOLVER_A}")"
checker_floor="$(floor_of "${VERIPB}" --version)"
echo "  process floor $(ms "${solver_floor}") ms to start the solver and print its usage;"
echo "                $(ms "${checker_floor}") ms to start the checker and print its version."
echo "                A row at the floor is measuring process start-up, not work."
echo "                Since M1-T35 the solver also reports its own \`startup\` from the"
echo "                inside; the two are measured independently and should agree."
echo "  audit         BAGUETTE_PROOF_AUDIT=${BAGUETTE_PROOF_AUDIT:-<unset>} (the CLI turns it on by default)"

# ------------------------------------------------------------ run the self-checks
#
# Before anything is measured. See "self-checks" above for why each of these is a
# property of this harness's own columns rather than of the solver in general.
echo
echo "self-checks on ${SOLVER_A}, before any measurement:"
sc_model="${MODELS[0]}"

if time_flag_unknown "${SOLVER_A}" "${sc_model}"; then
  echo "  note  this binary rejects --time as an unknown option, so it predates M1-T35."
  echo "        The internal-timing table is SKIPPED; the wall-clock table below is"
  echo "        unaffected and complete."
else
  HAVE_TIME_FLAG=1
fi

if [ "${HAVE_TIME_FLAG}" -eq 1 ]; then
  sc_why=""
  time_flag_is_quiet "${SOLVER_A}" "${sc_model}"
  case $? in
    0) echo "  ok    --time reports on stderr, changes no byte of stdout, of the .opb or"
       echo "        of the .pbp, and is silent without it (SPEC 2.2, I-M1)" ;;
    2) echo "  FAIL  the self-check model could not be solved at all: ${sc_model}" >&2
       exit 2 ;;
    *) echo >&2
       echo "  FAIL  --time is NOT invisible: ${sc_why}." >&2
       echo "        SPEC 2.2 pins solution output byte for byte and test/expected/*.out is" >&2
       echo "        ground truth (I-M1). A solver whose timing flag moves stdout is" >&2
       echo "        contaminating the thing this benchmark exists to measure, and no" >&2
       echo "        number is taken from it. Nothing was measured." >&2
       exit 2 ;;
  esac
fi

sc_a=""; sc_b=""; sc_short_len=""; sc_long_len=""
opb_path_independence "${SOLVER_A}" "${sc_model}"
case $? in
  0) echo "  ok    .opb bytes do not depend on the path the model was given (M1-T37):"
     echo "        ${sc_a} B through a ${sc_short_len}-character path and a ${sc_long_len}-character one" ;;
  2) echo "  FAIL  the self-check model could not be solved at all: ${sc_model}" >&2
     exit 2 ;;
  *) SELFCHECK_OPB_PATH_DEP=1
     echo "  FAIL  .opb bytes DEPEND ON THE PATH (M1-T37): ${sc_a} B through a"
     echo "        ${sc_short_len}-character path, ${sc_b} B through a ${sc_long_len}-character one."
     echo "        The .opb header comment is carrying the path it was given instead of the"
     echo "        model's name, so the \`.opb B\` column below is a property of the caller's"
     echo "        directory as well as of the model. Deltas WITHIN this run are still sound"
     echo "        -- both configurations use the same path -- but these bytes must not be"
     echo "        compared with any figure measured elsewhere. This run will exit non-zero." ;;
esac

# Several Claude sessions build in this checkout at once, and a benchmark run beside
# a `dune build` measures the build. Said here rather than left to be wondered about
# when two runs disagree.
first_load="$(cut -d' ' -f1 /proc/loadavg 2>/dev/null || echo 0)"
case "${first_load}" in
  0.[0-4]*|0) ;;
  *) echo
     echo "  WARNING: load average is ${first_load}. Something else is running on this"
     echo "  machine, and these timings are measuring it too. Re-run when it is idle." ;;
esac
echo

# ------------------------------------------- the solver's own internal timings
#
# M1-T35. `baguette --time` prints one `time: <phase> <microseconds> us <what it is>`
# line per phase on stderr. This reads them back.
#
# THIS RUNS ON ITS OWN DEDICATED REPEATS, outside the timed ones, for exactly the
# reason the peak-RSS pass does: --time costs a dozen clock reads and a dozen lines of
# stderr, and none of that may land inside a number this harness prints as "solve ms".
# The wall-clock column is therefore measured by a binary invoked exactly as it was
# before M1-T35 existed, and stays comparable with bench/README.md's 2026-09-16 table.
#
# The repeat with the SMALLEST `process` total is the one reported, whole. Taking a
# per-phase minimum across different runs would give a row whose parts do not add up to
# any run that happened; the solve/verify columns above can do that because they are
# two independent measurements, and a phase breakdown cannot.
#
# WHAT THESE NUMBERS ARE. CPU time (user + system) of the solver process, from
# Sys.time. NOT wall time: bin/dune links no `unix`, and CPU time turns out to be the
# better instrument anyway because it excludes the descheduling this file warns about
# four sessions deep. Two things follow and are printed with the table rather than left
# here:
#   * a CPU number and a wall number are different measurements and their difference is
#     an UPPER BOUND on process overhead, not an exact figure;
#   * `search` still contains the proof lines emitted during the search. Only the .opb
#     write and the .pbp flush are separable proof-emission phases from the CLI. See
#     the note above `module Timing` in bin/main.ml.
declare -A PH

internal_measure() {
  local fzn="$1" bin="$2" fmt="$3" prefix="$4"
  local -a cmd=(timeout "${TIMEOUT}")
  [ -n "${fmt}" ] && cmd+=(env "BAGUETTE_PROOF_FORMAT=${fmt}")
  cmd+=("${bin}" "${fzn}" --proof "${prefix}" --time)
  local i txt proc best=-1
  for ((i = 0; i < REPEATS; i++)); do
    txt="$("${cmd[@]}" 2>&1 >/dev/null)"
    [ $? -ne 0 ] && return 1
    proc="$(printf '%s\n' "${txt}" | awk '$1 == "time:" && $2 == "process" { print $3 }')"
    case "${proc}" in '' | *[!0-9]*) return 1 ;; esac
    if [ "${best}" -lt 0 ] || [ "${proc}" -lt "${best}" ]; then
      best="${proc}"
      PH=()
      while read -r k v; do PH["${k}"]="${v}"; done < <(
        printf '%s\n' "${txt}" | awk '$1 == "time:" && $4 == "us" { print $2, $3 }'
      )
    fi
  done
  [ -n "${PH[process]:-}" ] || return 1
  return 0
}

# Sums of PH keys, tolerating a phase that did not run. The groupings are stated in the
# table's own legend so that nothing is regrouped silently.
phsum() {
  local t=0 k
  for k in "$@"; do t=$((t + ${PH[$k]:-0})); done
  printf '%s' "${t}"
}

# ------------------------------------------------------------------ one measurement
#
# Sets, for the model in $1 under the configuration in $2/$3 (binary, format):
#   m_opb m_pbp  bytes, and m_stable=1 if every repeat produced identical bytes
#   m_solve m_verify        minimum microseconds
#   m_solve_hi m_verify_hi  maximum microseconds, which is where the spread comes from
#   m_srss m_vrss           peak RSS in kB of solve and of verify
#   m_lines m_longest m_rup m_pol m_levels m_depth   proof shape, and the tree proxy
#   m_fmt        the format the .pbp says it is, read from the file, not from the env
#   m_status     ok | REJECTED | SOLVER-FAILED | REFUSED
measure() {
  local fzn="$1" bin="$2" fmt="$3"
  local base prefix i t0 t1 rc
  base="$(basename "${fzn}" .fzn)"
  prefix="${OUTDIR}/${base}"

  m_status=ok
  m_stable=1
  m_solve=0; m_verify=0; m_solve_hi=0; m_verify_hi=0
  m_srss=""; m_vrss=""

  if ! guard "${fzn}"; then
    if [ "${FORCE}" -eq 0 ]; then
      m_status="REFUSED (widest declared domain ${g_maxw}, total ${g_tot}, estimated peak ${g_est} MB; -Y to force)"
      return 1
    fi
    echo "  -Y: running ${base} anyway -- widest declared domain ${g_maxw}, estimated peak ${g_est} MB"
  fi

  local -a solve=(timeout "${TIMEOUT}")
  [ -n "${fmt}" ] && solve+=(env "BAGUETTE_PROOF_FORMAT=${fmt}")
  solve+=("${bin}" "${fzn}" --proof "${prefix}")
  local -a verify=(timeout "${TIMEOUT}" "${VERIPB}" "${prefix}.opb" "${prefix}.pbp")

  for ((i = 0; i < WARMUP; i++)); do
    "${solve[@]}" > "${prefix}.stdout" 2> "${prefix}.stderr" || { m_status=SOLVER-FAILED; return 1; }
    "${verify[@]}" > "${prefix}.veripb" 2>&1 || { m_status=REJECTED; return 1; }
  done

  # The memory pass. Separate from the timed repeats on purpose: /usr/bin/time forks
  # and its cost would otherwise be inside a number called "solve ms".
  if [ "${HAVE_TIME}" -eq 1 ]; then
    m_srss="$(peak_rss_kb "${solve[@]}")"
    m_vrss="$(peak_rss_kb "${verify[@]}")"
  fi

  # The internal-timing pass (M1-T35), also outside the timed repeats. Skipped
  # silently per model only when the binary has no --time at all, which the preflight
  # has already announced once.
  m_iok=0
  if [ "${HAVE_TIME_FLAG}" -eq 1 ] && internal_measure "${fzn}" "${bin}" "${fmt}" "${prefix}"; then
    m_iok=1
    m_i_startup="$(phsum startup)"
    m_i_parse="$(phsum args parse)"
    m_i_compile="$(phsum compile)"
    m_i_opb="$(phsum opb)"
    m_i_search="$(phsum search)"
    m_i_pbp="$(phsum proofopen pbpclose)"
    m_i_rest="$(phsum output other)"
    m_i_inmain="$(phsum inmain)"
  fi

  local first_opb="" first_pbp="" opb pbp
  for ((i = 0; i < REPEATS; i++)); do
    t0="$(now_us)"
    "${solve[@]}" > "${prefix}.stdout" 2> "${prefix}.stderr"
    rc=$?
    t1="$(now_us)"
    [ "${rc}" -ne 0 ] && { m_status=SOLVER-FAILED; return 1; }
    local d=$((t1 - t0))
    if [ "${i}" -eq 0 ] || [ "${d}" -lt "${m_solve}" ]; then m_solve="${d}"; fi
    if [ "${d}" -gt "${m_solve_hi}" ]; then m_solve_hi="${d}"; fi

    opb="$(stat -c%s "${prefix}.opb")"
    pbp="$(stat -c%s "${prefix}.pbp")"
    # A size that is not reproducible cannot be compared with another run's size.
    # Checked rather than assumed; the answer today is that it is stable everywhere.
    if [ "${i}" -eq 0 ]; then first_opb="${opb}"; first_pbp="${pbp}"
    elif [ "${opb}" != "${first_opb}" ] || [ "${pbp}" != "${first_pbp}" ]; then m_stable=0; fi

    t0="$(now_us)"
    "${verify[@]}" > "${prefix}.veripb" 2>&1
    rc=$?
    t1="$(now_us)"
    [ "${rc}" -ne 0 ] && { m_status=REJECTED; return 1; }
    d=$((t1 - t0))
    if [ "${i}" -eq 0 ] || [ "${d}" -lt "${m_verify}" ]; then m_verify="${d}"; fi
    if [ "${d}" -gt "${m_verify_hi}" ]; then m_verify_hi="${d}"; fi
  done

  m_opb="${first_opb}"
  m_pbp="${first_pbp}"

  # What the proof SAYS it is. Reading the env var back would only report what we
  # asked for; D-0023's whole lesson is that the artefact is the authority.
  m_fmt="$(head -1 "${prefix}.pbp" | awk '{print $NF}')"

  m_lines="$(wc -l < "${prefix}.pbp" | tr -d ' ')"
  m_longest="$(awk '{ if (length > n) n = length } END { print n + 0 }' "${prefix}.pbp")"
  # Rule counts. The anchor has to admit BOTH formats: 3.0 introduces every derived
  # constraint with a label (`@c9 rup ...`) and 2.0 does not (`rup ...`), so a grep
  # for " rup " counts 31 lines under 3.0 and 0 under the same proof in 2.0 -- which
  # is what the first draft of this script did, and it is D-0025's vacuous-assertion
  # trap wearing a benchmark's clothes. `Writer.strip_label` is the authority on the
  # optional prefix; this regex is its shell transcription and nothing else may
  # assume a spelling.
  m_rup="$(grep -cE '^(@[^ ]+ )?rup ' "${prefix}.pbp")"
  m_pol="$(grep -cE '^(@[^ ]+ )?pol ' "${prefix}.pbp")"
  # Node count is not instrumented in the solver, so this is a PROXY and is labelled
  # as one everywhere it is printed: Search.branch emits one level marker per child it
  # explores, in both proof formats (Writer.level_marker). It moves when the search
  # tree moves, which is the question it is here to answer -- it is not a node count.
  m_levels="$(grep -cE '^(% level |# )[0-9]+' "${prefix}.pbp")"
  m_depth="$(grep -oE '^(% level |# )[0-9]+' "${prefix}.pbp" | grep -oE '[0-9]+$' | sort -n | tail -1)"
  [ -z "${m_depth}" ] && m_depth=0

  [ "${KEEP}" -eq 0 ] && rm -f "${prefix}.stdout" "${prefix}.stderr" "${prefix}.veripb" \
                               "${prefix}.opb" "${prefix}.pbp"
  return 0
}

# ------------------------------------------------------------------ the run

hdr() {
  printf '%-22s %10s %10s %9s %6s %9s %6s %7s %7s %7s %5s %5s %5s %4s\n' \
    "model" ".opb B" ".pbp B" "solve ms" "+-%" "verify ms" "+-%" "slvMB" "vrfMB" "longest" "lines" "rup" "pol" "lvl"
  printf '%-22s %10s %10s %9s %6s %9s %6s %7s %7s %7s %5s %5s %5s %4s\n' \
    "----------------------" "----------" "----------" "---------" "------" "---------" "------" \
    "-------" "-------" "-------" "-----" "-----" "-----" "----"
}

declare -A A_opb A_pbp A_solve A_verify A_lines A_longest A_rup A_pol A_levels A_depth A_fmt A_stable A_srss A_vrss
declare -A B_opb B_pbp B_solve B_verify B_lines B_longest B_rup B_pol B_levels B_depth B_fmt B_stable B_srss B_vrss
declare -A A_ssp A_vsp B_ssp B_vsp
declare -a ITAB=()
failed=0
refused=0
declare -a NAMES=()

ihdr() {
  printf '%-22s %9s %9s %8s %9s %9s %9s %8s %7s %9s %8s\n' \
    "model" "wall us" "startup" "parse" "compile" "opb" "search" "pbp" "rest" "inmain" "notslv%"
  printf '%-22s %9s %9s %8s %9s %9s %9s %8s %7s %9s %8s\n' \
    "----------------------" "---------" "---------" "--------" "---------" "---------" \
    "---------" "--------" "-------" "---------" "--------"
}

run_config() {
  local which="$1" bin="$2" fmt="$3" label="$4"
  local fzn base
  ITAB=()
  echo "configuration ${which}: ${label}"
  echo "  solver  ${bin}"
  echo "  format  BAGUETTE_PROOF_FORMAT=${fmt:-<unset, solver default>}"
  echo
  hdr
  for fzn in "${MODELS[@]}"; do
    base="$(basename "${fzn}" .fzn)"
    if ! measure "${fzn}" "${bin}" "${fmt}"; then
      printf '%-22s %s\n' "${base}" "${m_status} -- no timings reported for this model"
      case "${m_status}" in REFUSED*) refused=$((refused + 1)) ;; *) failed=$((failed + 1)) ;; esac
      continue
    fi
    local ssp vsp
    ssp="$(pct $((m_solve_hi - m_solve)) "${m_solve}")"
    vsp="$(pct $((m_verify_hi - m_verify)) "${m_verify}")"
    printf '%-22s %10s %10s %9s %5s%% %9s %5s%% %7s %7s %7s %5s %5s %5s %4s%s\n' \
      "${base}" "${m_opb}" "${m_pbp}" "$(ms "${m_solve}")" "${ssp}" \
      "$(ms "${m_verify}")" "${vsp}" "$(mb "${m_srss}")" "$(mb "${m_vrss}")" \
      "${m_longest}" "${m_lines}" "${m_rup}" "${m_pol}" "${m_levels}" \
      "$([ "${m_stable}" -eq 0 ] && printf '  !! proof bytes NOT reproducible across repeats')"
    if [ "${which}" = "A" ]; then
      NAMES+=("${base}")
      A_opb[$base]=$m_opb; A_pbp[$base]=$m_pbp; A_solve[$base]=$m_solve; A_verify[$base]=$m_verify
      A_lines[$base]=$m_lines; A_longest[$base]=$m_longest; A_rup[$base]=$m_rup; A_pol[$base]=$m_pol
      A_levels[$base]=$m_levels; A_depth[$base]=$m_depth; A_fmt[$base]=$m_fmt; A_stable[$base]=$m_stable
      A_ssp[$base]=$ssp; A_vsp[$base]=$vsp; A_srss[$base]=$m_srss; A_vrss[$base]=$m_vrss
    else
      B_opb[$base]=$m_opb; B_pbp[$base]=$m_pbp; B_solve[$base]=$m_solve; B_verify[$base]=$m_verify
      B_lines[$base]=$m_lines; B_longest[$base]=$m_longest; B_rup[$base]=$m_rup; B_pol[$base]=$m_pol
      B_levels[$base]=$m_levels; B_depth[$base]=$m_depth; B_fmt[$base]=$m_fmt; B_stable[$base]=$m_stable
      B_ssp[$base]=$ssp; B_vsp[$base]=$vsp; B_srss[$base]=$m_srss; B_vrss[$base]=$m_vrss
    fi
    if [ "${m_iok}" -eq 1 ]; then
      ITAB+=("$(printf '%-22s %9s %9s %8s %9s %9s %9s %8s %7s %9s %7s%%' \
        "${base}" "${m_solve}" "${m_i_startup}" "${m_i_parse}" "${m_i_compile}" \
        "${m_i_opb}" "${m_i_search}" "${m_i_pbp}" "${m_i_rest}" "${m_i_inmain}" \
        "$(pct $((m_solve - m_i_inmain)) "${m_solve}")")")
    fi
    if [ -n "${TSV}" ]; then
      printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "${which}" "${base}" "${m_fmt}" "${m_opb}" "${m_pbp}" "${m_solve}" "${m_verify}" \
        "${m_srss:-}" "${m_vrss:-}" "${m_lines}" "${m_longest}" "${m_rup}" "${m_pol}" \
        "${m_levels}" "${m_depth}" "${m_stable}" >> "${TSV}"
      printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "${which}" "${base}" "${m_i_startup:-}" "${m_i_parse:-}" "${m_i_compile:-}" \
        "${m_i_opb:-}" "${m_i_search:-}" "${m_i_pbp:-}" "${m_i_rest:-}" \
        "${m_i_inmain:-}" >> "${TSV}.internal"
    fi
  done
  echo

  if [ "${#ITAB[@]}" -gt 0 ]; then
    echo "  the solver's own internal timings, configuration ${which} (M1-T35)."
    echo "  MICROSECONDS OF CPU TIME inside the solver process, from \`baguette --time\`,"
    echo "  measured on dedicated runs OUTSIDE the timed repeats above -- so the wall-clock"
    echo "  table is still produced by a binary invoked exactly as it was before --time"
    echo "  existed. The repeat with the smallest total is reported whole, so the columns"
    echo "  add up to \`inmain\` rather than being per-column minimums of different runs."
    echo
    ihdr
    printf '%s\n' "${ITAB[@]}"
    echo
    echo "    wall us   the \"solve ms\" column above, in microseconds. WALL time around the"
    echo "              whole process: exec, dynamic link, runtime start, all of the below,"
    echo "              and exit. Every other column in this table is CPU time."
    echo "    startup   CPU burned before main's first statement: exec, dynamic link, OCaml"
    echo "              runtime start-up, module initialisers. THIS is M3-T5's process floor,"
    echo "              measured from inside instead of inferred from a null model."
    echo "    parse     argument handling + Builder.of_file (lex, parse, build Model.t)"
    echo "    compile   Compile.compile: store, engine, encoding. No I/O, no proof."
    echo "    opb       Encoding.write_opb: the .opb built, written and closed."
    echo "    search    Search.solve: propagation and search, AND THE PROOF LINES EMITTED"
    echo "              DURING THEM. These are not separable from the CLI -- every emission"
    echo "              point is inside lib/core/justify.ml and lib/proof/writer.ml. A claim"
    echo "              about propagation cost cannot be read off this column alone."
    echo "    pbp       proof channel opened + Encoding.start_proof + the final .pbp flush."
    echo "    rest      printing the solution, and whatever in main is in no phase."
    echo "    inmain    startup excluded; the sum of parse..rest exactly."
    echo "    notslv%   (wall - inmain) / wall. An UPPER BOUND on the share of the wall-clock"
    echo "              column that is not the solver's own work, because wall and inmain are"
    echo "              different clocks and CPU time is never above wall time. A row near"
    echo "              100% is a row whose \"solve ms\" is a timing of exec."
    echo
  fi

  local fmts
  fmts="$(if [ "${which}" = "A" ]; then printf '%s\n' "${A_fmt[@]:-}"; else printf '%s\n' "${B_fmt[@]:-}"; fi | sort -u | tr '\n' ' ')"
  fmts="$(printf '%s' "${fmts}" | tr -s ' ')"
  [ -z "${fmts}" ] || [ "${fmts}" = " " ] && fmts="(nothing was measured)"
  echo "  proof format actually emitted, read from each .pbp's own version line: ${fmts}"
  echo
}

if [ -n "${TSV}" ]; then
  printf 'config\tmodel\tformat\topb_bytes\tpbp_bytes\tsolve_us\tverify_us\tsolve_rss_kb\tverify_rss_kb\tlines\tlongest\trup\tpol\tlevels\tdepth\tbytes_reproducible\n' > "${TSV}"
  # The internal timings go to their OWN file, not extra columns here, because they are
  # a different clock (CPU, not wall) measured on different runs. Putting two clocks in
  # one row is how they get subtracted from each other by someone reading it later.
  printf 'config\tmodel\tstartup_cpu_us\tparse_cpu_us\tcompile_cpu_us\topb_cpu_us\tsearch_cpu_us\tpbp_cpu_us\trest_cpu_us\tinmain_cpu_us\n' > "${TSV}.internal"
fi

run_config A "${SOLVER_A}" "${FORMAT_A}" "${LABEL_A}"
[ "${COMPARE}" -eq 1 ] && run_config B "${SOLVER_B}" "${FORMAT_B}" "${LABEL_B}"

# ------------------------------------------------------------------ the comparison
#
# Each column is compared on its own and the verdict is per column, because the whole
# reason this row exists is that they move independently. A delta inside the measured
# spread of EITHER configuration is printed as "noise", not as a small win.
if [ "${COMPARE}" -eq 1 ]; then
  echo "${LABEL_B} against ${LABEL_A}, one column at a time. A timing delta no larger than"
  echo "the spread measured above is NOISE and is labelled so; it is not a small win."
  echo
  printf '%-22s %12s %12s %14s %14s %10s\n' "model" ".opb" ".pbp" "solve" "verify" "tree(lvl)"
  printf '%-22s %12s %12s %14s %14s %10s\n' "----------------------" "------------" "------------" \
    "--------------" "--------------" "----------"
  for base in "${NAMES[@]}"; do
    [ -z "${B_opb[$base]:-}" ] && continue
    d_opb="$(pct $(( ${B_opb[$base]} - ${A_opb[$base]} )) "${A_opb[$base]}")"
    d_pbp="$(pct $(( ${B_pbp[$base]} - ${A_pbp[$base]} )) "${A_pbp[$base]}")"
    d_solve="$(pct $(( ${B_solve[$base]} - ${A_solve[$base]} )) "${A_solve[$base]}")"
    d_verify="$(pct $(( ${B_verify[$base]} - ${A_verify[$base]} )) "${A_verify[$base]}")"
    # "inside the spread" uses the larger of the two configurations' spreads.
    noise_s=""; noise_v=""
    lim_s="${A_ssp[$base]}"; [ "${B_ssp[$base]}" -gt "${lim_s}" ] 2>/dev/null && lim_s="${B_ssp[$base]}"
    lim_v="${A_vsp[$base]}"; [ "${B_vsp[$base]}" -gt "${lim_v}" ] 2>/dev/null && lim_v="${B_vsp[$base]}"
    a_s="${d_solve#-}"; a_v="${d_verify#-}"
    [ "${a_s}" -le "${lim_s}" ] 2>/dev/null && noise_s=" noise"
    [ "${a_v}" -le "${lim_v}" ] 2>/dev/null && noise_v=" noise"
    tree="same"
    [ "${B_levels[$base]}" != "${A_levels[$base]}" ] && tree="CHANGED"
    printf '%-22s %11s%% %11s%% %8s%%%-6s %8s%%%-6s %10s\n' \
      "${base}" "${d_opb}" "${d_pbp}" "${d_solve}" "${noise_s}" "${d_verify}" "${noise_v}" "${tree}"
  done
  echo
  echo "tree(lvl) is the search-tree proxy. Where it says CHANGED the two configurations"
  echo "did not explore the same tree, and NONE of the other four columns is a"
  echo "like-for-like comparison of proof density on that model."
fi

# ------------------------------------------------------------------ footer

echo
echo "how to read this"
echo "  * Four numbers, four columns, no total. .opb bytes, .pbp bytes and verify"
echo "    time can move in opposite directions at an identical search tree -- GCS"
echo "    measured 5.9x smaller and 3.5x slower at once. A change that improves one"
echo "    and is silent about the others has not been measured."
echo "  * Every timing is the MINIMUM of ${REPEATS} sequential runs. The +-% beside it is"
echo "    (max - min) / min over those runs: the noise floor for that measurement on"
echo "    this machine, today. A difference smaller than it is noise. Say so."
echo "  * slvMB / vrfMB are peak RSS, from a dedicated run outside the timed repeats."
echo "    On this box memory is the resource that fails first: a wide-domain model"
echo "    costs about 1.5 kB of RSS per unit of declared width against 63 bytes of"
echo "    .opb, so a size-and-time-only benchmark would call swapping 'slow'."
echo "  * solve and verify are separate on purpose, and so is lvl (the search-tree"
echo "    proxy: one level marker per branch child explored -- node count is not"
echo "    instrumented). A proof that grew because the search changed and a proof that"
echo "    grew because each pruning costs more lines need opposite fixes."
echo "  * Byte counts come from a proof the checker ACCEPTED. A rejected proof is"
echo "    reported as REJECTED with no timings at all."
echo "  * The wall-clock table and the internal table are two different clocks and"
echo "    they are printed side by side rather than one replacing the other. Wall time"
echo "    around a process is what a user waits for and it will always carry the"
echo "    process floor; CPU time inside the solver is what a change to the solver can"
echo "    move. The pair is the measurement: 'solve ms' alone cannot tell a faster"
echo "    propagator from a faster exec, which is precisely what M3-T5 ran into."
echo "  * Do NOT subtract an internal number from a wall number and call the remainder"
echo "    a measurement of overhead. CPU time is never above wall time, so the"
echo "    remainder is an upper bound. notslv% is labelled as one."
echo "  * The internal 'search' column still contains the proof lines written during"
echo "    the search. Splitting it needs an accumulator inside lib/proof/writer.ml,"
echo "    which M1-T35 did not own. Until that exists, a statement of the form"
echo "    'propagation costs X' is not supported by this harness."

if [ "${SELFCHECK_OPB_PATH_DEP}" -eq 1 ]; then
  echo
  echo "SELF-CHECK FAILED: .opb bytes depend on the path the model was given (M1-T37)."
  echo "  The '.opb B' column above is a property of the caller's directory as well as of"
  echo "  the model. Deltas within this run are sound; the absolute bytes must not be"
  echo "  quoted against any figure measured from another directory. Exiting non-zero so"
  echo "  that this cannot be scrolled past."
fi

if [ "${refused}" -gt 0 ]; then
  echo
  echo "${refused} model(s) were REFUSED by the width/memory guard and did not run at all."
  echo "  That is the guard working, not a failure. -Y forces them; read bench/README.md"
  echo "  first, and do not force one while other sessions are using this machine."
fi
if [ "${failed}" -gt 0 ]; then
  echo
  echo "${failed} model(s) did not produce a verified proof. Their rows carry no numbers."
  exit 1
fi
[ "${SELFCHECK_OPB_PATH_DEP}" -eq 1 ] && exit 1
exit 0
