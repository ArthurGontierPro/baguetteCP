#!/bin/sh
# Solve every model TWICE and require the .opb, .pbp and stdout to be byte-identical
# across the two runs (the determinism half of M2-T12).
#
#   scripts/check_determinism.sh              the check (`make determinism`)
#   scripts/check_determinism.sh --self-test  proves the check can fail; runs first
#
# Exit 0 when every model's two runs agree (or the self-test saw the check fail on a
# planted difference), non-zero otherwise. It does not build the solver.
#
# Why this exists, and what it deliberately does NOT do.
#
# M2-T11 reported "60/60 artefacts byte-identical, hashes shown" and was telling the
# truth. The defect was that the measurement was a ONE-OFF, never committed as a check --
# so nothing re-measured it, and it rotted: the suite went from 20 models to 34 and the
# newest fourteen had never been in any comparison. A number in a roadmap row is not a
# control.
#
# THIS DOES NOT COMPARE AGAINST A STORED GOLDEN DIGEST, and that is the central design
# choice. A committed hash of the suite's artefacts would be wrong on the next legitimate
# proof change -- M1-T29 moved 14 of 34 .pbp files on 2026-09-17, correctly -- and a check
# that has to be re-blessed every time it fires teaches people to re-bless it without
# looking. What is checked instead is SELF-RELATIVE: run N and run N+1 of the same binary
# on the same model must agree. That property is true for every correct version of this
# solver and needs no maintenance.
#
# Carry agent-lazy2's warning with it, because it is the reason not to overclaim what a
# green run here means: BYTE-IDENTITY IS EVIDENCE OF NO CHANGE, NEVER OF CORRECTNESS. With
# linear.ml's trail walk deliberately reversed, every model artefact stayed identical and
# 20/20 models passed; only the unit suite went red. So this catches nondeterminism -- hash
# iteration order, an address leaking into output, an uninitialised read, a timestamp -- and
# nothing else. It is not a regression net for the proof.
#
# The other half of M2-T12 is NOT here. Checking that seeded branching leaves the suite's
# solutions valid needs `random_order`, which no CLI flag reaches (bin/main.ml has no seed
# option) and test_random.ml fuzzes generated models rather than the fixed suite. That half
# has to live in a test binary, and waits for lib/core to be free.
#
# THE REAL INSTANCES (D-0264). The test models are too small for the collector to run more
# than a few cycles, so a proof that depended on the GC (a table dropped under pressure, an
# address reaching a hash, a timer that forces a cycle) would pass the loop over them every
# time. So four instances of the differential lane's corpus (bench/diff/corpus, read here and
# never written) are solved twice more at a small node budget, each run under a DIFFERENT
# runtime: OCAMLRUNPARAM=s=16k,o=40 (a 128 KB minor heap and an eager major GC) and
# s=256k,o=400 (a 2 MB minor heap and a lazy one). bin/main.ml sizes the minor heap from the
# address-space limit unless OCAMLRUNPARAM names one, so the gate under `ulimit -v` and a
# campaign without it already run two runtimes. (Not larger: the runtime reserves the minor
# heap for 128 domains, and s=8M asks 8 GB of address space, which the gate's 4 GB cap
# refuses with "Not enough heap memory to reserve minor heaps".) The four cover the clause path with PB rows,
# cumulative, alldiff and the bits arm (atoms minted on demand), about 10 s together. The
# .opb, .pbp and stdout must agree, exactly as for the models.
#
# BOTH SEARCHES (M19-config-T1, D-0261). The models and the four instances are each run under
# the fixed search (--fixed-search) and under the default, the free search since D-0261, whose
# restarts, activity scores and saved phases must not depend on the clock, an address or the
# collector either. Both arms together, models and instances, take about 32 s on fataepyc-06.
#
# THE CONTRACT, AND ITS ONE EXCEPTION. The proof is a function of the binary, the input and
# the options for a run that ends on its own or at BAGUETTE_NODE_LIMIT. A run ended by an
# ASYNCHRONOUS stop (--time-limit, a signal such as `timeout`'s SIGTERM, SIGINT or SIGXCPU,
# or the heap budget --max-heap-mb) ends with a valid proof cut wherever the stop found it,
# and that point moves from run to run by design (Writer.conclude_interrupted). D-0264 is the
# record of a comparison that forgot this: two Challenge instances "not reproducible" were a
# `timeout 900` and an 8 GB heap budget landing at different points of the same node. So
# every real-instance run here must end by the node limit or on its own: its `limit:` line,
# when it has one, must say `fired=none signal=none`; otherwise the comparison is VOID, and
# that is a failure, never a pass.
#
# --self-test proves the check can fail, and runs FIRST on every gate. Same discipline as
# scripts/check_test_widths.py and scripts/check_fmt.sh, for the same reason: a guard
# nobody has watched fail is not yet a guard.

set -e

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SOLVER="${BAGUETTE:-${ROOT}/_build/default/bin/main.exe}"
MEM_CAP_KB="${BAGUETTE_MEM_CAP_KB:-4000000}"

# The suites already apply this; a script invoked directly must too (CLAUDE.md, and three
# memory-ceiling incidents on 2026-09-16).
#
# M7-T1: BAGUETTE_MEM_CAP_KB=none skips it entirely, matching run_model_tests.sh and
# verify_proof.sh, which already had that escape. This cap is about GATE TIME on a shared
# 15 GB development box; it is not a statement about what the solver can do, and the
# corpus node sets `none`. On the dev box a run that dies against it is a finding.
if [ "${MEM_CAP_KB}" != "none" ]; then
  _cur="$(ulimit -v)"
  if [ "${_cur}" = "unlimited" ] || { [ "${_cur}" -gt "${MEM_CAP_KB}" ] 2>/dev/null; }; then
    ulimit -v "${MEM_CAP_KB}" 2>/dev/null || true
  fi
fi

# M6-T5: the same reading of test/models/PENDING that scripts/run_model_tests.sh uses
# (its [is_pending], same file, same comment convention). Kept as a second small copy
# rather than a shared library because these two scripts have no other coupling and a
# sourced helper would be a new failure mode for both.
PENDING_FILE="${ROOT}/test/models/PENDING"
is_pending() {
  [ -f "${PENDING_FILE}" ] || return 1
  grep -v '^[[:space:]]*#' "${PENDING_FILE}" 2>/dev/null \
    | awk '{print $1}' | grep -qx "$1"
}

# The search both runs use (M19-config-T1, D-0261); run_check sets it per arm.
SEARCH="--fixed-search"

# One model, two runs, three artefacts compared. Echoes the differing kind on failure.
# $1 model path, $2 scratch dir. Prints nothing when identical.
compare_two_runs() {
  fzn="$1"; d="$2"
  base="$(basename "${fzn}" .fzn)"
  rc1=0; rc2=0
  # The search (M19-config-T1, D-0261), SEARCH, comes AFTER the proof prefix: the
  # self-test's flaky wrapper reads --proof PREFIX as arguments 2 and 3.
  for run in 1 2; do
    timeout 300 "${SOLVER}" "${fzn}" --proof "${d}/${base}.${run}" ${SEARCH} \
      > "${d}/${base}.${run}.out" 2> "${d}/${base}.${run}.err" || eval "rc${run}=\$?"
  done
  # M6-T5. A model listed in test/models/PENDING is known not to work yet, and a
  # non-zero exit from it is the EXPECTED outcome -- but it is still an outcome this
  # check has an opinion about, because "fails the same way twice" is exactly the
  # property this script exists to verify. So for a pending model a non-zero exit is
  # not a failure; a non-zero exit that DIFFERS between the two runs is.
  #
  # For every other model a non-zero exit is still a failure, and it is reported as
  # one rather than silently folded into the artefact comparison.
  if [ "${rc1}" -ne 0 ] || [ "${rc2}" -ne 0 ]; then
    if is_pending "${base}"; then
      if [ "${rc1}" -ne "${rc2}" ]; then
        echo "     ${base}: listed in PENDING, but exit status DIFFERS between two runs"
        echo "       (${rc1} then ${rc2}) -- that is nondeterminism, not a pending model"
        return 1
      fi
    else
      echo "     run of ${base} did not exit 0 (${rc1}, ${rc2}):"
      sed 's/^/       /' "${d}/${base}.1.err" | head -5
      return 1
    fi
  fi
  rc=0
  for kind in opb pbp; do
    # A model that exited non-zero may have written neither artefact. Two absences
    # agree; one absence does not, and cmp reports that as a difference, which is
    # the answer we want.
    if [ ! -e "${d}/${base}.1.${kind}" ] && [ ! -e "${d}/${base}.2.${kind}" ]; then
      continue
    fi
    if ! cmp -s "${d}/${base}.1.${kind}" "${d}/${base}.2.${kind}"; then
      echo "     ${base}: .${kind} DIFFERS between two runs of the same binary"
      rc=1
    fi
  done
  if ! cmp -s "${d}/${base}.1.out" "${d}/${base}.2.out"; then
    echo "     ${base}: stdout DIFFERS between two runs of the same binary"
    rc=1
  fi
  return $rc
}

# D-0264. True when the run whose stderr is $1 ended on its own (no `limit:` line) or at the
# node limit (`fired=none signal=none`); false for a clock, a signal or the heap budget.
stopped_by_itself() {
  l="$(grep '^limit:' "$1" | tail -1)"
  [ -z "$l" ] && return 0
  case "$l" in
    *"fired=none signal=none"*) return 0 ;;
    *) return 1 ;;
  esac
}

# The real instances (D-0264, see the header): name, node budget, extra flags ("-": none,
# and a flag's value follows a comma: --bits-above,0 is `--bits-above 0`).
REAL_INSTANCES="
2012_parity-learning_48_24_6.2 1000 -
2013_rcpsp_12 1000 -
2018_soccer-computational_xIGData_24_16_14_2 800 -
2011_cyclic-rcpsp_easy_6 300 --bits-above,0
"

# One real instance, two runs under two GC settings. $1 name, $2 budget, $3 flags, $4 dir.
compare_real() {
  name="$1"; budget="$2"; flags="$3"; d="$4"
  [ "${flags}" = "-" ] && flags=""
  flags="$(echo "${flags}" | tr ',' ' ')"
  gz="${ROOT}/bench/diff/corpus/${name}.fzn.gz"
  if [ ! -f "${gz}" ]; then
    echo "     ${name}: ${gz#"${ROOT}"/} is missing, so the real-instance check cannot run"
    return 1
  fi
  gunzip -c "${gz}" > "${d}/${name}.fzn"
  run=0
  for gc in "s=16k,o=40" "s=256k,o=400"; do
    run=$((run + 1))
    # The caller's BAGUETTE_* settings are not this check's (the diff lane's rule): a stray
    # BAGUETTE_RETENTION in a terminal must not become the configuration compared.
    # shellcheck disable=SC2086
    if ! (
      for v in $(env | sed -n 's/^\(BAGUETTE_[A-Za-z0-9_]*\)=.*/\1/p'); do unset "$v"; done
      BAGUETTE_NODE_LIMIT="${budget}" OCAMLRUNPARAM="${gc}" \
        timeout 300 "${SOLVER}" "${d}/${name}.fzn" ${SEARCH} ${flags} --stats --proof "${d}/${name}.${run}" \
        > "${d}/${name}.${run}.out" 2> "${d}/${name}.${run}.err"
    ); then
      echo "     ${name} (OCAMLRUNPARAM=${gc}) did not exit 0:"
      grep -v '^\(stats\|limit\|time\):' "${d}/${name}.${run}.err" | tail -3 | sed 's/^/       /'
      return 1
    fi
    if ! stopped_by_itself "${d}/${name}.${run}.err"; then
      echo "     ${name} (OCAMLRUNPARAM=${gc}): stopped by a clock, a signal or the heap budget,"
      echo "       not by the node limit, so its proof is not expected to reproduce and the"
      echo "       comparison is VOID (D-0264): $(grep '^limit:' "${d}/${name}.${run}.err" | cut -c1-160)"
      return 1
    fi
  done
  rc=0
  for kind in opb pbp; do
    if ! cmp -s "${d}/${name}.1.${kind}" "${d}/${name}.2.${kind}"; then
      echo "     ${name}: .${kind} DIFFERS between OCAMLRUNPARAM=s=16k,o=40 and s=256k,o=400"
      rc=1
    fi
  done
  if ! cmp -s "${d}/${name}.1.out" "${d}/${name}.2.out"; then
    echo "     ${name}: stdout DIFFERS between OCAMLRUNPARAM=s=16k,o=40 and s=256k,o=400"
    rc=1
  fi
  rm -f "${d}/${name}".*
  return $rc
}

self_test() {
  # A solver wrapper that is correct but NOT deterministic: it appends a changing comment
  # to the .opb after the real solver has written it. If the check cannot see that, it
  # cannot see the class of bug it exists for.
  d="$(mktemp -d)"
  trap 'rm -rf "$d"' EXIT INT TERM
  if [ ! -x "${SOLVER}" ]; then
    echo "FAIL determinism self-test: no solver at ${SOLVER} -- run \`dune build bin/\` first."
    echo "     (A missing binary is a FAILURE here, not a skip: dune runtest does not"
    echo "      build bin/main.exe, so a stale or absent one is exactly the trap"
    echo "      CLAUDE.md records.)"
    return 1
  fi
  cat > "$d/flaky" <<EOF
#!/bin/sh
"${SOLVER}" "\$@"
_rc=\$?
# --proof PREFIX is argument 2 and 3 as this script calls it.
if [ "\$2" = "--proof" ]; then printf '* nondeterministic marker %s\n' "\$\$" >> "\$3.opb"; fi
exit \$_rc
EOF
  chmod +x "$d/flaky"

  # (1) It must CATCH the flaky wrapper.
  if SOLVER="$d/flaky" compare_two_runs "${ROOT}/test/models/trivial_sat.fzn" "$d" \
       > "$d/flaky.log" 2>&1; then
    echo "FAIL determinism self-test: a deliberately nondeterministic solver was ACCEPTED."
    echo "     The check below would therefore pass on a solver whose artefacts change"
    echo "     run to run, which is the whole property M2-T12 exists to hold."
    return 1
  fi
  if ! grep -q 'DIFFERS' "$d/flaky.log"; then
    echo "FAIL determinism self-test: the flaky solver failed, but not for the right"
    echo "     reason -- no '.opb DIFFERS' line. It may have failed to run at all, in"
    echo "     which case this lane proves nothing."
    sed 's/^/       /' "$d/flaky.log" | head -5
    return 1
  fi

  # (2) And it must ACCEPT the real one. A check that always fails says as little as one
  # that always passes, and is noticed later.
  if ! compare_two_runs "${ROOT}/test/models/trivial_sat.fzn" "$d" > "$d/real.log" 2>&1; then
    echo "FAIL determinism self-test: the real solver was REJECTED on trivial_sat."
    echo "     Either the solver is genuinely nondeterministic -- which is a finding, not"
    echo "     a self-test problem -- or this check is broken."
    sed 's/^/       /' "$d/real.log" | head -10
    return 1
  fi
  # (3) The stop guard of the real instances (D-0264) must refuse each asynchronous stop
  # and accept a node-limit stop and a run with no `limit:` line (it ended on its own).
  # The lines are bin/main.ml's, copied from runs on fataepyc-06 on 2026-11-27.
  printf 'limit: reached time-limit=none cpu=1.0s wall=1.0s nodes=81 at=node fired=none signal=none\n' > "$d/ok.err"
  printf 'stats: nodes 3\n' > "$d/own.err"
  printf 'limit: reached time-limit=none cpu=900.09s wall=900.16s nodes=1628 at=trace fired=900.00s signal=TERM\n' > "$d/term.err"
  printf 'limit: killed signal=heap-budget phase=search cpu=785.65s wall=785.70s nodes=91\n' > "$d/heap.err"
  printf 'limit: reached time-limit=5 cpu=5.0s wall=5.0s nodes=40 at=node fired=5.00s signal=none\n' > "$d/clock.err"
  for f in ok own; do
    if ! stopped_by_itself "$d/$f.err"; then
      echo "FAIL determinism self-test: the stop guard refused a deterministic run ($f)."
      return 1
    fi
  done
  for f in term heap clock; do
    if stopped_by_itself "$d/$f.err"; then
      echo "FAIL determinism self-test: the stop guard ACCEPTED an asynchronous stop ($f),"
      echo "     so a real-instance comparison cut by a clock, a signal or the heap budget"
      echo "     would be read as evidence of determinism (D-0264)."
      return 1
    fi
  done
  echo "determinism self-test: catches a nondeterministic solver, accepts the real one,"
  echo "     and refuses a comparison cut by a clock, a signal or the heap budget"
  return 0
}

run_check() {
  if [ ! -x "${SOLVER}" ]; then
    echo "FAIL determinism: no solver at ${SOLVER}. Run \`dune build bin/\` first."
    return 1
  fi
  d="$(mktemp -d)"
  trap 'rm -rf "$d"' EXIT INT TERM
  n=0; bad=0
  # Two arms (M19-config-T1, D-0261): the fixed search, and the free search (the default,
  # so no flag), whose restarts, activity and phases must not depend on the clock or on
  # addresses either.
  # compare_two_runs assigns the global d (POSIX sh has no locals), hence top.
  top="$d"
  for arm in fixed free; do
    case "$arm" in fixed) SEARCH="--fixed-search" ;; free) SEARCH="" ;; esac
    mkdir -p "$top/$arm"
    for fzn in "${ROOT}"/test/models/*.fzn; do
      n=$((n + 1))
      compare_two_runs "${fzn}" "$top/$arm" || { echo "     (the ${arm} search)"; bad=$((bad + 1)); }
    done
  done
  d="$top"
  if [ "$bad" -ne 0 ]; then
    echo "FAIL determinism: ${bad} of ${n} runs produced different artefacts on a"
    echo "     second run of the SAME binary. That is nondeterminism in the solver or"
    echo "     the writer -- hash iteration order, an address reaching output, an"
    echo "     uninitialised read. It is not an expected-output question and must not"
    echo "     be fixed by re-blessing anything."
    return 1
  fi
  echo "determinism: ${n} runs (every model, fixed and free search), .opb/.pbp/stdout identical across two runs"
  r=0; rbad=0
  for arm in fixed free; do
    case "$arm" in fixed) SEARCH="--fixed-search" ;; free) SEARCH="" ;; esac
    for spec in $(echo "${REAL_INSTANCES}" | tr ' ' ':'); do
      name="${spec%%:*}"; rest="${spec#*:}"; budget="${rest%%:*}"; flags="${rest#*:}"
      r=$((r + 1))
      compare_real "${name}" "${budget}" "${flags}" "$d" || { echo "     (the ${arm} search)"; rbad=$((rbad + 1)); }
    done
  done
  if [ "$rbad" -ne 0 ]; then
    echo "FAIL determinism: ${rbad} of ${r} real-instance runs did not reproduce under two GC"
    echo "     settings at a node budget (D-0264). A proof that depends on the collector, an"
    echo "     address or a clock is a defect, and re-blessing is not an answer."
    return 1
  fi
  echo "determinism: ${r} real-instance runs (four instances, fixed and free search), .opb/.pbp/stdout identical under two GC settings"
  return 0
}

case "${1:-}" in
  --self-test) self_test ;;
  *) run_check ;;
esac
