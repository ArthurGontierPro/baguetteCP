#!/bin/sh
# M2-T12 (the determinism half). Solve every model TWICE and require the .opb, .pbp and
# stdout to be byte-identical across the two runs.
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
# --self-test proves the check can fail, and runs FIRST on every gate. Same discipline as
# scripts/check_test_widths.py and scripts/check_fmt.sh, for the same reason: a guard
# nobody has watched fail is not yet a guard.

set -e

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SOLVER="${BAGUETTE:-${ROOT}/_build/default/bin/main.exe}"
MEM_CAP_KB="${BAGUETTE_MEM_CAP_KB:-4000000}"

# The suites already apply this; a script invoked directly must too (CLAUDE.md, and three
# memory-ceiling incidents on 2026-09-16).
_cur="$(ulimit -v)"
if [ "${_cur}" = "unlimited" ] || { [ "${_cur}" -gt "${MEM_CAP_KB}" ] 2>/dev/null; }; then
  ulimit -v "${MEM_CAP_KB}" 2>/dev/null || true
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

# One model, two runs, three artefacts compared. Echoes the differing kind on failure.
# $1 model path, $2 scratch dir. Prints nothing when identical.
compare_two_runs() {
  fzn="$1"; d="$2"
  base="$(basename "${fzn}" .fzn)"
  rc1=0; rc2=0
  for run in 1 2; do
    timeout 300 "${SOLVER}" "${fzn}" --proof "${d}/${base}.${run}" \
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
  echo "determinism self-test: catches a nondeterministic solver, accepts the real one"
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
  for fzn in "${ROOT}"/test/models/*.fzn; do
    n=$((n + 1))
    compare_two_runs "${fzn}" "$d" || bad=$((bad + 1))
  done
  if [ "$bad" -ne 0 ]; then
    echo "FAIL determinism: ${bad} of ${n} models produced different artefacts on a"
    echo "     second run of the SAME binary. That is nondeterminism in the solver or"
    echo "     the writer -- hash iteration order, an address reaching output, an"
    echo "     uninitialised read. It is not an expected-output question and must not"
    echo "     be fixed by re-blessing anything."
    return 1
  fi
  echo "determinism: ${n} models, .opb/.pbp/stdout identical across two runs"
  return 0
}

case "${1:-}" in
  --self-test) self_test ;;
  *) run_check ;;
esac
