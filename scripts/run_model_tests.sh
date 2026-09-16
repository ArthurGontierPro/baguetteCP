#!/usr/bin/env bash
# Solve every model in test/models/, compare stdout against test/expected/,
# and verify the emitted proof with veripb.
#
# A model that produces the right answer with a proof veripb rejects is a FAILURE.
set -uo pipefail

# MACHINE LIMIT (2026-09-16). 15 GB of RAM shared by every concurrent session, and three
# test binaries had to be killed at the ceiling in one day. The cap is applied here as
# well as in the Makefile so that running this script directly is still capped. Lower
# only: if the caller already set a tighter limit we leave theirs alone.
: "${BAGUETTE_MEM_CAP_KB:=4000000}"
if [ "${BAGUETTE_MEM_CAP_KB}" != "none" ]; then
  _cur="$(ulimit -v)"
  if [ "${_cur}" = "unlimited" ] || { [ "${_cur}" -gt "${BAGUETTE_MEM_CAP_KB}" ] 2>/dev/null; }; then
    ulimit -v "${BAGUETTE_MEM_CAP_KB}" 2>/dev/null ||
      echo "warning: could not apply the ${BAGUETTE_MEM_CAP_KB} kB memory cap" >&2
  fi
  unset _cur
fi

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOLVER="${BAGUETTE:-${ROOT}/_build/default/bin/main.exe}"
# shellcheck source=checker.sh
. "${ROOT}/scripts/checker.sh"
OUT="${ROOT}/test/out"

mkdir -p "${OUT}"

pass=0; fail=0; skip=0; xfail=0; xpass=0

PENDING="${ROOT}/test/models/PENDING"

# Is this model known not to work yet? See test/models/PENDING.
is_pending() {
  [ -f "${PENDING}" ] || return 1
  grep -v '^[[:space:]]*#' "${PENDING}" 2>/dev/null \
    | awk '{print $1}' | grep -qx "$1"
}

pending_reason() {
  grep -v '^[[:space:]]*#' "${PENDING}" 2>/dev/null \
    | awk -v m="$1" '$1 == m { $1 = ""; sub(/^ +/, ""); print }'
}

# Report an outcome, accounting for whether the model was expected to fail.
# $1 = basename, $2 = "pass" or "fail", $3 = detail shown on an unexpected result
report() {
  local base="$1" outcome="$2" detail="${3:-}"
  if is_pending "${base}"; then
    if [ "${outcome}" = "pass" ]; then
      echo "XPASS ${base}: listed in test/models/PENDING but it PASSES now."
      echo "       Delete its line from test/models/PENDING."
      xpass=$((xpass+1))
      return 1
    fi
    echo "xfail ${base}: $(pending_reason "${base}")"
    xfail=$((xfail+1))
    return 0
  fi
  if [ "${outcome}" = "pass" ]; then
    echo "PASS  ${base}"
    pass=$((pass+1))
    return 0
  fi
  echo "FAIL  ${base}: ${detail}"
  fail=$((fail+1))
  return 1
}

if [ ! -x "${SOLVER}" ]; then
  echo "solver not built at ${SOLVER} — run 'make build' first" >&2
  exit 2
fi

# No checker is a failure of the whole run, not a per-model skip: "a test that does
# not check the proof is half a test" (CLAUDE.md). This used to set have_veripb=0 and
# report every model as "PASS (output only; proof NOT checked)" against a skip count.
if ! baguette_resolve_veripb; then
  echo "run_model_tests.sh: no proof was checked, so nothing here passed." >&2
  baguette_veripb_diagnostic
  exit 2
fi
echo "checker: ${VERIPB}"

for fzn in "${ROOT}"/test/models/*.fzn; do
  base="$(basename "${fzn}" .fzn)"
  expected="${ROOT}/test/expected/${base}.out"
  prefix="${OUT}/${base}"

  if [ ! -f "${expected}" ]; then
    echo "SKIP ${base}: no expected output in test/expected/"
    skip=$((skip+1))
    continue
  fi

  "${SOLVER}" "${fzn}" --proof "${prefix}" > "${prefix}.out" 2> "${prefix}.err"
  rc=$?

  if [ "${rc}" -ne 0 ]; then
    if report "${base}" fail "solver exited ${rc}"; then continue; fi
    sed 's/^/       /' "${prefix}.err" | head -5
    continue
  fi

  if ! diff -u "${expected}" "${prefix}.out" > "${prefix}.diff"; then
    if report "${base}" fail "output differs from test/expected/${base}.out"; then continue; fi
    sed 's/^/       /' "${prefix}.diff" | head -20
    echo "       Do not edit the expected file to make this pass (invariant I-M1)."
    continue
  fi

  if "${VERIPB}" "${prefix}.opb" "${prefix}.pbp" > "${prefix}.veripb" 2>&1; then
    report "${base}" pass || true
  else
    if report "${base}" fail "veripb rejected the proof"; then continue; fi
    sed 's/^/       /' "${prefix}.veripb" | tail -20
    echo "       opb=${prefix}.opb proof=${prefix}.pbp"
    echo "       See docs/PROOF-FORMAT.md section 6 before changing anything."
  fi
done

echo
echo "model tests: ${pass} passed, ${fail} failed, ${xfail} expected-fail, ${xpass} unexpected-pass, ${skip} skipped"

if [ "${xfail}" -gt 0 ]; then
  echo "  ${xfail} model(s) are listed in test/models/PENDING and are not yet expected to"
  echo "  work. That file should be empty by M1-T11."
fi
if [ "${xpass}" -gt 0 ]; then
  echo "  ${xpass} model(s) pass but are still listed in test/models/PENDING. Remove them."
fi

[ "${fail}" -eq 0 ] && [ "${xpass}" -eq 0 ]
