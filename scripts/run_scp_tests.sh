#!/usr/bin/env bash
# Solve every .scp in test/scp/, compare stdout against test/scp/expected/, verify the
# emitted proof with veripb, and judge the answer against the .scp alone with
# tools/scp/validate.py (M23-inputs-T5, D-0230).
#
# The .scp lane of scripts/run_model_tests.sh, with one check more: the expected outputs
# were not taken on trust from the solver that produced them. validate.py reads the .scp
# through tools/e2e/scpsem.py (CakeML's cpScript.sml, transcribed apart from lib/scp/),
# enumerates its solutions and grades the answer, so a reader that misreads a constraint
# fails here even when its proof verifies (the proof is of the MODEL baguette built, and
# a misread model has a valid proof of the wrong problem).
#
# Like run_model_tests.sh: the --no-proof run must print the same bytes and exit the same
# way (D-0126), and nothing may be written on stderr. A missing checker is a FAILURE.
set -uo pipefail

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
OUT="${ROOT}/test/out/scp"
mkdir -p "${OUT}"

if [ ! -x "${SOLVER}" ]; then
  echo "solver not built at ${SOLVER} -- run 'make build' first" >&2
  exit 1
fi
if ! baguette_resolve_veripb; then
  echo "FAIL no proof checker" >&2
  baguette_veripb_diagnostic
  exit 1
fi
if ! command -v python3 >/dev/null 2>&1; then
  echo "FAIL python3 not found: tools/scp/validate.py cannot judge the answers" >&2
  exit 1
fi

pass=0; fail=0
n=0
for scp in "${ROOT}"/test/scp/*.scp; do
  n=$((n+1))
  base="$(basename "${scp}" .scp)"
  expected="${ROOT}/test/scp/expected/${base}.out"
  prefix="${OUT}/${base}"
  if [ ! -f "${expected}" ]; then
    echo "FAIL ${base}: no expected output in test/scp/expected/"; fail=$((fail+1)); continue
  fi
  "${SOLVER}" "${scp}" --proof "${prefix}" > "${prefix}.out" 2> "${prefix}.err"
  rc=$?
  if [ "${rc}" -ne 0 ]; then
    echo "FAIL ${base}: solver exited ${rc}"; sed 's/^/       /' "${prefix}.err" | head -5
    fail=$((fail+1)); continue
  fi
  if [ -s "${prefix}.err" ]; then
    echo "FAIL ${base}: solver wrote to stderr"; sed 's/^/       /' "${prefix}.err" | head -5
    fail=$((fail+1)); continue
  fi
  if ! diff -u "${expected}" "${prefix}.out" > "${prefix}.diff"; then
    echo "FAIL ${base}: output differs from test/scp/expected/${base}.out"
    sed 's/^/       /' "${prefix}.diff" | head -20
    echo "       Do not edit the expected file to make this pass (invariant I-M1)."
    fail=$((fail+1)); continue
  fi
  if ! "${VERIPB}" "${prefix}.opb" "${prefix}.pbp" > "${prefix}.veripb" 2>&1 ||
     ! grep -q '^s VERIFIED' "${prefix}.veripb"; then
    echo "FAIL ${base}: veripb rejected the proof"; sed 's/^/       /' "${prefix}.veripb" | tail -10
    fail=$((fail+1)); continue
  fi
  if ! v="$(python3 -I "${ROOT}/tools/scp/validate.py" "${scp}" "${prefix}.out")"; then
    echo "FAIL ${base}: the answer is not the .scp's: ${v}"
    fail=$((fail+1)); continue
  fi
  "${SOLVER}" "${scp}" --no-proof > "${prefix}.noproof.out" 2> "${prefix}.noproof.err"
  rc2=$?
  if [ "${rc2}" -ne "${rc}" ] || [ -s "${prefix}.noproof.err" ] ||
     ! cmp -s "${prefix}.out" "${prefix}.noproof.out"; then
    echo "FAIL ${base}: the --no-proof run differs from the proved run (D-0126)"
    fail=$((fail+1)); continue
  fi
  echo "ok   ${base}  ($(grep -m1 '^s ' "${prefix}.veripb"); ${v})"
  pass=$((pass+1))
done

if [ "${n}" -eq 0 ]; then
  echo "FAIL the .scp lane ran on NO model: test/scp/*.scp is empty"
  exit 1
fi
echo "scp tests: ${pass} passed, ${fail} failed"
[ "${fail}" -eq 0 ]
