#!/usr/bin/env bash
# Solve every model in test/models/, compare stdout against test/expected/,
# and verify the emitted proof with veripb.
#
# A model that produces the right answer with a proof veripb rejects is a FAILURE.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOLVER="${BAGUETTE:-${ROOT}/_build/default/bin/main.exe}"
VERIPB="${VERIPB:-veripb}"
OUT="${ROOT}/test/out"

mkdir -p "${OUT}"

pass=0; fail=0; skip=0

if [ ! -x "${SOLVER}" ]; then
  echo "solver not built at ${SOLVER} — run 'make build' first" >&2
  exit 2
fi

have_veripb=1
command -v "${VERIPB}" >/dev/null 2>&1 || have_veripb=0
[ "${have_veripb}" -eq 1 ] || echo "NOTE: veripb not on PATH; proof checking will be skipped" >&2

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
    echo "FAIL ${base}: solver exited ${rc}"
    sed 's/^/       /' "${prefix}.err" | head -5
    fail=$((fail+1))
    continue
  fi

  if ! diff -u "${expected}" "${prefix}.out" > "${prefix}.diff"; then
    echo "FAIL ${base}: output differs from test/expected/${base}.out"
    sed 's/^/       /' "${prefix}.diff" | head -20
    echo "       Do not edit the expected file to make this pass (invariant I-M1)."
    fail=$((fail+1))
    continue
  fi

  if [ "${have_veripb}" -eq 0 ]; then
    echo "PASS ${base} (output only; proof NOT checked)"
    skip=$((skip+1))
    continue
  fi

  if "${VERIPB}" "${prefix}.opb" "${prefix}.pbp" > "${prefix}.veripb" 2>&1; then
    echo "PASS ${base}"
    pass=$((pass+1))
  else
    echo "FAIL ${base}: veripb rejected the proof"
    sed 's/^/       /' "${prefix}.veripb" | tail -20
    echo "       opb=${prefix}.opb proof=${prefix}.pbp"
    echo "       See docs/PROOF-FORMAT.md section 6 before changing anything."
    fail=$((fail+1))
  fi
done

echo
echo "model tests: ${pass} passed, ${fail} failed, ${skip} skipped"
[ "${fail}" -eq 0 ]
