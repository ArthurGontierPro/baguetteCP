#!/usr/bin/env bash
# Solve one FlatZinc model and verify the proof it emits.
#   scripts/verify_proof.sh test/models/trivial_sat.fzn
# Exit 0 only if the solver succeeds AND veripb accepts the proof.
set -euo pipefail

FZN="${1:?usage: verify_proof.sh MODEL.fzn}"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT="${ROOT}/test/out"
BASE="$(basename "${FZN}" .fzn)"
PREFIX="${OUT}/${BASE}"

SOLVER="${BAGUETTE:-${ROOT}/_build/default/bin/main.exe}"
VERIPB="${VERIPB:-veripb}"

mkdir -p "${OUT}"

if ! command -v "${VERIPB}" >/dev/null 2>&1; then
  echo "SKIP ${BASE}: veripb not on PATH" >&2
  exit 0
fi

echo "--- solving ${BASE}"
"${SOLVER}" "${FZN}" --proof "${PREFIX}" > "${PREFIX}.out"

echo "--- checking ${BASE}.pbp"
if "${VERIPB}" "${PREFIX}.opb" "${PREFIX}.pbp"; then
  echo "OK   ${BASE}"
else
  echo "FAIL ${BASE}: veripb rejected the proof" >&2
  echo "     model:  ${FZN}" >&2
  echo "     opb:    ${PREFIX}.opb" >&2
  echo "     proof:  ${PREFIX}.pbp" >&2
  echo "     See docs/PROOF-FORMAT.md section 6 before changing anything." >&2
  exit 1
fi
