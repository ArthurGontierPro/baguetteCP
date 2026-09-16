#!/usr/bin/env bash
# Solve one FlatZinc model and verify the proof it emits.
#   scripts/verify_proof.sh test/models/trivial_sat.fzn
# Exit 0 only if the solver succeeds AND veripb accepts the proof.
set -euo pipefail

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


FZN="${1:?usage: verify_proof.sh MODEL.fzn}"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT="${ROOT}/test/out"
BASE="$(basename "${FZN}" .fzn)"
PREFIX="${OUT}/${BASE}"

SOLVER="${BAGUETTE:-${ROOT}/_build/default/bin/main.exe}"

# scripts/checker.sh owns which veripb this is; it also explains why a missing one
# is a failure rather than a skip. This script used to `echo SKIP; exit 0` here, so
# a machine with no checker made every proof test pass.
# shellcheck source=checker.sh
. "${ROOT}/scripts/checker.sh"

mkdir -p "${OUT}"

if ! baguette_resolve_veripb; then
  echo "FAIL ${BASE}: the proof was NOT checked." >&2
  baguette_veripb_diagnostic
  exit 1
fi

echo "--- solving ${BASE}"
"${SOLVER}" "${FZN}" --proof "${PREFIX}" > "${PREFIX}.out"

echo "--- checking ${BASE}.pbp with ${VERIPB}"
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
