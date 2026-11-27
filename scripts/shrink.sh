#!/usr/bin/env bash
# Check whether one model's proof is rejected, and show where. It was meant to also find
# WHICH propagator emits the rejected step, by re-running with propagators disabled one at
# a time; that needs a solver flag --disable-propagator, planned with the engine (roadmap
# M1-T7) and never added, so that mode is gone (D-0254). What remains:
#
#   scripts/shrink.sh test/models/lin_unsat.fzn
#
# solves the model with --proof into test/out/shrink/base.{opb,pbp}, runs veripb on it and,
# when the checker refuses it, prints the checker's last lines (the rejected line and the
# checker's sentence). Localise from there with docs/PROOF-FORMAT.md section 6.
#
# Exit 0 when the proof is accepted; 1 when the solver itself fails; 2 when no checker is
# found; 3 when the proof is rejected.
set -uo pipefail

FZN="${1:?usage: shrink.sh MODEL.fzn}"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOLVER="${BAGUETTE:-${ROOT}/_build/default/bin/main.exe}"
# shellcheck source=checker.sh
. "${ROOT}/scripts/checker.sh"
if ! baguette_resolve_veripb; then
  echo "shrink.sh: no checker, so there is nothing to shrink against." >&2
  baguette_veripb_diagnostic
  exit 2
fi
OUT="${ROOT}/test/out/shrink"
mkdir -p "${OUT}"

echo "baseline:"
"${SOLVER}" "${FZN}" --proof "${OUT}/base" >"${OUT}/base.out" 2>"${OUT}/base.err"
rc=$?
if [ "${rc}" -ne 0 ]; then
  echo "  the solver failed on ${FZN} (exit ${rc}), so there is no proof to check:"
  tail -5 "${OUT}/base.err" | sed 's/^/    /'
  exit 1
fi
if "${VERIPB}" "${OUT}/base.opb" "${OUT}/base.pbp" >"${OUT}/base.check" 2>&1; then
  echo "  proof accepted -- nothing to shrink"
  exit 0
fi
echo "  proof REJECTED by ${VERIPB}; the checker's last lines:"
tail -8 "${OUT}/base.check" | sed 's/^/    /'
echo "  shrink.sh cannot say which propagator wrote the line: the --disable-propagator"
echo "  mode it was written for does not exist in the solver. See docs/PROOF-FORMAT.md"
echo "  section 6 to localise the rejected line."
exit 3
