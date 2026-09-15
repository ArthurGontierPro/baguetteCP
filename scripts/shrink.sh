#!/usr/bin/env bash
# Find which propagator emits a proof step veripb rejects, by re-running the model with
# propagators disabled one at a time.
#
#   scripts/shrink.sh test/models/lin_unsat.fzn
#
# Relies on --disable-propagator, which lands with the engine (roadmap M1-T7).
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

PROPAGATORS="${PROPAGATORS:-int_le int_lt int_eq int_ne int_lin_le int_lin_eq int_lin_ne bool_clause all_different element}"

echo "baseline:"
if "${SOLVER}" "${FZN}" --proof "${OUT}/base" >/dev/null 2>&1 &&
   "${VERIPB}" "${OUT}/base.opb" "${OUT}/base.pbp" >/dev/null 2>&1; then
  echo "  proof already accepted — nothing to shrink"
  exit 0
fi
echo "  proof rejected, searching"

for p in ${PROPAGATORS}; do
  if "${SOLVER}" "${FZN}" --disable-propagator "${p}" --proof "${OUT}/${p}" >/dev/null 2>&1 &&
     "${VERIPB}" "${OUT}/${p}.opb" "${OUT}/${p}.pbp" >/dev/null 2>&1; then
    echo "  SUSPECT: disabling '${p}' makes the proof check. Its justification is wrong."
    exit 0
  fi
done

echo "  no single propagator accounts for it — the encoding or the search logging is suspect"
exit 1
