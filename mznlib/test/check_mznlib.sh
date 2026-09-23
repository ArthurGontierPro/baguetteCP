#!/usr/bin/env bash
# Flatten every model beside this script against mznlib/ and compare the result
# with the committed artefact in test/models/.
#
# WHY THIS IS NOT IN scripts/: it needs a MiniZinc binary, which the dev
# environment does not have and the gate therefore cannot require. It is run by
# hand, on a machine that has one:
#
#   MZN=/path/to/minizinc mznlib/test/check_mznlib.sh
#
# What it checks:
#   bare.mzn         -- the library type-checks in a model that includes nothing
#   the others       -- each still flattens to the byte-identical body of the
#                       test/models/<name>.fzn committed beside it, ignoring
#                       both MiniZinc's machine-specific banner and the header
#                       comment the artefact carries
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
MZN="${MZN:-minizinc}"
command -v "${MZN}" >/dev/null 2>&1 || {
  echo "FAIL minizinc not found (MZN=${MZN}). This script cannot skip: with no"
  echo "     flattener there is nothing here to check, and reporting a pass"
  echo "     would be reporting a measurement that was never taken."
  exit 1
}
export MZN_SOLVER_PATH="${ROOT}/tools"
tmp="$(mktemp -d)"
trap 'rm -rf "${tmp}"' EXIT
fail=0 pass=0

# The body: everything after the leading run of comment and blank lines.
body() { awk 'NR==1,/^[^%[:space:]]/ { if ($0 ~ /^%/ || $0 ~ /^[[:space:]]*$/) next } { print }' "$1"; }

for src in "${ROOT}"/mznlib/test/*.mzn; do
  base="$(basename "${src}" .mzn)"
  if ! "${MZN}" -c --solver baguette "${src}" -o "${tmp}/${base}.fzn" > "${tmp}/${base}.err" 2>&1; then
    echo "FAIL ${base}: flattening failed"
    head -3 "${tmp}/${base}.err"
    fail=$((fail + 1))
    continue
  fi
  committed="${ROOT}/test/models/${base}.fzn"
  if [ ! -f "${committed}" ]; then
    echo "ok   ${base} (flattens; no committed artefact to compare)"
    pass=$((pass + 1))
    continue
  fi
  if diff -q <(body "${committed}") <(body "${tmp}/${base}.fzn") > /dev/null; then
    echo "ok   ${base}"
    pass=$((pass + 1))
  else
    echo "FAIL ${base}: flattened output differs from test/models/${base}.fzn"
    diff <(body "${committed}") <(body "${tmp}/${base}.fzn") | head -20
    fail=$((fail + 1))
  fi
done

echo "mznlib: ${pass} ok, ${fail} failed"
[ "${fail}" -eq 0 ]
