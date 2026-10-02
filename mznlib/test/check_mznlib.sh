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
#   directives       -- M6-T13 (D-0087). A source may carry, in its header,
#                         % MUST-EMIT: <constraint>      flattened output calls it
#                         % MUST-NOT-EMIT: <constraint>  ... and never calls this
#                         % SOLVES-AS: <name>            the flattened model, solved
#                                                        by BAGUETTE (default
#                                                        _build/default/bin/main.exe)
#                                                        through scripts/verify_proof.sh,
#                                                        prints test/expected/<name>.out
#                                                        and its proof is VERIFIED
#                       for a library route whose committed lane had to be written by
#                       hand (no flattener where it was written), so a byte comparison
#                       would test MiniZinc's X_INTRODUCED_ numbering and not the
#                       route. gcc_low_up_src_{sat,unsat} are the first two.
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
  # M6-T13: the directives, checked before the artefact comparison.
  dfail=0
  while IFS= read -r c; do
    grep -q "^constraint ${c}(" "${tmp}/${base}.fzn" ||
      { echo "FAIL ${base}: flattened output has no ${c} call"; dfail=1; }
  done < <(sed -n 's/^% MUST-EMIT: *\([A-Za-z0-9_]*\).*/\1/p' "${src}")
  while IFS= read -r c; do
    if grep -q "^constraint ${c}(" "${tmp}/${base}.fzn"; then
      echo "FAIL ${base}: flattened output still calls ${c} (the decomposition, not the route)"
      dfail=1
    fi
  done < <(sed -n 's/^% MUST-NOT-EMIT: *\([A-Za-z0-9_]*\).*/\1/p' "${src}")
  while IFS= read -r n; do
    exp="${ROOT}/test/expected/${n}.out"
    cp "${tmp}/${base}.fzn" "${tmp}/${n}_flat.fzn"
    if ! BAGUETTE="${BAGUETTE:-${ROOT}/_build/default/bin/main.exe}" \
      "${ROOT}/scripts/verify_proof.sh" "${tmp}/${n}_flat.fzn" > "${tmp}/${n}.vp" 2>&1; then
      echo "FAIL ${base}: the flattened model's proof was not VERIFIED"
      tail -3 "${tmp}/${n}.vp"
      dfail=1
    elif ! "${BAGUETTE:-${ROOT}/_build/default/bin/main.exe}" "${tmp}/${n}_flat.fzn" 2>/dev/null |
      diff -q - "${exp}" > /dev/null; then
      echo "FAIL ${base}: the flattened model does not print test/expected/${n}.out"
      dfail=1
    fi
  done < <(sed -n 's/^% SOLVES-AS: *\([A-Za-z0-9_]*\).*/\1/p' "${src}")
  if [ "${dfail}" -ne 0 ]; then
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
