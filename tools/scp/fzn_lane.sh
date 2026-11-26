#!/usr/bin/env bash
# The FlatZinc/.scp agreement lane of M23-inputs (D-0228 section 14 tests 1 and 2, D-0230).
#
# Usage: tools/scp/fzn_lane.sh [OUTDIR]     (BAGUETTE=binary, J=parallel runs, default 4)
#
# For every test model tools/e2e/fzn2scp.py translates: the .scp is solved by baguette
# with a proof, and the proof must be VERIFIED; the .fzn is solved by the same binary;
# the two must agree on the verdict (SAT, UNSAT, or the optimum, read from the
# `objective=` statistic of -s); and the .scp's answer is judged against the .scp alone by
# tools/scp/validate.py. One line per model in OUTDIR/res.txt, the totals on stdout. A
# model the reader refuses is listed as REFUSED with the reason; the plan expects the 7
# `member` models (fzn2scp writes them with `equals_if`, D-0228 section 14) and no other.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SOLVER="${BAGUETTE:-${ROOT}/_build/default/bin/main.exe}"
OUT="${1:-${ROOT}/test/out/scp-fzn}"
. "${ROOT}/scripts/checker.sh"
baguette_resolve_veripb || { echo "FAIL no proof checker" >&2; exit 1; }
mkdir -p "${OUT}/run"
export SOLVER OUT ROOT VERIPB
one() {
  m=$1; p="${OUT}/run/${m}"; fzn="${ROOT}/test/models/${m}.fzn"
  if ! python3 -I "${ROOT}/tools/e2e/fzn2scp.py" "$fzn" "$p.scp" "$p.names" 2> "$p.tr"; then
    echo "${m}|NOSCP|$(head -1 "$p.tr" | cut -c1-100)"; return; fi
  ( ulimit -v 4000000; timeout 120 "$SOLVER" "$p.scp" -s --proof "$p" > "$p.out" 2> "$p.err"; echo $? > "$p.rc" )
  if [ "$(cat "$p.rc")" != 0 ] && grep -q 'Fatal error' "$p.err"; then
    echo "${m}|FAIL|crash: $(grep -m1 'Fatal error' "$p.err" | cut -c1-100)"; return; fi
  if [ "$(cat "$p.rc")" != 0 ]; then
    echo "${m}|REFUSED|$(grep -m1 -o 'refused: .*' "$p.err" | cut -c10-110)"; return; fi
  v=$(timeout 300 "$VERIPB" "$p.opb" "$p.pbp" 2>&1 | grep -m1 '^s ' || echo "s REJECTED")
  rm -f "$p.opb" "$p.pbp"
  ( ulimit -v 4000000; timeout 120 "$SOLVER" "$fzn" -s --no-proof > "$p.fzn.out" 2> /dev/null )
  ans() { if grep -q '^=====UNSATISFIABLE' "$1"; then echo UNSAT;
          elif grep -q '^==========' "$1"; then echo "OPT $(grep -m1 'objective=' "$1" | sed 's/.*=//')";
          elif grep -q '^----------' "$1"; then echo SAT; else echo NONE; fi; }
  a=$(ans "$p.out"); b=$(ans "$p.fzn.out")
  val=$(timeout 300 python3 -I "${ROOT}/tools/scp/validate.py" "$p.scp" "$p.out" "$p.names")
  ok=OK
  case "$v" in "s VERIFIED"*) ;; *) ok=FAIL;; esac
  [ "$a" = "$b" ] || ok=FAIL
  case "$val" in OK*|TOOBIG*) ;; *) ok=FAIL;; esac
  echo "${m}|${ok}|scp=${a}|fzn=${b}|${v}|${val}"
}
export -f one
ls "${ROOT}"/test/models/*.fzn | xargs -n1 basename | sed 's/\.fzn$//' |
  xargs -P "${J:-4}" -I{} bash -c 'one {}' | sort > "${OUT}/res.txt"
echo "fzn lane: $(grep -c '|OK|' "${OUT}/res.txt") agree, $(grep -c '|FAIL|' "${OUT}/res.txt") FAIL, $(grep -c '|REFUSED|' "${OUT}/res.txt") refused by the reader, $(grep -c '|NOSCP|' "${OUT}/res.txt") not translated by fzn2scp"
grep '|FAIL|' "${OUT}/res.txt" | head -20
[ "$(grep -c '|FAIL|' "${OUT}/res.txt")" -eq 0 ]
