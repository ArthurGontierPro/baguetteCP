#!/usr/bin/env bash
# M7-T4. Proves the corpus harness's input gate can actually fail.
#
# `scripts/corpus_run.sh --self-test` runs this. It needs no corpus, no node, no
# solver and no checker: it feeds `validate_fzn` and `instance_id` fixtures and
# asserts what they return.
#
# Why it exists: the gate in corpus_run.sh is the whole of D-0069's correction, and
# a guard that has not been SEEN to fail is not yet a guard -- the same discipline
# scripts/check_fmt.sh --self-test and scripts/check_test_widths.py follow. The
# torn case below is a reconstruction of the real `2010_bacp.fzn`: a correct solve
# item with the tail fragment `lete) minimize objective;` spliced after it.
#
# Both polarities are asserted. A validator that rejects everything would let the
# harness file every instance as INPUT-INVALID and report no solver findings at
# all, which is a failure that looks exactly like a clean run.

set -u

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BAGUETTE_CORPUS_SOURCE_ONLY=1
export BAGUETTE_CORPUS_SOURCE_ONLY
# shellcheck source=/dev/null
. "$ROOT/scripts/corpus_run.sh"

D="$(mktemp -d)"
trap 'rm -rf "$D"' EXIT INT TERM
fails=0

# $1 name, $2 expect (ok|bad), $3 file
expect_validate() {
  local name="$1" want="$2" f="$3" out rc
  out="$(validate_fzn "$f")"
  rc=$?
  if [ "$want" = ok ] && [ "$rc" -ne 0 ]; then
    echo "FAIL $name: a WELL-FORMED .fzn was rejected as '$out'."
    echo "     A validator that rejects good input puts every instance under"
    echo "     INPUT-INVALID and reports no solver findings at all."
    fails=$((fails + 1))
    return
  fi
  if [ "$want" = bad ] && [ "$rc" -eq 0 ]; then
    echo "FAIL $name: a TORN .fzn was accepted. The gate is open, and a refusal"
    echo "     of this file would be recorded against the solver (D-0069)."
    fails=$((fails + 1))
    return
  fi
  if [ "$want" = bad ]; then
    echo "ok   $name -> rejected: $out"
  else
    echo "ok   $name -> accepted"
  fi
}

good='var 1..3: x;
constraint int_lin_le([1], [x], 2);
solve :: int_search([x], input_order, indomain_min) minimize x;'

printf '%s\n' "$good" > "$D/good.fzn"
expect_validate "a complete model" ok "$D/good.fzn"

# The real shape of 2010_bacp.fzn: a correct solve item, then another job's tail.
printf '%s\nlete) minimize objective;\n' "$good" > "$D/torn.fzn"
expect_validate "two solve items (the 2010_bacp shape)" bad "$D/torn.fzn"

printf 'var 1..3: x;\nconstraint int_lin_le([1], [x], 2);\n' > "$D/nosolve.fzn"
expect_validate "no solve item" bad "$D/nosolve.fzn"

printf 'var 1..3: x;\nsolve :: int_search([x], input_ord' > "$D/cut.fzn"
expect_validate "cut mid-item" bad "$D/cut.fzn"

: > "$D/empty.fzn"
expect_validate "empty" bad "$D/empty.fzn"

expect_validate "absent" bad "$D/does-not-exist.fzn"

printf 'var 1..3: x;\n\000\000\000solve satisfy;\n' > "$D/nul.fzn"
expect_validate "NUL bytes from an interleaved write" bad "$D/nul.fzn"

# instance_id: the D-0068 bug in one assertion. Two models in one family directory
# MUST NOT share an id, because the id is the output path and a shared path is the
# torn write. Fifteen models shared 2010_bacp; that is the whole of M7-T10.
a="$(instance_id /c/2010/bacp/bacp-1.mzn)"
b="$(instance_id /c/2010/bacp/bacp-10.mzn)"
if [ "$a" = "$b" ]; then
  echo "FAIL instance_id: /c/2010/bacp/bacp-1.mzn and bacp-10.mzn share the id '$a'."
  echo "     They would flatten to the same path and overwrite each other -- exactly"
  echo "     the failure M7-T10 was opened for."
  fails=$((fails + 1))
else
  echo "ok   instance_id -> distinct per model file ($a, $b)"
fi

if [ "$fails" -eq 0 ]; then
  echo "corpus self-test: PASS"
  exit 0
fi
echo "corpus self-test: $fails FAIL"
exit 1
