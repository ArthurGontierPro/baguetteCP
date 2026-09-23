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

# ------------------------------------------------- M7-T14: MEM_KB -> --max-heap-mb
#
# The derivation is the whole of M7-T14 and it is one arithmetic expression, so the
# thing that can go wrong with it is a units error: KB read as MB, or MB as KB,
# would pass a limit a thousandfold wrong in either direction and the symptom would
# be either every instance refused or the guard never firing -- and the SECOND of
# those looks exactly like the clean run we are trying to distinguish it from. So
# the units are asserted against the real default, not against a round number.
expect_eq() {
  local name="$1" want="$2" got="$3"
  if [ "$want" = "$got" ]; then
    echo "ok   $name -> $got"
  else
    echo "FAIL $name: expected '$want', got '$got'."
    fails=$((fails + 1))
  fi
}

# 32 GB of address space (the default and the cap) -> 15625 MB of OCaml major heap.
expect_eq "heap_mb_from_mem_kb at the 32 GB default" 15625 "$(heap_mb_from_mem_kb 32000000)"
expect_eq "heap_mb_from_mem_kb at 4 GB" 2048 "$(heap_mb_from_mem_kb 4194304)"
# No limit to derive from, and no limit invented: the empty string is what run_one
# tests to decide whether to pass the flag at all.
expect_eq "heap_mb_from_mem_kb with no MEM_KB" "" "$(heap_mb_from_mem_kb '')"
expect_eq "heap_mb_from_mem_kb with junk" "" "$(heap_mb_from_mem_kb 'unlimited')"
expect_eq "heap_mb_from_mem_kb below one MB of headroom" "" "$(heap_mb_from_mem_kb 512)"
# The margin is the point of the flag: the derived heap limit must be strictly less
# than the ulimit it is derived from, in the SAME units, or the guard loses the race
# to the kernel and we are back to an uncatchable exit 134.
if [ "$(( $(heap_mb_from_mem_kb 32000000) * 1024 ))" -lt 32000000 ]; then
  echo "ok   the derived heap limit leaves headroom below the ulimit"
else
  echo "FAIL the derived heap limit is not below MEM_KB. The kernel would refuse the"
  echo "     mapping before the guard fired, and M7-T14 would have changed nothing."
  fails=$((fails + 1))
fi

# ------------------------------------------------- M7-T15: model/data pairing
#
# `corpus_run.sh` took the SMALLEST .dzn in the family, which is a preference that
# was being applied as a verdict: about a dozen of wave 27's FLATTEN-FAIL rows are
# a data file that does not define the model's parameters, i.e. the harness's own
# choice recorded against the corpus (D-0069's mistake, one level down). The fix is
# that the smallest is tried FIRST and the others after it, so what is asserted
# here is the ORDER and the BOUND.
DD="$D/family"
mkdir -p "$DD"
printf 'x' > "$DD/tiny.dzn"                  # 1 byte   -- first
printf '%0100d' 0 > "$DD/small.dzn"          # 100 B    -- second
printf '%01000d' 0 > "$DD/medium.json"       # 1000 B   -- third
printf '%010000d' 0 > "$DD/large.dzn"        # 10000 B  -- fourth
got="$(data_candidates "$DD" 4 | xargs -n1 basename | tr '\n' ' ')"
expect_eq "data_candidates orders smallest-first" \
  "tiny.dzn small.dzn medium.json large.dzn " "$got"
expect_eq "data_candidates keeps the old first choice first" \
  "tiny.dzn" "$(data_candidates "$DD" 4 | head -1 | xargs basename)"
expect_eq "data_candidates honours DATA_TRIES" 2 "$(data_candidates "$DD" 2 | wc -l)"
# A family with no data files must yield NO candidates rather than an error or a
# spurious one: run_one appends the bare-model attempt itself, and that attempt is
# what gives a data-free model an honest outcome instead of a pairing failure.
mkdir -p "$D/emptyfamily"
expect_eq "data_candidates on a family with no data" 0 \
  "$(data_candidates "$D/emptyfamily" 4 | wc -l)"

if [ "$fails" -eq 0 ]; then
  echo "corpus self-test: PASS"
  exit 0
fi
echo "corpus self-test: $fails FAIL"
exit 1
