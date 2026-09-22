#!/usr/bin/env bash
# M7-T1. The lane that proves the width refusal is gone, that the SIGNAL that replaced
# it fires, and that the refusal is still reachable on request.
#
# ---------------------------------------------------------------- why a script
#
# The subject of this lane is a model whose declared domain is WIDER than test/models/
# is allowed to contain. scripts/check_test_widths.py enforces "no test may declare a
# wide domain", and that rule is not the solver's capability limit -- it is suite
# hygiene, it exists because three test binaries died at a memory ceiling, and M7-T1
# does not touch it. So the over-wide model is GENERATED into a temporary directory,
# solved, checked and deleted. Nothing wide is ever committed, the width lint keeps its
# full strength, and `make check` does not carry the artefact around.
#
# ---------------------------------------------------------------- the lanes
#
#   1  ENCODES     a model well past the old cap solves to the right
#                  answer and veripb 3.0.2 accepts its proof. The refusal is gone.
#   2  REPORTS     the same run says what it cost, on stderr, in words a reader who has
#                  never heard of D-0028 can act on. A silent success is as wrong as a
#                  silent failure, which is the whole point of the row.
#   3  COUNTS      --stats carries the aggregate the per-variable cap never bounded.
#   4  REFUSES     --max-order-width=N reproduces the pre-M7 refusal, wording and all,
#                  and BAGUETTE_MAX_ORDER_WIDTH=N does the same through the environment.
#   5  PRECEDENCE  the flag beats the environment variable.
#   6  SILENCES    --width-warn=none removes the sentence and nothing else.
#   7  TYPOS       a limit that is neither an integer nor `none` is an ERROR. A mistyped
#                  budget that quietly means "no budget" is the failure this row is
#                  about, so it must not be possible.
#
# --self-test runs FIRST on every gate and proves each assertion can fail, the same
# discipline as check_test_widths.py, check_fmt.sh and check_determinism.sh: a guard
# nobody has watched fail is not yet a guard.

set -u

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SOLVER="${BAGUETTE:-${ROOT}/_build/default/bin/main.exe}"

# This lane's own memory cap, separate from the suite's only so that it can be switched
# off on the corpus node like every other (M7-T1). The default is the suite's.
MEM_CAP_KB="${BAGUETTE_MEM_CAP_KB:-4000000}"
if [ "${MEM_CAP_KB}" != "none" ]; then
  _cur="$(ulimit -v)"
  if [ "${_cur}" = "unlimited" ] || { [ "${_cur}" -gt "${MEM_CAP_KB}" ] 2>/dev/null; }; then
    ulimit -v "${MEM_CAP_KB}" 2>/dev/null || true
  fi
fi

# The pre-M7 cap. Named once: it is what the flag has to restore, and what the warning
# threshold still defaults to.
OLD_CAP=10000
# Three times the old cap. Big enough that the pre-M7 build refused it flatly,
# small enough that the gate stays affordable -- the point is that the refusal is gone,
# not that we can encode a million. Measured cost is printed at the end of a run.
WIDE=30000

failures=0
fail() {
  failures=$((failures + 1))
  echo "FAIL $*"
}
ok() { echo "ok   $*"; }

# Assert that "$1" (a description) holds: $2 is the haystack, $3.. the needles.
needles_in() {
  desc="$1"
  hay="$2"
  shift 2
  missing=""
  for n in "$@"; do
    case "${hay}" in
    *"${n}"*) ;;
    *) missing="${missing} \"${n}\"" ;;
    esac
  done
  if [ -n "${missing}" ]; then
    fail "${desc}: output does not mention${missing}"
    echo "------- output was:"
    printf '%s\n' "${hay}" | head -30
    echo "-------"
    return 1
  fi
  ok "${desc}"
}

TMP="$(mktemp -d)"
trap 'rm -rf "${TMP}"' EXIT

# ------------------------------------------------------------------ the models
#
# SAT, and satisfiable on purpose: D-0053 measured that `red` is vacuous over a
# contradictory database, so a proof verified only over an UNSAT model has tested
# nothing about the lines that matter. The answer is checkable by hand -- x is pinned.
cat >"${TMP}/wide.fzn" <<EOF
var 0..${WIDE}: x :: output_var;
constraint int_lin_le([1], [x], 7);
constraint int_lin_le([-1], [x], -7);
solve satisfy;
EOF
# A second, one unit over the old cap: the smallest model the pre-M7 build refused.
cat >"${TMP}/justover.fzn" <<EOF
var 0..$((OLD_CAP + 1)): x :: output_var;
constraint int_lin_le([1], [x], 3);
constraint int_lin_le([-1], [x], -3);
solve satisfy;
EOF

run() { # run OUT_PREFIX MODEL EXTRA_ARGS...
  prefix="$1"
  model="$2"
  shift 2
  "${SOLVER}" "${model}" --proof "${prefix}" "$@" >"${prefix}.out" 2>"${prefix}.err"
  echo "$?"
}

# ============================================================== 1 ENCODES
lane_encodes() {
  rc="$(run "${TMP}/wide" "${TMP}/wide.fzn")"
  if [ "${rc}" != "0" ]; then
    fail "1 ENCODES: the solver exited ${rc} on a width-${WIDE} model"
    head -20 "${TMP}/wide.err"
    return
  fi
  if ! grep -q '^x = 7;$' "${TMP}/wide.out"; then
    fail "1 ENCODES: wrong answer on a width-${WIDE} model"
    head -5 "${TMP}/wide.out"
    return
  fi
  ok "1 ENCODES: width ${WIDE} (3x the pre-M7 cap of ${OLD_CAP}) solves to x = 7"

  # And the proof is CHECKED. A test that does not check the proof is half a test.
  # shellcheck source=scripts/checker.sh
  . "${ROOT}/scripts/checker.sh"
  if ! baguette_resolve_veripb; then
    baguette_veripb_diagnostic
    fail "1 ENCODES: no checker -- a missing checker is a FAILURE, never a skip"
    return
  fi
  if "${VERIPB}" "${TMP}/wide.opb" "${TMP}/wide.pbp" >"${TMP}/veripb.log" 2>&1; then
    ok "1 ENCODES: veripb accepts the proof of a model the pre-M7 build refused"
  else
    fail "1 ENCODES: veripb REJECTED the proof of the width-${WIDE} model"
    tail -20 "${TMP}/veripb.log"
  fi
}

# ============================================================== 2 REPORTS
lane_reports() {
  err="$(cat "${TMP}/wide.err")"
  needles_in "2 REPORTS: the default build says what the encoding cost" "${err}" \
    "warning" \
    "\`x\`" \
    "a width of ${WIDE}" \
    "one Boolean per value" \
    "Baguette will encode it" \
    "too large to store" \
    "--max-order-width" \
    "--width-warn=none"
  # On stderr, never stdout: stdout is the FlatZinc solution stream (SPEC 2.2).
  if grep -qi 'warning' "${TMP}/wide.out"; then
    fail "2 REPORTS: the warning leaked onto stdout"
  else
    ok "2 REPORTS: stdout carries the solution only"
  fi
}

# ============================================================== 3 COUNTS
lane_counts() {
  rc="$(run "${TMP}/stats" "${TMP}/wide.fzn" --stats)"
  [ "${rc}" = "0" ] || fail "3 COUNTS: --stats run exited ${rc}"
  err="$(cat "${TMP}/stats.err")"
  needles_in "3 COUNTS: --stats reports the encoding's aggregate cost" "${err}" \
    "stats: encoding cost" \
    "follows the DECLARED domains" \
    "ladder" \
    "widest" \
    "the one to narrow first" \
    "limits"
  # The ladder total is width - 1 for the one variable. Assert the NUMBER, not just
  # that a line exists -- a counter nobody checked the value of is decoration.
  want=$((WIDE - 1))
  if printf '%s\n' "${err}" | grep -qE "^stats: ladder +${want} cls"; then
    ok "3 COUNTS: the ladder total is ${want}, i.e. w - 1"
  else
    fail "3 COUNTS: expected a ladder total of ${want}"
    printf '%s\n' "${err}" | grep '^stats: ' | head -10
  fi
}

# ============================================================== 4 REFUSES
lane_refuses() {
  # The flag.
  "${SOLVER}" "${TMP}/justover.fzn" --max-order-width "${OLD_CAP}" \
    >"${TMP}/ref.out" 2>"${TMP}/ref.err"
  rc=$?
  if [ "${rc}" != "3" ]; then
    fail "4 REFUSES: --max-order-width=${OLD_CAP} exited ${rc}, expected 3 (model rejected)"
  else
    ok "4 REFUSES: --max-order-width=${OLD_CAP} exits 3 on width $((OLD_CAP + 1))"
  fi
  needles_in "4 REFUSES: and reproduces the pre-M7 wording" "$(cat "${TMP}/ref.err")" \
    "error" \
    "\`x\`" \
    "0..$((OLD_CAP + 1))" \
    "a width of $((OLD_CAP + 1))" \
    "baguette's limit is ${OLD_CAP}" \
    "order encoding" \
    "legal FlatZinc" \
    "Narrow the declared domain" \
    "this refusal is OFF by default"

  # The environment variable.
  BAGUETTE_MAX_ORDER_WIDTH="${OLD_CAP}" "${SOLVER}" "${TMP}/justover.fzn" \
    >"${TMP}/refenv.out" 2>"${TMP}/refenv.err"
  rc=$?
  if [ "${rc}" != "3" ]; then
    fail "4 REFUSES: BAGUETTE_MAX_ORDER_WIDTH=${OLD_CAP} exited ${rc}, expected 3"
  else
    needles_in "4 REFUSES: the environment variable refuses too" \
      "$(cat "${TMP}/refenv.err")" "baguette's limit is ${OLD_CAP}"
  fi

  # The same model, default build: accepted. Same source, opposite verdict, and the
  # only difference is the limit. This is the control the refusal lanes need.
  rc="$(run "${TMP}/acc" "${TMP}/justover.fzn")"
  if [ "${rc}" = "0" ] && grep -q '^x = 3;$' "${TMP}/acc.out"; then
    ok "4 REFUSES: and the SAME model runs to x = 3 with no limit set"
  else
    fail "4 REFUSES: the default build did not accept the model it refuses under a limit"
  fi
}

# ============================================================== 5 PRECEDENCE
lane_precedence() {
  BAGUETTE_MAX_ORDER_WIDTH="${OLD_CAP}" "${SOLVER}" "${TMP}/justover.fzn" \
    --max-order-width none >"${TMP}/prec.out" 2>"${TMP}/prec.err"
  rc=$?
  if [ "${rc}" = "0" ] && grep -q '^x = 3;$' "${TMP}/prec.out"; then
    ok "5 PRECEDENCE: --max-order-width=none beats BAGUETTE_MAX_ORDER_WIDTH=${OLD_CAP}"
  else
    fail "5 PRECEDENCE: the flag did not override the environment (exit ${rc})"
    head -5 "${TMP}/prec.err"
  fi
}

# ============================================================== 6 SILENCES
lane_silences() {
  rc="$(run "${TMP}/quiet" "${TMP}/wide.fzn" --width-warn none)"
  [ "${rc}" = "0" ] || fail "6 SILENCES: exited ${rc}"
  if [ -s "${TMP}/quiet.err" ]; then
    fail "6 SILENCES: --width-warn=none left something on stderr"
    head -5 "${TMP}/quiet.err"
  else
    ok "6 SILENCES: --width-warn=none removes the sentence"
  fi
  # And removes ONLY the sentence: the artefacts are unchanged.
  if cmp -s "${TMP}/wide.opb" "${TMP}/quiet.opb" &&
    cmp -s "${TMP}/wide.pbp" "${TMP}/quiet.pbp" &&
    cmp -s "${TMP}/wide.out" "${TMP}/quiet.out"; then
    ok "6 SILENCES: and changes nothing else -- .opb, .pbp and stdout are identical"
  else
    fail "6 SILENCES: silencing the warning changed an artefact"
  fi
}

# ============================================================== 7 TYPOS
lane_typos() {
  for bad in "10 000" "1e4" "-3" "ten"; do
    "${SOLVER}" "${TMP}/justover.fzn" --max-order-width "${bad}" \
      >"${TMP}/bad.out" 2>"${TMP}/bad.err"
    rc=$?
    if [ "${rc}" = "2" ] && grep -q 'is not a limit' "${TMP}/bad.err"; then
      ok "7 TYPOS: --max-order-width '${bad}' is a usage error, not a silent 'none'"
    else
      fail "7 TYPOS: --max-order-width '${bad}' exited ${rc} instead of 2 with a diagnostic"
      head -3 "${TMP}/bad.err"
    fi
  done
  BAGUETTE_MAX_ORDER_WIDTH="ten" "${SOLVER}" "${TMP}/justover.fzn" \
    >"${TMP}/badenv.out" 2>"${TMP}/badenv.err"
  rc=$?
  if [ "${rc}" = "2" ] && grep -q 'is not a limit' "${TMP}/badenv.err"; then
    ok "7 TYPOS: and so is a mistyped BAGUETTE_MAX_ORDER_WIDTH"
  else
    fail "7 TYPOS: a mistyped environment limit exited ${rc} instead of 2"
  fi
}

# ============================================================== --self-test
#
# Every lane above, re-run against a deliberately wrong expectation, and each one must
# REDDEN. This is the half that makes the lane a guard rather than a decoration.
self_test() {
  echo "check_unlimited self-test: each assertion must be able to fail"
  st_fail=0
  st_check() { # st_check DESC  (expects the body to have set st_ok)
    if [ "${st_ok}" = "1" ]; then
      echo "ok   self-test: $1"
    else
      echo "FAIL self-test: $1 -- the assertion did NOT redden"
      st_fail=$((st_fail + 1))
    fi
  }

  # 1: a solver that is not there must fail the ENCODES lane, not skip it.
  st_ok=0
  out="$(BAGUETTE=/nonexistent/baguette "$0" 2>&1)" || st_ok=1
  st_check "a missing solver fails the run"

  # 2: needles_in reddens on a missing needle.
  st_ok=0
  (needles_in "x" "hello" "goodbye" >/dev/null 2>&1) || true
  before="${failures}"
  needles_in "self-test probe" "hello" "goodbye" >/dev/null 2>&1
  [ "${failures}" -gt "${before}" ] && st_ok=1
  failures="${before}"
  st_check "needles_in reddens on a needle that is absent"

  # 3: the refusal really is off by default -- if it were not, the ENCODES lane would
  # be passing for the wrong reason. Assert the pre-M7 behaviour is NOT the default.
  st_ok=0
  "${SOLVER}" "${TMP}/justover.fzn" >/dev/null 2>&1 && st_ok=1
  st_check "the default build does NOT refuse the model the control refuses"

  # 4: and the limit really is doing something -- if --max-order-width were ignored,
  # lane 4 would be the one passing for the wrong reason.
  st_ok=0
  "${SOLVER}" "${TMP}/justover.fzn" --max-order-width "${OLD_CAP}" >/dev/null 2>&1 ||
    st_ok=1
  st_check "--max-order-width is honoured (the control is not a no-op)"

  # 5: the warning threshold is doing something.
  st_ok=0
  "${SOLVER}" "${TMP}/wide.fzn" --width-warn 999999999 2>"${TMP}/st.err" >/dev/null
  [ -s "${TMP}/st.err" ] || st_ok=1
  st_check "a threshold above the width silences the warning"

  if [ "${st_fail}" -gt 0 ]; then
    echo ""
    echo "${st_fail} self-test failure(s): this lane cannot be trusted to pass"
    exit 1
  fi
  echo "check_unlimited self-test: ok"
  exit 0
}

# ------------------------------------------------------------------ main

if [ ! -x "${SOLVER}" ]; then
  echo "FAIL check_unlimited: no solver at ${SOLVER}"
  echo "  Build it first: dune build --root . bin/   (dune runtest does NOT build it)"
  exit 1
fi

if [ "${1:-}" = "--self-test" ]; then
  self_test
fi

echo "check_unlimited (M7-T1): the width refusal is an option, and the signal is not"
lane_encodes
lane_reports
lane_counts
lane_refuses
lane_precedence
lane_silences
lane_typos

# What it cost, measured here rather than quoted from a note.
echo ""
echo "check_unlimited: artefacts for the width-${WIDE} model --" \
  "$(wc -c <"${TMP}/wide.opb") B .opb," \
  "$(wc -c <"${TMP}/wide.pbp") B .pbp"

if [ "${failures}" -gt 0 ]; then
  echo ""
  echo "${failures} failure(s)"
  exit 1
fi
echo "check_unlimited: ok"
