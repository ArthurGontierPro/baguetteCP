#!/usr/bin/env bash
# Solve every model in test/models/, compare stdout against test/expected/,
# and verify the emitted proof with veripb.
#
# A model that produces the right answer with a proof veripb rejects is a FAILURE.
#
# M9-no-proof-T2 (D-0126): and then solve it AGAIN under `--no-proof`, and require stdout
# and the exit code to be byte-identical to the proved run's. This is the only test in the
# tree that runs the solver without a proof (docs/SPEC.md section 1 forbids every other
# one), and it is the first direct test that proof logging never steers the search: the
# justifications, the trace lines and the deletions are the one thing the two runs do not
# share, so a difference here is a finding about the PROVED run -- something in Justify,
# Trace or Writer fed a decision, a wake or a reason -- and never a reason to touch the
# no-proof side. The proved side is the ordinary run above, so the lane costs one
# unverified run per model and nothing it prints is a result (SPEC 1).
set -uo pipefail

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

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOLVER="${BAGUETTE:-${ROOT}/_build/default/bin/main.exe}"
# shellcheck source=checker.sh
. "${ROOT}/scripts/checker.sh"
OUT="${ROOT}/test/out"

mkdir -p "${OUT}"

pass=0; fail=0; skip=0; xfail=0; xpass=0

PENDING="${ROOT}/test/models/PENDING"

# Is this model known not to work yet? See test/models/PENDING.
is_pending() {
  [ -f "${PENDING}" ] || return 1
  grep -v '^[[:space:]]*#' "${PENDING}" 2>/dev/null \
    | awk '{print $1}' | grep -qx "$1"
}

# M4-T1 found a PENDING line naming a model that does not exist -- written while the
# model was planned, left behind when the reproducer became a unit check instead. Nothing
# complained, because an entry that matches no model simply never fires. That is the same
# silently-inert-config shape this project keeps meeting, so it is now an error: a PENDING
# entry is a claim about a model, and a claim about a model that is not there is stale.
check_pending_entries() {
  [ -f "${PENDING}" ] || return 0
  local missing=0 m
  for m in $(grep -v '^[[:space:]]*#' "${PENDING}" 2>/dev/null | awk '{print $1}'); do
    [ -n "${m}" ] || continue
    if [ ! -f "${ROOT}/test/models/${m}.fzn" ]; then
      echo "FAIL test/models/PENDING lists \`${m}\`, but test/models/${m}.fzn does not exist."
      echo "     A PENDING entry is a claim about a model. Delete the line, or add the model."
      missing=$((missing + 1))
    fi
  done
  [ "${missing}" -eq 0 ]
}

pending_reason() {
  grep -v '^[[:space:]]*#' "${PENDING}" 2>/dev/null \
    | awk -v m="$1" '$1 == m { $1 = ""; sub(/^ +/, ""); print }'
}

# Report an outcome, accounting for whether the model was expected to fail.
# $1 = basename, $2 = "pass" or "fail", $3 = detail shown on an unexpected result
report() {
  local base="$1" outcome="$2" detail="${3:-}"
  if is_pending "${base}"; then
    if [ "${outcome}" = "pass" ]; then
      echo "XPASS ${base}: listed in test/models/PENDING but it PASSES now."
      echo "       Delete its line from test/models/PENDING."
      xpass=$((xpass+1))
      return 1
    fi
    echo "xfail ${base}: $(pending_reason "${base}")"
    xfail=$((xfail+1))
    return 0
  fi
  if [ "${outcome}" = "pass" ]; then
    echo "PASS  ${base}"
    pass=$((pass+1))
    return 0
  fi
  echo "FAIL  ${base}: ${detail}"
  fail=$((fail+1))
  return 1
}

if [ ! -x "${SOLVER}" ]; then
  echo "solver not built at ${SOLVER} — run 'make build' first" >&2
  exit 2
fi

# No checker is a failure of the whole run, not a per-model skip: "a test that does
# not check the proof is half a test" (CLAUDE.md). This used to set have_veripb=0 and
# report every model as "PASS (output only; proof NOT checked)" against a skip count.
if ! baguette_resolve_veripb; then
  echo "run_model_tests.sh: no proof was checked, so nothing here passed." >&2
  baguette_veripb_diagnostic
  exit 2
fi
echo "checker: ${VERIPB}"

for fzn in "${ROOT}"/test/models/*.fzn; do
  base="$(basename "${fzn}" .fzn)"
  expected="${ROOT}/test/expected/${base}.out"
  prefix="${OUT}/${base}"

  if [ ! -f "${expected}" ]; then
    echo "SKIP ${base}: no expected output in test/expected/"
    skip=$((skip+1))
    continue
  fi

  "${SOLVER}" "${fzn}" --proof "${prefix}" > "${prefix}.out" 2> "${prefix}.err"
  rc=$?

  if [ "${rc}" -ne 0 ]; then
    if report "${base}" fail "solver exited ${rc}"; then continue; fi
    sed 's/^/       /' "${prefix}.err" | head -5
    continue
  fi

  # M1-T49: with no --time (and no --proof-comments reaching a call site -- see
  # M1-T48), stderr should be empty. This is the only thing in `make check`'s path
  # that would notice a model start writing to stderr unasked; diff above only looks
  # at stdout. If a model earns a legitimate stderr line some day, this needs to
  # become a per-model expected-stderr comparison rather than being loosened to skip
  # the check -- do not just delete this block to get past it.
  if [ -s "${prefix}.err" ]; then
    if report "${base}" fail "solver wrote to stderr with no --time flag (M1-T49)"; then continue; fi
    sed 's/^/       /' "${prefix}.err" | head -20
    continue
  fi

  if ! diff -u "${expected}" "${prefix}.out" > "${prefix}.diff"; then
    if report "${base}" fail "output differs from test/expected/${base}.out"; then continue; fi
    sed 's/^/       /' "${prefix}.diff" | head -20
    echo "       Do not edit the expected file to make this pass (invariant I-M1)."
    continue
  fi

  if ! "${VERIPB}" "${prefix}.opb" "${prefix}.pbp" > "${prefix}.veripb" 2>&1; then
    if report "${base}" fail "veripb rejected the proof"; then continue; fi
    sed 's/^/       /' "${prefix}.veripb" | tail -20
    echo "       opb=${prefix}.opb proof=${prefix}.pbp"
    echo "       See docs/PROOF-FORMAT.md section 6 before changing anything."
    continue
  fi

  # M9-no-proof-T2 (D-0126): the stdout-identity lane. The proved run above is the
  # reference; this run writes no .opb, no .pbp and no justification, and must print
  # the same bytes and exit the same way. See the header. A model listed in PENDING
  # never gets here (the proved run already reported it).
  "${SOLVER}" "${fzn}" --no-proof > "${prefix}.noproof.out" 2> "${prefix}.noproof.err"
  rc2=$?
  if [ "${rc2}" -ne "${rc}" ]; then
    if report "${base}" fail "--no-proof exited ${rc2} where the proved run exited ${rc} (M9-no-proof-T2)"; then continue; fi
    sed 's/^/       /' "${prefix}.noproof.err" | head -5
    continue
  fi
  if [ -s "${prefix}.noproof.err" ]; then
    if report "${base}" fail "--no-proof wrote to stderr with no --time flag (M1-T49)"; then continue; fi
    sed 's/^/       /' "${prefix}.noproof.err" | head -20
    continue
  fi
  if ! cmp -s "${prefix}.out" "${prefix}.noproof.out"; then
    if report "${base}" fail "--no-proof stdout DIFFERS from the proved run (M9-no-proof-T2)"; then continue; fi
    diff -u "${prefix}.out" "${prefix}.noproof.out" | sed 's/^/       /' | head -20
    echo "       D-0126: the proof was steering the search. This is a finding about the PROVED"
    echo "       run (Justify, Trace or Writer fed a decision, a wake or a reason). Record it;"
    echo "       do not make this lane pass by changing the no-proof side."
    continue
  fi
  report "${base}" pass || true
done

# M9-no-proof-T2 (D-0126, D-0135): the same identity at `--bits-above 0`, on the bits_*
# models. The pass above runs them at the default W = none, where nothing is on the bits
# encoding; here every eligible variable is, so atoms are minted on demand
# ([Encoding.ensure_atom], D-0132) -- through the page in the proved run and not at all
# under `--no-proof`, whose justifications are never rendered -- and the proof-side ids
# the two runs mint after `start_proof` diverge. That is allowed (D-0126's id rule, point
# 3: no Explanation carries one) and this lane is what checks that the search never reads
# one. The proved side is verified by veripb here too; its stdout is NOT compared with
# test/expected/, which records the W = none run, only with the --no-proof run's.
bits_pass=0
for fzn in "${ROOT}"/test/models/bits_*.fzn; do
  [ -f "${fzn}" ] || continue
  base="$(basename "${fzn}" .fzn)"
  prefix="${OUT}/${base}.w0"
  "${SOLVER}" "${fzn}" --bits-above 0 --proof "${prefix}" > "${prefix}.out" 2> "${prefix}.err"
  rc=$?
  if [ "${rc}" -ne 0 ] || [ -s "${prefix}.err" ]; then
    echo "FAIL  ${base} (--bits-above 0): the proved run exited ${rc} or wrote to stderr"
    sed 's/^/       /' "${prefix}.err" | head -5
    fail=$((fail+1)); continue
  fi
  if ! "${VERIPB}" "${prefix}.opb" "${prefix}.pbp" > "${prefix}.veripb" 2>&1; then
    echo "FAIL  ${base} (--bits-above 0): veripb rejected the proof"
    sed 's/^/       /' "${prefix}.veripb" | tail -20
    fail=$((fail+1)); continue
  fi
  "${SOLVER}" "${fzn}" --bits-above 0 --no-proof > "${prefix}.noproof.out" 2> "${prefix}.noproof.err"
  rc2=$?
  if [ "${rc2}" -ne "${rc}" ] || [ -s "${prefix}.noproof.err" ]; then
    echo "FAIL  ${base} (--bits-above 0): --no-proof exited ${rc2} where the proved run exited ${rc}, or wrote to stderr (M9-no-proof-T2)"
    sed 's/^/       /' "${prefix}.noproof.err" | head -5
    fail=$((fail+1)); continue
  fi
  if ! cmp -s "${prefix}.out" "${prefix}.noproof.out"; then
    echo "FAIL  ${base} (--bits-above 0): --no-proof stdout DIFFERS from the proved run (M9-no-proof-T2)"
    diff -u "${prefix}.out" "${prefix}.noproof.out" | sed 's/^/       /' | head -20
    echo "       D-0126: a finding about the PROVED run. Record it; do not change the no-proof side."
    fail=$((fail+1)); continue
  fi
  echo "PASS  ${base} (--bits-above 0)"
  bits_pass=$((bits_pass+1))
done
if [ "${bits_pass}" -eq 0 ]; then
  echo "FAIL  the --bits-above 0 identity lane ran on NO model: test/models/bits_*.fzn is empty."
  fail=$((fail+1))
fi

# M10-search-strategy-T2/T3 (D-0137): every restart_*.fzn again WITH the opt-in search
# strategies on -- restarts after every learned conflict at first (luby:1), phase saving,
# and the annotation alternating with the activity order. The main pass above already ran
# these models with no flag, so this lane checks what the flags may change and what they
# may not: the proof is VERIFIED, the --no-proof run's stdout and exit code are the
# proved run's (D-0126), the ANSWER is the default run's (veripb's verdict line, which for
# an optimisation includes the proved bounds; a satisfiable model may print a different
# solution, which is allowed), and the search really restarted. A lane whose flag was not
# in force is the trap CLAUDE.md records twice, hence the last check.
restart_pass=0
RFLAGS=(--restarts luby:1 --phase-saving --search alternate)
for fzn in "${ROOT}"/test/models/restart_*.fzn; do
  [ -f "${fzn}" ] || continue
  base="$(basename "${fzn}" .fzn)"
  prefix="${OUT}/${base}.rs"
  "${SOLVER}" "${fzn}" "${RFLAGS[@]}" --proof "${prefix}" > "${prefix}.out" 2> "${prefix}.err"
  rc=$?
  if [ "${rc}" -ne 0 ] || [ -s "${prefix}.err" ]; then
    echo "FAIL  ${base} (restarts): the proved run exited ${rc} or wrote to stderr"
    sed 's/^/       /' "${prefix}.err" | head -5
    fail=$((fail+1)); continue
  fi
  if ! "${VERIPB}" "${prefix}.opb" "${prefix}.pbp" > "${prefix}.veripb" 2>&1; then
    echo "FAIL  ${base} (restarts): veripb rejected the proof"
    sed 's/^/       /' "${prefix}.veripb" | tail -20
    fail=$((fail+1)); continue
  fi
  v_new="$(grep -E '^s ' "${prefix}.veripb" | head -1)"
  v_ref="$(grep -E '^s ' "${OUT}/${base}.veripb" 2>/dev/null | head -1)"
  if [ -z "${v_new}" ] || [ "${v_new}" != "${v_ref}" ]; then
    echo "FAIL  ${base} (restarts): verdict [${v_new}] is not the default run's [${v_ref}]"
    fail=$((fail+1)); continue
  fi
  "${SOLVER}" "${fzn}" "${RFLAGS[@]}" --no-proof > "${prefix}.noproof.out" 2> "${prefix}.noproof.err"
  rc2=$?
  if [ "${rc2}" -ne "${rc}" ] || [ -s "${prefix}.noproof.err" ] \
     || ! cmp -s "${prefix}.out" "${prefix}.noproof.out"; then
    echo "FAIL  ${base} (restarts): --no-proof differs from the proved run (rc ${rc2}, D-0126)"
    fail=$((fail+1)); continue
  fi
  nr="$("${SOLVER}" "${fzn}" "${RFLAGS[@]}" --no-proof --stats 2>&1 > /dev/null \
        | awk '/^stats: restarts /{print $3}')"
  if [ -z "${nr}" ] || [ "${nr}" -eq 0 ]; then
    echo "FAIL  ${base} (restarts): the search did not restart (stats: restarts '${nr}')"
    fail=$((fail+1)); continue
  fi
  echo "PASS  ${base} (restarts: ${nr})"
  restart_pass=$((restart_pass+1))
done
if [ "${restart_pass}" -eq 0 ]; then
  echo "FAIL  the restart lane ran on NO model: test/models/restart_*.fzn is empty."
  fail=$((fail+1))
fi

echo
echo "model tests: ${pass} passed, ${fail} failed, ${xfail} expected-fail, ${xpass} unexpected-pass, ${skip} skipped"
echo "  every PASS is a proof veripb accepted AND a --no-proof run whose stdout and exit code"
echo "  are byte-identical to it (M9-no-proof-T2, D-0126); ${bits_pass} bits_* model(s) passed"
echo "  the same identity at --bits-above 0, proof verified; ${restart_pass} restart_* model(s)"
echo "  passed again with restarts, phase saving and the alternating order (M10, D-0137)."

if [ "${xfail}" -gt 0 ]; then

  echo "  ${xfail} model(s) are listed in test/models/PENDING and are not yet expected to"
  echo "  work. That file should be empty by M1-T11."
fi
if [ "${xpass}" -gt 0 ]; then
  echo "  ${xpass} model(s) pass but are still listed in test/models/PENDING. Remove them."
fi

check_pending_entries || fail=$((fail + 1))

[ "${fail}" -eq 0 ] && [ "${xpass}" -eq 0 ]
