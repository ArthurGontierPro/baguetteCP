#!/usr/bin/env bash
# M19-config-T1 (D-0261). THE FREE SEARCH'S MODEL TESTS: every model of test/models/ again,
# under the free search (D-0259 makes it the default), with its own checks.
#
#   scripts/free_model_tests.sh          (no arguments; `make models-free` runs it)
#
# scripts/run_model_tests.sh pins the fixed search (--fixed-search) and compares stdout with
# test/expected/ byte for byte. The free search cannot be held to those bytes: on a
# satisfaction model it may print another solution, and on an optimisation model another
# sequence of improving solutions. So each model is held here to what does not depend on
# the search:
#   1. the run exits 0 and writes nothing on stderr (M1-T49);
#   2. veripb VERIFIES its proof;
#   3. its STATUS, the last line of stdout (`----------`, `==========` or
#      `=====UNSATISFIABLE=====`), is the last line of test/expected/<model>.out;
#   4. its OBJECTIVE, `%%%mzn-stat: objective=` under -s, is the fixed search's (both read
#      without a proof; the fixed side is run_model_tests.sh's to verify);
#   5. its printed SOLUTION (the last one) is a solution of the model: the model with every
#      printed value fixed (scripts/fzn_fix_solution.py) is solved again by the fixed search
#      with a proof, which must end on `----------` and which veripb must verify;
#   6. the same search without a proof prints the same stdout and exit code (D-0126), the
#      `%%%mzn-stat:` lines of -s aside.
# A model listed in test/models/PENDING is skipped and named.
#
# The search under test is $FREE_SEARCH, default empty: the solver's default, the free search
# since D-0261. FREE_SEARCH=-f runs the same search by its MiniZinc flag.
# The solver is $BAGUETTE (default _build/default/bin/main.exe); this script does NOT build it.
# Exit 0 when nothing failed, 1 otherwise, 2 when the solver or the checker is missing.
set -uo pipefail

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
read -r -a FREE <<< "${FREE_SEARCH:-}"
# shellcheck source=checker.sh
. "${ROOT}/scripts/checker.sh"
OUT="${ROOT}/test/out/free"
mkdir -p "${OUT}"
PENDING="${ROOT}/test/models/PENDING"
is_pending() {
  [ -f "${PENDING}" ] || return 1
  grep -v '^[[:space:]]*#' "${PENDING}" 2>/dev/null | awk '{print $1}' | grep -qx "$1"
}

if [ ! -x "${SOLVER}" ]; then
  echo "solver not built at ${SOLVER} -- run 'make build' first" >&2
  exit 2
fi
if ! baguette_resolve_veripb; then
  echo "free_model_tests.sh: no proof was checked, so nothing here passed." >&2
  baguette_veripb_diagnostic
  exit 2
fi
echo "checker: ${VERIPB}; search under test: ${FREE_SEARCH:-the default}"

# Check 5 proves it can fail before it is trusted to pass (the `lint` discipline): on
# array_sat, whose only solution is q = [1, 4], a planted q = [2, 3] must be refused by the
# fixed search and the true one accepted.
solution_check_self_test() {
  local t="${OUT}/.self-test" m="${ROOT}/test/models/array_sat.fzn" v
  for v in "2, 3:=====UNSATISFIABLE=====" "1, 4:----------"; do
    printf 'q = array1d(1..2, [%s]);\n----------\n' "${v%%:*}" > "${t}.out"
    python3 -I "${ROOT}/scripts/fzn_fix_solution.py" "${m}" "${t}.out" > "${t}.fzn" &&
      "${SOLVER}" "${t}.fzn" --fixed-search --no-proof > "${t}.res" 2> /dev/null
    if [ "$(tail -1 "${t}.res")" != "${v#*:}" ]; then
      echo "FAIL free_model_tests self-test: q = [${v%%:*}] gave [$(tail -1 "${t}.res")], not [${v#*:}]."
      echo "     The solution check (5) cannot be trusted; nothing below was run."
      exit 1
    fi
  done
  rm -f "${t}".*
  echo "self-test: the solution check refuses a planted wrong solution and accepts the true one"
}
solution_check_self_test

pass=0; fail=0; skip=0; checked_sol=0
bad() { echo "FAIL  $1: $2"; fail=$((fail + 1)); }
objective() { grep -m1 '^%%%mzn-stat: objective=' "$1" | cut -d= -f2; }

for fzn in "${ROOT}"/test/models/*.fzn; do
  base="$(basename "${fzn}" .fzn)"
  expected="${ROOT}/test/expected/${base}.out"
  p="${OUT}/${base}"
  if [ ! -f "${expected}" ]; then echo "SKIP  ${base}: no expected output"; skip=$((skip + 1)); continue; fi
  if is_pending "${base}"; then echo "SKIP  ${base}: listed in test/models/PENDING"; skip=$((skip + 1)); continue; fi

  # 1
  "${SOLVER}" "${fzn}" "${FREE[@]+"${FREE[@]}"}" --proof "${p}" > "${p}.out" 2> "${p}.err"
  rc=$?
  if [ "${rc}" -ne 0 ]; then bad "${base}" "the run exited ${rc}"; sed 's/^/       /' "${p}.err" | head -5; continue; fi
  if [ -s "${p}.err" ]; then bad "${base}" "the run wrote to stderr (M1-T49)"; sed 's/^/       /' "${p}.err" | head -5; continue; fi
  # 2
  if ! "${VERIPB}" "${p}.opb" "${p}.pbp" > "${p}.veripb" 2>&1 || ! grep -q '^s VERIFIED' "${p}.veripb"; then
    bad "${base}" "veripb REJECTED the proof (opb=${p}.opb proof=${p}.pbp)"
    tail -5 "${p}.veripb" | sed 's/^/       /'
    continue
  fi
  # 3
  st_new="$(grep -v '^[[:space:]]*$' "${p}.out" | tail -1)"
  st_ref="$(grep -v '^[[:space:]]*$' "${expected}" | tail -1)"
  if [ "${st_new}" != "${st_ref}" ]; then bad "${base}" "status [${st_new}], expected [${st_ref}]"; continue; fi
  # 4 and 6
  "${SOLVER}" "${fzn}" --fixed-search -s --no-proof > "${p}.fixed.s" 2> /dev/null
  "${SOLVER}" "${fzn}" "${FREE[@]+"${FREE[@]}"}" -s --no-proof > "${p}.noproof.s" 2> /dev/null
  rc2=$?
  o_ref="$(objective "${p}.fixed.s")"; o_new="$(objective "${p}.noproof.s")"
  if [ "${o_new}" != "${o_ref}" ]; then bad "${base}" "objective [${o_new}], the fixed search's [${o_ref}]"; continue; fi
  if [ "${rc2}" -ne 0 ] || ! cmp -s "${p}.out" <(grep -v '^%%%mzn-stat' "${p}.noproof.s"); then
    bad "${base}" "--no-proof differs from the proved run (rc ${rc2}, D-0126)"
    diff <(cat "${p}.out") <(grep -v '^%%%mzn-stat' "${p}.noproof.s") | head -10 | sed 's/^/       /'
    continue
  fi
  # 5
  if [ "${st_new}" != "=====UNSATISFIABLE=====" ]; then
    if ! python3 -I "${ROOT}/scripts/fzn_fix_solution.py" "${fzn}" "${p}.out" > "${p}.fixed.fzn" 2> "${p}.fix.err"; then
      bad "${base}" "the printed solution could not be read: $(head -1 "${p}.fix.err")"; continue
    fi
    "${SOLVER}" "${p}.fixed.fzn" --fixed-search --proof "${p}.sol" > "${p}.sol.out" 2> "${p}.sol.err"
    rc3=$?
    if [ "${rc3}" -ne 0 ] || [ "$(grep -v '^[[:space:]]*$' "${p}.sol.out" | tail -1)" != "----------" ]; then
      bad "${base}" "the printed solution is NOT a solution of the model (rc ${rc3}: $(tail -1 "${p}.sol.out") $(head -1 "${p}.sol.err"))"
      continue
    fi
    if ! "${VERIPB}" "${p}.sol.opb" "${p}.sol.pbp" > "${p}.sol.veripb" 2>&1 || ! grep -q '^s VERIFIED SATISFIABLE' "${p}.sol.veripb"; then
      bad "${base}" "the printed solution's check was not verified: $(grep '^s ' "${p}.sol.veripb" | head -1)"; continue
    fi
    checked_sol=$((checked_sol + 1))
  fi
  rm -f "${p}.opb" "${p}.pbp" "${p}.sol.opb" "${p}.sol.pbp"
  echo "PASS  ${base}"
  pass=$((pass + 1))
done

echo
echo "free model tests: ${pass} passed, ${fail} failed, ${skip} skipped (search: ${FREE_SEARCH:-the default})"
echo "  every PASS: proof verified, status as expected, objective the fixed search's, the same"
echo "  stdout without a proof (D-0126), and, on ${checked_sol} model(s) with a printed solution,"
echo "  that solution fixed in the model and verified satisfiable by a second proved run."
[ "${fail}" -eq 0 ]
