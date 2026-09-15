#!/usr/bin/env bash
# Corrupt one step of an emitted proof and assert that veripb REJECTS the result.
#
#   scripts/mutate_proof.sh pol-coeff test/out/lin_unsat.pbp
#   scripts/mutate_proof.sh control   test/out/lin_unsat.pbp
#   scripts/mutate_proof.sh --list
#
# The inverse of scripts/verify_proof.sh, and it exists for the reason the Glasgow
# Constraint Solver's own run_test_and_expect_verify_failure.bash gives:
#
#   A propagator whose derivation has slack in it writes proofs that verify even when
#   one step is deliberately corrupted -- so "veripb accepts" on its own says little
#   about whether the honest derivation is load-bearing. The run passes only if veripb
#   says no. If veripb accepts, the honest derivation was slack, and that is a finding
#   about the propagator, not about the harness.
#
# The mutation is named, deterministic (same proof in, same corruption out) and applied
# to a COPY: the proof you point this at is never written to. `control` applies no
# corruption and passes only if veripb accepts -- a mutation lane whose instance does
# not verify honestly is green for no reason at all, so every mutation lane is paired
# with a control lane on the same instance.
#
# Exit codes -- distinct on purpose, because "the lane did nothing" must not look like
# "the lane passed":
#
#   0  the lane holds:   veripb rejected the corrupted proof (or accepted the control)
#   1  the lane FAILED:  veripb accepted a corrupted proof -- the honest derivation has
#                        slack in it. This is the finding the harness exists to produce;
#                        it belongs in docs/DECISIONS.md, not in a re-run.
#   2  usage or environment error
#   3  the mutation does not apply to this proof (no eligible line). NOT a pass: the
#      caller must report the lane as not-run, never as green.
#   4  veripb is not available, so nothing was checked. Also not a pass.
set -uo pipefail

usage() {
  cat >&2 <<EOF
usage: mutate_proof.sh [--nth N] [--keep] MUTATION PROOF.pbp [MODEL.opb]
       mutate_proof.sh --list

MODEL.opb defaults to PROOF.pbp with its extension replaced.
--nth N   apply the mutation to the Nth eligible site instead of the default one.
--keep    keep the corrupted proof even when the lane holds (see also
          BAGUETTE_PRESERVE_PROOF_FILES=1).
EOF
  exit 2
}

list_mutations() {
  cat <<'EOF'
control        no corruption at all. Passes only if veripb ACCEPTS. Every mutation lane
               needs one of these on the same instance, or the lane proves nothing.
pol-coeff      perturb a coefficient inside one `pol` step: a divisor `N d` becomes
               `N+1 d`, a multiplier `N *` becomes `N+1 *`, and a bare literal axiom --
               which is the coefficient 1 -- becomes `lit 2 *`.
pol-cite       change a constraint id cited by a `pol` to a different id that is still
               live at that point in the proof.
rup-drop-lit   drop one literal from a `rup` clause -- the last term, which in a D-0018
               trace line is a reason literal rather than the claim. Prefers a clause
               emitted inside a decision level and refuses a unit clause outright; see
               "the reason trap" below.
rhs-const      raise by one the constant on the right-hand side of a claim (`rup`/`red`),
               which strengthens it. Picks its target the same way rup-drop-lit does, and
               falls back to a unit claim only with a note saying the lane proves little.
drop-line      delete one emitted derivation step entirely -- `pol`, `rup`, `red` or a
               solution rule, by default the last one. Never a `#`, `w` or `del`: failing
               to delete is not an error (PROOF-FORMAT section 5), so a lane built on one
               of those would be green for the wrong reason.
EOF
}

# --- the reason trap, from GCS dev_docs/constraints.md:1085 ------------------------
# Dropping a literal from a reason is only a corruption when that literal traces back to
# a *search decision*. Anything a propagator derived is written into the proof as a
# clause in its own right, so the checker has it whether or not the reason repeats it --
# a rule that fired during root propagation has a reason that merely restates the
# database, and dropping from it changes nothing veripb can see. Such a lane goes green
# on an empty corruption.
#
# `rup-drop-lit` encodes as much of that as is visible in the proof text: it will not
# touch a unit clause (dropping the only literal corrupts the *claim*, not the reason,
# and tests nothing about the reason), and it prefers a clause emitted at a decision
# level -- `# N` with N >= 1 -- over one at the root. It reports which it chose, so a
# lane that only had root-level clauses to work with can be read as such rather than
# being mistaken for a real test.

MUT=""
PROOF=""
OPB=""
NTH=1
KEEP="${BAGUETTE_PRESERVE_PROOF_FILES:-0}"

while [ $# -gt 0 ]; do
  case "$1" in
    --list) list_mutations; exit 0 ;;
    --nth) NTH="${2:?--nth needs a number}"; shift 2 ;;
    --keep) KEEP=1; shift ;;
    -h|--help) usage ;;
    -*) echo "mutate_proof.sh: unknown option $1" >&2; usage ;;
    *)
      if [ -z "${MUT}" ]; then MUT="$1"
      elif [ -z "${PROOF}" ]; then PROOF="$1"
      elif [ -z "${OPB}" ]; then OPB="$1"
      else echo "mutate_proof.sh: too many arguments" >&2; usage
      fi
      shift ;;
  esac
done

[ -n "${MUT}" ] || usage
[ -n "${PROOF}" ] || usage
case "${NTH}" in ''|*[!0-9]*) echo "mutate_proof.sh: --nth wants a positive integer, got '${NTH}'" >&2; exit 2 ;; esac
[ "${NTH}" -ge 1 ] || { echo "mutate_proof.sh: --nth wants a positive integer" >&2; exit 2; }

# Absolute, so nothing below depends on the caller's cwd.
case "${PROOF}" in /*) ;; *) PROOF="$(pwd)/${PROOF}" ;; esac
[ -f "${PROOF}" ] || { echo "mutate_proof.sh: no such proof: ${PROOF}" >&2; exit 2; }

if [ -z "${OPB}" ]; then OPB="${PROOF%.*}.opb"; fi
case "${OPB}" in /*) ;; *) OPB="$(pwd)/${OPB}" ;; esac
[ -f "${OPB}" ] || { echo "mutate_proof.sh: no model beside the proof: ${OPB}" >&2; exit 2; }

# shellcheck source=checker.sh
. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/checker.sh"
if ! baguette_resolve_veripb; then
  echo "mutate_proof.sh: veripb not found, so NOTHING was checked for ${MUT}." >&2
  baguette_veripb_diagnostic
  exit 4
fi

BASE="$(basename "${PROOF}" .pbp)"
LANE="${BASE}/${MUT}"

WORK="$(mktemp -d "${TMPDIR:-/tmp}/baguette-mutate-XXXXXX")" || exit 2
MUTATED="${WORK}/${BASE}.pbp"
MODEL="${WORK}/${BASE}.opb"
DESC="${WORK}/desc"
LOG="${WORK}/veripb.log"
cp "${OPB}" "${MODEL}"
: > "${DESC}"

cleanup() {
  if [ "${KEEP}" = "1" ]; then
    echo "     corrupted proof kept at ${WORK}"
  else
    rm -rf "${WORK}"
  fi
}

# ------------------------------------------------------------------ mutations
# Each awk program writes the mutated proof to stdout and one human-readable line to
# DESC saying what it changed. An empty DESC means "no eligible site" -> exit 3.

# How many constraints the `f` rule loads, and which ids a `del`/`delc` retires. Used by
# pol-cite to pick a replacement id that is still live.
f_count() { awk '$1=="f" {print $2; exit}' "${PROOF}"; }

# Pick the claim line to corrupt, and say where it came from: "branch" (emitted inside a
# decision level) or "root". Shared by `rup-drop-lit` and `rhs-const`, because both are
# subject to the same two traps.
#
# A claim with only ONE literal is the last resort for both of them:
#   - dropping its only literal corrupts the claim rather than the reason, so the lane
#     stops saying anything about the reason (the trap above);
#   - raising the right-hand side of a one-literal `>= 1` gives `>= 2`, which no checker
#     could ever accept whatever the derivation says, so the lane is green for a reason
#     that has nothing to do with the proof.
# Order of preference: multi-literal inside a decision level, multi-literal at the root,
# then -- announced, never silently -- a unit claim.
#
# $1 = 1 to allow a unit claim as a last resort, 0 to refuse one.
select_claim() {
  awk -v nth="${NTH}" -v allow_unit="$1" '
    function nterms(  i, c) {
      c = 0
      for (i = 2; i <= NF; i++) { if ($i == ">=") break; if ($i ~ /^[+-]?[0-9]+$/) c++ }
      return c
    }
    $1 == "#" { lvl = $2 + 0; next }
    $1 == "w" { lvl = $2 - 1; if (lvl < 0) lvl = 0; next }
    $1 == "rup" || $1 == "u" || $1 == "red" {
      n = nterms()
      if (n >= 2 && lvl >= 1) branch[++nb] = NR
      else if (n >= 2)        root[++nr] = NR
      else if (n == 1)        unit[++nu] = NR
    }
    END {
      if (nb >= nth) { print branch[nth], "branch"; exit }
      if (nr >= nth) { print root[nth], "root"; exit }
      if (allow_unit && nu >= nth) { print unit[nth], "unit"; exit }
    }' "${PROOF}"
}

# Say so when a lane had to settle for a weaker site than the one it wants.
warn_site() {
  case "$2" in
    root)
      echo "NOTE ${LANE}: the best available claim is at the ROOT level." >&2
      echo "     Read the reason trap in this script before believing this lane: a" >&2
      echo "     root-level reason restates facts the checker already has." >&2 ;;
    unit)
      echo "NOTE ${LANE}: the best available claim is a UNIT clause, so this lane" >&2
      echo "     corrupts the claim rather than the reason behind it. veripb will" >&2
      echo "     reject it either way; that says little about the derivation." >&2 ;;
  esac
}

case "${MUT}" in

  control)
    cp "${PROOF}" "${MUTATED}"
    printf 'no corruption (control lane)\n' > "${DESC}"
    ;;

  pol-coeff)
    awk -v nth="${NTH}" -v desc="${DESC}" '
      function isnum(t) { return t ~ /^-?[0-9]+$/ }
      function islit(t) { return t ~ /^~?[A-Za-z_][A-Za-z0-9_]*$/ }
      {
        if (!done && ($1 == "pol" || $1 == "p")) {
          n = split($0, t, " ")
          idx = 0; kind = ""
          for (i = 3; i <= n; i++)
            if (t[i] == "d" && isnum(t[i-1])) { idx = i-1; kind = "divisor"; break }
          if (idx == 0)
            for (i = 3; i <= n; i++)
              if (t[i] == "*" && isnum(t[i-1])) { idx = i-1; kind = "multiplier"; break }
          if (idx == 0)
            for (i = 2; i <= n; i++)
              if (islit(t[i])) { idx = i; kind = "axiom"; break }
          if (idx > 0) {
            hit++
            if (hit == nth) {
              before = $0
              if (kind == "axiom") t[idx] = t[idx] " 2 *"
              else                 t[idx] = t[idx] + 1
              out = t[1]
              for (i = 2; i <= n; i++) out = out " " t[i]
              printf "line %d: %s coefficient perturbed\n  before: %s\n   after: %s\n", \
                     NR, kind, before, out > desc
              print out
              done = 1
              next
            }
          }
        }
        print
      }' "${PROOF}" > "${MUTATED}"
    ;;

  pol-cite)
    DELETED="$(awk '($1=="del"||$1=="d"||$1=="delc") && $2=="id" {for(i=3;i<=NF;i++) printf "%s ", $i}' "${PROOF}")"
    awk -v nth="${NTH}" -v desc="${DESC}" -v nf="$(f_count)" -v deleted="${DELETED}" '
      function isnum(t) { return t ~ /^[0-9]+$/ }
      BEGIN {
        split(deleted, dd, " ")
        for (k in dd) if (dd[k] != "") dead[dd[k]] = 1
      }
      {
        if (!done && ($1 == "pol" || $1 == "p")) {
          n = split($0, t, " ")
          # An integer operand is an id unless the next token makes it a coefficient.
          idx = 0
          for (i = 2; i <= n; i++)
            if (isnum(t[i]) && t[i+1] != "*" && t[i+1] != "d") { idx = i; break }
          if (idx > 0) {
            delete cited
            for (i = 2; i <= n; i++) if (isnum(t[i])) cited[t[i]] = 1
            orig = t[idx] + 0
            cand = 0
            for (off = 1; off <= nf && cand == 0; off++) {
              for (s = -1; s <= 1 && cand == 0; s += 2) {
                c = orig + (s * off)
                if (c >= 1 && c <= nf && !(c in dead) && !(("" c) in cited)) cand = c
              }
            }
            if (cand > 0) {
              hit++
              if (hit == nth) {
                before = $0
                t[idx] = cand
                out = t[1]
                for (i = 2; i <= n; i++) out = out " " t[i]
                printf "line %d: cited id %d replaced by live id %d\n  before: %s\n   after: %s\n", \
                       NR, orig, cand, before, out > desc
                print out
                done = 1
                next
              }
            }
          }
        }
        print
      }' "${PROOF}" > "${MUTATED}"
    ;;

  rup-drop-lit)
    # Two passes: pick the target claim first, then rewrite it. A unit clause is never
    # eligible here -- dropping its only literal is not a corruption of a reason.
    TARGET="$(select_claim 0)"
    if [ -n "${TARGET}" ]; then
      TLINE="${TARGET% *}"; TWHERE="${TARGET#* }"
      awk -v tline="${TLINE}" -v where="${TWHERE}" -v desc="${DESC}" '
        NR == tline {
          before = $0
          n = split($0, t, " ")
          # Terms run from token 2 up to ">=", as (coefficient, literal) pairs. Drop the
          # LAST one: in a D-0018 trace line the claim comes first and the reason
          # literals follow, so the last term is the one that carries a decision.
          last = 0
          for (i = 2; i <= n; i++) { if (t[i] == ">=") break; if (t[i] ~ /^[+-]?[0-9]+$/) last = i }
          out = t[1]
          for (i = 2; i <= n; i++) {
            if (i == last || i == last + 1) continue
            out = out " " t[i]
          }
          printf "line %d: dropped the literal `%s %s` from a %s-level rup clause\n  before: %s\n   after: %s\n", \
                 NR, t[last], t[last+1], where, before, out > desc
          print out
          next
        }
        { print }' "${PROOF}" > "${MUTATED}"
      warn_site "${TLINE}" "${TWHERE}"
    else
      cp "${PROOF}" "${MUTATED}"
    fi
    ;;

  rhs-const)
    # Raising the constant strengthens the claim, so the checker has to reject it unless
    # the honest claim was weaker than it needed to be. Lowering it would weaken the
    # claim, which usually still checks -- that is not a test.
    TARGET="$(select_claim 1)"
    if [ -n "${TARGET}" ]; then
      TLINE="${TARGET% *}"; TWHERE="${TARGET#* }"
      awk -v tline="${TLINE}" -v where="${TWHERE}" -v desc="${DESC}" '
        NR == tline {
          before = $0
          n = split($0, t, " ")
          idx = 0
          for (i = 2; i < n; i++) if (t[i] == ">=" && t[i+1] ~ /^-?[0-9]+$/) { idx = i+1; break }
          if (idx == 0) { print; next }
          old = t[idx] + 0
          t[idx] = old + 1
          out = t[1]
          for (i = 2; i <= n; i++) out = out " " t[i]
          printf "line %d: right-hand side of a %s-level claim raised from %d to %d\n  before: %s\n   after: %s\n", \
                 NR, where, old, old + 1, before, out > desc
          print out
          next
        }
        { print }' "${PROOF}" > "${MUTATED}"
      warn_site "${TLINE}" "${TWHERE}"
    else
      cp "${PROOF}" "${MUTATED}"
    fi
    ;;

  drop-line)
    # Only a *derivation* step is eligible: `pol`, `rup`, `red` and the solution rules
    # that yield an id. Deleting anything else is not a corruption at all --
    # docs/PROOF-FORMAT.md section 5 says in so many words that "failing to delete does
    # not make a proof wrong", so a lane built on a dropped `w` is green for the wrong
    # reason, and a dropped `f`/`output`/`conclusion` tests the parser rather than the
    # derivation. Default target is the LAST such step, the one the conclusion leans on.
    TARGET="$(awk '
      $1=="pol" || $1=="p" || $1=="rup" || $1=="u" || $1=="red" || \
      $1=="solx" || $1=="v" || $1=="soli" || $1=="o" { deriv[++nd] = NR }
      END { if (nd >= '"${NTH}"') print deriv[nd - '"${NTH}"' + 1] }' "${PROOF}")"
    if [ -n "${TARGET}" ]; then
      awk -v tline="${TARGET}" -v desc="${DESC}" '
        NR == tline { printf "line %d: deleted outright\n  before: %s\n   after: <nothing>\n", NR, $0 > desc; next }
        { print }' "${PROOF}" > "${MUTATED}"
      # A `conclusion SAT` leans on the assignment, not on anything derived along the
      # way: its branch nogoods were checked when they were emitted and then wiped, so
      # deleting one leaves a proof that is still perfectly valid. Say so, rather than
      # letting the lane report a "finding" that is really just the wrong instance.
      if ! grep -q '^conclusion UNSAT' "${PROOF}"; then
        echo "NOTE ${LANE}: this proof does not end in 'conclusion UNSAT : <id>', so no" >&2
        echo "     later line need cite the step being deleted. Expect veripb to accept," >&2
        echo "     and read that as the instance being wrong for this lane, not as slack." >&2
      fi
    else
      cp "${PROOF}" "${MUTATED}"
    fi
    ;;

  *)
    echo "mutate_proof.sh: unknown mutation '${MUT}'. Known ones:" >&2
    list_mutations >&2
    cleanup
    exit 2 ;;
esac

if [ ! -s "${DESC}" ]; then
  echo "N/A  ${LANE}: no site this mutation applies to in ${PROOF}" >&2
  echo "     Nothing was corrupted, so nothing was tested. Do not read this as a pass;" >&2
  echo "     pick an instance whose proof contains the step this mutation is about." >&2
  cleanup
  exit 3
fi

# An "empty corruption" -- a mutation that rewrote nothing -- would make the lane green
# on the control's own proof. Catch it here rather than in the checker.
if [ "${MUT}" != "control" ] && cmp -s "${PROOF}" "${MUTATED}"; then
  echo "BUG  ${LANE}: the mutation reported a change but the file is identical." >&2
  sed 's/^/     /' "${DESC}" >&2
  cleanup
  exit 2
fi

echo "--- ${LANE}"
sed 's/^/    /' "${DESC}"

"${VERIPB}" "${MODEL}" "${MUTATED}" > "${LOG}" 2>&1
rc=$?

if [ "${MUT}" = "control" ]; then
  if [ "${rc}" -eq 0 ]; then
    echo "OK   ${LANE}: veripb accepts the honest proof"
    cleanup
    exit 0
  fi
  echo "FAIL ${LANE}: veripb REJECTS the uncorrupted proof." >&2
  echo "     Every mutation lane on this instance is therefore meaningless: a lane whose" >&2
  echo "     instance does not verify honestly is green for no reason at all." >&2
  sed 's/^/     /' "${LOG}" | tail -20 >&2
  echo "     opb=${OPB} proof=${PROOF}" >&2
  KEEP=1
  cleanup
  exit 1
fi

if [ "${rc}" -ne 0 ]; then
  echo "OK   ${LANE}: veripb rejected the corrupted proof, as it must"
  sed 's/^/     /' "${LOG}" | grep -i 'failed\|error' | head -3
  cleanup
  exit 0
fi

echo "FAIL ${LANE}: veripb ACCEPTED a proof that was deliberately corrupted." >&2
echo "     The honest derivation this was made from has slack in it: the step that was" >&2
echo "     corrupted is not load-bearing, and 'veripb accepts' says nothing about it." >&2
sed 's/^/     /' "${DESC}" >&2
echo "     That is a finding about the propagator, not about this harness. Record it in" >&2
echo "     docs/DECISIONS.md; do not weaken the lane to make it pass (CLAUDE.md)." >&2
echo "     opb=${OPB} honest=${PROOF}" >&2
KEEP=1
cleanup
exit 1
