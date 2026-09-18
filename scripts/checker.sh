#!/usr/bin/env bash
# The one place that decides WHICH veripb this project checks against.
#
# SOURCE this file; do not run it. It defines two functions and no side effects:
#
#   baguette_resolve_veripb    sets $VERIPB to the resolved checker, or returns 1
#                              after printing a diagnostic on stderr.
#   baguette_veripb_diagnostic prints the "no checker" diagnostic. Callers print it
#                              and then FAIL; see "no skipping", below.
#
# Running this file directly prints the resolved checker and its version, which is
# the quickest way to answer "what am I actually checking against?":
#
#   scripts/checker.sh
#
# ---------------------------------------------------------------- the order
#
# 1. $VERIPB, if set and non-empty. An explicit choice always wins, and a $VERIPB
#    that does not resolve is an ERROR -- never a silent fall-through to something
#    else, because the whole point of setting it is to pin the checker.
# 2. $HOME/.cargo/bin/veripb -- the checker of record (VeriPB 3.0.2, the Rust
#    implementation). See docs/DECISIONS.md D-0023.
# 3. `veripb` on PATH.
#
# There is exactly ONE checker now: D-0046 removed proof format 2.0 and with it the
# Python VeriPB this project used to keep beside the Rust one. The consequence is
# recorded in D-0046 and is not a detail -- veripb 3.0.2 is the sole oracle, so a bug
# in it is a bug this project has no second implementation to see it with.
#
# PATH is still LAST on purpose. Two builds used to be installed side by side with the
# other one first on PATH, so "whatever is on PATH" silently meant the wrong checker --
# exactly the failure M1-T18 exists to remove. Naming the binary here makes the choice
# greppable, and `scripts/checker.sh` makes it printable.
#
# ---------------------------------------------------------------- no skipping
#
# A caller that cannot find a checker must FAIL, not skip. Until M1-T18,
# verify_proof.sh echoed "SKIP" and exited 0 when veripb was missing, so an
# environment with no checker made the proof tests PASS -- the one outcome a suite
# built on "a test that does not check the proof is half a test" must never produce.
# test_mutation.ml already got this right (it FAILs when it cannot find its script);
# no decision record ever sanctioned the skip. There is no BAGUETTE_SKIP_PROOFS
# escape hatch and none should be added.

baguette_veripb_candidates() {
  printf '%s\n' "${HOME}/.cargo/bin/veripb" "veripb"
}

baguette_veripb_diagnostic() {
  echo "  No VeriPB checker was found, so NOTHING was checked. This is a FAILURE," >&2
  echo "  not a skip: an unchecked proof is not a passing test (CLAUDE.md)." >&2
  echo "  VeriPB 3.0.2 is the only checker this project has (D-0046); there is no" >&2
  echo "  second implementation to fall back to." >&2
  echo "  Looked for, in order:" >&2
  echo "    \$VERIPB                      (currently: ${VERIPB:-<unset>})" >&2
  echo "    ${HOME}/.cargo/bin/veripb     VeriPB 3.0.2, Rust -- the checker of record" >&2
  echo "    veripb on \$PATH" >&2
  echo "  scripts/bootstrap.sh installs it. See docs/PROOF-FORMAT.md section 1." >&2
}

# Sets VERIPB (exported) on success. Returns 1 and explains on failure.
baguette_resolve_veripb() {
  if [ -n "${VERIPB:-}" ]; then
    if command -v "${VERIPB}" >/dev/null 2>&1; then
      export VERIPB
      return 0
    fi
    echo "checker.sh: \$VERIPB is set to '${VERIPB}', which is not executable." >&2
    echo "  An explicit \$VERIPB is never silently replaced by another checker." >&2
    return 1
  fi
  local c
  for c in $(baguette_veripb_candidates); do
    if command -v "${c}" >/dev/null 2>&1; then
      VERIPB="${c}"
      export VERIPB
      return 0
    fi
  done
  return 1
}

# Run directly: say what would be used, and prove it runs.
if [ "${BASH_SOURCE[0]}" = "${0}" ]; then
  if baguette_resolve_veripb; then
    echo "veripb: ${VERIPB}"
    "${VERIPB}" --version 2>&1 | grep -i version | head -2
    exit 0
  fi
  baguette_veripb_diagnostic
  exit 1
fi
