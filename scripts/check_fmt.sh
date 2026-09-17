#!/bin/sh
# M1-T64. Verify formatting instead of silently fixing it.
#
# `make fmt` runs `dune build @fmt --auto-promote`, which REWRITES unformatted files.
# That is the right behaviour for an explicit fixer and the wrong behaviour for a gate:
# with it in `make check`, an unformatted commit is never anybody's failure -- it is
# silently repaired by the next person's gate run, in THEIR working tree.
#
# Two things that actually happened, on 2026-09-17, and are why this script exists:
#
#   * M1-T53 committed two test files unformatted. Nothing said so.
#   * The orchestrator then committed that formatting debt inside an unrelated commit,
#     because sessions are told to stage explicit paths and the reformatting showed up
#     in `git status` looking like their own work.
#   * Two further sessions each independently reported those same files as unformatted,
#     each seeing its own branch base. A failing gate would have spent that attention
#     once, on the person who caused it.
#
# So: this verifies. `make fmt` still fixes. A gate that quietly makes itself green is
# this project's signature failure mode wearing a tidy diff.
#
# Run with --self-test to prove the check can fail. That runs FIRST on every gate, the
# same discipline scripts/check_test_widths.py follows, and for the same reason: a guard
# that has not been seen to fail is not yet a guard.

set -e

ROOT="$(cd "$(dirname "$0")/.." && pwd)"

have_ocamlformat() { command -v ocamlformat >/dev/null 2>&1; }

# A missing ocamlformat is a LOUD SKIP, not a failure, and the asymmetry with
# scripts/checker.sh is deliberate: veripb verifies a correctness property, so a missing
# one makes the run worthless and must fail. ocamlformat verifies a cosmetic one, so
# refusing to run the gate without it would block real work over whitespace. It is loud
# enough that nobody can mistake it for a pass.
warn_missing() {
  echo "=========================================================================="
  echo "fmt check SKIPPED: ocamlformat is not installed (opam install ocamlformat)."
  echo "Formatting was NOT verified. This is a hole in this run of the gate."
  echo "=========================================================================="
}

self_test() {
  if ! have_ocamlformat; then
    warn_missing
    echo "fmt self-test: cannot run without ocamlformat"
    return 0
  fi
  # An isolated throwaway project, NOT this repo. Writing a deliberately unformatted .ml
  # into lib/ or test/ would be seen by `dune build` as well as by @fmt, and two other
  # sessions share this checkout -- a stray module is their broken build, not just mine.
  d="$(mktemp -d)"
  trap 'rm -rf "$d"' EXIT INT TERM
  echo '(lang dune 3.6)' > "$d/dune-project"
  cp "$ROOT/.ocamlformat" "$d/.ocamlformat"
  echo '(library (name probe))' > "$d/dune"
  # Unformatted on purpose: ocamlformat's default profile puts the body on its own line
  # and normalises the spacing.
  printf 'let  f   x=\n  x+1\nlet g y    =   f  (  y  )\n' > "$d/probe.ml"

  if (cd "$d" && dune build @fmt >/dev/null 2>&1); then
    echo "FAIL fmt self-test: @fmt ACCEPTED a deliberately unformatted module."
    echo "     The gate below would therefore pass on unformatted code, which is the"
    echo "     whole failure M1-T64 exists to close. Do not trust a green fmt check"
    echo "     until this passes."
    return 1
  fi

  # And the other polarity: it must ACCEPT formatted input, or it is a check that always
  # fails, which is just as useless and much easier to notice too late.
  (cd "$d" && dune build @fmt --auto-promote >/dev/null 2>&1) || true
  if (cd "$d" && dune build @fmt >/dev/null 2>&1); then
    echo "fmt self-test: refuses unformatted, accepts formatted"
    return 0
  fi
  echo "FAIL fmt self-test: @fmt REJECTED its own formatted output."
  echo "     The check can never pass, so it says nothing about the tree."
  return 1
}

run_check() {
  if ! have_ocamlformat; then
    warn_missing
    return 0
  fi
  if (cd "$ROOT" && dune build @fmt >/dev/null 2>&1); then
    echo "fmt: clean"
    return 0
  fi
  echo "FAIL fmt: files are not formatted. The gate no longer fixes this for you (M1-T64)."
  echo "     Run \`make fmt\` to format, then look at \`git status\` and stage only YOUR"
  echo "     files -- if the diff touches a file you did not work on, it is another"
  echo "     session's formatting debt and belongs in their commit, not yours."
  echo ""
  (cd "$ROOT" && dune build @fmt 2>&1 | head -40) || true
  return 1
}

case "${1:-}" in
  --self-test) self_test ;;
  *) run_check ;;
esac
