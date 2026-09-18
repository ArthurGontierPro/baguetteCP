#!/usr/bin/env bash
# Explanation size, per model (M2-T17, off docs/EXPLANATION-REVIEW.md section 5).
#
# The gap this closes: a sound but maximally weak explanation -- one that names every
# variable in scope -- passes every test in this repository today, and VeriPB accepts
# it. Nothing measures explanation QUALITY. The literature's quality metric is
# generality: a shorter, weaker-premised explanation prunes more later. That is
# harmless while every propagator is linear and the derivation is forced (M2-T10 is
# the strength-side sibling that covers propagators); it stops being harmless at
# M4-T1 (all_different), where the choice of Hall set is the whole game. This script
# makes explanation size a tracked number before that row lands, so a regression is
# visible.
#
# Scoped deliberately to bench/ and to artefacts that already exist: no lib/ change,
# no new solver counter. The literal counts are read straight off the emitted .pbp,
# exactly the way run_bench.sh already reads `rup`/`pol` line COUNTS off it -- this
# script reads what is INSIDE those lines instead of just counting them.
#
# Two metrics, reported separately because nothing here says they move together:
#
#   rup_lits   literals per DERIVED constraint (`rup ... >= k ;` lines). This is the
#              direct reading of "how many variables does this explanation name" --
#              the exact quantity section 5's warning is about.
#   pol_prems  premises cited per `pol` CHAIN: every operand pushed onto the proof's
#              stack before the trailing `;` -- a cited constraint id (`@cN`) or a
#              literal pushed as its own unit axiom -- with the `+`/`*`/`d`/`s`/`w`/`!`
#              operators themselves excluded. A `pol` chain is how a derivation
#              COMBINES existing facts, so this is the combining side of the same
#              question: how many premises did it take.
#
# `rup` lines and `pol` lines are counted independently and can be empty on a given
# model (bool_clause_sat.fzn has no `pol` line at all); a metric with zero occurrences
# on a model is reported as `n/a`, not 0, for the same reason bench/README.md section 4
# reports a zero-denominator fallback rate as `n/a`: a zero would read as "explanations
# here are free", which is not what an empty denominator means.
#
# Usage:
#   bench/explanation_size.sh                       every model in test/models/
#   bench/explanation_size.sh MODEL.fzn ...          just these
#   bench/explanation_size.sh -p FILE.pbp ...        measure existing .pbp files directly,
#                                                     no solve step (used by -c)
#   bench/explanation_size.sh -c                     THE CONTROL (see bench/control/size/)
#                                                     -- asserts, exits non-zero
#   bench/explanation_size.sh -s BIN ...             solver binary (default
#                                                     _build/default/bin/main.exe)
#
# Measurement only. Never a commit gate -- see bench/README.md section 1 and this
# task's obligation (d). Run under `ulimit -v 4000000` and a `timeout`, same as every
# other script in this directory; this script does not impose either itself so it
# composes with run_bench.sh's own self-checks rather than fighting them.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOLVER="${BAGUETTE:-${ROOT}/_build/default/bin/main.exe}"
MODELS_DIR="${ROOT}/test/models"
TIMEOUT="${TIMEOUT:-60}"
MODE=solve
CONTROL=0
declare -a ARGS=()

usage() {
  cat <<'EOF'
usage: bench/explanation_size.sh [options] [MODEL.fzn ...]

With no models named, every .fzn in test/models/ is measured.

  -p        treat the named paths as .pbp files already on disk; skip solving
  -s BIN    solver binary                          (default _build/default/bin/main.exe)
  -c        run THE CONTROL (bench/control/size/): asserts, exits non-zero on failure
  -t SECS   per-model solve timeout                (default 60)
  -h        this text

Reports one line per model/file: rup_lits (literals per derived `rup` constraint,
mean over that model's `rup` lines) and pol_prems (premises cited per `pol` chain,
mean over that model's `pol` lines). See the header comment for what each measures
and why they are reported separately rather than combined.
EOF
}

while getopts ':ps:ct:h' opt; do
  case "${opt}" in
    p) MODE=pbp ;;
    s) SOLVER="${OPTARG}" ;;
    c) CONTROL=1 ;;
    t) TIMEOUT="${OPTARG}" ;;
    h) usage; exit 0 ;;
    \?) echo "unknown option -${OPTARG}" >&2; usage >&2; exit 2 ;;
    :) echo "option -${OPTARG} needs an argument" >&2; exit 2 ;;
  esac
done
shift $((OPTIND - 1))
ARGS=("$@")

# measure_pbp FILE -- prints "rup_lits_mean\trup_n\tpol_prems_mean\tpol_n" for one .pbp.
# Awk, not the shell: this runs once per model in the 38-model suite and a per-line
# shell loop over every rup/pol line of a real proof is the wrong tool for that.
measure_pbp() {
  local pbp="$1"
  awk '
    function is_lit_token(t) {
      # a PB literal or its negated-coefficient term: [+-]<int>, the shape every
      # `rup` body term takes in this proof format (Writer emits `+1 lit`, never a
      # bare coefficient, so this also skips the trailing ">= k" left in by mistake
      # if the split ever includes it).
      return (t ~ /^[+-][0-9]+$/)
    }
    function is_operator(t) {
      return (t == "+" || t == "*" || t == "d" || t == "s" || t == "w" || t == "!" || t == "")
    }
    {
      line = $0
      # drop a leading label, e.g. "@c9 "
      if (line ~ /^@[^ ]+ /) { sub(/^@[^ ]+ /, "", line) }
    }
    line ~ /^rup / {
      sub(/^rup /, "", line)
      idx = index(line, ">=")
      body = (idx > 0) ? substr(line, 1, idx - 1) : line
      n = split(body, toks, /[ \t]+/)
      lits = 0
      for (i = 1; i <= n; i++) if (is_lit_token(toks[i])) lits++
      rup_total += lits
      rup_n++
      next
    }
    line ~ /^pol / {
      sub(/^pol /, "", line)
      sub(/;[ \t]*$/, "", line)
      n = split(line, toks, /[ \t]+/)
      prem = 0
      for (i = 1; i <= n; i++) if (!is_operator(toks[i])) prem++
      pol_total += prem
      pol_n++
      next
    }
    END {
      rup_mean = (rup_n > 0) ? rup_total / rup_n : -1
      pol_mean = (pol_n > 0) ? pol_total / pol_n : -1
      printf "%.4f\t%d\t%.4f\t%d\n", rup_mean, rup_n, pol_mean, pol_n
    }
  ' "${pbp}"
}

fmt_field() {
  # $1 = mean (-1 means "no occurrences"), $2 = n
  local mean="$1" n="$2"
  if [ "${n}" -eq 0 ]; then
    printf 'n/a'
  else
    printf '%s(n=%s)' "${mean}" "${n}"
  fi
}

report_one() {
  # $1 = label, $2 = .pbp path
  local label="$1" pbp="$2"
  if [ ! -s "${pbp}" ]; then
    printf '%-28s %s\n' "${label}" 'NO PROOF (solve failed or was refused)'
    return 1
  fi
  local row rup_mean rup_n pol_mean pol_n
  row="$(measure_pbp "${pbp}")"
  IFS=$'\t' read -r rup_mean rup_n pol_mean pol_n <<<"${row}"
  printf '%-28s rup_lits=%-16s pol_prems=%-16s\n' \
    "${label}" "$(fmt_field "${rup_mean}" "${rup_n}")" "$(fmt_field "${pol_mean}" "${pol_n}")"
}

run_control() {
  local base="${ROOT}/bench/control/size/base/ctl_size.pbp"
  local variant="${ROOT}/bench/control/size/variant/ctl_size.pbp"
  local fail=0

  if [ ! -f "${base}" ] || [ ! -f "${variant}" ]; then
    echo "control fixtures missing: expected ${base} and ${variant}" >&2
    exit 1
  fi

  local brow vrow
  brow="$(measure_pbp "${base}")"
  vrow="$(measure_pbp "${variant}")"
  local b_rup_mean b_rup_n b_pol_mean b_pol_n
  local v_rup_mean v_rup_n v_pol_mean v_pol_n
  IFS=$'\t' read -r b_rup_mean b_rup_n b_pol_mean b_pol_n <<<"${brow}"
  IFS=$'\t' read -r v_rup_mean v_rup_n v_pol_mean v_pol_n <<<"${vrow}"

  echo "control: bench/control/size/{base,variant}/ctl_size.pbp"
  printf '  base    rup_lits=%s(n=%s) pol_prems=%s(n=%s)\n' "${b_rup_mean}" "${b_rup_n}" "${b_pol_mean}" "${b_pol_n}"
  printf '  variant rup_lits=%s(n=%s) pol_prems=%s(n=%s)\n' "${v_rup_mean}" "${v_rup_n}" "${v_pol_mean}" "${v_pol_n}"

  # Both metrics must be present on both fixtures (that is the fixture's job) and
  # the variant -- the deliberately widened explanation -- must score STRICTLY
  # higher on both. A metric that never moves is not a metric (M2-T17's obligation b).
  if [ "${b_rup_n}" -eq 0 ] || [ "${v_rup_n}" -eq 0 ] || [ "${b_pol_n}" -eq 0 ] || [ "${v_pol_n}" -eq 0 ]; then
    echo "FAIL: fixture is missing a rup or pol line -- cannot assert either metric moved" >&2
    fail=1
  fi

  if awk -v b="${b_rup_mean}" -v v="${v_rup_mean}" 'BEGIN { exit !(v > b) }'; then
    echo "PASS: rup_lits grew (${b_rup_mean} -> ${v_rup_mean})"
  else
    echo "FAIL: rup_lits did not grow (${b_rup_mean} -> ${v_rup_mean})" >&2
    fail=1
  fi

  if awk -v b="${b_pol_mean}" -v v="${v_pol_mean}" 'BEGIN { exit !(v > b) }'; then
    echo "PASS: pol_prems grew (${b_pol_mean} -> ${v_pol_mean})"
  else
    echo "FAIL: pol_prems did not grow (${b_pol_mean} -> ${v_pol_mean})" >&2
    fail=1
  fi

  if [ "${fail}" -ne 0 ]; then
    echo "CONTROL FAILED" >&2
    exit 1
  fi
  echo "CONTROL OK"
  exit 0
}

if [ "${CONTROL}" -eq 1 ]; then
  run_control
fi

if [ "${MODE}" = pbp ]; then
  [ "${#ARGS[@]}" -eq 0 ] && { echo "no .pbp files given with -p" >&2; exit 2; }
  for f in "${ARGS[@]}"; do
    report_one "$(basename "${f}")" "${f}"
  done
  exit 0
fi

declare -a MODELS=()
if [ "${#ARGS[@]}" -eq 0 ]; then
  while IFS= read -r -d '' f; do MODELS+=("${f}"); done \
    < <(find "${MODELS_DIR}" -maxdepth 1 -name '*.fzn' -print0 | sort -z)
else
  MODELS=("${ARGS[@]}")
fi

WORKDIR="$(mktemp -d)"
trap 'rm -rf "${WORKDIR}"' EXIT

for fzn in "${MODELS[@]}"; do
  base="$(basename "${fzn}" .fzn)"
  prefix="${WORKDIR}/${base}"
  if ! timeout "${TIMEOUT}" "${SOLVER}" "${fzn}" --proof "${prefix}" >"${prefix}.stdout" 2>"${prefix}.stderr"; then
    printf '%-28s SOLVER-FAILED (see stderr in %s)\n' "${base}" "${prefix}.stderr"
    continue
  fi
  report_one "${base}" "${prefix}.pbp"
done
