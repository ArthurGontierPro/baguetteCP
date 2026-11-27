#!/usr/bin/env bash
# Mutations of lib/scp/reader.ml, the .scp reader, each of which the lanes must catch. This is
# test 6 of the plan in D-0228 section 14 (the record that made .scp baguette's second input),
# run for M23-inputs-T5, the milestone's acceptance; D-0230 records the reader and its lanes.
#
# Usage: tools/scp/mutate.sh WORKDIR
#
# For each mutation: a detached worktree of HEAD in WORKDIR, the one-line change applied
# with sed (the script FAILS if the line is not found, so a reformatted reader cannot turn
# a mutation into a no-op), bin/main.exe built, then the three lanes run against it: the
# hand-written models (scripts/run_scp_tests.sh), the FlatZinc agreement lane
# (tools/scp/fzn_lane.sh) and 200 random files (tools/scp/random_lane.py). A mutation is
# CAUGHT when at least one lane fails. Prints one line per mutation (CAUGHT or SURVIVED) and
# exits 0 when every mutation is caught, 1 if one survives. It exits 1 at once, with a
# `FAIL <mutation>: ...` line, when a worktree cannot be made, a mutated line is not found or
# a mutant does not build, and when WORKDIR is not given. Each worktree is removed after its
# lanes; the logs stay in WORKDIR/<mutation>.*.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
WORK="$1"; mkdir -p "$WORK"
MUT=(
  "element-off-by-one|s/            if off = 1 then y/            if off = 0 then y/"
  "circuit-off-by-one|s/      let range = List.init n (fun i -> i) in/      let range = List.init n (fun i -> i + 1) in/"
  "less_equal-swapped|s/  | Le -> Model.Int_le (x, y)/  | Le -> Model.Int_le (y, x)/"
  "all_different-dropped|s/      post st pos kw (Model.All_different (operands st (List.hd args) \"the variables\"))/      ignore (operands st (List.hd args) \"the variables\")/"
)
survived=0
for entry in "${MUT[@]}"; do
  name="${entry%%|*}"; expr="${entry#*|}"
  wt="$WORK/$name"
  git -C "$ROOT" worktree remove --force "$wt" >/dev/null 2>&1
  git -C "$ROOT" worktree add --detach "$wt" HEAD >/dev/null 2>&1 || { echo "FAIL $name: no worktree"; exit 1; }
  before="$(md5sum < "$wt/lib/scp/reader.ml")"
  sed -i "$expr" "$wt/lib/scp/reader.ml"
  if [ "$before" = "$(md5sum < "$wt/lib/scp/reader.ml")" ]; then
    echo "FAIL $name: the mutated line was not found"; exit 1
  fi
  ( cd "$wt" && dune build --root . -j 8 bin/main.exe > "$WORK/$name.build" 2>&1 ) ||
    { echo "FAIL $name: does not build"; exit 1; }
  B="$wt/_build/default/bin/main.exe"
  lanes=""
  BAGUETTE="$B" "$wt/scripts/run_scp_tests.sh" > "$WORK/$name.scp.log" 2>&1 || lanes="$lanes scp-models"
  BAGUETTE="$B" J=4 "$wt/tools/scp/fzn_lane.sh" "$WORK/$name.fzn" > "$WORK/$name.fzn.log" 2>&1 || lanes="$lanes fzn-agreement"
  python3 -I "$wt/tools/scp/random_lane.py" "$B" "$WORK/$name.rand" 200 11 > "$WORK/$name.rand.log" 2>&1 || lanes="$lanes random"
  if [ -n "$lanes" ]; then echo "CAUGHT   $name by:$lanes"; else echo "SURVIVED $name"; survived=1; fi
  git -C "$ROOT" worktree remove --force "$wt" >/dev/null 2>&1
done
exit $survived
