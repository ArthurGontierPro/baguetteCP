#!/usr/bin/env bash
# M7-T4. The corpus harness: flatten -> solve -> CHECK THE PROOF -> classify.
#
# One line of TSV per instance, one bucket per line. Every solved instance's proof
# goes through veripb 3.0.2; a run without a checked proof is not a result
# (CLAUDE.md, proof discipline). `PROOF-REJECTED` is its OWN bucket and is never
# folded into a failure -- that bucket is the entire point of the exercise.
#
# ---------------------------------------------------------------- why it exists
#
# The first full corpus run (D-0068) was driven by a one-off script that lived on
# the cluster node, outside version control. It produced this project's first eight
# checked proofs for input it did not author, and it also produced 22 rows that were
# its OWN failures wearing the solver's name (D-0069, M7-T10). This file is the
# reviewable replacement, so the next run is reproduced rather than reconstructed.
#
# ------------------------------------------------- the rule the buckets encode
#
# D-0069: **a measurement's own failure modes look exactly like findings about the
# subject, and nothing in a results table distinguishes them.** So every bucket that
# attributes a failure to the SOLVER is gated on a check that the input was
# well-formed first. A torn, truncated or missing `.fzn` lands in `INPUT-INVALID`
# and can never be reported as `REFUSED-MODEL`.
#
# Concretely, what went wrong in D-0068's run and what is fixed here:
#
#   1. **Instance ids collided.** The id was `<year>_<family>`, but a family
#      directory holds many `.mzn` files -- `2010/bacp/` holds fifteen. Fifteen jobs
#      therefore flattened to the SAME `2010_bacp.fzn`, read each other's half-written
#      bytes, and deleted it from under one another. That is the whole of the "torn
#      write": all 13 torn parses, all 5 "no such file" and every other suspect row
#      belonged to one of 18 colliding ids. The id here includes the model's own
#      basename, so no two jobs share a path.
#   2. **The flatten was not atomic.** Even with unique ids, a killed or timed-out
#      flatten leaves a partial file behind that the next resumed run would solve.
#      Here MiniZinc writes to `<work>/<id>.fzn.part` and the result is `mv`d into
#      place -- a rename within one directory, atomic on ext4 (and on any local
#      POSIX filesystem). `require_local_fs` refuses to run on NFS, where that
#      guarantee does not hold.
#   3. **Nothing validated the input.** `validate_fzn` runs before the solver is
#      ever invoked.
#
# ---------------------------------------------------------------- the buckets
#
# Input-side -- these blame the HARNESS or the corpus, never the solver:
#   FLATTEN-FAIL       minizinc exited non-zero
#   FLATTEN-TIMEOUT    minizinc exceeded $FLATTEN_TIMEOUT
#   NO-DATA            no .dzn/.json data file beside the model
#   INPUT-INVALID      the .fzn is missing, empty, truncated, NUL-bearing, or has
#                      other than exactly one `solve` item. Detail says which.
#
# Solver-side -- only reachable once the input above is known good:
#   REFUSED-MODEL      exit 2, front end. The refusing message is PRESERVED in the
#                      detail column: that column is what D-0069 classified by.
#   REFUSED-LIMIT      exit 3, a declared resource limit
#   TIMEOUT-SOLVE      exceeded $SOLVE_TIMEOUT
#   SOLVE-ERR-<rc>     any other exit, rc kept (134 = SIGABRT/OOM, see D-0068)
#
# Proof-side:
#   OK-PROOF-VERIFIED  solved AND veripb accepted the proof. The only success.
#   PROOF-REJECTED     solved, veripb REJECTED. Its own bucket. Never a failure
#                      bucket, never merged, and the proof is KEPT for inspection.
#   TIMEOUT-CHECK      veripb exceeded $CHECK_TIMEOUT -- says nothing either way
#   NO-PROOF           solver exited 0 but emitted no .pbp. A result without a
#                      checked proof is not a result, so this is not a success.
#
# There is no bucket that means "failed"; that is deliberate.
#
# ---------------------------------------------------------------- usage
#
#   scripts/corpus_run.sh [corpus-root] [output-dir]
#
#   CORPUS   corpus root; searched for */*/*.mzn      (default $1)
#   OUT      output directory                          (default $2)
#   PAR      parallel jobs, hard-capped at 92          (default 32)
#   MEM_KB   per-job address-space cap, capped 32 GB   (default 32000000)
#   SOLVE_TIMEOUT / FLATTEN_TIMEOUT / CHECK_TIMEOUT    (default 300 / 120 / 900)
#   MZN      the minizinc binary                       (default: PATH)
#   BAGUETTE the solver binary            (default: _build/default/bin/main.exe)
#   VERIPB   the checker; resolved by scripts/checker.sh if unset
#   ONLY     a file of instance ids to run, one per line -- for re-running suspects
#   KEEP     1 to keep every .fzn/.opb/.pbp, not only the interesting ones
#
# `PAR` and `MEM_KB` are capped rather than trusted: 92 jobs at 32 GB is the node's
# documented ceiling (M7-T4) and a harness that lets a typo exceed it takes the node
# down for everyone.
#
# ---------------------------------------------------------------- resumption
#
# Results are APPENDED to $OUT/results.tsv and an instance is skipped if its id
# already appears in column 1. An interrupted run is finished by re-invoking with
# the same arguments; nothing is recomputed. To redo an instance, delete its row.
#
# ---------------------------------------------------------------- completion
#
# The last line of a COMPLETE run is `DONE-<epoch>\t<recorded>\t<corpus-size>`, and
# it is written only when every SELECTED instance has a row -- so an ONLY run of 103
# is complete at 103 and does not need the other 333. The marker's absence means
# the run is partial, and `report` says so in as many words rather
# than printing a total that looks whole. A partial table read as a total is how
# D-0068's numbers became D-0069's correction.

set -u -o pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"

CORPUS="${CORPUS:-${1:-}}"
OUT="${OUT:-${2:-}}"
PAR="${PAR:-32}"
MEM_KB="${MEM_KB:-32000000}"
SOLVE_TIMEOUT="${SOLVE_TIMEOUT:-300}"
FLATTEN_TIMEOUT="${FLATTEN_TIMEOUT:-120}"
CHECK_TIMEOUT="${CHECK_TIMEOUT:-900}"
MZN="${MZN:-minizinc}"
BAGUETTE="${BAGUETTE:-$ROOT/_build/default/bin/main.exe}"
KEEP="${KEEP:-0}"
ONLY="${ONLY:-}"

PAR_MAX=92
MEM_KB_MAX=32000000

die() {
  echo "corpus_run: $*" >&2
  exit 1
}

# ---------------------------------------------------------------- preflight

# A rename is only atomic within one filesystem, and only reliably so on a local
# one. D-0069 licensed the temp-and-rename fix on the grounds that /scratch is
# ext4; that premise is checked here rather than assumed, because the same script
# run over an NFS home directory would silently lose the guarantee it depends on.
require_local_fs() {
  local dir="$1" fstype
  fstype="$(df -PT "$dir" 2>/dev/null | awk 'NR==2 {print $2}')"
  case "$fstype" in
    nfs | nfs3 | nfs4 | cifs | smbfs | fuse.sshfs | 9p)
      die "$dir is on $fstype. Rename is not reliably atomic there, and this harness
            depends on it to never hand a half-written .fzn to the solver. Point OUT at
            local storage (on fataepyc-07: /scratch)."
      ;;
    "") echo "corpus_run: WARNING: could not determine the filesystem type of $dir." >&2 ;;
    *) ;;
  esac
}

preflight() {
  [ -n "$CORPUS" ] || die "no corpus root. Usage: corpus_run.sh <corpus-root> <output-dir>"
  [ -n "$OUT" ] || die "no output dir. Usage: corpus_run.sh <corpus-root> <output-dir>"
  [ -d "$CORPUS" ] || die "corpus root $CORPUS does not exist"
  command -v "$MZN" >/dev/null 2>&1 || die "minizinc not found (MZN=$MZN)"
  [ -x "$BAGUETTE" ] || die "solver not found or not executable: $BAGUETTE
            Build it first: dune build --root . bin/"
  [ -f "$ROOT/tools/baguette.msc" ] || die "tools/baguette.msc is missing"
  [ -d "$ROOT/mznlib" ] || die "mznlib/ is missing"

  # D-0067: flattening must use THIS project's MiniZinc library, or the .fzn comes
  # back decomposed into linear rows and the corpus stops measuring the propagators
  # it was run to measure. MZN_SOLVER_PATH points at tools/, whose .msc points at
  # mznlib/. Overriding it is not supported -- a run with the wrong library is not
  # comparable to any other run.
  export MZN_SOLVER_PATH="$ROOT/tools"

  # The checker is resolved exactly once, here, by the one place allowed to decide
  # it. A MISSING checker is a failure and never a skip: a corpus run that cannot
  # check proofs would report OK for every solve and would be worse than no run.
  # shellcheck source=/dev/null
  . "$ROOT/scripts/checker.sh"
  baguette_resolve_veripb || {
    baguette_veripb_diagnostic
    die "no veripb. Every proof must be checked, so this run would say nothing."
  }
  export VERIPB

  if [ "$PAR" -gt "$PAR_MAX" ]; then
    echo "corpus_run: PAR=$PAR exceeds the node's ceiling; capping at $PAR_MAX." >&2
    PAR=$PAR_MAX
  fi
  if [ "$MEM_KB" -gt "$MEM_KB_MAX" ]; then
    echo "corpus_run: MEM_KB=$MEM_KB exceeds 32 GB; capping at $MEM_KB_MAX." >&2
    MEM_KB=$MEM_KB_MAX
  fi

  mkdir -p "$OUT/log" "$OUT/work" || die "cannot create $OUT"
  require_local_fs "$OUT"
}

# ---------------------------------------------------------------- the id
#
# The id must be unique per .mzn FILE, not per family directory. D-0068's harness
# used <year>_<family>, and 18 families hold several models each, so up to fifteen
# concurrent jobs shared one output path. Everything M7-T10 was opened to explain
# follows from that one line. The basename is included here for exactly that
# reason; do not shorten it back.
instance_id() {
  local mzn="$1" d fam yr base
  d="$(dirname "$mzn")"
  fam="$(basename "$d")"
  yr="$(basename "$(dirname "$d")")"
  base="$(basename "$mzn" .mzn)"
  if [ "$base" = "$fam" ]; then
    printf '%s_%s' "$yr" "$fam"
  else
    printf '%s_%s_%s' "$yr" "$fam" "$base"
  fi | tr -c 'A-Za-z0-9._-' '_'
}

# ---------------------------------------------------------------- validation
#
# Runs BEFORE the solver is invoked, and its failures are the harness's own.
# Prints a one-line reason and returns 1; silent and returns 0 if the file is
# well-formed enough to be worth a solver's opinion.
#
# This is not a FlatZinc parser and must not become one -- the solver's front end
# is the authority on what is a legal model (SPEC 2.1). The only question here is
# whether the bytes on disk are a COMPLETE capture of what the flattener wrote, so
# that a refusal afterwards can honestly be attributed to the model.
validate_fzn() {
  local f="$1" solves last
  [ -f "$f" ] || {
    echo "the .fzn does not exist"
    return 1
  }
  [ -s "$f" ] || {
    echo "the .fzn is empty"
    return 1
  }
  # NOT `grep $'\000'`: a pattern containing a NUL is truncated to the empty
  # pattern, which matches every file. The self-test caught exactly that, which is
  # what it is for. Comparing the byte count with and without NULs cannot lie.
  if [ "$(wc -c < "$f")" -ne "$(tr -d '\000' < "$f" | wc -c)" ]; then
    echo "the .fzn contains NUL bytes -- a partial or interleaved write"
    return 1
  fi
  # A FlatZinc model has exactly one solve item. Zero means the capture was cut
  # short; more than one means two writers interleaved -- which is precisely what
  # 2010_bacp.fzn looked like, a correct solve item followed by the tail fragment
  # `lete) minimize objective;` from another job's shorter file.
  # No `|| echo 0` here: `grep -c` PRINTS 0 and exits 1 on no match, so the
  # fallback would append a second line and every arithmetic test below would
  # break on "0\n0". The exit status is simply not consulted.
  solves="$(grep -ac '^[[:space:]]*solve' "$f" 2>/dev/null)"
  solves="${solves:-0}"
  if [ "$solves" -eq 0 ]; then
    echo "the .fzn has no solve item -- truncated capture"
    return 1
  fi
  if [ "$solves" -gt 1 ]; then
    echo "the .fzn has $solves solve items -- interleaved or torn write"
    return 1
  fi
  # Every FlatZinc item ends in a semicolon, so a final line that does not is a
  # capture that stopped mid-item.
  last="$(tail -c 4096 "$f" | tr -d '\r' | grep -v '^[[:space:]]*$' | tail -1)"
  case "$last" in
    *\;) ;;
    *)
      echo "the .fzn does not end in a complete item -- truncated"
      return 1
      ;;
  esac
  # THE CHECK THAT CATCHES THE REAL 2010_bacp.fzn, and the one the self-test
  # showed was missing: the solve item is the LAST item of a FlatZinc model, so
  # nothing may follow its terminating semicolon. The real torn file ended
  #
  #     solve :: int_search(...) minimize objective;
  #     lete) minimize objective;
  #
  # -- a complete model, then another writer's tail. Neither the solve COUNT (the
  # fragment does not begin with `solve`) nor the trailing-semicolon test sees
  # that; only "does anything follow the solve item" does.
  tail_after="$(sed -n '/^[[:space:]]*solve/,$p' "$f" | tr '\n' ' ' | sed 's/^[^;]*;//' \
    | tr -d '[:space:]')"
  if [ -n "$tail_after" ]; then
    echo "content follows the solve item ('$(printf '%s' "$tail_after" | cut -c1-40)') -- torn write"
    return 1
  fi
  return 0
}

# ---------------------------------------------------------------- one instance

emit() {
  # id, bucket, fzn bytes, pbp bytes, detail. Tabs are the separator, so the
  # detail is flattened: a checker or front-end message containing a newline would
  # otherwise turn one result into two rows.
  printf '%s\t%s\t%s\t%s\t%s\n' "$1" "$2" "$3" "$4" \
    "$(printf '%s' "$5" | tr '\t\n\r' '   ' | cut -c1-200)"
}

run_one() {
  local mzn="$1" id L W dat rc sz pbp reason detail
  id="$(instance_id "$mzn")"
  L="$OUT/log/$id"
  W="$OUT/work/$id"

  # Smallest data file, as D-0068 did, so the corpus measures the solver rather
  # than the instance size. Recorded in the log so it is never in doubt which one.
  dat="$(ls -S "$(dirname "$mzn")"/*.dzn "$(dirname "$mzn")"/*.json 2>/dev/null | tail -1)"
  printf 'model=%s\ndata=%s\n' "$mzn" "${dat:-<none>}" > "$L.inst"

  ulimit -v "$MEM_KB" 2>/dev/null

  # Flatten to a private .part beside the destination and rename. Same directory,
  # so the rename is within one filesystem; preflight has already refused to run
  # anywhere that rename is not atomic.
  rm -f "$W.fzn.part" "$L.fzn"
  timeout "$FLATTEN_TIMEOUT" "$MZN" -c --solver baguette "$mzn" ${dat:+"$dat"} \
    -o "$W.fzn.part" > "$L.mzn.err" 2>&1
  rc=$?
  if [ "$rc" -eq 124 ]; then
    emit "$id" "FLATTEN-TIMEOUT" - - "exceeded ${FLATTEN_TIMEOUT}s"
    rm -f "$W.fzn.part"
    return
  fi
  if [ "$rc" -ne 0 ]; then
    emit "$id" "FLATTEN-FAIL" - - "$(head -c 200 "$L.mzn.err")"
    rm -f "$W.fzn.part"
    return
  fi
  if [ -z "$dat" ] && [ ! -s "$W.fzn.part" ]; then
    emit "$id" "NO-DATA" - - "no .dzn or .json beside $mzn"
    rm -f "$W.fzn.part"
    return
  fi
  mv -f "$W.fzn.part" "$L.fzn" || {
    emit "$id" "INPUT-INVALID" - - "could not rename the flattened model into place"
    return
  }

  # THE GATE. Nothing below this line may be attributed to the solver until the
  # input has been shown to be a complete capture.
  if ! reason="$(validate_fzn "$L.fzn")"; then
    emit "$id" "INPUT-INVALID" "$(stat -c%s "$L.fzn" 2>/dev/null || echo 0)" - "$reason"
    return
  fi
  sz="$(stat -c%s "$L.fzn")"

  rm -f "$L.opb" "$L.pbp"
  timeout "$SOLVE_TIMEOUT" "$BAGUETTE" --proof "$L" "$L.fzn" > "$L.out" 2> "$L.err"
  rc=$?
  detail="$(head -c 200 "$L.err")"
  case "$rc" in
    0) ;;
    2)
      emit "$id" "REFUSED-MODEL" "$sz" - "$detail"
      cleanup_one "$L" keepfzn
      return
      ;;
    3)
      emit "$id" "REFUSED-LIMIT" "$sz" - "$detail"
      cleanup_one "$L" keepfzn
      return
      ;;
    124)
      emit "$id" "TIMEOUT-SOLVE" "$sz" - "exceeded ${SOLVE_TIMEOUT}s"
      cleanup_one "$L"
      return
      ;;
    *)
      emit "$id" "SOLVE-ERR-$rc" "$sz" - "$detail"
      cleanup_one "$L" keepfzn
      return
      ;;
  esac

  if [ ! -s "$L.pbp" ] || [ ! -s "$L.opb" ]; then
    emit "$id" "NO-PROOF" "$sz" 0 "solver exited 0 but emitted no proof"
    cleanup_one "$L" keepfzn
    return
  fi
  pbp="$(stat -c%s "$L.pbp")"

  if timeout "$CHECK_TIMEOUT" "$VERIPB" "$L.opb" "$L.pbp" > "$L.vp" 2>&1; then
    emit "$id" "OK-PROOF-VERIFIED" "$sz" "$pbp" "$(tail -1 "$L.vp")"
    cleanup_one "$L"
    return
  fi
  rc=$?
  if [ "$rc" -eq 124 ]; then
    # Not a rejection. A checker that ran out of time has said nothing about the
    # proof, and folding it into PROOF-REJECTED would manufacture a defect.
    emit "$id" "TIMEOUT-CHECK" "$sz" "$pbp" "veripb exceeded ${CHECK_TIMEOUT}s"
    cleanup_one "$L"
    return
  fi
  # The bucket the run exists for. The artefacts are kept unconditionally, even
  # under KEEP=0: a rejected proof that was deleted cannot be investigated, and
  # re-running to reproduce it costs the whole instance again.
  emit "$id" "PROOF-REJECTED" "$sz" "$pbp" \
    "$(grep -i 'Caused by' -A1 "$L.vp" | tail -1 | head -c 200)"
}

cleanup_one() {
  local L="$1" keepfzn="${2:-}"
  [ "$KEEP" = "1" ] && return 0
  rm -f "$L.opb" "$L.pbp"
  # A refused or crashed instance keeps its .fzn: the model is the evidence, and
  # re-flattening to look at it is both slow and not guaranteed to reproduce.
  [ -n "$keepfzn" ] || rm -f "$L.fzn"
  return 0
}

# ---------------------------------------------------------------- the report
#
# Refuses to print a total for a run with no completion marker. A partial table
# read as a whole one is the specific mistake D-0069 had to correct.
report() {
  local res="$OUT/results.tsv"
  [ -f "$res" ] || die "no results at $res"
  if grep -aq '^DONE-' "$res"; then
    echo "run: COMPLETE ($(grep -a '^DONE-' "$res" | tail -1))"
  else
    echo "run: ***PARTIAL*** -- no DONE marker. These counts are a lower bound on"
    echo "     every bucket and must not be reported as a total."
  fi
  grep -av '^DONE-' "$res" | cut -f2 | sed 's/^SOLVE-ERR-.*/SOLVE-ERR-*/' \
    | sort | uniq -c | sort -rn
  echo "distinct instances: $(grep -av '^DONE-' "$res" | cut -f1 | sort -u | wc -l)"
  # An id appearing twice means two jobs shared an output path, which is the
  # D-0068 bug itself. It cannot happen with the id above, so say so loudly if it
  # ever does rather than letting the duplicates sit in the counts.
  local dups
  dups="$(grep -av '^DONE-' "$res" | cut -f1 | sort | uniq -d | wc -l)"
  if [ "$dups" -gt 0 ]; then
    echo "FAIL: $dups instance ids appear more than once. Two jobs shared an output"
    echo "      path and their .fzn files raced. These rows are NOT results; see D-0069."
    return 1
  fi
  return 0
}

# ---------------------------------------------------------------- main

main() {
  preflight
  export OUT MZN BAGUETTE MEM_KB SOLVE_TIMEOUT FLATTEN_TIMEOUT CHECK_TIMEOUT KEEP
  export -f run_one instance_id validate_fzn emit cleanup_one

  find "$CORPUS" -mindepth 3 -name '*.mzn' | sort > "$OUT/all.lst"
  local total
  total="$(wc -l < "$OUT/all.lst")"
  [ "$total" -gt 0 ] || die "no *.mzn found under $CORPUS (expected <root>/<year>/<family>/)"

  touch "$OUT/results.tsv"
  # Resumption: an id already in column 1 is done. Computed once, not per job, so
  # the skip costs one pass over the table rather than one grep per instance.
  grep -av '^DONE-' "$OUT/results.tsv" | cut -f1 | sort -u > "$OUT/.done.ids"

  # Two different reasons to skip an instance, and they must not be conflated:
  # ALREADY RECORDED (resumption) and NOT SELECTED (the ONLY filter). The first
  # draft printed one number for both and reported "333 already recorded" for a
  # run whose results file was empty -- the harness misdescribing its own scope,
  # which is the failure mode this whole file exists to make impossible.
  : > "$OUT/todo.lst"
  : > "$OUT/.selected.ids"
  local mzn id
  while IFS= read -r mzn; do
    id="$(instance_id "$mzn")"
    if [ -n "$ONLY" ] && ! grep -qxF "$id" "$ONLY"; then continue; fi
    printf '%s\n' "$id" >> "$OUT/.selected.ids"
    grep -qxF "$id" "$OUT/.done.ids" && continue
    printf '%s\n' "$mzn" >> "$OUT/todo.lst"
  done < "$OUT/all.lst"

  local todo selected
  todo="$(wc -l < "$OUT/todo.lst")"
  selected="$(wc -l < "$OUT/.selected.ids")"
  [ "$selected" -gt 0 ] || die "the ONLY filter selected none of the $total instances"
  echo "corpus_run: $total in the corpus, $selected selected, $((selected - todo)) \
already recorded, $todo to run."
  echo "corpus_run: PAR=$PAR MEM_KB=$MEM_KB checker=$VERIPB"

  if [ "$todo" -gt 0 ]; then
    xargs -a "$OUT/todo.lst" -P "$PAR" -I{} bash -c 'run_one "$@"' _ {} \
      >> "$OUT/results.tsv"
  fi

  # The marker goes down only if every instance in all.lst now has a row. A run
  # killed part-way leaves no marker, and `report` then says PARTIAL rather than
  # printing a number that looks whole.
  # Completeness is judged against what was SELECTED, not against the corpus: a
  # deliberate ONLY run of 103 instances is complete when it has 103 rows. The
  # marker carries both numbers so the scope is never in doubt afterwards.
  local recorded
  recorded="$(grep -av '^DONE-' "$OUT/results.tsv" | cut -f1 | sort -u \
    | grep -cxF -f "$OUT/.selected.ids")"
  if [ "$recorded" -ge "$selected" ]; then
    printf 'DONE-%s\t%s\t%s\n' "$(date +%s)" "$recorded" "$total" >> "$OUT/results.tsv"
  else
    echo "corpus_run: PARTIAL -- $recorded of $selected recorded, no DONE marker written."
    echo "corpus_run: re-run with the same arguments to finish; nothing is recomputed."
  fi
  report
}

# Sourcing this file defines the functions and does nothing else, so the self-test
# can exercise validate_fzn against real torn bytes rather than re-implementing it.
[ -n "${BAGUETTE_CORPUS_SOURCE_ONLY:-}" ] && return 0

case "${1:-}" in
  --report)
    OUT="${OUT:-${2:-}}"
    [ -n "$OUT" ] || die "usage: corpus_run.sh --report <output-dir>"
    report
    ;;
  --self-test) exec "$ROOT/scripts/corpus_selftest.sh" ;;
  *) main ;;
esac
