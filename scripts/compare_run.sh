#!/usr/bin/env bash
# M6-T4 (absorbs M5-T3). The comparison harness: the same instance, flattened by EACH
# solver's own library, run by baguette, Chuffed and the Glasgow Constraint Solver, and
# every pair of answers compared. It is baguette's first EXTERNAL oracle: a
# `DISAGREE` involving baguette is a soundness finding, and is printed first.
#
# ---------------------------------------------------------------- shape
#
# Modelled on scripts/corpus_run.sh, and it keeps that file's discipline (D-0069: a
# measurement's own failures look exactly like findings about the subject, so every
# bucket that blames a SOLVER is gated on a validated input). corpus_run.sh is
# agent-perf's this wave, so it is NOT sourced: `require_local_fs`, `instance_id`,
# `validate_fzn` and `data_candidates` below are COPIED from it (wave 31, at e59f214),
# with `instance_id` deliberately byte-identical so that an `ONLY` list from a
# corpus_run.sh table selects the same instances here. If one changes, change both.
#
#   phase A, per INSTANCE   choose the data file, then flatten with every library
#   phase B, per (INSTANCE, SOLVER)   solve, then check the proof if one was logged
#
# ---------------------------------------------------------------- the instance
#
# An instance is (model, data), and the agreement verdict only means something if all
# three solvers saw the SAME one. So the data file is chosen ONCE per instance, by a
# rule that depends on the instance alone -- never on which solvers this run selected:
#
#   the smallest data file (corpus_run.sh's order, `data_candidates`, then the bare
#   model last) that AT LEAST ONE of the three libraries flattens.
#
# Phase A therefore flattens with all three libraries even on a single-solver pass
# (`SOLVERS=chuffed`), which is also what makes `$OUT/flatten.tsv` -- and from it
# bench/corpus/shared_set.lst -- a property of the corpus rather than of the run. The
# choice is recorded in `$OUT/pair.tsv` (every attempt in `log/<id>.pair`); a solver
# whose library then refuses that instance gets `FLATTEN-FAIL` for it. That is a
# library-coverage fact, not an answer.
#
# **The rule is deterministic only up to FLATTEN_TIMEOUT**, and that was MEASURED, not
# foreseen: `2025_gt-sort` (whose flatten is heavy -- a 1.5 MB .ozn) paired
# `n7_ub20_75.0_BEST.json` in the Chuffed pass and `n9_ub10_50.0_BEST.json` in the GCS
# pass, because on a loaded node the smaller one's flatten crossed the timeout in one
# run and not the other. Hence `PAIRS`: a run that is to be compared with an earlier
# one, or with bench/corpus/answers.tsv, pins its data from that file instead of
# re-deriving it, and `--answers` marks an instance whose runs paired differently
# DISPUTED rather than pinning either.
#
# Each library: baguette's mznlib via tools/baguette.msc (D-0067), Chuffed's own
# `share/minizinc/chuffed` via the bundle's chuffed.msc, GCS's `minizinc/mznlib` via
# the glasgow.msc its build writes beside `fzn-glasgow` (which asks for JSON FlatZinc,
# `inputType: JSON`). Flattening writes `.part` and `mv`s it into place (atomic on the
# local filesystem `require_local_fs` insists on). Then tools/compare/compare.py
# `prep` makes the objective an output variable in each flattened file -- the same
# edit for all three, so "the last printed objective" exists for every solver.
#
# ---------------------------------------------------------------- the 1.x shims
#
# The 2008-2010 Challenge models are MiniZinc 1.x: `:: is_output` and string-valued
# search annotations (`int_search(x, "first_fail", "indomain_min", "complete")`).
# MiniZinc 2.10.1's standard library defines neither, so Chuffed's and GCS's libraries
# refuse them at type-checking (`undefined identifier is_output`, `no function or
# predicate with this signature found: int_search(..., string, ...)`), while baguette's
# mznlib carries mznlib/compat_mzn1.mzn and flattens them. Measured on the first pilot
# attempt: 22 of 88 pilot instances were FLATTEN-FAIL for both other solvers for this
# reason alone, all of them 2008-2010 models. So with COMPAT=1 (default) that SAME file is
# passed to the other two flattens as a second model file. It is language
# compatibility only -- one inert annotation and a string -> ann mapping onto the
# standard annotations, plus a 2-argument `global_cardinality` that forwards to the
# solver's OWN global -- and decomposes nothing, so each solver still flattens with its
# own library. COMPAT=0 restores the strict behaviour.
#
# ---------------------------------------------------------------- the run
#
# Every solver runs under `timeout -k 30 $SOLVE_TIMEOUT`, `ulimit -v $MEM_KB` and
# `ulimit -f $PROOF_CAP_KB`, and follows the model's search annotation:
#   baguette  --max-heap-mb (MEM_KB/2, as corpus_run.sh) --proof <base>
#   chuffed   -a on optimisation only (intermediate solutions); NO -f, so free search
#             is OFF and the annotation is honoured. Restarts are Chuffed's default.
#   gcs       -i on optimisation only; no -f; --restarts left at its default 0 (off);
#             --prove --proof-files-basename <base> when GCS_PROVE=1 (default)
# SPEC 3.4 forbids baguette restarts, so the comparison is annotation-driven on all
# three. `ulimit -f` exists because GCS's proofs are LARGE -- 12 GB in two minutes on
# 2010_bacp_bacp-8 when it was first tried here -- and 16 jobs of that fill a disk.
#
# ---------------------------------------------------------------- the row
#
#   id solver status wall_s objective nsols fzn_bytes opb_bytes pbp_bytes
#      check_verdict check_s detail
#
# status, input-side (the HARNESS or the corpus, never the solver):
#   FLATTEN-FAIL   that solver's library did not flatten the chosen instance
#                  (detail says so for a flatten timeout)
#   NO-DATA        no data file anywhere and the model needs parameters
#   INPUT-INVALID  the flattened file is torn/empty/truncated (validate_fzn / prep)
# status, solver-side (only once the input is known good):
#   SAT            a solution (on an optimisation model: an incumbent, not proved)
#   UNSAT          =====UNSATISFIABLE=====, clean exit
#   OPT            ==========  after >= 1 solution on an optimisation model
#   UNKNOWN        clean exit, nothing proved
#   TIMEOUT        killed at SOLVE_TIMEOUT (nsols/objective still record what it found)
#   CAPPED         killed by SIGXFSZ: the harness's PROOF_CAP_KB file cap. Ours, not
#                  the solver's -- its own name so it can never read as an ERROR
#   REFUSED        baguette exit 2/3/5; the others: non-zero exit whose message says
#                  unsupported / not supported / not implemented
#   ERROR          any other non-zero exit (rc in the detail)
# objective: `-` for satisfaction, else `min:V` / `max:V` (V the LAST printed value,
#   `-` if none). check_verdict, for baguette and gcs (`-` for chuffed):
#   VERIFIED       veripb exit 0 and an `s VERIFIED ...` line
#   VERIFIED-WEAK  accepted, but the conclusion does not establish the printed status
#                  (UNSAT without UNSATISFIABLE, OPT without BOUNDS a <= obj <= a)
#   REJECTED       "Verification error at ..." + a "Caused by" that is not a grammar
#                  complaint -- the wording, not the exit status (CLAUDE.md, M2-T14)
#   CHECK-ERROR    anything else the checker said; TIMEOUT-CHECK  CHECK_TIMEOUT
#   NO-PROOF       clean exit, no .opb/.pbp;  NOT-CHECKED  the run did not finish
#
# The agreement verdict per instance (AGREE / DISAGREE / INCOMPLETE) is computed by
# `--report` from the table, so a resumed or merged table is judged as a whole.
#
# ---------------------------------------------------------------- usage
#
#   scripts/compare_run.sh <corpus-root> <out-dir>
#   scripts/compare_run.sh --report <out-dir> [<out-dir>...] [--pinned answers.tsv]
#   scripts/compare_run.sh --answers <out-dir>... <answers.tsv>
#   scripts/compare_run.sh --shared <out-dir>...       ids every library flattened
#
#   SOLVERS     which solvers RUN       (default "baguette chuffed gcs")
#   PAR         jobs PER SOLVER, default 16; PAR x |SOLVERS| is capped at 48
#   MEM_KB      per-process address-space cap, capped 32 GB (default 32000000)
#   PROOF_CAP_KB  per-file size cap (ulimit -f), default 16000000 (~16 GB)
#   SOLVE_TIMEOUT / FLATTEN_TIMEOUT / CHECK_TIMEOUT   (default 300 / 120 / 900)
#   MZN         minizinc               (default: PATH)
#   BAGUETTE    (default _build/default/bin/main.exe)
#   CHUFFED     (default fzn-chuffed beside minizinc)
#   GCS         fzn-glasgow            (default: PATH); GCS_MSC_DIR its .msc dir
#               (default: the binary's directory). GCS_PROVE=1|0 (default 1)
#   BAGUETTE_MZN_ID / CHUFFED_MZN_ID / GCS_MZN_ID   the solver ids flattened for
#   EXTRA_MSC_DIR  prepended to MZN_SOLVER_PATH (the self-test's shims)
#   ONLY        a file of instance ids; KEEP=1 keeps every artefact; DATA_TRIES (4)
#   PAIRS       a TSV whose column 1 is the id and whose LAST column is the data file
#               (`<none>` = bare): a run's pair.tsv, or bench/corpus/answers.tsv.
#               Listed ids use THAT data instead of searching. Use it for any run
#               meant to be compared with a pinned answer (see "the instance").
#   COMPAT      1 (default) passes COMPAT_MZN (mznlib/compat_mzn1.mzn) to the chuffed
#               and gcs flattens; 0 does not. See "the 1.x shims".
#
# Results are APPENDED and resumed by (id, solver); the last line of a complete run is
# `DONE-<epoch> <rows> <selected>`. `--report` refuses to call a table without it whole.

set -u -o pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TOOL="$ROOT/tools/compare/compare.py"

CORPUS="${CORPUS:-${1:-}}"
OUT="${OUT:-${2:-}}"
SOLVERS="${SOLVERS:-baguette chuffed gcs}"
PAR="${PAR:-16}"
MEM_KB="${MEM_KB:-32000000}"
PROOF_CAP_KB="${PROOF_CAP_KB:-16000000}"
SOLVE_TIMEOUT="${SOLVE_TIMEOUT:-300}"
FLATTEN_TIMEOUT="${FLATTEN_TIMEOUT:-120}"
CHECK_TIMEOUT="${CHECK_TIMEOUT:-900}"
MZN="${MZN:-minizinc}"
BAGUETTE="${BAGUETTE:-$ROOT/_build/default/bin/main.exe}"
CHUFFED="${CHUFFED:-}"
GCS="${GCS:-fzn-glasgow}"
GCS_MSC_DIR="${GCS_MSC_DIR:-}"
GCS_PROVE="${GCS_PROVE:-1}"
BAGUETTE_MZN_ID="${BAGUETTE_MZN_ID:-org.baguette.baguette}"
CHUFFED_MZN_ID="${CHUFFED_MZN_ID:-org.chuffed.chuffed}"
GCS_MZN_ID="${GCS_MZN_ID:-com.github.ciaranm.glasgow-constraint-solver}"
EXTRA_MSC_DIR="${EXTRA_MSC_DIR:-}"
KEEP="${KEEP:-0}"
ONLY="${ONLY:-}"
DATA_TRIES="${DATA_TRIES:-4}"
PAIRS="${PAIRS:-}"
COMPAT="${COMPAT:-1}"
COMPAT_MZN="${COMPAT_MZN:-$ROOT/mznlib/compat_mzn1.mzn}"

TOTAL_MAX=48
MEM_KB_MAX=32000000
# The three libraries the data pairing consults: ALWAYS all three (see "the instance").
PAIR_SOLVERS="baguette chuffed gcs"

die() {
  echo "compare_run: $*" >&2
  exit 1
}

# ------------------------------------------- copied from scripts/corpus_run.sh
# (read-only this wave; see the header). Same bodies, same reasons -- the comments
# that justify them live there and are not repeated here.

require_local_fs() {
  local dir="$1" fstype
  fstype="$(df -PT "$dir" 2>/dev/null | awk 'NR==2 {print $2}')"
  case "$fstype" in
    nfs | nfs3 | nfs4 | cifs | smbfs | fuse.sshfs | 9p)
      die "$dir is on $fstype. Rename is not reliably atomic there, and this harness
            depends on it to never hand a half-written .fzn to a solver. Point OUT at
            local storage (on fataepyc-07: /scratch)."
      ;;
    "") echo "compare_run: WARNING: could not determine the filesystem type of $dir." >&2 ;;
    *) ;;
  esac
}

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

validate_fzn() {
  local f="$1" solves last tail_after
  [ -f "$f" ] || {
    echo "the .fzn does not exist"
    return 1
  }
  [ -s "$f" ] || {
    echo "the .fzn is empty"
    return 1
  }
  if [ "$(wc -c < "$f")" -ne "$(tr -d '\000' < "$f" | wc -c)" ]; then
    echo "the .fzn contains NUL bytes -- a partial or interleaved write"
    return 1
  fi
  # JSON FlatZinc (GCS) is not line-structured; compare.py `prep` parses it whole,
  # which is the stronger completeness check, and is run on every file anyway.
  if [ "$(head -c 64 "$f" | tr -d '[:space:]' | cut -c1)" = "{" ]; then
    return 0
  fi
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
  last="$(tail -c 4096 "$f" | tr -d '\r' | grep -v '^[[:space:]]*$' | tail -1)"
  case "$last" in
    *\;) ;;
    *)
      echo "the .fzn does not end in a complete item -- truncated"
      return 1
      ;;
  esac
  tail_after="$(sed -n '/^[[:space:]]*solve/,$p' "$f" | tr '\n' ' ' | sed 's/^[^;]*;//' \
    | tr -d '[:space:]')"
  if [ -n "$tail_after" ]; then
    echo "content follows the solve item ('$(printf '%s' "$tail_after" | cut -c1-40)') -- torn write"
    return 1
  fi
  return 0
}

data_candidates() {
  local dir="$1" limit="${2:-4}"
  find "$dir" -maxdepth 2 -type f \( -name '*.dzn' -o -name '*.json' \) \
    -printf '%s\t%p\n' 2>/dev/null | sort -n -k1,1 | head -n "$limit" | cut -f2-
  return 0
}

# ------------------------------------------------------------------ helpers

flat() { printf '%s' "$1" | tr '\t\n\r' '   ' | cut -c1-200; }

# id solver status wall objective nsols fzn opb pbp verdict check_s detail
emit() {
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$1" "$2" "$3" "$4" "$5" \
    "$6" "$7" "$8" "$9" "${10}" "${11}" "$(flat "${12}")"
}

mzn_id_of() {
  case "$1" in
    baguette) printf '%s' "$BAGUETTE_MZN_ID" ;;
    chuffed) printf '%s' "$CHUFFED_MZN_ID" ;;
    gcs) printf '%s' "$GCS_MZN_ID" ;;
  esac
}

now_ns() { date +%s%N; }
secs() { awk -v a="$1" -v b="$2" 'BEGIN { printf "%.3f", (b - a) / 1e9 }'; }

has_row() { # id solver
  [ -f "$OUT/results.tsv" ] && awk -F'\t' -v i="$1" -v s="$2" \
    '$1 == i && $2 == s { f = 1; exit } END { exit !f }' "$OUT/results.tsv"
}

# Flatten $1 (mzn) with $2's library and data $3 ('' = bare) into $4. Prints the
# failure message on failure. rc 0 ok, 1 refused, 124 timeout.
flatten_with() {
  local mzn="$1" solver="$2" dat="$3" dst="$4" rc compat=""
  rm -f "$dst.part" "$dst"
  # The MiniZinc 1.x LANGUAGE shims (see "the 1.x shims" in the header): baguette's
  # library includes them itself, the other two get the same file as a second model.
  [ "$COMPAT" = 1 ] && [ "$solver" != baguette ] && compat="$COMPAT_MZN"
  # --no-output-ozn: with `-o X.part` MiniZinc cannot derive the .ozn's name from the
  # .fzn's, and writes `<model>.ozn` BESIDE THE MODEL -- i.e. into the shared corpus.
  # Found on the node 2026-10-01: 412 stray .ozn files under mzn-challenge/. Nothing
  # here reads an .ozn (the solvers print FlatZinc output directly).
  timeout -k 10 "$FLATTEN_TIMEOUT" "$MZN" -c --no-output-ozn --solver "$(mzn_id_of "$solver")" \
    "$mzn" ${compat:+"$compat"} ${dat:+"$dat"} -o "$dst.part" > "$dst.err" 2>&1
  rc=$?
  if [ "$rc" -eq 0 ] && [ -s "$dst.part" ]; then
    mv -f "$dst.part" "$dst" || {
      echo "could not rename the flattened model into place"
      return 1
    }
    rm -f "$dst.err"
    return 0
  fi
  rm -f "$dst.part"
  [ "$rc" -eq 124 ] || [ "$rc" -eq 137 ] && {
    echo "flatten exceeded ${FLATTEN_TIMEOUT}s"
    return 124
  }
  # MiniZinc's "did you forget to specify a data file?" can follow pages of warnings,
  # so it is looked for in the WHOLE message, not in the 200 bytes kept. Two instances
  # of the first Chuffed pass were FLATTEN-FAIL instead of NO-DATA for exactly that.
  grep -qa 'did you forget to specify a data file' "$dst.err" && printf '[needs-data] '
  head -c 200 "$dst.err"
  [ "$rc" -eq 0 ] && echo " (minizinc exited 0 but wrote nothing)"
  return 1
}

# Validate + prep one flattened file. Prints `OK<TAB>sense<TAB>objname` or
# `INVALID<TAB>reason`.
check_input() {
  local f="$1" reason sp
  if ! reason="$(validate_fzn "$f")"; then
    printf 'INVALID\t%s\n' "$reason"
    return
  fi
  if ! sp="$(python3 "$TOOL" prep "$f")"; then
    printf 'INVALID\t%s\n' "$sp"
    return
  fi
  printf 'OK\t%s\n' "$sp"
}

# ------------------------------------------------------------------ phase A

pair_one() {
  local mzn="$1" id W c s ndata msg rc chosen="" found=0 first_err="" ok_any
  local -a cands=()
  id="$(instance_id "$mzn")"
  W="$OUT/work/$id"
  ulimit -v "$MEM_KB" 2>/dev/null
  while IFS= read -r c; do
    [ -n "$c" ] && cands+=("$c")
  done < <(data_candidates "$(dirname "$mzn")" "$DATA_TRIES")
  ndata=${#cands[@]}
  cands+=("")
  # PAIRS pins the data file instead of searching for it (see "the instance").
  local pinned=""
  if [ -n "$PAIRS" ]; then
    pinned="$(awk -F'\t' -v i="$id" '$1 == i {d = $NF} END {print d}' "$PAIRS")"
    if [ -n "$pinned" ]; then
      # answers.tsv stores data relative to the corpus root; pair.tsv absolute.
      case "$pinned" in
        "<none>") cands=("") ;;
        /*) cands=("$pinned") ;;
        *) cands=("$CORPUS/$pinned") ;;
      esac
    fi
  fi
  : > "$OUT/log/$id.pair"
  [ -n "$pinned" ] && printf 'pinned\t%s\tfrom %s\n' "$pinned" "$PAIRS" >> "$OUT/log/$id.pair"
  declare -A res=() det=()
  for c in "${cands[@]}"; do
    ok_any=0
    for s in $PAIR_SOLVERS; do
      msg="$(flatten_with "$mzn" "$s" "$c" "$W.$s.fzn")"
      rc=$?
      res[$s]=$rc
      det[$s]="$msg"
      printf '%s\t%s\trc=%s\t%s\n' "${c:-<none>}" "$s" "$rc" "$(flat "$msg")" \
        >> "$OUT/log/$id.pair"
      [ "$rc" -eq 0 ] && ok_any=1
      [ -n "$first_err" ] || [ "$rc" -eq 0 ] || first_err="$msg"
    done
    if [ "$ok_any" -eq 1 ]; then
      chosen="${c:-<none>}"
      found=1
      break
    fi
  done
  rm -f "$W".*.fzn.err
  if [ "$found" -ne 1 ]; then
    local st="FLATTEN-FAIL" why="[$ndata data file(s) + bare, no library flattened any] $first_err"
    if [ "$ndata" -eq 0 ] && [ "${first_err#\[needs-data\] }" != "$first_err" ]; then
      st="NO-DATA"
      why="no .dzn/.json under $(dirname "$mzn") and the model needs parameters"
    fi
    printf '%s\t%s\t%s\t%s\n' "$id" "$mzn" "$st" "-" >> "$OUT/pair.tsv"
    for s in $PAIR_SOLVERS; do
      printf '%s\t%s\t%s\t-\t-\t-\t%s\n' "$id" "$s" "$st" "$(flat "$why")" >> "$OUT/flatten.tsv"
    done
    for s in $SOLVERS; do
      has_row "$id" "$s" || emit "$id" "$s" "$st" - - - - - - - - "$why" >> "$OUT/results.tsv"
    done
    return
  fi
  local line verdict sense obj bytes
  for s in $PAIR_SOLVERS; do
    if [ "${res[$s]}" -eq 0 ]; then
      line="$(check_input "$W.$s.fzn")"
      verdict="$(printf '%s' "$line" | cut -f1)"
      if [ "$verdict" = OK ]; then
        sense="$(printf '%s' "$line" | cut -f2)"
        obj="$(printf '%s' "$line" | cut -f3)"
        bytes="$(stat -c%s "$W.$s.fzn")"
        printf '%s\t%s\tOK\t%s\t%s\t%s\t-\n' "$id" "$s" "$bytes" "$sense" "$obj" \
          >> "$OUT/flatten.tsv"
      else
        printf '%s\t%s\tINPUT-INVALID\t-\t-\t-\t%s\n' "$id" "$s" \
          "$(flat "$(printf '%s' "$line" | cut -f2-)")" >> "$OUT/flatten.tsv"
      fi
    else
      printf '%s\t%s\tFLATTEN-FAIL\t-\t-\t-\t%s\n' "$id" "$s" "$(flat "${det[$s]}")" \
        >> "$OUT/flatten.tsv"
    fi
  done
  printf '%s\t%s\t%s\t%s\n' "$id" "$mzn" "PAIRED" "$chosen" >> "$OUT/pair.tsv"
  emit_input_failures "$id"
  # A solver that does not run keeps no flattened file, unless KEEP.
  if [ "$KEEP" != 1 ]; then
    for s in $PAIR_SOLVERS; do
      case " $SOLVERS " in *" $s "*) ;; *) rm -f "$W.$s.fzn" ;; esac
    done
  fi
}

# For a paired instance, write the input-side row of every SELECTED solver whose
# library did not produce a valid file. Also used on resumption.
emit_input_failures() {
  local id="$1" s fl st det
  for s in $SOLVERS; do
    has_row "$id" "$s" && continue
    fl="$(awk -F'\t' -v i="$id" -v s="$s" '$1 == i && $2 == s' "$OUT/flatten.tsv" | tail -1)"
    st="$(printf '%s' "$fl" | cut -f3)"
    det="$(printf '%s' "$fl" | cut -f7)"
    case "$st" in
      OK | '') ;;
      *) emit "$id" "$s" "$st" - - - - - - - - "$det" >> "$OUT/results.tsv" ;;
    esac
  done
}

# ------------------------------------------------------------------ phase B

solve_one() {
  local id="$1" s="$2" W L fl sense obj fzn bytes model dat rc t0 t1 wall cls status
  local objective nsols detail opb=- pbp=- verdict=- check_s=- msg line
  W="$OUT/work/$id"
  L="$OUT/log/$id.$s"
  fzn="$W.$s.fzn"
  ulimit -v "$MEM_KB" 2>/dev/null
  fl="$(awk -F'\t' -v i="$id" -v s="$s" '$1 == i && $2 == s' "$OUT/flatten.tsv" | tail -1)"
  sense="$(printf '%s' "$fl" | cut -f5)"
  obj="$(printf '%s' "$fl" | cut -f6)"
  if [ ! -s "$fzn" ]; then
    # Resumed after the file was cleaned up: flatten again with the RECORDED data.
    model="$(awk -F'\t' -v i="$id" '$1 == i {m = $2} END {print m}' "$OUT/pair.tsv")"
    dat="$(awk -F'\t' -v i="$id" '$1 == i {d = $4} END {print d}' "$OUT/pair.tsv")"
    [ "$dat" = "<none>" ] && dat=""
    if ! msg="$(flatten_with "$model" "$s" "$dat" "$fzn")"; then
      emit "$id" "$s" FLATTEN-FAIL - - - - - - - - "on re-flatten: $msg"
      return
    fi
    line="$(check_input "$fzn")"
    if [ "$(printf '%s' "$line" | cut -f1)" != OK ]; then
      emit "$id" "$s" INPUT-INVALID - - - - - - - - "$(printf '%s' "$line" | cut -f2-)"
      return
    fi
  fi
  bytes="$(stat -c%s "$fzn")"
  rm -f "$L".*
  local -a cmd=()
  case "$s" in
    baguette)
      local heap=$(( MEM_KB / 1024 / 2 ))
      cmd=("$BAGUETTE" --max-heap-mb "$heap" --proof "$L" "$fzn")
      ;;
    chuffed)
      cmd=("$CHUFFED")
      [ "$sense" = sat ] || cmd+=(-a)
      cmd+=("$fzn")
      ;;
    gcs)
      cmd=("$GCS")
      [ "$sense" = sat ] || cmd+=(-i)
      [ "$GCS_PROVE" = 1 ] && cmd+=(--prove --proof-files-basename "$L")
      cmd+=("$fzn")
      ;;
  esac
  t0="$(now_ns)"
  (
    ulimit -f "$PROOF_CAP_KB" 2>/dev/null
    exec timeout -k 30 "$SOLVE_TIMEOUT" "${cmd[@]}"
  ) > "$L.out" 2> "$L.err"
  rc=$?
  t1="$(now_ns)"
  wall="$(secs "$t0" "$t1")"
  cls="$(python3 "$TOOL" classify "$s" "$rc" "$L.out" "$L.err" "$sense" "$obj" 153)"
  status="$(printf '%s' "$cls" | cut -f1)"
  objective="$(printf '%s' "$cls" | cut -f2)"
  nsols="$(printf '%s' "$cls" | cut -f3)"
  detail="$(printf '%s' "$cls" | cut -f4-)"

  case "$s" in baguette | gcs)
    if [ "$s" = gcs ] && [ "$GCS_PROVE" != 1 ]; then
      verdict=-
    elif [ "$rc" -ne 0 ]; then
      verdict=NOT-CHECKED
      [ -s "$L.pbp" ] && pbp="$(stat -c%s "$L.pbp")"
      [ -s "$L.opb" ] && opb="$(stat -c%s "$L.opb")"
    elif [ ! -s "$L.pbp" ] || [ ! -s "$L.opb" ]; then
      verdict=NO-PROOF
    else
      opb="$(stat -c%s "$L.opb")"
      pbp="$(stat -c%s "$L.pbp")"
      t0="$(now_ns)"
      timeout -k 30 "$CHECK_TIMEOUT" "$VERIPB" "$L.opb" "$L.pbp" > "$L.vp" 2>&1
      rc=$?
      t1="$(now_ns)"
      check_s="$(secs "$t0" "$t1")"
      line="$(python3 "$TOOL" verdict "$rc" "$L.vp" "$status")"
      verdict="$(printf '%s' "$line" | cut -f1)"
      detail="${detail:+$detail; }$(printf '%s' "$line" | cut -f2-)"
    fi
    ;;
  esac
  emit "$id" "$s" "$status" "$wall" "$objective" "$nsols" "$bytes" "$opb" "$pbp" \
    "$verdict" "$check_s" "$detail"
  [ "$KEEP" = 1 ] && return 0
  # A rejected or weak proof is the evidence: kept unconditionally (corpus_run.sh).
  case "$verdict" in REJECTED | VERIFIED-WEAK | CHECK-ERROR) return 0 ;; esac
  rm -f "$L.opb" "$L.pbp" "$L.scp" "$L.varmap"
  case "$status" in REFUSED | ERROR) ;; *) rm -f "$fzn" ;; esac
  return 0
}

# ------------------------------------------------------------------ preflight

preflight() {
  [ -n "$CORPUS" ] || die "no corpus root. Usage: compare_run.sh <corpus-root> <output-dir>"
  [ -n "$OUT" ] || die "no output dir. Usage: compare_run.sh <corpus-root> <output-dir>"
  [ -d "$CORPUS" ] || die "corpus root $CORPUS does not exist"
  command -v python3 >/dev/null 2>&1 || die "python3 is required (tools/compare/compare.py)"
  [ -f "$TOOL" ] || die "$TOOL is missing"
  [ "$COMPAT" != 1 ] || [ -f "$COMPAT_MZN" ] || die "COMPAT=1 but $COMPAT_MZN is missing"
  [ -z "$PAIRS" ] || [ -f "$PAIRS" ] || die "PAIRS=$PAIRS does not exist"
  command -v "$MZN" >/dev/null 2>&1 || die "minizinc not found (MZN=$MZN)"
  MZN="$(command -v "$MZN")"
  [ -n "$CHUFFED" ] || CHUFFED="$(dirname "$MZN")/fzn-chuffed"
  GCS="$(command -v "$GCS" 2>/dev/null || printf '%s' "$GCS")"
  [ -n "$GCS_MSC_DIR" ] || GCS_MSC_DIR="$(dirname "$GCS")"
  local s n=0
  for s in $SOLVERS; do
    case "$s" in
      baguette) [ -x "$BAGUETTE" ] || die "baguette not executable: $BAGUETTE (dune build --root . bin/)" ;;
      chuffed) [ -x "$CHUFFED" ] || die "fzn-chuffed not executable: $CHUFFED" ;;
      gcs) [ -x "$GCS" ] || die "fzn-glasgow not executable: $GCS" ;;
      *) die "unknown solver '$s' in SOLVERS (baguette chuffed gcs)" ;;
    esac
    n=$((n + 1))
  done
  [ "$n" -gt 0 ] || die "SOLVERS is empty"
  NSOLVERS=$n
  # D-0067 for baguette; the shims' and GCS's .msc directories for the others. The
  # bundle's own solvers (Chuffed) are found by minizinc without help.
  export MZN_SOLVER_PATH="${EXTRA_MSC_DIR:+$EXTRA_MSC_DIR:}$ROOT/tools:$GCS_MSC_DIR"
  # Every library must be present: the pairing rule consults all three.
  local avail
  avail="$("$MZN" --solvers 2>/dev/null)"
  for s in $PAIR_SOLVERS; do
    printf '%s' "$avail" | grep -qF "$(mzn_id_of "$s")" \
      || die "minizinc does not know solver '$(mzn_id_of "$s")' ($s). The data pairing
            consults all three libraries, so all three must be installed even when
            SOLVERS='$SOLVERS'. MZN_SOLVER_PATH=$MZN_SOLVER_PATH"
  done
  # A MISSING checker is a failure and never a skip (CLAUDE.md).
  # shellcheck source=/dev/null
  . "$ROOT/scripts/checker.sh"
  baguette_resolve_veripb || {
    baguette_veripb_diagnostic
    die "no veripb. Every logged proof must be checked, so this run would say nothing."
  }
  export VERIPB
  local cap=$(( TOTAL_MAX / NSOLVERS ))
  if [ "$PAR" -gt "$cap" ]; then
    echo "compare_run: PAR=$PAR x $NSOLVERS solvers exceeds $TOTAL_MAX jobs; capping PAR at $cap." >&2
    PAR=$cap
  fi
  if [ "$MEM_KB" -gt "$MEM_KB_MAX" ]; then
    echo "compare_run: MEM_KB=$MEM_KB exceeds 32 GB; capping." >&2
    MEM_KB=$MEM_KB_MAX
  fi
  case "$DATA_TRIES" in '' | *[!0-9]*) die "DATA_TRIES must be a number" ;; esac
  mkdir -p "$OUT/log" "$OUT/work" || die "cannot create $OUT"
  require_local_fs "$OUT"
  touch "$OUT/results.tsv" "$OUT/pair.tsv" "$OUT/flatten.tsv"
}

hash_of() { [ -f "$1" ] && md5sum "$1" | cut -d' ' -f1 || echo "-"; }

write_conf() {
  # Every binary hashed, so no number from this run is quoted without knowing what
  # produced it (CLAUDE.md: "a comparison whose two sides used the same binary...").
  {
    echo "started=$(date -Is)"
    echo "solvers=$SOLVERS"
    echo "solve_timeout=$SOLVE_TIMEOUT"
    echo "flatten_timeout=$FLATTEN_TIMEOUT"
    echo "check_timeout=$CHECK_TIMEOUT"
    echo "par_per_solver=$PAR"
    echo "mem_kb=$MEM_KB"
    echo "proof_cap_kb=$PROOF_CAP_KB"
    echo "minizinc=$MZN"
    echo "minizinc_md5=$(hash_of "$MZN")"
    echo "baguette=$BAGUETTE"
    echo "baguette_md5=$(hash_of "$BAGUETTE")"
    echo "harness_commit=$(git -C "$ROOT" rev-parse --short HEAD 2>/dev/null || echo -)"
    echo "chuffed=$CHUFFED"
    echo "chuffed_md5=$(hash_of "$CHUFFED")"
    echo "gcs=$GCS"
    echo "gcs_md5=$(hash_of "$GCS")"
    echo "gcs_commit=$(git -C "$(dirname "$GCS")" rev-parse --short HEAD 2>/dev/null || echo -)"
    echo "gcs_prove=$GCS_PROVE"
    echo "compat=$COMPAT ${COMPAT_MZN} $(hash_of "$COMPAT_MZN")"
    echo "veripb=$VERIPB $("$VERIPB" --version 2>/dev/null | tail -1)"
  } > "$OUT/run.conf.part" && mv -f "$OUT/run.conf.part" "$OUT/run.conf"
}

# ------------------------------------------------------------------ main

main() {
  preflight
  # A resumed run keeps its first configuration on record; a changed one is noted.
  if [ -f "$OUT/run.conf" ]; then
    cp -f "$OUT/run.conf" "$OUT/run.conf.prev"
  fi
  write_conf
  export OUT MZN BAGUETTE CHUFFED GCS GCS_PROVE MEM_KB PROOF_CAP_KB SOLVE_TIMEOUT
  export FLATTEN_TIMEOUT CHECK_TIMEOUT KEEP DATA_TRIES SOLVERS PAIR_SOLVERS TOOL VERIPB
  export BAGUETTE_MZN_ID CHUFFED_MZN_ID GCS_MZN_ID COMPAT COMPAT_MZN PAIRS CORPUS
  export -f pair_one solve_one flatten_with check_input emit_input_failures instance_id
  export -f validate_fzn data_candidates emit flat mzn_id_of now_ns secs has_row

  find "$CORPUS" -mindepth 3 -name '*.mzn' | sort > "$OUT/all.lst"
  local total
  total="$(wc -l < "$OUT/all.lst")"
  [ "$total" -gt 0 ] || die "no *.mzn found under $CORPUS (expected <root>/<year>/<family>/)"

  : > "$OUT/.selected.ids"
  : > "$OUT/todo.pair"
  local mzn id
  cut -f1 "$OUT/pair.tsv" | sort -u > "$OUT/.paired.ids"
  while IFS= read -r mzn; do
    id="$(instance_id "$mzn")"
    if [ -n "$ONLY" ] && ! grep -qxF "$id" "$ONLY"; then continue; fi
    printf '%s\n' "$id" >> "$OUT/.selected.ids"
    grep -qxF "$id" "$OUT/.paired.ids" || printf '%s\n' "$mzn" >> "$OUT/todo.pair"
  done < "$OUT/all.lst"
  local selected
  selected="$(wc -l < "$OUT/.selected.ids")"
  [ "$selected" -gt 0 ] || die "the ONLY filter selected none of the $total instances"
  local total_par=$(( PAR * NSOLVERS ))
  echo "compare_run: $total in the corpus, $selected selected, $(wc -l < "$OUT/todo.pair") to pair."
  echo "compare_run: SOLVERS='$SOLVERS' PAR=$PAR per solver ($total_par total) MEM_KB=$MEM_KB \
SOLVE_TIMEOUT=$SOLVE_TIMEOUT checker=$VERIPB"

  # Phase A.
  if [ -s "$OUT/todo.pair" ]; then
    xargs -a "$OUT/todo.pair" -P "$total_par" -I{} bash -c 'pair_one "$@"' _ {}
  fi
  # Resumption: input-side rows for solvers newly selected on an already-paired id.
  while IFS= read -r id; do
    awk -F'\t' -v i="$id" '$1 == i && $3 == "PAIRED" {f = 1} END {exit !f}' "$OUT/pair.tsv" \
      && emit_input_failures "$id"
  done < "$OUT/.selected.ids"

  # Phase B: one xargs per solver, each -P PAR, so no solver ever exceeds its share.
  local s pids=()
  for s in $SOLVERS; do
    : > "$OUT/todo.$s"
    while IFS= read -r id; do
      has_row "$id" "$s" && continue
      awk -F'\t' -v i="$id" -v s="$s" '$1 == i && $2 == s && $3 == "OK" {f = 1} END {exit !f}' \
        "$OUT/flatten.tsv" || continue
      printf '%s\n' "$id" >> "$OUT/todo.$s"
    done < "$OUT/.selected.ids"
    echo "compare_run: $s: $(wc -l < "$OUT/todo.$s") to run."
    if [ -s "$OUT/todo.$s" ]; then
      xargs -a "$OUT/todo.$s" -P "$PAR" -I{} bash -c 'solve_one "$1" "$2"' _ {} "$s" \
        >> "$OUT/results.tsv" &
      pids+=($!)
    fi
  done
  local p
  for p in "${pids[@]}"; do wait "$p"; done

  # Complete when every selected (id, solver) has a row.
  local want=0 have=0
  for s in $SOLVERS; do
    while IFS= read -r id; do
      want=$((want + 1))
      has_row "$id" "$s" && have=$((have + 1))
    done < "$OUT/.selected.ids"
  done
  if [ "$have" -ge "$want" ]; then
    printf 'DONE-%s\t%s\t%s\n' "$(date +%s)" "$have" "$selected" >> "$OUT/results.tsv"
  else
    echo "compare_run: PARTIAL -- $have of $want (instance, solver) rows; no DONE marker."
    echo "compare_run: re-run with the same arguments to finish; nothing is recomputed."
  fi
  python3 "$TOOL" report "$OUT"
}

[ -n "${BAGUETTE_COMPARE_SOURCE_ONLY:-}" ] && return 0

case "${1:-}" in
  --report)
    shift
    [ $# -gt 0 ] || die "usage: compare_run.sh --report <out-dir>... [--pinned answers.tsv]"
    exec python3 "$TOOL" report "$@"
    ;;
  --answers)
    shift
    [ $# -ge 2 ] || die "usage: compare_run.sh --answers <out-dir>... <answers.tsv>"
    exec python3 "$TOOL" answers "$@"
    ;;
  --shared)
    shift
    [ $# -ge 1 ] || die "usage: compare_run.sh --shared <out-dir>..."
    exec python3 "$TOOL" shared "$@"
    ;;
  --self-test) exec "$ROOT/scripts/compare_selftest.sh" ;;
  *) main ;;
esac
