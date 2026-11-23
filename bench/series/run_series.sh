#!/usr/bin/env bash
# M17-bench-series-T1 (D-0203). One Challenge series, from a commit, in arms.
#
#   bench/series/run_series.sh --name NAME --commit REV --par N [--arm LABEL:proof|noproof:FLAGS ...]
#                              [--repo URL] [--dir DIR] [--results DIR] [--phase PHASE]
#
# An arm is `LABEL:proof:FLAGS` (a proof is logged and veripb checks it) or `LABEL:noproof:FLAGS`
# (`--no-proof`; the answers are UNVERIFIED). FLAGS are baguette's, e.g. `-f`, may be empty.
# Default arms: `A:proof:`  `B:proof:-f`  `C:noproof:`.  REV must be on --repo (default: the hub
# /cluster/arthur/baguette.git), so push the branch first. The driver and its helpers are those of
# the CLONE at REV, so a series measures one commit end to end, mznlib included.
#
# Phases, each idempotent, in order (--phase runs one of them):
#   setup    clone at REV, build the release binary (dune -j 16, the recipe of `make release`),
#            hash it, copy it to DIR/bin, write DIR/series.conf, generate the arm shims
#   flatten  every edition's instances, flattened ONCE with the clone's mznlib (all arms hard-link
#            the .fzn), the editions side by side, PAR_FLAT instances in all (default: PAR x arms)
#   run      the arms side by side, 2026 down to 2011, `PAR` instances at a time PER ARM; veripb on
#            every finished run (bench/series/veripb_wrap.sh: own cgroup, own time limit)
#   read     bench/series/read_series.sh: the tables, into DIR/tables
#   publish  copy the tables to --results (default /cluster/arthur/baguette-results/series-<DATE>)
#
# Settings are D-0133's: 1 200 s solve, 1 200 s flatten, 16 GiB address space for the SOLVER, 16 GB
# proof cap, --max-heap-mb 8192, each solver run in `systemd-run --user --scope -p MemoryMax=32G`.
# veripb: MemoryMax=64G, no address-space cap, 3 600 s of checking (D-0203). PAR is per arm, so the
# processes running at once are PAR x arms, solver or checker alike (a worker runs one at a time):
# keep it at 92 or below, the user's rule for the node. Verified runs' .opb/.pbp are deleted by the
# harness (their sizes stay in results.tsv); a REJECTED or CHECK-ERROR run keeps its files.
#
# Resumable: run it again with the same arguments. setup and flatten skip what exists, and
# compare_run.sh skips every (instance, solver) that already has a row. Pidfiles only: the driver
# writes DIR/pid, each arm driver DIR/<LABEL>.pid, the monitor DIR/monitor.pid. To stop a series,
# `kill $(cat DIR/pid DIR/*.pid)`, nothing else, and `ps` first.
set -u
NAME=""; COMMIT=""; PAR=""; REPO=/cluster/arthur/baguette.git; DIR=""; RESULTS=""; PHASE=all
ARMS=()
while [ $# -gt 0 ]; do
  case "$1" in
    --name) NAME="$2"; shift 2 ;;
    --commit) COMMIT="$2"; shift 2 ;;
    --par) PAR="$2"; shift 2 ;;
    --arm) ARMS+=("$2"); shift 2 ;;
    --repo) REPO="$2"; shift 2 ;;
    --dir) DIR="$2"; shift 2 ;;
    --results) RESULTS="$2"; shift 2 ;;
    --phase) PHASE="$2"; shift 2 ;;
    *) echo "run_series: unknown argument $1" >&2; exit 2 ;;
  esac
done
[ -n "$NAME" ] && [ -n "$COMMIT" ] && [ -n "$PAR" ] || { sed -n 2,6p "$0" >&2; exit 2; }
[ ${#ARMS[@]} -gt 0 ] || ARMS=("A:proof:" "B:proof:-f" "C:noproof:")
DIR="${DIR:-/scratch/arthur/series-$NAME}"
RESULTS="${RESULTS:-/cluster/arthur/baguette-results/series-$NAME}"
SRC="$DIR/src"
YEARS="2026 2025 2024 2023 2022 2021 2020 2019 2018 2017 2016 2015 2014 2013 2012 2011"
export PATH=$HOME/.local/bin:$HOME/.cargo/bin:/scratch/arthur/mzn/MiniZincIDE-2.10.1-x86_64-linux-gnu/bin:$PATH
mkdir -p "$DIR/log" "$DIR/sem"
NARMS=${#ARMS[@]}
TOTAL=$((PAR * NARMS))
[ "$TOTAL" -le 92 ] || { echo "run_series: PAR x arms = $TOTAL exceeds 92" >&2; exit 2; }
PAR_FLAT="${PAR_FLAT:-$TOTAL}"
log() { echo "=== $(date -Is) $*" | tee -a "$DIR/log/driver.log"; }
arm_field() { printf '%s' "$1" | cut -d: -f"$2"; }

phase_setup() {
  if [ ! -d "$SRC/.git" ]; then git clone -q "$REPO" "$SRC" || exit 1; fi
  git -C "$SRC" checkout -q "$COMMIT" || exit 1
  eval "$(opam env --switch=baguette)"
  if [ ! -x "$DIR/bin/main.exe" ]; then
    # The recipe of `make release`, with dune's jobs capped at 16 (the user's make -j rule).
    ( cd "$SRC" && dune build --root . --profile release --build-dir _build_release -j 16 bin/main.exe ) \
      > "$DIR/log/build.log" 2>&1 || { echo "build failed, see $DIR/log/build.log" >&2; exit 1; }
    mkdir -p "$DIR/bin"
    cp "$SRC/_build_release/default/bin/main.exe" "$DIR/bin/main.exe"
  fi
  md5sum "$DIR/bin/main.exe" | cut -d' ' -f1 > "$DIR/bin/binary.md5"
  cp "$SRC/bench/series/rss_wrap.py" "$SRC/bench/series/veripb_wrap.sh" "$SRC/bench/series/solver_wrap.sh" "$DIR/bin/"
  for a in "${ARMS[@]}"; do
    l=$(arm_field "$a" 1); p=$(arm_field "$a" 2); f=$(printf '%s' "$a" | cut -d: -f3-)
    cat > "$DIR/bin/baguette-$l.sh" <<SHIM
#!/bin/bash
export SERIES_BIN=$DIR/bin/main.exe SERIES_FLAGS="$f" SERIES_RSS_WRAP=$DIR/bin/rss_wrap.py
export SERIES_PROOF=$([ "$p" = proof ] && echo 1 || echo 0)
exec $DIR/bin/solver_wrap.sh "\$@"
SHIM
    chmod +x "$DIR/bin/baguette-$l.sh"
  done
  cat > "$DIR/bin/flatten-only.sh" <<'FO'
#!/bin/bash
echo "series flatten pass, not a solver run" >&2
exit 2
FO
  chmod +x "$DIR/bin/flatten-only.sh"
  {
    echo "name=$NAME"
    echo "commit=$(git -C "$SRC" rev-parse HEAD)"
    echo "subject=$(git -C "$SRC" log -1 --format=%s | cut -c1-120)"
    echo "binary_md5=$(cat "$DIR/bin/binary.md5")"
    echo "par=$PAR"
    echo "total_par=$TOTAL"
    echo "solve_timeout=1200"
    echo "flatten_timeout=1200"
    echo "check_limit=3600"
    echo "solver_mem=16GiB address space, MemoryMax=32G, --max-heap-mb 8192, proof cap 16 GB"
    echo "check_mem=MemoryMax=64G, no address-space cap, at most 12 proofs of 2 GiB or more at once"
    echo "veripb=$($HOME/.cargo/bin/veripb --version 2>&1 | tail -1)"
    echo "host=$(hostname)"
    for a in "${ARMS[@]}"; do echo "arm=$a"; done
  } > "$DIR/series.conf.new"
  # The start date is that of the FIRST setup, so a resumed series keeps it.
  if [ -f "$DIR/series.conf" ]; then grep '^started=' "$DIR/series.conf" >> "$DIR/series.conf.new"
  else echo "started=$(date -Is)" >> "$DIR/series.conf.new"; fi
  mv "$DIR/series.conf.new" "$DIR/series.conf"
  log "setup done: $(grep -E '^(commit|binary_md5)=' "$DIR/series.conf" | tr '\n' ' ')"
}

common_env() {
  eval "$(opam env --switch=baguette)"
  export SOLVERS="baguette" GCS=/scratch/arthur/gcs/build/fzn-glasgow
}

phase_flatten() {
  # All editions at once, PAR_FLAT / 16 instances each: one slow instance (a flatten has a 1 200 s
  # limit) holds up only its own edition and not the fifteen others.
  common_env
  cd "$SRC" || exit 1
  mkdir -p "$DIR/flat"
  local per=$(( PAR_FLAT / 16 )) pids=() y
  [ "$per" -ge 1 ] || per=1
  for y in $YEARS; do
    [ -e "$DIR/flat/$y.done" ] && continue
    (
      log "flatten $y start"
      PAR=$per TOTAL_MAX=$per SOLVE_TIMEOUT=60 FLATTEN_TIMEOUT=1200 CHECK_TIMEOUT=60 \
        MEM_KB=16777216 BAGUETTE="$DIR/bin/flatten-only.sh" INSTANCES="bench/challenge/$y.lst" \
        scripts/compare_run.sh /scratch/arthur/mznc "$DIR/flat/$y" > "$DIR/flat/$y.log" 2>&1
      touch "$DIR/flat/$y.done"
      log "flatten $y end"
    ) &
    pids+=($!)
    echo $! >> "$DIR/flat.pids"
  done
  for p in "${pids[@]}"; do wait "$p"; done
  touch "$DIR/flat/DONE"
}

arm_driver() {
  local l="$1" A="$DIR/$1" y
  mkdir -p "$A"; echo $BASHPID > "$DIR/$l.pid"
  common_env
  cd "$SRC" || exit 1
  export PAR TOTAL_MAX=$PAR SOLVE_TIMEOUT=1200 FLATTEN_TIMEOUT=1200 MEM_KB=16777216 \
    BAGUETTE="$DIR/bin/baguette-$l.sh" \
    VERIPB="$DIR/bin/veripb_wrap.sh" SERIES_VERIPB_REAL="$HOME/.cargo/bin/veripb" \
    SERIES_CHECK_LIMIT=3600 SERIES_CHECK_MEMMAX=64G SERIES_SEM_DIR="$DIR/sem" SERIES_BIG_SLOTS=12 \
    CHECK_TIMEOUT=28800 CHECK_MEM_KB=unlimited
  for y in $YEARS; do
    if grep -q '^DONE-' "$A/$y/results.tsv" 2> /dev/null; then continue; fi
    if [ ! -e "$A/$y/pair.tsv" ]; then
      mkdir -p "$A/$y/work" "$A/$y/log"
      cp "$DIR/flat/$y/pair.tsv" "$DIR/flat/$y/flatten.tsv" "$A/$y/"
      cp "$DIR/flat/$y/log/"*.pair "$A/$y/log/" 2> /dev/null
      awk -F'\t' '$3 == "FLATTEN-FAIL" || $3 == "NO-DATA" || $3 == "INPUT-INVALID"' \
        "$DIR/flat/$y/results.tsv" > "$A/$y/results.tsv"
      for f in "$DIR/flat/$y/work/"*.baguette.fzn; do [ -e "$f" ] && ln -f "$f" "$A/$y/work/"; done
    fi
    log "arm $l $y start"
    INSTANCES="bench/challenge/$y.lst" scripts/compare_run.sh /scratch/arthur/mznc "$A/$y" > "$A/$y.log" 2>&1
    log "arm $l $y end rc=$?"
  done
  touch "$A/DONE"
}

monitor() {
  # Every 5 minutes: load, the processes of this series (solver and checker), and free space. Never kills.
  echo $BASHPID > "$DIR/monitor.pid"
  while [ ! -e "$DIR/ALLDONE" ]; do
    n=$(ps -u arthur -o comm= | grep -cE '^(main.exe|veripb)$')
    echo "$(date -Is) load=$(cut -d' ' -f1-3 /proc/loadavg) running_main_or_veripb=$n memfree_gb=$(awk '/MemAvailable/{printf "%d", $2/1048576}' /proc/meminfo) scratch_free_gb=$(df -BG --output=avail /scratch | tail -1 | tr -dc 0-9)" >> "$DIR/monitor.log"
    sleep 300
  done
}

phase_run() {
  rm -f "$DIR/ALLDONE"
  monitor &
  local pids=() a
  for a in "${ARMS[@]}"; do
    arm_driver "$(arm_field "$a" 1)" > "$DIR/log/arm-$(arm_field "$a" 1).log" 2>&1 &
    pids+=($!)
  done
  log "run started: $NARMS arms x PAR $PAR"
  for p in "${pids[@]}"; do wait "$p"; done
  touch "$DIR/ALLDONE"
  grep -q '^ended=' "$DIR/series.conf" || echo "ended=$(date -Is)" >> "$DIR/series.conf"
  log "run finished"
}

phase_read() { common_env; "$SRC/bench/series/read_series.sh" "$DIR" "$SRC"; }

phase_publish() {
  mkdir -p "$RESULTS"
  cp -r "$DIR/tables/." "$RESULTS/"
  cp "$DIR/series.conf" "$DIR/monitor.log" "$RESULTS/" 2> /dev/null
  cp "$SRC/bench/series/"*.sh "$SRC/bench/series/rss_wrap.py" "$RESULTS/" 2> /dev/null
  cp "$DIR/log/driver.log" "$RESULTS/"
  log "published to $RESULTS"
}

echo $$ > "$DIR/pid"
case "$PHASE" in
  all) phase_setup; phase_flatten; phase_run; phase_read; phase_publish ;;
  setup) phase_setup ;;
  flatten) phase_flatten ;;
  run) phase_run ;;
  read) phase_read ;;
  publish) phase_publish ;;
  *) echo "unknown phase $PHASE" >&2; exit 2 ;;
esac
