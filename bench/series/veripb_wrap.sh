#!/bin/bash
# M17-bench-series-T1 (D-0203). veripb under ITS OWN limits, so a checker memory failure is counted
# apart and is not a CHECK-ERROR from the solver's cap:
#   * its own cgroup, `systemd-run --user --scope -p MemoryMax=$SERIES_CHECK_MEMMAX` (default 64G),
#     and no address-space cap (the series driver sets CHECK_MEM_KB=unlimited for the harness);
#   * its own time limit $SERIES_CHECK_LIMIT seconds of CHECKING (default 3600). The harness's own
#     `timeout` is set far above it (it also covers the wait for a slot below), so it is a net
#     and not the limit;
#   * a proof of 2 GiB or more waits for one of $SERIES_BIG_SLOTS (default 12) slots, so that
#     at most 12 large checks (12 x 64 GB) are in memory at once on the shared node.
# Verdicts, as compare.py's `verdict` reads them: exit 124 = TIMEOUT-CHECK (the limit above);
# exit 97 and a first line "Error: SERIES-CHECKER-MEMORY ..." = CHECK-ERROR that tools/compare/
# readme_table.py counts as a checker MEMORY failure (SIGKILL by the cgroup before the limit, or
# an allocation abort); anything else is veripb's own exit status and output, unchanged.
REAL="${SERIES_VERIPB_REAL:-$HOME/.cargo/bin/veripb}"
case "${1:-}" in --version | -V | --help | -h | "") exec "$REAL" "$@" ;; esac
LIMIT="${SERIES_CHECK_LIMIT:-3600}"
MEMMAX="${SERIES_CHECK_MEMMAX:-64G}"
SEM="${SERIES_SEM_DIR:-/tmp}"
size=0
for f in "$@"; do [ -f "$f" ] && size=$((size + $(stat -c%s "$f"))); done
if [ "$size" -ge 2147483648 ] && [ -d "$SEM" ]; then
  while :; do
    for i in $(seq 1 "${SERIES_BIG_SLOTS:-12}"); do
      exec {fd}> "$SEM/slot$i"
      flock -n "$fd" && break 2
      exec {fd}>&-
    done
    sleep 5
  done
fi
out="$(mktemp "${TMPDIR:-/tmp}/vpw.XXXXXX")"
start=$SECONDS
timeout -k 30 "$LIMIT" systemd-run --user --scope -q -p MemoryMax="$MEMMAX" -p MemorySwapMax=0 \
  "$REAL" "$@" > "$out" 2>&1 &
child=$!
trap 'kill -TERM "$child" 2>/dev/null; wait "$child" 2>/dev/null; cat "$out"; rm -f "$out"; exit 124' TERM INT
wait "$child"
rc=$?
trap - TERM INT
el=$((SECONDS - start))
if [ "$rc" -eq 124 ] || { [ "$rc" -eq 137 ] && [ "$el" -ge "$LIMIT" ]; }; then
  cat "$out"; rm -f "$out"; exit 124
fi
if [ "$rc" -eq 137 ] || { [ "$rc" -eq 134 ] && grep -q 'memory allocation' "$out"; }; then
  echo "Error: SERIES-CHECKER-MEMORY veripb died with status $rc after ${el}s (MemoryMax=$MEMMAX)"
  cat "$out"; rm -f "$out"; exit 97
fi
cat "$out"; rm -f "$out"
exit "$rc"
