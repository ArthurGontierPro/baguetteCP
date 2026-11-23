#!/bin/bash
# M17-bench-series-T1 (D-0203). The solver as the harness's BAGUETTE=, one per arm. Environment,
# set by the arm's generated shim (run_series.sh): SERIES_BIN (main.exe), SERIES_FLAGS (the arm's
# flags), SERIES_PROOF (1 = keep the harness's `--proof PREFIX`, 0 = drop it and pass --no-proof),
# SERIES_RSS_WRAP (rss_wrap.py). The solver runs in its own `systemd-run --user --scope -p
# MemoryMax=32G` under the RSS recorder, which writes `rss_kb=N` to PREFIX.rss. `--stats` is on
# so the node count is on stderr. The address-space cap (16 GiB) and the proof cap are the
# harness's, applied in its solver subshell.
L=""; prev=""; args=()
for a in "$@"; do
  [ "$prev" = --proof ] && L="$a"
  if [ "$SERIES_PROOF" = 0 ]; then
    if [ "$a" = --proof ]; then prev="$a"; continue; fi
    if [ "$prev" = --proof ]; then prev="$a"; continue; fi
  fi
  args+=("$a"); prev="$a"
done
extra=()
[ "$SERIES_PROOF" = 0 ] && extra=(--no-proof)
# shellcheck disable=SC2086
exec systemd-run --user --scope -q -p MemoryMax=32G /usr/bin/python3 -I "$SERIES_RSS_WRAP" \
  "${L:-/dev/null}.rss" "$SERIES_BIN" --stats "${extra[@]}" $SERIES_FLAGS "${args[@]}"
