#!/bin/bash
# M17-bench-series-T1 (D-0203). Holds a launch while /scratch has under $SERIES_MIN_FREE_GB GB free
# (the user's floor, 2 000, on 2026-11-23: with no proof cap a proof can be hundreds of GB). Run by
# compare_run.sh as PRE_RUN before each solve and each check, outside their timeouts. Never kills.
while [ "$(df -BG --output=avail /scratch | tail -1 | tr -dc 0-9)" -lt "${SERIES_MIN_FREE_GB:-2000}" ]; do
  sleep 60
done
