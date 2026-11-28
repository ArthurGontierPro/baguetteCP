#!/usr/bin/env bash
# M18-coverage-T9 (D-0265): the population of "the refused third" from the series of
# 2026-11-26 (D-0227). Every instance REFUSED (heap budget) in arm B or arm D, plus every
# instance that TIMED OUT with no solution in B or D without passing NODE_MAX nodes
# (default 1000), which is a refusal in effect.
#
# Output (stdout), tab-separated:
#   id  why  B_status  B_nodes  B_rss_kb  D_status  D_nodes  D_rss_kb  A_status  C_status
# why is "refused" or "stuck" (timeout, no solution, at most NODE_MAX nodes in B or D).
#
# usage: bench/refused/population.sh [SERIES_DIR] > population.tsv
set -euo pipefail
S="${1:-/cluster/arthur/baguette-results/series-20261126}"
NODE_MAX="${NODE_MAX:-1000}"
awk -F'\t' -v nmax="$NODE_MAX" '
  FILENAME ~ /results_[ABCD]\.tsv$/ {
    arm = substr(FILENAME, length(FILENAME) - 4, 1); st[$1, arm] = $3; next
  }
  FNR > 1 && $1 == "A" {
    id = $3; y = $2
    stat[id, y] = $6; nodes[id, y] = $12; rss[id, y] = $14; obj[id, y] = $8
    stat[id, "A"] = $5; ids[id] = 1
  }
  END {
    for (id in ids) {
      why = ""
      if (st[id, "B"] == "REFUSED" || st[id, "D"] == "REFUSED") why = "refused"
      else {
        for (k = 1; k <= 2; k++) {
          y = (k == 1 ? "B" : "D")
          if (stat[id, y] == "TIMEOUT" && obj[id, y] ~ /-$/ && nodes[id, y] + 0 <= nmax) why = "stuck"
        }
      }
      if (why == "") continue
      printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n", id, why, st[id, "B"], nodes[id, "B"], rss[id, "B"], \
        st[id, "D"], nodes[id, "D"], rss[id, "D"], st[id, "A"], st[id, "C"]
    }
  }' "$S"/results_A.tsv "$S"/results_B.tsv "$S"/results_C.tsv "$S"/results_D.tsv "$S"/pairs.tsv | sort
