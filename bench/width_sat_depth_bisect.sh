#!/usr/bin/env bash
# M6-T6. Re-runnable measurement for the width_sat_depth regression bisect.
#
# width_sat_depth.fzn's own header comment claims "at 99 it is 43 ms end to end"
# (commit 83cc658, M1-T30). Measured on main at 2026-09-21: 160 ms shipped
# (BAGUETTE_PROPAGATE_LEARNED=on, the default) and 590 ms with it off. This script
# times the CURRENT checkout's bin/main.exe against that model, best-of-N wall clock,
# with and without the flag where it exists. It does not check out other commits --
# see bench/README.md's M6-T6 section for the bisect result and how it was produced
# (git bisect run against a wall-clock threshold, by hand, in a worktree).
#
# MEASUREMENT ONLY, NEVER A COMMIT GATE (bench/README.md).
set -euo pipefail

N="${1:-5}"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="$ROOT/_build/default/bin/main.exe"
MODEL="$ROOT/test/models/width_sat_depth.fzn"
OUT="$(mktemp -d)/wsd"

if [ ! -x "$BIN" ]; then
  echo "FAIL: $BIN not built. Run: dune build --root . bin/" >&2
  exit 1
fi

best_of_n() {
  local env_prefix="$1"
  local best="999999"
  for i in $(seq 1 "$N"); do
    local t0 t1 d
    t0=$(date +%s.%N)
    (ulimit -v 4000000; timeout 30 env $env_prefix "$BIN" "$MODEL" --proof "$OUT" >/dev/null)
    t1=$(date +%s.%N)
    d=$(awk -v a="$t1" -v b="$t0" 'BEGIN{printf "%.4f", a-b}')
    echo "  run $i: ${d}s" >&2
    best=$(awk -v a="$d" -v b="$best" 'BEGIN{print (a<b)?a:b}')
  done
  echo "$best"
}

echo "width_sat_depth.fzn, best of $N, wall clock (solve + proof write, no veripb):" >&2
echo "learned propagation ON (default):" >&2
on=$(best_of_n "")
echo "learned propagation OFF (BAGUETTE_PROPAGATE_LEARNED=off):" >&2
off=$(best_of_n "BAGUETTE_PROPAGATE_LEARNED=off")

echo
echo "on=${on}s  off=${off}s"
