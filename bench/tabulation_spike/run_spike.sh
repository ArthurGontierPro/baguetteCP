#!/usr/bin/env bash
# M4-T6 spike (D-0184): tabulation proofs vs the solver's own (D-0060) on the spike models,
# and the mutation controls, each asserted at the checker's full wording.
#
#   bench/tabulation_spike/run_spike.sh OUTDIR
#
# Needs bin/main.exe built (dune build --root . bin/) and veripb 3.0.2 (scripts/checker.sh).
# Every process runs under a 4 GB address-space cap and a timeout; the caller wraps the whole
# script in `systemd-run --user --scope -p MemoryMax=...` on the node. Exit 1 on any
# unexpected verdict.
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
out=${1:?usage: run_spike.sh OUTDIR}
mkdir -p "$out"
echo $$ >"$out/pid"
bin="$root/_build/default/bin/main.exe"
# shellcheck source=/dev/null
. "$root/scripts/checker.sh"
baguette_resolve_veripb || { baguette_veripb_diagnostic; echo "FAIL no checker"; exit 1; }
veripb=$VERIPB
[ -x "$bin" ] || { echo "FAIL $bin not built"; exit 1; }
ulimit -v 4000000

RUP="The constraint is not implied by reverse unit propagation (RUP) from core and derived database."
RED="Proofgoal #1 could not be autoproven. Please add an explicit subproof for proofgoal #1."
fail=0
cd "$out"

check() { # opb pbp -> "verdict seconds peakKB"
  local log="$2.log"
  /usr/bin/time -f '%e %M' -o "$2.time" timeout 300 "$veripb" "$1" "$2" >"$log" 2>&1
  local v
  v=$(grep -o 's VERIFIED [A-Z]*\|Checking error' "$log" | head -1 | sed 's/^s VERIFIED /VERIFIED_/; s/ /_/g')
  echo "${v:-ERROR} $(tail -1 "$2.time")"
}

printf '%-24s %-6s %6s %6s %8s %7s %7s | %6s %6s %8s %7s %s\n' model answer \
  b.node b.line b.bytes b.chk_s b.kB t.node t.line t.bytes t.chk_s "t.verdict"
for fzn in "$here"/models/*.fzn; do
  m=$(basename "$fzn" .fzn)
  timeout 60 "$bin" "$fzn" --proof "$m.base" --stats >"$m.base.out" 2>"$m.base.err"
  bnodes=$(awk '/^stats: nodes /{print $3}' "$m.base.err")
  read -r bv bt bk < <(check "$m.base.opb" "$m.base.pbp")
  tinfo=$(python3 -I "$here/tabulate.py" "$fzn" "$m.base.opb" "$m.tab.pbp")
  echo "$tinfo" >"$m.tab.info"
  tnodes=$(echo "$tinfo" | sed 's/.*nodes=\([0-9]*\).*/\1/')
  read -r tv tt tk < <(check "$m.base.opb" "$m.tab.pbp")
  printf '%-24s %-6s %6s %6s %8s %7s %7s | %6s %6s %8s %7s %s\n' "$m" \
    "$(head -1 "$m.base.out" | cut -c1-6)" "$bnodes" "$(wc -l <"$m.base.pbp")" \
    "$(wc -c <"$m.base.pbp")" "$bt" "$bk" "$tnodes" "$(wc -l <"$m.tab.pbp")" \
    "$(wc -c <"$m.tab.pbp")" "$tt" "$tv"
  [ "$bv" = "$tv" ] || { echo "FAIL $m: base says '$bv', tabulation says '$tv'"; fail=1; }
  echo "  $m tabulation: $tinfo"
done

# Mutations, on the SATISFIABLE models only (D-0053: a refusal over a contradictory
# database proves nothing, and an acceptance there proves nothing either).
expect() { # model mutation wording|ACCEPT [regex the refused LINE must match]
  local m=$1 mu=$2 want=$3 shape=${4:-}
  python3 -I "$here/tabulate.py" "$here/models/$m.fzn" "$m.base.opb" "$m.$mu.pbp" --mutate "$mu" >/dev/null
  timeout 300 "$veripb" "$m.base.opb" "$m.$mu.pbp" >"$m.$mu.log" 2>&1
  if [ "$want" = ACCEPT ]; then
    if grep -q '^s VERIFIED' "$m.$mu.log"; then echo "ok   $m $mu: accepted (as expected)"
    else echo "FAIL $m $mu: expected acceptance"; fail=1; fi
    return
  fi
  local at line
  at=$(grep -o "Checking error at [^ ]*:[0-9]*" "$m.$mu.log" | head -1 | sed 's/.*://')
  line=$(sed -n "${at:-0}p" "$m.$mu.pbp")
  if ! grep -qF "$want" "$m.$mu.log"; then
    echo "FAIL $m $mu: expected \"$want\", got: $(grep -v '^Running' "$m.$mu.log" | head -3 | tr '\n' ' ')"
    fail=1
  elif [ -n "$shape" ] && ! echo "$line" | grep -qE "$shape"; then
    echo "FAIL $m $mu: refused, but at the wrong line $at: $line"
    fail=1
  else
    echo "ok   $m $mu: refused at line $at ($(echo "$line" | cut -c1-60)...) -- \"$want\""
  fi
}
SEL='tab_s_[0-9m]+_[0-9m]+'
for m in tab_times_sat tab_times_holes_sat; do
  # the corrupted tuple's CAB: x, y literals and one selector
  expect $m wrong-def "$RUP" "^@t[0-9]+ rup [^t]*\+1 $SEL >= 1 ;\$"
  expect $m flip-witness "$RED" "^@t[0-9]+ red .* : $SEL -> 0 ;\$"
  # the claimed removal: a clause over order literals only, after the tabulation
  expect $m unsupported "$RUP" "^@t[0-9]+ rup [^t]*>= 1 ;\$"
  # ALO: selectors only
  expect $m alo-direct "$RUP" "^@t[0-9]+ rup (\+1 $SEL )+>= 1 ;\$"
  expect $m cab-no-zlemma "$RUP" "^@t[0-9]+ rup [^t]*\+1 $SEL >= 1 ;\$"
done
# no-kill: needed exactly where a value has two or more hole-killed supports the model's
# rows cannot split on -- z = 2 in tab_times_holes_sat.
expect tab_times_holes_sat no-kill "$RUP" '^@t[0-9]+ rup \+1 ~z_ge_2 \+1 z_ge_3 >= 1 ;$'
expect tab_times_sat no-kill ACCEPT
exit $fail
