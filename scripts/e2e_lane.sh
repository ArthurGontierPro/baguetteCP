#!/usr/bin/env bash
# The END-TO-END lane (M14-e2e-verification-T2, D-0176): baguette's answers on the covered
# test models certified by CakeML's verified CP encoder and verified PB checker (D-0174).
#
# Three passes, each one line per item and a summary; the lane FAILS if any line does:
#
#   1. chain       every test/models/*.fzn through tools/e2e/chain.sh: fzn2scp.py ->
#                  cake_pb_cp (encode) -> baguette --proof (order arm, default flags) ->
#                  bridge.py -> veripb --elaborate -> cake_pb_cp (check). VERIFIED needs
#                  cake_pb_cp's own `s VERIFIED SATISFIABLE|UNSATISFIABLE`, agreeing with
#                  baguette's answer. A model outside the translator's subset is SKIPPED with
#                  its first uncovered construct; any other outcome is FAIL.
#   2. controls    deliberate corruptions that the chain MUST refuse, each asserted at the
#                  refused line AND in the checker's own sentence (CLAUDE.md: a lane that
#                  asserts a rejection asserts the wording, at full strength):
#                    opb-stronger   baguette's .opb row says more than the model: refused at
#                                   THAT row's pin, "not implied by reverse unit propagation"
#                    scp-weaker     the .scp says less than baguette's row: refused at a pin
#                    scp-stronger   the .scp says more, baguette's `sol` breaks it: refused at
#                                   `sol`, conflicting with the mutated constraint's own row
#                    opb-reif       (T4, D-0178) baguette's reified big-M row with its
#                                   reifier's literal flipped, a wrong reification: refused
#                                   at THAT row's pin, as opb-stronger
#                  opb-stronger also runs on the Boolean family and int_lin_le_reif (T4).
#                    bridge-witness an atom definition with a wrong witness: refused at it,
#                                   "Proofgoal #1 could not be autoproven" (satisfiable models,
#                                   so the `red` is judged, D-0053)
#   3. validation  the TRUSTED translator against MiniZinc's reference solvers (D-0174 sec. 6,
#                  GCS #987): on every model of pass 1 that is not SKIPPED, the solution set
#                  cake's semantics admit for the .scp (tools/e2e/scpsem.py, which reads only
#                  the .scp) must equal the one Gecode (and CP-SAT) enumerate from the .fzn,
#                  over every variable, and baguette's printed solution must be one of them.
#                  A model too large to enumerate is UNCHECKED, and counted as such.
#
# Usage: scripts/e2e_lane.sh [-j N] [OUTDIR]       (N <= 8; OUTDIR default /tmp/baguette-e2e-$$)
# Env:   CAKE_PB_CP  the verified encoder/checker (default: the build of D-0174, see below);
#                    missing is a FAILURE, never a skip
#        BAGUETTE    the solver (default _build/default/bin/main.exe; build it first, the lane
#                    does not, and prints its md5)
#        MZN_BIN     the MiniZinc bundle's bin/ holding fzn-gecode and fzn-cp-sat
#
# cake_pb_cp: gitlab.com/MIAOresearch/software/cakepb, cp/, commit 438b8f83, built with
# `gcc basis_ffi.c cp/cake_pb_cp.S -o cake_pb_cp` (sha256 ca92491e...). It exits 0 when it
# refuses, so every verdict here is read from its `s VERIFIED` line.
#
# Each run goes under `systemd-run --user --scope -p MemoryMax=32G` when systemd-run exists
# (the shared node), with a timeout, and writes its PID next to its output (OUTDIR/*.pid,
# removed when it finishes); the lane writes its own to OUTDIR/lane.pid.
set -u
ROOT=$(cd "$(dirname "$0")/.." && pwd)
J=8
while [ $# -gt 0 ]; do
    case "$1" in
        -j) J=$2; shift 2 ;;
        -j*) J=${1#-j}; shift ;;
        *) break ;;
    esac
done
[ "$J" -le 8 ] || { echo "e2e_lane: -j $J: at most 8 in parallel"; exit 2; }
OUT=${1:-/tmp/baguette-e2e-$$}
mkdir -p "$OUT/chain" "$OUT/controls" "$OUT/validate"
echo $$ > "$OUT/lane.pid"
trap 'rm -f "$OUT/lane.pid"' EXIT

export CAKE_PB_CP=${CAKE_PB_CP:-/cluster/arthur/baguette-results/wave55-e2e/cake_pb_cp-438b8f83}
export BAGUETTE=${BAGUETTE:-$ROOT/_build/default/bin/main.exe}
MZN_BIN=${MZN_BIN:-/scratch/arthur/mzn/MiniZincIDE-2.10.1-x86_64-linux-gnu/bin}
export E2E_TIMEOUT=${E2E_TIMEOUT:-300}
for f in "$CAKE_PB_CP" "$BAGUETTE" "$MZN_BIN/fzn-gecode" "$MZN_BIN/fzn-cp-sat"; do
    [ -x "$f" ] || { echo "FAIL e2e_lane: $f is missing or not executable"; exit 1; }
done
echo "e2e_lane: baguette md5 $(md5sum < "$BAGUETTE" | cut -c1-8), cake_pb_cp sha256 $(sha256sum < "$CAKE_PB_CP" | cut -c1-8), out $OUT"

if command -v systemd-run > /dev/null 2>&1; then
    RUN=(systemd-run --user --scope -q -p MemoryMax=32G)
else
    RUN=()
fi
export RUNPFX="${RUN[*]}"
run() { $RUNPFX timeout "$((E2E_TIMEOUT * 4))" "$@"; }
export -f run

fail=0

# ---------------------------------------------------------------- 1. chain
ls "$ROOT"/test/models/*.fzn | xargs -P "$J" -I{} bash -c 'run "$0"/tools/e2e/chain.sh {} "$1"' "$ROOT" "$OUT/chain" \
    | sort > "$OUT/chain.txt"
cat "$OUT/chain.txt" | sed -E 's/ veripb=.*//'
nv=$(grep -c ' VERIFIED ' "$OUT/chain.txt")
nvs=$(grep -c ' VERIFIED SAT ' "$OUT/chain.txt")
nvu=$(grep -c ' VERIFIED UNSAT ' "$OUT/chain.txt")
ns=$(grep -c ' SKIPPED ' "$OUT/chain.txt")
nf=$(grep -vc -E ' (VERIFIED|SKIPPED) ' "$OUT/chain.txt")
nm=$(ls "$ROOT"/test/models/*.fzn | wc -l)
nl=$(wc -l < "$OUT/chain.txt")
echo "chain: $nm models, $nv VERIFIED ($nvs SAT, $nvu UNSAT), $ns SKIPPED, $nf FAIL"
[ "$nf" -eq 0 ] && [ "$nl" -eq "$nm" ] || fail=1
[ "$nv" -gt 0 ] || { echo "FAIL chain: NOT ONE model was verified. This is not a pass."; fail=1; }

# ---------------------------------------------------------------- 2. controls
RUP="The constraint is not implied by reverse unit propagation (RUP) from core and derived database."
SOL="Propagation engine error: The given solution is conflicting with constraint"
RED="Proofgoal #1 could not be autoproven."
CONTROLS="chain_sat:opb-stronger php_unsat:opb-stronger chain_sat:scp-weaker php_unsat:scp-weaker
search_all_const_sat:scp-stronger bits_pb_learn_sat:scp-stronger chain_sat:bridge-witness lin_sat:bridge-witness
bool_or_sat:opb-stronger bool_and_sat:opb-stronger reif_lin_le_sat:opb-stronger
reif_eq_refute_sat:opb-reif reif_le_refute_sat:opb-reif bits_reif_sat:opb-reif"
NCONTROLS=14
for c in $CONTROLS; do echo "$c"; done | xargs -P "$J" -I{} bash -c \
    'm=${0%%:*}; k=${0#*:}; run "$1"/tools/e2e/chain.sh "$1/test/models/$m.fzn" "$2" "$k"' {} "$ROOT" "$OUT/controls" \
    | sort > "$OUT/controls.txt"
nc=0
ncok=0
while IFS= read -r l; do
    nc=$((nc + 1))
    k=${l%% *}
    k=${k#*.}
    at=$(echo "$l" | sed -n 's/.*| at=\([^|]*\) | cause=.*/\1/p')
    cause=$(echo "$l" | sed -n 's/.*| cause=\(.*\) | target=.*/\1/p')
    target=$(echo "$l" | sed -n 's/.*| target=\(.*\)$/\1/p')
    ok=0
    case "$k" in
        opb-stronger | opb-reif) [ "$at" = "$target rup" ] && [ "$cause" = "$RUP" ] && ok=1 ;;
        scp-weaker) [[ "$at" =~ ^@c[0-9]+\ rup$ ]] && [ "$cause" = "$RUP" ] && ok=1 ;;
        scp-stronger) [[ "$at" == "sol "* ]] && [[ "$cause" =~ ^"$SOL"\ [0-9]+\ in\ the\ database\.\ \(@S\[c\[$target\]\]\)$ ]] && ok=1 ;;
        bridge-witness) [ "$at" = "$target red" ] && [ "$cause" = "$RED" ] && ok=1 ;;
    esac
    if [[ "$l" == *" REFUSED "* ]] && [ $ok -eq 1 ]; then
        echo "PASS  $l"
        ncok=$((ncok + 1))
    else
        echo "FAIL  $l"
    fi
done < "$OUT/controls.txt"
echo "controls: $ncok of $nc refused where and as expected ($NCONTROLS expected)"
[ "$nc" -eq "$NCONTROLS" ] && [ "$ncok" -eq "$NCONTROLS" ] || fail=1

# ---------------------------------------------------------------- 3. validation
# shellcheck disable=SC2016
grep -v ' SKIPPED ' "$OUT/chain.txt" | awk '{print $1}' | xargs -P "$J" -I{} bash -c '
    m=$0; c="$2/$m"; v="$3/$m"
    run python3 -I "$1/tools/e2e/scpsem.py" "$c.scp" "$c.names" > "$v.scpsem" 2>&1
    run python3 -I "$1/tools/e2e/fzn_solutions.py" "$4/fzn-gecode" "$1/test/models/$m.fzn" "$c.names" "$v.g" 120 > "$v.gecode.ref" 2>&1
    run python3 -I "$1/tools/e2e/fzn_solutions.py" "$4/fzn-cp-sat" "$1/test/models/$m.fzn" "$c.names" "$v.s" 120 > "$v.cpsat.ref" 2>&1
    echo "$m $(python3 -I "$1/tools/e2e/validate.py" "$v.scpsem" "$c.names" "$c.bag.out" "$v.gecode.ref" "$v.cpsat.ref")"
' {} "$ROOT" "$OUT/chain" "$OUT/validate" "$MZN_BIN" | sort > "$OUT/validate.txt"
cat "$OUT/validate.txt"
na=$(grep -c ' AGREE ' "$OUT/validate.txt")
nu=$(grep -c ' UNCHECKED ' "$OUT/validate.txt")
nd=$(grep -vc -E ' (AGREE|UNCHECKED) ' "$OUT/validate.txt")
echo "validation: $na AGREE, $nu UNCHECKED, $nd DIFFER"
[ "$nd" -eq 0 ] && [ "$na" -gt 0 ] || fail=1

[ $fail -eq 0 ] && echo "e2e_lane: PASS" || echo "e2e_lane: FAIL"
exit $fail
