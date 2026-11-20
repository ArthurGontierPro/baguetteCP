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
#                    copy-witness   (T5, D-0180) a WRONG DEFINITION of an auxiliary baguette
#                                   introduces, a global_cardinality copy defined as the NEGATION
#                                   of its original: refused at that `@Y1` red line, as
#                                   bridge-witness. Its model, tools/e2e/models/gcc_repeat_free_sat,
#                                   leaves the original free (in test/models/gcc_repeat_sat it is
#                                   fixed at the root, so the wrong definition is true there)
#                  T5 adds opb-stronger on element, global_cardinality, array_int_maximum and
#                  inverse, and opb-reif on member, whose selector guard flipped is a wrong
#                  definition of the selectors mznlib introduces. Every control's model is
#                  satisfiable and has a solution the corrupted claim excludes (D-0180).
#                    opt-better     (T8, D-0182) a WRONG CLAIMED OPTIMUM: baguette's `conclusion
#                    opt-worse      BOUNDS` one better (one worse) than the optimum it found:
#                                   refused by veripb at that line, on the upper (lower) bound
#                    core-better    the same corruption in the ELABORATED core, after veripb
#                    core-worse     accepted: refused by cake_pb_cp itself at its conclusion
#                                   ("conclusion BOUNDS check failed: ..."), so the verified
#                                   checker refuses a wrong optimum whatever the elaborator did
#   1b. solver     (M14-e2e-verification-T3, D-0187) every model again through chain.sh with
#                  E2E_SOLVER=1: baguette --e2e writes the prefix itself and its .pbp is checked
#                  against cake's .opb with no bridge. A model --e2e does not cover is SKIPPED
#                  with baguette's reason; every model it VERIFIES must be VERIFIED by pass 1
#                  too, with the same answer, and every model pass 1 VERIFIES must be VERIFIED
#                  here or SKIPPED with an `e2e:` reason. FAIL otherwise.
#   2b. solver controls  the corruptions of the solver-written path, asserted as in pass 2:
#                    pin-stronger   the prefix's pin of baguette's first model row with three
#                                   terms or more states it with degree + 1: refused at THAT
#                                   pin ("Expected constraint is not syntactically implied by
#                                   the constraint at the hint." for an `ia`, the RUP sentence
#                                   for a `rup`)
#                    sel-witness    a WRONG DEFINITION of a disequality selector (`@D1`'s
#                                   witness s -> ~F): refused at that red line, "Proofgoal #1
#                                   could not be autoproven." (models where the flag is free)
#                  plus scp-weaker, scp-stronger, bridge-witness (the atom definition), and the
#                  wrong optimum (opt-*, core-*) on the solver's own proof. T3b (D-0188) adds
#                  pin-stronger on T5's globals, where the first such row is the family's:
#                  element (2), global_cardinality (2), array_int_maximum and int_max,
#                  inverse, member (2); each corrupted row is false in at least one of the
#                  model's solutions (enumerated by scpsem.py, D-0188 section 6).
#   3. validation  the TRUSTED translator against MiniZinc's reference solvers (D-0174 sec. 6,
#                  GCS #987): on every model of pass 1 that is not SKIPPED, the solution set
#                  cake's semantics admit for the .scp (tools/e2e/scpsem.py, which reads only
#                  the .scp) must equal the one Gecode (and CP-SAT) enumerate from the .fzn,
#                  over every variable, and baguette's printed solution must be one of them.
#                  A model too large to enumerate is UNCHECKED, and counted as such. With an
#                  objective (T8) the references enumerate it as `solve satisfy`, and the
#                  .scp's prob_type must name the .fzn's direction and variable, and
#                  baguette's last solution must reach the set's optimum under it.
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
nvo=$(grep -c ' VERIFIED OPT=' "$OUT/chain.txt")
ns=$(grep -c ' SKIPPED ' "$OUT/chain.txt")
nf=$(grep -vc -E ' (VERIFIED|SKIPPED) ' "$OUT/chain.txt")
nm=$(ls "$ROOT"/test/models/*.fzn | wc -l)
nl=$(wc -l < "$OUT/chain.txt")
echo "chain: $nm models, $nv VERIFIED ($nvs SAT, $nvu UNSAT, $nvo OPT), $ns SKIPPED, $nf FAIL"
[ "$nf" -eq 0 ] && [ "$nl" -eq "$nm" ] || fail=1
[ "$nv" -gt 0 ] || { echo "FAIL chain: NOT ONE model was verified. This is not a pass."; fail=1; }

# ---------------------------------------------------------------- 1b. solver (T3, D-0187)
mkdir -p "$OUT/solver"
ls "$ROOT"/test/models/*.fzn | E2E_SOLVER=1 xargs -P "$J" -I{} bash -c 'run "$0"/tools/e2e/chain.sh {} "$1"' "$ROOT" "$OUT/solver" \
    | sort > "$OUT/solver.txt"
sv=$(grep -c ' VERIFIED ' "$OUT/solver.txt")
ss=$(grep -c ' SKIPPED e2e: ' "$OUT/solver.txt")
st=$(grep -c ' SKIPPED ' "$OUT/solver.txt")
sf=$(grep -vc -E ' (VERIFIED|SKIPPED) ' "$OUT/solver.txt")
# the two passes agree: a model VERIFIED on one path is VERIFIED on the other with the same
# answer, unless --e2e does not cover it (SKIPPED e2e: ...)
sd=$(join <(awk '{print $1, $2, $3}' "$OUT/chain.txt") <(awk '{print $1, $2, $3, $4}' "$OUT/solver.txt") |
    awk '($2 == "VERIFIED" && !($4 == "VERIFIED" && $5 == $3) && !($4 == "SKIPPED" && $5 == "e2e:")) ||
         ($4 == "VERIFIED" && !($2 == "VERIFIED" && $3 == $5)) {print}')
[ -n "$sd" ] && echo "$sd" | sed 's/^/DISAGREE /'
nsd=$(echo -n "$sd" | grep -c .)
grep -v -E ' (VERIFIED|SKIPPED) ' "$OUT/solver.txt"
echo "solver: $nm models, $sv VERIFIED by cake_pb_cp with the prefix written by baguette --e2e, $ss outside --e2e's families, $((st - ss)) outside the translator's, $sf FAIL, $nsd disagreeing with the bridged pass"
[ "$sf" -eq 0 ] && [ "$nsd" -eq 0 ] && [ "$(wc -l < "$OUT/solver.txt")" -eq "$nm" ] || fail=1
[ "$sv" -gt 0 ] || { echo "FAIL solver: NOT ONE model was verified. This is not a pass."; fail=1; }

# ---------------------------------------------------------------- 2. controls
RUP="The constraint is not implied by reverse unit propagation (RUP) from core and derived database."
SOL="Propagation engine error: The given solution is conflicting with constraint"
RED="Proofgoal #1 could not be autoproven."
CONTROLS="chain_sat:opb-stronger php_unsat:opb-stronger chain_sat:scp-weaker php_unsat:scp-weaker
search_all_const_sat:scp-stronger bits_pb_learn_sat:scp-stronger chain_sat:bridge-witness lin_sat:bridge-witness
bool_or_sat:opb-stronger bool_and_sat:opb-stronger reif_lin_le_sat:opb-stronger
reif_eq_refute_sat:opb-reif reif_le_refute_sat:opb-reif bits_reif_sat:opb-reif
element_sat:opb-stronger element_learn_prunes_sat:opb-stronger gcc_forced_sat:opb-stronger
gcc_const_counts_sat:opb-stronger maxmin_sat:opb-stronger inverse_sat:opb-stronger
member_sat:opb-reif member_gap_sat:opb-reif gcc_repeat_free_sat:copy-witness
opt_min_sat:opt-better opt_max_sat:opt-better opt_min_sat:opt-worse restart_queens6_opt:opt-worse
opt_min_sat:core-better restart_queens6_opt:core-better opt_max_sat:core-worse bits_maxmin_opt_sat:core-worse"
NCONTROLS=31
OPTW="The lower bound claimed for \`conclusion BOUNDS\` is larger than the best logged objective value."
CORE="conclusion BOUNDS check failed:"
for c in $CONTROLS; do echo "$c"; done | xargs -P "$J" -I{} bash -c \
    'm=${0%%:*}; k=${0#*:}; f="$1/test/models/$m.fzn"; [ -f "$f" ] || f="$1/tools/e2e/models/$m.fzn"
     run "$1"/tools/e2e/chain.sh "$f" "$2" "$k"' {} "$ROOT" "$OUT/controls" \
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
        bridge-witness | copy-witness) [ "$at" = "$target red" ] && [ "$cause" = "$RED" ] && ok=1 ;;
        opt-better)
            ub=${target#* }
            [ "$at" = "conclusion BOUNDS" ] && [ "$cause" = "Unable to verify 'conclusion BOUNDS'. The claimed upper bound of $ub mismatches the best recorded upper bound of $((ub + 1))." ] && ok=1 ;;
        opt-worse) [ "$at" = "conclusion BOUNDS" ] && [ "$cause" = "$OPTW" ] && ok=1 ;;
        core-better) [ "$at" = "conclusion BOUNDS" ] && [ "$cause" = "$CORE [lb <= dbound] T [upper bound check] F [lower bound check] T" ] && ok=1 ;;
        core-worse) [ "$at" = "conclusion BOUNDS" ] && [ "$cause" = "$CORE [lb <= dbound] F [upper bound check] T [lower bound check] T" ] && ok=1 ;;
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

# ---------------------------------------------------------------- 2b. solver controls (T3)
IA="Expected constraint is not syntactically implied by the constraint at the hint."
SCONTROLS="chain_sat:pin-stronger php_unsat:pin-stronger bool_or_sat:pin-stronger bool_and_sat:pin-stronger
reif_lin_le_sat:pin-stronger alldiff_const_sat:sel-witness ne_sat:sel-witness reif_ne_entail_sat:sel-witness
chain_sat:scp-weaker php_unsat:scp-weaker search_all_const_sat:scp-stronger bits_pb_learn_sat:scp-stronger
chain_sat:bridge-witness lin_sat:bridge-witness opt_min_sat:opt-better opt_max_sat:opt-better
opt_min_sat:opt-worse restart_queens6_opt:opt-worse opt_min_sat:core-better restart_queens6_opt:core-better
opt_max_sat:core-worse opt_min_sat:core-worse
element_sat:pin-stronger element_learn_prunes_sat:pin-stronger gcc_forced_sat:pin-stronger
gcc_const_counts_sat:pin-stronger maxmin_sat:pin-stronger maxmin_int_max_sat:pin-stronger
inverse_sat:pin-stronger member_sat:pin-stronger member_gap_sat:pin-stronger"
NSCONTROLS=31
mkdir -p "$OUT/scontrols"
for c in $SCONTROLS; do echo "$c"; done | E2E_SOLVER=1 xargs -P "$J" -I{} bash -c \
    'm=${0%%:*}; k=${0#*:}; f="$1/test/models/$m.fzn"; [ -f "$f" ] || f="$1/tools/e2e/models/$m.fzn"
     run "$1"/tools/e2e/chain.sh "$f" "$2" "$k"' {} "$ROOT" "$OUT/scontrols" \
    | sort > "$OUT/scontrols.txt"
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
        pin-stronger) { [ "$at" = "$target ia" ] && [ "$cause" = "$IA" ]; } || { [ "$at" = "$target rup" ] && [ "$cause" = "$RUP" ]; } && ok=1 ;;
        scp-weaker) { [[ "$at" =~ ^@c[0-9]+\ ia$ ]] && [ "$cause" = "$IA" ]; } || { [[ "$at" =~ ^@c[0-9]+\ rup$ ]] && [ "$cause" = "$RUP" ]; } && ok=1 ;;
        scp-stronger) [[ "$at" == "sol "* ]] && [[ "$cause" =~ ^"$SOL"\ [0-9]+\ in\ the\ database\.\ \(@S\[c\[$target\]\]\)$ ]] && ok=1 ;;
        bridge-witness | sel-witness) [ "$at" = "$target red" ] && [ "$cause" = "$RED" ] && ok=1 ;;
        opt-better)
            ub=${target#* }
            [ "$at" = "conclusion BOUNDS" ] && [ "$cause" = "Unable to verify 'conclusion BOUNDS'. The claimed upper bound of $ub mismatches the best recorded upper bound of $((ub + 1))." ] && ok=1 ;;
        opt-worse) [ "$at" = "conclusion BOUNDS" ] && [ "$cause" = "$OPTW" ] && ok=1 ;;
        core-better) [ "$at" = "conclusion BOUNDS" ] && [ "$cause" = "$CORE [lb <= dbound] T [upper bound check] F [lower bound check] T" ] && ok=1 ;;
        core-worse) [ "$at" = "conclusion BOUNDS" ] && [ "$cause" = "$CORE [lb <= dbound] F [upper bound check] T [lower bound check] T" ] && ok=1 ;;
    esac
    if [[ "$l" == *" REFUSED "* ]] && [ $ok -eq 1 ]; then
        echo "PASS  $l"
        ncok=$((ncok + 1))
    else
        echo "FAIL  $l"
    fi
done < "$OUT/scontrols.txt"
echo "solver controls: $ncok of $nc refused where and as expected ($NSCONTROLS expected)"
[ "$nc" -eq "$NSCONTROLS" ] && [ "$ncok" -eq "$NSCONTROLS" ] || fail=1

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
