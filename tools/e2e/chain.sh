#!/usr/bin/env bash
# One model through the end-to-end chain: baguette's proof, checked by CakeML's verified
# cake_pb_cp against cake's own encoding of the model (the chain chosen by D-0174, run over the
# test models as the lane of D-0176; written for M14-e2e-verification-T2):
#
#   fzn2scp.py  M.fzn            -> M.scp, M.names   (the translator: TRUSTED, small)
#   cake_pb_cp  M.scp            -> M.cake.opb       (the verified encoder)
#   baguette    M.fzn --proof    -> M.bag.opb, M.bag.pbp (order arm, default flags)
#   bridge.py                    -> M.bridged.pbp    (re-derives M.bag.opb from M.cake.opb)
#   veripb M.cake.opb M.bridged.pbp --elaborate M.core   (untrusted elaborator)
#   cake_pb_cp  M.scp M.core     -> "s VERIFIED ..."  (the verified checker: the verdict)
#
# Usage: tools/e2e/chain.sh MODEL.fzn OUTDIR [MUTATION]
#   MUTATION, for the lane's controls (D-0176):
#     opb-stronger    baguette's first model row with three terms or more gets its degree
#                     raised by 1 after baguette ran: its .opb now says MORE than the model,
#                     a transcription bug; the bridge cannot derive that row from cake's file
#     scp-stronger    the translator's first lin_less_equal/lin_equals gets its right-hand
#                     side lowered by 1 (a mistranslation): a SAT answer's `sol` conflicts
#                     with cake's row, or baguette's row is not derivable from it
#     scp-weaker      the same raised by 1: baguette's row is not derivable from it
#     opb-reif        baguette's first reified big-M row gets its reifier's literal flipped
#                     after baguette ran (tools/e2e/mutate.py reif): a wrong reification in
#                     its .opb, which the bridge cannot derive either (T4, D-0178)
#     bridge-witness  the bridge's first `@A2` atom definition gets the witness `-> 0` in place
#                     of `-> 1` (D-0174's first mutation): its red line is refused
#     copy-witness    the bridge's first `@Y1` line, which defines a global_cardinality copy's
#                     rung as its original's, gets the witness `Y -> ~X` (tools/e2e/mutate.py
#                     copy): a wrong definition of an auxiliary baguette introduces, refused at
#                     that red line (T5, D-0180)
#     opt-better      (T8, D-0182) baguette's `conclusion BOUNDS` claims an optimum one
#                     better than the one it found (tools/e2e/mutate.py bounds .. -1):
#                     refused by veripb at that line, the best recorded upper bound
#     opt-worse       the same one worse (+1): refused at that line, the lower bound
#     core-better     the ELABORATED core's conclusion moved by -1 after veripb accepted the
#     core-worse      bridged proof (+1 for core-worse): refused by cake_pb_cp ITSELF, the
#                     verified checker, at its conclusion line ("conclusion BOUNDS check
#                     failed: ..."), so a wrong optimum is refused even past an untrusted
#                     elaborator that let it through
#   A mutation run prints `MODEL.MUT REFUSED ANSWER | at=<first two tokens of the refused
#   line> | cause=<the checker's sentence> | target=<what was mutated>`, and the lane checks
#   all of it against what the control expects (scripts/e2e_lane.sh).
#
# E2E_SOLVER=1 (M14-e2e-verification-T3, D-0187): the SOLVER-WRITTEN path. baguette runs with
# `--e2e` and its own .pbp is checked against M.cake.opb directly: its head derives M.bag.opb's
# rows from cake's, so there is no bridge and no `veripb alone` baseline (that proof does not
# check against baguette's own .opb). A model --e2e does not cover (baguette exits 3 with
# "--e2e: ...") is SKIPPED with that reason. Two more mutations, for this path:
#     pin-stronger    the solver-written pin of the row opb-stronger picks (the first .opb row
#                     with three terms or more) gets its degree raised by 1 in the proof: the
#                     prefix now claims a row cake's file does not imply
#                     (tools/e2e/mutate.py pin); refused at that pin
#     sel-witness     the first disequality selector definition `@D1[...]` gets the witness
#                     `s -> ~F` in place of `s -> F` (tools/e2e/mutate.py sel): a wrong
#                     definition of the auxiliary the solver introduces, refused at that red
#                     line
# bridge-witness, scp-*, opt-* and core-* apply to it unchanged (on the solver's own .pbp).
# T6 (D-0195) adds two, on either path's proof (the bridged one or the solver's):
#     flag-witness    the first regular state flag past layer 0, `@D1[s]`, defined with the
#                     witness `s -> ~F`, F cake's flag (tools/e2e/mutate.py flag)
#     guard-witness   the first `@D1[...]` (on an int_abs model, its sign guard's definition
#                     as x_ge_0) with the witness `s -> ~F` (tools/e2e/mutate.py sel)
# and a refused line inside a subproof is reported as the `pbc` that opens it (an int_abs
# row derived by contradiction), so pin-stronger and opb-stronger name the row's label.
#
# Prints ONE line: `MODEL VERDICT detail`, VERDICT in VERIFIED, SKIPPED, FAIL, and REFUSED
# (mutation runs only). VERIFIED is followed by SAT, UNSAT or OPT=<v> (T8, D-0182): an
# optimisation model is VERIFIED only on cake_pb_cp's `s VERIFIED BOUNDS v <= OBJ <= v`,
# v the optimum baguette's own `conclusion BOUNDS v : .. v` claims (negated back for
# `maximize`; cake prints a negative number as `~6`), or, when baguette says UNSAT, on
# `s VERIFIED BOUNDS -INF <= OBJ <= +INF`. That print is cake's OBounds NONE NONE, and under
# cpScript.sml's cp_sem_concl the side that is NONE for the problem's direction (cp_is_lb
# for minimize, cp_is_ub for maximize) means cp_unsatisfiable. The verdict is read from
# cake_pb_cp's `s VERIFIED` line, never from its exit status: it exits 0 when it refuses
# (D-0174 section 6).
#
# Exit 0 whenever that line is printed, whatever the verdict; 1 when no checker is found (the
# line then reads `MODEL FAIL no checker`), or when OUTDIR, MODEL.fzn or CAKE_PB_CP is missing.
# Every artefact goes to OUTDIR/MODEL[.MUTATION].* (the script's PID in its .pid while it runs).
#
# Env: CAKE_PB_CP (required), BAGUETTE (default _build/default/bin/main.exe, which this script
# does NOT build), VERIPB (else scripts/checker.sh), E2E_TIMEOUT (s, default 300).
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
FZN=${1:?usage: chain.sh MODEL.fzn OUTDIR [MUTATION]}
OUT=${2:?usage: chain.sh MODEL.fzn OUTDIR [MUTATION]}
MUT=${3:-}
CK=${CAKE_PB_CP:?set CAKE_PB_CP to a built cake_pb_cp}
B=${BAGUETTE:-$ROOT/_build/default/bin/main.exe}
TO=${E2E_TIMEOUT:-300}
# shellcheck source=/dev/null
. "$ROOT/scripts/checker.sh"
baguette_resolve_veripb || { echo "$(basename "$FZN" .fzn) FAIL no checker"; exit 1; }
V=$VERIPB

m=$(basename "$FZN" .fzn)
[ -n "$MUT" ] && m="$m.$MUT"
o="$OUT/$m"
mkdir -p "$OUT"
echo $$ > "$o.pid"
say() { echo "$m $*"; rm -f "$o.pid"; exit 0; }
now() { date +%s.%N; }
dt() { awk -v a="$1" -v b="$2" 'BEGIN{printf "%.3f", b-a}'; }
target=

if ! python3 -I "$HERE/fzn2scp.py" "$FZN" "$o.scp" "$o.names" 2> "$o.tr.err"; then
    r=$(sed -n 's/^UNCOVERED: //p' "$o.tr.err" | head -1)
    [ -n "$r" ] && say "SKIPPED $r"
    say "FAIL translator: $(head -1 "$o.tr.err")"
fi
opt=$(sed -n 's/.*(prob_type (\(minimize\|maximize\) .*/\1/p' "$o.scp")
case "$MUT" in
    scp-stronger | scp-weaker)
        d=-1
        [ "$MUT" = scp-weaker ] && d=1
        target=$(python3 -I "$HERE/mutate.py" scp "$o.scp" "$d") || say "FAIL no linear constraint to mutate"
        ;;
esac
timeout "$TO" "$CK" "$o.scp" > "$o.cake.opb" 2> "$o.cake.err"
[ -s "$o.cake.err" ] && say "FAIL cake_pb_cp refused the .scp: $(head -1 "$o.cake.err")"

SOLVER=${E2E_SOLVER:-}
EF=()
[ -n "$SOLVER" ] && EF=(--e2e)
# E2E_FLAGS (T7, D-0196): more solver flags, `--bits-above W` for the bits arm; a `bits-*`
# control runs at `--bits-above 0` whatever E2E_FLAGS says
read -r -a XF <<< "${E2E_FLAGS:-}"
case "$MUT" in bits-*) XF=(--bits-above 0) ;; esac
# E2E_SEARCH (M19-config-T1, D-0261): the search, --fixed-search unless set (empty is the
# default search): the lane's controls were recorded on the fixed search
read -r -a SF <<< "${E2E_SEARCH---fixed-search}"
(ulimit -v 4000000; timeout "$TO" "$B" "$FZN" --proof "$o.bag" "${SF[@]}" "${EF[@]}" "${XF[@]}" > "$o.bag.out" 2> "$o.bag.err")
rc=$?
if [ -n "$SOLVER" ] && [ $rc -eq 3 ] && grep -q '^baguette: --e2e: ' "$o.bag.err"; then
    say "SKIPPED e2e: $(sed -n 's/^baguette: --e2e: \(.*\) (D-0187).*/\1/p' "$o.bag.err" | head -1)"
fi
[ $rc -eq 0 ] || say "FAIL baguette exited $rc"
# the proof checked against cake's file: the bridged one, or the solver's own under --e2e
PB="$o.bridged.pbp"
[ -n "$SOLVER" ] && PB="$o.bag.pbp"
ans=SAT
grep -q '=====UNSATISFIABLE=====' "$o.bag.out" && ans=UNSAT
want=
if [ -n "$opt" ]; then
    if [ $ans = UNSAT ]; then
        want="s VERIFIED BOUNDS -INF <= OBJ <= +INF"
    else
        grep -qx '==========' "$o.bag.out" || say "FAIL baguette did not prove optimality"
        read -r lb ub <<< "$(sed -n 's/^conclusion BOUNDS \(-\?[0-9]*\) : \S* \(-\?[0-9]*\).*/\1 \2/p' "$o.bag.pbp")"
        [ -n "${ub:-}" ] && [ "$lb" = "$ub" ] || say "FAIL baguette's conclusion is not an optimum: $(grep '^conclusion' "$o.bag.pbp")"
        v=$ub
        [ "$opt" = maximize ] && v=$((-ub))
        ans="OPT=$v"
        sv=${v/#-/\~}
        want="s VERIFIED BOUNDS $sv <= OBJ <= $sv"
    fi
fi

if [ "$MUT" = opb-stronger ] || [ "$MUT" = bits-opb ]; then
    target=$(python3 -I "$HERE/mutate.py" opb "$o.bag.opb") || say "FAIL no model row to mutate"
fi
if [ "$MUT" = pin-stronger ] || [ "$MUT" = bits-pin ]; then
    target=$(python3 -I "$HERE/mutate.py" pin "$o.bag.opb" "$o.bag.pbp") || say "FAIL no pinned model row to mutate"
fi
if [ "$MUT" = sel-witness ]; then
    target=$(python3 -I "$HERE/mutate.py" sel "$o.bag.pbp") || say "FAIL no selector definition to mutate"
fi
case "$MUT" in
    opt-better | opt-worse)
        d=-1
        [ "$MUT" = opt-worse ] && d=1
        target=$(python3 -I "$HERE/mutate.py" bounds "$o.bag.pbp" "$d") || say "FAIL no conclusion BOUNDS to mutate"
        ;;
esac
if [ "$MUT" = opb-reif ]; then
    target=$(python3 -I "$HERE/mutate.py" reif "$o.bag.opb") || say "FAIL no reified row to mutate"
fi

tv=NA
if [ -z "$SOLVER" ]; then
    # veripb alone on baguette's own files: the cost the chain is compared against
    t0=$(now)
    timeout "$TO" "$V" "$o.bag.opb" "$o.bag.pbp" > "$o.vbag.log" 2>&1
    t1=$(now)
    tv=$(dt "$t0" "$t1")

    python3 -I "$HERE/bridge.py" "$o.cake.opb" "$o.names" "$o.bag.opb" "$o.bag.pbp" \
        > "$o.bridged.pbp" 2> "$o.bridge.err" || say "FAIL bridge: $(tail -1 "$o.bridge.err")"
fi
if [ "$MUT" = bridge-witness ]; then
    target=$(python3 -I "$HERE/mutate.py" witness "$PB") || say "FAIL no atom definition to mutate"
fi
if [ "$MUT" = copy-witness ]; then
    target=$(python3 -I "$HERE/mutate.py" copy "$PB") || say "FAIL no copy definition to mutate"
fi
# T6 (D-0195), on either path's proof: a regular state flag, an int_abs sign guard defined wrong
if [ "$MUT" = flag-witness ]; then
    target=$(python3 -I "$HERE/mutate.py" flag "$PB") || say "FAIL no regular flag definition to mutate"
fi
# T7 (D-0196), on either path's proof: a bits-arm bit defined as the wrong cake bit
if [ "$MUT" = bits-def ]; then
    target=$(python3 -I "$HERE/mutate.py" bitdef "$PB") || say "FAIL no bits definition to mutate"
fi
if [ "$MUT" = bits-tight ]; then
    target=$(python3 -I "$HERE/mutate.py" tight "$PB") || say "FAIL no row by contradiction to mutate"
fi
if [ "$MUT" = guard-witness ]; then
    target=$(python3 -I "$HERE/mutate.py" sel "$PB") || say "FAIL no guard definition to mutate"
fi

t0=$(now)
timeout "$TO" "$V" "$o.cake.opb" "$PB" --elaborate "$o.core" > "$o.veripb.log" 2>&1
t1=$(now)
te=$(dt "$t0" "$t1")
case "$MUT" in
    core-better | core-worse)
        d=-1
        [ "$MUT" = core-worse ] && d=1
        grep -q '^s VERIFIED' "$o.veripb.log" || say "FAIL mutation $MUT: veripb refused the unmutated proof"
        target=$(python3 -I "$HERE/mutate.py" bounds "$o.core" "$d") || say "FAIL no conclusion BOUNDS in the core"
        ;;
esac
rm -f "$o.check.log"
t0=$(now)
[ -s "$o.core" ] && timeout "$TO" "$CK" "$o.scp" "$o.core" > "$o.check.log" 2>&1
t1=$(now)
tc=$(dt "$t0" "$t1")
s=$(grep -m1 '^s ' "$o.check.log" 2> /dev/null)

if [ -n "$MUT" ]; then
    # a control: the chain must refuse, and say where and why in the checker's own words
    [[ "$s" == "s VERIFIED"* ]] && say "FAIL mutation $MUT VERIFIED ($s) target=$target"
    if [[ "$MUT" == core-* ]]; then
        # refused by cake_pb_cp itself: `c Checking failed for top-level proof step starting
        # at line: N (...). Reason: R`
        ln=$(sed -n 's/^c Checking failed for top-level proof step starting at line: \([0-9]*\) .*/\1/p' "$o.check.log" | head -1)
        [ -n "$ln" ] || say "FAIL mutation $MUT: cake_pb_cp did not refuse (${s:-no s line})"
        at=$(sed -n "${ln}p" "$o.core" | awk '{print $1, $2}')
        cause=$(sed -n 's/^c Checking failed for top-level proof step .* Reason: //p' "$o.check.log" | head -1)
        say "REFUSED $ans | at=$at | cause=$cause | target=$target"
    fi
    ln=$(sed -n 's/.*\(Checking\|Verification\) error at .*:\([0-9]*\)$/\2/p' "$o.veripb.log" | head -1)
    [ -n "$ln" ] || say "FAIL mutation $MUT: veripb did not refuse (cake: ${s:-no s line})"
    at=$(sed -n "${ln}p" "$PB" | awk '{print $1, $2}')
    # a line inside a subproof (T6, D-0195: an int_abs row by contradiction) is reported as
    # the `pbc` that opens it, whose label names the row
    if sed -n "${ln}p" "$PB" | grep -q '^[[:space:]]'; then
        at=$(head -n "$ln" "$PB" | grep ' pbc ' | tail -1 | awk '{print $1, $2}')
    fi
    cause=$(grep -A1 '^Caused by:' "$o.veripb.log" | tail -1 | sed 's/^[[:space:]]*//')
    # one sentence, except a BOUNDS refusal, whose second sentence says which bound (T8)
    [[ "$cause" == "Unable to verify 'conclusion BOUNDS'."* ]] || cause=$(echo "$cause" | sed 's/\. .*/./')
    # "conflicting with constraint K": name K by its label, a cake row (K <= f) or the
    # (K - f)-th line of the prefix (every prefix line but a `del` derives exactly one constraint)
    k=$(echo "$cause" | sed -n 's/.*conflicting with constraint \([0-9]*\) in the database.*/\1/p')
    if [ -n "$k" ]; then
        f=$(grep -c ';' "$o.cake.opb")
        if [ "$k" -le "$f" ]; then
            lab=$(grep ';' "$o.cake.opb" | sed -n "${k}p" | awk '{print $1}')
        else
            # the bridged proof has an `f` line (skip 2 lines), the solver's has none (skip 1)
            hd=3
            [ -n "$SOLVER" ] && hd=2
            lab=$(tail -n +$hd "$PB" | grep -v -e '^%' -e '^del ' | sed -n "$((k - f))p" | awk '{print $1}')
        fi
        cause="$cause ($lab)"
    fi
    say "REFUSED $ans | at=$at | cause=$cause | target=$target"
fi
[[ "$s" == "s VERIFIED"* ]] || say "FAIL $ans veripb: $(grep -m1 -A2 'error' "$o.veripb.log" | tr '\n' ' ' | head -c 300) cake: ${s:-no s line}"
if [ -n "$want" ]; then
    [ "$s" = "$want" ] || say "FAIL baguette said $ans, cake_pb_cp says $s"
else
    case "$ans:$s" in
        "SAT:s VERIFIED SATISFIABLE"* | "UNSAT:s VERIFIED UNSATISFIABLE"*) ;;
        *) say "FAIL baguette said $ans, cake_pb_cp says $s" ;;
    esac
fi
say "VERIFIED $ans veripb=${tv}s elaborate=${te}s cake=${tc}s pbp=$(stat -c %s "$o.bag.pbp") bridged=$(stat -c %s "$PB") core=$(stat -c %s "$o.core")"
