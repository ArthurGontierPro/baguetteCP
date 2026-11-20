#!/usr/bin/env bash
# One model through the end-to-end chain of D-0174/D-0176 (M14-e2e-verification-T2):
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
#     bridge-witness  the bridge's first `@A2` atom definition gets the witness `-> 0` in place
#                     of `-> 1` (D-0174's first mutation): its red line is refused
#   A mutation run prints `MODEL.MUT REFUSED ANSWER | at=<first two tokens of the refused
#   line> | cause=<the checker's sentence> | target=<what was mutated>`, and the lane checks
#   all of it against what the control expects (scripts/e2e_lane.sh).
#
# Prints ONE line: `MODEL VERDICT detail`, VERDICT in VERIFIED, SKIPPED, FAIL, and REFUSED
# (mutation runs only). The verdict is read from cake_pb_cp's `s VERIFIED` line, never from
# its exit status: it exits 0 when it refuses (D-0174 section 6).
#
# Env: CAKE_PB_CP (required), BAGUETTE, VERIPB (else scripts/checker.sh), E2E_TIMEOUT (s).
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
case "$MUT" in
    scp-stronger | scp-weaker)
        d=-1
        [ "$MUT" = scp-weaker ] && d=1
        target=$(python3 -I "$HERE/mutate.py" scp "$o.scp" "$d") || say "FAIL no linear constraint to mutate"
        ;;
esac
timeout "$TO" "$CK" "$o.scp" > "$o.cake.opb" 2> "$o.cake.err"
[ -s "$o.cake.err" ] && say "FAIL cake_pb_cp refused the .scp: $(head -1 "$o.cake.err")"

(ulimit -v 4000000; timeout "$TO" "$B" "$FZN" --proof "$o.bag" > "$o.bag.out" 2> "$o.bag.err")
rc=$?
[ $rc -eq 0 ] || say "FAIL baguette exited $rc"
ans=SAT
grep -q '=====UNSATISFIABLE=====' "$o.bag.out" && ans=UNSAT

if [ "$MUT" = opb-stronger ]; then
    target=$(python3 -I "$HERE/mutate.py" opb "$o.bag.opb") || say "FAIL no model row to mutate"
fi

# veripb alone on baguette's own files: the cost the chain is compared against
t0=$(now)
timeout "$TO" "$V" "$o.bag.opb" "$o.bag.pbp" > "$o.vbag.log" 2>&1
t1=$(now)
tv=$(dt "$t0" "$t1")

python3 -I "$HERE/bridge.py" "$o.cake.opb" "$o.names" "$o.bag.opb" "$o.bag.pbp" \
    > "$o.bridged.pbp" 2> "$o.bridge.err" || say "FAIL bridge: $(tail -1 "$o.bridge.err")"
if [ "$MUT" = bridge-witness ]; then
    target=$(python3 -I "$HERE/mutate.py" witness "$o.bridged.pbp") || say "FAIL no atom definition to mutate"
fi

t0=$(now)
timeout "$TO" "$V" "$o.cake.opb" "$o.bridged.pbp" --elaborate "$o.core" > "$o.veripb.log" 2>&1
t1=$(now)
te=$(dt "$t0" "$t1")
rm -f "$o.check.log"
t0=$(now)
[ -s "$o.core" ] && timeout "$TO" "$CK" "$o.scp" "$o.core" > "$o.check.log" 2>&1
t1=$(now)
tc=$(dt "$t0" "$t1")
s=$(grep -m1 '^s ' "$o.check.log" 2> /dev/null)

if [ -n "$MUT" ]; then
    # a control: the chain must refuse, and say where and why in the checker's own words
    [[ "$s" == "s VERIFIED"* ]] && say "FAIL mutation $MUT VERIFIED ($s) target=$target"
    ln=$(sed -n 's/.*\(Checking\|Verification\) error at .*:\([0-9]*\)$/\2/p' "$o.veripb.log" | head -1)
    [ -n "$ln" ] || say "FAIL mutation $MUT: veripb did not refuse (cake: ${s:-no s line})"
    at=$(sed -n "${ln}p" "$o.bridged.pbp" | awk '{print $1, $2}')
    cause=$(grep -A1 '^Caused by:' "$o.veripb.log" | tail -1 | sed 's/^[[:space:]]*//; s/\. .*/./')
    # "conflicting with constraint K": name K by its label, a cake row (K <= f) or the
    # (K - f)-th line of the prefix (every prefix line derives exactly one constraint)
    k=$(echo "$cause" | sed -n 's/.*conflicting with constraint \([0-9]*\) in the database.*/\1/p')
    if [ -n "$k" ]; then
        f=$(grep -c ';' "$o.cake.opb")
        if [ "$k" -le "$f" ]; then
            lab=$(grep ';' "$o.cake.opb" | sed -n "${k}p" | awk '{print $1}')
        else
            lab=$(tail -n +3 "$o.bridged.pbp" | grep -v '^%' | sed -n "$((k - f))p" | awk '{print $1}')
        fi
        cause="$cause ($lab)"
    fi
    say "REFUSED $ans | at=$at | cause=$cause | target=$target"
fi
[[ "$s" == "s VERIFIED"* ]] || say "FAIL $ans veripb: $(grep -m1 -A2 'error' "$o.veripb.log" | tr '\n' ' ' | head -c 300) cake: ${s:-no s line}"
case "$ans:$s" in
    "SAT:s VERIFIED SATISFIABLE"* | "UNSAT:s VERIFIED UNSATISFIABLE"*) ;;
    *) say "FAIL baguette said $ans, cake_pb_cp says $s" ;;
esac
say "VERIFIED $ans veripb=${tv}s elaborate=${te}s cake=${tc}s pbp=$(stat -c %s "$o.bag.pbp") bridged=$(stat -c %s "$o.bridged.pbp") core=$(stat -c %s "$o.core")"
