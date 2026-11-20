#!/usr/bin/env bash
# M14-e2e-verification-T1 (D-0174): the end-to-end chain on the four demo models.
#
#   cake_pb_cp M.scp                      -> M.cake.opb   (the verified encoder's OPB)
#   baguette M.fzn --proof M.bag          -> M.bag.opb, M.bag.pbp (baguette's own, unchanged)
#   bridge.py M.cake.opb M.bag.opb M.bag.pbp -> M.bridged.pbp (re-derives every M.bag.opb row
#                                              from M.cake.opb, then baguette's proof)
#   veripb M.cake.opb M.bridged.pbp --elaborate M.core
#   cake_pb_cp M.scp M.core               -> "s VERIFIED ..." (the verified checker, last word)
#
# M.scp and M.fzn are hand-written twins (no translator yet, M14-T2). cake_pb_cp is built from
# the public CakePB repository (gitlab.com/MIAOresearch/software/cakepb, cp/, commit 438b8f83):
# `gcc basis_ffi.c cp/cake_pb_cp.S -o cake_pb_cp`. cake_pb_cp exits 0 on a refusal, so the
# verdict is read from its "s VERIFIED" line, never from its status.
#
# Usage: CAKE_PB_CP=/path/to/cake_pb_cp bench/e2e_spike/run.sh OUTDIR
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
OUT=${1:?usage: run.sh OUTDIR}
CK=${CAKE_PB_CP:?set CAKE_PB_CP to a built cake_pb_cp}
B=${BAGUETTE:-$ROOT/_build/default/bin/main.exe}
V=$("$ROOT/scripts/checker.sh" 2>/dev/null | sed -n 's/^veripb: //p')
V=${V:-$HOME/.cargo/bin/veripb}
mkdir -p "$OUT"
fail=0
for scp in "$HERE"/models/*.scp; do
    m=$(basename "$scp" .scp)
    o="$OUT/$m"
    "$CK" "$scp" > "$o.cake.opb"
    (ulimit -v 4000000; "$B" "$HERE/models/$m.fzn" --proof "$o.bag" > "$o.out" 2>&1)
    python3 -I "$HERE/bridge.py" "$o.cake.opb" "$o.bag.opb" "$o.bag.pbp" > "$o.bridged.pbp"
    v=$("$V" "$o.cake.opb" "$o.bridged.pbp" --elaborate "$o.core" 2>&1 | grep '^s ')
    c=$("$CK" "$scp" "$o.core" 2>&1 | grep '^s ')
    echo "$m | veripb: ${v:-REFUSED} | cake_pb_cp: ${c:-REFUSED}"
    [[ "$c" == "s VERIFIED"* ]] || fail=1
done
exit $fail
