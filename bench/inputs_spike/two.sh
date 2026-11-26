# two.sh MODEL.fzn : one .scp, two proofs, both checked by cake_pb_cp against that .scp
f=$1; m=$(basename $f .fzn); D=/scratch/arthur/scp-gcs-20261124; o=$D/out/$m
G=/scratch/arthur/baguette-gate-20261124h
export CAKE_PB_CP=/cluster/arthur/baguette-results/wave55-e2e/cake_pb_cp-438b8f83 E2E_SOLVER=1 E2E_TIMEOUT=60
V=$HOME/.cargo/bin/veripb
python3 -I $G/tools/e2e/fzn2scp.py $f $o.scp $o.names 2> $o.tr || { echo "$m|NOSCP|$(cat $o.tr|head -1)|"; exit; }
b=$(bash $G/tools/e2e/chain.sh $f $D/outb 2>&1 | tail -1)
cmp -s $o.scp $D/outb/$m.scp && same=samescp || same=DIFFscp
timeout 60 $CAKE_PB_CP $o.scp > $o.opb 2>$o.cerr
( timeout 60 $D/build/glasgow_scp_solver --prove --proof-files-basename $o.gcs $o.scp > $o.gout 2>&1 ); rc=$?
if [ $rc -ne 0 ]; then g="SOLVER rc=$rc $(grep -m1 -i error $o.gout | cut -c1-120)"; else
 timeout 120 $V $o.opb $o.gcs.pbp --elaborate $o.core > $o.vl 2>&1
 if ! grep -q '^s VERIFIED' $o.vl; then g="VERIPB $(grep -m1 -iE 'error|not |unknown' $o.vl | cut -c1-160)"; else
 g=$(timeout 120 $CAKE_PB_CP $o.scp $o.core 2>&1 | grep -m1 '^s VERIFIED' || echo CAKE-REFUSED); fi; fi
echo "$m|$same|$b|$g"
