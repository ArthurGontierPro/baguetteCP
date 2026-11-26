# y.sh MODEL SOLVER OUTDIR : GCS on the .scp, decide, development cake; raw proof, then solx written sol
m=$1; G=$2; D=/scratch/arthur/scp-gcs-20261124; mkdir -p $D/$3; p=$D/$3/$m; V=$HOME/.cargo/bin/veripb; CK=/cluster/arthur/cakepb-develop-cp-62bdc7f/cake_pb_cp
cp $D/out/$m.scp $p.scp; timeout 60 $CK $p.scp > $p.opb 2> $p.cerr; [ -s $p.cerr ] && { echo "$m|CAKE-ENC $(head -c 80 $p.cerr)|"; exit; }
timeout 60 $G --prove --proof-files-basename $p.g $p.scp > $p.o 2>&1 || { echo "$m|SOLVER rc=$? $(tail -1 $p.o|cut -c1-90)|"; exit; }
raw=no; timeout 120 $V $p.opb $p.g.pbp --elaborate $p.core0 2>/dev/null | grep -q '^s VERIFIED' && raw=yes
sed 's/^solx /sol /; s/^solx;/sol ;/' $p.g.pbp > $p.pbp
timeout 120 $V $p.opb $p.pbp --elaborate $p.core > $p.vl 2>&1
if ! grep -q '^s VERIFIED' $p.vl; then echo "$m|VERIPB $(grep -vE '^Running|^$|Caused' $p.vl | tr '\n' ' ' | cut -c1-170)|raw=$raw"; else
echo "$m|$(timeout 120 $CK $p.scp $p.core 2>&1 | grep -m1 '^s VERIFIED' || echo CAKE-REFUSED)|raw=$raw"; fi
