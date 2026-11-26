# w.sh MODEL : the August GCS on the .scp of fzn2scp, decide, solx written sol, public cake
m=$1; D=/scratch/arthur/scp-gcs-20261124; p=$D/o6/$m; V=$HOME/.cargo/bin/veripb; CK=/cluster/arthur/baguette-results/wave55-e2e/cake_pb_cp-438b8f83
timeout 60 $D/buildold/glasgow_scp_solver --prove --proof-files-basename $p.g $D/out/$m.scp > $p.o 2>&1 || { echo "$m|SOLVER rc=$? $(tail -1 $p.o|cut -c1-90)"; exit; }
raw=no; timeout 120 $V $D/out/$m.opb $p.g.pbp --elaborate $p.core0 2>/dev/null | grep -q '^s VERIFIED' && raw=yes
sed 's/^solx /sol /; s/^solx;/sol ;/' $p.g.pbp > $p.pbp
timeout 120 $V $D/out/$m.opb $p.pbp --elaborate $p.core > $p.vl 2>&1
if ! grep -q '^s VERIFIED' $p.vl; then echo "$m|VERIPB $(grep -vE '^Running|^$|Caused' $p.vl | tr '\n' ' ' | cut -c1-150)|raw=$raw"; else
echo "$m|$(timeout 120 $CK $D/out/$m.scp $p.core 2>&1 | grep -m1 '^s VERIFIED' || echo CAKE-REFUSED)|raw=$raw"; fi
