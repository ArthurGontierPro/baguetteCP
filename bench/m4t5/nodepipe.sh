#!/bin/bash
# nodepipe.sh P : unhinted check, elaboration, splice, hinted check, perf sample (all timed)
P=$1; D=/scratch/arthur/hints-d0102; cd $D; ulimit -v 64000000
VP=$HOME/.cargo/bin/veripb; T="/usr/bin/time -f %e_s_%M_KB"
( $T timeout 10800 $VP $P.opb $P.pbp > $P.vu 2>&1; echo rc=$? >> $P.vu ) &
( $T timeout 600 perf record -F 199 -g -o $P.perf -- $VP $P.opb $P.pbp > $P.vperf 2>&1 ) &
$T timeout 10800 $VP $P.opb $P.pbp -e $P.elab.pbp > $P.ve 2>&1; echo rc=$? >> $P.ve
python3 ${ROOT:-/scratch/arthur/baguette-hints}/bench/m4t5/splice_hints.py $P.pbp $P.elab.pbp $P.h.pbp > $P.sp 2>&1
for i in 1 2; do $T timeout 10800 $VP $P.opb $P.h.pbp > $P.vh$i 2>&1; echo rc=$? >> $P.vh$i; done
wait; echo DONE >> $P.sp
