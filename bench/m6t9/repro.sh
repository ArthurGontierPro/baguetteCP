#!/usr/bin/env bash
# run one job when my sweep uses < 63 slots
P=/scratch/arthur/perf-out-prof
id=$1
while [ "$(pgrep -fc "[p]erf-frozen2/_build/default/bin/main.exe")" -ge 63 ]; do sleep 10; done
cd /scratch/arthur/baguette-perf && export MZN_SOLVER_PATH=$PWD/tools
I=/scratch/arthur/perf-out-a/log/$id.inst; m=$(sed -n "s/^model=//p" $I); d=$(sed -n "s/^data=//p" $I); [ "$d" = "<none>" ] && d=""
[ -s $P/fzn/$id.fzn ] || timeout 120 /scratch/arthur/mzn/MiniZincIDE-2.10.1-x86_64-linux-gnu/bin/minizinc -c --solver baguette $m $d -o $P/fzn/$id.fzn > /dev/null 2>&1
(ulimit -v 32000000; OCAMLRUNPARAM=b timeout 300 ./_build/default/bin/main.exe $P/fzn/$id.fzn --time-limit 280 --stats --max-heap-mb 15625 --proof $P/repro.$id > $P/repro.$id.out 2> $P/repro.$id.err)
echo "rc=$?" >> $P/repro.$id.err
timeout 900 ~/.cargo/bin/veripb $P/repro.$id.opb $P/repro.$id.pbp > $P/repro.$id.vp 2>&1; echo vrc=$? >> $P/repro.$id.vp
