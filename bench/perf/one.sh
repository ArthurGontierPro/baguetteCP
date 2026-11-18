#!/usr/bin/env bash
# M11-T1: one measurement. usage: one.sh INST BUDGET MODE KIND
#   MODE: np (--no-proof) | p (--proof) | b0np / b0p (the same with --bits-above 0)
#   KIND: stat (perf stat instructions:u,cycles:u + --stats + GC totals + /usr/bin/time)
#         rec  (perf record -F 499, self time, no call graph)
#         dw   (perf record -F 99 --call-graph dwarf,8192)
export PATH=$HOME/.cargo/bin:$HOME/.local/bin:$PATH
R=/scratch/arthur/wave47-inventory-runs; B=$R/main.exe; M=$R/m
inst=$1; nl=$2; mode=$3; kind=$4; tag=${inst}_${nl}_${mode}_${kind}
f=$R/inst/$inst.fzn
case $mode in
  np) a="--no-proof";; p) a="--proof $M/pf_$tag";;
  b0np) a="--no-proof --bits-above 0";; b0p) a="--bits-above 0 --proof $M/pf_$tag";;
esac
ulimit -v 32000000
export BAGUETTE_NODE_LIMIT=$nl
case $kind in
  stat) OCAMLRUNPARAM=v=0x400 perf stat -x, -e instructions:u,cycles:u -o $M/$tag.perfstat \
          /usr/bin/time -f "wall=%e rss=%M" $B --stats $a $f > $M/$tag.out 2> $M/$tag.err ;;
  rec)  perf record -q --per-thread -m 128 -F 499 -o $M/$tag.data $B $a $f > /dev/null 2> $M/$tag.err ;;
  dw)   perf record -q --per-thread -m 1024 -F 99 --call-graph dwarf,8192 -o $M/$tag.data $B $a $f > /dev/null 2> $M/$tag.err ;;
esac
echo "rc=$?" >> $M/$tag.err
if [ -f $M/pf_$tag.pbp ]; then echo "pbp_bytes=$(stat -c %s $M/pf_$tag.pbp) opb_bytes=$(stat -c %s $M/pf_$tag.opb)" >> $M/$tag.err; rm -f $M/pf_$tag.pbp $M/pf_$tag.opb; fi
if [ $kind = rec ]; then
  perf report -i $M/$tag.data --no-children --stdio --sort symbol 2>/dev/null | grep -v "^#" | grep "%" | head -80 > $M/$tag.top
fi
touch $M/$tag.done
