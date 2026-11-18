#!/usr/bin/env bash
# M11-complexity-T1 (D-0140): one SCRATCH measurement -- main's binary or a scratch variant
# (bench/perf/scratch/*.patch applied to main, never merged) on one instance at a node budget.
# usage: one_s.sh VARIANT INST BUDGET MODE     VARIANT: base | s1 | s2 | s3 | all; MODE: np | p
# Writes s/<variant>_<inst>_<budget>_<mode>.{perfstat,out,err}; for MODE p, the md5 and size of
# the .opb and .pbp go into the .err and the proof files are deleted.
export PATH=$HOME/.cargo/bin:$HOME/.local/bin:$PATH
R=/scratch/arthur/wave47-inventory-runs
v=$1; inst=$2; nl=$3; mode=$4; tag=${v}_${inst}_${nl}_${mode}
if [ "$v" = base ]; then B=$R/main.exe; else B=$R/main-$v.exe; fi
O=$R/s; mkdir -p $O
case $mode in np) a="--no-proof" ;; p) a="--proof $O/pf_$tag" ;; esac
ulimit -v 32000000
export BAGUETTE_NODE_LIMIT=$nl
perf stat -x, -e instructions:u,cycles:u -o $O/$tag.perfstat \
  $B --stats $a $R/inst/$inst.fzn > $O/$tag.out 2> $O/$tag.err
echo "rc=$?" >> $O/$tag.err
if [ -f $O/pf_$tag.pbp ]; then
  echo "pbp_md5=$(md5sum < $O/pf_$tag.pbp | cut -c1-32) pbp_bytes=$(stat -c %s $O/pf_$tag.pbp) opb_md5=$(md5sum < $O/pf_$tag.opb | cut -c1-32)" >> $O/$tag.err
  rm -f $O/pf_$tag.pbp $O/pf_$tag.opb
fi
touch $O/$tag.done
