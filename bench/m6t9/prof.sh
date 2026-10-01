#!/usr/bin/env bash
# M6-T9 profiles: perf record 60 s per instance, both binaries hashed.
P=/scratch/arthur/perf-out-prof
NEW=/scratch/arthur/perf-frozen2/_build/default/bin/main.exe
OLD=/scratch/arthur/perf-frozen/_build/default/bin/main.exe
md5sum $NEW $OLD > $P/hashes.txt
one() {
  local tag=$1 bin=$2 id=$3
  ( ulimit -v 32000000
    OCAMLRUNPARAM=v=0x400 /usr/bin/perf record -m 32 -F 499 --call-graph dwarf,8192 -o $P/$tag.$id.perf.data -- \
      /usr/bin/time -f "rss_kb=%M wall=%e" $bin $P/fzn/$id.fzn --time-limit 60 --stats --time --proof $P/$tag.$id \
      > $P/$tag.$id.out 2> $P/$tag.$id.err
    /usr/bin/perf report -i $P/$tag.$id.perf.data --no-children --percent-limit 1 --stdio --sort symbol 2>/dev/null | grep "%" > $P/$tag.$id.self.txt
    /usr/bin/perf report -i $P/$tag.$id.perf.data --children --percent-limit 5 --stdio --sort symbol -g none 2>/dev/null | grep "%" > $P/$tag.$id.children.txt
    rm -f $P/$tag.$id.pbp $P/$tag.$id.opb
  ) &
}
for id in 2011_costas-array_CostasArray 2018_rotating-workforce 2008_trucking 2017_tc-graph-color_tcgc2 2016_prize-collecting_pc 2009_black-hole; do one new $NEW $id; done
one old $OLD 2011_costas-array_CostasArray
wait
echo PROF-DONE
