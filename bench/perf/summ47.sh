#!/usr/bin/env bash
# M11-complexity-T1 (D-0140): one line per `stat` run of the inventory matrix.
# usage: summ47.sh RUNDIR    (RUNDIR/m holds <inst>_<budget>_<mode>_stat.{err,perfstat,done})
# Columns: instance, node budget, mode, user instructions and cycles (10^9), wall s, peak RSS MB,
# nodes, conflicts, learned clauses, database size, propagator runs, wakes, wakes declined by an
# advisor, seeded runs, skipped seed slots, learned_clause instances and their runs per node,
# allocated and promoted words (10^6), minor and major collections, .pbp size (MB).
cd "$1/m" || exit 1
printf "inst\tbudget\tmode\tGinstr\tGcyc\twall\trssMB\tnodes\tconfl\tlearned\tdb\tprops\twakes\tadvised\tseeded\tskipped\tlc_inst\tlc_runs_per_node\tallocMw\tpromMw\tminor\tmajor\tpbpMB\n"
for f in *_stat.err; do
  t=${f%_stat.err}
  [ -f "${t}_stat.done" ] || continue
  mode=${t##*_}; r=${t%_*}; nl=${r##*_}; inst=${r%_*}
  ins=$(awk -F, '/instructions/ {printf "%.2f", $1/1e9}' "${t}_stat.perfstat")
  cyc=$(awk -F, '/cycles/ {printf "%.2f", $1/1e9}' "${t}_stat.perfstat")
  wall=$(grep -o 'wall=[0-9.]*' "$f" | tail -1 | cut -d= -f2)
  rss=$(grep -o 'rss=[0-9]*' "$f" | tail -1 | cut -d= -f2)
  lim=$(grep '^limit:' "$f" | head -1)
  g() { echo "$lim" | grep -o " $1=[^ ]*" | cut -d= -f2; }
  st() { grep -E "^stats: $1 " "$f" | awk '{print $3}' | head -1; }
  lc=$(grep -E '^stats: learned_clause ' "$f" | awk '{print $3"\t"$5}')
  [ -z "$lc" ] && lc="0	0"
  aw=$(awk '/^allocated_words/ {printf "%.0f", $2/1e6}' "$f")
  pw=$(awk '/^promoted_words/ {printf "%.0f", $2/1e6}' "$f")
  mi=$(awk '/^minor_collections/ {print $2}' "$f")
  ma=$(awk '/^major_collections/ {print $2}' "$f")
  pb=$(grep -o 'pbp_bytes=[0-9]*' "$f" | cut -d= -f2)
  if [ -n "$pb" ]; then pb=$((pb / 1000000)); else pb=-; fi
  printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" \
    "$inst" "$nl" "$mode" "$ins" "$cyc" "$wall" "$((${rss:-0} / 1000))" "$(g nodes)" "$(g conflicts)" \
    "$(g learned)" "$(g db)" "$(g props)" "$(st wakes)" "$(st advised)" "$(st seeded)" "$(st skipped)" \
    "$lc" "$aw" "$pw" "$mi" "$ma" "$pb"
done | sort -t"$(printf '\t')" -k1,1 -k3,3 -k2,2n
