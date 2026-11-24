#!/usr/bin/env bash
# M17-bench-series-T1 (D-0203). Read a series directory: the tables, into DIR/tables. Read-only
# over the run directories.
#   read_series.sh DIR [REPO]      REPO holds tools/compare (default: the clone DIR/src)
# Writes, for the arms of DIR/series.conf:
#   results_<L>.tsv                every row of the arm (the DONE markers dropped)
#   rank_<L>_<YEAR>.txt            challenge_rank.py: the arm's rank. A `-f` arm is ranked in the FREE
#                                  category here, and in the fixed-search one as rank_<L>fd_<YEAR>.txt;
#                                  a `noproof` arm with --trust-unverified (its answers are unverified)
#   refusal_causes_<L>.txt, arms.txt (arms_compare.py, the first arm against each other one)
# tools/compare/readme_table.py then writes the README section from DIR.
set -u
DIR="$1"; REPO="${2:-$DIR/src}"
T="$DIR/tables"; mkdir -p "$T"
AR="${MZNC_ARCHIVE:-/scratch/arthur/mznc-archive/results}"
cd "$REPO" || exit 1
arms=$(grep '^arm=' "$DIR/series.conf" | cut -d= -f2-)
args=(); pairs=(); trust=(); first=""
while IFS= read -r a; do
  l=${a%%:*}; rest=${a#*:}; p=${rest%%:*}; f=${rest#*:}
  [ -n "$first" ] || first=$l
  args+=("$l=$DIR/$l")
  [ "$l" = "$first" ] || pairs+=(--pair "$first" "$l")
  [ "$p" = noproof ] && trust+=(--trust "$l")
  grep -h -v '^DONE-' "$DIR/$l"/20*/results.tsv > "$T/results_$l.tsv"
  opts=(--no-chuffed); [ "$p" = noproof ] && opts+=(--trust-unverified)
  isfree=0; case " $f " in *" -f "*) isfree=1 ;; esac
  for y in $(seq 2026 -1 2011); do
    [ -d "$DIR/$l/$y" ] || continue   # an edition with no instance of a --list run
    if [ "$isfree" = 1 ]; then
      python3 -I tools/compare/challenge_rank.py "$AR/$y.json" "bench/challenge/$y.lst" "$DIR/$l/$y" "${opts[@]}" --category=free --as="baguette-$l-free" > "$T/rank_${l}_$y.txt" 2>&1
      python3 -I tools/compare/challenge_rank.py "$AR/$y.json" "bench/challenge/$y.lst" "$DIR/$l/$y" "${opts[@]}" --as="baguette-$l-in-fd" > "$T/rank_${l}fd_$y.txt" 2>&1
    else
      python3 -I tools/compare/challenge_rank.py "$AR/$y.json" "bench/challenge/$y.lst" "$DIR/$l/$y" "${opts[@]}" --as="baguette-$l-fd" > "$T/rank_${l}_$y.txt" 2>&1
    fi
  done
  python3 -I tools/compare/refusal_causes.py "$DIR/$l" > "$T/refusal_causes_$l.txt" 2>&1
done <<< "$arms"
python3 -I tools/compare/arms_compare.py . "${args[@]}" "${trust[@]}" "${pairs[@]}" --tsv "$T/pairs.tsv" > "$T/arms.txt" 2>&1
cp "$DIR/series.conf" "$T/series.conf"
[ -f "$DIR/monitor.log" ] && cp "$DIR/monitor.log" "$T/monitor.log"
echo "read_series: tables in $T"
