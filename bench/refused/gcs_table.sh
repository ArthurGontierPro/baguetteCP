#!/usr/bin/env bash
# M18-coverage-T9 (D-0265): GCS (with proof) and Chuffed on the population, from the runs of
# D-0211 (node07-gcs, 16 GiB, 1 200 s), joined with the population.
# usage: gcs_table.sh POPULATION.tsv RSSDIR (the extracted logs_rss_err.tgz) > gcs.tsv
# columns: id gcs_status gcs_wall gcs_obj gcs_rss_mb gcs_opb_mb gcs_pbp_gb gcs_err chuffed_status chuffed_obj chuffed_rss_mb
set -u
P=$1; R=$2
G=/cluster/arthur/baguette-results/node07-gcs
printf 'id\tgcs_status\tgcs_wall\tgcs_obj\tgcs_rss_mb\tgcs_opb_mb\tgcs_pbp_gb\tgcs_err\tchuffed_status\tchuffed_obj\tchuffed_rss_mb\n'
while IFS=$'\t' read -r id rest; do
  y=${id%%_*}
  g=$(awk -F'\t' -v i="$id" '$1==i' $G/results_G.tsv | head -1)
  h=$(awk -F'\t' -v i="$id" '$1==i' $G/results_H.tsv | head -1)
  grss=$(sed -n 's/rss_kb=//p' $R/G/$y/log/$id.gcs.rss 2> /dev/null)
  hrss=$(sed -n 's/rss_kb=//p' $R/H/$y/log/$id.chuffed.rss 2> /dev/null)
  gerr=$(grep -v '^\s*$' $R/G/$y/log/$id.gcs.err 2> /dev/null | grep -i -m1 'error\|bad_alloc\|killed\|memory' | cut -c1-80 | tr '\t' ' ')
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$id" \
    "$(echo "$g" | cut -f3)" "$(echo "$g" | cut -f4)" "$(echo "$g" | cut -f5)" \
    "$( [ -n "$grss" ] && echo $((grss / 1024)) || echo -)" \
    "$(echo "$g" | awk -F'\t' '$8 ~ /^[0-9]+$/ {printf "%d", $8/1e6; next} {print "-"}')" \
    "$(echo "$g" | awk -F'\t' '$9 ~ /^[0-9]+$/ {printf "%.1f", $9/1e9; next} {print "-"}')" \
    "${gerr:--}" \
    "$(echo "$h" | cut -f3)" "$(echo "$h" | cut -f5)" \
    "$( [ -n "$hrss" ] && echo $((hrss / 1024)) || echo -)"
done < "$P"
