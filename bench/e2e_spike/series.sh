#!/usr/bin/env bash
# The Challenge measurement of M14-e2e-verification-T8 (D-0182): tools/e2e/measure.sh over a
# list of flattened instances, at most 8 at a time (the node runs other series).
#
# Usage: bench/e2e_spike/series.sh LIST OUTDIR      LIST: one .fzn path per line, cheapest first
# Appends one line per instance to OUTDIR/results.tsv (measure.sh's columns) and writes its
# own PID to OUTDIR/series.pid; each instance's PID is OUTDIR/runs/<id>.pid while it runs.
# Clean up by those files, never by name.
set -u
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
LIST=${1:?usage: series.sh LIST OUTDIR}
OUT=${2:?usage: series.sh LIST OUTDIR}
mkdir -p "$OUT/runs"
echo $$ > "$OUT/series.pid"
trap 'rm -f "$OUT/series.pid"' EXIT
: "${CAKE_PB_CP:?set CAKE_PB_CP}" "${BAGUETTE:?set BAGUETTE to the release binary}"
{
    echo "# started $(date -Is) baguette md5 $(md5sum < "$BAGUETTE" | cut -c1-8) cake_pb_cp sha256 $(sha256sum < "$CAKE_PB_CP" | cut -c1-8)"
    echo "# id answer verdict t_tr rss_tr t_enc rss_enc t_solve rss_solve t_veripb rss_veripb t_bridge rss_bridge t_elab rss_elab t_cake rss_cake opb pbp bridged core cake_s_line"
} >> "$OUT/results.tsv"
xargs -P 8 -I{} "$ROOT/tools/e2e/measure.sh" {} "$OUT/runs" < "$LIST" >> "$OUT/results.tsv"
echo "# done $(date -Is)" >> "$OUT/results.tsv"
