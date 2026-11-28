#!/usr/bin/env bash
# M18-coverage-T9 (D-0265): wide_holders.py over the population, from one arm's stderr.
# usage: wide_all.sh ARM > wide_<ARM>.tsv   (W, default /scratch/arthur/refused-work)
W=${W:-/scratch/arthur/refused-work}
ARM=${1:-D}
D=$(cd "$(dirname "$0")" && pwd)
printf 'id\tn_wide\tsum_width\tfamilies\tn_elem_res\telem_res_width\telem_res_distinct\tother_width\n'
cut -f1 $W/population.tsv | xargs -P 8 -I{} sh -c '
  f=$(ls '"$W"'/fzn07/flat/*/work/{}.baguette.fzn 2>/dev/null | head -1)
  e='"$W"'/runs/'"$ARM"'/{}.err
  if [ -f "$e" ] && [ -n "$f" ]; then timeout 600 python3 '"$D"'/wide_holders.py "$e" "$f"; else printf "%s\tno-err\n" {}; fi'
