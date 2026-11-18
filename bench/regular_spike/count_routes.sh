#!/bin/bash
# M7-T28 (D-0146 section 6): which of the selected Challenge instances actually REACH the new
# routes once flattened. The selection reads model sources, and a source can name `regular`
# without the flattened model calling it (gbac: zero calls). Flattens each listed instance with
# the given checkout's mznlib, the way scripts/compare_run.sh does (compat_mzn1.mzn included),
# and prints: id, baguette_regular calls, baguette_global_cardinality calls, flatten status.
# Usage: count_routes.sh <checkout> <instances.lst> <corpus-root> [par]   (on the node)
set -u
SRC=$1; LST=$2; ROOT=$3; PAR=${4:-4}
MZN=${MZN:-/scratch/arthur/mzn/MiniZincIDE-2.10.1-x86_64-linux-gnu/bin/minizinc}
export MZN_SOLVER_PATH=$SRC/tools
T=$(mktemp -d /scratch/arthur/wave49-globals-count.XXXX)
one() {
  id=$1; model=$2; data=$3
  out=$T/$id.fzn
  args=("$ROOT/$model")
  [ "$data" != "<none>" ] && [ -n "$data" ] && args+=("$ROOT/$data")
  if timeout 600 $MZN -c --solver baguette "$SRC/mznlib/compat_mzn1.mzn" "${args[@]}" -o $out > /dev/null 2>&1; then
    printf "%s\t%d\t%d\tOK\n" "$id" "$(grep -c '^constraint baguette_regular' $out)" \
      "$(grep -c '^constraint baguette_global_cardinality' $out)"
  else
    printf "%s\t-\t-\tFLATTEN-FAIL\n" "$id"
  fi
  rm -f $out
}
export -f one; export T MZN ROOT SRC
grep -v '^#' "$LST" | cut -f1-3 | xargs -P "$PAR" -L 1 bash -c 'one "$0" "$1" "$2"'
rm -rf $T
