#!/bin/bash
# gen_codes.sh OUT -- the codes instances of M13-codes-leads-T1 (D-0183): Golay, QR48 and the random
# [80,40] codes of codes-cp's phase 1 (benchmark/gen/phase1.py), as .dzn -> .fzn -> baguette .opb.
# Decision instances through models/minweight_chk.mzn with ENC=2 (the parity checks as sums), the
# optimisation face through bench/lp/minweight_opt.mzn. The .opb is written by a run at
# --time-limit 0, so it is the model before any search.
set -e
OUT=${1:?OUT}; mkdir -p "$OUT"; cd "$OUT"
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../.." && pwd)
CC=${CODES_CP:-/cluster/arthur/codes-cp}
MZN=${MZN:-/scratch/arthur/mzn/MiniZincIDE-2.10.1-x86_64-linux-gnu/bin/minizinc}
BAG=${BAGUETTE:-$ROOT/_build_release/default/bin/main.exe}
# name code wmax nfix (decision: UNSAT at d-4 for QR, d-1 for random; SAT at d)
DEC="golay24_w4_f0 qr23 4 0
golay24_w8_f0 qr23 8 0
qr48_w8_f0 qr47 8 0
qr48_w8_f3 qr47 8 3
qr48_w12_f0 qr47 12 0
qr48_w12_f3 qr47 12 3
rand80s1_w8 rand80s1 8 0
rand80s1_w9 rand80s1 9 0
rand80s2_w9 rand80s2 9 0
rand80s2_w10 rand80s2 10 0
rand80s3_w9 rand80s3 9 0
rand80s3_w10 rand80s3 10 0"
OPT="golay24_min qr23
qr48_min qr47
rand80s1_min rand80s1
rand80s2_min rand80s2
rand80s3_min rand80s3"
mk() {  # name code wmax nfix model enc
  python3 "$CC/benchmark/gen/p1.py" "$2" "$3" "$4" "$1.json" > /dev/null
  python3 "$CC/benchmark/writers/write.py" "$1.json" "$1" dzn > /dev/null
  "$MZN" -c --solver "$ROOT/tools/baguette.msc" "$5" "$1.dzn" $6 -o "$1.fzn"
  "$BAG" --proof "$1" --time-limit 0 "$1.fzn" > "$1.out" 2>&1 || true
}
echo "$DEC" | while read -r nm code w f; do mk "$nm" "$code" "$w" "$f" "$CC/models/minweight_chk.mzn" "-D ENC=2"; done
echo "$OPT" | while read -r nm code; do mk "$nm" "$code" 0 0 "$HERE/minweight_opt.mzn" ""; done
ls -la *.opb
