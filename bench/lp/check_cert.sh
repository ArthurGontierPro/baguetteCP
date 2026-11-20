#!/bin/bash
# check_cert.sh FZN OUTDIR [SECONDS] [K] -- the proof shape of a root LP consequence, checked by the
# real checker (M13-codes-leads-T1, D-0183).
#  1. baguette runs FZN for SECONDS (default 5) with a proof, so the proof holds its last `soli`,
#     the constraint obj <= incumbent - 1;
#  2. tools/lp/opb2lp.py solves the root LP of the .opb and writes the `pol` lines that derive its
#     bound and K (default 2) reduced-cost fixings, each followed by an `ia` that pins the claim;
#  3. the proof is cut before its `output`/`conclusion` lines, the LP lines appended, and it
#     concludes NONE; veripb must ACCEPT;
#     With MIPSOL=S, the incumbent is instead HiGHS's best MIP point on the .opb within S seconds,
#     logged into the cut proof as `@lpsol soli <every literal>` (the checker re-checks it), so the
#     cutoff can be the optimum where baguette's own incumbent is far from it;
#  4. the controls: the same with ONE claim made one unit stronger, once per claim; veripb must
#     REJECT each, at that claim's line, in the checker's wording (an exit status alone cannot tell a judgement from a parse error).
set -u
FZN=${1:?FZN}; OUT=${2:?OUT}; T=${3:-5}; K=${4:-2}
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../.." && pwd)
PY=${PY:-/scratch/arthur/wave55-lp-runs/venv/bin/python}
BAG=${BAGUETTE:-$ROOT/_build_release/default/bin/main.exe}
VERIPB=${VERIPB:-$HOME/.cargo/bin/veripb}
mkdir -p "$OUT"; P=$OUT/$(basename "$FZN" .fzn)
# with MIPSOL the prefix holds no search (--time-limit 0): baguette's own cutoffs would refuse the point
[ -n "${MIPSOL:-}" ] && T=0
"$BAG" --proof "$P" --time-limit "$T" "$FZN" > "$P.out" 2>&1
n=$(grep -c . "$P.pbp"); head -n $((n - 3)) "$P.pbp" > "$P.lp.pbp"   # drop output/conclusion/end
if [ -n "${MIPSOL:-}" ]; then
  "$PY" "$ROOT/tools/lp/opb2lp.py" "$P.opb" --sol-out "$P.sol" --time-limit "$MIPSOL" | grep '^{' > "$P.sol.json"
  [ -s "$P.sol" ] || { echo "no MIP solution"; exit 1; }
  cat "$P.sol" >> "$P.lp.pbp"
  UB=$(python3 -c "import json; print(round(json.load(open('$P.sol.json'))['sol_value']))"); CUT=@lpsol
else
  INC=$(grep -o 'incumbent=[-0-9]*' "$P.out" | tail -1 | cut -d= -f2)
  CUT=$(grep -E '^@[A-Za-z0-9_]+ soli ' "$P.pbp" | tail -1 | cut -d' ' -f1)
  [ -n "$INC" ] && [ -n "$CUT" ] || { echo "no incumbent or no soli in $P.pbp"; exit 1; }
  # the incumbent baguette prints is the FlatZinc value; the .opb minimises, so a maximisation is negated
  grep -q 'maximize' "$FZN" && UB=$((-INC)) || UB=$INC
fi
echo "cutoff $CUT: obj <= $UB - 1"
"$PY" "$ROOT/tools/lp/opb2lp.py" "$P.opb" --ub "$UB" --cert "$K" --cutoff "$CUT" --cert-out "$P.cert" | grep '^{' > "$P.lp.json"
cp "$P.lp.pbp" "$P.base.pbp"
cat "$P.cert" >> "$P.lp.pbp"
printf 'output NONE ;\nconclusion NONE ;\nend pseudo-Boolean proof ;\n' >> "$P.lp.pbp"
/usr/bin/time -f '%e s %M KB' "$VERIPB" "$P.opb" "$P.lp.pbp" > "$P.lp.veripb" 2>&1; echo "accept-run rc=$?" | tee -a "$P.lp.veripb"
# the controls, one per claim: that `ia` alone one unit stronger (its right-hand side + 1)
nia=$(grep -c '^ia ' "$P.cert")
for k in $(seq 1 "$nia"); do
  cp "$P.base.pbp" "$P.bad$k.pbp"
  awk -v k="$k" '/^ia /{ c++; if (c == k) for (i = 1; i <= NF; i++) if ($i == ">=") { $(i+1) = $(i+1) + 1; break } } { print }' "$P.cert" >> "$P.bad$k.pbp"
  printf 'output NONE ;\nconclusion NONE ;\nend pseudo-Boolean proof ;\n' >> "$P.bad$k.pbp"
  "$VERIPB" "$P.opb" "$P.bad$k.pbp" > "$P.bad$k.veripb" 2>&1; rc=$?
  at=$(grep -m1 -oE '(Checking|Verification) error at [^ ]*' "$P.bad$k.veripb" | sed 's/.*://')
  why=$(grep -m1 -E 'not syntactically implied|could not|falsifies' "$P.bad$k.veripb" | sed 's/^[[:space:]]*//')
  want=$(( $(grep -c '' "$P.base.pbp") + $(grep -n '^ia ' "$P.cert" | sed -n "${k}p" | cut -d: -f1) ))
  echo "control $k/$nia rc=$rc, rejected at line ${at:-none} (the claim is line $want): ${why:-NO checker judgement}"
  rm -f "$P.bad$k.pbp"
done
rm -f "$P.base.pbp"
grep -c '^ia ' "$P.cert" | sed 's/^/ia lines: /'
cat "$P.lp.json"
