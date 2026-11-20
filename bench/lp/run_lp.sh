#!/bin/bash
# run_lp.sh JOBS.tsv OUTDIR [PAR] -- run tools/lp/opb2lp.py on each job (M13-codes-leads-T1, D-0183).
# JOBS.tsv: name <TAB> path.opb <TAB> ub-or-"-" [<TAB> ub2-or-"-"] (ub: the incumbent, ub2: best known,
# both in the .opb's minimisation sense). MIPROOT=S adds HiGHS's own root (cuts, no branching). One job per line, at most PAR (default 8) at once,
# each under a 32G memory scope and a 900 s timeout. OUTDIR/NAME.json holds the result line,
# OUTDIR/NAME.err the stderr; OUTDIR/pid holds this launcher's PID (kill by that file only).
set -u
JOBS=${1:?JOBS}; OUT=${2:?OUT}; PAR=${3:-8}
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../.." && pwd)
PY=${PY:-/scratch/arthur/wave55-lp-runs/venv/bin/python}
mkdir -p "$OUT"; echo $$ > "$OUT/pid"
one() {
  local name=$1 opb=$2 ub=$3 ub2=${4:--} args=()
  [ "$ub" != "-" ] && args+=(--ub "$ub")
  [ "$ub2" != "-" ] && [ -n "$ub2" ] && args+=(--ub2 "$ub2")
  systemd-run --user --scope -q -p MemoryMax=32G \
    timeout 900 "$PY" "$ROOT/tools/lp/opb2lp.py" "$opb" --name "$name" "${args[@]}" \
    > "$OUT/$name.stdout" 2> "$OUT/$name.err"
  echo "rc=$?" >> "$OUT/$name.err"
  grep '^{' "$OUT/$name.stdout" > "$OUT/$name.json" || echo "{\"name\": \"$name\", \"failed\": true}" > "$OUT/$name.json"
  # HiGHS's own root in a process of its own: its MIP has crashed (SIGSEGV) where the LP did not
  if [ "${MIPROOT:-0}" != "0" ]; then
    systemd-run --user --scope -q -p MemoryMax=32G \
      timeout 900 "$PY" "$ROOT/tools/lp/opb2lp.py" "$opb" --name "$name" --mip-only --mip-root "$MIPROOT" \
      > "$OUT/$name.mip.stdout" 2> "$OUT/$name.mip.err"
    echo "rc=$?" >> "$OUT/$name.mip.err"
    grep '^{' "$OUT/$name.mip.stdout" > "$OUT/$name.mip" || echo "{\"mip_root_status\": \"crashed\"}" > "$OUT/$name.mip"
  fi
}
export -f one; export PY ROOT OUT MIPROOT
while IFS=$'\t' read -r name opb ub ub2; do
  while [ "$(jobs -rp | wc -l)" -ge "$PAR" ]; do wait -n; done
  one "$name" "$opb" "$ub" "$ub2" &
done < <(grep -v '^#' "$JOBS")
wait
touch "$OUT/done"
