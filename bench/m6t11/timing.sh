#!/usr/bin/env bash
# M6-T11. Minimum wall time of N runs (default 3) per binary per model, --proof on, under
# the 4 GB cap. MEASUREMENT ONLY. The models D-0085 quotes are regenerated into a temp dir:
#   bench/m6t11/timing.sh OLD_MAIN_EXE NEW_MAIN_EXE [N]
set -uo pipefail
: "${BAGUETTE_MEM_CAP_KB:=4000000}"
ulimit -v "${BAGUETTE_MEM_CAP_KB}" 2>/dev/null || true
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
OLD="$1"; NEW="$2"; N="${3:-3}"
G="$(mktemp -d "${TMPDIR:-/tmp}/m6t11.XXXXXX")"
trap 'rm -rf "${G}"' EXIT
python3 "${ROOT}/bench/m6t11/gen.py" ne 7 0 > "${G}/ne7.fzn"
python3 "${ROOT}/bench/m6t11/gen.py" ne 7 2000 > "${G}/ne7_pad2000.fzn"
python3 "${ROOT}/bench/m6t11/gen.py" wide 400 300 400 > "${G}/wide400x300.fzn"
python3 "${ROOT}/bench/m6t11/gen.py" knap 8 2 3 1 > "${G}/knap8.fzn"
python3 "${ROOT}/bench/m6t11/gen.py" knap 10 2 3 1 > "${G}/knap10.fzn"
best() { # bin model -> min wall seconds over N runs
  local b="$1" m="$2" t best=999999
  for _ in $(seq "${N}"); do
    /usr/bin/time -o "${G}/t" -f '%e' "${b}" "${m}" --proof "${G}/run" >/dev/null 2>/dev/null
    t="$(tail -1 "${G}/t")"
    best="$(awk -v a="${t}" -v b="${best}" 'BEGIN{print (a<b)?a:b}')"
  done
  echo "${best}"
}
printf '%-26s %9s %9s %7s\n' model old_s new_s ratio
for m in "${ROOT}/test/models/width_sat_depth.fzn" "${G}"/*.fzn; do
  o="$(best "${OLD}" "${m}")"; n="$(best "${NEW}" "${m}")"
  printf '%-26s %9s %9s %7s\n' "$(basename "${m}" .fzn)" "${o}" "${n}" \
    "$(awk -v o="${o}" -v n="${n}" 'BEGIN{ if (n>0) printf "%.2fx", o/n; else print "-" }')"
done
