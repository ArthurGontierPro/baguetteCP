#!/usr/bin/env bash
# M2-T6. The wake discipline's contract, measured between two binaries: STDOUT
# byte-identical on every model, and every NEW proof verifies -- proofs MAY change bytes
# (same fixpoint, different trail order). bench/m6t11/byte_identity.sh's machinery
# (each binary, --proof, every test/models/*.fzn plus extras, md5 of .opb/.pbp/stdout),
# with the verdict split by artefact kind and veripb run over every NEW proof.
#
# Usage:  bench/m2t6/identity.sh OLD_MAIN_EXE NEW_MAIN_EXE [extra.fzn ...]
# Exit 0 iff stdout is identical everywhere AND every NEW proof verifies.
# MEASUREMENT ONLY, NEVER A COMMIT GATE. Copy the OLD binary out of _build first.
set -uo pipefail
: "${BAGUETTE_MEM_CAP_KB:=4000000}"
ulimit -v "${BAGUETTE_MEM_CAP_KB}" 2>/dev/null || true
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
# shellcheck source=/dev/null
. "${ROOT}/scripts/checker.sh"
baguette_resolve_veripb || { echo "FAIL no checker" >&2; exit 2; }
[ $# -ge 2 ] || { echo "usage: $0 OLD NEW [extra.fzn ...]" >&2; exit 2; }
OLD="$1"; NEW="$2"; shift 2
WORK="$(mktemp -d "${TMPDIR:-/tmp}/m2t6id.XXXXXX")"
models=( "${ROOT}"/test/models/*.fzn "$@" )
run_one() { # bin tag
  local bin="$1" dir="${WORK}/$2" b
  mkdir -p "${dir}"
  for fzn in "${models[@]}"; do
    b="$(basename "${fzn}" .fzn)"
    "${bin}" "${fzn}" --proof "${dir}/${b}" > "${dir}/${b}.out" 2> "${dir}/${b}.err"
    echo "rc=$?" >> "${dir}/${b}.out"
  done
}
echo "OLD $(md5sum < "${OLD}" | cut -d' ' -f1)  ${OLD}"
echo "NEW $(md5sum < "${NEW}" | cut -d' ' -f1)  ${NEW}"
run_one "${OLD}" old
run_one "${NEW}" new
n=${#models[@]} out_diff=0 opb_diff=0 pbp_diff=0 bad=0 checked=0
for fzn in "${models[@]}"; do
  b="$(basename "${fzn}" .fzn)"
  cmp -s "${WORK}/old/${b}.out" "${WORK}/new/${b}.out" || { out_diff=$((out_diff+1)); echo "STDOUT-DIFF ${b}"; }
  cmp -s "${WORK}/old/${b}.opb" "${WORK}/new/${b}.opb" || { opb_diff=$((opb_diff+1)); echo "opb-diff ${b}"; }
  cmp -s "${WORK}/old/${b}.pbp" "${WORK}/new/${b}.pbp" || { pbp_diff=$((pbp_diff+1)); echo "pbp-diff ${b}"; }
  if [ -s "${WORK}/new/${b}.pbp" ]; then
    checked=$((checked+1))
    if ! "${VERIPB}" "${WORK}/new/${b}.opb" "${WORK}/new/${b}.pbp" > "${WORK}/new/${b}.chk" 2>&1; then
      bad=$((bad+1)); echo "PROOF-REJECTED ${b}"
    fi
  fi
done
echo "models=${n} stdout-differ=${out_diff} opb-differ=${opb_diff} pbp-differ=${pbp_diff} new-proofs-checked=${checked} rejected=${bad} (work dir ${WORK})"
[ "${out_diff}" -eq 0 ] && [ "${bad}" -eq 0 ]
