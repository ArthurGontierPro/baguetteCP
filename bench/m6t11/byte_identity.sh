#!/usr/bin/env bash
# M6-T11. Two-binary BYTE-IDENTITY check: a constant-factor change must leave every
# emitted artefact unchanged. Runs each binary with --proof over every test/models/*.fzn
# (plus any extra .fzn given after the binaries), hashes the .opb, the .pbp and stdout,
# and diffs the two hash lists. Exit 0 iff zero differences.
#
# Usage:  bench/m6t11/byte_identity.sh OLD_MAIN_EXE NEW_MAIN_EXE [extra.fzn ...]
#
# MEASUREMENT ONLY, NEVER A COMMIT GATE. Copy the OLD binary out of _build first: a
# rebuild overwrites _build/default/bin/main.exe in place.
set -uo pipefail
: "${BAGUETTE_MEM_CAP_KB:=4000000}"
ulimit -v "${BAGUETTE_MEM_CAP_KB}" 2>/dev/null || true
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
[ $# -ge 2 ] || { echo "usage: $0 OLD NEW [extra.fzn ...]" >&2; exit 2; }
OLD="$1"; NEW="$2"; shift 2
WORK="$(mktemp -d "${TMPDIR:-/tmp}/byteid.XXXXXX")"
models=( "${ROOT}"/test/models/*.fzn "$@" )

run_one() { # bin tag
  local bin="$1" tag="$2" dir="${WORK}/$2"
  mkdir -p "${dir}"
  for fzn in "${models[@]}"; do
    local b; b="$(basename "${fzn}" .fzn)"
    "${bin}" "${fzn}" --proof "${dir}/${b}" > "${dir}/${b}.out" 2> "${dir}/${b}.err"
    echo "rc=$?" >> "${dir}/${b}.out"
  done
  ( cd "${dir}" && md5sum ./*.opb ./*.pbp ./*.out ) > "${WORK}/${tag}.md5"
}

echo "OLD $(md5sum < "${OLD}" | cut -d' ' -f1)  ${OLD}"
echo "NEW $(md5sum < "${NEW}" | cut -d' ' -f1)  ${NEW}"
run_one "${OLD}" old
run_one "${NEW}" new
n="$(wc -l < "${WORK}/old.md5")"
if diff "${WORK}/old.md5" "${WORK}/new.md5" > "${WORK}/diff.txt"; then
  echo "BYTE-IDENTICAL: ${n} artefacts over ${#models[@]} models (work dir ${WORK})"
  exit 0
else
  echo "DIFFERENT: $(grep -c '^<' "${WORK}/diff.txt") of ${n} artefacts differ (see ${WORK}/diff.txt)"
  exit 1
fi
