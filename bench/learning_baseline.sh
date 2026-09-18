#!/usr/bin/env bash
# M2-L14. THE BASELINE M2-L13 IS JUDGED AGAINST, and the instrument that produces it.
#
# Two tables, and neither is a score:
#
#   Table 1  search-tree NODES per model, with learned-constraint propagation ON and
#            OFF (BAGUETTE_PROPAGATE_LEARNED, bin/main.ml). The ablation is the whole
#            measurement: a model whose two columns are equal is a model on which
#            learning cannot be observed, whatever its node count.
#
#   Table 2  RE-DERIVED NOGOODS per model. See "why this is the real test" below.
#
# WHY M2-L14 EXISTS. Over the 39 models that predate it the suite totals 231 nodes and
# NOT ONE of them moves under the ablation -- the largest search was width_sat_depth at
# 99 nodes, and that is a width fixture, a spine rather than a search. Conflict learning
# pays off when the same conflict recurs in a DIFFERENT subtree, and a ten-node tree has
# no second subtree. So M2-L12's suite-wide zero was at least partly a statement about
# the instrument rather than about learning.
#
# WHY TABLE 2 IS THE REAL TEST, and not the node counts. A node count is circumstantial:
# a tree can shrink for reasons that have nothing to do with a learned constraint firing
# in a subtree it was not derived in. This is direct. A 1UIP nogood is BY CONSTRUCTION
# falsified by the decision path that produced it, so the search cannot re-derive the
# same nogood from within that same subtree -- to derive it a second time it must have
# reached an equivalent conflict from a path it had already refuted. So count the
# level-0 learned `rup` lines in the emitted .pbp and subtract the distinct ones. The
# difference is a COUNT of returns to an already-refuted conflict from elsewhere in the
# tree; it is the property M2-L14's obligation (c) names, measured rather than asserted.
#
# MEASUREMENT ONLY, NEVER A COMMIT GATE (bench/README.md). Node counts are exact and
# reproducible -- unlike the timings in run_bench.sh -- but a change that moves them is
# a change to be explained, not a failure to be blocked on.
#
# Usage:  bench/learning_baseline.sh [model.fzn ...]     (default: all of test/models/)
set -uo pipefail

: "${BAGUETTE_MEM_CAP_KB:=4000000}"
if [ "${BAGUETTE_MEM_CAP_KB}" != "none" ]; then
  _cur="$(ulimit -v)"
  if [ "${_cur}" = "unlimited" ] || { [ "${_cur}" -gt "${BAGUETTE_MEM_CAP_KB}" ] 2>/dev/null; }; then
    ulimit -v "${BAGUETTE_MEM_CAP_KB}" 2>/dev/null ||
      echo "warning: could not apply the ${BAGUETTE_MEM_CAP_KB} kB memory cap" >&2
  fi
  unset _cur
fi

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOLVER="${BAGUETTE:-${ROOT}/_build/default/bin/main.exe}"
if [ ! -x "${SOLVER}" ]; then
  echo "solver not built at ${SOLVER}." >&2
  echo "  dune build --root . bin/      (and note that 'dune runtest' does NOT build it)" >&2
  exit 2
fi

WORK="$(mktemp -d)"
trap 'rm -rf "${WORK}"' EXIT

if [ "$#" -gt 0 ]; then MODELS=("$@"); else MODELS=("${ROOT}"/test/models/*.fzn); fi

# Level-0 learned `rup` lines in a .pbp, as sorted literal sets: total and distinct.
# Depends on --proof-comments emitting `% level N`, which is how the level is known.
nogoods() {
  awk '
    /^% level [0-9]+$/ { lvl = $3; next }
    lvl == 0 && /^@c[0-9]+ rup .* >= 1 ;$/ {
      # `@cN rup +1 LIT +1 LIT ... >= 1 ;` -- literals sit at fields 4, 6, ... NF-3,
      # the trailing three being `>=`, `1` and `;`. Sorted into a canonical order
      # before printing, because two derivations of the same clause need not list its
      # literals in the same order and an unsorted key would call them distinct.
      m = 0
      for (i = 4; i <= NF - 3; i += 2) lit[++m] = $i
      for (i = 2; i <= m; i++) {          # insertion sort; asort() is a gawk extension
        v = lit[i]; j = i - 1
        while (j >= 1 && lit[j] > v) { lit[j+1] = lit[j]; j-- }
        lit[j+1] = v
      }
      s = ""
      for (i = 1; i <= m; i++) s = s " " lit[i]
      print s
      delete lit
    }' "$1"
}

printf '%-26s %8s %8s %7s   %8s %8s %8s\n' \
  model nodes-on nodes-off factor nogoods distinct re-derived
printf '%-26s %8s %8s %7s   %8s %8s %8s\n' \
  "-------------------------" -------- --------- ------- -------- -------- ----------

t_on=0; t_off=0; t_ng=0; t_re=0; moved=0; n_models=0

for fzn in "${MODELS[@]}"; do
  base="$(basename "${fzn}" .fzn)"
  n_models=$((n_models + 1))

  on=$(BAGUETTE_PROPAGATE_LEARNED=on "${SOLVER}" "${fzn}" --stats 2>&1 >/dev/null \
        | awk '$2 == "nodes" { print $3 }')
  off=$(BAGUETTE_PROPAGATE_LEARNED=off "${SOLVER}" "${fzn}" --stats 2>&1 >/dev/null \
        | awk '$2 == "nodes" { print $3 }')
  if [ -z "${on}" ] || [ -z "${off}" ]; then
    printf '%-26s %8s %8s\n' "${base}" "ERR" "ERR"
    continue
  fi

  # The re-derivation count is taken from the OFF build on purpose: ON is the build
  # whose whole job is to stop the re-derivation happening, so counting it there would
  # measure the fix and not the phenomenon.
  BAGUETTE_PROPAGATE_LEARNED=off "${SOLVER}" "${fzn}" \
      --proof "${WORK}/p" --proof-comments >/dev/null 2>&1
  ng=$(nogoods "${WORK}/p.pbp" | wc -l)
  dis=$(nogoods "${WORK}/p.pbp" | sort -u | wc -l)
  re=$((ng - dis))

  factor="-"
  if [ "${on}" -gt 0 ]; then
    factor=$(awk -v a="${off}" -v b="${on}" 'BEGIN { printf "%.2fx", a / b }')
  fi
  [ "${on}" -ne "${off}" ] && moved=$((moved + 1))

  printf '%-26s %8d %8d %7s   %8d %8d %8d\n' "${base}" "${on}" "${off}" "${factor}" "${ng}" "${dis}" "${re}"
  t_on=$((t_on + on)); t_off=$((t_off + off)); t_ng=$((t_ng + ng)); t_re=$((t_re + re))
done

printf '%-26s %8s %8s %7s   %8s %8s %8s\n' \
  "-------------------------" -------- --------- ------- -------- -------- ----------
printf '%-26s %8d %8d %7s   %8d %8s %8d\n' \
  "TOTAL (${n_models} models)" "${t_on}" "${t_off}" \
  "$(awk -v a="${t_off}" -v b="${t_on}" 'BEGIN { if (b > 0) printf "%.2fx", a / b; else printf "-" }')" \
  "${t_ng}" "" "${t_re}"
echo
echo "${moved} of ${n_models} models move at all under the ablation. A model that does not"
echo "move is not evidence about learning -- it is a model with no second subtree."
