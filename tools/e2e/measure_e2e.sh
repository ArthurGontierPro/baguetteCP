#!/usr/bin/env bash
# One instance through the SOLVER-WRITTEN end-to-end chain, in which baguette writes the prefix
# that re-derives its .opb from cake_pb_cp's itself, under --e2e (M14-e2e-verification-T3,
# D-0187), every stage timed with its peak RSS, for comparison with tools/e2e/measure.sh's
# bridged chain (D-0182, the first measurement of cake_pb_cp on search proofs) on the same
# instance:
#
#   fzn2scp.py -> cake_pb_cp (encode) -> baguette --e2e --proof -> veripb --elaborate
#   -> cake_pb_cp (check)                      (no bridge, no `veripb alone` baseline)
#
# and then the PREFIX alone (the solver-written head of the proof, up to its closing
# `% e2e prefix` comment, followed by `conclusion NONE`), elaborated and checked the same
# way: tools/e2e/prefix.sh's measurement, for the solver's prefix.
#
# Usage: tools/e2e/measure_e2e.sh MODEL.fzn OUTDIR
# Env:   as measure.sh: CAKE_PB_CP (required), BAGUETTE, VERIPB, SOLVE_TIMEOUT, CHECK_TIMEOUT,
#        CAKE_HEAP, KEEP; E2E_FLAGS, more solver flags, e.g. `--bits-above 64` for the bits
#        arm (M14-e2e-verification-T7, D-0196, the bits arm in the end-to-end chain).
#
# Prints ONE tab-separated line:
#   id answer verdict  t_solve rss_solve  t_elab rss_elab  t_cake rss_cake
#   pbp prefix core  t_pelab rss_pelab  t_pcake rss_pcake  cake_s_line  prefix_tally
# times in seconds, RSS in MB, sizes in bytes; `prefix_tally` is the prefix's own closing
# comment (substitutions, atom clauses, selectors, pins by kind). A model --e2e does not
# cover is `E2E-UNCOVERED` with baguette's reason in the last column. The script's PID is in
# OUTDIR/<id>.pid while it runs (clean up by that file, never by name). Exit 0 once that line
# is printed, whatever the verdict; 1 when no checker is found (`no checker`) or when an
# argument or CAKE_PB_CP is missing.
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
FZN=${1:?usage: measure_e2e.sh MODEL.fzn OUTDIR}
OUT=${2:?usage: measure_e2e.sh MODEL.fzn OUTDIR}
CK=${CAKE_PB_CP:?set CAKE_PB_CP to a built cake_pb_cp}
B=${BAGUETTE:-$ROOT/_build_release/default/bin/main.exe}
TS=${SOLVE_TIMEOUT:-300}
TC=${CHECK_TIMEOUT:-7200}
# shellcheck source=/dev/null
. "$ROOT/scripts/checker.sh"
baguette_resolve_veripb || { echo "no checker"; exit 1; }
V=$VERIPB
RUN=()
command -v systemd-run > /dev/null 2>&1 && RUN=(systemd-run --user --scope -q -p MemoryMax=32G)

id=$(basename "$FZN" .fzn)
o="$OUT/$id"
mkdir -p "$OUT"
echo $$ > "$o.pid"
stage() {
    local name=$1 to=$2
    shift 2
    "${RUN[@]}" /usr/bin/time -f '%e %M' -o "$o.$name.time" timeout "$to" "$@"
    st_rc=$?
    read -r st_t st_m < <(tail -1 "$o.$name.time" 2> /dev/null)
    st_t=${st_t:--}
    st_m=$(awk -v k="${st_m:-0}" 'BEGIN{printf "%.0f", k/1024}')
}
sz() { [ -f "$1" ] && stat -c %s "$1" || echo -; }
T=()
fin() {
    local verdict=$1 s=${2:-} tally
    while [ ${#T[@]} -lt 5 ]; do T+=("- -"); done
    tally=$(grep -m1 '^% e2e prefix' "$o.bag.pbp" 2> /dev/null | sed 's/^% e2e prefix (D-0187, contract cake_pb_cp [0-9a-f]*): //')
    local line x
    line=$(printf '%s\t%s\t%s' "$id" "${ans:--}" "$verdict")
    for x in "${T[@]:0:3}"; do line+=$(printf '\t%s\t%s' ${x}); done
    line+=$(printf '\t%s\t%s\t%s' "$(sz "$o.bag.pbp")" "$(sz "$o.prefix.pbp")" "$(sz "$o.core")")
    for x in "${T[@]:3:2}"; do line+=$(printf '\t%s\t%s' ${x}); done
    line+=$(printf '\t%s\t%s' "$s" "${tally:--}")
    printf '%s\n' "$line"
    [ "${KEEP:-0}" = 1 ] || rm -f "$o.bag.pbp" "$o.core" "$o.prefix.pbp" "$o.prefix.core"
    rm -f "$o.pid"
    exit 0
}
ans=

CH=(--CML_HEAP_SIZE="${CAKE_HEAP:-24576}" --CML_STACK_SIZE=4096)
python3 -I "$HERE/fzn2scp.py" "$FZN" "$o.scp" "$o.names" 2> "$o.tr.err" || fin "SKIPPED" "$(head -1 "$o.tr.err")"
"$CK" "${CH[@]}" "$o.scp" > "$o.cake.opb" 2> "$o.cake.err"
[ -s "$o.cake.err" ] && fin "CAKE-ENCODE-FAIL"
opt=$(sed -n 's/.*(prob_type (\(minimize\|maximize\) .*/\1/p' "$o.scp")

# E2E_FLAGS (T7, D-0196): more solver flags, `--bits-above W` for the bits arm
stage solve "$TS" bash -c 'ulimit -v 4000000; exec "$0" "$1" --proof "$2" --e2e $5 > "$3" 2> "$4"' \
    "$B" "$FZN" "$o.bag" "$o.bag.out" "$o.bag.err" "${E2E_FLAGS:-}"
T+=("$st_t $st_m")
[ "$st_rc" -eq 124 ] && fin "SOLVE-TIMEOUT"
[ "$st_rc" -eq 3 ] && grep -q '^baguette: --e2e: ' "$o.bag.err" &&
    fin "E2E-UNCOVERED" "$(sed -n 's/^baguette: --e2e: \(.*\) (D-0187).*/\1/p' "$o.bag.err" | head -1)"
[ "$st_rc" -eq 0 ] || fin "SOLVE-EXIT-$st_rc"
ans=SAT
grep -q '=====UNSATISFIABLE=====' "$o.bag.out" && ans=UNSAT
want=
if [ -n "$opt" ]; then
    if [ $ans = UNSAT ]; then
        want="s VERIFIED BOUNDS -INF <= OBJ <= +INF"
    else
        grep -qx '==========' "$o.bag.out" || fin "NOT-OPTIMAL"
        read -r lb ub <<< "$(sed -n 's/^conclusion BOUNDS \(-\?[0-9]*\) : \S* \(-\?[0-9]*\).*/\1 \2/p' "$o.bag.pbp")"
        [ -n "${ub:-}" ] && [ "$lb" = "$ub" ] || fin "NOT-OPTIMAL"
        v=$ub
        [ "$opt" = maximize ] && v=$((-ub))
        ans="OPT=$v"
        sv=${v/#-/\~}
        want="s VERIFIED BOUNDS $sv <= OBJ <= $sv"
    fi
fi
stage elab "$TC" bash -c 'exec "$0" "$1" "$2" --elaborate "$3" > "$4" 2>&1' \
    "$V" "$o.cake.opb" "$o.bag.pbp" "$o.core" "$o.elab.log"
T+=("$st_t $st_m")
el=ok
[ "$st_rc" -eq 124 ] && el=ELAB-TIMEOUT
grep -q '^s VERIFIED' "$o.elab.log" || el=${el/ok/ELAB-REFUSED}
s=
if [ $el = ok ]; then
    stage cake "$TC" bash -c 'exec "$0" "$1" "$2" "$3" "$4" > "$5" 2>&1' "$CK" "${CH[@]}" "$o.scp" "$o.core" "$o.check.log"
    T+=("$st_t $st_m")
    s=$(grep -m1 '^s ' "$o.check.log")
else
    T+=("- -")
fi
rm -f "$o.core"
# the prefix alone: every line up to and including its closing comment
awk '{print} /^% e2e prefix/ {exit}' "$o.bag.pbp" > "$o.prefix.pbp"
printf 'output NONE ;\nconclusion NONE ;\nend pseudo-Boolean proof ;\n' >> "$o.prefix.pbp"
stage pelab "$TC" bash -c 'exec "$0" "$1" "$2" --elaborate "$3" > "$4" 2>&1' \
    "$V" "$o.cake.opb" "$o.prefix.pbp" "$o.prefix.core" "$o.pelab.log"
T+=("$st_t $st_m")
stage pcake "$TC" bash -c 'exec "$0" "$1" "$2" "$3" "$4" > "$5" 2>&1' "$CK" "${CH[@]}" "$o.scp" "$o.prefix.core" "$o.pcheck.log"
T+=("$st_t $st_m")
[ $el = ok ] || fin "$el"
[[ "$s" == "s VERIFIED"* ]] || fin "CAKE-REFUSED" "$(grep -m1 -i 'fail\|error\|exhausted' "$o.check.log" | head -c 200)"
if [ -n "$want" ]; then
    [ "$s" = "$want" ] || fin "CAKE-DISAGREES" "$s"
else
    case "$ans:$s" in
        "SAT:s VERIFIED SATISFIABLE"* | "UNSAT:s VERIFIED UNSATISFIABLE"*) ;;
        *) fin "CAKE-DISAGREES" "$s" ;;
    esac
fi
fin "VERIFIED" "$s"
