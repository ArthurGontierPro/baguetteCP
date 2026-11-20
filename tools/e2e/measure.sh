#!/usr/bin/env bash
# One instance through the end-to-end chain, every stage timed and its peak RSS taken
# (M14-e2e-verification-T8, D-0182): the first measurement of cake_pb_cp on baguette's
# SEARCH proofs, against `veripb` alone on baguette's own files.
#
#   fzn2scp.py -> cake_pb_cp (encode) -> baguette --proof -> veripb (alone, the baseline)
#   -> bridge.py -> veripb --elaborate -> cake_pb_cp (check)
#
# Usage: tools/e2e/measure.sh MODEL.fzn OUTDIR
# Env:   CAKE_PB_CP (required), BAGUETTE (use the release binary, D-0171), VERIPB (else
#        scripts/checker.sh), SOLVE_TIMEOUT (s, default 300), CHECK_TIMEOUT (s, per checking
#        stage, default 7200), KEEP=1 to keep the proofs (default: deleted once measured,
#        their sizes recorded), CAKE_HEAP (MB, default 24576: cake_pb_cp's CakeML heap,
#        whose default of 4 GB a long proof can exhaust; passed as --CML_HEAP_SIZE to both
#        of its runs, and it is reserved as virtual memory, so the RSS column is what it
#        touched).
#
# Prints ONE tab-separated line:
#   id answer verdict  t_tr rss_tr  t_enc rss_enc  t_solve rss_solve  t_veripb rss_veripb
#   t_bridge rss_bridge  t_elab rss_elab  t_cake rss_cake  opb pbp bridged core  cake_s_line
# times in seconds, RSS in MB, sizes in bytes. `verdict` is VERIFIED when cake_pb_cp's own
# `s VERIFIED ...` line states baguette's answer (chain.sh's rule, including OPT), else the
# first stage that did not end as it should (SKIPPED, SOLVE-TIMEOUT, VERIPB-REFUSED,
# BRIDGE-FAIL, ELAB-REFUSED, CAKE-REFUSED, CAKE-DISAGREES, ...). Each stage runs under
# `systemd-run --user --scope -p MemoryMax=32G` when it exists; the script's PID is in
# OUTDIR/<id>.pid while it runs (clean up by that file, never by name).
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
FZN=${1:?usage: measure.sh MODEL.fzn OUTDIR}
OUT=${2:?usage: measure.sh MODEL.fzn OUTDIR}
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
T=() # stage results, "t rss"
# stage NAME TIMEOUT CMD...: runs CMD timed, sets st_t, st_m (MB), st_rc
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
fin() {
    local verdict=$1 s=${2:-}
    while [ ${#T[@]} -lt 7 ]; do T+=("- -"); done
    # ONE write per line: several instances append to the same file at once
    local line x
    line=$(printf '%s\t%s\t%s' "$id" "${ans:--}" "$verdict")
    for x in "${T[@]}"; do line+=$(printf '\t%s\t%s' ${x}); done
    line+=$(printf '\t%s\t%s\t%s\t%s\t%s' "$(sz "$o.bag.opb")" "$(sz "$o.bag.pbp")" "$(sz "$o.bridged.pbp")" "$(sz "$o.core")" "$s")
    printf '%s\n' "$line"
    [ "${KEEP:-0}" = 1 ] || rm -f "$o.bag.pbp" "$o.bridged.pbp" "$o.core"
    rm -f "$o.pid"
    exit 0
}
ans=

CH=(--CML_HEAP_SIZE="${CAKE_HEAP:-24576}" --CML_STACK_SIZE=4096)
stage tr "$TC" python3 -I "$HERE/fzn2scp.py" "$FZN" "$o.scp" "$o.names" 2> "$o.tr.err"
T+=("$st_t $st_m")
[ "$st_rc" -eq 0 ] || fin "SKIPPED"
stage enc "$TC" bash -c 'exec "$0" "$1" "$2" "$3" > "$4" 2> "$5"' "$CK" "${CH[@]}" "$o.scp" "$o.cake.opb" "$o.cake.err"
T+=("$st_t $st_m")
[ -s "$o.cake.err" ] && fin "CAKE-ENCODE-FAIL"
opt=$(sed -n 's/.*(prob_type (\(minimize\|maximize\) .*/\1/p' "$o.scp")

# solve: the release binary, the proof, a 4 GB cap on its address space like every suite
stage solve "$TS" bash -c 'ulimit -v 4000000; exec "$0" "$1" --proof "$2" > "$3" 2> "$4"' \
    "$B" "$FZN" "$o.bag" "$o.bag.out" "$o.bag.err"
T+=("$st_t $st_m")
[ "$st_rc" -eq 124 ] && fin "SOLVE-TIMEOUT"
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

# the baseline: veripb alone on baguette's own .opb and .pbp, what the chain is compared to
stage veripb "$TC" bash -c 'exec "$0" "$1" "$2" > "$3" 2>&1' "$V" "$o.bag.opb" "$o.bag.pbp" "$o.vbag.log"
T+=("$st_t $st_m")
[ "$st_rc" -eq 124 ] && fin "VERIPB-TIMEOUT"
grep -q '^s VERIFIED' "$o.vbag.log" || fin "VERIPB-REFUSED"
stage bridge "$TC" bash -c 'exec python3 -I "$0" "$1" "$2" "$3" "$4" > "$5" 2> "$6"' \
    "$HERE/bridge.py" "$o.cake.opb" "$o.names" "$o.bag.opb" "$o.bag.pbp" "$o.bridged.pbp" "$o.bridge.err"
T+=("$st_t $st_m")
[ "$st_rc" -eq 0 ] || fin "BRIDGE-FAIL"
stage elab "$TC" bash -c 'exec "$0" "$1" "$2" --elaborate "$3" > "$4" 2>&1' \
    "$V" "$o.cake.opb" "$o.bridged.pbp" "$o.core" "$o.elab.log"
T+=("$st_t $st_m")
[ "$st_rc" -eq 124 ] && fin "ELAB-TIMEOUT"
grep -q '^s VERIFIED' "$o.elab.log" || fin "ELAB-REFUSED"
stage cake "$TC" bash -c 'exec "$0" "$1" "$2" "$3" "$4" > "$5" 2>&1' "$CK" "${CH[@]}" "$o.scp" "$o.core" "$o.check.log"
T+=("$st_t $st_m")
[ "$st_rc" -eq 124 ] && fin "CAKE-TIMEOUT"
s=$(grep -m1 '^s ' "$o.check.log")
[[ "$s" == "s VERIFIED"* ]] || fin "CAKE-REFUSED" "$(grep -m1 -i 'fail\|error' "$o.check.log" | head -c 200)"
if [ -n "$want" ]; then
    [ "$s" = "$want" ] || fin "CAKE-DISAGREES" "$s"
else
    case "$ans:$s" in
        "SAT:s VERIFIED SATISFIABLE"* | "UNSAT:s VERIFIED UNSATISFIABLE"*) ;;
        *) fin "CAKE-DISAGREES" "$s" ;;
    esac
fi
fin "VERIFIED" "$s"
