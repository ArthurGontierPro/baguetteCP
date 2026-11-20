#!/usr/bin/env bash
# The SYMMETRY lane (M15-symmetry-T2, D-0179): dejavu beside baguette, the breaking proved in the
# proof, on the instances of bench/symmetry/instances.tsv. Per instance, one line and a row of
# OUTDIR/results.tsv:
#
#   1. the .fzn (test/models/, or minweight_chk.mzn + .dzn flattened with ENC=2)
#   2. ORIG.opb: baguette's model without breaking (`--proof P --time-limit 0`, no search)
#   3. baseline: baguette on the .fzn with --proof --stats (answer, nodes, time; proof deleted)
#   4. tools/symmetry/symchain.py: opb2graph.py, dejavu once per level, the cuts, OUT.fzn
#   5. broken: baguette on OUT.fzn with --proof --stats
#   6. tools/symmetry/symmerge.py: the cuts re-derived (`red` with a swap, else `dom` under the
#      points' lex order) at the head of baguette's proof
#   7. veripb ORIG.opb MERGED.pbp: `s VERIFIED UNSATISFIABLE|SATISFIABLE`, agreeing with the
#      instance's expected answer and with both baguette runs. Anything else is FAIL.
#   8. controls (satisfiable models marked `yes`): on the second cut of level 1, under the rules
#      auto (red there) and dom, a wrong witness (--bad-witness) and a wrong cut (--bad-cut) must
#      each be refused AT the mutated line, in the checker's words: "Checking error at
#      FILE:LINE" and "could not be autoproven" (CLAUDE.md: assert the wording, at full strength).
#
# Usage: scripts/sym_lane.sh [-j N] [--big] [OUTDIR] [NAME...]   (N <= 8; OUTDIR default
#        /tmp/baguette-sym-$$; NAMEs restrict to those instances)
# Env:   BAGUETTE  the solver (default _build/default/bin/main.exe; NOT built here: run
#                  `dune build --root . bin/` first; its sha256 is printed)
#        DEJAVU    dejavu as distributed (default /cluster/arthur/tools/dejavu-f984485/build/dejavu,
#                  upstream main f984485, see its PROVENANCE file)
#        VERIPB    the checker (default: scripts/checker.sh's resolution)
#        MZN       MiniZinc 2.10.1 (default the bundle under /scratch/arthur/mzn/)
#        CODES_CP  codes-cp's checkout, for the big tier's .dzn (default /cluster/arthur/codes-cp)
#        SYM_TL    seconds per step (default 1800)
#        SYM_KEEP  1 keeps the merged proofs (deleted by default: QR48's is hundreds of MB)
# A missing tool is a FAILURE, never a skip. Each step runs under `systemd-run --user --scope -p
# MemoryMax=32G` (when systemd-run exists) and `timeout`, and writes OUTDIR/<name>/<step>.pid
# while it runs; the lane writes OUTDIR/lane.pid. Clean up by those PIDs only, never by name.
set -u
ROOT=$(cd "$(dirname "$0")/.." && pwd)
J=4; BIG=0
while [ $# -gt 0 ]; do
    case "$1" in
        -j) J=$2; shift 2 ;;
        -j*) J=${1#-j}; shift ;;
        --big) BIG=1; shift ;;
        *) break ;;
    esac
done
[ "$J" -le 8 ] || { echo "sym_lane: -j $J: at most 8 in parallel"; exit 2; }
OUT=${1:-/tmp/baguette-sym-$$}; [ $# -gt 0 ] && shift
ONLY=" $* "
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)
echo $$ > "$OUT/lane.pid"
trap 'rm -f "$OUT/lane.pid"' EXIT

BAGUETTE=${BAGUETTE:-$ROOT/_build/default/bin/main.exe}
export DEJAVU=${DEJAVU:-/cluster/arthur/tools/dejavu-f984485/build/dejavu}
. "$ROOT/scripts/checker.sh"
baguette_resolve_veripb || { baguette_veripb_diagnostic; echo "sym_lane: FAIL"; exit 1; }
VERIPB=$(command -v "$VERIPB")
MZN=${MZN:-/scratch/arthur/mzn/MiniZincIDE-2.10.1-x86_64-linux-gnu/bin/minizinc}
CODES_CP=${CODES_CP:-/cluster/arthur/codes-cp}
TL=${SYM_TL:-1800}
PY=${PYTHON:-python3}
fail=0
for t in "$BAGUETTE" "$DEJAVU" "$VERIPB" "$MZN"; do
    [ -x "$t" ] || { echo "sym_lane: FAIL $t is missing or not executable"; fail=1; }
done
[ $fail = 0 ] || { echo "sym_lane: FAIL"; exit 1; }
echo "sym_lane: baguette $(sha256sum "$BAGUETTE" | cut -c1-16), dejavu $(sha256sum "$DEJAVU" | cut -c1-16), $("$VERIPB" --version 2>&1 | head -1)"

if command -v systemd-run > /dev/null 2>&1; then
    RUN=(systemd-run --user --scope -q -p MemoryMax=32G)
else
    RUN=()
fi
# run PIDFILE CMD...: one step, capped, its PID in PIDFILE while it runs
run() {
    local pf=$1; shift
    "${RUN[@]}" timeout "$TL" "$@" &
    local p=$!
    echo $p > "$pf"
    wait $p
    local rc=$?
    rm -f "$pf"
    return $rc
}
answer() { grep -q '^=====UNSATISFIABLE=====' "$1" && echo UNSAT && return
           grep -q '^----------' "$1" && echo SAT && return; echo NONE; }
nodes() { awk '$1 == "stats:" && $2 == "nodes" {print $3; exit}' "$1"; }
wall() { sed -n 's/^wall \([0-9.]*\) rss.*/\1/p' "$1" | tail -1; }
rss() { sed -n 's/^wall .* rss \([0-9]*\)$/\1/p' "$1" | tail -1; }
TIME=(/usr/bin/time -f 'wall %e rss %M')

one() {
    local n=$1 src=$2 depth=$3 expect=$4 controls=$5
    local D=$OUT/$n; mkdir -p "$D"; local L=$D/lane.log; : > "$L"
    local fzn
    case "$src" in
        test:*) fzn=$ROOT/test/models/${src#test:} ;;
        mzn:*)  local dzn=${src#mzn:}; dzn=${dzn/@CODES/$CODES_CP}
                [ "${dzn#/}" = "$dzn" ] && dzn=$ROOT/bench/symmetry/$dzn
                fzn=$D/$n.fzn
                run "$D/flatten.pid" "$MZN" -c --solver "$ROOT/tools/baguette.msc" -D "ENC=2;" \
                    "$ROOT/bench/symmetry/minweight_chk.mzn" "$dzn" -o "$fzn" >> "$L" 2>&1 ;;
    esac
    [ -s "$fzn" ] || { echo "FAIL $n: no .fzn ($src)"; return; }
    run "$D/orig.pid" "$BAGUETTE" "$fzn" --proof "$D/orig" --time-limit 0 > /dev/null 2>> "$L"
    rm -f "$D/orig.pbp"
    [ -s "$D/orig.opb" ] || { echo "FAIL $n: baguette wrote no .opb"; return; }
    run "$D/base.pid" "${TIME[@]}" "$BAGUETTE" "$fzn" --proof "$D/base" --stats > "$D/base.log" 2>&1
    rm -f "$D/base.pbp" "$D/base.opb"
    run "$D/chain.pid" "${TIME[@]}" "$PY" "$ROOT/tools/symmetry/symchain.py" "$fzn" "$D/orig.opb" \
        "$D/sym" --depth "$depth" > "$D/chain.log" 2>&1
    [ -s "$D/sym.chain.json" ] || { echo "FAIL $n: symchain: $(tail -1 "$D/chain.log")"; return; }
    run "$D/broken.pid" "${TIME[@]}" "$BAGUETTE" "$D/sym.fzn" --proof "$D/sym" --stats > "$D/broken.log" 2>&1
    run "$D/merge.pid" "$PY" "$ROOT/tools/symmetry/symmerge.py" "$D/sym.chain.json" "$D/orig.opb" \
        "$D/sym.opb" "$D/sym.pbp" "$D/merged.pbp" > "$D/merge.log" 2>&1
    run "$D/veripb.pid" "${TIME[@]}" "$VERIPB" "$D/orig.opb" "$D/merged.pbp" > "$D/veripb.log" 2>&1
    local ba br v
    ba=$(answer "$D/base.log"); br=$(answer "$D/broken.log")
    v=$(grep -m1 '^s VERIFIED' "$D/veripb.log")
    local verdict=VERIFIED
    case "$expect:$v" in
        UNSAT:"s VERIFIED UNSATISFIABLE"|SAT:"s VERIFIED SATISFIABLE") ;;
        *) verdict="FAIL(veripb: $(grep -m1 -E '^s |error' "$D/veripb.log"))" ;;
    esac
    [ "$ba" = "$expect" ] && [ "$br" = "$expect" ] || verdict="FAIL(answers base $ba broken $br, expected $expect)"
    local stat ctl="-"
    stat=$($PY - "$D/sym.chain.json" <<'EOF'
import json, sys
J = json.load(open(sys.argv[1])); L = J["levels"]
pts = [lv for lv in L if "point" in lv]
print(L[0]["order"], len(pts), "/".join(str(lv["orbit"]) for lv in pts) or "-", len(J["cuts"]),
      J["dejavu_s"], sep="\t")
EOF
)
    local mrg; mrg=$(grep -o '[0-9]* red, [0-9]* dom, largest witness [0-9]*' "$D/merge.log")
    if [ "$controls" = yes ]; then
        ctl=$(controls "$n" "$D")
    fi
    rm -f "$D/sym.pbp"
    [ "${SYM_KEEP:-0}" = 1 ] || rm -f "$D/merged.pbp"
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$n" "$expect" "$stat" "$mrg" \
        "$(nodes "$D/base.log")" "$(wall "$D/base.log")" "$(wall "$D/chain.log")" \
        "$(nodes "$D/broken.log")" "$(wall "$D/broken.log")" "$(wall "$D/veripb.log")" \
        "$(rss "$D/veripb.log")" "$verdict" "$ctl" > "$D/row.tsv"
    echo "$n: $verdict, controls $ctl"
}

# the four controls; prints "refused 4/4" or what got through
controls() {
    local n=$1 D=$2 K ok=0 bad=""
    K=$($PY -c "import json,sys;J=json.load(open(sys.argv[1]));print(next((k+1 for k,c in enumerate(J['cuts']) if c['level']==1),''))" "$D/sym.chain.json")
    [ -n "$K" ] || { echo "FAIL(no level-1 cut)"; return; }
    local rule mut
    for rule in auto dom; do
        for mut in bad-witness bad-cut; do
            local m=$D/ctl-$rule-$mut
            "$PY" "$ROOT/tools/symmetry/symmerge.py" "$D/sym.chain.json" "$D/orig.opb" "$D/sym.opb" \
                "$D/sym.pbp" "$m.pbp" --rule "$rule" --$mut "$K" > "$m.merge.log" 2>&1
            local line; line=$(sed -n 's/.*MUTATED: .*, line \([0-9]*\) ->.*/\1/p' "$m.merge.log")
            run "$D/ctl.pid" "$VERIPB" "$D/orig.opb" "$m.pbp" > "$m.veripb.log" 2>&1
            if [ -n "$line" ] && grep -q "Checking error at $m.pbp:$line\$" "$m.veripb.log" \
               && grep -q "could not be autoproven" "$m.veripb.log"; then
                ok=$((ok + 1))
            else
                bad="$bad $rule/$mut"
            fi
            rm -f "$m.pbp"
        done
    done
    if [ -z "$bad" ]; then echo "refused 4/4 (cut $K)"; else echo "FAIL(accepted or wrong wording:$bad)"; fi
}

printf 'instance\texpect\tgroup\tlevels\torbits\tcuts\tdejavu_s\tproof_rules\tnodes_without\ts_without\tchain_s\tnodes_with\ts_with\tveripb_s\tveripb_kB\tverdict\tcontrols\n' > "$OUT/results.tsv"
names=()
while read -r n src depth expect controls tier; do
    case "$n" in ''|\#*) continue ;; esac
    [ "$ONLY" = "  " ] || [[ "$ONLY" == *" $n "* ]] || continue
    [ "$tier" = big ] && [ $BIG = 0 ] && [[ "$ONLY" != *" $n "* ]] && continue
    while [ "$(jobs -rp | wc -l)" -ge "$J" ]; do wait -n; done
    one "$n" "$src" "$depth" "$expect" "$controls" &
    names+=("$n")
done < "$ROOT/bench/symmetry/instances.tsv"
wait
nf=0
for n in "${names[@]}"; do
    if [ -s "$OUT/$n/row.tsv" ]; then cat "$OUT/$n/row.tsv" >> "$OUT/results.tsv"; else echo "$n: FAIL (no result row)"; nf=$((nf + 1)); fi
done
nf=$((nf + $(grep -c 'FAIL' "$OUT/results.tsv")))
echo "sym_lane: ${#names[@]} instances, results in $OUT/results.tsv"
if [ $nf = 0 ]; then echo "sym_lane: PASS"; else echo "sym_lane: FAIL ($nf)"; exit 1; fi
