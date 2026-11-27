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
# Usage: scripts/sym_lane.sh [-j N] [--big] [--chain "ARGS"] [--solver "ARGS"] [--no-base]
#                            [OUTDIR] [NAME...]   (N <= 8; OUTDIR default /tmp/baguette-sym-$$;
#                            NAMEs restrict to those instances)
#        --chain ARGS   extra symchain.py arguments, e.g. "--order search" (M15-symmetry-T3,
#                       D-0181: the chain that follows the search's variable order and value choice)
#        --solver ARGS  main.exe arguments for BOTH runs (baseline and broken), default
#                       --fixed-search (D-0261), which ARGS replaces; e.g. the
#                       dynamic search "--search activity --restarts luby --phase-saving"
#        --no-base      skip step 3 (the baseline's columns are then "-"); for a second chain
#                       over instances whose baseline another OUTDIR already measured
#
# Ends on `sym_lane: PASS`, exit 0, or `sym_lane: FAIL (n)`, exit 1, where n counts the
# instances with no result row and the rows marked FAIL.
#
# A `mzn:` source may end in `:Wmax=K`: the .dzn is copied with its `Wmax = ...;` set to K (QR48's
# weight-12 question reuses codes-cp's weight-8 file, as codes-cp's qr48orb_w12 is that file's code).
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
# SOLVER_ARGS is --fixed-search unless --solver replaces it (M19-config-T1, D-0261): the
# lane's measurements were taken on the fixed search
J=4; BIG=0; CHAIN_ARGS=""; SOLVER_ARGS="--fixed-search"; NOBASE=0
while [ $# -gt 0 ]; do
    case "$1" in
        -j) J=$2; shift 2 ;;
        -j*) J=${1#-j}; shift ;;
        --big) BIG=1; shift ;;
        --chain) CHAIN_ARGS=$2; shift 2 ;;
        --solver) SOLVER_ARGS=$2; shift 2 ;;
        --no-base) NOBASE=1; shift ;;
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
echo "sym_lane: chain [${CHAIN_ARGS}] solver [${SOLVER_ARGS}]$([ $NOBASE = 1 ] && echo ', no baseline')"
read -r -a CHAIN_A <<< "$CHAIN_ARGS"
read -r -a SOLVER_A <<< "$SOLVER_ARGS"

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
                local wmax=""
                case "$dzn" in *:Wmax=*) wmax=${dzn##*:Wmax=}; dzn=${dzn%:Wmax=*} ;; esac
                [ "${dzn#/}" = "$dzn" ] && dzn=$ROOT/bench/symmetry/$dzn
                if [ -n "$wmax" ]; then
                    sed "s/Wmax = [0-9]*;/Wmax = $wmax;/" "$dzn" > "$D/$n.dzn"
                    grep -q "Wmax = $wmax;" "$D/$n.dzn" || { echo "FAIL $n: no Wmax in $dzn"; return; }
                    dzn=$D/$n.dzn
                fi
                fzn=$D/$n.fzn
                run "$D/flatten.pid" "$MZN" -c --solver "$ROOT/tools/baguette.msc" -D "ENC=2;" \
                    "$ROOT/bench/symmetry/minweight_chk.mzn" "$dzn" -o "$fzn" >> "$L" 2>&1 ;;
    esac
    [ -s "$fzn" ] || { echo "FAIL $n: no .fzn ($src)"; return; }
    run "$D/orig.pid" "$BAGUETTE" "$fzn" --proof "$D/orig" --time-limit 0 > /dev/null 2>> "$L"
    rm -f "$D/orig.pbp"
    [ -s "$D/orig.opb" ] || { echo "FAIL $n: baguette wrote no .opb"; return; }
    if [ $NOBASE = 0 ]; then
        run "$D/base.pid" "${TIME[@]}" "$BAGUETTE" "$fzn" --proof "$D/base" --stats "${SOLVER_A[@]}" > "$D/base.log" 2>&1
        rm -f "$D/base.pbp" "$D/base.opb"
    else
        printf '=====NOBASE=====\n' > "$D/base.log"
    fi
    run "$D/chain.pid" "${TIME[@]}" "$PY" "$ROOT/tools/symmetry/symchain.py" "$fzn" "$D/orig.opb" \
        "$D/sym" --depth "$depth" "${CHAIN_A[@]}" > "$D/chain.log" 2>&1
    [ -s "$D/sym.chain.json" ] || { echo "FAIL $n: symchain: $(tail -1 "$D/chain.log")"; return; }
    run "$D/broken.pid" "${TIME[@]}" "$BAGUETTE" "$D/sym.fzn" --proof "$D/sym" --stats "${SOLVER_A[@]}" > "$D/broken.log" 2>&1
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
    [ $NOBASE = 1 ] && ba=$expect
    [ "$ba" = "$expect" ] && [ "$br" = "$expect" ] || verdict="FAIL(answers base $ba broken $br, expected $expect)"
    local stat ctl="-"
    stat=$($PY - "$D/sym.chain.json" <<'EOF'
import json, sys
J = json.load(open(sys.argv[1])); L = J["levels"]
pts = [lv for lv in L if "point" in lv]
print(L[0]["order"], len(pts), "/".join(str(lv["orbit"]) for lv in pts) or "-", len(J["cuts"]),
      J["dejavu_s"], sep="\t")
print(" ".join(lv["point"] for lv in pts) or "-", ",".join(str(lv.get("prefix_fixed", "-")) for lv in pts) or "-",
      sep="\t", file=open(sys.argv[1] + ".points", "w"))
EOF
)
    local mrg; mrg=$(grep -o '[0-9]* red, [0-9]* dom, largest witness [0-9]*' "$D/merge.log")
    if [ "$controls" = yes ]; then
        ctl=$(controls "$n" "$D")
    fi
    rm -f "$D/sym.pbp"
    [ "${SYM_KEEP:-0}" = 1 ] || rm -f "$D/merged.pbp"
    local nb wb
    nb=$(nodes "$D/base.log"); wb=$(wall "$D/base.log")
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$n" "$expect" "$stat" "$mrg" \
        "${nb:--}" "${wb:--}" "$(wall "$D/chain.log")" \
        "$(nodes "$D/broken.log")" "$(wall "$D/broken.log")" "$(wall "$D/veripb.log")" \
        "$(rss "$D/veripb.log")" "$verdict" "$ctl" "$(cat "$D/sym.chain.json.points")" > "$D/row.tsv"
    echo "$n: $verdict, controls $ctl"
}

# the four controls; prints "refused 4/4" or what got through.
# The cut: T2's, the second cut of level 1, unless the probe (symmerge --as-rup) shows it is
# already implied by the lines before it -- then every mutation of it is accepted for that reason
# alone, and the control would test nothing (D-0181). The next level-1 cut is tried, then the first.
controls() {
    local n=$1 D=$2 K="" ok=0 bad="" k
    for k in $($PY -c "import json,sys;J=json.load(open(sys.argv[1]));L=[i for i,c in enumerate(J['cuts']) if c['level']==1];print(*(L[1:]+L[:1]))" "$D/sym.chain.json"); do
        "$PY" "$ROOT/tools/symmetry/symmerge.py" "$D/sym.chain.json" "$D/orig.opb" "$D/sym.opb" \
            "$D/sym.pbp" "$D/probe.pbp" --as-rup "$k" > "$D/probe.merge.log" 2>&1
        local pl; pl=$(sed -n 's/.*MUTATED: .*, line \([0-9]*\) ->.*/\1/p' "$D/probe.merge.log")
        run "$D/ctl.pid" "$VERIPB" "$D/orig.opb" "$D/probe.pbp" > "$D/probe.veripb.log" 2>&1
        rm -f "$D/probe.pbp"
        if [ -n "$pl" ] && grep -q "Checking error at $D/probe.pbp:$pl\$" "$D/probe.veripb.log"; then
            K=$k; break
        fi
    done
    # every level-1 cut implied by the lines before it: no mutation of one can be refused, so the
    # controls cannot run on this chain. Reported as VACUOUS, not as a pass (and not a failure of the
    # pipeline: measured on php_escape_sat with search-order points pushed to 1, D-0181)
    [ -n "$K" ] || { echo "VACUOUS(every level-1 cut is implied by the lines before it)"; return; }
    local rule mut vac=""
    for rule in auto dom; do
        # can a bad cut c v X be refused at all? Not if the unit c is derivable (then c v X is a
        # weakening of it). Such a control is VACUOUS: reported, not counted (D-0181).
        "$PY" "$ROOT/tools/symmetry/symmerge.py" "$D/sym.chain.json" "$D/orig.opb" "$D/sym.opb" \
            "$D/sym.pbp" "$D/probe.pbp" --rule "$rule" --unit-probe "$K" > "$D/probe.merge.log" 2>&1
        run "$D/ctl.pid" "$VERIPB" "$D/orig.opb" "$D/probe.pbp" > "$D/unit-$rule.veripb.log" 2>&1
        rm -f "$D/probe.pbp"
        local vac_rule=0
        grep -q '^s VERIFIED' "$D/unit-$rule.veripb.log" && { vac_rule=1; vac="$vac $rule/bad-cut"; }
        for mut in bad-witness bad-cut; do
            [ "$mut" = bad-cut ] && [ $vac_rule = 1 ] && continue
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
    local tot=$((4 - $(echo $vac | wc -w)))
    if [ -z "$bad" ]; then echo "refused $ok/$tot (cut $K)${vac:+, vacuous:$vac}"; else echo "FAIL(accepted or wrong wording:$bad)"; fi
}

printf 'instance\texpect\tgroup\tlevels\torbits\tcuts\tdejavu_s\tproof_rules\tnodes_without\ts_without\tchain_s\tnodes_with\ts_with\tveripb_s\tveripb_kB\tverdict\tcontrols\tpoints\tprefix_fixed\n' > "$OUT/results.tsv"
names=()
while read -r n src depth expect controls tier; do
    case "$n" in ''|\#*) continue ;; esac
    [ "$ONLY" = "  " ] || [[ "$ONLY" == *" $n "* ]] || continue
    [ "$tier" = big ] && [ $BIG = 0 ] && [[ "$ONLY" != *" $n "* ]] && continue
    [ "$tier" = huge ] && [[ "$ONLY" != *" $n "* ]] && continue   # only when named
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
echo "sym_lane: ${#names[@]} instances, results in $OUT/results.tsv$(v=$(grep -c VACUOUS "$OUT/results.tsv"); [ "$v" -gt 0 ] && echo ", controls VACUOUS on $v")"
if [ $nf = 0 ]; then echo "sym_lane: PASS"; else echo "sym_lane: FAIL ($nf)"; exit 1; fi
