#!/usr/bin/env bash
# The PREFIX's share of the chain's cost (M14-e2e-verification-T8, D-0182): the bridge's
# prefix alone (baguette's .opb re-derived from cake's, no search), elaborated by veripb and
# checked by cake_pb_cp, timed with peak RSS. Run after tools/e2e/measure.sh on the same
# OUTDIR: it reads the .scp, .names, .cake.opb and .bag.opb measure.sh keeps, and needs no
# solver run, since the prefix does not depend on baguette's search proof.
#
# Usage: tools/e2e/prefix.sh OUTDIR ID
# Prints: id t_bridge t_elab rss_elab t_cake rss_cake prefix_bytes core_bytes cake_s_line
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
OUT=${1:?usage: prefix.sh OUTDIR ID}
id=${2:?usage: prefix.sh OUTDIR ID}
CK=${CAKE_PB_CP:?set CAKE_PB_CP}
TC=${CHECK_TIMEOUT:-7200}
# shellcheck source=/dev/null
. "$ROOT/scripts/checker.sh"
baguette_resolve_veripb || { echo "no checker"; exit 1; }
RUN=()
command -v systemd-run > /dev/null 2>&1 && RUN=(systemd-run --user --scope -q -p MemoryMax=32G)
o="$OUT/$id"
p="$OUT/$id.prefix"
echo $$ > "$p.pid"
t() { "${RUN[@]}" /usr/bin/time -f '%e %M' -o "$p.$1.time" timeout "$TC" bash -c "$2"; tail -1 "$p.$1.time"; }
n=$(grep -c ';' "$o.bag.opb")
printf 'pseudo-Boolean proof version 3.0\nf %s ;\noutput NONE ;\nconclusion NONE ;\nend pseudo-Boolean proof ;\n' "$n" > "$p.stub.pbp"
read -r tb _ < <(t bridge "python3 -I '$HERE/bridge.py' '$o.cake.opb' '$o.names' '$o.bag.opb' '$p.stub.pbp' > '$p.pbp'")
read -r te me < <(t elab "'$VERIPB' '$o.cake.opb' '$p.pbp' --elaborate '$p.core' > '$p.elab.log' 2>&1")
read -r tc mc < <(t cake "'$CK' --CML_HEAP_SIZE=${CAKE_HEAP:-24576} --CML_STACK_SIZE=4096 '$o.scp' '$p.core' > '$p.check.log' 2>&1")
s=$(grep -m1 '^s ' "$p.check.log")
printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$id" "$tb" "$te" "$((me / 1024))" "$tc" "$((mc / 1024))" \
    "$(stat -c %s "$p.pbp")" "$(stat -c %s "$p.core" 2> /dev/null || echo -)" "$s"
rm -f "$p.pbp" "$p.core" "$p.stub.pbp" "$p.pid"
