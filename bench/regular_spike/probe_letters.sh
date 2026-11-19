#!/bin/bash
# M7-T28 (D-0151 section 1): run gen_letters_probe.py's proofs through VeriPB 3.0.2 on
# fataepyc-06. Every ok<k>.pbp must be accepted; each nf<k>_<j>.pbp (the last fact of one line
# dropped) and nl<k>.pbp (the flag lines removed) is reported as refused at the RUP wording,
# accepted, or refused otherwise -- the counts are D-0151's, not a pass/fail of this script.
# Usage: bash probe_letters.sh [outdir] [n] [seed]
set -u
here="$(cd "$(dirname "$0")" && pwd)"
out="${1:-$here/out-letters}"
n="${2:-60}"
seed="${3:-7}"
rm -rf "$out"
mkdir -p "$out"
python3 -I "$here/gen_letters_probe.py" "$out" "$n" "$seed" || exit 1
VERIPB="${VERIPB:-$HOME/.cargo/bin/veripb}"
RUP='The constraint is not implied by reverse unit propagation (RUP) from core and derived database.'
verdict() {
  local m="$1" p="$2" msg rc
  msg=$("$VERIPB" "$m" "$p" 2>&1)
  rc=$?
  if [ $rc -eq 0 ]; then
    echo accepted
  elif printf '%s' "$msg" | grep -qF "$RUP"; then
    echo refused-rup
  else
    echo "refused-other: $(printf '%s' "$msg" | grep -i -m1 -E 'error|fail')"
  fi
}
ok_acc=0
ok_bad=0
for p in "$out"/ok*.pbp; do
  k=$(basename "$p" .pbp | sed 's/^ok//')
  v=$(verdict "$out/m$k.opb" "$p")
  if [ "$v" = accepted ]; then ok_acc=$((ok_acc + 1)); else ok_bad=$((ok_bad + 1)); echo "OK-REFUSED ok$k: $v"; fi
done
echo "ok: $ok_acc accepted, $ok_bad refused"
for kind in nf nl; do
  : > "$out/$kind.verdicts"
  for p in "$out"/$kind*.pbp; do
    [ -e "$p" ] || continue
    b=$(basename "$p" .pbp)
    k=$(echo "$b" | sed -E "s/^$kind([0-9]+).*/\1/")
    echo "$b $(verdict "$out/m$k.opb" "$p")" >> "$out/$kind.verdicts"
  done
  echo "$kind: $(cut -d' ' -f2 "$out/$kind.verdicts" | sort | uniq -c | tr '\n' ' ')"
done
