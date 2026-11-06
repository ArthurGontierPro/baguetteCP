#!/bin/bash
# run.sh -- M8-bits-encoding-T0 driver. NODE ONLY (fataepyc-06): nothing here runs
# on the laptop. Sequential by design, one checker at a time, every step under the
# harness's 16 GiB address-space cap and a per-step timeout.
#
#   run.sh <out-dir> [widths]        e.g.  run.sh /scratch/arthur/wave41-spike/out
#
# For every width x arm x style it generates the pair with gen.py, then:
#   1. veripb model.opb proof.pbp                 verdict, wall s, cpu s, max RSS
#   2. veripb -e proof.elab.pbp model.opb proof.pbp   elaborated bytes, wall, cpu, RSS
#   3. cake_pb model.opb proof.elab.pbp           verdict, wall s, cpu s, max RSS
#   4. veripb on each broken variant              verdict and the checker's wording
# and appends one row per (pair, variant) to <out-dir>/results.tsv.
#
# Verdicts are the checker's own `s ...` line, or the first line naming a checking
# error, never an exit status alone (PROOF-FORMAT section 2a: a lane that asserts a
# rejection asserts the WORDING).
set -u
OUT=${1:?usage: run.sh <out-dir> [widths]}
WIDTHS=${2:-1000,10000,100000,1000000}
VERIPB=${VERIPB:-$HOME/.cargo/bin/veripb}
CAKE=${CAKE:-/scratch/arthur/cake_pb}
TIME=/usr/bin/time
TMO=${TMO:-7200}
HERE=$(cd "$(dirname "$0")" && pwd)
ulimit -v 16777216
mkdir -p "$OUT"
cd "$OUT" || exit 2

echo "gen: $(date -Is)" >&2
python3 -I "$HERE/gen.py" --out "$OUT" --widths "$WIDTHS" > "$OUT/gen.tsv" || exit 3

TSV="$OUT/results.tsv"
printf 'width\tarm\tstyle\tvariant\topb_bytes\tpbp_bytes\tveripb_rc\tveripb_verdict\tveripb_wall_s\tveripb_cpu_s\tveripb_rss_kb\telab_bytes\telab_rc\telab_wall_s\telab_cpu_s\telab_rss_kb\tcake_rc\tcake_verdict\tcake_wall_s\tcake_cpu_s\tcake_rss_kb\n' > "$TSV"

wall_to_s() { # "h:mm:ss" or "m:ss.ss" -> seconds
  awk -F: '{ if (NF == 3) print $1*3600 + $2*60 + $3; else print $1*60 + $2 }' <<< "$1"
}

# measure NAME CMD... : runs CMD under time -v, writes NAME.out/.err/.time, prints
# "rc wall cpu rss" on stdout.
measure() {
  local name=$1; shift
  timeout "$TMO" "$TIME" -v -o "$name.time" "$@" > "$name.out" 2> "$name.err"
  local rc=$?
  local wall user sys rss
  wall=$(awk -F': ' '/Elapsed \(wall clock\)/{print $2}' "$name.time" 2>/dev/null)
  user=$(awk -F': ' '/User time/{print $2}' "$name.time" 2>/dev/null)
  sys=$(awk -F': ' '/System time/{print $2}' "$name.time" 2>/dev/null)
  rss=$(awk -F': ' '/Maximum resident/{print $2}' "$name.time" 2>/dev/null)
  local cpu
  cpu=$(awk -v u="${user:-0}" -v s="${sys:-0}" 'BEGIN{printf "%.2f", u + s}')
  echo "$rc $(wall_to_s "${wall:-0:0}") $cpu ${rss:-0}"
}

# verdict NAME : the checker's judgement line, from stdout then stderr.
verdict() {
  local name=$1 v
  v=$(grep -m1 -E '^s ' "$name.out" 2>/dev/null)
  [ -z "$v" ] && v=$(grep -m1 -E 'Checking error|Verification error|error|Error|FAIL|not implied|could not' "$name.err" "$name.out" 2>/dev/null | head -1 | sed 's/^[^:]*:[^:]*://')
  [ -z "$v" ] && v=$(tail -1 "$name.err" 2>/dev/null)
  echo "${v:-<no output>}" | tr '\t' ' ' | cut -c1-200
}

# wording NAME : the sentence after a checking error (the next non-empty line).
wording() {
  local name=$1
  grep -A3 -E 'Checking error|Verification error' "$name.err" "$name.out" 2>/dev/null \
    | grep -v -E 'Checking error|Verification error|^--$' | sed 's/^[^:]*:[^:]*://' \
    | grep -v '^[[:space:]]*$' | head -1 | cut -c1-200
}

for w in ${WIDTHS//,/ }; do
  for arm in order bits; do
    for style in rup pol; do
      d="$OUT/w$w/$arm/$style"
      [ -d "$d" ] || continue
      cd "$d" || exit 2
      opb=$(stat -c %s model.opb); pbp=$(stat -c %s proof.pbp)
      echo "== w=$w $arm $style  $(date -Is)" >&2
      read -r vrc vwall vcpu vrss < <(measure veripb "$VERIPB" --stats model.opb proof.pbp)
      vv=$(verdict veripb)
      echo "   veripb rc=$vrc $vv  wall=${vwall}s cpu=${vcpu}s rss=${vrss}kB" >&2
      ebytes=0; erc=-; ewall=-; ecpu=-; erss=-; crc=-; cv=-; cwall=-; ccpu=-; crss=-
      if [ "$vrc" = 0 ]; then
        rm -f proof.elab.pbp
        read -r erc ewall ecpu erss < <(measure elab "$VERIPB" -e proof.elab.pbp model.opb proof.pbp)
        [ -f proof.elab.pbp ] && ebytes=$(stat -c %s proof.elab.pbp)
        echo "   elab   rc=$erc bytes=$ebytes wall=${ewall}s cpu=${ecpu}s rss=${erss}kB" >&2
        if [ "$erc" = 0 ] && [ -s proof.elab.pbp ]; then
          read -r crc cwall ccpu crss < <(measure cake "$CAKE" model.opb proof.elab.pbp)
          cv=$(verdict cake)
          echo "   cake   rc=$crc $cv  wall=${cwall}s cpu=${ccpu}s rss=${crss}kB" >&2
        fi
      fi
      printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$w" "$arm" "$style" ok "$opb" "$pbp" "$vrc" "$vv" "$vwall" "$vcpu" "$vrss" \
        "$ebytes" "$erc" "$ewall" "$ecpu" "$erss" "$crc" "$cv" "$cwall" "$ccpu" "$crss" >> "$TSV"
      for b in proof.broken*.pbp; do
        [ -f "$b" ] || continue
        tag=${b#proof.}; tag=${tag%.pbp}
        read -r brc bwall bcpu brss < <(measure "$tag" "$VERIPB" model.opb "$b")
        bv=$(verdict "$tag"); bw=$(wording "$tag")
        echo "   $tag rc=$brc $bv | $bw  wall=${bwall}s" >&2
        printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
          "$w" "$arm" "$style" "$tag" "$opb" "$(stat -c %s "$b")" "$brc" "$bv | $bw" "$bwall" "$bcpu" "$brss" \
          - - - - - - - - - - >> "$TSV"
      done
    done
  done
done
echo "done: $(date -Is)" >&2
