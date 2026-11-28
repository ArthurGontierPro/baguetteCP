#!/usr/bin/env bash
# M18-coverage-T9 (D-0265): one run of one instance, in the series' setting (D-0227 section 1):
# 16 GiB address space, --max-heap-mb 8192, MemoryMax=32G, --stats, -f.
#
# usage: run1.sh ID ARM [STOP_GIB]
#   ARM  B       proof, -f                      (arm B of D-0227)
#        D       --no-proof, -f                 (arm D)
#        Dorder  --no-proof, -f, --bits-above none
#        Dnolim  --no-proof, -f, no heap budget, MemoryMax=64G, no address-space cap (does it fit?)
#        PB      proof, -f, the memprobe binary (BAGUETTE_MEMPROBE), --max-heap-mb 65536, MemoryMax=80G
#        PD      as PB with --no-proof (both stop after the probe at STOP_GIB GiB of heap, default 8)
# env: W (work dir, default /scratch/arthur/refused-work), BIN, PROBE_BIN, TL (default 1200)
# Output: $W/runs/<ARM>/<ID>.{out,err,time,rc,pid,proofsize,probe.tsv}. Proofs are deleted after
# their size is recorded.
set -u
ID=$1; ARM=$2
[ -n "${3:-}" ] && STOP_GIB=$3   # optional third word of a queue line: the probe's stop
W=${W:-/scratch/arthur/refused-work}
BIN=${BIN:-$W/bin/main-4158b921.exe}
PROBE_BIN=${PROBE_BIN:-$W/bin/probe.exe}
TL=${TL:-1200}
FZN=$(ls $W/fzn07/flat/*/work/$ID.baguette.fzn 2> /dev/null | head -1)
O=$W/runs/$ARM; mkdir -p $O
OUT=$O/$ID
[ -n "$FZN" ] || { echo "no fzn" > $OUT.rc; exit 2; }
echo $$ > $OUT.pid
heap="--max-heap-mb 8192"; mem=32G; as=16777216; env=(); bin=$BIN
case $ARM in
  B) flags=(--proof $OUT) ;;
  D) flags=(--no-proof) ;;
  Dorder) flags=(--no-proof --bits-above none) ;;
  Dnolim) flags=(--no-proof); heap=""; mem=64G; as=unlimited ;;
  PB) flags=(--proof $OUT); heap="--max-heap-mb 65536"; mem=80G; as=unlimited; bin=$PROBE_BIN
      env=(BAGUETTE_MEMPROBE=$OUT.probe.tsv BAGUETTE_MEMPROBE_STOP_GIB=${STOP_GIB:-8}) ;;
  PD) flags=(--no-proof); heap="--max-heap-mb 65536"; mem=80G; as=unlimited; bin=$PROBE_BIN
      env=(BAGUETTE_MEMPROBE=$OUT.probe.tsv BAGUETTE_MEMPROBE_STOP_GIB=${STOP_GIB:-8}) ;;
  *) echo "bad arm $ARM"; exit 2 ;;
esac
(
  ulimit -v $as
  env "${env[@]}" systemd-run --user --scope -q -p MemoryMax=$mem \
    /usr/bin/time -v -o $OUT.time timeout -s TERM $((TL + 60)) \
    $bin --stats -f $heap --time-limit $TL "${flags[@]}" $FZN > $OUT.out 2> $OUT.err
  echo "rc=$?" > $OUT.rc
)
if [ -f $OUT.opb ] || [ -f $OUT.pbp ]; then
  ls -l $OUT.opb $OUT.pbp 2> /dev/null | awk '{print $5, $9}' > $OUT.proofsize
  rm -f $OUT.opb $OUT.pbp $OUT.opb.rows
fi
rm -f $OUT.pid
