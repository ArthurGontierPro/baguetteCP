#!/usr/bin/env bash
# M11-complexity-T1 (D-0140): every marginal profile of the inventory matrix, in one text file.
# usage: report47.sh RUNDIR > profiles.txt
# For each instance and mode: the segment 0..1 000 nodes (setup included, as recorded), then
# the MARGINAL segments 1 000..10 000 and 10 000..40 000 (agg47.py with two perf.data).
A=$(cd "$(dirname "$0")" && pwd)/agg47.py
[ -f "$A" ] || A=$(cd "$1" && pwd)/agg47.py
cd "$1/m" || exit 1
for inst in H_qr48_bag_def H_qr72_bag_def 2013_rcpsp_11 2012_mspsp_hard_01 \
  2011_cyclic-rcpsp_easy_6 2014_openshop_gp10-4; do
  for mode in np p b0np b0p; do
    [ -f "${inst}_1000_${mode}_rec.data" ] && { echo; echo "######## $inst $mode, nodes 0..1000 (setup included)"; python3 -I "$A" "${inst}_1000_${mode}_rec.data" 25; }
    [ -f "${inst}_1000_${mode}_rec.data" ] && [ -f "${inst}_10000_${mode}_rec.data" ] && { echo; echo "######## $inst $mode, MARGINAL nodes 1000..10000"; python3 -I "$A" "${inst}_1000_${mode}_rec.data" "${inst}_10000_${mode}_rec.data" 25; }
    [ -f "${inst}_10000_${mode}_rec.data" ] && [ -f "${inst}_40000_${mode}_rec.data" ] && { echo; echo "######## $inst $mode, MARGINAL nodes 10000..40000 (QR48: 10000..23367, the whole run)"; python3 -I "$A" "${inst}_10000_${mode}_rec.data" "${inst}_40000_${mode}_rec.data" 25; }
    [ ! -f "${inst}_1000_${mode}_rec.data" ] && [ -f "${inst}_10000_${mode}_rec.data" ] && { echo; echo "######## $inst $mode, nodes 0..10000 (setup included)"; python3 -I "$A" "${inst}_10000_${mode}_rec.data" 25; }
  done
done
[ -f 2014_openshop_gp10-4_1_np_rec.data ] && { echo; echo "######## 2014_openshop_gp10-4 np, SETUP ONLY (BAGUETTE_NODE_LIMIT=1)"; python3 -I "$A" 2014_openshop_gp10-4_1_np_rec.data 25; }
exit 0
