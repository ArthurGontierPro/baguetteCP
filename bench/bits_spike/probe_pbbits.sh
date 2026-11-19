#!/bin/bash
# M8-bits-encoding, PB conflict analysis over rows with a bits term (D-0153): hand-written
# checker probes for the LIFTING SHAPE, run on fataepyc-06 against VeriPB 3.0.2 before any
# solver code was written. The verdicts are recorded in D-0153 section 1.
#
# Model M (m.opb, SATISFIABLE: x = 4, y = 7, z = 1): x, y in 0..7 on 3 bits each, z in
# 0..3 on the ladder. R1: x + z <= 5 (mixed: bits x, order z). R2: x + y >= 11 (bits only).
# The scene: the decision z >= 3; R1 pushes x <= 2 (the pivot ~x_ge_3, a BITS term pruned);
# R2 conflicts (x + y <= 9 < 11). One elimination, as lib/core/pb_analysis.ml makes it:
#   - the conflict row is INSTANTIATED at the conflict: each bits block replaced through the
#     bridge at the bound it read (x <= 2: B2 of x_ge_3; y at its declared hi: @uby);
#   - the reason row is instantiated at the PIVOT's own atom (x <= 2 pushed: B1 of x_ge_3),
#     so the pruned term is the pivot with coefficient |a| k;
#   - the reason is reduced (division by the pivot's coefficient 3) and added.
# Model S (s.opb, SATISFIABLE: x = 4, y = z = 0): the ORDER pivot in a mixed reason. R3:
# z + y <= 2, R4: x + z >= 4. The scene: the decision x <= 1; R4 pushes z >= 3 (pivot
# z_ge_1, order); R3 conflicts. The reason's bits block is instantiated at the bound x <= 1
# (B2 of x_ge_2); the reduction weakens the two non-falsified rungs.
# Usage: bash probe_pbbits.sh   (writes its files beside itself and runs veripb on each)
set -u
cd "$(dirname "$0")"
cat > m.opb <<'EOF'
* #variable= 9 #constraint= 8
@R1 -1 x_bit_0 -2 x_bit_1 -4 x_bit_2 -1 z_ge_1 -1 z_ge_2 -1 z_ge_3 >= -5 ;
@R2 +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +1 y_bit_0 +2 y_bit_1 +4 y_bit_2 >= 11 ;
@lbx +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 >= 0 ;
@ubx -1 x_bit_0 -2 x_bit_1 -4 x_bit_2 >= -7 ;
@lby +1 y_bit_0 +2 y_bit_1 +4 y_bit_2 >= 0 ;
@uby -1 y_bit_0 -2 y_bit_1 -4 y_bit_2 >= -7 ;
@L1 +1 z_ge_1 +1 ~z_ge_2 >= 1 ;
@L2 +1 z_ge_2 +1 ~z_ge_3 >= 1 ;
EOF
HEAD='pseudo-Boolean proof version 3.0
f 8 ;
@x3a red +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +3 ~x_ge_3 >= 3 : x_ge_3 -> 0 ;
@x3b red +1 ~x_bit_0 +2 ~x_bit_1 +4 ~x_bit_2 +5 x_ge_3 >= 5 : x_ge_3 -> 1 ;'
TAIL='output NONE ;
conclusion NONE ;
end pseudo-Boolean proof ;'
# p1: the honest shape. i0 = R2 + B2_3 + @uby = 5 x_ge_3 >= 2; i1 = R1 + B1_3 =
# 3 ~x_ge_3 + ~z_ge_1 + ~z_ge_2 + ~z_ge_3 >= 1; r1 = i1 / 3; l = i0 + 5 r1. The learned row
# is pinned by `ia` at level 0, as Pb_analysis.introduce writes it (emit_stating).
{ echo "$HEAD"; cat <<'EOF'
@i0 pol @R2 @x3b + @uby + ;
@e0 e +5 x_ge_3 >= 2 : @i0 ;
@i1 pol @R1 @x3a + ;
@e1 e +3 ~x_ge_3 +1 ~z_ge_1 +1 ~z_ge_2 +1 ~z_ge_3 >= 1 : @i1 ;
@r1 pol @i1 3 d ;
@l pol @i0 @r1 5 * + ;
@L ia +5 ~z_ge_1 +5 ~z_ge_2 +5 ~z_ge_3 >= 2 : @l ;
EOF
echo "$TAIL"; } > p1.pbp
# p2: B1 cited where B2 belongs in the conflict row's instantiation (the mutation lane)
sed 's/^@i0 pol @R2 @x3b + @uby + ;$/@i0 pol @R2 @x3a + @uby + ;/; /^@e0 /d' p1.pbp > p2.pbp
# p3: the reason instantiated through B2 where B1 belongs
sed 's/^@i1 pol @R1 @x3a + ;$/@i1 pol @R1 @x3b + ;/; /^@e1 /d' p1.pbp > p3.pbp
# p4: the learned row over-claimed (degree 3, i.e. z <= 1, which is TRUE in the model but
# not what this derivation gives)
sed 's/^@L ia +5 ~z_ge_1 +5 ~z_ge_2 +5 ~z_ge_3 >= 2 : @l ;$/@L ia +5 ~z_ge_1 +5 ~z_ge_2 +5 ~z_ge_3 >= 3 : @l ;/' p1.pbp > p4.pbp
# p5: B1 under the flipped witness. FIRST WRITTEN OVER m.opb AND ACCEPTED THERE: R2 forces
# x >= 4 at the root (y <= 7), so `x_ge_3 -> 1` is the right value in every model and the
# goal is autoproven -- D-0132 section 5.4's lesson again. It runs over t.opb (R1 alone:
# x = 0 is feasible), where the witness is wrong in some model.
cat > t.opb <<'EOT'
* #variable= 9 #constraint= 7
@R1 -1 x_bit_0 -2 x_bit_1 -4 x_bit_2 -1 z_ge_1 -1 z_ge_2 -1 z_ge_3 >= -5 ;
@lbx +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 >= 0 ;
@ubx -1 x_bit_0 -2 x_bit_1 -4 x_bit_2 >= -7 ;
@lby +1 y_bit_0 +2 y_bit_1 +4 y_bit_2 >= 0 ;
@uby -1 y_bit_0 -2 y_bit_1 -4 y_bit_2 >= -7 ;
@L1 +1 z_ge_1 +1 ~z_ge_2 >= 1 ;
@L2 +1 z_ge_2 +1 ~z_ge_3 >= 1 ;
EOT
{ echo 'pseudo-Boolean proof version 3.0'; echo 'f 7 ;'
  echo '@x3a red +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +3 ~x_ge_3 >= 3 : x_ge_3 -> 1 ;'
  echo "$TAIL"; } > p5.pbp
{ echo 'pseudo-Boolean proof version 3.0'; echo 'f 7 ;'
  echo '@x3a red +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +3 ~x_ge_3 >= 3 : x_ge_3 -> 0 ;'
  echo '@x3b red +1 ~x_bit_0 +2 ~x_bit_1 +4 ~x_bit_2 +5 x_ge_3 >= 5 : x_ge_3 -> 1 ;'
  echo '@i1 pol @R1 @x3a + ;'
  echo '@e1 e +3 ~x_ge_3 +1 ~z_ge_1 +1 ~z_ge_2 +1 ~z_ge_3 >= 1 : @i1 ;'
  echo "$TAIL"; } > p5ok.pbp
# p6: the ALTERNATIVE "the bits row itself as an antecedent": eliminate x's whole block
# by adding the two rows (R2 + R1: the x bits cancel exactly, no atom), y at @uby. On this
# scene the reason is TIGHT (x <= 5 - 3 exactly), so no rounding is lost.
{ echo "$HEAD"; cat <<'EOF'
@c pol @R2 @R1 + @uby + ;
@C ia +1 ~z_ge_1 +1 ~z_ge_2 +1 ~z_ge_3 >= 2 : @c ;
EOF
echo "$TAIL"; } > p6.pbp
# p7: the ALTERNATIVE "the sparse chain as the ladder of a bits term": the staircase
# X' <= 2 + 2 x_ge_3 + 3 x_ge_5 over the two minted atoms and their link, asked as a rup.
{ echo "$HEAD"; cat <<'EOF'
@x5a red +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +5 ~x_ge_5 >= 5 : x_ge_5 -> 0 ;
@x5b red +1 ~x_bit_0 +2 ~x_bit_1 +4 ~x_bit_2 +3 x_ge_5 >= 3 : x_ge_5 -> 1 ;
@k pol @x5a @x3b + s 3 d ;
@K e +1 ~x_ge_5 +1 x_ge_3 >= 1 : @k ;
@st rup -1 x_bit_0 -2 x_bit_1 -4 x_bit_2 +2 x_ge_3 +3 x_ge_5 >= -2 ;
EOF
echo "$TAIL"; } > p7.pbp
# p7w: the same staircase on 8 bits (x in 0..255, atoms at 100 and 200), where unit
# propagation over the pairs has to carry a 256-value range.
cat > w.opb <<'EOT'
* #variable= 8 #constraint= 2
@lbx +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +8 x_bit_3 +16 x_bit_4 +32 x_bit_5 +64 x_bit_6 +128 x_bit_7 >= 0 ;
@ubx -1 x_bit_0 -2 x_bit_1 -4 x_bit_2 -8 x_bit_3 -16 x_bit_4 -32 x_bit_5 -64 x_bit_6 -128 x_bit_7 >= -255 ;
EOT
XB='+1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +8 x_bit_3 +16 x_bit_4 +32 x_bit_5 +64 x_bit_6 +128 x_bit_7'
NXB='+1 ~x_bit_0 +2 ~x_bit_1 +4 ~x_bit_2 +8 ~x_bit_3 +16 ~x_bit_4 +32 ~x_bit_5 +64 ~x_bit_6 +128 ~x_bit_7'
MXB='-1 x_bit_0 -2 x_bit_1 -4 x_bit_2 -8 x_bit_3 -16 x_bit_4 -32 x_bit_5 -64 x_bit_6 -128 x_bit_7'
{ echo 'pseudo-Boolean proof version 3.0'; echo 'f 2 ;'
  echo "@a1 red $XB +100 ~x_ge_100 >= 100 : x_ge_100 -> 0 ;"
  echo "@a2 red $NXB +156 x_ge_100 >= 156 : x_ge_100 -> 1 ;"
  echo "@b1 red $XB +200 ~x_ge_200 >= 200 : x_ge_200 -> 0 ;"
  echo "@b2 red $NXB +56 x_ge_200 >= 56 : x_ge_200 -> 1 ;"
  echo '@k pol @b1 @a2 + s 101 d ;'
  echo '@K e +1 ~x_ge_200 +1 x_ge_100 >= 1 : @k ;'
  echo "@st rup $MXB +100 x_ge_100 +56 x_ge_200 >= -99 ;"
  echo "$TAIL"; } > p7w.pbp
# p8: the learned row as a bare rup (expected: accepted HERE at 3 bits, the D-0127 caveat;
# not relied on -- the analysis writes the pol)
{ echo "$HEAD"; cat <<'EOF'
@L rup +5 ~z_ge_1 +5 ~z_ge_2 +5 ~z_ge_3 >= 2 ;
EOF
echo "$TAIL"; } > p8.pbp
#
cat > s.opb <<'EOF'
* #variable= 9 #constraint= 8
@R3 -1 z_ge_1 -1 z_ge_2 -1 z_ge_3 -1 y_bit_0 -2 y_bit_1 -4 y_bit_2 >= -2 ;
@R4 +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +1 z_ge_1 +1 z_ge_2 +1 z_ge_3 >= 4 ;
@lbx +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 >= 0 ;
@ubx -1 x_bit_0 -2 x_bit_1 -4 x_bit_2 >= -7 ;
@lby +1 y_bit_0 +2 y_bit_1 +4 y_bit_2 >= 0 ;
@uby -1 y_bit_0 -2 y_bit_1 -4 y_bit_2 >= -7 ;
@L1 +1 z_ge_1 +1 ~z_ge_2 >= 1 ;
@L2 +1 z_ge_2 +1 ~z_ge_3 >= 1 ;
EOF
SHEAD='pseudo-Boolean proof version 3.0
f 8 ;
@x2a red +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +2 ~x_ge_2 >= 2 : x_ge_2 -> 0 ;
@x2b red +1 ~x_bit_0 +2 ~x_bit_1 +4 ~x_bit_2 +6 x_ge_2 >= 6 : x_ge_2 -> 1 ;'
# s1: i0 = R3 + @lby = ~z1 + ~z2 + ~z3 >= 1; i1 = R4 + B2_2 = 6 x_ge_2 + z1 + z2 + z3 >= 3;
# r1 = i1 + ~z_ge_2 + ~z_ge_3 (the two non-falsified rungs weakened; divisor 1);
# l = i0 + r1 = 6 x_ge_2 + ~z2 + ~z3 >= 1.
{ echo "$SHEAD"; cat <<'EOF'
@i0 pol @R3 @lby + ;
@i1 pol @R4 @x2b + ;
@r1 pol @i1 ~z_ge_2 + ~z_ge_3 + ;
@l pol @i0 @r1 + ;
@L ia +6 x_ge_2 +1 ~z_ge_2 +1 ~z_ge_3 >= 1 : @l ;
EOF
echo "$TAIL"; } > s1.pbp
# s2: the reason's bits block through B1 where B2 belongs
sed 's/^@i1 pol @R4 @x2b + ;$/@i1 pol @R4 @x2a + ;/' s1.pbp > s2.pbp
VERIPB=$HOME/.cargo/bin/veripb
run() { echo "== $1 ($2)"; "$VERIPB" "$2" "$1.pbp" 2>&1 | grep -v '^$' | tail -3; }
for p in p1 p2 p3 p4 p6 p7 p8; do run $p m.opb; done
for p in p5 p5ok; do run $p t.opb; done
run p7w w.opb
for p in s1 s2; do run $p s.opb; done
