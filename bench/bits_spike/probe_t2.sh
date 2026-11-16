#!/bin/bash
# M8-bits-encoding-T2 (D-0132): six hand-written checker probes for the bits arm, run on
# fataepyc-06 against VeriPB 3.0.2 on 2026-11-13 before any solver code was written. The
# verdicts are recorded in D-0132 section 1. Model: x in 0..5 on 3 bits (x_bit_i = bit i of
# x - 0), y in 0..3 on the ladder, R: 2x + y <= 7; the pruning x <= 2 from y >= 2.
# Usage: bash probe_t2.sh   (writes its files beside itself and runs veripb on each pair)
set -u
cd "$(dirname "$0")"
cat > m.opb <<'EOF'
* #variable= 6 #constraint= 5
@c1 -2 x_bit_0 -4 x_bit_1 -8 x_bit_2 -1 y_ge_1 -1 y_ge_2 -1 y_ge_3 >= -7 ;
@c2 +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 >= 0 ;
@c3 -1 x_bit_0 -2 x_bit_1 -4 x_bit_2 >= -5 ;
@c4 +1 ~y_ge_2 +1 y_ge_1 >= 1 ;
@c5 +1 ~y_ge_3 +1 y_ge_2 >= 1 ;
EOF
# p1: the honest shape: order bridge pair, degree-0 rup, bool bridge, red pair, mixed pol with
# ceiling division, ia pin, sparse link with e pin, a consumer rup.
cat > p1.pbp <<'EOF'
pseudo-Boolean proof version 3.0
f 5 ;
@o1 rup +1 y_ge_1 +1 y_ge_2 +1 y_ge_3 +2 ~y_ge_2 >= 2 ;
@o2 rup +1 ~y_ge_1 +1 ~y_ge_2 +1 ~y_ge_3 +2 y_ge_2 >= 2 ;
@olb rup +1 y_ge_1 +1 y_ge_2 +1 y_ge_3 >= 0 ;
@oub rup +1 ~y_ge_1 +1 ~y_ge_2 +1 ~y_ge_3 >= 0 ;
@bb rup +1 b_ge_1 +1 ~b_ge_1 >= 1 ;
@b1 red +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +3 ~x_ge_3 >= 3 : x_ge_3 -> 0 ;
@b2 red +1 ~x_bit_0 +2 ~x_bit_1 +4 ~x_bit_2 +5 x_ge_3 >= 5 : x_ge_3 -> 1 ;
@g pol @c1 @o1 1 * + 2 d @b1 + s ;
@t ia +1 ~x_ge_3 +1 ~y_ge_2 >= 1 : @g ;
del id @g ;
@a1 red +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +1 ~x_ge_1 >= 1 : x_ge_1 -> 0 ;
@a2 red +1 ~x_bit_0 +2 ~x_bit_1 +4 ~x_bit_2 +7 x_ge_1 >= 7 : x_ge_1 -> 1 ;
@l pol @b1 @a2 + s 3 d ;
@e e +1 ~x_ge_3 +1 x_ge_1 >= 1 : @l ;
@n rup +1 ~y_ge_2 +1 ~x_ge_3 +1 x_ge_1 >= 1 ;
output NONE ;
conclusion NONE ;
end pseudo-Boolean proof ;
EOF
# p2: an ia claim stronger than the derivation -> the wording
cat > p2.pbp <<'EOF'
pseudo-Boolean proof version 3.0
f 5 ;
@o1 rup +1 y_ge_1 +1 y_ge_2 +1 y_ge_3 +2 ~y_ge_2 >= 2 ;
@b1 red +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +3 ~x_ge_3 >= 3 : x_ge_3 -> 0 ;
@b2 red +1 ~x_bit_0 +2 ~x_bit_1 +4 ~x_bit_2 +5 x_ge_3 >= 5 : x_ge_3 -> 1 ;
@g pol @c1 @o1 1 * + 2 d @b1 + s ;
@t ia +1 ~x_ge_3 >= 1 : @g ;
output NONE ;
conclusion NONE ;
end pseudo-Boolean proof ;
EOF
# p3: B2 cited where B1 belongs
cat > p3.pbp <<'EOF'
pseudo-Boolean proof version 3.0
f 5 ;
@o1 rup +1 y_ge_1 +1 y_ge_2 +1 y_ge_3 +2 ~y_ge_2 >= 2 ;
@b1 red +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +3 ~x_ge_3 >= 3 : x_ge_3 -> 0 ;
@b2 red +1 ~x_bit_0 +2 ~x_bit_1 +4 ~x_bit_2 +5 x_ge_3 >= 5 : x_ge_3 -> 1 ;
@g pol @c1 @o1 1 * + 2 d @b2 + s ;
@t ia +1 ~x_ge_3 +1 ~y_ge_2 >= 1 : @g ;
output NONE ;
conclusion NONE ;
end pseudo-Boolean proof ;
EOF
# p4: B1 under the flipped witness, over a satisfiable model with the atom undecided
cat > p4.pbp <<'EOF'
pseudo-Boolean proof version 3.0
f 5 ;
@b1 red +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +3 ~x_ge_3 >= 3 : x_ge_3 -> 1 ;
@b2 red +1 ~x_bit_0 +2 ~x_bit_1 +4 ~x_bit_2 +5 x_ge_3 >= 5 : x_ge_3 -> 1 ;
output NONE ;
conclusion NONE ;
end pseudo-Boolean proof ;
EOF
# p5: ia of a clause against a UNIT (is weakening by a literal "syntactically implied"?)
cat > p5.pbp <<'EOF'
pseudo-Boolean proof version 3.0
f 5 ;
@b1 red +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +3 ~x_ge_3 >= 3 : x_ge_3 -> 0 ;
@u rup +1 ~x_ge_3 >= 1 ;
@t ia +1 ~x_ge_3 +1 ~y_ge_2 >= 1 : @u ;
output NONE ;
conclusion NONE ;
end pseudo-Boolean proof ;
EOF
# p6: B2 before B1 (the order of the pair)
cat > p6.pbp <<'EOF'
pseudo-Boolean proof version 3.0
f 5 ;
@b2 red +1 ~x_bit_0 +2 ~x_bit_1 +4 ~x_bit_2 +5 x_ge_3 >= 5 : x_ge_3 -> 1 ;
@b1 red +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +3 ~x_ge_3 >= 3 : x_ge_3 -> 0 ;
output NONE ;
conclusion NONE ;
end pseudo-Boolean proof ;
EOF
# conflict model: x in 2..5 (X' = x - 2), y in 0..3, 2x + y <= 3: -2X' - Y' >= -3 + 4 = 1, infeasible.
cat > c.opb <<'EOF'
* #variable= 6 #constraint= 5
@c1 -2 x_bit_0 -4 x_bit_1 -8 x_bit_2 -1 y_ge_1 -1 y_ge_2 -1 y_ge_3 >= 1 ;
@c2 +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 >= 0 ;
@c3 -1 x_bit_0 -2 x_bit_1 -4 x_bit_2 >= -3 ;
@c4 +1 ~y_ge_2 +1 y_ge_1 >= 1 ;
@c5 +1 ~y_ge_3 +1 y_ge_2 >= 1 ;
EOF
cat > c1.pbp <<'EOF'
pseudo-Boolean proof version 3.0
f 5 ;
@olb rup +1 y_ge_1 +1 y_ge_2 +1 y_ge_3 >= 0 ;
@g pol @c1 @c2 2 * + @olb 1 * + ;
@t ia >= 1 : @g ;
del id @g ;
@z rup >= 1 ;
output NONE ;
conclusion UNSAT : @z ;
end pseudo-Boolean proof ;
EOF
# c2: is the bare mixed row refuted unaided (D-0131's weakened_row_only shape, over bits)?
cat > c2.pbp <<'EOF'
pseudo-Boolean proof version 3.0
f 5 ;
@z rup >= 1 ;
output NONE ;
conclusion UNSAT : @z ;
end pseudo-Boolean proof ;
EOF
export PATH=$HOME/.cargo/bin:$PATH
for p in p1 p2 p3 p4 p5 p6; do echo "== $p"; veripb m.opb $p.pbp 2>&1 | grep -v '^$' | tail -3; done
for p in c1 c2; do echo "== $p"; veripb c.opb $p.pbp 2>&1 | grep -v '^$' | tail -3; done
