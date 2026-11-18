#!/bin/bash
# M8-bits-encoding-T3 (D-0134): hand-written checker probes for maxmin over bits (the
# SELECTOR shape) and for Ne's two-half shape, run on fataepyc-06 against VeriPB 3.0.2
# before any solver code was written. The verdicts are recorded in D-0134 section 1.
#
# Model A (a.opb, satisfiable): m in 0..7, x in 0..7 (3 bits each), y in 0..3 (2 bits),
# m = max(x, y). The conjunctive half is the two linear rows x - m <= 0, y - m <= 0 (c1,
# c2); the disjunctive half is one SELECTOR row per operand, b_i -> m <= x_i as the big-M
# row m - x_i + M_i b_i <= M_i with M_i = dhi(m) - dlo(x_i) (c3, c4), and the clause
# b_x \/ b_y (c5). Bound rows c6..c11. The pruning probed is R3 at H = 4: facts x <= 4,
# y <= 3 (declared), claim m <= 4; its trace clause is C_5 = ~m_ge_5 \/ x_ge_5.
# Usage: bash probe_t3.sh   (writes its files beside itself and runs veripb on each pair)
set -u
cd "$(dirname "$0")"
cat > a.opb <<'EOF'
* #variable= 10 #constraint= 11
@c1 -1 x_bit_0 -2 x_bit_1 -4 x_bit_2 +1 m_bit_0 +2 m_bit_1 +4 m_bit_2 >= 0 ;
@c2 -1 y_bit_0 -2 y_bit_1 +1 m_bit_0 +2 m_bit_1 +4 m_bit_2 >= 0 ;
@c3 -1 m_bit_0 -2 m_bit_1 -4 m_bit_2 +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 -7 _mx1_ge_1 >= -7 ;
@c4 -1 m_bit_0 -2 m_bit_1 -4 m_bit_2 +1 y_bit_0 +2 y_bit_1 -7 _mx2_ge_1 >= -7 ;
@c5 +1 _mx1_ge_1 +1 _mx2_ge_1 >= 1 ;
@c6 +1 m_bit_0 +2 m_bit_1 +4 m_bit_2 >= 0 ;
@c7 -1 m_bit_0 -2 m_bit_1 -4 m_bit_2 >= -7 ;
@c8 +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 >= 0 ;
@c9 -1 x_bit_0 -2 x_bit_1 -4 x_bit_2 >= -7 ;
@c10 +1 y_bit_0 +2 y_bit_1 >= 0 ;
@c11 -1 y_bit_0 -2 y_bit_1 >= -3 ;
EOF
# The same model with an objective, for the soli probes.
{ echo '* #variable= 10 #constraint= 11'; echo 'min: +1 m_bit_0 +2 m_bit_1 +4 m_bit_2 ;'; tail -n +2 a.opb; } > amin.opb
# a1: the honest R3 shape. Per operand: the selector row + the operand's bound (B2 at 5
# for x, the declared @c11 for y) + B1 of m at 5, divided by D_i = v - bound (1 for x,
# 5 - 3 = 2 for y), saturated; the clauses summed with the selector clause, saturated.
cat > a1.pbp <<'EOF'
pseudo-Boolean proof version 3.0
f 11 ;
@m1 red +1 m_bit_0 +2 m_bit_1 +4 m_bit_2 +5 ~m_ge_5 >= 5 : m_ge_5 -> 0 ;
@m2 red +1 ~m_bit_0 +2 ~m_bit_1 +4 ~m_bit_2 +3 m_ge_5 >= 3 : m_ge_5 -> 1 ;
@x1 red +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +5 ~x_ge_5 >= 5 : x_ge_5 -> 0 ;
@x2 red +1 ~x_bit_0 +2 ~x_bit_1 +4 ~x_bit_2 +3 x_ge_5 >= 3 : x_ge_5 -> 1 ;
@g pol @c3 @x2 + @m1 + s @c4 @c11 + @m1 + 2 d s + @c5 + s ;
@t ia +1 ~m_ge_5 +1 x_ge_5 >= 1 : @g ;
del id @g ;
output NONE ;
conclusion NONE ;
end pseudo-Boolean proof ;
EOF
# a2: B1 of x cited where B2 belongs (the mutation lane's wording)
sed 's/@g pol @c3 @x2 +/@g pol @c3 @x1 +/' a1.pbp > a2.pbp
# a3: the pin over-claims (a unit the derivation does not give)
sed 's/@t ia +1 ~m_ge_5 +1 x_ge_5 >= 1 : @g ;/@t ia +1 ~m_ge_5 >= 1 : @g ;/' a1.pbp > a3.pbp
# a4: the wrong selector row cited (c4 where c3 belongs)
sed 's/@g pol @c3 @x2 +/@g pol @c4 @x2 +/' a1.pbp > a4.pbp
# a5: is C_5 RUP over the selector rows, unaided? (expected: no -- the reason the pol exists)
cat > a5.pbp <<'EOF'
pseudo-Boolean proof version 3.0
f 11 ;
@m1 red +1 m_bit_0 +2 m_bit_1 +4 m_bit_2 +5 ~m_ge_5 >= 5 : m_ge_5 -> 0 ;
@m2 red +1 ~m_bit_0 +2 ~m_bit_1 +4 ~m_bit_2 +3 m_ge_5 >= 3 : m_ge_5 -> 1 ;
@x1 red +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +5 ~x_ge_5 >= 5 : x_ge_5 -> 0 ;
@x2 red +1 ~x_bit_0 +2 ~x_bit_1 +4 ~x_bit_2 +3 x_ge_5 >= 3 : x_ge_5 -> 1 ;
@t rup +1 ~m_ge_5 +1 x_ge_5 >= 1 ;
output NONE ;
conclusion NONE ;
end pseudo-Boolean proof ;
EOF
# a6: soli over bits only, with a TIE (m = x = y = 3): both selectors are left free by
# unit propagation -- does the checker accept a solution that does not fix them?
cat > a6.pbp <<'EOF'
pseudo-Boolean proof version 3.0
f 11 ;
@s soli m_bit_0 m_bit_1 ~m_bit_2 x_bit_0 x_bit_1 ~x_bit_2 y_bit_0 y_bit_1 ;
output NONE ;
conclusion NONE ;
end pseudo-Boolean proof ;
EOF
# a7: the same soli with the selectors listed (one chosen)
cat > a7.pbp <<'EOF'
pseudo-Boolean proof version 3.0
f 11 ;
@s soli m_bit_0 m_bit_1 ~m_bit_2 x_bit_0 x_bit_1 ~x_bit_2 y_bit_0 y_bit_1 _mx1_ge_1 ~_mx2_ge_1 ;
output NONE ;
conclusion NONE ;
end pseudo-Boolean proof ;
EOF
# a8: sol + conclusion SAT over bits only, with the tie
cat > a8.pbp <<'EOF'
pseudo-Boolean proof version 3.0
f 11 ;
sol m_bit_0 m_bit_1 ~m_bit_2 x_bit_0 x_bit_1 ~x_bit_2 y_bit_0 y_bit_1 ;
output NONE ;
conclusion SAT ;
end pseudo-Boolean proof ;
EOF
# a9: soli over bits only, NO tie (m = x = 3, y = 1): the selectors follow by propagation
cat > a9.pbp <<'EOF'
pseudo-Boolean proof version 3.0
f 11 ;
@s soli m_bit_0 m_bit_1 ~m_bit_2 x_bit_0 x_bit_1 ~x_bit_2 y_bit_0 ~y_bit_1 ;
output NONE ;
conclusion NONE ;
end pseudo-Boolean proof ;
EOF
# a10: soli with a WRONG solution (m = 3, x = 1, y = 1: m > max): must be refused
cat > a10.pbp <<'EOF'
pseudo-Boolean proof version 3.0
f 11 ;
@s soli m_bit_0 m_bit_1 ~m_bit_2 x_bit_0 ~x_bit_1 ~x_bit_2 y_bit_0 ~y_bit_1 ;
output NONE ;
conclusion NONE ;
end pseudo-Boolean proof ;
EOF
#
# Model C (c.opb, UNSAT at the root): m in 5..7 (2 bits of m - 5), x, y in 0..3 (2 bits),
# m = max(x, y). C_5 is the empty clause; the conflict has no fact. c3: m - x + 7 b_x <= 7
# is -M' + X' - 7 b_x >= -2 with M' = m - 5.
cat > c.opb <<'EOF'
* #variable= 8 #constraint= 11
@c1 -1 x_bit_0 -2 x_bit_1 +1 m_bit_0 +2 m_bit_1 >= -5 ;
@c2 -1 y_bit_0 -2 y_bit_1 +1 m_bit_0 +2 m_bit_1 >= -5 ;
@c3 -1 m_bit_0 -2 m_bit_1 +1 x_bit_0 +2 x_bit_1 -7 _mx1_ge_1 >= -2 ;
@c4 -1 m_bit_0 -2 m_bit_1 +1 y_bit_0 +2 y_bit_1 -7 _mx2_ge_1 >= -2 ;
@c5 +1 _mx1_ge_1 +1 _mx2_ge_1 >= 1 ;
@c6 +1 m_bit_0 +2 m_bit_1 >= 0 ;
@c7 -1 m_bit_0 -2 m_bit_1 >= -2 ;
@c8 +1 x_bit_0 +2 x_bit_1 >= 0 ;
@c9 -1 x_bit_0 -2 x_bit_1 >= -3 ;
@c10 +1 y_bit_0 +2 y_bit_1 >= 0 ;
@c11 -1 y_bit_0 -2 y_bit_1 >= -3 ;
EOF
# c1: the factless conflict: every operand at its declared bound (@c9, @c11), m at its
# declared lower bound (@c6), D_i = 5 - 3 = 2, to 0 >= 1; pinned; then rup >= 1.
cat > c1.pbp <<'EOF'
pseudo-Boolean proof version 3.0
f 11 ;
@g pol @c3 @c9 + @c6 + 2 d s @c4 @c11 + @c6 + 2 d s + @c5 + s ;
@t ia >= 1 : @g ;
del id @g ;
@z rup >= 1 ;
output NONE ;
conclusion UNSAT : @z ;
end pseudo-Boolean proof ;
EOF
# c2: rup >= 1 alone (is the selector shape refuted unaided?)
cat > c2.pbp <<'EOF'
pseudo-Boolean proof version 3.0
f 11 ;
@z rup >= 1 ;
output NONE ;
conclusion UNSAT : @z ;
end pseudo-Boolean proof ;
EOF
#
# Model E (e.opb, satisfiable, MIXED): m in 0..3 on the ladder, x in 0..7 on 3 bits,
# y in 0..3 on the ladder; m = max(x, y). M_x = M_y = 3. The pruning is R3 at H = 1:
# facts x <= 1, y <= 1, claim m <= 1; C_2 = ~m_ge_2 \/ x_ge_2 \/ y_ge_2. The order
# operands are cited through D-0132's rup bridges (B1' of m at 2, B2' of y at 2).
cat > e.opb <<'EOF'
* #variable= 11 #constraint= 11
@c1 -1 x_bit_0 -2 x_bit_1 -4 x_bit_2 +1 m_ge_1 +1 m_ge_2 +1 m_ge_3 >= 0 ;
@c2 -1 y_ge_1 -1 y_ge_2 -1 y_ge_3 +1 m_ge_1 +1 m_ge_2 +1 m_ge_3 >= 0 ;
@c3 -1 m_ge_1 -1 m_ge_2 -1 m_ge_3 +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 -3 _mx1_ge_1 >= -3 ;
@c4 -1 m_ge_1 -1 m_ge_2 -1 m_ge_3 +1 y_ge_1 +1 y_ge_2 +1 y_ge_3 -3 _mx2_ge_1 >= -3 ;
@c5 +1 _mx1_ge_1 +1 _mx2_ge_1 >= 1 ;
@c6 +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 >= 0 ;
@c7 -1 x_bit_0 -2 x_bit_1 -4 x_bit_2 >= -7 ;
@c8 +1 ~m_ge_2 +1 m_ge_1 >= 1 ;
@c9 +1 ~m_ge_3 +1 m_ge_2 >= 1 ;
@c10 +1 ~y_ge_2 +1 y_ge_1 >= 1 ;
@c11 +1 ~y_ge_3 +1 y_ge_2 >= 1 ;
EOF
cat > e1.pbp <<'EOF'
pseudo-Boolean proof version 3.0
f 11 ;
@o1 rup +1 m_ge_1 +1 m_ge_2 +1 m_ge_3 +2 ~m_ge_2 >= 2 ;
@o2 rup +1 ~y_ge_1 +1 ~y_ge_2 +1 ~y_ge_3 +2 y_ge_2 >= 2 ;
@x1 red +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +2 ~x_ge_2 >= 2 : x_ge_2 -> 0 ;
@x2 red +1 ~x_bit_0 +2 ~x_bit_1 +4 ~x_bit_2 +6 x_ge_2 >= 6 : x_ge_2 -> 1 ;
@g pol @c3 @x2 + @o1 + s @c4 @o2 + @o1 + s + @c5 + s ;
@t ia +1 ~m_ge_2 +1 x_ge_2 +1 y_ge_2 >= 1 : @g ;
del id @g ;
output NONE ;
conclusion NONE ;
end pseudo-Boolean proof ;
EOF
#
# Model G (g.opb, satisfiable): x in 0..7 (3 bits), y in 0..3 (2 bits), x + y <> 5 as
# int_lin_ne's A/B pair over the selector _ne1 (big_a = big_b = 6). The hole probed is
# x <> 3 from y = 2 (facts y >= 2, y <= 2): the clause ~x_ge_3 \/ x_ge_4 \/ ~y_ge_2 \/
# y_ge_3, as D-0130 section 7.4's two halves resolved on the selector.
cat > g.opb <<'EOF'
* #variable= 6 #constraint= 6
@c1 -1 x_bit_0 -2 x_bit_1 -4 x_bit_2 -1 y_bit_0 -2 y_bit_1 +6 _ne1_ge_1 >= -4 ;
@c2 +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +1 y_bit_0 +2 y_bit_1 -6 _ne1_ge_1 >= 0 ;
@c3 +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 >= 0 ;
@c4 -1 x_bit_0 -2 x_bit_1 -4 x_bit_2 >= -7 ;
@c5 +1 y_bit_0 +2 y_bit_1 >= 0 ;
@c6 -1 y_bit_0 -2 y_bit_1 >= -3 ;
EOF
cat > g1.pbp <<'EOF'
pseudo-Boolean proof version 3.0
f 6 ;
@x3a red +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +3 ~x_ge_3 >= 3 : x_ge_3 -> 0 ;
@x3b red +1 ~x_bit_0 +2 ~x_bit_1 +4 ~x_bit_2 +5 x_ge_3 >= 5 : x_ge_3 -> 1 ;
@x4a red +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +4 ~x_ge_4 >= 4 : x_ge_4 -> 0 ;
@x4b red +1 ~x_bit_0 +2 ~x_bit_1 +4 ~x_bit_2 +4 x_ge_4 >= 4 : x_ge_4 -> 1 ;
@y2a red +1 y_bit_0 +2 y_bit_1 +2 ~y_ge_2 >= 2 : y_ge_2 -> 0 ;
@y2b red +1 ~y_bit_0 +2 ~y_bit_1 +2 y_ge_2 >= 2 : y_ge_2 -> 1 ;
@y3a red +1 y_bit_0 +2 y_bit_1 +3 ~y_ge_3 >= 3 : y_ge_3 -> 0 ;
@y3b red +1 ~y_bit_0 +2 ~y_bit_1 +1 y_ge_3 >= 1 : y_ge_3 -> 1 ;
@g pol @c1 @x3a + @y2a + s @c2 @x4b + @y3b + s + s ;
@t ia +1 ~x_ge_3 +1 x_ge_4 +1 ~y_ge_2 +1 y_ge_3 >= 1 : @g ;
del id @g ;
output NONE ;
conclusion NONE ;
end pseudo-Boolean proof ;
EOF
# g2: the hole clause as a bare rup over the pair (expected refused: the reason for the pol)
cat > g2.pbp <<'EOF'
pseudo-Boolean proof version 3.0
f 6 ;
@x3a red +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +3 ~x_ge_3 >= 3 : x_ge_3 -> 0 ;
@x3b red +1 ~x_bit_0 +2 ~x_bit_1 +4 ~x_bit_2 +5 x_ge_3 >= 5 : x_ge_3 -> 1 ;
@x4a red +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +4 ~x_ge_4 >= 4 : x_ge_4 -> 0 ;
@x4b red +1 ~x_bit_0 +2 ~x_bit_1 +4 ~x_bit_2 +4 x_ge_4 >= 4 : x_ge_4 -> 1 ;
@y2a red +1 y_bit_0 +2 y_bit_1 +2 ~y_ge_2 >= 2 : y_ge_2 -> 0 ;
@y2b red +1 ~y_bit_0 +2 ~y_bit_1 +2 y_ge_2 >= 2 : y_ge_2 -> 1 ;
@y3a red +1 y_bit_0 +2 y_bit_1 +3 ~y_ge_3 >= 3 : y_ge_3 -> 0 ;
@y3b red +1 ~y_bit_0 +2 ~y_bit_1 +1 y_ge_3 >= 1 : y_ge_3 -> 1 ;
@t rup +1 ~x_ge_3 +1 x_ge_4 +1 ~y_ge_2 +1 y_ge_3 >= 1 ;
output NONE ;
conclusion NONE ;
end pseudo-Boolean proof ;
EOF
# g3: the A half cites B2 of x where B1 belongs (the lane's wording)
sed 's/@g pol @c1 @x3a +/@g pol @c1 @x3b +/' g1.pbp > g3.pbp
VERIPB=$HOME/.cargo/bin/veripb
run() { echo "== $1 ($2)"; "$VERIPB" "$2" "$1.pbp" 2>&1 | grep -v '^$' | tail -3; }
for p in a1 a2 a3 a4 a5 a8; do run $p a.opb; done
for p in a6 a7 a9 a10; do run $p amin.opb; done
for p in c1 c2; do run $p c.opb; done
run e1 e.opb
for p in g1 g2 g3; do run $p g.opb; done
