#!/bin/bash
# M8-bits-encoding-T3 continuation (D-0134 section 8): hand-written checker probes for the
# REIFIED equality over bits, run on fataepyc-06 against VeriPB 3.0.2 before the solver
# code was written. The verdicts are recorded in D-0134 section 8.
#
# Model R (r.opb, satisfiable): x in 0..7 (3 bits), y in 0..3 (2 bits), b a bool (order,
# b_ge_1), b <-> (x + y = 5) as Encoding.add_int_lin_eq_reif's four guarded rows over the
# selector _ne1: c = 5, span 0..10, k_le = k_ge = 5, big_a = big_b = 6.
#   c1 LE  x + y + 5 b <= 10         (b = 1 -> x + y <= 5)
#   c2 GE -x - y + 5 b <= 0          (b = 1 -> x + y >= 5)
#   c3 A   x + y - 6 sel - 6 b <= 4  (b = 0, sel = 0 -> x + y <= 4)
#   c4 B  -x - y + 6 sel - 6 b <= 0  (b = 0, sel = 1 -> x + y >= 6)
# Model N (n.opb): the same with b <-> (x + y <> 5) (int_ne_reif: the guards flip).
# The reifier is an ORDER variable of width 1: its bridge is the tautology
# +1 b_ge_1 +1 ~b_ge_1 >= 1 (D-0132 section 5.3), cited x |guard coefficient|.
# Usage: bash probe_t3c.sh   (writes its files beside itself and runs veripb on each pair)
set -u
cd "$(dirname "$0")"
cat > r.opb <<'EOR'
* #variable= 7 #constraint= 8
@c1 -1 x_bit_0 -2 x_bit_1 -4 x_bit_2 -1 y_bit_0 -2 y_bit_1 -5 b_ge_1 >= -10 ;
@c2 +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +1 y_bit_0 +2 y_bit_1 -5 b_ge_1 >= 0 ;
@c3 -1 x_bit_0 -2 x_bit_1 -4 x_bit_2 -1 y_bit_0 -2 y_bit_1 +6 _ne1_ge_1 +6 b_ge_1 >= -4 ;
@c4 +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +1 y_bit_0 +2 y_bit_1 -6 _ne1_ge_1 +6 b_ge_1 >= 0 ;
@c5 +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 >= 0 ;
@c6 -1 x_bit_0 -2 x_bit_1 -4 x_bit_2 >= -7 ;
@c7 +1 y_bit_0 +2 y_bit_1 >= 0 ;
@c8 -1 y_bit_0 -2 y_bit_1 >= -3 ;
EOR
cat > n.opb <<'EOR'
* #variable= 7 #constraint= 8
@c1 -1 x_bit_0 -2 x_bit_1 -4 x_bit_2 -1 y_bit_0 -2 y_bit_1 +5 b_ge_1 >= -5 ;
@c2 +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +1 y_bit_0 +2 y_bit_1 +5 b_ge_1 >= 5 ;
@c3 -1 x_bit_0 -2 x_bit_1 -4 x_bit_2 -1 y_bit_0 -2 y_bit_1 +6 _ne1_ge_1 -6 b_ge_1 >= -10 ;
@c4 +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +1 y_bit_0 +2 y_bit_1 -6 _ne1_ge_1 -6 b_ge_1 >= -6 ;
@c5 +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 >= 0 ;
@c6 -1 x_bit_0 -2 x_bit_1 -4 x_bit_2 >= -7 ;
@c7 +1 y_bit_0 +2 y_bit_1 >= 0 ;
@c8 -1 y_bit_0 -2 y_bit_1 >= -3 ;
EOR
# The atom pairs every probe below may cite, and the reifier's tautology bridge.
PAIRS='@x3a red +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +3 ~x_ge_3 >= 3 : x_ge_3 -> 0 ;
@x3b red +1 ~x_bit_0 +2 ~x_bit_1 +4 ~x_bit_2 +5 x_ge_3 >= 5 : x_ge_3 -> 1 ;
@x4a red +1 x_bit_0 +2 x_bit_1 +4 x_bit_2 +4 ~x_ge_4 >= 4 : x_ge_4 -> 0 ;
@x4b red +1 ~x_bit_0 +2 ~x_bit_1 +4 ~x_bit_2 +4 x_ge_4 >= 4 : x_ge_4 -> 1 ;
@y2a red +1 y_bit_0 +2 y_bit_1 +2 ~y_ge_2 >= 2 : y_ge_2 -> 0 ;
@y2b red +1 ~y_bit_0 +2 ~y_bit_1 +2 y_ge_2 >= 2 : y_ge_2 -> 1 ;
@y3a red +1 y_bit_0 +2 y_bit_1 +3 ~y_ge_3 >= 3 : y_ge_3 -> 0 ;
@y3b red +1 ~y_bit_0 +2 ~y_bit_1 +1 y_ge_3 >= 1 : y_ge_3 -> 1 ;
@bt rup +1 b_ge_1 +1 ~b_ge_1 >= 1 ;'
pbp() { # pbp <name> <body>: a proof over 8 model rows with the pairs, then <body>
  { echo 'pseudo-Boolean proof version 3.0'; echo 'f 8 ;'; echo "$PAIRS"; echo "$2"
    echo 'output NONE ;'; echo 'conclusion NONE ;'; echo 'end pseudo-Boolean proof ;'; } > "$1.pbp"
}
# r1, int_eq_reif's enforce-not-hold: b = 0 (fact b <= 0) and y = 2 make x <> 3. Ne's
# two halves (probe g1 of D-0134) with the reifier as one more term in each, b's literal
# left in both parts, the selector resolved away.
R1='@g pol @c3 @x3a + @y2a + @bt 6 * + s @c4 @x4b + @y3b + @bt 6 * + s + s ;
@t ia +1 ~x_ge_3 +1 x_ge_4 +1 ~y_ge_2 +1 y_ge_3 +1 b_ge_1 >= 1 : @g ;
del id @g ;'
pbp r1 "$R1"
# r2, the ENTAILMENT face: x = 3, y = 2 entail x + y = 5, so b >= 1. The reifier's term
# carries the NEGATION of the claim (b <= 0) as the bound assumed, as maxmin's claim
# variable does (D-0134 section 2.3); the derivation is r1's and the pinned clause is the
# trace clause b_ge_1 \/ ~facts, claim first.
R2='@g pol @c3 @x3a + @y2a + @bt 6 * + s @c4 @x4b + @y3b + @bt 6 * + s + s ;
@t ia +1 b_ge_1 +1 ~x_ge_3 +1 x_ge_4 +1 ~y_ge_2 +1 y_ge_3 >= 1 : @g ;
del id @g ;'
pbp r2 "$R2"
# r3: the pin drops the reifier's literal (claims the bare disequality): must be refused
pbp r3 "$(echo "$R1" | sed 's/ +1 b_ge_1 >= 1 : @g/ >= 1 : @g/')"
# r4: part A cites B2 of x (x3b) where B1 belongs: must be refused at the ia
pbp r4 "$(echo "$R1" | sed 's/@g pol @c3 @x3a +/@g pol @c3 @x3b +/')"
# r5: the entailment clause as a bare rup over the pairs (expected accepted here at 3
# bits, as D-0134's a5/g2; not relied on)
pbp r5 '@t rup +1 b_ge_1 +1 ~x_ge_3 +1 x_ge_4 +1 ~y_ge_2 +1 y_ge_3 >= 1 ;'
# r6, enforce-hold (b = 1): LE with y >= 2 gives x <= 3, Linear's bits Combine with the
# reifier a term at its bound (D-0132 section 2.1): row, y's B1 at 2, 5 x b's bridge, x's
# atom B1 at 4, saturated.
pbp r6 '@g pol @c1 @y2a + @bt 5 * + @x4a + s ;
@t ia +1 ~x_ge_4 +1 ~y_ge_2 +1 ~b_ge_1 >= 1 : @g ;
del id @g ;'
# r7, the entailment face's REFUTATION half: b open, x >= 4 and y >= 2 refute x + y = 5
# through LE, so b <= 0: Linear's Combine over LE with b the pruned term, divided by 5.
pbp r7 '@g pol @c1 @x4a + @y2a + 5 d @bt + s ;
@t ia +1 ~b_ge_1 +1 ~x_ge_4 +1 ~y_ge_2 >= 1 : @g ;
del id @g ;'
# r8, a CONFLICT of enforce-not-hold: b = 0, x = 3, y = 2 all fixed (no claim): r1's
# derivation pins ~facts, the same clause read as the conflict's line.
pbp r8 "$R1"
# n1, int_ne_reif: b = 1 means x + y <> 5, so b = 1 and y = 2 make x <> 3; the guards
# carry +6 b, the reifier's fact is b >= 1 and its literal in the clause is ~b_ge_1.
pbp n1 '@g pol @c3 @x3a + @y2a + @bt 6 * + s @c4 @x4b + @y3b + @bt 6 * + s + s ;
@t ia +1 ~x_ge_3 +1 x_ge_4 +1 ~y_ge_2 +1 y_ge_3 +1 ~b_ge_1 >= 1 : @g ;
del id @g ;'
# n2: the same pin with the reifier literal of the wrong polarity: must be refused
pbp n2 '@g pol @c3 @x3a + @y2a + @bt 6 * + s @c4 @x4b + @y3b + @bt 6 * + s + s ;
@t ia +1 ~x_ge_3 +1 x_ge_4 +1 ~y_ge_2 +1 y_ge_3 +1 b_ge_1 >= 1 : @g ;
del id @g ;'
VERIPB=$HOME/.cargo/bin/veripb
run() { echo "== $1 ($2)"; "$VERIPB" "$2" "$1.pbp" 2>&1 | grep -v '^$' | tail -3; }
for p in r1 r2 r3 r4 r5 r6 r7 r8; do run $p r.opb; done
for p in n1 n2; do run $p n.opb; done
