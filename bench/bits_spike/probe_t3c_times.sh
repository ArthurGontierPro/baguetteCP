#!/bin/bash
# M8-bits-encoding-T3 continuation, step 5 (D-0134 section 13): int_times over two WIDE
# operands, the per-value case split against the BINARY expansion of the narrower operand,
# written by hand in FlatZinc, so that the expansion is measured on the solver and the
# checker before anything is built. Both are solved at --bits-above 0 and verified.
#
#   value.fzn   x * y = z with x, y in 2..300, z = 2021: the split posts one guard Boolean
#               and two rows per value of y (299 groups), lib/core/prop/arith.ml.
#   binary.fzn  the same product over y's bits: y = 2 + sum 2^i c_i (c_i bools, 9 of them),
#               p_i = x * c_i (int_times over a 0..1 operand: two groups each, after the
#               narrower-operand rule of builder.ml), z = 2 x + sum 2^i p_i. Every row is
#               linear or a narrow int_times: no new proof shape.
# Usage: bash probe_t3c_times.sh <main.exe>
set -u
cd "$(dirname "$0")"
BIN=$1
cat > times_value.fzn <<'EOF'
var 2..300: x :: output_var;
var 2..300: y :: output_var;
var 4..90000: z;
constraint int_times(x, y, z);
constraint int_lin_eq([1], [z], 2021);
constraint int_lin_le([1, -1], [x, y], 0);
solve satisfy;
EOF
{
  echo 'var 2..300: x :: output_var;'
  echo 'var 2..300: y :: output_var;'
  echo 'var 4..90000: z;'
  for i in 0 1 2 3 4 5 6 7 8; do echo "var bool: c$i;"; echo "var 0..300: p$i;"; done
  echo 'constraint int_lin_eq([1, -1, -2, -4, -8, -16, -32, -64, -128, -256], [y, c0, c1, c2, c3, c4, c5, c6, c7, c8], 2);'
  for i in 0 1 2 3 4 5 6 7 8; do echo "constraint int_times(x, c$i, p$i);"; done
  echo 'constraint int_lin_eq([2, 1, 2, 4, 8, 16, 32, 64, 128, 256, -1], [x, p0, p1, p2, p3, p4, p5, p6, p7, p8, z], 0);'
  echo 'constraint int_lin_eq([1], [z], 2021);'
  echo 'constraint int_lin_le([1, -1], [x, y], 0);'
  echo 'solve satisfy;'
} > times_binary.fzn
VERIPB=$HOME/.cargo/bin/veripb
for m in times_value times_binary; do
  /usr/bin/time -f "%e s %M kB" "$BIN" --stats --bits-above 0 --proof "$m" "$m.fzn" > "$m.out" 2> "$m.err"
  echo "== $m: $(head -2 "$m.out" | tr '\n' ' ') opb $(stat -c %s "$m.opb") B, pbp $(stat -c %s "$m.pbp") B, solve $(tail -1 "$m.err")"
  grep -E '^stats: (opb|bits|nodes|conflicts) ' "$m.err" | cut -c1-70
  /usr/bin/time -f "verify %e s %M kB" "$VERIPB" "$m.opb" "$m.pbp" 2>&1 | grep -E '^s |rror|verify'
done
