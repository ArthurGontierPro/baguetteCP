% M18-coverage-T5 (docs/DECISIONS.md D-0239): lex_lesseq and lex_less over integers as
% LINEAR ROWS over one 0..1 flag per position, in place of std's reified chain.
%
% MiniZinc 2.10.1's std (stdlib_internal.mzn, lex_lesseq_std_decomposition) writes
%   b[i] = (x[i] <= y[i] /\ (x[i] < y[i] \/ b[i + 1]))
% with b[0] the constraint and b[n] the tail (true for lex_lesseq when x is not the longer
% array, true for lex_less when x is the shorter one). Flattened, that is per position two
% int_lin_le_reif (four big-M rows and two reified Booleans), an array_bool_and and three
% bool_clauses, about five propagator instances.
%
% Here b[i] says the same thing ("x[i..] <=lex y[i..] given the tail") and is a var 0..1,
% b[1] the constant 1 and b[n + 1] the tail, so the definition is four int_lin_le rows per
% position, each the big-M form of one implication:
%   R1  b[i]                  -> x[i] <= y[i]
%   R2  b[i] /\ not b[i + 1]  -> x[i] <  y[i]
%   R3  not b[i]              -> x[i] >= y[i]
%   R4  not b[i] /\ b[i + 1]  -> x[i] >  y[i]
% R1 and R2 are b[i] -> (x[i] <= y[i] /\ (x[i] < y[i] \/ b[i + 1])), R3 and R4 the converse,
% so b is functionally determined by x and y, as std's is: the solutions over (x, y, b) are
% std's, one for one. A row that a constant end makes trivial is not written (R3 and R4 at
% i = 1, R2 at the last position when the tail is true, R1 when it is false, ...).
% Every row is an int_lin_le, lib/core/prop/linear.ml's, bounds consistent and justified
% by its own pol; no new builtin.
%
% With bounds consistency on the rows this prunes what Frisch et al.'s GAC algorithm prunes:
% the values it removes are bounds of x[alpha] and y[alpha] (alpha the first position not
% fixed equal), b[alpha] is 1 by R2 down the fixed-equal prefix, and b[beta] is 0 by R1 or by
% R2 once b[beta + 1] is (beta the first position from which the suffix cannot be <=lex).
% The big-M constants are the declared bounds' (ub(x) - lb(y) + 1 and ub(y) - lb(x) + 1), so a
% variable without bounds keeps std's text.
%
% lex_greater, lex_greatereq, lex_chain_* and lex2 reach these through std. The Boolean and the
% reified forms keep std's text (fzn_lex_less(eq)_bool, fzn_lex_less(eq)_int_reif).

predicate baguette_lex_rows(array [int] of var int: xs, array [int] of var int: ys, bool: tail) =
  let {
    array [int] of var int: x = array1d(xs);
    array [int] of var int: y = array1d(ys);
    int: n = min(length(x), length(y));
  } in
  if n = 0 then
    tail
  elseif not forall (i in 1..n) (has_bounds(x[i]) /\ has_bounds(y[i])) then
    if tail then lex_lesseq_std_decomposition(xs, ys) else lex_less_std_decomposition(xs, ys) endif
  else
    let {
      array [2..n] of var 0..1: bm;
      array [1..n + 1] of var 0..1: b = [1] ++ [bm[i] | i in 2..n] ++ [bool2int(tail)];
    } in
    forall (i in 1..n) (
      let {
        int: m = max(0, ub(x[i]) - lb(y[i]) + 1);
        int: k = max(0, ub(y[i]) - lb(x[i]) + 1);
      } in
      (if i = n /\ not tail then true else x[i] - y[i] + (m - 1) * b[i] <= m - 1 endif) /\
      (if i = n /\ tail then true else x[i] - y[i] + m * b[i] - m * b[i + 1] <= m - 1 endif) /\
      (if i = 1 \/ (i = n /\ tail) then true else y[i] - x[i] - (k - 1) * b[i] <= 0 endif) /\
      (if i = 1 \/ (i = n /\ not tail) then
         true
       else
         y[i] - x[i] - k * b[i] + k * b[i + 1] <= k - 1
       endif)
    )
  endif;

predicate fzn_lex_lesseq_int(array [int] of var int: xs, array [int] of var int: ys) =
  baguette_lex_rows(xs, ys, length(xs) <= length(ys));
