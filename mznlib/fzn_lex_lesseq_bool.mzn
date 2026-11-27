% M18-coverage-T5 (docs/DECISIONS.md D-0239): lex_lesseq and lex_less over Booleans as the
% four rows of fzn_lex_lesseq_int.mzn per position, over Boolean flags, each one
% `baguette_bool_lin_le` (D-0220's builtin: Booleans read as 0..1, no bool2int copy). The
% big-M constants of 0..1 cells are 2 and 1:
%   R1  b[i]                  -> x[i] <= y[i]    x - y + b[i]               <= 1
%   R2  b[i] /\ not b[i + 1]  -> x[i] <  y[i]    x - y + 2 b[i] - 2 b[i + 1] <= 1
%   R3  not b[i]              -> x[i] >= y[i]    y - x - b[i]               <= 0
%   R4  not b[i] /\ b[i + 1]  -> x[i] >  y[i]    y - x - 2 b[i] + 2 b[i + 1] <= 1
% b[1] is true and b[n + 1] the tail; a fixed operand is folded into the constant, so no
% builtin call carries a constant, and a row left with no variable is checked here.

predicate baguette_bool_lin_le(array [int] of int: a, array [int] of var bool: x, int: c);

predicate baguette_lex_bool_row(array [int] of int: a, array [int] of var bool: v, int: c) =
  let {
    set of int: open = {j | j in index_set(v) where not is_fixed(v[j])};
    int: k = c - sum (j in index_set(v) diff open) (a[j] * bool2int(fix(v[j])));
  } in
  if open = {} then 0 <= k else baguette_bool_lin_le([a[j] | j in open], [v[j] | j in open], k) endif;

predicate baguette_lex_rows_bool(array [int] of var bool: xs, array [int] of var bool: ys, bool: tail) =
  let {
    array [int] of var bool: x = array1d(xs);
    array [int] of var bool: y = array1d(ys);
    int: n = min(length(x), length(y));
  } in
  if n = 0 then
    tail
  else
    let {
      array [2..n] of var bool: bm;
      array [1..n + 1] of var bool: b = [true] ++ [bm[i] | i in 2..n] ++ [tail];
    } in
    forall (i in 1..n) (
      (if i = n /\ not tail then true
       else baguette_lex_bool_row([1, -1, 1], [x[i], y[i], b[i]], 1) endif) /\
      (if i = n /\ tail then true
       else baguette_lex_bool_row([1, -1, 2, -2], [x[i], y[i], b[i], b[i + 1]], 1) endif) /\
      (if i = 1 \/ (i = n /\ tail) then true
       else baguette_lex_bool_row([-1, 1, -1], [x[i], y[i], b[i]], 0) endif) /\
      (if i = 1 \/ (i = n /\ not tail) then true
       else baguette_lex_bool_row([-1, 1, -2, 2], [x[i], y[i], b[i], b[i + 1]], 1) endif)
    )
  endif;

predicate fzn_lex_lesseq_bool(array [int] of var bool: xs, array [int] of var bool: ys) =
  baguette_lex_rows_bool(xs, ys, length(xs) <= length(ys));
