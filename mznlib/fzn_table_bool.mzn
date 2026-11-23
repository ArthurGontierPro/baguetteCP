% M18-coverage-T1 (docs/DECISIONS.md D-0206): table over var bool, kept whole. The same
% route as mznlib/fzn_table_int.mzn, the tuples written 0/1 (a Boolean is the integer
% 0..1 here, D-0007), so both spellings are one relation in lib/core/prop/table.ml.

predicate baguette_table_bool(
  array [int] of var bool: x,
  array [int] of int: t,
  array [int] of var bool: s,
);

predicate fzn_table_bool(array [int] of var bool: x, array [int, int] of bool: t) =
  let {
    array [int] of var bool: xs = array1d(x);
    int: n = length(xs);
    set of int: rows = index_set_1of2(t);
    int: c0 = min(index_set_2of2(t)) - 1;
    array [int] of int: keep =
      [k | k in rows where forall (j in 1..n) (not is_fixed(xs[j]) \/ fix(xs[j]) = t[k, c0 + j])];
  } in
  if n = 0 then
    card(rows) > 0
  elseif length(keep) = 0 then
    false
  else
    let {
      array [1..length(keep)] of var bool: s;
    } in baguette_table_bool(xs, [bool2int(t[k, c0 + j]) | k in keep, j in 1..n], s)
  endif;
