% M18-coverage-T1 (docs/DECISIONS.md D-0206): table, kept whole.
%
% MiniZinc 2.10.1's std/fzn_table_int.mzn is one array_int_element per column over a
% SHARED index i in 1..T: GAC already (a star around i), but each element writes about
% 2T rows over the index's ladder and direct encoding, so a table cost about (2n + 3) T
% rows, and the census of M18-coverage found 52 of its 135 Challenge instances refused
% by the heap budget.
%
% Here the relation is ONE call, `baguette_table(x, t, s)`, reaching
% lib/core/prop/table.ml:
%
%   - t, the tuples FLATTENED row-major, only those inside the declared domains of x
%     (`t[k, j] in dom(x[j])`: a tuple outside them is false, and dropping it here is
%     a domain restriction the flattener does for free);
%   - s, one SELECTOR var bool per tuple kept, introduced by this `let`, as member's
%     selectors and regular's state flags are. s[k] means "x is tuple k"; the
%     propagator reasons over them as store variables, and they never need search.
%
% An empty table (or one no tuple of which survives the domains) is false; a table over
% no position is true.

predicate baguette_table(
  array [int] of var int: x,
  array [int] of int: t,
  array [int] of var bool: s,
);

predicate fzn_table_int(array [int] of var int: x, array [int, int] of int: t) =
  let {
    array [int] of var int: xs = array1d(x);
    int: n = length(xs);
    set of int: rows = index_set_1of2(t);
    int: c0 = min(index_set_2of2(t)) - 1;
    array [int] of int: keep =
      [k | k in rows where forall (j in 1..n) (t[k, c0 + j] in dom(xs[j]))];
  } in
  if n = 0 then
    card(rows) > 0
  elseif length(keep) = 0 then
    false
  else
    let {
      array [1..length(keep)] of var bool: s;
    } in baguette_table(xs, [t[k, c0 + j] | k in keep, j in 1..n], s)
  endif;
