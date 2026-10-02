%-----------------------------------------------------------------------------%
% baguette solver library -- redefinitions-2.0.mzn  (M4-T9, D-0095)
%
% std/redefinitions-2.0.mzn gives array_int_maximum and array_int_minimum a BODY:
% a chain of auxiliaries y[i] = max(xs[i], y[i-1]), each of which then reaches
% redefinitions.mzn's int_max and, before M4-T9, its reified decomposition.  That
% throws away lib/core/prop/maxmin.ml, so this file SHADOWS the std one (MiniZinc
% resolves an include in the solver library before std, which is how
% redefinitions.mzn shadows std/redefinitions.mzn) and declares both BODYLESS, so
% the call reaches the .fzn verbatim -- std's `maximum'/`minimum' globals and the
% `max(array)'/`min(array)' functions all lower to these two.
%
% There is NO fzn_array_int_maximum: std has no such predicate to shadow.  The
% versioned file is the only place these two have a body, so it is the only place
% to take it away.
%
% Everything else std/redefinitions-2.0.mzn defines is kept VERBATIM, because
% shadowing the file shadows all of it: bool_clause_reif (which redefinitions.mzn's
% header relies on) and the two float forms (floats are outside docs/SPEC.md 2.1;
% kept so that such a model is refused by the front end, as before, and not by a
% missing predicate here).
%-----------------------------------------------------------------------------%

predicate bool_clause_reif(array [int] of var bool: xs, array [int] of var bool: ys, var bool: b) =
  clause(xs, ys ++ [b]) /\
    forall (i in index_set(xs)) (xs[i] -> b) /\
    forall (i in index_set(ys)) (ys[i] \/ b);

% Kept whole: n linear rows plus the per-value clause family, one propagator.
predicate array_int_maximum(var int: m, array [int] of var int: xs);
predicate array_int_minimum(var int: m, array [int] of var int: xs);

predicate array_float_maximum(var float: m, array [int] of var float: xs) =
  let {
    int: l = min(index_set(xs));
    int: u = max(index_set(xs));
    float: ly = lb_array(xs);
    float: uy = ub_array(xs);
    array [l..u] of var ly..uy: y;
  } in y[l] = xs[l] /\ m = y[u] /\ forall (i in l + 1..u) (y[i] == max(xs[i], y[i - 1]));

predicate array_float_minimum(var float: m, array [int] of var float: xs) =
  let {
    int: l = min(index_set(xs));
    int: u = max(index_set(xs));
    float: ly = lb_array(xs);
    float: uy = ub_array(xs);
    array [l..u] of var ly..uy: y;
  } in y[l] = xs[l] /\ m = y[u] /\ forall (i in l + 1..u) (y[i] == min(xs[i], y[i - 1]));
