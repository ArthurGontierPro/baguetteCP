% M7-T28 (docs/DECISIONS.md D-0146 section 7, D-0151 section 2): inverse, kept whole.
%
% MiniZinc 2.10.1's std/fzn_inverse.mzn is `f[i] in index_set(invf) /\ invf[f[i]] = i` and
% the mirror, an array_var_int_element per position, which baguette's subset does not
% have: it reached the solver as std's further decomposition, n^2 reified equalities and
% their clauses. Here the index-set restrictions stay (they tighten the declarations when
% the flattener can, and are unit rows of the .opb otherwise), and the channel itself is
% ONE call, `baguette_inverse(f, fmin, g, gmin)`, the two first indices carrying the index
% sets (FlatZinc arrays are 1-based). lib/core/prop/inverse.ml's header states the rows.

predicate baguette_inverse(
  array [int] of var int: f,
  int: fmin,
  array [int] of var int: g,
  int: gmin,
);

predicate fzn_inverse(array [int] of var int: f, array [int] of var int: invf) =
  if length(f) = 0 /\ length(invf) = 0 then
    true
  else
    forall (i in index_set(f)) (f[i] in index_set(invf))
      /\ forall (j in index_set(invf)) (invf[j] in index_set(f))
      /\ baguette_inverse(
        array1d(f),
        if length(f) = 0 then 1 else min(index_set(f)) endif,
        array1d(invf),
        if length(invf) = 0 then 1 else min(index_set(invf)) endif,
      )
  endif;
