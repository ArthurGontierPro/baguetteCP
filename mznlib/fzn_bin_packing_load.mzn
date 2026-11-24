% M18-coverage-T4 (docs/DECISIONS.md D-0220): bin_packing_load without the bool2int copies.
%
% MiniZinc 2.10.1's std/fzn_bin_packing_load.mzn is sum(load) = sum(weight), bin[i] in the
% bin range, and per bin `load[b] = sum(i) (weight[i] * bool2int(bin[i] = b))`. Flattened,
% each (item, bin) pair whose bin is in the item's domain costs an int_eq_reif (the
% INDICATOR `bin[i] = b`, a Boolean shared by common-subexpression elimination with any
% other part of the model that says the same), a bool2int (a second, 0..1 integer copy of
% it, its two rows and its own propagator) and one term of the bin's int_lin_eq.
%
% Here the same rows are written without the copy: per bin one
% `baguette_bool_lin_eq(w, [bin[i] = b | ...], load[b])`, an int_lin_eq whose terms are
% the indicators themselves, read as 0..1 (docs/SPEC.md 2.1). std's other two lines stay.
%
% Each load is also restricted to the sums its bin's items can reach (0 .. the weights of
% the items that may go there). std's flattening finds those bounds by itself, because
% there each load is the variable its own linear row defines; here nothing defines it, and
% without the restriction a load keeps its declared domain (gbac: 0..298 where std had
% 0..18, and the squares built from it 300 times wider).

predicate baguette_bool_lin_eq(array [int] of int: a, array [int] of var bool: x, var int: y);

predicate fzn_bin_packing_load(
  array [int] of var int: load,
  array [int] of var int: bin,
  array [int] of int: weight,
) =
  let {
    set of int: B = index_set(load);
    array [int] of var int: bs = array1d(bin);
    array [int] of int: ws = array1d(weight);
    set of int: I = index_set(bs);
  } in
  sum(load) = sum(weight)
    /\ forall (i in I) (min(B) <= bs[i] /\ bs[i] <= max(B))
    /\ forall (b in B) (
      let {
        array [int] of int: items = [i | i in I where ws[i] != 0 /\ b in dom(bs[i])];
      } in
      load[b] in sum ([min(0, ws[i]) | i in items])..sum ([max(0, ws[i]) | i in items])
        /\ baguette_bool_lin_eq([ws[i] | i in items], [bs[i] = b | i in items], load[b])
    );
