% M18-coverage-T4 (docs/DECISIONS.md D-0220): bin_packing without the bool2int copies.
%
% MiniZinc 2.10.1's std/fzn_bin_packing.mzn is, for every bin b of
% lb_array(bin)..ub_array(bin), `sum(i) (weight[i] * bool2int(bin[i] != b)) >= W -
% capacity` (W the total weight), i.e. the load of b is at most `capacity`. Here it is
% that inequality over the indicators `bin[i] = b` themselves (fzn_bin_packing_load.mzn
% says why), one `baguette_bool_lin_le(w, [bin[i] = b | ...], capacity)` per bin of the
% same range. std's form counts the items NOT in b; the two are the same row, negated and
% shifted by W, and the indicators are the same Booleans.

predicate baguette_bool_lin_le(array [int] of int: a, array [int] of var bool: x, int: c);

predicate fzn_bin_packing(int: capacity, array [int] of var int: bin, array [int] of int: weight) =
  if length(bin) > 0 then
    let {
      array [int] of var int: bs = array1d(bin);
      array [int] of int: ws = array1d(weight);
      set of int: I = index_set(bs);
    } in
    forall (b in lb_array(bin)..ub_array(bin)) (
      let {
        array [int] of int: items = [i | i in I where ws[i] != 0 /\ b in dom(bs[i])];
      } in
      baguette_bool_lin_le([ws[i] | i in items], [bs[i] = b | i in items], capacity)
    )
  endif;
