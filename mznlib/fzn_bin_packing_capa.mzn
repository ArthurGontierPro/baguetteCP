% M18-coverage-T4 (docs/DECISIONS.md D-0220): bin_packing_capa without the bool2int
% copies.
%
% MiniZinc 2.10.1's std/fzn_bin_packing_capa.mzn is bin[i] in index_set(capacity) and per
% bin `capacity[b] >= sum(i) (weight[i] * bool2int(bin[i] = b))`. Here the same rows are
% written over the indicators `bin[i] = b` themselves (fzn_bin_packing_load.mzn says why),
% per bin one `baguette_bool_lin_le(w, [bin[i] = b | ...], capacity[b])`.

predicate baguette_bool_lin_le(array [int] of int: a, array [int] of var bool: x, int: c);

predicate fzn_bin_packing_capa(
  array [int] of int: capacity,
  array [int] of var int: bin,
  array [int] of int: weight,
) =
  let {
    set of int: B = index_set(capacity);
    array [int] of var int: bs = array1d(bin);
    array [int] of int: ws = array1d(weight);
    set of int: I = index_set(bs);
  } in
  forall (i in I) (min(B) <= bs[i] /\ bs[i] <= max(B))
    /\ forall (b in B) (
      let {
        array [int] of int: items = [i | i in I where ws[i] != 0 /\ b in dom(bs[i])];
      } in
      baguette_bool_lin_le([ws[i] | i in items], [bs[i] = b | i in items], capacity[b])
    );
