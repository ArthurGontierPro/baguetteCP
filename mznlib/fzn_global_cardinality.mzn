%-----------------------------------------------------------------------------%
% global_cardinality stays whole.
%
% std/fzn_global_cardinality.mzn decomposes to one reified equality per variable
% per cover value, channelled to 0/1 and summed against the count.  That throws
% away lib/core/prop/gcc.ml, and what it throws away is not a constant factor:
% the decomposition's rows are ONE PER VALUE, and gcc's interval-capacity rule
% is a sum ACROSS values.  No amount of propagation over the per-value rows
% separately reaches an inference that no single one of them mentions.  D-0078
% measures both sides.
%
% M7-T15 (D-0076) bridged MiniZinc 1.x's two-argument spelling onto the
% three-argument predicate and let std decompose it, and said in as many words
% why that was right AT THE TIME: baguette had no propagator for the call to be
% kept whole for.  It has one now, and compat_mzn1.mzn's bridge therefore lands
% here instead -- the same bridge, a different destination.
%
% The bodyless declaration is what makes MiniZinc emit the call verbatim.  Note
% that it is the fzn_ name that is declared, not the globals.mzn one: std's
% global_cardinality reaches fzn_global_cardinality itself, so shadowing the
% inner predicate keeps the outer one's argument handling (cover as an array of
% par int, the open form) exactly as std defines it.
%
% THE COUNTS NEED A DECLARED DOMAIN, and that is why this file has a body at all.
%
% std's `global_cardinality' takes `array [int] of var int: counts', and a model that
% passes it a freshly introduced array gets variables with NO domain.  Under the
% decomposition that did not matter: the `sum(bool2int(...)) = counts[i]' rows let
% MiniZinc infer 0..length(x) and the declaration came out bounded.  Keep the global
% whole and those rows are gone, so the count arrives at the front end as `var int' and
% is REFUSED -- docs/SPEC.md 2.1 requires a finite declared domain, and that refusal is
% right.  MEASURED on 2008_debruijn_binary, which is the instance this whole bridge
% exists for.
%
% So `fzn_global_cardinality' states the bound the decomposition used to imply and hands
% the constraint to `baguette_global_cardinality', which is the bodyless one.  The bounds
% are not a heuristic: a tally over |x| variables is between 0 and |x| by definition, so
% nothing is lost and nothing is assumed.
%
% THE FRONT END REFUSES three shapes rather than mis-counting them, and all
% three are refusals with a source position (lib/flatzinc/compile.ml's
% post_global_cardinality says why): a cover and counts of different lengths, a
% count that is a literal constant rather than a variable, and the same variable
% twice in the array.
%-----------------------------------------------------------------------------%

predicate baguette_global_cardinality(
  array [int] of var int: x,
  array [int] of int: cover,
  array [int] of var int: counts,
);

predicate fzn_global_cardinality(
  array [int] of var int: x,
  array [int] of int: cover,
  array [int] of var int: counts,
) =
  forall (i in index_set(counts)) (counts[i] >= 0 /\ counts[i] <= length(x))
  /\ baguette_global_cardinality(x, cover, counts);
