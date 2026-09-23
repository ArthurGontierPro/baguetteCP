(* global_cardinality(x, cover, counts): for each i, [counts.(i)] is the number of
   variables of [x] taking the value [cover.(i)].  The cover is a list of CONSTANTS; the
   counts are variables, and a fixed cardinality is the degenerate case (a variable
   declared on one value), not a different shape.

   gcc is all_different's generalisation -- all_different is gcc with every count in
   {0, 1} -- so this module is shaped on lib/core/prop/alldiff.ml and its rule A below
   IS alldiff's Hall rule with the capacities set to one.  Read alldiff.ml's header
   first; this one states what is DIFFERENT, and the differences are large enough to be
   worth the reading.

   ---------------------------------------------------------------------------
   Consistency level, and why the declaration is [Checking]
   ---------------------------------------------------------------------------

   The filtering is bounds-level REASONING -- it reads lo/hi and writes lo/hi and never
   looks at an interior hole -- but the tag is [Propagator.Checking], which is the level
   the M2-T10 oracle (BAGUETTE_CONSISTENCY=1) holds a propagator to.  That is not
   modesty for its own sake:

     - bounds consistency for gcc is Quimper/Katriel's algorithm, not the capacity-Hall
       rules here, and with VARIABLE counts it additionally has to reach a fixpoint
       between the count bounds and the interval capacities.  Nothing below proves that
       it does;
     - alldiff could declare [Bounds] at stage 1 because Hall intervals ARE bounds
       consistency for all_different (Puget).  There is no such theorem for what is
       written here;
     - a declaration the oracle falsifies is worse than a modest one: the oracle raises
       [Weaker_than_declared] at a search node, which is a crash, not a warning.

   So the tag says what is PROVED, this header says what is IMPLEMENTED, and bounds
   consistency by Quimper's algorithm -- then domain consistency by Regin's flow -- is a
   later row, exactly as stage 2 was for all_different.  What [Checking] does oblige,
   and what rule C delivers, is that a TOTAL assignment violating the cardinalities is
   refused: with every x fixed, [must_v] = [may_v] = the true tally and rule C pushes
   both of the count's bounds onto it, so a count fixed anywhere else empties.

   ---------------------------------------------------------------------------
   The model rows, and the one thing that shapes this whole module
   ---------------------------------------------------------------------------

   The tally `how many x take the value v` looks like a sum over the DIRECT encoding,
   which is what all_different's Hall derivation counts over.  It is not available here,
   and the reason is structural rather than incidental: **the direct encoding does not
   exist when the .opb is written.**  It is introduced lazily, with `red`, by
   [Encoding.start_proof] (PROOF-FORMAT section 3), so a model row over `x_eq_v` is a
   row over variables the model file has never heard of.  all_different does not hit
   this because its model rows are pairwise disequalities over ORDER literals; a gcc
   counting row has nowhere to hide.

   The way out is an identity, and it costs nothing:

     [x = v]  =  x_ge_v - x_ge_(v+1)

   -- the order encoding's own indicator.  So the counting row is linear in the
   literals the .opb already has, and lib/flatzinc/compile.ml posts, per cover value v
   with count variable c,

     sum_{i in D_v} (x_i_ge_v - x_i_ge_(v+1))  =  c - const_v

   as an [Encoding.add_equality], where D_v is the x whose DECLARED domain holds v and
   const_v counts the x that are fixed to v outright (a constant operand, or a variable
   declared on one value -- they have no order literal at that end either, so they are
   folded into the row's right-hand side).  [ge_cid] is the `>=` half ("the tally is at
   least the count") and [le_cid] the `<=` half.

   Three consequences, and each of them is a simplification:

     1. **This propagator requests no direct encoding at all.**  No `x_eq_v` variables,
        no channelling clauses, no at-least-one line -- none of the width-proportional
        machinery D-0028 charges for.  all_different pays for all of it.
     2. **"x takes a value in [a, b]" telescopes.**  Summing the indicator over an
        interval leaves `x_ge_a - x_ge_(b+1)`, so the at-least-one line a Hall argument
        needs is not derived from the channelling: it IS the variable's two bound facts,
        cited with [Explanation.defining] (D-0064's per-bound root test) or, where a
        decision moved the bound, as [Explanation.clause] with the facts carried into
        the pruning's [Reason] (alldiff's [Gone_hole] shape, I-P5).
     3. **The pruning needs no channelling telescope either.**  What the counting leaves
        is already a statement about order literals, so turning it into a bound is one
        more bound fact rather than alldiff's per-value forward-clause sum.

   ---------------------------------------------------------------------------
   Rule A -- interval capacity.  The generalisation of the Hall interval, and the
   reason this row exists
   ---------------------------------------------------------------------------

   For an interval [a, b] every value of which is in the cover, write

     cap  = sum_{v in [a,b]} (hi(c_v) - const_v)      the values' capacity for the
                                                      MOVABLE variables
     H    = { i : [lo_i, hi_i] is inside [a, b] }     the variables confined to it

     |H| > cap   ->  Conflict;
     |H| = cap   ->  for every OTHER y,  lo(y) in [a,b] => lo(y) := b + 1
                                         hi(y) in [a,b] => hi(y) := a - 1.

   With every capacity 1 this IS all_different's Hall rule.  With capacities above 1 it
   is strictly stronger than anything the per-value decomposition can see, and the
   reason is worth stating exactly, because it is this row's whole thesis: the
   decomposition's rows are ONE PER VALUE (`sum_i (x_i = v) = c_v`), and this argument
   is a sum ACROSS values.  No single row of the decomposition mentions two cover values
   at once, so no amount of propagation over them separately reaches it.

   THE DERIVATION, as cutting planes.  Write I_i for the indicator `x_i lands in
   [a, b]`, which by the telescope above is `x_i_ge_a' - x_i_ge_(b'+1)` over that
   variable's own clipped interval [a', b'] = [a, b] intersected with its declared
   range.  The lines are

     ALO_i    I_i >= 1                        one per i in H       [alo_line]
              (its two bound facts: lo_i >= a' and hi_i <= b', each a unit line)
     HIGH_v   - sum_{i in D_v} (x_i_ge_v - x_i_ge_(v+1))  >=  const_v - hi(c_v)
              one per v in [a, b]              [high_row]
              (the model row [le_cid] with the count's own ladder cleared -- see there)

   Add them all.  Summing HIGH_v over v in [a, b] telescopes each variable's terms into
   exactly -I_i, so every i in H cancels against its own ALO_i and the degree is
   |H| - cap.  What survives is

     - sum_{i in D \ H} I_i  >=  |H| - cap

   With |H| = cap the degree is 0 and every variable but the target y is dropped by
   adding `I_i >= 0`, which is FREE -- it is the ladder itself, the rung chain from a'
   to b'+1 ([drop_line]).  The row is then

     x_y_ge_(b'+1) - x_y_ge_a'  >=  0

   -- "y is past b, or y is below a" -- and one bound fact of y's own turns it into the
   push: cite `y >= a'` and what is left is `y >= b + 1`; cite `y <= b'` and what is
   left is `y <= a - 1`.

   THE EMPTYING PUSH NEEDS ONE MORE LINE, and this is alldiff's [overshoot_cancel] under
   another name.  The conflict arm pushes a CONFINED variable past its own upper bound,
   so the residue `y_ge_(b+1)` has to become a contradiction rather than a valid bound.
   It does so for nothing when b is at or above y's DECLARED top -- the literal is the
   constant false and is simply not there -- and that is the case every model reaches
   first, which is exactly how alldiff shipped the same defect latent (M4-T2's note).
   When y's declared top is HIGHER than b and only its CURRENT top is inside, the
   literal is real, the row derives the perfectly valid `y >= b + 1`, and 3.0.2 answers
   "the constraint with ID n is not contradicting".  Measured here on the first model
   whose confined variables were narrowed by a linear row rather than declared narrow.
   What closes it is y's own upper bound: `y <= b'` cancels the residue exactly.  The
   test is `b + 1 > hi(y)`, which is not a heuristic -- in the |H| = cap arm the pushed
   variable is NOT confined, so its upper bound is strictly above b and the residue IS
   the pruning and must stay.

   With |H| > cap the degree is |H| - cap >= 1 and the row is contradicting.  It is
   REPORTED the way all_different reports its pigeonhole: by pushing one surplus
   confined variable out of the interval it is confined to, so [Store.apply]'s [Failed]
   arm pairs the derivation with [Reason.none] and no `rup` conflict line claims a
   counting argument as reverse unit propagation (I-X10, D-0040).

   ---------------------------------------------------------------------------
   Rule C -- the count variables' own bounds
   ---------------------------------------------------------------------------

     may_v  = const_v + |{ i movable : v in [lo_i, hi_i] }|     possible takers
     must_v = const_v + |{ i movable : lo_i = hi_i = v }|       certain takers
     hi(c_v) := may_v      and      lo(c_v) := must_v

   This is the rule that makes the propagator a CHECKER, and it is also how a shortfall
   becomes a refutation: when fewer variables can take v than the count demands, the
   upper push empties c_v's domain and the conflict is the emptying, as in rule A.

   THE UPPER DERIVATION starts from [ge_cid] and clears the x terms in the two ways
   their status allows -- `- e_i >= 0` for an x that CANNOT take v ([zero_e], free, from
   the bound that excludes v) and `- e_i >= -1` for one that can ([cost_e], two literal
   axioms, one unit of degree each, and there are may_v - const_v of them).  What is
   left is `- sum_k c_ge_k >= cdlo - may_v`, the count's ladder bounded by a number, and
   [ladder_at_most] turns it into the single literal ~c_ge_(may_v+1): add, for each j in
   (cdlo, may_v], the rung chain c_ge_j -> c_ge_(may_v+1), weaken the ladder above away
   for free, and ONE DIVISION by may_v - cdlo + 1 rounds the degree up to 1.  That
   division is the only place in this module where [Combine]'s divisor does real work,
   and it is what a [Cut] could not have expressed.

   THE LOWER DERIVATION is its mirror over [le_cid]: every x FIXED to v hands the row
   `e_i >= 1` ([unit_e], its two bound facts again) to gain a unit of degree from, every
   other term clears for free ([free_e], one ladder rung), and [ladder_at_least] does
   the same division the other way up.

   ---------------------------------------------------------------------------
   What is NOT here, and why
   ---------------------------------------------------------------------------

   1. **No flow.**  Domain-consistent gcc is Regin's flow argument and is a separate
      row, as stage 2 was for all_different.

   2. **No interval LOWER-capacity rule.**  Its per-value case -- when the number of
      possible takers of v equals the count's lower bound, every one of them must take v
      -- is exactly what the decomposition's own linear row already propagates, so it
      would not earn its justification HERE, in the row whose thesis is that the global
      infers what the decomposition cannot.  Its interval case does earn it, and needs
      one line this module does not build: `one variable takes at most one value of
      [a, b]`.  Over the order encoding that line is free as well (the indicators over
      [a, b] telescope to x_ge_a - x_ge_(b+1) <= 1, which is two literal axioms), so the
      next stage starts from a sentence rather than from zero.  It is not built because
      nothing in this row needs it.

   3. **NO NEW [Explanation] CONSTRUCTOR.**  Everything above is
      [Combine]/[Weaken]/[Model_row]/[Defining] and, for a bound a decision moved,
      [Clause].  D-0044's bet is not spent here.

   ---------------------------------------------------------------------------
   Snapshotting and I-X6
   ---------------------------------------------------------------------------

   As in alldiff: every number a derivation reads is frozen into a [snap]/[csnap] at the
   moment of the pruning and the thunk reads nothing from the store afterwards.  The
   [Encoding] ids it reads live are written once, by [Encoding.start_proof], before the
   first decision, and never move. *)

module Lit = Baguette_proof.Lit
module Encoding = Baguette_proof.Encoding

(* --------------------------------------------------------------------- the instance *)

(* A MOVABLE x of the scope: one whose declared domain holds more than one value, so it
   has order literals for the derivation to talk about.  Anything fixed is folded into
   [cconst] by lib/flatzinc/compile.ml and never reaches this array. *)
type term = { x : Var.t; name : string; decl_lo : int; decl_hi : int }

type cover = {
  cv : int;
  cx : Var.t;
  cname : string;
  cdlo : int;
  cdhi : int;
  (* How many x of the scope are FIXED to [cv] -- a constant operand, or a variable
     declared on one value.  They have no order literal at [cv] either way, so the
     model row leaves them out and subtracts them from its right-hand side instead.
     Every count below adds them back, so the two agree by construction. *)
  cconst : int;
  ge_cid : int; (* the tally of D_v is at least c_v - const_v *)
  le_cid : int; (* ... and at most *)
}

type t = { terms : term array; cov : cover array; enc : Encoding.t }

let name = "global_cardinality"
let consistency = Propagator.Checking

let vars t =
  Array.to_list (Array.map (fun tm -> tm.x) t.terms)
  @ Array.to_list (Array.map (fun c -> c.cx) t.cov)

let make store enc ~cover vars_x =
  let terms =
    Array.of_list
      (List.map
         (fun x ->
           let d = Store.get store x in
           { x; name = Store.name store x; decl_lo = Domain.lo d; decl_hi = Domain.hi d })
         vars_x)
  in
  let cov =
    Array.of_list
      (List.map
         (fun (cv, cx, cconst, ge_cid, le_cid) ->
           let d = Store.get store cx in
           {
             cv;
             cx;
             cname = Store.name store cx;
             cdlo = Domain.lo d;
             cdhi = Domain.hi d;
             cconst;
             ge_cid;
             le_cid;
           })
         cover)
  in
  { terms; cov; enc }

(* ------------------------------------------------------------------------ snapshots *)

type snap = {
  s_var : Var.t;
  s_name : string;
  s_dlo : int;
  s_dhi : int;
  s_lo : int;
  s_hi : int;
  (* Whether each current bound was established AT THE ROOT -- the trail entry
     supporting it belongs to level 0, or it has never moved.  A root-established bound
     is a consequence of the model and its unit line is citable however deep the search
     has gone; one a decision set is not, and the derivation then cites the implication
     instead and carries the facts in the [Reason] (D-0064, and alldiff's [Gone_hole]). *)
  s_lo_root : bool;
  s_hi_root : bool;
  s_lo_why : Reason.t;
  s_hi_why : Reason.t;
}

type csnap = {
  k_cov : cover;
  k_lo : int;
  k_hi : int;
  k_lo_root : bool;
  k_hi_root : bool;
  k_lo_why : Reason.t;
  k_hi_why : Reason.t;
}

let established_at_root store v ~lower =
  let sup = if lower then Store.lo_support store v else Store.hi_support store v in
  sup = Store.no_support || Store.level_of_index store sup = 0

let support_reason store v ~lower =
  let sup = if lower then Store.lo_support store v else Store.hi_support store v in
  if sup = Store.no_support then Reason.none
  else (Store.trail_entry store sup).Store.reason

let range a b = List.init (Stdlib.max 0 (b - a + 1)) (fun i -> a + i)

let snap_of store tm =
  let d = Store.get store tm.x in
  {
    s_var = tm.x;
    s_name = tm.name;
    s_dlo = tm.decl_lo;
    s_dhi = tm.decl_hi;
    s_lo = Domain.lo d;
    s_hi = Domain.hi d;
    s_lo_root = established_at_root store tm.x ~lower:true;
    s_hi_root = established_at_root store tm.x ~lower:false;
    s_lo_why = support_reason store tm.x ~lower:true;
    s_hi_why = support_reason store tm.x ~lower:false;
  }

let csnap_of store c =
  let d = Store.get store c.cx in
  {
    k_cov = c;
    k_lo = Domain.lo d;
    k_hi = Domain.hi d;
    k_lo_root = established_at_root store c.cx ~lower:true;
    k_hi_root = established_at_root store c.cx ~lower:false;
    k_lo_why = support_reason store c.cx ~lower:true;
    k_hi_why = support_reason store c.cx ~lower:false;
  }

(* ---------------------------------------------------------------------- explanations *)

let cid_of what = function
  | Some id -> id
  | None ->
      invalid_arg
        (Printf.sprintf
           "Gcc: %s has no constraint id. Every line this module names is a ladder rung \
            or one of the two counting rows lib/flatzinc/compile.ml posted; a [None] \
            here means the propagator and the .opb have drifted apart."
           what)

let cite id = Explanation.term 1 (Explanation.model_row id)

(* A fact the derivation needs at UNIT strength.  Root-established: the unit line itself
   ([Explanation.defining], resolved by [Justify.defining_lit]).  Otherwise: the
   globally valid implication `l \/ ~facts`, whose leftover literals stay in the row and
   are carried by the pruning's [Reason]. *)
let fact_summand ~root ~why lit =
  if root then Explanation.defining 1 lit
  else
    Explanation.term 1 (Explanation.clause (lit :: List.map Lit.negate (Reason.lits why)))

(* The ladder chain `x_ge_j - x_ge_m >= 0` for j < m, as a plain sum of the consistency
   rows: [Encoding.consistency_id x u] is `x_ge_u - x_ge_(u+1) >= 0`, so summing
   u = j .. m-1 telescopes.  Every key it asks for is strictly inside the declared
   range, which is exactly where the rung exists. *)
let rung_summands t x ~from_ ~to_ =
  List.map
    (fun u -> cite (cid_of "ladder rung" (Encoding.consistency_id t.enc x u)))
    (range from_ (to_ - 1))

let rung_line t x ~from_ ~to_ = Explanation.combine (rung_summands t x ~from_ ~to_) 1

(* A bound fact the derivation LEANS ON, cancelled where it can be and left in the row
   where it cannot.

   This is the single most important thing to understand about every derivation below,
   and it is alldiff.ml's rule restated for the order encoding.  A statement like "x
   lands in [a, b]" is worth two units of degree and NOTHING in the proof gives them
   away: a decision is not an assumption in this format, so a bound a decision moved has
   no unit line and none is derivable (measured -- veripb 3.0.2 refuses the minted
   `rup ~n_ge_1 >= 1` with "not implied by reverse unit propagation").

   So the derivation does not ask for one.  It sums LADDER CHAINS, which are globally
   valid and free, and the bound literal is simply left in the row: what comes out is

     <the pruning>  \/  ~<the bounds it read>

   -- the [Ne] shape, sound at any level -- and the pruning's [Reason] carries those
   same bounds, which is what makes the trace line true (I-P5) and RUP.  [bound_cancels]
   then removes a literal where, and only where, the bound was established AT THE ROOT,
   because a root bound is a consequence of the model and its unit line is citable
   however deep the search has gone (D-0064, per bound, not per solver level).  That
   matters for one case and it is the important one: a ROOT conflict must derive 0 >= 1,
   and a row with literals left in it is not contradicting. *)
let bound_cancels ~lo_of ~hi_of snaps =
  List.concat_map
    (fun s ->
      let below = lo_of s and above = hi_of s in
      (if below > 0 && s.s_lo > s.s_dlo && s.s_lo_root then
         [ Explanation.defining below (Lit.ge s.s_name s.s_lo) ]
       else [])
      @
      if above > 0 && s.s_hi < s.s_dhi && s.s_hi_root then
        [ Explanation.defining above (Lit.le s.s_name s.s_hi) ]
      else [])
    snaps

(* HIGH_v: the model row [le_cid] with the count's ladder cleared, leaving

     - sum_{i in D_v} (x_i_ge_v - x_i_ge_(v+1))  >=  const_v - hi(c_v).

   [le_cid] is that sum with `+ sum_{k = cdlo+1}^{cdhi} c_ge_k >= const_v - cdlo`.  Each
   c_ge_k at or below hi(c) is cleared by the literal axiom ~c_ge_k -- cancelling a
   POSITIVE term, so it costs the unit of degree that walks the right-hand side down
   from const_v - cdlo to const_v - hi(c), and it needs no fact at all.  Each above it is
   cleared by the chain from hi(c)+1, which leaves one copy of c_ge_(hi(c)+1) per rung
   cleared -- the count's own upper bound, cancelled by [bound_cancels]' rule where it
   was established at the root and carried in the [Reason] where it was not. *)
let high_row t k =
  let c = k.k_cov in
  let above = c.cdhi - k.k_hi in
  Explanation.combine
    (cite c.le_cid
     :: List.map
          (fun kk -> Explanation.weaken [ (1, Lit.negate (Lit.ge c.cname kk)) ])
          (range (c.cdlo + 1) k.k_hi)
    @ List.concat_map
        (fun kk -> rung_summands t c.cname ~from_:(k.k_hi + 1) ~to_:kk)
        (range (k.k_hi + 1) c.cdhi)
    @
    if above > 0 && k.k_hi < c.cdhi && k.k_hi_root then
      [ Explanation.defining above (Lit.le c.cname k.k_hi) ]
    else [])
    1

(* ------------------------------------------------------------------- rule A: capacity *)

let declares s v = s.s_dlo <= v && v <= s.s_dhi
let clip_lo s ~a = Stdlib.max a s.s_dlo
let clip_hi s ~b = Stdlib.min b s.s_dhi

(* The confined variable's share of the counting: `I_i >= 1`, as far as the ladder can
   take it.  The chains a' -> lo(i) and hi(i)+1 -> b'+1 are globally valid and free, and
   what they leave in the row is exactly ~x_ge_lo(i) and x_ge_(hi(i)+1) -- the variable's
   own two bounds, which is what confines it to [a, b] in the first place.  A clipped end
   that IS the declared end contributes a constant instead, which the model row folded
   into its right-hand side already, so there is nothing to cite and nothing left over. *)
let alo_summands t s ~a ~b =
  let a' = clip_lo s ~a and b' = clip_hi s ~b in
  (if a' > s.s_dlo then rung_summands t s.s_name ~from_:a' ~to_:s.s_lo else [])
  @
  if b' < s.s_dhi then rung_summands t s.s_name ~from_:(s.s_hi + 1) ~to_:(b' + 1) else []

let alo_leftovers s ~a ~b =
  ((if clip_lo s ~a > s.s_dlo then 1 else 0), if clip_hi s ~b < s.s_dhi then 1 else 0)

(* `I_i >= 0` for a variable the pruning does not care about: free, because it is the
   ladder.  The two degenerate ends are literal axioms rather than a chain, for the same
   reason [alo_summands] has two guards. *)
let drop_summands t s ~a ~b =
  let a' = clip_lo s ~a and b' = clip_hi s ~b in
  if a' > s.s_dlo && b' < s.s_dhi then
    [ Explanation.term 1 (rung_line t s.s_name ~from_:a' ~to_:(b' + 1)) ]
  else if a' <= s.s_dlo && b' < s.s_dhi then
    [ Explanation.weaken [ (1, Lit.le s.s_name b') ] ]
  else if a' > s.s_dlo && b' >= s.s_dhi then
    [ Explanation.weaken [ (1, Lit.ge s.s_name a') ] ]
  else []

(* The counting argument: one at-least-one per confined variable, one HIGH row per
   value, and a free ladder line for every other variable's indicator.  [extra] is the
   variable being pruned, whose terms are what the row is left holding. *)
let cap_summands t ~a ~b ~snaps ~halls ~caps ~extra =
  let named s =
    List.exists (fun h -> String.equal h.s_name s.s_name) halls
    || match extra with Some y -> String.equal y.s_name s.s_name | None -> false
  in
  let in_scope s = List.exists (fun v -> declares s v) (range a b) in
  List.concat_map (fun s -> alo_summands t s ~a ~b) halls
  @ List.map (fun k -> Explanation.term 1 (high_row t k)) caps
  @ List.concat_map
      (fun s -> if named s || not (in_scope s) then [] else drop_summands t s ~a ~b)
      snaps

(* The push.  After the counting the row is `y_ge_(b'+1) - y_ge_a' >= 0` -- "y is past b,
   or y is below a" -- and turning it into a bound is the same ladder move once more:
   the chain a' -> lo(y) replaces ~y_ge_a' by ~y_ge_lo(y), which [bound_cancels] then
   removes where the bound is a root one, and what is left is `y >= b + 1`.  The upper
   push is its mirror.

   THE EMPTYING PUSH NEEDS ONE MORE CHAIN, and this is alldiff's [overshoot_cancel] under
   another name.  The conflict arm pushes a CONFINED variable past its own upper bound,
   so the residue y_ge_(b+1) has to become a contradiction rather than a valid bound.  It
   does so for nothing when b is at or above y's DECLARED top -- the literal is the
   constant false and is simply not there -- and that is the case every model reaches
   first, which is how alldiff shipped the same defect latent (M4-T2's note).  When y's
   declared top is higher than b and only its CURRENT top is inside, the literal is real,
   the row derives the perfectly valid `y >= b + 1`, and 3.0.2 answers "the constraint
   with ID n is not contradicting".  Measured here on the first model whose confined
   variables were narrowed by a linear row rather than declared narrow.  The test is
   `b + 1 > hi(y)`, which is not a heuristic: in the |H| = cap arm the pushed variable is
   NOT confined, so its upper bound is strictly above b and the residue IS the pruning
   and must stay. *)
(* D-0010's CURRENCY, and gcc is the first global that had to pay it.

   What the counting leaves is a single order literal -- `y_ge_(b+1) >= 1` for a lower
   push.  That is a true and sufficient statement of the new bound, and it is NOT what
   another propagator can combine with.  lib/core/prop/order_reason.ml's header says why
   in one sentence: an order literal is 0/1, so `a * y_ge_b` tops out at `a` and not at
   `a * b`; a bound is worth its whole prefix of the ladder, `sum_{k = dlo+1}^{b} y_ge_k`,
   which is the substitution lib/proof/encoding.ml performs on the model side.  A
   [Linear] row summed against the single literal is short by exactly the rungs beneath
   it, and 3.0.2 answers "the constraint with ID n is not contradicting".

   MEASURED, and it is the defect this row shipped first: a gcc capacity push of `u` to 5
   consumed by `int_lin_le([1],[u],4)` at the ROOT.  all_different does not show it for a
   reason that is luck rather than design -- its derivations still reach
   [Explanation.clause] often enough that lib/core/search.ml's [rests_on_a_clause] routes
   those root conflicts the D-0022 way, where the empty clause is cited and the
   arithmetic is never evaluated.  gcc's derivation is [Defining] all the way down, so
   the numeric route is the one it takes, and the numeric route is where the currency
   matters.

   The lift is the same shape both ways: take W copies of the single-literal derivation
   and add, for every rung beneath (above) the pushed bound, the chain that relates it to
   that bound.  The lower rungs' coefficients come out at 1, the pushed literal's excess
   cancels, and the right-hand side is W -- which is the ladder statement
   [Order_reason.weaken_declared] would have built.

   Only for a push that MOVES a bound.  An emptying push already derives 0 >= 1 and a
   contradiction is in no currency at all. *)
let ladder_lift t ~y ~lower ~bound base =
  if lower then
    let w = bound - y.s_dlo in
    if w < 2 then base
    else
      Explanation.combine
        (Explanation.term w base
        :: List.map
             (fun k -> Explanation.term 1 (rung_line t y.s_name ~from_:k ~to_:bound))
             (range (y.s_dlo + 1) (bound - 1)))
        1
  else
    let w = y.s_dhi - bound in
    if w < 2 then base
    else
      Explanation.combine
        (Explanation.term w base
        :: List.map
             (fun k ->
               Explanation.term 1 (rung_line t y.s_name ~from_:(bound + 1) ~to_:k))
             (range (bound + 2) y.s_dhi))
        1

let prune_expl t ~a ~b ~snaps ~halls ~caps ~y ~lower ~bound =
  let moves = if lower then bound <= y.s_hi else bound >= y.s_lo in
  Explanation.deferred (fun () ->
      let finish e = if moves then ladder_lift t ~y ~lower ~bound e else e in
      let a' = clip_lo y ~a and b' = clip_hi y ~b in
      let low_side = a' > y.s_dlo and high_side = b' < y.s_dhi in
      let want_low = lower || a - 1 < y.s_lo in
      let want_high = (not lower) || b + 1 > y.s_hi in
      let y_low =
        if low_side && want_low then rung_summands t y.s_name ~from_:a' ~to_:y.s_lo
        else []
      in
      let y_high =
        if high_side && want_high then
          rung_summands t y.s_name ~from_:(y.s_hi + 1) ~to_:(b' + 1)
        else []
      in
      finish
      @@ Explanation.combine
           (cap_summands t ~a ~b ~snaps ~halls ~caps ~extra:(Some y)
           @ bound_cancels
               ~lo_of:(fun s -> fst (alo_leftovers s ~a ~b))
               ~hi_of:(fun s -> snd (alo_leftovers s ~a ~b))
               halls
           @ y_low @ y_high
           @ bound_cancels
               ~lo_of:(fun _ -> if low_side && want_low then 1 else 0)
               ~hi_of:(fun _ -> if high_side && want_high then 1 else 0)
               [ y ])
           1)

(* Every variable in scope is named, and that is deliberate rather than lazy: rule A's
   top level weakens the indicator of every x that is neither confined nor the target,
   so D-0026's reverse agreement check ([Explanation.top_weaken_owners]) requires the
   reason to name them all.  A tail with a fact the derivation did not need is a weaker
   trace line, which is sound; a tail missing one is I-P5.  The counts are named at
   their upper bound, which is the only one rule A reads. *)
let scope_facts ~snaps ~caps =
  List.concat_map
    (fun s ->
      [
        Reason.at_least ~name:s.s_name ~decl:s.s_dlo s.s_lo;
        Reason.at_most ~name:s.s_name ~decl:s.s_dhi s.s_hi;
      ]
      @ (if s.s_lo_root then [] else s.s_lo_why)
      @ if s.s_hi_root then [] else s.s_hi_why)
    snaps
  @ List.concat_map
      (fun k ->
        [
          Reason.at_most ~name:k.k_cov.cname ~decl:k.k_cov.cdhi k.k_hi;
          Reason.at_least ~name:k.k_cov.cname ~decl:k.k_cov.cdlo k.k_cov.cdlo;
        ]
        @ if k.k_hi_root then [] else k.k_hi_why)
      caps

(* ----------------------------------------------------------- rule C: the count bounds *)

(* `- e_i^v >= 0` -- clearing the indicator of a value the variable CANNOT take, at no
   cost in degree, from the bound that excludes it.  Below the window: the literal axiom
   ~x_ge_v pays for the positive half, and the chain v+1 -> lo(x) walks the negative half
   up to the bound, which is what is left in the row.  Above it: the free axiom
   x_ge_(v+1) and the chain hi(x)+1 -> v, leaving x_ge_(hi+1).  Both leftovers are the
   variable's own bound and are [bound_cancels]' business. *)
let zero_summands t s v =
  if v < s.s_lo then
    (if v > s.s_dlo then [ Explanation.weaken [ (1, Lit.negate (Lit.ge s.s_name v)) ] ]
     else [])
    @ rung_summands t s.s_name ~from_:(v + 1) ~to_:s.s_lo
  else if v > s.s_hi then
    (if v < s.s_dhi then [ Explanation.weaken [ (1, Lit.ge s.s_name (v + 1)) ] ] else [])
    @ rung_summands t s.s_name ~from_:(s.s_hi + 1) ~to_:v
  else invalid_arg "Gcc.zero_summands: the value is inside the current window"

(* `- e_i^v >= -1` -- clearing the indicator of a value the variable CAN take, at the one
   unit of degree D-0009 says a literal axiom costs.  Two axioms, one per end, and no
   fact: this is the only clearing in the module that reads nothing. *)
let cost_summands s v =
  (if v > s.s_dlo then [ Explanation.weaken [ (1, Lit.negate (Lit.ge s.s_name v)) ] ]
   else [])
  @ if v < s.s_dhi then [ Explanation.weaken [ (1, Lit.ge s.s_name (v + 1)) ] ] else []

(* `e_i^v >= 0` -- clearing an indicator out of the LOWER row, where it appears
   negatively and so clears for free.  In the general case that is one ladder rung; at a
   declared end the rung does not exist and the constant makes a literal axiom do it. *)
let free_summands t s v =
  if v > s.s_dlo && v < s.s_dhi then
    [ cite (cid_of "ladder rung" (Encoding.consistency_id t.enc s.s_name v)) ]
  else if v <= s.s_dlo then
    [ Explanation.weaken [ (1, Lit.negate (Lit.ge s.s_name (v + 1))) ] ]
  else [ Explanation.weaken [ (1, Lit.ge s.s_name v) ] ]

(* A variable FIXED to v contributes `e_i^v >= 1` to the lower row, and it contributes it
   BY CONTRIBUTING NOTHING: its term is -x_ge_v + x_ge_(v+1), whose normalisation moves a
   whole unit onto the right-hand side and leaves exactly ~x_ge_v and x_ge_(v+1) -- which
   are its two bounds, since lo = hi = v.  So there is no line to build here at all, only
   the two leftovers for [bound_cancels], and the degree the lower rule needs is the
   arithmetic's own.  This function exists to say so; deleting it would leave the reader
   hunting for the missing summand. *)
let fixed_leftovers s v = ((if v > s.s_dlo then 1 else 0), if v < s.s_dhi then 1 else 0)

(* The ladder step both count rules end with, in its two directions.

   After the x terms are cleared the upper rule holds `- sum_k c_ge_k >= cdlo - may` and
   the lower one `sum_k c_ge_k >= must - cdlo`.  Neither is yet a literal about the
   bound.  Turning the first into ~c_ge_(may+1) and the second into c_ge_must is the
   same move twice: relate every other rung to the one wanted by a chain, weaken the
   rest away, and divide once.  The division is where the degree rounds UP to 1, and it
   is the only place in this module where [Combine]'s divisor does real work. *)
let ladder_at_most t ~c ~may =
  if may < c.cdlo then
    (* Fewer possible takers than the count's declared minimum.  Every rung clears for
       free -- the terms are negative -- and the row is 0 >= cdlo - may >= 1. *)
    ( List.map
        (fun kk -> Explanation.weaken [ (1, Lit.ge c.cname kk) ])
        (range (c.cdlo + 1) c.cdhi),
      1 )
  else
    ( List.map
        (fun j -> Explanation.term 1 (rung_line t c.cname ~from_:j ~to_:(may + 1)))
        (range (c.cdlo + 1) may)
      @ List.map
          (fun kk -> Explanation.weaken [ (1, Lit.ge c.cname kk) ])
          (range (may + 2) c.cdhi),
      may - c.cdlo + 1 )

let ladder_at_least t ~c ~must =
  if must > c.cdhi then
    ( List.map
        (fun kk -> Explanation.weaken [ (1, Lit.negate (Lit.ge c.cname kk)) ])
        (range (c.cdlo + 1) c.cdhi),
      1 )
  else
    ( List.map
        (fun kk -> Explanation.weaken [ (1, Lit.negate (Lit.ge c.cname kk)) ])
        (range (c.cdlo + 1) (must - 1))
      @ List.map
          (fun kk -> Explanation.term 1 (rung_line t c.cname ~from_:must ~to_:kk))
          (range (must + 1) c.cdhi),
      c.cdhi - must + 1 )

let c_upper_expl t ~k ~poss ~gone ~may =
  let c = k.k_cov in
  let v = c.cv in
  Explanation.deferred (fun () ->
      let tail, divisor = ladder_at_most t ~c ~may in
      Explanation.combine
        ((cite c.ge_cid :: List.concat_map (fun s -> zero_summands t s v) gone)
        @ List.concat_map (fun s -> cost_summands s v) poss
        @ bound_cancels
            ~lo_of:(fun s -> if v < s.s_lo then 1 else 0)
            ~hi_of:(fun s -> if v > s.s_hi then 1 else 0)
            gone
        @ tail)
        divisor)

let c_lower_expl t ~k ~fixed ~others ~must =
  let c = k.k_cov in
  let v = c.cv in
  Explanation.deferred (fun () ->
      let tail, divisor = ladder_at_least t ~c ~must in
      Explanation.combine
        ((cite c.le_cid :: List.concat_map (fun s -> free_summands t s v) others)
        @ bound_cancels
            ~lo_of:(fun s -> fst (fixed_leftovers s v))
            ~hi_of:(fun s -> snd (fixed_leftovers s v))
            fixed
        @ tail)
        divisor)

(* ------------------------------------------------------------------------ propagation *)

exception Found of Store.conflict
exception Moved

let rule_c t store ~snaps ~caps ~apply =
  List.iter
    (fun k ->
      let c = k.k_cov in
      let v = c.cv in
      let dv = List.filter (fun s -> declares s v) snaps in
      let poss = List.filter (fun s -> s.s_lo <= v && v <= s.s_hi) dv in
      let gone = List.filter (fun s -> not (s.s_lo <= v && v <= s.s_hi)) dv in
      let fixed = List.filter (fun s -> s.s_lo = v && s.s_hi = v) dv in
      let others = List.filter (fun s -> not (s.s_lo = v && s.s_hi = v)) dv in
      let may = c.cconst + List.length poss in
      let must = c.cconst + List.length fixed in
      let facts = scope_facts ~snaps:dv ~caps:[ k ] in
      if may < k.k_hi then
        apply ~lower:false c.cx may
          (Reason.because
             ~concludes:(Some (Reason.at_most ~name:c.cname ~decl:c.cdhi may))
             facts
             (c_upper_expl t ~k ~poss ~gone ~may));
      if must > k.k_lo then
        apply ~lower:true c.cx must
          (Reason.because
             ~concludes:(Some (Reason.at_least ~name:c.cname ~decl:c.cdlo must))
             (facts @ if k.k_lo_root then [] else k.k_lo_why)
             (c_lower_expl t ~k ~fixed ~others ~must)))
    caps;
  ignore store

(* One pass.  Rule C first -- it is O(values * n) and it is what turns a shortfall into a
   conflict -- then rule A over every candidate interval all of whose values are in the
   cover.  Both return through [Moved]/[Found]: a pass that changed anything restarts,
   so every interval is examined against a CURRENT snapshot rather than one a push
   earlier in the same pass has invalidated (alldiff's rule, and for its reason). *)
let pass t store =
  let snaps = Array.to_list (Array.map (snap_of store) t.terms) in
  let caps = Array.to_list (Array.map (csnap_of store) t.cov) in
  let apply ~lower x bound j =
    match
      if lower then Store.set_lo store x bound j else Store.set_hi store x bound j
    with
    | Store.Conflict c -> raise (Found c)
    | Store.Changed -> raise Moved
    | Store.Unchanged -> ()
  in
  rule_c t store ~snaps ~caps ~apply;
  let cover_at = Hashtbl.create 16 in
  List.iter (fun k -> Hashtbl.replace cover_at k.k_cov.cv k) caps;
  let los = List.sort_uniq compare (List.map (fun s -> s.s_lo) snaps) in
  let his = List.sort_uniq compare (List.map (fun s -> s.s_hi) snaps) in
  let push ~a ~b ~halls ~caps_ab ~y ~lower x bound =
    apply ~lower x bound
      (Reason.because
         ~concludes:
           (Some
              (if lower then Reason.at_least ~name:y.s_name ~decl:y.s_dlo bound
               else Reason.at_most ~name:y.s_name ~decl:y.s_dhi bound))
         (scope_facts ~snaps ~caps:caps_ab)
         (prune_expl t ~a ~b ~snaps ~halls ~caps:caps_ab ~y ~lower ~bound))
  in
  List.iter
    (fun a ->
      List.iter
        (fun b ->
          if b >= a then
            let found = List.map (fun v -> Hashtbl.find_opt cover_at v) (range a b) in
            if List.for_all Option.is_some found then
              let caps_ab = List.filter_map Fun.id found in
              let cap =
                List.fold_left (fun acc k -> acc + k.k_hi - k.k_cov.cconst) 0 caps_ab
              in
              if cap >= 0 then
                (* Variables whose DECLARED range is inside [a, b] consume their unit of
                   capacity by the model row's own constant folding, so they must be in
                   the confined set rather than outside it; ordering them first is what
                   makes that so whenever there is room for them at all. *)
                let all_in = List.filter (fun s -> a <= s.s_lo && s.s_hi <= b) snaps in
                let folded, rest =
                  List.partition (fun s -> a <= s.s_dlo && s.s_dhi <= b) all_in
                in
                let ordered = folded @ rest in
                let n = List.length ordered in
                if n > cap then
                  let halls = List.filteri (fun i _ -> i < cap) ordered in
                  let y = List.nth ordered cap in
                  push ~a ~b ~halls ~caps_ab ~y ~lower:true y.s_var (b + 1)
                else if n = cap then
                  List.iter
                    (fun y ->
                      if
                        not
                          (List.exists (fun s -> String.equal s.s_name y.s_name) ordered)
                      then
                        if a <= y.s_lo && y.s_lo <= b then
                          push ~a ~b ~halls:ordered ~caps_ab ~y ~lower:true y.s_var (b + 1)
                        else if a <= y.s_hi && y.s_hi <= b then
                          push ~a ~b ~halls:ordered ~caps_ab ~y ~lower:false y.s_var
                            (a - 1))
                    snaps)
        his)
    los;
  false

let rec loop t store = if try pass t store with Moved -> true then loop t store

let propagate t store =
  try
    loop t store;
    Propagator.Fixpoint
  with Found c -> Propagator.Conflict c
