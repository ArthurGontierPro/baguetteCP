(* Model.t -> the store, the PB encoding and the propagator instances the engine runs.

   This is the `flatzinc -> core` edge docs/ARCHITECTURE.md section 1 always had in its
   module map: the translation lives on this side of the boundary because core must not
   depend on flatzinc. Everything below is the FlatZinc-shaped half of what
   test/unit/test_endtoend.ml does by hand over its own miniature model type; that file
   is the worked example this one follows.

   ---------------------------------------------------------------------------
   Variable identity is load-bearing. Do not reorder anything here.
   ---------------------------------------------------------------------------

   [compile] builds the store with variables in **exactly [Model.vars] order**, so that
   for every [i],

       Baguette_core.Var.of_int i   denotes   Model.var m i

   and [Store.name store (Var.of_int i) = (Model.var m i).v_name].

   The CLI depends on that identity and cannot detect its violation. It turns a
   [Search.assignment] -- a [(Var.t * int) list] -- back into an [int array] indexed by
   *model* variable index, and hands that array both to the independent re-check of
   invariant I-S1 and to the FlatZinc output printer. If the two numberings disagree,
   the re-check validates a permuted assignment (which for a symmetric-looking model can
   easily still satisfy every constraint) and the solver prints a wrong answer with a
   proof the checker accepts. There is no test that catches a permutation after the
   fact; the only defence is that the array is built here, once, by a plain
   [Array.map] over [m.vars], and that nothing filters, sorts or deduplicates it.

   The same order is used for [Encoding.declare_int], so the .opb's variable names line
   up with the store's too -- and D-0010 records why those two must agree beyond mere
   tidiness: a propagator's explanation states a bound relative to the variable's
   *declared* bound, which it reads from the store, while the model row's constant comes
   from the encoding's declared bound. A mismatch there produces a proof that justifies
   a different constraint from the one the solver propagated.

   ---------------------------------------------------------------------------
   One propagator instance per model row (D-0011)
   ---------------------------------------------------------------------------

   Every instance is given its own row id at construction. An instance without one
   falls back to the ambient row, which carries no payload and therefore cannot
   say *which* row it meant; D-0011 records why no routing scheme downstream can
   recover it (the trail stores [{ var; old; why }] and no propagator identity), and
   D-0015 records that test_endtoend.ml shipped exactly that bug by computing the ids
   and then discarding them. So:

   - [Int_lin_le] is one row and one [Linear.t].
   - [Int_lin_eq] is *two* rows -- the `<=` row and the `>=` row, the latter posted from
     the negated terms -- and two [Linear.t] values from [Lin_eq.make], posted as two
     independent instances. [Encoding.add_equality] is deliberately not used: it takes
     PB literal terms, not integer terms, and would not go through the order-encoding
     expansion these rows need.
   - [Int_lin_ne] is *two* rows and *one* instance -- the one asymmetric shape here,
     and deliberately so. The rows are [Encoding.add_int_lin_ne]'s A/B pair over a
     shared auxiliary Boolean, because a disequality is not a single PB inequality; the
     single [Ne.t] cites *neither* of them, and the pair of ids is dropped rather than
     stored. lib/core/prop/ne.ml's header is the argument: every explanation that
     propagator builds is a [Clause] stating its own content in full, so it never names
     a row, and D-0011's hazard -- the ambient row, meaning "whatever
     ctx.model_id points at" -- cannot arise. Handing [Ne.make] a row id it does not
     use would be worse than dropping one: it would imply a citation that never happens.
   - [Int_le] / [Int_lt] / [Int_eq] are the same shapes over `a - b`, and [Int_ne] is
     the [Int_lin_ne] shape over `a - b`, packed under [Ne.Int_ne] rather than [Ne] so
     the instance reports the builtin the model actually wrote.

   ---------------------------------------------------------------------------
   Normalisation happens once, and both halves read the same list
   ---------------------------------------------------------------------------

   model.ml's own comment allows a term list to repeat a variable index. Duplicates are
   merged by summing coefficients and zero coefficients are dropped -- exactly once, by
   [normalise_terms], whose single result feeds both [Encoding.add_int_lin_le] (the row
   in the .opb) and [Linear.make] (the propagator). Normalising twice, or normalising
   one side only, is how the row and the propagator come to state different constraints;
   veripb would then accept a proof of something the solver never did, which is the
   failure mode D-0009 records.

   ---------------------------------------------------------------------------
   Nothing is silently ignored (SPEC 2.1, normative)
   ---------------------------------------------------------------------------

   "Encountering a builtin outside the implemented set MUST produce a clear error naming
   the builtin and exit non-zero. It MUST NOT silently ignore the constraint." Every
   rejection below goes through [Error.failf] with a position, so the CLI's existing
   error path prints it like any parse error. [Model.t] carries no position for the
   solve item, so the objective and the search annotations borrow the position of a
   variable they mention and fall back to [Pos.unknown] when they mention none.

   ---------------------------------------------------------------------------
   The arithmetic cap (roadmap M1-T23)
   ---------------------------------------------------------------------------

   This file is where the checked arithmetic in lib/core/prop/ stops being a runtime
   tripwire and becomes a property of every model the CLI accepts. Two checks, on the
   two things that multiply:

     [check_declared_bound]  every declared bound satisfies |bound| <= Checked.limit
     [check_row]             every posted row satisfies
                               |rhs| + sum_i |a_i| * max(|lo_i|, |hi_i|) <= Checked.limit

   Neither implies the other. A huge coefficient over a two-value domain overflows
   with no large bound anywhere; and a variable that appears in no constraint at all
   is still handed to [Domain.make] and [Encoding.declare_int], so it needs its own
   check. lib/core/checked.ml's header derives the limit: everything the propagators
   and the .opb expansion compute from a row of magnitude M is bounded by 9M + 6, and
   the limit is max_int / 16.

   **This is an overflow cap, not a width cap.** The bound the limit places on a
   declared domain is |bound| <= 2.88 * 10^17, so a width of 5.7 * 10^17 passes it --
   thirteen orders of magnitude above the width at which D-0028's measured cost (a
   justification is Theta(declared width) per other term per pruning: 29.8 MB in one
   `pol` line at w = 10^6) becomes unusable. The two caps have different
   justifications and different right answers, and D-0029 point 3 keeps them apart
   deliberately. The declared-bound check below exists because a bound is one of the
   two things that multiply, and for no other reason.

   The checks run *before* the row is posted, which is the whole point. The gap
   M1-T23 closed was not that a propagator pruned wrongly -- it was that
   [Encoding.linear_terms_int_lin_le] folds the constant sum_i a_i * lo_i with the
   same wrapping arithmetic the propagator's slack uses, so the .opb row and the
   solver agreed on a model that was not the one in the .fzn, and veripb had nothing
   to disagree with. lib/proof/ cannot defend itself against that (a row has to be
   written; there is no "decline" for an artefact). Refusing the model here is what
   defends it, and refusing it *here* rather than at the first propagation is what
   keeps [Checked.Overflow] off the search path entirely.

   ---------------------------------------------------------------------------
   The width cap (roadmap M1-T54, decided in D-0041; SPEC 3.1 is normative)
   ---------------------------------------------------------------------------

   The separate decision D-0028 point 3 asked for, and the one the section above is
   careful not to be. A third check, on the thing that is *expanded* rather than the
   two things that multiply:

     [reject_declared_width]  every declared domain satisfies
                                hi - lo <= Encoding.max_order_width

   The cap and its derivation live in lib/proof/encoding.ml, beside the ladder they
   bound, and are NAMED from here rather than restated. What this file adds is the
   position: [Encoding] can refuse but cannot say which line of which .fzn, so the
   user-facing refusal is here -- exit 3, like every other rejection in this file --
   and [Encoding.Width_too_large] is the backstop for a caller that does not come
   through this door: a second front end, or a test. That is the two-layer shape of
   M1-T32 / I-X8, and it is here for the same reason.

   The exception is deliberately NOT [Encoding.Unrepresentable]. bin/main.ml's arm for
   that one exits 4 and tells the reader baguette's own invariant has failed, which is
   right for a wrapped row (Compile's arithmetic cap should have caught it) and would
   be actively wrong here: an over-wide domain is a model problem, reported at the
   model, with the model's exit code.

   ---------------------------------------------------------------------------
   What the setup costs, and what of it is this file's (M16-file-review-T5, D-0193)
   ---------------------------------------------------------------------------

   On the Challenge's costliest setups [compile]'s own code is a few percent; the rest
   is what it calls ([Encoding]'s declarations and rows, [Engine.create], the globals'
   [make]). Its own rules: [normalise_terms] answers a short row over distinct
   variables without a table; the name check is one sized [Model.Names]; and under
   [Discard_rows] (`--no-proof`) the objective's .opb line, one term per rung of the
   objective, is not built, because the header that would print it is never written.

   Three paths are quadratic in an argument's length and are left so, each bounded by
   what the .fzn states and none seen in a profile: [post_all_different] tests every
   pair of its n operands for a constant or a repeat (O(n^2) cheap tests; the global's
   own [Alldiff.make] dominates long before), [post_global_cardinality] filters the
   movable variables once per cover value (O(cover x n)), and [post_regular] finds a
   state's predecessors per symbol run (O(n x Q^2 x runs), the size of its own table
   times Q). *)

module Var = Baguette_core.Var
module Checked = Baguette_core.Checked
module Domain = Baguette_core.Domain
module Store = Baguette_core.Store
module Propagator = Baguette_core.Propagator
module Linear = Baguette_core.Linear
module Lin_eq = Baguette_core.Lin_eq
module Ne = Baguette_core.Ne
module Alldiff = Baguette_core.Alldiff
module Element = Baguette_core.Element
module Gcc = Baguette_core.Gcc
module Maxmin = Baguette_core.Maxmin
module Cumulative = Baguette_core.Cumulative
module Regular = Baguette_core.Regular (* M7-T28, D-0146 *)
module Inverse = Baguette_core.Inverse (* M7-T28, D-0151 *)
module Member = Baguette_core.Member (* M7-T28, D-0159 *)
module View = Baguette_core.View

(* M2-L12/D-0052: the clause propagator was widened to general order literals and its
   file renamed [Clause]. The Boolean face this front end builds is [Clause.make] plus
   the submodules below, which still declare DOMAIN because their [0, 1] restriction
   makes that true; the widened module itself declares BOUNDS. Aliased under the old name
   so that every call site here keeps saying which builtin it is packing. *)
module Bool_clause = Baguette_core.Clause
module Bool2int = Baguette_core.Bool2int
module Reif_lin_le = Baguette_core.Reif_lin_le
module Reif_lin_eq = Baguette_core.Reif_lin_eq
module Arith = Baguette_core.Arith
module Engine = Baguette_core.Engine
module Encoding = Baguette_proof.Encoding
module Opb = Baguette_proof.Opb
module Search = Baguette_core.Search
module Lit = Baguette_proof.Lit

type t = {
  store : Baguette_core.Store.t;
  engine : Baguette_core.Engine.t;
  encoding : Baguette_proof.Encoding.t;
  objective : Baguette_core.Search.objective option;
      (* M5-T1. [None] is `solve satisfy;` and every pre-M5 model. [Some] is what
         [bin/main.ml] hands to [Search.optimise], resolved HERE rather than there
         because the declared bounds the branch-and-bound floor case turns on
         (lib/core/search.ml, [type bnb] note (2)) are this module's -- they are the
         bounds the .opb objective line was written against, not whatever the store's
         have narrowed to by the time anyone asks. *)
  order : Baguette_core.Search.order option;
      (* M7-T2. [None] is a model with no search annotation, and it is not merely a
         default: it is the same value [Search.solve]'s [?order] already defaults to
         ([spec_order]), so an unannotated model branches byte-for-byte as it did before
         this field existed. [Some] is the annotation, HONOURED -- docs/SPEC.md 3.4 says
         it must be, and until M7-T2 the only way to honour it was to refuse the model.
         Resolved here, beside the objective, for the same reason: the annotation names
         model variable INDICES, and this module is the one that promises the store is
         built in [Model.vars] order. *)
}

(* ------------------------------------------------------------------- term handling *)

(* Merge repeated variable indices by summing their coefficients, then drop the terms
   that cancelled to zero. First-occurrence order is preserved so the emitted row is a
   deterministic function of the model -- a proof that changes shape between runs is a
   proof nobody can diff against a previous failure.

   Called once per constraint; its result is what both the .opb row and the propagator
   are built from. See the module header. *)
let normalise_terms_by_table (terms : (int * int) list) : (int * int) list =
  let coeff = Hashtbl.create 16 in
  let order = ref [] in
  List.iter
    (fun (c, i) ->
      match Hashtbl.find_opt coeff i with
      | None ->
          Hashtbl.replace coeff i c;
          order := i :: !order
      | Some c0 -> Hashtbl.replace coeff i (Checked.add c0 c))
    terms;
  List.rev !order
  |> List.filter_map (fun i ->
         let c = Hashtbl.find coeff i in
         if c = 0 then None else Some (c, i))

(* M16-file-review-T5 (D-0193): a row whose variables are pairwise distinct -- nearly
   every row a flattener writes -- has nothing to merge, so its result is its own terms
   with the zero coefficients dropped, which is what the table below computes for it (each
   index occurs once, so its entry is its coefficient and the order is the input's). Up to
   [distinct_scan_max] terms that is decided by comparing the indices pairwise, where the
   table cost one polymorphic [Hashtbl] of 16 buckets per constraint; a longer row keeps
   the table, so the scan stays O(k^2) for k <= 8. *)
let distinct_scan_max = 8

let rec indices_distinct = function
  | [] -> true
  | (_, i) :: rest -> List.for_all (fun (_, j) -> j <> i) rest && indices_distinct rest

let rec short_list n = function
  | [] -> true
  | _ :: rest -> n > 0 && short_list (n - 1) rest

let normalise_terms (terms : (int * int) list) : (int * int) list =
  if short_list distinct_scan_max terms && indices_distinct terms then
    List.filter (fun (c, _) -> c <> 0) terms
  else normalise_terms_by_table terms

let negate_terms terms = List.map (fun (c, i) -> (Checked.neg c, i)) terms

(* [a - b <= offset], as a term list over model variable indices plus a right-hand
   side, with constant operands folded into the right-hand side so the term list only
   ever mentions real variables (model.ml's own convention for its linear forms).

   [int_le(x, 2)] is [Int_le (Var x, Const 2)], hence terms [(1, x)] and rhs 2. *)
let difference_terms (a : Model.operand) (b : Model.operand) ~offset =
  let terms = ref [] and rhs = ref offset in
  (match a with
  | Model.Var i -> terms := (1, i) :: !terms
  | Model.Const n -> rhs := Checked.sub !rhs n);
  (match b with
  | Model.Var j -> terms := (-1, j) :: !terms
  | Model.Const n -> rhs := Checked.add !rhs n);
  (List.rev !terms, !rhs)

(* ---------------------------------------------------------------------- positions *)

let operand_pos (m : Model.t) (op : Model.operand) =
  match op with
  | Model.Var i when i >= 0 && i < Model.nvars m -> (Model.var m i).Model.v_pos
  | _ -> Pos.unknown

let rec search_pos (m : Model.t) (s : Model.search) =
  match s with
  | Model.Int_search (i :: _, _, _) when i >= 0 && i < Model.nvars m ->
      (Model.var m i).Model.v_pos
  | Model.Int_search _ -> Pos.unknown
  | Model.Seq (s :: _) -> search_pos m s
  | Model.Seq [] -> Pos.unknown

(* --------------------------------------------------------------------- rejections *)

(* SPEC 2.1 is normative about the shape of these: name the thing, say why it is not
   there, and exit non-zero. Each one asserts on its message in test_compile.ml, so
   the wording is part of the tested surface, not decoration. *)

(* M7-T11 REMOVED `reject_set_domain`, which used to refuse `var {1,3,5}: x` here.

   It was not weakened; the thing it was protecting against was fixed. Its message said
   exactly what was missing -- "`Encoding.declare_int` takes only ~lo and ~hi, so the
   holes in a set domain have no representation in the .opb" -- and so encoding the hull
   instead would have been a RELAXATION: the solver could report UNSAT and hand veripb a
   refutation of an .opb that is satisfiable.

   [Encoding.declare_int_with_holes] now gives the holes a representation, one clause
   each, in the same order ladder and of the mirror polarity. See that function's header
   for the direction and why getting it backwards would be silently unsound, and D-0072
   for the decision. With the holes in the .opb the hull is no longer a relaxation, so
   the refusal has nothing left to protect. *)

(* M5-T1 narrowed this from "every objective" to "an objective that is not a variable".

   `solve minimize 3;` is legal FlatZinc and it is refused rather than answered, because
   the artefact it would need cannot be built: `conclusion BOUNDS` requires the .opb to
   carry a `min:` line (docs/SPEC.md section 4.3 -- "without one the checker raises
   InvalidProof"), and a constant objective has no order literals to write one out of.
   Answering it as a satisfaction problem and printing `==========` would be claiming an
   optimality the proof does not contain, which is the one thing this project does not
   do. A model that really wants it can introduce `var 3..3: obj` and minimise that. *)
let reject_constant_objective pos what value =
  Error.failf pos
    "unsupported solve goal `%s %d`: the objective must be a VARIABLE. `conclusion \
     BOUNDS` requires the .opb to carry a `min:` objective line (docs/SPEC.md section \
     4.3), and that line is the objective variable's order encoding -- a constant has \
     none, so there is nothing to write and nothing to prove optimal. Introduce `var \
     %d..%d: obj;` and write `solve %s obj;`."
    what value value value what

(* M7-T2 kept this, and that is the point of it. [Search] now implements input_order and
   first_fail over indomain_min and indomain_max, which is what the MiniZinc challenge
   corpus overwhelmingly asks for -- but the tail (smallest, largest, dom_w_deg,
   indomain_split, indomain_median, ...) is NOT implemented, and a model asking for one
   is refused BY NAME rather than quietly given something else. docs/SPEC.md section 3.4
   says the annotation MUST be honoured when present; silently substituting a strategy
   solves a different problem and reports it as this one's answer. *)
let reject_search pos ~annotation =
  Error.failf pos
    "unsupported search annotation %s: baguette implements the `input_order` and \
     `first_fail` variable choices over the `indomain_min` and `indomain_max` value \
     choices, and `seq_search` over those. It does not implement this one, and \
     docs/SPEC.md section 3.4 says the annotation MUST be honoured when present -- so it \
     is rejected rather than silently replaced by a strategy that would solve a \
     different problem. Remove the annotation, or write one of the implemented forms."
    annotation

(* M2-T1 / M2-T2. The Boolean row's builtins take `var bool` arguments, and a `var bool`
   is the one domain [Encoding.declare_bool] gives the order encoding on [0, 1]
   (docs/PROOF-FORMAT.md section 3, "Booleans"). A `var 0..1` is *not* accepted in its
   place: FlatZinc types a Boolean and a zero-one integer differently, and the difference
   is not cosmetic here -- lib/core/prop/bool_clause.ml spells every literal as
   [Lit.bool_true] / [Lit.bool_false], and SPEC 2.2 prints a `bool` output as
   `false`/`true` under its *declared* type. Accepting an int would make the propagator's
   literals and the declaration disagree about what the variable is. *)

let reject_non_bool_var pos ~builtin ~what (v : Model.var) =
  Error.failf pos
    "builtin `%s`: %s must be a `var bool` or a Boolean constant, but `%s` is declared \
     over %s. A `var 0..1` is not accepted in its place: docs/PROOF-FORMAT.md section 3 \
     gives a `var bool` exactly one Boolean, `%s_ge_1`, and SPEC 2.2 prints it as \
     false/true under its declared type, so an integer variable here would be encoded \
     and printed as something the model did not declare. Declare it `var bool`, or use \
     `bool2int` to channel between the two."
    builtin what v.Model.v_name
    (Model.string_of_domain v.Model.v_dom)
    v.Model.v_name

let reject_non_bool_const pos ~builtin ~what n =
  Error.failf pos
    "builtin `%s`: %s must be a Boolean, but the constant %d was given. `true` and \
     `false` fold to 1 and 0; no other value is a Boolean."
    builtin what n

(* roadmap M1-T23. The two arithmetic rejections. [Checked.limit] and the 9M + 6
   envelope it is chosen against are derived in lib/core/checked.ml's header; the
   message repeats the figure rather than the derivation because the person reading it
   is holding a model, not the solver. *)

let reject_declared_bound (v : Model.var) lo hi =
  Error.failf v.Model.v_pos
    "variable `%s` is declared over %d..%d, which exceeds baguette's arithmetic limit: a \
     declared bound may not exceed +/-%d. baguette computes over OCaml's native 63-bit \
     int, which wraps silently, and a wrapped product is not merely a wrong bound: \
     lib/proof/encoding.ml expands the .opb row from the same arithmetic the propagator \
     uses, so the corrupted row and the corrupted pruning agree and veripb accepts a \
     refutation of a model you did not write. The limit leaves every intermediate the \
     solver and the encoding compute inside the representable range. Rescale the model, \
     or shift the domain towards zero."
    v.Model.v_name lo hi Checked.limit

(* M1-T54, from D-0028 point 3 and decided in D-0041. The width rejection. The cap
   itself lives in
   [Encoding] -- next to the ladder it bounds, with its derivation -- and is named from
   here rather than copied: nothing in this tree has cost more than two statements of one
   envelope drifting apart (D-0029's [Arith] copy is a copy only because lib/proof cannot
   name lib/core; lib/flatzinc names lib/proof, so there is no excuse for a second
   constant here).

   Two readers, two messages. [Encoding.Width_too_large] is what a caller that did not
   come through here gets; this is the one a person holding a .fzn gets, and it says
   plainly that the limit is baguette's rather than FlatZinc's, because the model is
   legal and the refusal is a deliberate choice about proof size. *)
let reject_declared_width (v : Model.var) lo hi =
  Error.failf v.Model.v_pos
    "variable `%s` is declared over %d..%d, a width of %d, and baguette's limit is %s. \
     Every integer variable is given the order encoding eagerly, so a declared width of \
     w costs w-1 ladder clauses in the .opb before any constraint is posted, and makes \
     every justification that cancels this variable's contribution Theta(w) literals \
     long. Measured: two variables declared 0..999999 produce a 156 MB .opb and a single \
     29.8 MB proof line, for a model that is infeasible by inspection -- a proof the \
     checker accepts and nobody can store or review. This model is legal FlatZinc; the \
     limit is baguette's, and refusing is deliberate rather than a defect. Narrow the \
     declared domain, or rescale the model so the same question fits a smaller one. \
     M7-T1: this refusal is OFF by default; you are seeing it because a width limit was \
     asked for with --max-order-width or BAGUETTE_MAX_ORDER_WIDTH."
    v.Model.v_name lo hi (hi - lo)
    (Encoding.order_width_limit_string ())

let reject_row pos ~what ~magnitude =
  Error.failf pos
    "%s exceeds baguette's arithmetic limit: its magnitude |rhs| + sum |coeff| * \
     max(|lo|, |hi|) over the declared domains is %s, and the limit is %d. That sum \
     bounds every product and partial sum the propagator and the .opb expansion of this \
     row compute, and baguette computes over OCaml's native 63-bit int, which wraps \
     silently -- with the row and the propagator wrapping identically, so the proof \
     would verify against an .opb that is not this model. Rescale the coefficients, or \
     narrow the declared domains."
    what
    (match magnitude with
    | Some m -> string_of_int m
    | None -> "larger than a 63-bit int can hold")
    Checked.limit

(* M7-T2. [Model.search] is a list of annotations and [Seq] nests, so the whole thing
   flattens to a list of [Search.phase] consulted in order -- which is exactly
   `seq_search`'s meaning, and it is why nesting needs no representation here: a
   `seq_search` inside a `seq_search` is the concatenation of their phases.

   A variable the annotation never mentions still has to be branched on, and
   [Search.sequence] falls back to [Search.spec_order] for those. That fallback is the
   one place where an annotated model's search is NOT the annotation, and it is what
   docs/SPEC.md section 3.4 has to say out loud.

   The annotation's array carries MODEL variable indices, and this module's contract is
   that the store is built in [Model.vars] order (see the module header), so the index is
   the [Var.t]. Nothing else in this file may assume that; this is the place that
   promises it. *)
let rec phases_of_search (m : Model.t) (s : Model.search) :
    Baguette_core.Search.phase list =
  match s with
  | Model.Seq subs -> List.concat_map (phases_of_search m) subs
  | Model.Int_search (idxs, vc, vl) ->
      let pos = search_pos m s in
      List.iter
        (fun i ->
          if i < 0 || i >= Model.nvars m then
            Error.failf pos "search annotation names variable index %d, out of range" i)
        idxs;
      let p_var =
        match vc with
        | Model.Input_order -> Baguette_core.Search.input_order
        | Model.First_fail -> Baguette_core.Search.first_fail
        | Model.Anti_first_fail -> Baguette_core.Search.anti_first_fail
        | Model.Smallest -> Baguette_core.Search.smallest
        | Model.Largest -> Baguette_core.Search.largest
      in
      let p_val =
        match vl with
        | Model.Indomain_min -> Baguette_core.Search.indomain_min
        | Model.Indomain_max -> Baguette_core.Search.indomain_max
        | Model.Indomain_split -> Baguette_core.Search.indomain_split
        (* M7-T12. The only value choice that can return an [Assign]; see
           [Search.indomain_median] for the dispatch and D-0077 for why the shape
           exists. *)
        | Model.Indomain_median -> Baguette_core.Search.indomain_median
      in
      [
        {
          Baguette_core.Search.p_vars = Array.of_list (List.map Var.of_int idxs);
          p_var;
          p_val;
        };
      ]

(* [None] when the model carries no search annotation, which must stay
   indistinguishable from the pre-M7-T2 behaviour: [Search.solve]'s [?order] then
   defaults to [spec_order], the same function, rather than to a [sequence] with an empty
   phase list that would merely delegate to it. Same tree, same proof. *)
let order_of_model (m : Model.t) : Baguette_core.Search.order option =
  match List.concat_map (phases_of_search m) m.Model.search with
  | [] -> None
  | phases -> Some (Baguette_core.Search.sequence phases)

(* --------------------------------------------------------------------- declaration *)

let bounds_of_domain (v : Model.var) =
  match v.Model.v_dom with
  | Model.Dbool -> (0, 1)
  | Model.Drange (lo, hi) ->
      if lo > hi then
        Error.failf v.Model.v_pos "variable `%s` has the empty domain %d..%d"
          v.Model.v_name lo hi
      else (lo, hi)
  | Model.Dset [] ->
      Error.failf v.Model.v_pos "variable `%s` has an empty domain" v.Model.v_name
  | Model.Dset values ->
      (* The HULL of the value set. The holes inside it are [holes_of_domain] below,
         and the two are computed apart because everything between here and
         [Store.create] -- the arithmetic cap, the width cap, the .opb `min:` line --
         is about the hull and nothing else. M7-T11. *)
      ( List.fold_left min (List.hd values) values,
        List.fold_left max (List.hd values) values )

(* The values strictly inside the declared hull that the declaration excludes. Empty for
   every domain but a set literal, and by construction never contains [lo] or [hi]: the
   hull is the min and max of the value set, so both ends are present. M7-T11. *)
let holes_of_domain (v : Model.var) =
  match v.Model.v_dom with
  | Model.Dbool | Model.Drange _ | Model.Dset [] -> []
  | Model.Dset values ->
      let lo, hi = bounds_of_domain v in
      let present = List.sort_uniq Stdlib.compare values in
      let rec go v present acc =
        if v > hi then List.rev acc
        else
          match present with
          | p :: rest when p = v -> go (v + 1) rest acc
          | _ -> go (v + 1) present (v :: acc)
      in
      go lo present [] |> List.filter (fun h -> h > lo && h < hi)

(* The .opb's Boolean variable names come from [Lit.sanitize], which maps every
   character outside [A-Za-z0-9_] to '_'. Two distinct FlatZinc identifiers can collide
   under it -- the array element `x[1]` and a scalar called `x_1_` both become `x_1_` --
   and a collision would silently merge their order literals inside [Opb.normalise],
   producing a row that is not the model's. [Encoding] keys on the unsanitised name and
   so would not notice. Checked once, here, because this is the only place that knows
   the whole variable list.

   M16-file-review-T5 (D-0193): the table is over [String] and sized for every variable
   at once. It was a polymorphic [Hashtbl] created at 64 and doubled about fourteen times
   on a million-variable model, re-hashing every name at each doubling. It is only
   probed, never iterated, so its layout is not observable. *)
let check_name_collisions (m : Model.t) =
  let seen = Model.Names.create (max 64 (Array.length m.Model.vars)) in
  Array.iter
    (fun (v : Model.var) ->
      let s = Lit.sanitize v.Model.v_name in
      match Model.Names.find_opt seen s with
      | Some other when not (String.equal other v.Model.v_name) ->
          Error.failf v.Model.v_pos
            "variables `%s` and `%s` both become `%s` in the .opb (identifiers are \
             sanitised for the pseudo-Boolean format, docs/PROOF-FORMAT.md section 3), \
             so their encodings would be indistinguishable. Rename one of them."
            other v.Model.v_name s
      | Some _ ->
          Error.failf v.Model.v_pos "variable `%s` is declared more than once"
            v.Model.v_name
      | None -> Model.Names.replace seen s v.Model.v_name)
    m.Model.vars

(* ------------------------------------------------------------------------ compile *)

(* A propagator with everything decided except the id the engine will know it by.

   That id is not a label: [Engine.create] builds its array from the list it is given
   and then looks an instance up as [instances.(id)] (lib/core/engine.ml), so an
   instance's id must equal its *position* in that list -- and an arm of the match
   below, which may yield one instance or two, cannot know its own position. So each
   arm yields pending instances and [compile] closes them over their index once, at the
   end, with a single [List.mapi]. *)
type pending = int -> Propagator.instance

(* M2-L6: every [Linear.t] in this solver is packed here -- including both halves of an
   [int_lin_eq] (D-0011) and the [int_le]/[int_lt]/[int_eq] shapes that delegate -- so
   teaching [Linear] its own PB row is taught once, here, and reaches all of them. *)
(* [~mixed] (M8-bits-encoding-T2, D-0132 section 2.7; D-0153): [None] for a row with no
   term on the bits encoding, [Some bits_n] for a row with one. T2 packed the latter
   WITHOUT its PB row, because [Linear.pb_row] spelled the order expansion and the .opb
   holds the bits; since D-0153 the row is spelled as the .opb holds it
   ([Linear.pb_row ~bits_n]) and PB conflict analysis instantiates its bits blocks
   through their bridges before it resolves (lib/core/ladder.ml, "The bits arm"). *)
let linear_row ~mixed (lin : Linear.t) =
  match mixed with
  | None -> fun store -> Some (Linear.pb_row store lin)
  | Some bits_n -> fun store -> Some (Linear.pb_row ~bits_n store lin)

let pack_linear ~mixed (lin : Linear.t) : pending =
 fun id ->
  Propagator.pack ~id ~idempotent:true ~row:(linear_row ~mixed lin)
    (module Linear : Propagator.S with type t = Linear.t)
    lin

(* [Ne] and [Ne.Int_ne] are one propagator over one [Ne.t]; they differ only in the
   [name] the packed instance reports, so each builtin is packed under its own. *)
let pack_lin_ne (p : Ne.t) : pending =
 fun id -> Propagator.pack ~id (module Ne : Propagator.S with type t = Ne.t) p

let pack_ne (p : Ne.t) : pending =
 fun id -> Propagator.pack ~id (module Ne.Int_ne : Propagator.S with type t = Ne.t) p

(* The five packings of one clause propagator (M2-T1). [Bool_clause] and its four
   submodules share [t], [make], [vars] and [propagate] outright and differ only in the
   [name] the packed instance reports, exactly as [Ne] and [Ne.Int_ne] do: an instance
   says which builtin the model actually wrote, which is what a trace line or a failure
   message has to say to be worth reading. A clause decomposition means several
   instances carry the same name, which is correct -- they came from one builtin. *)
let pack_clause_as (type a) (module P : Propagator.S with type t = a) (p : a) : pending =
 fun id -> Propagator.pack ~id (module P) p

let pack_bool_clause (p : Bool_clause.t) : pending =
  pack_clause_as
    (module Bool_clause.Bool_clause : Propagator.S with type t = Bool_clause.t)
    p

let pack_array_bool_or (p : Bool_clause.t) : pending =
  pack_clause_as
    (module Bool_clause.Array_bool_or : Propagator.S with type t = Bool_clause.t)
    p

let pack_array_bool_and (p : Bool_clause.t) : pending =
  pack_clause_as
    (module Bool_clause.Array_bool_and : Propagator.S with type t = Bool_clause.t)
    p

let pack_bool_eq (p : Bool_clause.t) : pending =
  pack_clause_as (module Bool_clause.Bool_eq : Propagator.S with type t = Bool_clause.t) p

(* M3-T4: the reification dispatcher's four faces. One [Reif.t] per reified builtin,
   packed under the builtin the model wrote (the [Ne] / [Ne.Int_ne] rule again), and
   WITHOUT [~row:]: an instance here stands for two or four rows and [Propagator.pb_row]
   promises exactly one, so the honest answer is the default [None] and M2-L6's clause
   fallback. lib/core/prop/reif.ml's header carries the argument. *)
let pack_reif_as (type a) (module P : Propagator.S with type t = a) (p : a) : pending =
 fun id -> Propagator.pack ~id (module P) p

let pack_int_lin_le_reif (p : Reif_lin_le.t) : pending =
  pack_reif_as
    (module Reif_lin_le.Int_lin_le_reif : Propagator.S with type t = Reif_lin_le.t)
    p

let pack_int_le_reif (p : Reif_lin_le.t) : pending =
  pack_reif_as
    (module Reif_lin_le.Int_le_reif : Propagator.S with type t = Reif_lin_le.t)
    p

let pack_int_eq_reif (p : Reif_lin_eq.t) : pending =
  pack_reif_as
    (module Reif_lin_eq.Int_eq_reif : Propagator.S with type t = Reif_lin_eq.t)
    p

let pack_int_ne_reif (p : Reif_lin_eq.t) : pending =
  pack_reif_as
    (module Reif_lin_eq.Int_ne_reif : Propagator.S with type t = Reif_lin_eq.t)
    p

let pack_bool_not (p : Bool_clause.t) : pending =
  pack_clause_as
    (module Bool_clause.Bool_not : Propagator.S with type t = Bool_clause.t)
    p

let pack_bool2int (p : Bool2int.t) : pending =
 fun id -> Propagator.pack ~id (module Bool2int : Propagator.S with type t = Bool2int.t) p

(* M4-T4b. Every row of the arithmetic family is a [Linear] over a row the .opb really
   contains, so these pack exactly as [pack_linear] does -- [~row:] included, because
   each one IS one row and M2-L6 can resolve it. What differs is only the [name] the
   instance reports, which is the builtin the model wrote rather than `int_lin_le`;
   lib/core/prop/arith.ml's faces exist for that and nothing else. *)
let pack_arith_row (module P : Propagator.S with type t = Linear.t) ~mixed
    (lin : Linear.t) : pending =
 fun id ->
  (* M6-T18: a ROW face is [Linear] and makes [pack_linear]'s idempotence claim; the
     guard faces below are reifications and do not (lib/core/propagator.ml, above
     [pack]). [~mixed] as in [pack_linear]. *)
  Propagator.pack ~id ~idempotent:true ~row:(linear_row ~mixed lin) (module P) lin

let pack_times_row ~mixed (p : Linear.t) : pending =
  pack_arith_row (module Arith.Times_row : Propagator.S with type t = Linear.t) ~mixed p

let pack_div_row ~mixed (p : Linear.t) : pending =
  pack_arith_row (module Arith.Div_row : Propagator.S with type t = Linear.t) ~mixed p

let pack_abs_row ~mixed (p : Linear.t) : pending =
  pack_arith_row (module Arith.Abs_row : Propagator.S with type t = Linear.t) ~mixed p

(* M8-bits-encoding-T3 continuation (D-0134 section 9): `bool2int(b, x)` over a BITS
   integer. lib/core/prop/bool2int.ml justifies its four pushes with [Clause]s, RUP over
   its two rows and x's LADDER, and a bits x has no ladder (no bound crosses a bits row
   by unit propagation, D-0127). So over a bits x the channelling is posted as what it
   is, the equality x = b: the same two rows in the same order, each with a [Linear]
   instance -- whose pushes are Bool2int's four, one per row and bound -- justified by
   [Linear]'s bits `pol` (D-0132). This face is the [Arith] faces' device: the instance
   reports the builtin the model wrote. Defined here and not in bool2int.ml because the
   choice is the compiler's, made from the scope, as [post_maxmin]'s shape is. *)
module Bool2int_row : Propagator.S with type t = Linear.t = struct
  type t = Linear.t

  let name = "bool2int"
  let consistency = Propagator.Bounds
  let vars = Linear.vars
  let propagate = Linear.propagate
end

let pack_bool2int_row ~bits_n (p : Linear.t) : pending =
  pack_arith_row
    (module Bool2int_row : Propagator.S with type t = Linear.t)
    ~mixed:(Some bits_n) p

(* ---------------------------------------------------------------------------
   M8-bits-encoding-T2: eligibility for the bits encoding, by SCOPE (D-0130 section 3.4,
   D-0132 section 2.7)
   ---------------------------------------------------------------------------

   The width half is [Encoding.wants_bits]. The scope half is this: a variable is held
   on the order encoding, whatever `--bits-above` says, when any row the model will post
   over it names its order literals per value or when a propagator over it justifies
   with a [Clause] -- because the .opb is closed before the first proof line (I-X5), a
   `red` is a proof line, and a `red` whose atom already occurs in a model row has a
   goal the fresh-atom witness cannot discharge; and because a `rup` over a bits row is
   refused at every width (D-0127). The families, by the name `--stats` reports:

     alldiff      all_different_int: the direct encoding and the pairwise clause rows
     gcc          global_cardinality: the counting rows over the order encoding
     element      array_int_element: the index's direct encoding, the result's rows
     cumulative   the capacity rows over gcc's window indicators
     holes        a declared set domain: the hole rows are ladder rows

   Eligible: int_lin_le/eq, int_le/lt/eq, int_lin_le_reif/int_le_reif (every face of
   lib/core/prop/reif_lin_le.ml is a [Linear] instance), int_times/div/abs (guarded
   linear rows and [Linear] instances), the clause family's rows (bools, width 1), and
   since M8-bits-encoding-T3 array_int_maximum/minimum: a scope with a bits variable
   posts the SELECTOR shape instead of one clause row per threshold value
   (lib/core/prop/maxmin.ml, D-0134), so nothing in it names an order literal per
   value and nothing holds it; int_ne/int_lin_ne, whose nogood over a bits scope is
   D-0130 section 7.4's two-half `pol` through the A/B pair (lib/core/prop/ne.ml); and
   int_eq_reif/int_ne_reif, whose two [Clause] pieces over a bits scope are the same
   two halves with the reifier as one more term (lib/core/prop/reif_lin_eq.ml, D-0134
   section 8) and whose other faces are [Linear] instances; and bool2int, posted over a
   bits integer as its two rows with a [Linear] each ([Bool2int_row], D-0134 section 9)
   rather than as lib/core/prop/bool2int.ml's [Clause]-justified instance.
   Computed from the model BEFORE any declaration, which is the only moment the scope
   is known and the encoding is empty. *)
let held_families (m : Model.t) : (int, string list) Hashtbl.t =
  let held = Hashtbl.create 64 in
  let hold family (ops : Model.operand list) =
    List.iter
      (function
        | Model.Var i ->
            let fs = Option.value (Hashtbl.find_opt held i) ~default:[] in
            if not (List.mem family fs) then Hashtbl.replace held i (family :: fs)
        | Model.Const _ -> ())
      ops
  in
  Array.iteri
    (fun i (v : Model.var) ->
      match v.Model.v_dom with
      | Model.Dset (_ :: _) when holes_of_domain v <> [] -> hold "holes" [ Model.Var i ]
      | _ -> ())
    m.Model.vars;
  List.iter
    (fun (c : Model.constr) ->
      match c.Model.k with
      | Model.All_different ops -> hold "alldiff" ops
      | Model.Global_cardinality (xs, _, counts) -> hold "gcc" (xs @ counts)
      | Model.Cumulative (ss, _, _, _) -> hold "cumulative" ss
      | Model.Array_int_element (idx, _, res) -> hold "element" [ idx; res ]
      | Model.Regular r -> hold "regular" r.Model.r_xs (* M7-T28: rows over x's ladder *)
      | Model.Inverse iv ->
          (* M7-T28 (D-0151): the channel rows are over both arrays' ladders *)
          hold "inverse" (iv.Model.inv_f @ iv.Model.inv_g)
      | Model.Member mb ->
          (* M7-T28 (D-0159, D-0170): every line is a [Clause] over the ladders of x
             and y, and so are the threshold lemmas written ahead of some *)
          hold "member" (mb.Model.mem_y :: mb.Model.mem_x)
      | Model.Int_lin_le _ | Model.Int_lin_eq _ | Model.Int_le _ | Model.Int_lt _
      | Model.Int_eq _ | Model.Bool_clause _ | Model.Array_bool_or _
      | Model.Array_bool_and _ | Model.Bool_eq _ | Model.Bool_not _
      | Model.Int_lin_le_reif _ | Model.Int_le_reif _ | Model.Int_times _
      | Model.Int_div _ | Model.Int_abs _ | Model.Array_int_maximum _
      | Model.Array_int_minimum _ | Model.Int_lin_ne _ | Model.Int_ne _
      | Model.Int_eq_reif _ | Model.Int_ne_reif _ | Model.Bool2int _ ->
          ())
    m.Model.constraints;
  held

(* A guard definition is a reification, so it packs like one -- without [~row:], for
   the reason [pack_reif_as] gives. It reports the arithmetic builtin and not
   `int_lin_le_reif`, because the model contains no reification: a reader sent looking
   for one would not find it. *)
let pack_times_guard (p : Reif_lin_le.t) : pending =
  pack_reif_as (module Arith.Times_guard : Propagator.S with type t = Reif_lin_le.t) p

let pack_div_guard (p : Reif_lin_le.t) : pending =
  pack_reif_as (module Arith.Div_guard : Propagator.S with type t = Reif_lin_le.t) p

let pack_abs_guard (p : Reif_lin_le.t) : pending =
  pack_reif_as (module Arith.Abs_guard : Propagator.S with type t = Reif_lin_le.t) p

(* M14-e2e-verification-T3 (D-0187). The cake constraint tools/e2e/fzn2scp.py writes for
   a FlatZinc constraint, over the variables' FlatZinc names: the second half of what
   [Baguette_proof.E2e] needs to derive this constraint's rows from cake_pb_cp's .opb. The
   builder keeps a linear row's variable terms as written and folds its constants into the
   right-hand side, which is what cake does with the translator's constants in place
   (mk_lin_constraint_ge), so the terms go across unchanged. A builtin outside the covered
   families is refused here, before any row is posted. Only called under `--e2e`.

   T3b (D-0188): T5's globals. [c_id] tells `int_max(x, y, z)` (cake's `max`) from
   `array_int_maximum(z, [x, y])` (cake's `array_max`), which build the same [cstr]; the
   int_eq tying a gcc copy has [c_id = ""] and no .scp counterpart (D-0188 section 3.3). *)
let e2e_spec (names : string array) (con : Model.constr) : Baguette_proof.E2e.spec =
  let module E = Baguette_proof.E2e in
  let op = function Model.Var i -> E.Var names.(i) | Model.Const n -> E.Const n in
  let lin ts = List.map (fun (a, i) -> (a, E.Var names.(i))) ts in
  match con.Model.k with
  | Model.Int_eq (Model.Var i, Model.Var j) when con.Model.c_id = "" ->
      E.Copy (names.(i), names.(j))
  | _ when con.Model.c_id = "" -> E.refuse "a constraint no FlatZinc item states"
  | Model.Int_lin_le (ts, r) -> E.Lin_le (lin ts, r)
  | Model.Int_lin_eq (ts, r) -> E.Lin_eq (lin ts, r)
  | Model.Int_lin_ne (ts, r) -> E.Lin_ne (lin ts, r)
  | Model.Int_le (a, b) -> E.Le (op a, op b)
  | Model.Int_lt (a, b) -> E.Lt (op a, op b)
  | Model.Int_eq (a, b) -> E.Eq (op a, op b)
  | Model.Int_ne (a, b) -> E.Ne (op a, op b)
  | Model.All_different xs -> E.All_different (List.map op xs)
  (* T4: a Boolean b is cake's 0..1 integer, `b` true is the tuple (b = 1) *)
  | Model.Bool_clause (ps, ns) ->
      E.Or
        ( List.map (fun p -> (op p, 1)) ps @ List.map (fun n -> (op n, 0)) ns,
          (E.Const 1, 1) )
  | Model.Array_bool_or (xs, r) -> E.Or (List.map (fun x -> (op x, 1)) xs, (op r, 1))
  | Model.Array_bool_and (xs, r) -> E.And (List.map (fun x -> (op x, 1)) xs, (op r, 1))
  | Model.Bool2int (b, x) -> E.Eq (op b, op x)
  | Model.Bool_eq (a, b) -> E.Eq (op a, op b)
  | Model.Bool_not (a, b) -> E.Ne (op a, op b)
  | Model.Int_lin_le_reif (ts, r, b) -> E.Lin_le_iff ((op b, 1), lin ts, r)
  | Model.Int_le_reif (a, b, r) -> E.Le_iff ((op r, 1), op a, op b)
  | Model.Int_eq_reif (a, b, r) -> E.Eq_iff ((op r, 1), op a, op b)
  | Model.Int_ne_reif (a, b, r) -> E.Ne_iff ((op r, 1), op a, op b)
  (* T6 (D-0195): int_times and int_div stay outside the chain (section 2.4) *)
  | Model.Int_times _ -> E.refuse "int_times is not covered by --e2e"
  | Model.Int_div _ -> E.refuse "int_div is not covered by --e2e"
  | Model.Int_abs (x, z, _) -> E.Abs (op x, op z)
  | Model.Cumulative (ss, d, r, cap) ->
      E.Cumulative (List.map op ss, Array.to_list d, Array.to_list r, cap)
  | Model.Regular r ->
      E.regular_spec ~letters:(List.map op r.Model.r_xs) ~nq:r.Model.r_nq
        ~smin:r.Model.r_smin ~delta:r.Model.r_delta ~q0:r.Model.r_q0
        ~finals:(Array.to_list r.Model.r_final)
  (* T5 (T3b): the translator's (tools/e2e/fzn2scp.py) keyword for each *)
  | Model.Array_int_element (i, vs, z) -> E.Element (Array.to_list vs, op i, op z)
  | Model.Global_cardinality (xs, cover, counts) ->
      E.Gcc (List.map op xs, Array.to_list cover, List.map op counts)
  | Model.Array_int_maximum (m, [ x; y ]) when con.Model.c_id = "int_max" ->
      E.Max (op x, op y, op m)
  | Model.Array_int_minimum (m, [ x; y ]) when con.Model.c_id = "int_min" ->
      E.Min (op x, op y, op m)
  | Model.Array_int_maximum (m, xs) -> E.Array_max (List.map op xs, op m)
  | Model.Array_int_minimum (m, xs) -> E.Array_min (List.map op xs, op m)
  | Model.Inverse iv ->
      E.Inverse
        ( List.map op iv.Model.inv_f,
          iv.Model.inv_fmin,
          List.map op iv.Model.inv_g,
          iv.Model.inv_gmin )
  | Model.Member mb ->
      E.Member
        ( List.combine (List.map op mb.Model.mem_b) (List.map op mb.Model.mem_x),
          op mb.Model.mem_y )

let compile (m : Model.t) : t =
  (* M5-T1. Resolved to a model variable index and a direction, or refused. The
     ENCODING half of it happens further down, once the variable is declared: an
     objective line is the order encoding of that variable and cannot be written before
     it exists. *)
  let objective_var =
    match m.Model.objective with
    | Model.Satisfy -> None
    | Model.Minimize (Model.Var i) -> Some (i, Baguette_core.Search.Minimise)
    | Model.Maximize (Model.Var i) -> Some (i, Baguette_core.Search.Maximise)
    | Model.Minimize (Model.Const n) ->
        reject_constant_objective (operand_pos m (Model.Const n)) "minimize" n
    | Model.Maximize (Model.Const n) ->
        reject_constant_objective (operand_pos m (Model.Const n)) "maximize" n
  in
  let search_order = order_of_model m in
  check_name_collisions m;

  (* Variables, in Model.vars order, into both the store and the encoding. Read the
     module header before touching this. *)
  let bounds = Array.map bounds_of_domain m.Model.vars in
  (* M1-T23, half one of the cap: a bound large enough to overflow when multiplied is
     refused at its declaration, where the diagnostic can name the variable. A `var
     bool` is (0, 1) and a set domain was already rejected above, so in practice this
     only ever fires on a `Drange`. *)
  Array.iteri
    (fun i (v : Model.var) ->
      let lo, hi = bounds.(i) in
      if not (Checked.bound_fits lo && Checked.bound_fits hi) then
        reject_declared_bound v lo hi)
    m.Model.vars;
  (* M1-T54: the width cap, on the user-facing path, where the diagnostic can carry a
     position. A separate pass and not a second clause in the loop above, because the
     two caps answer different questions and share nothing but their subject: one is
     about arithmetic that cannot be computed (a soundness requirement, D-0029), this
     one about a proof that cannot be stored (a cost decision, D-0028).

     It runs AFTER the arithmetic pass and the ordering is load-bearing twice over.
     First, every bound here has passed [Checked.bound_fits], so |lo|, |hi| <=
     Checked.limit = max_int / 16 and the [hi - lo] this message prints cannot itself
     overflow -- [Encoding.order_width_exceeds] makes no such assumption because it has
     no cap behind it. Second, a model that is over both limits should be told about the
     arithmetic one, which is the harder error: narrowing a 10^18-wide domain to 10 000
     would not have made it representable.

     It also runs BEFORE [Store.create] and [Encoding.create], so a refused model
     allocates neither a domain nor a ladder. That, rather than the diagnostic, is what
     distinguishes this check from `ulimit -v` and [Mem_guard], which can only kill a
     run already in progress. *)
  (* M8-bits-encoding-T2: which variables go on bits -- eligible by width
     ([Encoding.wants_bits]) and by scope ([held_families]) -- decided here, before the
     width refusal (which is the ORDER ladder's and does not apply to a bits variable)
     and before any declaration. *)
  let held = held_families m in
  let on_bits =
    Array.mapi
      (fun i (v : Model.var) ->
        let lo, hi = bounds.(i) in
        (match v.Model.v_dom with Model.Dbool -> false | _ -> true)
        && Encoding.wants_bits ~lo ~hi
        && not (Hashtbl.mem held i))
      m.Model.vars
  in
  Array.iteri
    (fun i (v : Model.var) ->
      let lo, hi = bounds.(i) in
      if (not on_bits.(i)) && Encoding.order_width_exceeds ~lo ~hi then
        reject_declared_width v lo hi)
    m.Model.vars;
  let names = Array.map (fun (v : Model.var) -> v.Model.v_name) m.Model.vars in
  (* The store gets the HULL, holes and all, and the holes are then taken out by a
     propagator rather than being baked into the declared domain (M7-T11, D-0072).

     [Domain.of_list] would put them in directly and that was the first thing tried. It
     is WRONG, and silently so: a hole that is in the store but in no propagator has no
     trail entry behind it ([Store.remover] returns [None] -- lib/core/trace.ml's header
     is explicit about this being the `var {1,3,5}` case), so nothing in the proof ever
     claims it. A conflict that only arises because of a hole -- `int_eq(x, 4)` over
     `{1,3,5}` is the smallest one -- is then justified by a [pol] over the two model
     rows that is not contradictory without the hole, and veripb rejects the refutation:
     measured, "The constraint with ID 9 is not contradicting, as specified by the hint."
     Putting the hole behind a [Ne] instance instead means every hole pruning is an
     ordinary logged pruning with an ordinary trail entry. *)
  let store =
    Store.create ~names ~domains:(Array.map (fun (lo, hi) -> Domain.make lo hi) bounds)
  in
  let encoding = Encoding.create () in
  (* The held-back accounting for `--stats`: eligible by width, held by scope. *)
  Array.iteri
    (fun i (_ : Model.var) ->
      let lo, hi = bounds.(i) in
      if Encoding.wants_bits ~lo ~hi then
        match Hashtbl.find_opt held i with
        | Some fs -> List.iter (Encoding.note_held_back encoding) (List.rev fs)
        | None -> ())
    m.Model.vars;
  (* M14-e2e-verification-T3b (D-0188 section 3.3): the prefix defines a gcc copy's ladder
     as its original's, so it is told the pairs before the copy is declared *)
  if Encoding.e2e_on encoding then
    List.iter
      (fun (c : Model.constr) ->
        match c.Model.k with
        | Model.Int_eq (Model.Var i, Model.Var j) when c.Model.c_id = "" ->
            Encoding.e2e_copy encoding ~copy:m.Model.vars.(j).Model.v_name
              ~orig:m.Model.vars.(i).Model.v_name
        | _ -> ())
      m.Model.constraints;
  (* M14-e2e-verification-T6 (D-0195): the Booleans the .scp has no counterpart for, which
     the prefix DEFINES instead of declaring: a regular state flag as cake's own flag of the
     same constraint `c<k>` (k counted as in the loop that posts the rows), an int_abs sign
     guard as x_ge_0 *)
  (if Encoding.e2e_on encoding then
     let k = ref 0 in
     List.iter
       (fun (c : Model.constr) ->
         if c.Model.c_id <> "" then incr k;
         match c.Model.k with
         | Model.Regular r ->
             let nq = r.Model.r_nq in
             List.iteri
               (fun j f ->
                 match f with
                 | Model.Var fi ->
                     Encoding.e2e_flag encoding ~var:names.(fi)
                       ~cake:
                         (Printf.sprintf "x[c%d][%d_%d][st]" !k (j / nq)
                            (Baguette_proof.E2e.regular_state ~q0:r.Model.r_q0 ~nq
                               ((j mod nq) + 1)))
                 | Model.Const _ ->
                     Baguette_proof.E2e.refuse "a regular state flag is a constant")
               r.Model.r_flags
         | Model.Int_abs (Model.Var xi, _, { Model.x_sign = Some b; _ }) ->
             Encoding.e2e_guard encoding ~var:names.(b) ~x:names.(xi) ~at:0 ~pos:true
         | _ -> ())
       m.Model.constraints);
  Array.iteri
    (fun i (v : Model.var) ->
      let lo, hi = bounds.(i) in
      match v.Model.v_dom with
      | _ when on_bits.(i) -> Encoding.declare_int_bits encoding v.Model.v_name ~lo ~hi
      | Model.Dbool -> Encoding.declare_bool encoding v.Model.v_name
      | Model.Dset (_ :: _) ->
          (* M7-T11: one clause per hole, of the mirror polarity to the ladder rung at
             the same value. [Encoding] validates that each hole is strictly interior
             and counts the clauses against M7-T8's encoding budget. *)
          Encoding.declare_int_with_holes encoding v.Model.v_name
            ~holes:(holes_of_domain v) ~lo ~hi
      | _ -> Encoding.declare_int encoding v.Model.v_name ~lo ~hi)
    m.Model.vars;

  (* M5-T1/M5-T2: the .opb `min:` line, which `conclusion BOUNDS` cannot do without.

     It is the objective variable's own order encoding and nothing else -- under
     SPEC 4.2, x = lo + sum_{v = lo+1}^{hi} [x >= v] -- so it is built by the same
     substitution every linear row is built by, [linear_terms_int_lin_le] over the
     single term (+/-1, obj). Writing it that way rather than by hand is the point:
     if the order encoding's shape ever changes, the objective line changes with it
     instead of silently disagreeing with the rows the search reasons over.

     MAXIMISATION IS NEGATED HERE, once, and [lib/proof/opb.ml] states the convention
     ("An objective is minimised; FlatZinc maximisation is negated by the caller").
     The consequence is that the numbers in `conclusion BOUNDS` are the negation of the
     model's objective value under `maximize`; [Search.optimise] applies the same sign
     and is the only other place that knows about it. *)
  let objective =
    Option.map
      (fun (i, dir) ->
        let name = names.(i) in
        let lo, hi = bounds.(i) in
        let coeff = match dir with Search.Minimise -> 1 | Search.Maximise -> -1 in
        (* M16-file-review-T5 (D-0193): under [Discard_rows] (`--no-proof`) the line is
           not built. Its one reader is the .opb's header ([Encoding.write_opb]), which
           that sink never writes, and its length is the objective's width: one term
           per rung, 52 million on wmsmc-int, where building it was the whole setup
           (140 G instructions of 140 G). *)
        (match !Encoding.row_sink with
        | Encoding.Discard_rows -> ()
        | Encoding.Retain_rows | Encoding.Stream_rows_to _ ->
            let terms, constant =
              Encoding.linear_terms_int_lin_le encoding [ (coeff, name) ]
            in
            Encoding.set_objective encoding (Opb.objective ~constant terms));
        Encoding.e2e_objective encoding name ~sign:coeff;
        {
          Search.o_var = Var.of_int i;
          o_name = name;
          o_dir = dir;
          o_decl_lo = lo;
          o_decl_hi = hi;
        })
      objective_var
  in

  (* Every variable is declared before any row is added: a row's order-encoding
     expansion reads the declared bounds out of the encoding, so a row posted against
     an undeclared variable raises [Encoding.Undeclared]. *)
  let name_of pos i =
    if i < 0 || i >= Model.nvars m then
      Error.failf pos "internal: constraint mentions variable index %d, out of range" i
    else names.(i)
  in
  let opb_terms pos terms = List.map (fun (c, i) -> (c, name_of pos i)) terms in
  let prop_terms terms = List.map (fun (c, i) -> (c, Var.of_int i)) terms in

  (* M1-T23, half two of the cap. Called by every [post_*] below, on the *normalised*
     term list -- the same list the row and the propagator are built from, so the
     magnitude measured is the magnitude of what is actually posted. Merging duplicate
     variables can only shrink it (|a + b| <= |a| + |b|), so checking after
     normalisation is the tighter of the two places and never accepts a row the
     unnormalised check would have refused for the row that is really emitted.

     An equality posts a second row over the negated terms; its magnitude is identical
     term by term, so one check covers both. A disequality's A/B pair is bigger than
     its own row by the big-M coefficient, and that is exactly what the factor of 16
     in [Checked.limit] is sized for (lib/core/checked.ml, path 4). *)
  let term_bounds pos nterms =
    List.map
      (fun (c, i) ->
        if i < 0 || i >= Model.nvars m then
          Error.failf pos "internal: constraint mentions variable index %d, out of range"
            i
        else
          let lo, hi = bounds.(i) in
          (c, lo, hi))
      nterms
  in
  let check_row pos ~what nterms rhs =
    let tb = term_bounds pos nterms in
    if not (Checked.row_fits tb rhs) then
      reject_row pos ~what ~magnitude:(Checked.row_magnitude tb rhs)
  in

  (* M8-bits-encoding-T2: does this row carry a term on the bits encoding? Decides
     [pack_linear]'s [~mixed]. *)
  let mixed nterms =
    Encoding.n_bits_vars encoding > 0 && List.exists (fun (_, i) -> on_bits.(i)) nterms
  in
  (* ...and the same answer as [pack_linear]'s [~mixed] wants it (D-0153). *)
  let row_bits nterms = if mixed nterms then Some (Encoding.bits_n encoding) else None in
  (* One row + one instance. [nterms] is the *same* normalised list on both sides. *)
  let post_le_as ~pack ~what pos nterms rhs =
    check_row pos ~what nterms rhs;
    let row_id = Encoding.add_int_lin_le encoding (opb_terms pos nterms) rhs in
    [ pack ~mixed:(row_bits nterms) (Linear.make ~row_id store (prop_terms nterms) rhs) ]
  in
  let post_le pos nterms rhs =
    post_le_as ~pack:pack_linear ~what:"this linear inequality" pos nterms rhs
  in
  (* Two rows + two instances (D-0011). The `>=` half is the negated row; [Lin_eq.make]
     builds its [Linear.t] from the same negation, so each instance's terms are exactly
     the row it cites. *)
  let post_eq pos nterms rhs =
    check_row pos ~what:"this linear equality" nterms rhs;
    let le_id = Encoding.add_int_lin_le encoding (opb_terms pos nterms) rhs in
    let ge_id =
      Encoding.add_int_lin_le encoding (opb_terms pos (negate_terms nterms)) (-rhs)
    in
    let le, ge = Lin_eq.make ~le_id ~ge_id store (prop_terms nterms) rhs in
    let mixed = row_bits nterms in
    [ pack_linear ~mixed le; pack_linear ~mixed ge ]
  in
  (* Two rows, one instance, no row id -- see the module header. The propagator is
     built here, eagerly, rather than inside the pending closure, because [Ne.make]
     reads each variable's *declared* domain out of the store (D-0010) and must run
     before anything narrows it; only the packing is deferred. *)
  let post_ne pos nterms rhs ~pack =
    check_row pos ~what:"this disequality" nterms rhs;
    let ab = Encoding.add_int_lin_ne encoding (opb_terms pos nterms) rhs in
    (* M8-bits-encoding-T3 (D-0134 section 6): over a bits scope the pair's ids are the
       instance's, its prunings derived through them (lib/core/prop/ne.ml); otherwise
       dropped, as the module header says. *)
    let rows = if mixed nterms then Some ab else None in
    [ pack (Ne.make ?rows store (prop_terms nterms) rhs) ]
  in

  (* ---------------------------------------------------------- M4-T1, all_different

     One [Alldiff] instance over the DISTINCT variable operands, plus the pairwise
     clause rows [Encoding.add_all_different] posts for them, plus a request for the
     direct encoding of each -- which [Encoding.start_proof] honours, because that is
     the first moment a [Writer.t] exists and the Hall derivation names channelling ids
     as data (lib/core/prop/alldiff.ml's header).

     Two shapes reach here that the propagator deliberately does not handle, and each
     is decomposed rather than special-cased inside it:

     - A CONSTANT operand. `all_different([x, y, 3])` is `all_different([x, y])` plus
       `x <> 3` and `y <> 3`, and the disequalities go through the ordinary [post_ne]
       path so they get the rows and the propagator M1 already has for them. Nothing
       in the .opb or in [Alldiff] then has to know that a value can be occupied by
       something with no encoding of its own.
     - A REPEATED variable. `all_different([x, y, x])` is unsatisfiable outright, and
       [post_ne] over the normalised `x - x <> 0` is exactly the ground contradiction
       that file's own header documents (`ne_self_unsat`). Passing the repeat through
       to [Alldiff] instead would give it two snapshots with one name, and the Hall
       set's "is this variable in the set" test is by name.

     Two equal constants take the same route as a repeated variable, through the same
     empty term list. *)
  let post_all_different pos (xs : Model.operand list) =
    let ne_pair a b =
      post_ne pos
        (normalise_terms (fst (difference_terms a b ~offset:0)))
        (snd (difference_terms a b ~offset:0))
        ~pack:pack_ne
    in
    let rec decompose seen = function
      | [] -> []
      | op :: rest ->
          (* Every pair involving [op] that [Alldiff] will not cover: a pair with a
             constant either way, and a pair of two occurrences of the same variable. *)
          let here =
            List.concat_map
              (fun other ->
                match (op, other) with
                | Model.Var i, Model.Var j when i <> j -> []
                | _ -> ne_pair op other)
              rest
          in
          here @ decompose (op :: seen) rest
    in
    let vars_in_scope =
      List.sort_uniq compare
        (List.filter_map (function Model.Var i -> Some i | Model.Const _ -> None) xs)
    in
    let global =
      if List.length vars_in_scope < 2 then []
      else
        let names = List.map (name_of pos) vars_in_scope in
        List.iter (Encoding.request_direct encoding) names;
        let rows = Encoding.add_all_different encoding names in
        let p = Alldiff.make store encoding ~rows (List.map Var.of_int vars_in_scope) in
        [
          (fun id ->
            Propagator.pack ~id (module Alldiff : Propagator.S with type t = Alldiff.t) p);
        ]
    in
    decompose [] xs @ global
  in
  (* ------------------------------------------------------------------------ M7-T16

     `fzn_global_cardinality(xs, cover, counts)`: the COUNTING ROWS
     lib/core/prop/gcc.ml's derivations are built over, and the propagator instance.

     THE ROWS ARE OVER THE ORDER ENCODING, and that is forced rather than chosen. A
     tally is naturally a sum over the DIRECT encoding, but the direct encoding does not
     exist when the .opb is written -- [Encoding.start_proof] introduces it later, with
     `red` (PROOF-FORMAT section 3) -- so a model row naming `x_eq_v` would name
     variables the model file has never heard of. The identity
     `[x = v] = x_ge_v - x_ge_(v+1)` makes the same tally linear in literals the .opb
     already has, and gcc.ml's header says what that buys: no direct encoding is
     requested for this constraint at all, which is the width-proportional cost
     all_different pays and this does not.

     WHAT IS FOLDED AND WHAT IS A TERM. An x that is FIXED -- a constant operand, or a
     variable declared on a single value -- has no order literal at its own value, so it
     is not a term of any row and not a variable of the propagator; it is counted once,
     into that value's [const_v], which both the row's right-hand side and every count
     in gcc.ml subtract and add back respectively. Likewise a variable whose declared
     domain STARTS at v contributes the constant 1 rather than a literal, which is
     [ones].

     TWO REFUSALS, both of them here rather than in the propagator, because this is
     where a source position is in hand:

       - a cover and a counts array of different lengths;
       - (M7-T16 refused a CONSTANT count here as well. M7-T18 lifted that: a constant
         is the count view [View.const k], whose row is the one-value variable's row
         with an empty ladder, and it is no longer refused);
       - the same variable twice in [xs]. Its tally contribution would be 2 and every
         cancellation in gcc.ml assumes 1. all_different can let a repeat through
         because its pairwise decomposition refutes it; there is no such decomposition
         here, so it is refused rather than mis-counted. SINCE M7-T29 (D-0146) THIS IS A
         GUARD, NOT A PATH: [Builder.split_gcc_repeats] replaces every repeat by a copy
         tied with `int_eq` in the model itself, so a parsed model never reaches it; a
         [Model.t] built by other means still meets the refusal rather than a miscount. *)
  let post_global_cardinality pos (xs : Model.operand list) (cover : int array)
      (counts : Model.operand list) =
    if Array.length cover <> List.length counts then
      Error.failf pos
        "builtin `fzn_global_cardinality`: the cover has %d values but there are %d \
         counts; they must match position for position"
        (Array.length cover) (List.length counts);
    let decl i =
      let d = Store.get store (Var.of_int i) in
      (Domain.lo d, Domain.hi d)
    in
    let fixed_value = function
      | Model.Const n -> Some n
      | Model.Var i ->
          let lo, hi = decl i in
          if lo = hi then Some lo else None
    in
    let movable =
      List.filter_map
        (fun op ->
          match op with
          | Model.Var i when Option.is_none (fixed_value op) -> Some i
          | _ -> None)
        xs
    in
    if List.length (List.sort_uniq compare movable) <> List.length movable then
      Error.failf pos
        "builtin `fzn_global_cardinality`: the same variable appears more than once in \
         the array. Its contribution to a tally would be more than one, which every \
         cancellation in lib/core/prop/gcc.ml assumes it is not";
    let consts = List.filter_map fixed_value xs in
    let cover_rows =
      List.mapi
        (fun j cnt ->
          let v = cover.(j) in
          (* M7-T18: a CONSTANT count is the count VIEW [View.const k] (D-0058), and its
             row is the one-value variable's row: [cdlo = cdhi = k], so the ladder term
             below is empty and [k] sits on the degree side. See gcc.ml's header,
             "Constant counts". *)
          let cview, cname, (cdlo, cdhi) =
            match cnt with
            | Model.Var i -> (View.of_var (Var.of_int i), name_of pos i, decl i)
            | Model.Const k -> (View.const k, "", (k, k))
          in
          let dv =
            List.filter
              (fun i ->
                let lo, hi = decl i in
                lo <= v && v <= hi)
              movable
          in
          let const_v = List.length (List.filter (fun n -> n = v) consts) in
          let ones = List.length (List.filter (fun i -> fst (decl i) = v) dv) in
          let terms =
            List.concat_map
              (fun i ->
                let nm = name_of pos i in
                let lo, hi = decl i in
                (if v > lo then [ (1, Lit.ge nm v) ] else [])
                @ if v + 1 <= hi then [ (-1, Lit.ge nm (v + 1)) ] else [])
              dv
            @ List.init (max 0 (cdhi - cdlo)) (fun k -> (-1, Lit.ge cname (cdlo + 1 + k)))
          in
          let ge_cid, le_cid =
            Encoding.add_equality encoding terms (cdlo - ones - const_v)
          in
          (v, cview, const_v, ge_cid, le_cid))
        counts
    in
    (* NO [request_direct] CALL (M7-T17, D-0082).

       Nothing in lib/core/prop/gcc.ml names a direct literal -- the whole point of the
       order-encoded counting rows above is that it does not have to (D-0078). M7-T16
       requested the direct encoding here anyway, purely to arm lib/core/trace.ml's
       [derive_ahead], which then triggered on [Encoding.has_direct] of the pruned
       variable; without it gcc's trace lines went out as bare `rup` and 3.0.2 refused
       them. That cost the scope's width-proportional `red` lines (+13% on
       `2008_debruijn_binary`). The trigger is now [Store.entry]'s [ahead], set by
       gcc.ml's rule A at its own pruning call through [Store.deriving_ahead], so the
       encoding nothing read is gone with the call. *)
    let p = Gcc.make store encoding ~cover:cover_rows (List.map Var.of_int movable) in
    [ (fun id -> Propagator.pack ~id (module Gcc : Propagator.S with type t = Gcc.t) p) ]
  in
  (* ======================================================================== M7-T28

     `baguette_regular(x, Q, smin, d, q0, F, s)` (D-0146 section 3; the one block this
     row adds to this file, with its dispatch and bits-hold arms below). The rows are
     lib/core/prop/regular.ml's header, posted in this order:

       ALO_i, AMO_i   for every layer i = 0..n (the flags' exactly-one)
       START, ACCEPT
       FWD(i, q, R)   per layer i < n, state q, symbol run R of x_i's declared hull

     and the backward chains B(i, q', R) go to [Encoding.add_root_lemma], which derives
     them as `rup` when the proof starts -- derived, not posted, so a wrong one is a
     refused line and not a stronger model (D-0146 section 3.2).

     A SYMBOL RUN is a maximal stretch of consecutive values of the hull whose columns of
     the table are identical. Every argument the proof makes about a value holds for its
     whole run, so one row per run is exact, and a hull wider than the alphabet costs at
     most two all-fail runs rather than a row per value.

     Refused with a position: a table that is not Q rows, a transition outside 0..Q, a
     start or an accepting state outside 1..Q, and flags that are not (n + 1) * Q
     Booleans declared on 0..1 (the library introduces them; a hand-written .fzn that
     gets them wrong is told so). A letter that is a constant is a [Regular.Fixed]: no
     literal, one run. *)
  let post_regular pos (r : Model.regular) =
    let builtin = "baguette_regular" in
    let nq = r.Model.r_nq in
    let xs = Array.of_list r.Model.r_xs and flags = Array.of_list r.Model.r_flags in
    let n = Array.length xs in
    let decl i =
      let d = Store.get store (Var.of_int i) in
      (Domain.lo d, Domain.hi d)
    in
    if nq < 1 then
      Error.failf pos "builtin `%s`: Q is %d; an automaton needs a state" builtin nq;
    if Array.length r.Model.r_delta mod nq <> 0 then
      Error.failf pos "builtin `%s`: the transition table has %d entries, not Q = %d rows"
        builtin
        (Array.length r.Model.r_delta)
        nq;
    Array.iter
      (fun t ->
        if t < 0 || t > nq then
          Error.failf pos "builtin `%s`: a transition goes to %d, outside 0..%d" builtin t
            nq)
      r.Model.r_delta;
    if r.Model.r_q0 < 1 || r.Model.r_q0 > nq then
      Error.failf pos "builtin `%s`: the start state %d is outside 1..%d" builtin
        r.Model.r_q0 nq;
    Array.iter
      (fun f ->
        if f < 1 || f > nq then
          Error.failf pos "builtin `%s`: the accepting state %d is outside 1..%d" builtin
            f nq)
      r.Model.r_final;
    if Array.length flags <> (n + 1) * nq then
      Error.failf pos
        "builtin `%s`: %d state flags for %d letters and Q = %d; there must be %d" builtin
        (Array.length flags) n nq
        ((n + 1) * nq);
    let fvars =
      Array.map
        (function
          | Model.Var i when decl i = (0, 1) -> Var.of_int i
          | _ ->
              Error.failf pos
                "builtin `%s`: a state flag is not a Boolean variable declared on 0..1"
                builtin)
        flags
    in
    let flit i q = Lit.ge (Store.name store fvars.((i * nq) + q - 1)) 1 in
    let cells =
      Array.map
        (function
          | Model.Const c -> Regular.Fixed c
          | Model.Var i ->
              let dlo, dhi = decl i in
              Regular.Letter { var = Var.of_int i; name = name_of pos i; dlo; dhi })
        xs
    in
    let w = Array.length r.Model.r_delta / nq in
    let step q v =
      let k = v - r.Model.r_smin in
      if k < 0 || k >= w then 0 else r.Model.r_delta.(((q - 1) * w) + k)
    in
    let states = List.init nq (fun k -> k + 1) in
    let runs i =
      let lo, hi =
        match cells.(i) with
        | Regular.Fixed c -> (c, c)
        | Regular.Letter { dlo; dhi; _ } -> (dlo, dhi)
      in
      let same u v = List.for_all (fun q -> step q u = step q v) states in
      let rec go a v acc =
        if v > hi then List.rev ((a, hi) :: acc)
        else if same a v then go a (v + 1) acc
        else go v (v + 1) ((a, v - 1) :: acc)
      in
      go lo (lo + 1) []
    in
    let notin i (a, b) =
      match cells.(i) with
      | Regular.Fixed _ -> []
      | Regular.Letter { name; dlo; dhi; _ } ->
          (if a > dlo then [ Lit.negate (Lit.ge name a) ] else [])
          @ if b < dhi then [ Lit.ge name (b + 1) ] else []
    in
    let add c = ignore (Encoding.add_constraint encoding c : int) in
    for i = 0 to n do
      add (Opb.ge (List.map (fun q -> (1, flit i q)) states) 1);
      add (Opb.ge (List.map (fun q -> (1, Lit.negate (flit i q))) states) (nq - 1))
    done;
    add (Opb.clause [ flit 0 r.Model.r_q0 ]);
    add
      (Opb.ge
         (List.map
            (fun f -> (1, flit n f))
            (List.sort_uniq compare (Array.to_list r.Model.r_final)))
         1);
    for i = 0 to n - 1 do
      let rs = runs i in
      List.iter
        (fun q ->
          List.iter
            (fun (a, b) ->
              let t = step q a in
              add
                (Opb.clause
                   ((Lit.negate (flit i q) :: notin i (a, b))
                   @ if t > 0 then [ flit (i + 1) t ] else [])))
            rs)
        states;
      List.iter
        (fun q' ->
          List.iter
            (fun (a, b) ->
              let preds = List.filter (fun q -> step q a = q') states in
              Encoding.add_root_lemma encoding
                (Opb.clause
                   ((Lit.negate (flit (i + 1) q') :: notin i (a, b))
                   @ List.map (fun q -> flit i q) preds)))
            rs)
        states
    done;
    let letters =
      Array.to_list
        (Array.map (function Model.Var i -> Some i | Model.Const _ -> None) xs)
      |> List.filter_map Fun.id
    in
    let aliased = List.length (List.sort_uniq compare letters) <> List.length letters in
    let p =
      Regular.make store ~xs:cells ~nq ~smin:r.Model.r_smin ~delta:r.Model.r_delta
        ~q0:r.Model.r_q0
        ~final:(Array.to_list r.Model.r_final)
        ~flags:fvars
    in
    if aliased then
      [
        (fun id ->
          Propagator.pack ~id
            (module Regular.Aliased : Propagator.S with type t = Regular.t)
            p);
      ]
    else
      [
        (fun id ->
          Propagator.pack ~idempotent:true ~id
            (module Regular : Propagator.S with type t = Regular.t)
            p);
      ]
  in
  (* ------------------------------------------------------------------------ M7-T28

     `baguette_inverse(f, fmin, g, gmin)` (D-0146 section 7, D-0151 section 2): the
     CHANNEL rows lib/core/prop/inverse.ml's header states, over the order literals of
     both arrays, and the propagator. A constant in either array is a [Inverse.Fixed]:
     every literal about it is folded here to true (the row is not written) or false (it
     is dropped from the row), so a constant that contradicts the relation leaves an
     empty row, which is the false row -- the right answer. *)
  let post_inverse pos (iv : Model.inverse) =
    let cell = function
      | Model.Const c -> Inverse.Fixed c
      | Model.Var i ->
          let d = Store.get store (Var.of_int i) in
          Inverse.Cell
            {
              var = Var.of_int i;
              name = name_of pos i;
              dlo = Domain.lo d;
              dhi = Domain.hi d;
            }
    in
    let f = Array.of_list (List.map cell iv.Model.inv_f)
    and g = Array.of_list (List.map cell iv.Model.inv_g) in
    let fmin = iv.Model.inv_fmin and gmin = iv.Model.inv_gmin in
    let nf = Array.length f and ng = Array.length g in
    (* A disjunct: the constant true (the row holds), the constant false (dropped), or
       literals. *)
    let ne c v =
      match c with
      | Inverse.Fixed k -> if k = v then `F else `T
      | Inverse.Cell { name; dlo; dhi; _ } ->
          if v < dlo || v > dhi then `T
          else if dlo = dhi then `F
          else `L (Encoding.ne_clause_lits ~name ~decl_lo:dlo ~decl_hi:dhi v)
    and ge c v =
      match c with
      | Inverse.Fixed k -> if k >= v then `T else `F
      | Inverse.Cell { name; dlo; dhi; _ } ->
          if v <= dlo then `T else if v > dhi then `F else `L [ Lit.ge name v ]
    and le c v =
      match c with
      | Inverse.Fixed k -> if k <= v then `T else `F
      | Inverse.Cell { name; dlo; dhi; _ } ->
          if v >= dhi then `T
          else if v < dlo then `F
          else `L [ Lit.negate (Lit.ge name (v + 1)) ]
    in
    let row parts =
      if not (List.mem `T parts) then
        let lits = List.concat_map (function `L l -> l | `T | `F -> []) parts in
        ignore (Encoding.add_constraint encoding (Opb.clause lits) : int)
    in
    let gmax = gmin + ng - 1 and fmax = fmin + nf - 1 in
    Array.iter
      (fun c ->
        row [ ge c gmin ];
        row [ le c gmax ])
      f;
    Array.iter
      (fun c ->
        row [ ge c fmin ];
        row [ le c fmax ])
      g;
    Array.iteri
      (fun kf cf ->
        let i = fmin + kf in
        Array.iteri
          (fun kg cg ->
            let j = gmin + kg in
            (* CH(i, j): f_i = j -> g_j = i; CH'(j, i): g_j = i -> f_i = j *)
            row [ ne cf j; ge cg i ];
            row [ ne cf j; le cg i ];
            row [ ne cg i; ge cf j ];
            row [ ne cg i; le cf j ])
          g)
      f;
    let p = Inverse.make ~f ~fmin ~g ~gmin in
    (* Idempotent only when no variable occurs twice across the two arrays: an aliased
       variable is two cells one removal changes at once, and the second pass can then
       owe the first one more (the header's I-P2 argument is per cell). *)
    let ops =
      List.filter_map
        (function Model.Var i -> Some i | Model.Const _ -> None)
        (iv.Model.inv_f @ iv.Model.inv_g)
    in
    let idempotent = List.length (List.sort_uniq compare ops) = List.length ops in
    (* STAGE 2 (D-0146 section 7.3, D-0151 section 2): both arrays are permutations, so
       all_different over each is IMPLIED, and lib/core/prop/alldiff.ml over it brings the
       matching's pruning the channel cannot see (a pigeonhole). Its derivations cite the
       pairwise rows `x <> v \/ z <> v`, which this .opb does not state: they are ROOT
       LEMMAS, each `rup` from the two channel rows CH(i, v) and CH(k, v) (or from the
       restriction rows, for a v outside the other index set), registered with
       [Encoding.add_cited_lemma] and handed to alldiff through its lemma-row hook. One
       instance per array over its variables, when they are pairwise distinct (a repeat
       is the involution's or a unification's, and Alldiff's Hall test is by name), and
       when the model does not already post all_different over the same set (its model
       rows would make this one a duplicate). A constant in the array is left to the
       channel. *)
    let stage2 (arr : Model.operand list) =
      let is =
        List.filter_map (function Model.Var i -> Some i | Model.Const _ -> None) arr
      in
      let set = List.sort_uniq compare is in
      let posted =
        List.exists
          (fun (c : Model.constr) ->
            match c.Model.k with
            | Model.All_different xs ->
                List.sort_uniq compare
                  (List.filter_map
                     (function Model.Var i -> Some i | Model.Const _ -> None)
                     xs)
                = set
            | _ -> false)
          m.Model.constraints
      in
      if List.length set < 2 || List.length set <> List.length is || posted then []
      else
        let names = List.map (name_of pos) is in
        List.iter (Encoding.request_direct encoding) names;
        let decl i =
          let d = Store.get store (Var.of_int i) in
          (Domain.lo d, Domain.hi d)
        in
        let rec pairs = function
          | [] -> []
          | x :: rest -> List.map (fun z -> (x, z)) rest @ pairs rest
        in
        let lemma_rows =
          List.concat_map
            (fun (x, z) ->
              let (xlo, xhi), (zlo, zhi) = (decl x, decl z) in
              let nx = name_of pos x and nz = name_of pos z in
              List.init
                (max 0 (min xhi zhi - max xlo zlo + 1))
                (fun k ->
                  let v = max xlo zlo + k in
                  let c =
                    Opb.clause
                      (Encoding.ne_clause_lits ~name:nx ~decl_lo:xlo ~decl_hi:xhi v
                      @ Encoding.ne_clause_lits ~name:nz ~decl_lo:zlo ~decl_hi:zhi v)
                  in
                  ((nx, nz, v), Encoding.add_cited_lemma encoding c)))
            (pairs is)
        in
        let a =
          Alldiff.make ~lemma_rows store encoding ~rows:[] (List.map Var.of_int is)
        in
        [
          (fun id ->
            Propagator.pack ~id (module Alldiff : Propagator.S with type t = Alldiff.t) a);
        ]
    in
    (fun id ->
      Propagator.pack ~idempotent ~id
        (module Inverse : Propagator.S with type t = Inverse.t)
        p)
    :: (stage2 iv.Model.inv_f @ stage2 iv.Model.inv_g)
  in
  (* ------------------------------------------------------------------------ M7-T28

     `baguette_member(x, y, b)` (D-0151 section 3, D-0159, D-0170): the rows
     lib/core/prop/member.ml's header states, in this order -- OR over the selectors, then
     per position k, [a, b] the overlap of the two DECLARED hulls (M7-T34):

       ~b_k \/ [x_k >= a]   ~b_k \/ ~[x_k >= b+1]   ~b_k \/ [y >= a]   ~b_k \/ ~[y >= b+1]
       F_k   sum_{v=a+1..b} ([x_k >= v] + ~[y >= v]) + (b - a) ~b_k >= b - a
       G_k   the same with x_k and y swapped

     a constant literal folded (a clause it makes true not written), a big-M row only when
     b > a, and the single row `~b_k` when the hulls are disjoint. At most six rows per
     position whatever the width; the threshold clauses D-0159 posted here, two per value
     of the overlap, are now lemmas member.ml writes into the proof where a line needs
     one. A position whose x_k IS y has no rows: b_k is free.

     Refused with a position: a selector count other than one per position, and a
     selector that is not a Boolean variable declared on 0..1, distinct from the others
     and from x and y (the library introduces them; a hand-written .fzn that gets them
     wrong is told so). *)
  let post_member pos (mb : Model.member) =
    let builtin = "baguette_member" in
    let decl i =
      let d = Store.get store (Var.of_int i) in
      (Domain.lo d, Domain.hi d)
    in
    let xs = Array.of_list mb.Model.mem_x and bs = Array.of_list mb.Model.mem_b in
    let n = Array.length xs in
    if Array.length bs <> n then
      Error.failf pos
        "builtin `%s`: %d selectors for %d positions; there must be one each" builtin
        (Array.length bs) n;
    let letters =
      List.filter_map
        (function Model.Var i -> Some i | Model.Const _ -> None)
        (mb.Model.mem_y :: mb.Model.mem_x)
    in
    let svars =
      Array.map
        (function
          | Model.Var i when decl i = (0, 1) && not (List.mem i letters) -> i
          | _ ->
              Error.failf pos
                "builtin `%s`: a selector is not a Boolean variable declared on 0..1 and \
                 distinct from x and y"
                builtin)
        bs
    in
    if List.length (List.sort_uniq compare (Array.to_list svars)) <> n then
      Error.failf pos "builtin `%s`: a selector occurs twice" builtin;
    let cell = function
      | Model.Const c -> Member.Fixed c
      | Model.Var i ->
          let dlo, dhi = decl i in
          Member.Cell { var = Var.of_int i; name = name_of pos i; dlo; dhi }
    in
    let cx = Array.map cell xs and cy = cell mb.Model.mem_y in
    let hull = function
      | Member.Fixed c -> (c, c)
      | Member.Cell { dlo; dhi; _ } -> (dlo, dhi)
    in
    let blit k = Lit.ge (name_of pos svars.(k)) 1 in
    let or_row = Encoding.add_constraint encoding (Opb.clause (List.init n blit)) in
    let same a b =
      match (a, b) with
      | Member.Cell { var = u; _ }, Member.Cell { var = w; _ } -> Var.equal u w
      | _ -> false
    in
    (* [c >= v] as the constant true, the constant false, or a literal. *)
    let ge c v =
      match c with
      | Member.Fixed k -> if k >= v then `T else `F
      | Member.Cell { name; dlo; dhi; _ } ->
          if v <= dlo then `T else if v > dhi then `F else `L (Lit.ge name v)
    in
    let not_ = function `T -> `F | `F -> `T | `L l -> `L (Lit.negate l) in
    let clause parts =
      if not (List.mem `T parts) then
        let lits = List.filter_map (function `L l -> Some l | `T | `F -> None) parts in
        ignore (Encoding.add_constraint encoding (Opb.clause lits) : int)
    in
    (* sum_{v = a+1..b} ([p >= v] + ~[q >= v]) + (b - a) ~b_k >= b - a: p - q >= 0 over
       the overlap's rungs, both being in [a, b]. Every [v] is a rung of both: a cell in
       the overlap with b > a is a variable. *)
    let big_m nb p q a b =
      if b > a then
        let rung c v = match ge c v with `L l -> l | `T | `F -> assert false in
        let terms =
          List.concat_map
            (fun v -> [ (1, rung p v); (1, Lit.negate (rung q v)) ])
            (List.init (b - a) (fun i -> a + 1 + i))
        in
        ignore
          (Encoding.add_constraint encoding (Opb.ge (terms @ [ (b - a, nb) ]) (b - a))
            : int)
    in
    Array.iteri
      (fun k c ->
        if not (same c cy) then
          let nb = Lit.negate (blit k) in
          let lx, hx = hull c and ly, hy = hull cy in
          let a = max lx ly and b = min hx hy in
          if a > b then clause [ `L nb ]
          else (
            (* x_k and y in [a, b] under b_k *)
            clause [ `L nb; ge c a ];
            clause [ `L nb; not_ (ge c (b + 1)) ];
            clause [ `L nb; ge cy a ];
            clause [ `L nb; not_ (ge cy (b + 1)) ];
            (* F_k, G_k: x_k - y >= 0 and y - x_k >= 0 over the overlap's rungs *)
            big_m nb c cy a b;
            big_m nb cy c a b))
      cx;
    let aliased = List.length (List.sort_uniq compare letters) <> List.length letters in
    let p = Member.make store ~xs:cx ~y:cy ~sels:(Array.map Var.of_int svars) ~or_row in
    if aliased then
      [
        (fun id ->
          Propagator.pack ~id
            (module Member.Aliased : Propagator.S with type t = Member.t)
            p);
      ]
    else
      [
        (fun id ->
          Propagator.pack ~idempotent:true ~id
            (module Member : Propagator.S with type t = Member.t)
            p);
      ]
  in
  (* ===================================================================== end M7-T28 *)
  (* ------------------------------------------------------------------------ M4-T9

     `array_int_maximum(m, xs)` / `array_int_minimum(m, xs)`, as lib/core/prop/maxmin.ml's
     header splits it (D-0095):

       - the CONJUNCTIVE half, one ordinary `int_lin_le` row and [Linear] instance per
         operand: `x_i - m <= 0` for a maximum, `m - x_i <= 0` for a minimum. These are
         the model rows R1/R2 are justified against, by [Linear]'s pol and nothing new;
       - the DISJUNCTIVE half, the per-value clause family [Maxmin.rows] lists, one
         `>= 1` row each over ORDER literals the .opb already has, and one [Maxmin]
         instance whose every explanation is one of those rows restated.

     Constants are views ([View.const]) on the propagator side and folded right-hand
     sides on the row side, so `int_max(x, 3, m)` needs no case of its own. Rows are
     posted in a fixed order -- linear rows in operand order, then the clauses in
     increasing threshold -- because the order they are appended is the order of the ids
     the proof cites.

     M8-bits-encoding-T3 (D-0134 sections 2.1, 2.5): when a variable of the scope is on
     the bits encoding, the disjunctive half is the SELECTOR shape instead -- one big-M
     row per operand over a fresh `$mxN` and one clause over the selectors, posted by
     [Encoding.add_choice] from [Maxmin.selector_rows] after the linear rows, and the
     ids handed back to the instance. The group's pick ([Maxmin.chosen]) reads the
     solution by FlatZinc name, which is all [Encoding] may see. A scope with no bits
     variable takes the per-value branch, byte for byte as before. *)
  let post_maxmin pos ~(dir : Maxmin.dir) (mo : Model.operand) (xs : Model.operand list) =
    let linear =
      List.concat_map
        (fun x ->
          let a, b = match dir with Maxmin.Max -> (x, mo) | Maxmin.Min -> (mo, x) in
          let terms, rhs = difference_terms a b ~offset:0 in
          post_le pos (normalise_terms terms) rhs)
        xs
    in
    let view = function
      | Model.Var i -> View.of_var (Var.of_int i)
      | Model.Const k -> View.const k
    in
    let on_bits_op = function Model.Var i -> on_bits.(i) | Model.Const _ -> false in
    let selector =
      Encoding.n_bits_vars encoding > 0 && List.exists on_bits_op (mo :: xs)
    in
    let p =
      Maxmin.make
        ~shape:(if selector then `Selector else `Per_value)
        store ~dir (view mo) (List.map view xs)
    in
    if selector then
      match Maxmin.selector_rows p with
      | [] -> () (* the disjunction holds by declaration; no rule fires *)
      | srs ->
          let rows =
            List.map
              (fun (r : Maxmin.selector_row) ->
                (r.Maxmin.sr_terms, r.Maxmin.sr_big_m, r.Maxmin.sr_rhs))
              srs
          in
          (* Every term is +-1 and M_i = dhi(m) - dlo(x_i), so each row's magnitude
             is a few declared bounds, inside [Checked.limit]'s envelope (path 1) by
             the declaration cap; [Encoding.add_int_lin_le]'s own guard backs it. *)
          let ids, clause = Encoding.add_choice encoding ~rows ~pick:(Maxmin.chosen p) in
          Maxmin.attach_selectors p ~rows:ids ~clause
    else
      List.iter
        (fun lits ->
          ignore
            (Encoding.add_constraint encoding (Opb.ge (List.map (fun l -> (1, l)) lits) 1)
              : int))
        (Maxmin.rows p);
    let pack id =
      match dir with
      | Maxmin.Max ->
          Propagator.pack ~id
            (module Maxmin.Maximum : Propagator.S with type t = Maxmin.t)
            p
      | Maxmin.Min ->
          Propagator.pack ~id
            (module Maxmin.Minimum : Propagator.S with type t = Maxmin.t)
            p
    in
    linear @ [ pack ]
  in
  (* ------------------------------------------------------------------------ M4-T10

     `baguette_cumulative(s, d, r, cap)` (D-0096). The capacity rows are built and
     posted by [Cumulative.make] itself -- one row per time point whose may-load exceeds
     the capacity, over the starts' ORDER literals, no auxiliary -- so this arm only
     maps operands and refuses negative constants with a position. *)
  let post_cumulative pos (ss : Model.operand list) (ds : int array) (rs : int array) cap
      =
    if cap < 0 then
      Error.failf pos
        "builtin `baguette_cumulative`: the capacity is %d; it must be >= 0 (mznlib \
         routes a negative or variable capacity to std's decomposition)"
        cap;
    Array.iter
      (fun d ->
        if d < 0 then
          Error.failf pos
            "builtin `baguette_cumulative`: a duration is %d; it must be >= 0" d)
      ds;
    Array.iter
      (fun r ->
        if r < 0 then
          Error.failf pos
            "builtin `baguette_cumulative`: a resource is %d; it must be >= 0" r)
      rs;
    let specs =
      List.mapi
        (fun i s ->
          ( (match s with
            | Model.Const n -> Cumulative.Fixed n
            | Model.Var v -> Cumulative.Start (Var.of_int v)),
            ds.(i),
            rs.(i) ))
        ss
    in
    let p = Cumulative.make store encoding ~cap specs in
    [
      (fun id ->
        Propagator.pack ~id
          (module Cumulative : Propagator.S with type t = Cumulative.t)
          p);
    ]
  in
  (* ------------------------------------------------------------------------ M4-T3

     `array_int_element(idx, as, c)`, with `as` a constant array and a 1-BASED index.

     THE INDEX IS A VIEW (D-0058): [View.shift (View.of_var idx) (-1)] is the 0-based
     array offset, and lib/core/prop/element.ml prunes through it straight into [idx]'s
     own domain. There is no auxiliary variable and no channelling row -- which is the
     whole of what M4-T0 bought and what the aux-variable shape would have cost, since a
     channel is a bounds-consistent step and element's [Domain] claim would not survive
     one.

     A CONSTANT INDEX is decomposed here and never reaches the propagator, so that module
     has one degenerate case instead of two: in range it is the equality `c = as[k]`,
     which the ordinary [post_eq] path posts with the rows and the propagator M1 already
     has; out of range it is the empty row `0 <= -1`, the same ground contradiction
     [post_ne] gives `x - x <> 0` (lib/core/prop/ne.ml's `ne_self_unsat`), refuted by one
     [pol] over a row the .opb really holds. A constant RESULT is not decomposed: it is a
     [View.Const], which the propagator and [Encoding.view_ge] both handle as the
     arithmetic they already are.

     ONE [request_direct] CALL, and the one that is NOT here is the measured half.

     The index's is ordinary and required: element.ml names [idx]'s [direct_lo_id],
     [direct_hi_id] and [at_least_one_id] in every derivation, and D-0058 is explicit that
     a view's `=` is the BASE's, so the request is for [idx] itself and never for the
     view.

     The RESULT gets none. It was requested here at first, on the argument that
     lib/core/trace.ml's [derive_ahead] gated on [Encoding.has_direct] of the PRUNED
     variable (it no longer does: M7-T17, D-0082) and that a result pruning would therefore need its [pol] written out ahead
     of its trace line (I-X10, D-0040). MEASURED 2026-09-21: dropping the call reddens
     NOTHING -- all six element models and a scene built specifically to need it (an
     index HOLE punched by an `int_ne`, so the result's pruning rests on something
     [Reason.t] cannot state) verify unchanged. The result's trace lines are RUP against
     this constraint's own rows with no derivation ahead of them, which is the [Ne]
     situation and the reason element is classified [Single_row] rather than
     [Needs_derivation]. So the call is gone, and with it the result's whole direct
     encoding -- width-proportional, which is exactly the cost D-0028 and D-0058 measure.
     An argument for a proof line that no proof needs is the thing this project's rules
     are about; it is recorded here rather than deleted so the next reader does not make
     it again. *)
  let post_array_int_element pos (idx : Model.operand) (values : int array)
      (res : Model.operand) =
    match idx with
    | Model.Const k ->
        if k < 1 || k > Array.length values then post_le pos [] (-1)
        else
          let terms, rhs = difference_terms res (Model.Const values.(k - 1)) ~offset:0 in
          post_eq pos (normalise_terms terms) rhs
    | Model.Var i ->
        let iname = name_of pos i in
        let index = View.shift (View.of_var (Var.of_int i)) (-1) in
        let result =
          match res with
          | Model.Const c -> View.const c
          | Model.Var j -> View.of_var (Var.of_int j)
        in
        Encoding.request_direct encoding iname;
        let rows =
          Element.post_rows encoding ~index_name:iname
            ~imap:(Option.get (View.map_of index))
            ~result:(View.to_encoding store result)
            ~values
            ~positions:(Element.declared_positions store ~pos:index)
        in
        let p = Element.make store encoding ~rows ~pos:index ~res:result ~values in
        [
          (fun id ->
            Propagator.pack ~id (module Element : Propagator.S with type t = Element.t) p);
        ]
  in

  (* ------------------------------------------------------------- M2, Booleans *)

  (* An operand a Boolean builtin requires to be Boolean. Checked *here*, not in
     lib/flatzinc/builder.ml, because this is the first place the variable declarations
     are in hand: the builder knows arity and shape, this knows types. Returned
     unchanged so a caller can write [bool_operand ... op] where it would have written
     [op] and cannot forget the check. *)
  let bool_operand pos ~builtin ~what (op : Model.operand) : Model.operand =
    (match op with
    | Model.Const n -> if n <> 0 && n <> 1 then reject_non_bool_const pos ~builtin ~what n
    | Model.Var i -> (
        if i < 0 || i >= Model.nvars m then
          Error.failf pos "internal: constraint mentions variable index %d, out of range"
            i
        else
          match (Model.var m i).Model.v_dom with
          | Model.Dbool -> ()
          | _ -> reject_non_bool_var pos ~builtin ~what (Model.var m i)));
    op
  in

  (* ------------------------------------------------------------- M3, reification

     Every reified builtin below is one call to [post_reif_le] or [post_reif_eq]. That
     is roadmap M3-T4's whole claim made concrete on this side of the boundary: the
     five propagation cases of `b <-> C` are the dispatcher's
     (lib/core/prop/reif.ml), and what is left here is posting the rows and choosing
     an author. `int_ne_reif` differs from `int_eq_reif` by ONE argument, [~positive],
     and `int_le_reif` from `int_lin_le_reif` by nothing but [difference_terms].

     The degenerate cases are not an afterthought. A FlatZinc model is entitled to say
     `int_le_reif(x, y, b)` where the declared domains already settle `x <= y`, and
     then `b <-> C` is not a reification: it is `b = 1`. [Encoding]'s reification doors
     refuse such a condition by name ([Reif_constant], M3-T1's own check, which
     [reif_rows] makes for the identical reason) rather than emit two rows one of which
     no longer mentions the reifier, so the decision is made HERE, from the same
     declared bounds, and the model keeps its meaning: a unit row fixing the reifier,
     and one [Linear] instance over it. *)

  (* The span of a normalised term list over the DECLARED domains -- the two numbers
     every big-M below is computed from. Call [check_row] first: this is where the
     products live that M1-T23's cap is sized for. *)
  let term_span nterms =
    List.fold_left
      (fun (lo, hi) (c, i) ->
        let l, u = bounds.(i) in
        if c >= 0 then (Checked.add lo (Checked.mul c l), Checked.add hi (Checked.mul c u))
        else (Checked.add lo (Checked.mul c u), Checked.add hi (Checked.mul c l)))
      (0, 0) nterms
  in
  (* The reifier as a variable index, with the two things that make it one checked
     here rather than inside [Encoding]: it is a `var bool` (D-0007), and it does not
     occur in its own condition. `b <-> C(b)` is not a definition -- [reif_rows] raises
     [Reif_in_condition] for it -- and a term list mentioning the reifier would also
     collide with the guard term the rows below append. *)
  let reifier_index pos ~builtin nterms r =
    match bool_operand pos ~builtin ~what:"the reifier" r with
    | Model.Const n -> Either.Left (n = 1)
    | Model.Var ri ->
        if List.exists (fun (_, i) -> i = ri) nterms then
          Error.failf pos
            "builtin `%s`: the reifier `%s` also occurs in the constraint it reifies, so \
             `b <-> C(b)` is not a definition"
            builtin (Model.var m ri).Model.v_name;
        Either.Right ri
  in
  (* One unit row and one [Linear] instance fixing a Boolean to [v]. The row is posted
     because `conclusion SAT` re-checks the assignment against the .opb, so the .opb has
     to be the model; the instance is posted because nothing else would establish the
     value, and it justifies itself the ordinary D-0013 way over its own row. *)
  let post_fixed_bool pos ri v =
    let nterms = if v = 1 then [ (-1, ri) ] else [ (1, ri) ] in
    let rhs = if v = 1 then -1 else 0 in
    check_row pos ~what:"this reified constant" nterms rhs;
    let row_id = Encoding.add_int_lin_le encoding (opb_terms pos nterms) rhs in
    [ pack_linear ~mixed:None (Linear.make ~row_id store (prop_terms nterms) rhs) ]
  in
  (* b <-> (sum a_i x_i <= rhs). Two rows, one instance. *)
  let post_reif_le pos ~builtin ~pack nterms rhs r =
    check_row pos ~what:"this reified linear inequality" nterms rhs;
    match reifier_index pos ~builtin nterms r with
    | Either.Left true -> post_le pos nterms rhs
    | Either.Left false ->
        post_le pos (negate_terms nterms) (Checked.sub (Checked.neg rhs) 1)
    | Either.Right ri ->
        let lo, hi = term_span nterms in
        let k_fwd = Checked.sub hi rhs and k_bwd = Checked.add (Checked.sub rhs lo) 1 in
        if k_fwd <= 0 then post_fixed_bool pos ri 1
        else if k_bwd <= 0 then post_fixed_bool pos ri 0
        else (
          (* Both augmented rows, measured before either is posted -- the guard term is
             a bool, so its contribution to the magnitude is its own coefficient. *)
          check_row pos ~what:"this reified linear inequality"
            (nterms @ [ (k_fwd, ri) ])
            (Checked.add rhs k_fwd);
          check_row pos ~what:"this reified linear inequality"
            (negate_terms nterms @ [ (Checked.neg k_bwd, ri) ])
            (Checked.sub (Checked.neg rhs) 1);
          let fwd_id, bwd_id, k_fwd, k_bwd =
            Encoding.add_int_lin_le_reif_rows encoding (opb_terms pos nterms) rhs
              ~reifier:(name_of pos ri)
          in
          [
            pack
              (Reif_lin_le.make ~fwd_id ~bwd_id ~k_fwd ~k_bwd store (prop_terms nterms)
                 rhs ~reifier:(Var.of_int ri));
          ])
  in
  (* b <-> (sum a_i x_i = rhs) when [positive], b <-> (sum <> rhs) when not. Four rows
     and one .opb-only auxiliary Boolean; one instance. *)
  let post_reif_eq pos ~builtin ~pack ~positive nterms rhs r =
    check_row pos ~what:"this reified linear equality" nterms rhs;
    match reifier_index pos ~builtin nterms r with
    | Either.Left b ->
        if b = positive then post_eq pos nterms rhs
        else post_ne pos nterms rhs ~pack:pack_lin_ne
    | Either.Right ri ->
        let lo, hi = term_span nterms in
        let k_le = Checked.sub hi rhs and k_ge = Checked.sub rhs lo in
        if k_le < 0 || k_ge < 0 then post_fixed_bool pos ri (if positive then 0 else 1)
        else if k_le = 0 && k_ge = 0 then
          post_fixed_bool pos ri (if positive then 1 else 0)
        else
          let g = Stdlib.max 1 in
          check_row pos ~what:"this reified linear equality"
            (nterms @ [ (g k_le, ri) ])
            (Checked.add rhs (g k_le));
          check_row pos ~what:"this reified linear equality"
            (negate_terms nterms @ [ (g k_ge, ri) ])
            (Checked.add (Checked.neg rhs) (g k_ge));
          let r =
            Encoding.add_int_lin_eq_reif encoding (opb_terms pos nterms) rhs
              ~reifier:(name_of pos ri) ~pos:positive
          in
          (* M8-bits-encoding-T3 (D-0134 section 8): over a bits scope A's and B's ids are
             the instance's, its disequality pieces derived through them
             (lib/core/prop/reif_lin_eq.ml); otherwise dropped, as [post_ne] drops its
             pair's. *)
          let rows =
            if mixed nterms then
              Some
                {
                  Reif_lin_eq.a_id = r.Encoding.a_id;
                  b_id = r.Encoding.b_id;
                  big_a = r.Encoding.big_a;
                  big_b = r.Encoding.big_b;
                }
            else None
          in
          [
            pack
              (Reif_lin_eq.make ?rows ~le_id:r.Encoding.le_id ~ge_id:r.Encoding.ge_id
                 ~k_le:r.Encoding.k_le ~k_ge:r.Encoding.k_ge ~positive store
                 (prop_terms nterms) rhs ~reifier:(Var.of_int ri));
          ]
  in

  (* One clause -- a list of (operand, polarity) pairs -- as one .opb row and (unless it
     is already satisfied) one propagator instance.

     The row. A clause over Boolean variables is a linear inequality over the same
     variables, so it goes through [Encoding.add_int_lin_le] like every other row rather
     than through a second, clause-shaped door:

         x_1 \/ ... \/ x_p \/ ~y_1 \/ ... \/ ~y_q
       is  sum_i x_i + sum_j (1 - y_j) >= 1
       is  -sum_i x_i + sum_j y_j <= q - 1

     and the order-encoding expansion of that, over variables declared on [0, 1], is
     literally the clause: `+1 x_1_ge_1 ... +1 ~y_1_ge_1 ... >= 1`. That is what makes
     lib/core/prop/bool_clause.ml's [rup] close in a single unit propagation, and it is
     why nothing here needs [Opb.clause]: one door into the .opb means one expansion to
     keep right.

     Constants. [k] counts the *constant* literals that are true. Each of them weakens
     the row by one, which is the same `k` appearing in the right-hand side above with
     the constant terms folded out, so the row stays an exact statement of the
     constraint rather than a stronger one.

     When k >= 1 the clause is a tautology and **no propagator is posted**. This is the
     one place the row and the instance deliberately part company, and the asymmetry is
     load-bearing rather than an optimisation: a [Bool_clause.t] over the *remaining*
     variable literals would assert that one of them is true, which the constraint does
     not say, and would prune values that are in solutions. The row is still posted,
     because `conclusion SAT` re-checks the assignment against the .opb and the .opb
     should be the model; a vacuous row costs one line and says something true.

     When k = 0 and there are no variable literals either, the row is the empty sum
     `>= 1 ;` -- false -- and the propagator is [Bool_clause.make]'s empty clause, which
     conflicts immediately with [Explanation.clause []]. That is the ground-constraint
     argument above, reached from the Boolean side; `bool_clause([], [])` is a legal
     unsatisfiable model and needs no special case. *)
  let post_clause pos ~builtin ~what ~pack (lits : (Model.operand * bool) list) =
    let k = ref 0 and vlits_rev = ref [] in
    List.iter
      (fun (op, positive) ->
        match bool_operand pos ~builtin ~what op with
        | Model.Const n -> if n = 1 = positive then incr k
        | Model.Var i -> vlits_rev := (i, positive) :: !vlits_rev)
      lits;
    let vlits = List.rev !vlits_rev in
    let q = List.length (List.filter (fun (_, positive) -> not positive) vlits) in
    let nterms =
      normalise_terms
        (List.map (fun (i, positive) -> ((if positive then -1 else 1), i)) vlits)
    in
    let rhs = !k + q - 1 in
    check_row pos ~what:"this Boolean clause" nterms rhs;
    ignore (Encoding.add_int_lin_le encoding (opb_terms pos nterms) rhs : int);
    if !k > 0 then []
    else
      [
        pack
          (Bool_clause.make store
             (List.map (fun (i, positive) -> (Var.of_int i, positive)) vlits));
      ]
  in

  (* The four clause decompositions. Each posts its clauses in a fixed order, through
     [let] bindings rather than by relying on the evaluation order of [@] or of a
     constructor's arguments, which OCaml leaves unspecified: every [post_clause] call
     appends a row to the .opb, so the order they run in is the order of the ids the
     proof cites. Getting that wrong would not fail to compile and would not fail a
     unit test -- it would shift every later id.

     One instance per clause is D-0027 point 3's default and loses nothing here: unit
     propagation over these clauses is domain consistent for the whole reified
     constraint, which a fused propagator could not improve on. *)
  let clause ~builtin ~pack pos lits =
    post_clause pos ~builtin ~what:"every argument" ~pack lits
  in

  (* r <-> (x_1 \/ ... \/ x_n):  (~r \/ x_1 \/ ... \/ x_n)  and  (r \/ ~x_i) for each i.
     An empty [xs] leaves the unit (~r), which forces r false -- the identity of the
     connective, with no empty-array case to write. *)
  let post_array_bool_or pos xs r =
    let builtin = "array_bool_or" and pack = pack_array_bool_or in
    let forward =
      clause ~builtin ~pack pos ((r, false) :: List.map (fun x -> (x, true)) xs)
    in
    let backward =
      List.concat_map (fun x -> clause ~builtin ~pack pos [ (r, true); (x, false) ]) xs
    in
    forward @ backward
  in

  (* r <-> (x_1 /\ ... /\ x_n):  (~r \/ x_i) for each i  and  (r \/ ~x_1 \/ ... \/ ~x_n).
     An empty [xs] leaves the unit (r), which forces r true. *)
  let post_array_bool_and pos xs r =
    let builtin = "array_bool_and" and pack = pack_array_bool_and in
    let forward =
      List.concat_map (fun x -> clause ~builtin ~pack pos [ (r, false); (x, true) ]) xs
    in
    let backward =
      clause ~builtin ~pack pos ((r, true) :: List.map (fun x -> (x, false)) xs)
    in
    forward @ backward
  in

  let post_bool_eq pos a b =
    let builtin = "bool_eq" and pack = pack_bool_eq in
    let fwd = clause ~builtin ~pack pos [ (a, false); (b, true) ] in
    let bwd = clause ~builtin ~pack pos [ (a, true); (b, false) ] in
    fwd @ bwd
  in

  let post_bool_not pos a b =
    let builtin = "bool_not" and pack = pack_bool_not in
    let fwd = clause ~builtin ~pack pos [ (a, true); (b, true) ] in
    let bwd = clause ~builtin ~pack pos [ (a, false); (b, false) ] in
    fwd @ bwd
  in

  (* bool2int(b, x) is x = b, so it posts the two rows an equality posts -- row LE
     `x - b <= 0` first, row GE `b - x <= 0` second, which is the order
     lib/core/prop/bool2int.ml's header names them in and the order its worked RUP
     checks assume.

     Two instances or one. When both operands are variables the instance is
     [Bool2int.t], whose reasons are O(1) clauses rather than D-0013's weaken-divide-add
     [pol]; D-0028 measured what the [pol] route costs and `bool2int` is precisely where
     a wide integer meets a Boolean, so the [Weaken] chain would be one literal per value
     of the integer's *declared* width, per pruning, for a constraint that immediately
     confines it to {0, 1}. When either side is a constant there is nothing to channel:
     the constraint is an ordinary ground equality and [post_eq] already states it
     exactly, with two [Linear] instances over a term list of length at most one. Writing
     a Boolean special case for that would be a second implementation of `x = c`. *)
  let post_bool2int pos b x =
    let b = bool_operand pos ~builtin:"bool2int" ~what:"the first argument" b in
    match (b, x) with
    | Model.Var bi, Model.Var xi when on_bits.(xi) ->
        (* M8-bits-encoding-T3 continuation: the same two rows, a [Linear] over each
           ([Bool2int_row]'s header says why). *)
        let nterms = normalise_terms [ (1, xi); (-1, bi) ] in
        check_row pos ~what:"this bool2int channelling" nterms 0;
        let le_id = Encoding.add_int_lin_le encoding (opb_terms pos nterms) 0 in
        let ge_id =
          Encoding.add_int_lin_le encoding (opb_terms pos (negate_terms nterms)) 0
        in
        let le, ge = Lin_eq.make ~le_id ~ge_id store (prop_terms nterms) 0 in
        let bits_n = Encoding.bits_n encoding in
        [ pack_bool2int_row ~bits_n le; pack_bool2int_row ~bits_n ge ]
    | Model.Var bi, Model.Var xi ->
        let nterms = normalise_terms [ (1, xi); (-1, bi) ] in
        check_row pos ~what:"this bool2int channelling" nterms 0;
        ignore (Encoding.add_int_lin_le encoding (opb_terms pos nterms) 0 : int);
        ignore
          (Encoding.add_int_lin_le encoding (opb_terms pos (negate_terms nterms)) 0 : int);
        [ pack_bool2int (Bool2int.make store ~b:(Var.of_int bi) ~x:(Var.of_int xi)) ]
    | _ ->
        let terms, rhs = difference_terms x b ~offset:0 in
        post_eq pos (normalise_terms terms) rhs
  in

  (* ---------------------------------------------------------------- M4, arithmetic

     lib/core/prop/arith.ml's header is the specification of what is posted here and
     why; this is the wiring. Three things about it are worth stating on this side of
     the boundary.

     First, the auxiliary Booleans are DEFINED BEFORE anything else, unconditionally,
     for every auxiliary the constraint carries -- even on a path that then does not
     use one. lib/flatzinc/builder.ml creates only the auxiliaries it expects to be
     used, but the two decisions live in two files, and an auxiliary left undefined is
     a free variable of the model that [Model.check_assignment] would then judge
     against a definition nothing established. Posting the definition anyway makes the
     agreement between the two files unnecessary rather than merely likely.

     Second, a definition is an ordinary [int_lin_le_reif], posted through the very
     same [post_reif_le] every reified builtin uses. There is no second reification
     door and no second big-M to keep in step with [Encoding]'s.

     Third, the rows themselves go through [Encoding.add_int_lin_le] and [Linear.make]
     over the SAME normalised term list, exactly as [post_le] does, so M1-T23's cap
     measures what is actually posted and [Model_row] names a row [Linear.pb_row] can
     reproduce. *)
  let aff_of (op : Model.operand) : Arith.aff =
    match op with Model.Const n -> Arith.aff_const n | Model.Var i -> Arith.aff_var i
  in
  let case_of (op : Model.operand) : Arith.case =
    match op with Model.Const n -> Arith.Case_const n | Model.Var j -> Arith.Case_var j
  in
  let bound i = bounds.(i) in
  (* The sign of the first operand, as [Arith] wants it. When the builder made a
     Boolean, that Boolean IS the answer. When it did not, the declared domain has to
     settle the question on its own -- and if it does not, the two files have drifted
     and this is a bug in one of them, so it says so rather than guessing a sign. *)
  let arith_sign pos ~builtin (x : Model.operand) (aux : Model.aux) : Arith.sign =
    match aux.Model.x_sign with
    | Some b -> Arith.Bit b
    | None -> (
        match x with
        | Model.Const n -> if n >= 0 then Arith.Nonneg else Arith.Neg
        | Model.Var i ->
            let lo, hi = bounds.(i) in
            if lo >= 0 then Arith.Nonneg
            else if hi < 0 then Arith.Neg
            else
              Error.failf pos
                "internal: builtin `%s` needs a sign split on `%s` (declared %d..%d) but \
                 the front end created no Boolean for it"
                builtin names.(i) lo hi)
  in
  (* `b <-> e >= k`, as the [int_lin_le_reif] `b <-> (-e <= -k)`. *)
  let post_ge_def pos ~builtin ~pack (e : Model.operand) k b =
    let terms, rhs = difference_terms (Model.Const 0) e ~offset:(Checked.neg k) in
    post_reif_le pos ~builtin ~pack (normalise_terms terms) rhs (Model.Var b)
  in
  let post_aux_defs pos ~builtin ~pack (x : Model.operand) (y : Model.operand)
      (aux : Model.aux) =
    let sign =
      match aux.Model.x_sign with
      | None -> []
      | Some b -> post_ge_def pos ~builtin ~pack x 0 b
    in
    sign
    @ List.concat_map (fun (v, b) -> post_ge_def pos ~builtin ~pack y v b) aux.Model.y_ge
  in
  let post_arith_rows pos ~builtin ~pack (rows : Arith.row list) =
    List.concat_map
      (fun (r : Arith.row) ->
        let nterms = normalise_terms r.Arith.r_terms in
        post_le_as ~pack
          ~what:("a row of this `" ^ builtin ^ "`")
          pos nterms r.Arith.r_rhs)
      rows
  in
  (* x * y = z. With y a constant this is the linear equality c*x = z and none of the
     machinery above is needed -- no ladder, no sign, no cushion -- so it takes that
     path, and lib/flatzinc/builder.ml creates no auxiliary for it. *)
  let post_int_times pos x y z aux =
    let builtin = "int_times" in
    let defs = post_aux_defs pos ~builtin ~pack:pack_times_guard x y aux in
    match y with
    | Model.Const c ->
        let tx, cx =
          match x with
          | Model.Var i -> ([ (c, i) ], 0)
          | Model.Const n -> ([], Checked.mul c n)
        in
        let tz, cz =
          match z with
          | Model.Var i -> ([ (-1, i) ], 0)
          | Model.Const n -> ([], Checked.neg n)
        in
        defs @ post_eq pos (normalise_terms (tx @ tz)) (Checked.neg (Checked.add cx cz))
    | Model.Var _ ->
        let sign = arith_sign pos ~builtin x aux in
        defs
        @ post_arith_rows pos ~builtin ~pack:pack_times_row
            (Arith.times_rows ~bound ~x:(aff_of x) ~y:(case_of y) ~z:(aff_of z) ~sign
               ~ge:aux.Model.y_ge)
  in
  (* q = x div y. There is no linear path here at any arity: truncation toward zero is
     decided by the sign of x (D-0033), so even a constant divisor keeps its sign
     split. A constant divisor only collapses the ladder to one case, which
     [Arith.Case_const] already is. *)
  let post_int_div pos x y q aux =
    let builtin = "int_div" in
    let defs = post_aux_defs pos ~builtin ~pack:pack_div_guard x y aux in
    let sign = arith_sign pos ~builtin x aux in
    defs
    @ post_arith_rows pos ~builtin ~pack:pack_div_row
        (Arith.div_rows ~bound ~x:(aff_of x) ~y:(case_of y) ~q:(aff_of q) ~sign
           ~ge:aux.Model.y_ge)
  in
  let post_int_abs pos x z aux =
    let builtin = "int_abs" in
    let defs = post_aux_defs pos ~builtin ~pack:pack_abs_guard x x aux in
    let sign = arith_sign pos ~builtin x aux in
    defs
    @ post_arith_rows pos ~builtin ~pack:pack_abs_row
        (Arith.abs_rows ~bound ~x:(aff_of x) ~z:(aff_of z) ~sign)
  in

  (* A ground constraint -- one whose term list is empty once constants are folded, such
     as `int_le(1, 2)` or an int_lin_le over an all-constant array -- is posted like any
     other, and deliberately so.

     If it holds, the row is a vacuously true `>= -k` line in the .opb and the propagator
     computes slack >= 0 and does nothing; both are harmless.

     If it does not hold, the model is refuted before search begins and the proof still
     has to establish that. Dropping the constraint would make the solver report UNSAT
     with a proof that does not support it -- the .opb would be satisfiable. Posting it
     works: the expansion produces an empty left-hand side with a positive right-hand
     side, `>= 1 ;`, the [Linear] instance (which the engine seeds into its queue even
     though it watches no variable) sees slack < 0 on the first pass and reports a
     conflict with no decision active, and search renders that as D-0013's derivation --
     here a single `pol <row_id>` restating the contradiction -- and concludes UNSAT
     citing it.

     This was checked against the checker rather than assumed, because none of the
     documentation says whether a constraint with no terms is even parseable. It is: an
     .opb line `>= 1 ;` is accepted, `pol` over it is accepted, `conclusion UNSAT` citing
     the result is accepted, and the vacuously true form `>= -1 ;` is accepted alongside
     a `conclusion SAT`. It also verifies with `#variable= 0`, i.e. in a model whose only
     content is the ground contradiction.

     A disequality reaches the same case by a different route, and `int_ne(x, x)` is it:
     [normalise_terms] merges the two occurrences of x into a zero coefficient and drops
     it, leaving the empty sum <> 0, which is false. There is no special case for that
     either, and none is wanted. [Encoding.add_int_lin_ne]'s A/B pair degenerates to two
     contradictory units on its own auxiliary Boolean; [Ne.propagate] finds every one of
     its (zero) terms fixed with the sum at the value it must avoid and conflicts with an
     empty [Clause]; and the refutation veripb accepts is `rup >= 1 ;`, closed the
     D-0022/I-X7 way because it rests on a clause. That model is
     test/models/ne_self_unsat.fzn. *)
  (* M14-e2e-verification-T3: the .scp name of the k-th constraint is `c<k>`, k counted
     from 1 in file order (tools/e2e/fzn2scp.py), which is [m.constraints]' order. *)
  let e2e_k = ref 0 in
  let instances =
    List.concat_map
      (fun (c : Model.constr) ->
        if Encoding.e2e_on encoding then (
          (* a gcc copy's int_eq (c_id = "") is no .scp constraint and takes no number *)
          if c.Model.c_id <> "" then incr e2e_k;
          Encoding.e2e_begin encoding ~name:(Printf.sprintf "c%d" !e2e_k)
            (e2e_spec names c));
        let pos = c.Model.c_pos in
        (* [check_row] is the diagnostic path and covers every row this arm posts, but
           the arithmetic that happens *before* a row exists -- merging duplicate
           coefficients, folding a constant operand into the right-hand side, negating
           an equality's terms -- is checked too (M1-T23) and can raise first, on
           inputs so large that no magnitude can be reported. Converting that to the
           same positioned [Error.failf] is what stops an overflowing model from
           leaving the CLI with an escaping exception instead of a diagnostic. *)
        let r =
          try
            match c.Model.k with
            | Model.Int_lin_le (terms, rhs) -> post_le pos (normalise_terms terms) rhs
            | Model.Int_lin_eq (terms, rhs) -> post_eq pos (normalise_terms terms) rhs
            | Model.Int_lin_ne (terms, rhs) ->
                post_ne pos (normalise_terms terms) rhs ~pack:pack_lin_ne
            | Model.Int_le (a, b) ->
                let terms, rhs = difference_terms a b ~offset:0 in
                post_le pos (normalise_terms terms) rhs
            | Model.Int_lt (a, b) ->
                let terms, rhs = difference_terms a b ~offset:(-1) in
                post_le pos (normalise_terms terms) rhs
            | Model.Int_eq (a, b) ->
                let terms, rhs = difference_terms a b ~offset:0 in
                post_eq pos (normalise_terms terms) rhs
            | Model.Int_ne (a, b) ->
                let terms, rhs = difference_terms a b ~offset:0 in
                post_ne pos (normalise_terms terms) rhs ~pack:pack_ne
            | Model.Bool_clause (ps, ns) ->
                clause ~builtin:"bool_clause" ~pack:pack_bool_clause pos
                  (List.map (fun o -> (o, true)) ps @ List.map (fun o -> (o, false)) ns)
            | Model.Array_bool_or (xs, r) -> post_array_bool_or pos xs r
            | Model.Array_bool_and (xs, r) -> post_array_bool_and pos xs r
            | Model.Bool2int (b, x) -> post_bool2int pos b x
            | Model.Bool_eq (a, b) -> post_bool_eq pos a b
            | Model.Bool_not (a, b) -> post_bool_not pos a b
            | Model.Int_lin_le_reif (terms, rhs, r) ->
                post_reif_le pos ~builtin:"int_lin_le_reif" ~pack:pack_int_lin_le_reif
                  (normalise_terms terms) rhs r
            | Model.Int_le_reif (a, b, r) ->
                let terms, rhs = difference_terms a b ~offset:0 in
                post_reif_le pos ~builtin:"int_le_reif" ~pack:pack_int_le_reif
                  (normalise_terms terms) rhs r
            | Model.Int_eq_reif (a, b, r) ->
                let terms, rhs = difference_terms a b ~offset:0 in
                post_reif_eq pos ~builtin:"int_eq_reif" ~pack:pack_int_eq_reif
                  ~positive:true (normalise_terms terms) rhs r
            | Model.Int_ne_reif (a, b, r) ->
                let terms, rhs = difference_terms a b ~offset:0 in
                post_reif_eq pos ~builtin:"int_ne_reif" ~pack:pack_int_ne_reif
                  ~positive:false (normalise_terms terms) rhs r
            | Model.Int_times (x, y, z, aux) -> post_int_times pos x y z aux
            | Model.Int_div (x, y, q, aux) -> post_int_div pos x y q aux
            | Model.Int_abs (x, z, aux) -> post_int_abs pos x z aux
            | Model.All_different xs -> post_all_different pos xs
            | Model.Global_cardinality (xs, cover, counts) ->
                post_global_cardinality pos xs cover counts
            | Model.Cumulative (ss, ds, rs, cap) -> post_cumulative pos ss ds rs cap
            | Model.Array_int_element (i, vs, c) -> post_array_int_element pos i vs c
            | Model.Array_int_maximum (mo, xs) -> post_maxmin pos ~dir:Maxmin.Max mo xs
            | Model.Array_int_minimum (mo, xs) -> post_maxmin pos ~dir:Maxmin.Min mo xs
            | Model.Regular r -> post_regular pos r (* M7-T28, D-0146 *)
            | Model.Inverse iv -> post_inverse pos iv (* M7-T28, D-0151 *)
            | Model.Member mb -> post_member pos mb (* M7-T28, D-0159 *)
          with Checked.Overflow msg ->
            reject_row pos
              ~what:
                (Printf.sprintf
                   "this constraint (its coefficients alone already overflow: %s)" msg)
              ~magnitude:None
        in
        Encoding.e2e_end encoding;
        r)
      m.Model.constraints
  in
  (* M7-T11: the declared holes of a set domain, as propagator instances.

     One [Ne] per hole, over the single term (+1, x) with right-hand side the hole, so
     the instance's whole job is "x <> h". [Ne] cites no row id (its header says why)
     and justifies itself with a self-contained [rup] over order literals -- and the
     clause that [rup] has to land on is exactly the hole row
     [Encoding.declare_int_with_holes] has already put in the .opb, so no disequality
     row and no auxiliary Boolean is minted for it. That is what keeps D-0072's "one
     clause per hole" true of the artefact and not just of the intention:
     [Encoding.add_int_lin_ne] would have cost an aux variable and two rows instead.

     These come BEFORE the model's own constraints so that a declared hole is pruned
     before anything reasons about the variable, and because a fixed order is what the
     determinism gate checks. *)
  let hole_instances =
    List.concat_map
      (fun (i, (v : Model.var)) ->
        List.map
          (fun h -> pack_lin_ne (Ne.make store [ (1, Var.of_int i) ] h))
          (holes_of_domain v))
      (Array.to_list (Array.mapi (fun i v -> (i, v)) m.Model.vars))
  in
  let instances = hole_instances @ instances in
  let engine = Engine.create (List.mapi (fun id pending -> pending id) instances) in
  { store; engine; encoding; objective; order = search_order }
