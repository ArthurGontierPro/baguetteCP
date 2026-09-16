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
   falls back to [Explanation.Trivial], which carries no payload and therefore cannot
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
     a row, and D-0011's hazard -- [Explanation.Trivial], meaning "whatever
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

   The checks run *before* the row is posted, which is the whole point. The gap
   M1-T23 closed was not that a propagator pruned wrongly -- it was that
   [Encoding.linear_terms_int_lin_le] folds the constant sum_i a_i * lo_i with the
   same wrapping arithmetic the propagator's slack uses, so the .opb row and the
   solver agreed on a model that was not the one in the .fzn, and veripb had nothing
   to disagree with. lib/proof/ cannot defend itself against that (a row has to be
   written; there is no "decline" for an artefact). Refusing the model here is what
   defends it, and refusing it *here* rather than at the first propagation is what
   keeps [Checked.Overflow] off the search path entirely. *)

module Var = Baguette_core.Var
module Checked = Baguette_core.Checked
module Domain = Baguette_core.Domain
module Store = Baguette_core.Store
module Propagator = Baguette_core.Propagator
module Linear = Baguette_core.Linear
module Lin_eq = Baguette_core.Lin_eq
module Ne = Baguette_core.Ne
module Engine = Baguette_core.Engine
module Encoding = Baguette_proof.Encoding
module Lit = Baguette_proof.Lit

type t = {
  store : Baguette_core.Store.t;
  engine : Baguette_core.Engine.t;
  encoding : Baguette_proof.Encoding.t;
}

(* ------------------------------------------------------------------- term handling *)

(* Merge repeated variable indices by summing their coefficients, then drop the terms
   that cancelled to zero. First-occurrence order is preserved so the emitted row is a
   deterministic function of the model -- a proof that changes shape between runs is a
   proof nobody can diff against a previous failure.

   Called once per constraint; its result is what both the .opb row and the propagator
   are built from. See the module header. *)
let normalise_terms (terms : (int * int) list) : (int * int) list =
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

let reject_set_domain (v : Model.var) values =
  let lo = List.fold_left min (List.hd values) values in
  let hi = List.fold_left max (List.hd values) values in
  Error.failf v.Model.v_pos
    "variable `%s` is declared over the set domain %s, which baguette cannot encode: \
     `Encoding.declare_int` takes only ~lo and ~hi, so the holes in a set domain have no \
     representation in the .opb. Encoding the hull %d..%d instead would be a \
     *relaxation* -- the solver could then report UNSAT and hand veripb a proof against \
     an .opb that is satisfiable -- so the model is rejected instead. Missing: a \
     hole-removal constraint in the encoding (the direct encoding, roadmap M1-T9/M4)."
    v.Model.v_name
    (Model.string_of_domain v.Model.v_dom)
    lo hi

let reject_objective pos what operand_name =
  Error.failf pos
    "unsupported solve goal `%s %s`: baguette searches for a solution only. Optimisation \
     -- the objective line in the .opb and `conclusion BOUNDS` in the proof \
     (docs/SPEC.md section 4.3) -- is roadmap M5. Use `solve satisfy;`."
    what operand_name

let reject_search pos ~annotation =
  Error.failf pos
    "unsupported search annotation %s: `Search.solve` implements first_fail variable \
     selection with indomain_min branching, which is docs/SPEC.md section 3.4's default. \
     Any other strategy would be silently ignored rather than honoured, so it is \
     rejected (docs/SPEC.md section 3.4 says the annotation MUST be honoured when \
     present). Remove the annotation, or write `int_search(..., first_fail, \
     indomain_min, complete)`."
    annotation

(* roadmap M1-T23. The two arithmetic rejections. [Checked.limit] and the 9M + 6
   envelope it is chosen against are derived in lib/core/checked.ml's header; the
   message repeats the figure rather than the derivation because the person reading it
   is holding a model, not the solver. *)

let reject_declared_bound (v : Model.var) lo hi =
  Error.failf v.Model.v_pos
    "variable `%s` is declared over %d..%d, and a declared bound may not exceed +/-%d. \
     baguette computes over OCaml's native 63-bit int, which wraps silently, and a \
     wrapped product is not merely a wrong bound: lib/proof/encoding.ml expands the .opb \
     row from the same arithmetic the propagator uses, so the corrupted row and the \
     corrupted pruning agree and veripb accepts a refutation of a model you did not \
     write. The limit leaves every intermediate the solver and the encoding compute \
     inside the representable range. Rescale the model, or shift the domain towards \
     zero."
    v.Model.v_name lo hi Checked.limit

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

(* [Model.search] is a list of annotations; [Seq] nests. Nothing here changes how the
   search runs -- [Search.solve] is not parameterised -- so the only useful thing to do
   with an annotation is to check that it asks for what is actually implemented. *)
let rec check_search (m : Model.t) (s : Model.search) =
  match s with
  | Model.Seq subs -> List.iter (check_search m) subs
  | Model.Int_search (_, vc, vl) ->
      let pos = search_pos m s in
      let vc_name =
        match vc with
        | Model.Input_order -> "input_order"
        | Model.First_fail -> "first_fail"
      in
      let vl_name =
        match vl with
        | Model.Indomain_min -> "indomain_min"
        | Model.Indomain_max -> "indomain_max"
      in
      if vc <> Model.First_fail || vl <> Model.Indomain_min then
        reject_search pos
          ~annotation:(Printf.sprintf "`int_search(..., %s, %s, ...)`" vc_name vl_name)

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
  | Model.Dset values -> reject_set_domain v values

(* The .opb's Boolean variable names come from [Lit.sanitize], which maps every
   character outside [A-Za-z0-9_] to '_'. Two distinct FlatZinc identifiers can collide
   under it -- the array element `x[1]` and a scalar called `x_1_` both become `x_1_` --
   and a collision would silently merge their order literals inside [Opb.normalise],
   producing a row that is not the model's. [Encoding] keys on the unsanitised name and
   so would not notice. Checked once, here, because this is the only place that knows
   the whole variable list. *)
let check_name_collisions (m : Model.t) =
  let seen = Hashtbl.create 64 in
  Array.iter
    (fun (v : Model.var) ->
      let s = Lit.sanitize v.Model.v_name in
      match Hashtbl.find_opt seen s with
      | Some other when not (String.equal other v.Model.v_name) ->
          Error.failf v.Model.v_pos
            "variables `%s` and `%s` both become `%s` in the .opb (identifiers are \
             sanitised for the pseudo-Boolean format, docs/PROOF-FORMAT.md section 3), \
             so their encodings would be indistinguishable. Rename one of them."
            other v.Model.v_name s
      | Some _ ->
          Error.failf v.Model.v_pos "variable `%s` is declared more than once"
            v.Model.v_name
      | None -> Hashtbl.replace seen s v.Model.v_name)
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

let pack_linear (lin : Linear.t) : pending =
 fun id -> Propagator.pack ~id (module Linear : Propagator.S with type t = Linear.t) lin

(* [Ne] and [Ne.Int_ne] are one propagator over one [Ne.t]; they differ only in the
   [name] the packed instance reports, so each builtin is packed under its own. *)
let pack_lin_ne (p : Ne.t) : pending =
 fun id -> Propagator.pack ~id (module Ne : Propagator.S with type t = Ne.t) p

let pack_ne (p : Ne.t) : pending =
 fun id -> Propagator.pack ~id (module Ne.Int_ne : Propagator.S with type t = Ne.t) p

let compile (m : Model.t) : t =
  (match m.Model.objective with
  | Model.Satisfy -> ()
  | Model.Minimize op ->
      reject_objective (operand_pos m op) "minimize" (Model.string_of_operand m op)
  | Model.Maximize op ->
      reject_objective (operand_pos m op) "maximize" (Model.string_of_operand m op));
  List.iter (check_search m) m.Model.search;
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
  let names = Array.map (fun (v : Model.var) -> v.Model.v_name) m.Model.vars in
  let store =
    Store.create ~names ~domains:(Array.map (fun (lo, hi) -> Domain.make lo hi) bounds)
  in
  let encoding = Encoding.create () in
  Array.iteri
    (fun i (v : Model.var) ->
      let lo, hi = bounds.(i) in
      match v.Model.v_dom with
      | Model.Dbool -> Encoding.declare_bool encoding v.Model.v_name
      | _ -> Encoding.declare_int encoding v.Model.v_name ~lo ~hi)
    m.Model.vars;

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

  (* One row + one instance. [nterms] is the *same* normalised list on both sides. *)
  let post_le pos nterms rhs =
    check_row pos ~what:"this linear inequality" nterms rhs;
    let row_id = Encoding.add_int_lin_le encoding (opb_terms pos nterms) rhs in
    [ pack_linear (Linear.make ~row_id store (prop_terms nterms) rhs) ]
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
    [ pack_linear le; pack_linear ge ]
  in
  (* Two rows, one instance, no row id -- see the module header. The propagator is
     built here, eagerly, rather than inside the pending closure, because [Ne.make]
     reads each variable's *declared* domain out of the store (D-0010) and must run
     before anything narrows it; only the packing is deferred. *)
  let post_ne pos nterms rhs ~pack =
    check_row pos ~what:"this disequality" nterms rhs;
    ignore (Encoding.add_int_lin_ne encoding (opb_terms pos nterms) rhs : int * int);
    [ pack (Ne.make store (prop_terms nterms) rhs) ]
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

     This was checked against veripb 2.2.2 rather than assumed, because none of the
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
  let instances =
    List.concat_map
      (fun (c : Model.constr) ->
        let pos = c.Model.c_pos in
        (* [check_row] is the diagnostic path and covers every row this arm posts, but
           the arithmetic that happens *before* a row exists -- merging duplicate
           coefficients, folding a constant operand into the right-hand side, negating
           an equality's terms -- is checked too (M1-T23) and can raise first, on
           inputs so large that no magnitude can be reported. Converting that to the
           same positioned [Error.failf] is what stops an overflowing model from
           leaving the CLI with an escaping exception instead of a diagnostic. *)
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
        with Checked.Overflow msg ->
          reject_row pos
            ~what:
              (Printf.sprintf
                 "this constraint (its coefficients alone already overflow: %s)" msg)
            ~magnitude:None)
      m.Model.constraints
  in
  let engine = Engine.create (List.mapi (fun id pending -> pending id) instances) in
  { store; engine; encoding }
