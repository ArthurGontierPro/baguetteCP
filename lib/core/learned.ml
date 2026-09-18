(* learned.ml: the LEARNED-CONSTRAINT type, its runtime instance, and its proof-side
   introduction and deletion (M2-L1).

   Consistency level: none of its own. A learned constraint does not get a propagator
   family -- see "The bet" below; it is instantiated as a [Linear] instance and prunes at
   [Linear]'s level (BOUNDS, docs/SPEC.md 3.2). Governing records: docs/DECISIONS.md
   D-0044 (the type) and D-0045's addendum (the proof-side lifetime).

   ---------------------------------------------------------------------------
   The type: sum a_i l_i >= b, over Lit.t
   ---------------------------------------------------------------------------

   D-0044 decided that the learned object is a pseudo-Boolean inequality and that a
   CLAUSE is its degree-1, unit-coefficient case rather than a separate type. That is
   what [t] below is, and [of_clause] is not a second constructor -- it is [make] with
   every coefficient 1 and degree 1.

   The argument D-0044 rests on is a property of our encoding: D-0028's order encoding is
   eager, so every atomic constraint x >= v already IS a 0-1 variable in the .opb, and a
   clause over order literals already IS the PB constraint sum l_i >= 1 over those same
   variables. Pumpkin's LLG has to mint an auxiliary variable per literal to cross from a
   clause to a linear inequality; we have nothing to cross.

   [make] normalises: a negative coefficient is absorbed by negating its literal
   (a*l = a + |a|*~l, so the degree grows by |a|), a zero coefficient is dropped, and
   repeated literals are merged. After [make] every coefficient is >= 1, which is the
   form [Opb] and both checkers want and the form the reduction rules of M2-L5 assume.

   ---------------------------------------------------------------------------
   The bet, and exactly where it holds -- MEASURED, M2-L1
   ---------------------------------------------------------------------------

   docs/ROADMAP.md M2-L1 bets that "a learned row is exactly what [Linear] already
   propagates -- no new propagator family if this holds". It holds, with a boundary that
   is worth stating precisely because M2-L3 will run into it:

     - In the PROOF, D-0044 is right without qualification: the order literals are real
       0-1 variables of the .opb and a [Learned.t] is written out by [to_opb] with no
       conversion and no auxiliary variable.
     - In the SOLVER'S STORE they are not variables at all. The store holds the model's
       integer variables; [x >= v] is a *question about a domain*, not a handle. So a
       runtime instance exists only where the PB row can be read back as a linear row
       over those integer variables, and [to_linear_row] below is exactly the predicate
       for that. It succeeds on:

         * a clause over `var bool`s -- D-0007 order-encodes a Boolean on [0, 1], so its
           ladder has ONE rung and [b >= 1] is the integer b itself. This is the D-0044
           check (test (b)): a degree-1 unit-coefficient [Learned.t] over Boolean order
           literals is the linear row `sum -b_i + sum y_j <= |y| - 1`, and [Linear] on it
           is unit propagation.
         * a model row's own expansion -- [Encoding.linear_terms_int_lin_le] gives every
           rung of a variable's ladder the SAME coefficient a_i, and a uniform run over
           the whole ladder is a_i * (x - lo_i). This is the round-trip (test (a)).
         * a single threshold that is outside the ladder, which is a constant.

       and it FAILS, returning [None], on a threshold strictly inside an integer
       variable's ladder: `[x >= 3]` for x declared 0..5 is not any linear function of x
       over that box, and neither is a sum of two such. There is no rounding of this: a
       1UIP cut over integer variables produces exactly those literals, so **M2-L3 must
       expect [None] from [to_linear_row] on its own output** and either restrict the cut
       to the shapes above or accept that the learned constraint is proof-only until a
       propagator for it exists. Recorded here rather than discovered there.

   Nothing in this module widens [Linear]. It builds a [Linear.t] and hands it to
   [Propagator.pack], which is the whole of "no new propagator family".

   ---------------------------------------------------------------------------
   Why the [Linear.t] is built here instead of through [Linear.make]
   ---------------------------------------------------------------------------

   [Linear.make] reads each variable's domain out of the store at construction time and
   freezes it as the term's DECLARED domain -- its own header says this "has to happen
   before anything ... has narrowed it". A learned constraint is created in the middle of
   search, when domains have been narrowed, so [make] would freeze a narrow box as the
   declared one and every [Order_reason.weaken_declared] chain the instance later builds
   would be short of the ladder the .opb actually contains. The chain would then fail to
   cancel the row's coefficient and the `pol` would derive something other than the bound.

   So the declared bounds come from the ENCODING, which is where the ladder's width is
   defined ([Encoding.domain]), and the [Linear.t] record is built directly. That is a
   deliberate reach into another module's representation and it is confined to
   [to_linear] below. It is not a shortcut around [make]'s checks -- [make] has none
   beyond the freeze -- it is the freeze done against the right source.

   ---------------------------------------------------------------------------
   The proof side: level 0, or the backjump takes it -- D-0045's addendum
   ---------------------------------------------------------------------------

   MEASURED by M2-L1 before it was fixed, against both checkers, and it is exactly what
   D-0045 predicted:

     - 3.0: [Writer.fresh] tags every id with the writer's current level and
       [Writer.wipe_level l] deletes every id tagged at level >= l. A constraint derived
       at the conflict level is deleted by the backjump that follows, and citing it
       afterwards is "Trying to access constraint with ID 3 that has already been
       deleted".
     - 2.0: our [t.tags] is not maintained at all -- the checker holds the level stack
       and `w l` retires against it. Same deletion, different machinery, and the wording
       shares no useful substring: "Rule 6 is trying to access constraint (constraintId
       3), that was marked as safe to delete".

   [introduce] therefore emits inside [Justify.with_level ctx 0], which moves the level
   FOR REAL in both formats (a `# 0` under 2.0, a `% level 0` comment under 3.0) rather
   than writing our own table, which would have been green under 3.0 and wrong under 2.0.

   The consequence for I-X2 is the one M2-L4 will own: a level-0 id is no longer retired
   by any backjump, so somebody must delete it explicitly. That somebody is [retire], and
   until the retention policy exists its caller is whoever called [introduce]. A learned
   constraint is the first object in this solver whose lifetime is not a search level's.

   ---------------------------------------------------------------------------
   Determinism (docs/ROADMAP.md M2-L1 test (e))
   ---------------------------------------------------------------------------

   Nothing in this module iterates a hash table, and no function here returns a list
   whose order depends on one. [make] sorts and merges through [Lit.compare]; the
   grouping in [to_linear_row] is done on a sorted list, not in a [Hashtbl]. The gate
   requires two runs of one binary to be byte-identical, and a learned database iterated
   in hash order is the specific way learning breaks it. There is no [Hashtbl] in this
   file; keep it that way. *)

module Lit = Baguette_proof.Lit
module Opb = Baguette_proof.Opb
module Writer = Baguette_proof.Writer
module Encoding = Baguette_proof.Encoding

(* One term: a strictly positive coefficient on a literal. [make] is the only way to get
   one, and it is what establishes the sign. *)
type term = { coeff : int; lit : Lit.t }

(* sum_i coeff_i * lit_i >= degree. *)
type t = { terms : term list; degree : int }

(* ------------------------------------------------------------------- construction *)

(* Normalise to positive coefficients and merge repeats.

   [a * l] with a < 0 becomes [|a| * ~l] with the degree raised by [|a|], since
   l = 1 - ~l. A zero coefficient contributes nothing at all -- not even to the degree --
   and is dropped, exactly as [Encoding.linear_terms_int_lin_le] drops a zero term.

   Repeated literals are summed. This is not tidying: [Opb.normalise] and the checkers
   both expect a literal to appear once, and a cut that resolves two reasons naming the
   same bound produces repeats by construction (M2-L2's output does), so the merge is on
   the path M2-L3 will take. Sorting by [Lit.compare] makes the result a function of the
   SET of terms and not of the order they were built in, which is test (e). *)
let make (raw : (int * Lit.t) list) (degree : int) : t =
  let signed, degree =
    List.fold_left
      (fun (acc, d) (a, l) ->
        if a = 0 then (acc, d)
        else if a > 0 then ((l, a) :: acc, d)
        else ((Lit.negate l, -a) :: acc, d - a))
      ([], degree) raw
  in
  let sorted = List.sort (fun (l1, _) (l2, _) -> Lit.compare l1 l2) (List.rev signed) in
  let rec merge = function
    | [] -> []
    | [ (l, a) ] -> [ { coeff = a; lit = l } ]
    | (l1, a1) :: (l2, a2) :: rest ->
        if Lit.equal l1 l2 then merge ((l1, a1 + a2) :: rest)
        else { coeff = a1; lit = l1 } :: merge ((l2, a2) :: rest)
  in
  { terms = merge sorted; degree }

(* D-0044's degenerate case, written as what it is: every coefficient 1, degree 1. *)
let of_clause (lits : Lit.t list) : t = make (List.map (fun l -> (1, l)) lits) 1
let terms t = t.terms
let degree t = t.degree
let lits t = List.map (fun tm -> tm.lit) t.terms
let is_empty t = t.terms = []

(* Is this the clause case? Asked by tests, and by anything that wants to know whether a
   [rup] is available (a clause is RUP-checkable; a general PB inequality derived by
   cutting planes is not, which is the whole difficulty Koops et al. exist to solve and
   is M2-L6's problem, not this module's). *)
let is_clause t = t.degree = 1 && List.for_all (fun tm -> tm.coeff = 1) t.terms

(* ------------------------------------------------- M2-L6: PB arithmetic on the row *)

(* An instance's own row ([Propagator.pb_row]) as this type. [make] does the
   normalisation, so a [pb_row] may hand over negative coefficients -- and
   [Linear.pb_row] does, deliberately, so that the sign convention lives in exactly one
   place. *)
let of_pb_row (r : Propagator.pb_row) : t =
  make r.Propagator.r_terms r.Propagator.r_degree

(* [combine a ca b cb] is the cutting-planes ADDITION [ca * a + cb * b], which is what a
   `pol` line of the form [ida ca * idb cb * +] derives. It is the step that eliminates
   the pivot in PB conflict analysis, and the elimination is entirely in the third stage
   below.

   Three stages, and the third is the one a reader will look for:

     1. scale. Every coefficient and the degree multiplied, through [Checked] -- I-X8 and
        D-0029: growth past the cap must [raise], not wrap, and conflict analysis is the
        one place in this solver where coefficients multiply without bound. The raise
        propagates to the caller, which treats it as a reason to FALL BACK to the clause
        path rather than as a crash; see lib/core/pb_analysis.ml.
     2. merge. [make]'s job: repeated literals summed, zero coefficients dropped.
     3. CANCEL COMPLEMENTS. [make] does not do this one, and must not be changed to: it
        merges equal literals, and [l] and [~l] are not equal. But over 0-1 variables
        [l + ~l = 1], so

            p * l  +  n * ~l   =   min(p,n)  +  (p-m) * l  +  (n-m) * ~l,   m = min(p,n)

        and the constant moves across, LOWERING the degree by m. Skipping this stage
        would leave a row that is still sound but is not the row the checker holds: both
        checkers normalise complements away when they read a constraint, so our copy and
        theirs would disagree on every subsequent step, and the first [pol] built on the
        difference would be rejected. That is the whole reason this function exists
        instead of a fold over [make].

   The pivot is cancelled by this stage and by nothing else: the caller arranges that the
   pivot appears with coefficient [k] on one side and [k] on the other, so [p = n] and
   both terms vanish. Nothing here knows which literal was the pivot, which is correct --
   cancellation is arithmetic, not a special case. *)
let combine (a : t) (ca : int) (b : t) (cb : int) : t =
  let scaled t c = List.map (fun tm -> (Checked.mul c tm.coeff, tm.lit)) t.terms in
  let raw = scaled a ca @ scaled b cb in
  let degree = Checked.add (Checked.mul ca a.degree) (Checked.mul cb b.degree) in
  (* Net each pseudo-Boolean variable, keeping both polarities so the constant that
     falls out of the cancellation can be counted exactly once per variable. *)
  let sorted = List.sort (fun (_, l1) (_, l2) -> Lit.var_compare l1.Lit.v l2.Lit.v) raw in
  let rec cancel acc dropped = function
    | [] -> (acc, dropped)
    | (_, l) :: _ as group ->
        let mine, others =
          List.partition (fun (_, m) -> Lit.var_equal l.Lit.v m.Lit.v) group
        in
        let side positive =
          List.fold_left
            (fun s (c, m) -> if m.Lit.positive = positive then Checked.add s c else s)
            0 mine
        in
        let p = side true and n = side false in
        let m = min p n in
        let keep =
          List.filter
            (fun (c, _) -> c > 0)
            [
              (Checked.sub p m, { Lit.v = l.Lit.v; Lit.positive = true });
              (Checked.sub n m, { Lit.v = l.Lit.v; Lit.positive = false });
            ]
        in
        cancel (acc @ keep) (Checked.add dropped m) others
  in
  let terms, dropped = cancel [] 0 sorted in
  make terms (Checked.sub degree dropped)

let to_string t =
  Printf.sprintf "%s >= %d"
    (String.concat " "
       (List.map
          (fun tm -> Printf.sprintf "+%d %s" tm.coeff (Lit.to_string tm.lit))
          t.terms))
    t.degree

(* --------------------------------------------------------------------- proof side *)

(* The constraint as the .opb/.pbp writes it. [Opb.ge] is already the checkers' own
   normal form for a ">=" and [make] has already made every coefficient positive, so
   there is nothing to negate here. *)
let to_opb t = Opb.ge (List.map (fun tm -> (tm.coeff, tm.lit)) t.terms) t.degree

(* Put the learned constraint on the page and hand back its id.

   AT LEVEL 0, unconditionally -- see the module header. That is the whole of M2-L1's
   proof-side half and the reason [Justify.with_level] exists.

   [rup] is the rule, which is D-0044's staging and not a permanent choice: a learned
   CLAUSE is a single [rup] line, the checker re-derives the intermediate resolvents by
   unit propagation, and the cut choice costs nothing in proof size. A general PB
   inequality is not RUP-derivable and M2-L6 owes it a [pol] built from the reduction
   steps; that path will call [Justify.with_level] in exactly the same place, which is
   why the bracket is not folded into this function's body. [is_clause] is what a caller
   asks before trusting the [rup].

   I-X2: the id returned is an id you must delete, with [retire]. Nothing else will --
   a backjump will not, which is the point. *)
let introduce ctx t ~origin : Writer.cid =
  Justify.with_level ctx 0 (fun () -> Writer.rup (Justify.writer ctx) ~origin (to_opb t))

(* The other half of I-X2, and a separate function rather than a comment on [introduce]
   because a learned constraint's lifetime is a policy (M2-L4) and not a scope. *)
let retire ctx (id : Writer.cid) = Writer.delete (Justify.writer ctx) id

(* ------------------------------------------------- the runtime instance (the bet) *)

(* The PB row rewritten over the positive order literals only, as a sorted
   [(name, threshold, coefficient)] list plus a constant that moves to the left-hand
   side. A negated literal ~[x >= v] is [1 - [x >= v]], so it contributes its coefficient
   to the constant and minus its coefficient to the rung.

   [None] for a direct-encoding ([Eq]) literal: the direct encoding is a set of 0-1
   variables with no order to read a bound off (D-0019, D-0040), so there is no linear
   form and saying so is the honest answer. *)
let ladder_form t =
  let rec go acc const = function
    | [] -> Some (List.sort compare acc, const)
    | { coeff; lit } :: rest -> (
        match lit.Lit.v with
        | Lit.Eq _ -> None
        | Lit.Ge (x, v) ->
            if lit.Lit.positive then go ((x, v, coeff) :: acc) const rest
            else go ((x, v, -coeff) :: acc) (const + coeff) rest)
  in
  go [] 0 t.terms

(* One variable's rungs, read back as a linear contribution.

   [rungs] is that variable's [(threshold, coefficient)] pairs, sorted and with the zeros
   already dropped; [(lo, hi)] is its DECLARED domain, i.e. the ladder the .opb actually
   contains. The answer is [Some (a, k)] meaning "contributes a * x, plus the constant
   k", or [None] meaning the row has no linear form over this variable.

   Three cases, and they are the whole of the boundary the module header states:

     - a threshold at or below [lo] is the constant true and a threshold above [hi] is
       the constant false. Neither depends on x. These are folded away first, so a row
       that happens to mention an out-of-range rung is not refused for it.
     - the remaining rungs must be EXACTLY [lo+1 .. hi], each with the same coefficient
       a. Then sum_v a*[x >= v] = a*(x - lo), because the order encoding's own identity
       is x = lo + sum_{v=lo+1}^{hi} [x >= v] (docs/PROOF-FORMAT.md section 3). A `var
       bool` has hi = lo + 1, so a single rung satisfies this and the clause case falls
       out of the general rule rather than being special-cased.
     - anything else -- a gap in the run, or two rungs at different coefficients -- has
       no linear form. This is where an interior threshold on an integer variable lands.

   Note that "exactly the ladder" is checked by construction (length and consecutiveness)
   rather than by set membership: a row with a rung repeated would otherwise pass the
   length test, and [make] has already merged repeats, so the two agree. *)
let linear_of_rungs ~lo ~hi rungs =
  let const = ref 0 in
  let inside =
    List.filter
      (fun (v, c) ->
        if v <= lo then (
          const := !const + c;
          false)
        else if v > hi then false
        else true)
      rungs
  in
  match inside with
  | [] -> Some (0, !const)
  | (v0, a) :: _ ->
      let width = hi - lo in
      let consecutive =
        v0 = lo + 1
        && List.length inside = width
        && List.for_all2
             (fun (v, c) i -> v = lo + 1 + i && c = a)
             inside
             (List.init (List.length inside) Fun.id)
      in
      if consecutive then Some (a, !const - (a * lo)) else None

(* The whole row as `sum c_i x_i <= rhs` over integer variable NAMES, or [None] when it
   has no such form. [Linear] is a "<=" propagator and this module's [t] is a ">=", so
   the sign flips exactly once, here.

   Derivation, spelled out because the sign is the thing to get wrong:
     sum_i a_i * (x_i - lo_i) + K  >=  degree            (from the rungs)
     sum_i a_i x_i                 >=  degree - K'       where K' folds the -a_i*lo_i
     sum_i (-a_i) x_i              <=  K' - degree
*)
let to_linear_row t ~decl =
  match ladder_form t with
  | None -> None
  | Some (rungs, const0) ->
      (* [rungs] is sorted by (name, threshold), so a variable's rungs are contiguous. *)
      let rec group = function
        | [] -> []
        | (x, v, c) :: rest ->
            let mine, others = List.partition (fun (y, _, _) -> String.equal x y) rest in
            (x, (v, c) :: List.map (fun (_, v, c) -> (v, c)) mine) :: group others
      in
      let groups = group rungs in
      let rec fold acc const = function
        | [] -> Some (List.rev acc, const)
        | (x, rungs) :: rest -> (
            match decl x with
            | None -> None
            | Some (lo, hi) -> (
                let rungs =
                  List.filter (fun (_, c) -> c <> 0) (List.sort compare rungs)
                in
                match linear_of_rungs ~lo ~hi rungs with
                | None -> None
                | Some (0, k) -> fold acc (const + k) rest
                | Some (a, k) -> fold ((-a, x) :: acc) (const + k) rest))
      in
      Option.map (fun (terms, const) -> (terms, const - t.degree)) (fold [] const0 groups)

(* The [Linear.t] a learned row propagates as, or [None] when it has no linear form.

   [~row_id] is the proof id [introduce] returned: every [Combine] the instance builds is
   [Explanation.Model_row row_id], i.e. "cite that constraint". The constructor's name
   says "model row" for historical reasons (D-0015); what it means is a constraint id
   that is already on the page, and a learned constraint's id is exactly that -- which is
   why no new [Explanation] constructor is spent here, and D-0044's central claim would
   be in trouble if one were.

   The declared bounds come from [decl], not from the store: see the module header. *)
let to_linear ~row_id store ~decl t : Linear.t option =
  match to_linear_row t ~decl with
  | None -> None
  | Some (rterms, rhs) ->
      let rec build acc = function
        | [] -> Some { Linear.terms = List.rev acc; rhs; row_id }
        | (a, name) :: rest -> (
            match (Store.var_named store name, decl name) with
            | Some x, Some (lo, hi) ->
                build ({ Linear.coeff = a; x; decl_lo = lo; decl_hi = hi } :: acc) rest
            | _ -> None)
      in
      build [] rterms

(* Pack it for the engine. [~id] must be [Engine.next_id] of the engine it is about to be
   added to -- [Engine.add] checks that and says why. *)
let instance ~id ~row_id store ~decl t : Propagator.instance option =
  Option.map
    (fun lin -> Propagator.pack ~id (module Linear) lin)
    (to_linear ~row_id store ~decl t)

(* The declared-domain lookup an [Encoding] provides, in the shape [to_linear] wants.
   Kept here rather than in [Encoding] because it is this module's question: [Encoding]
   already answers it, it just answers it by raising. *)
let decl_of_encoding enc name =
  if Encoding.is_declared enc name then Some (Encoding.domain enc name) else None
