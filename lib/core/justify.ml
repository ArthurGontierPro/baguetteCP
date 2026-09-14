(* Justify: turn an [Explanation.t] into VeriPB proof rules and hand back the id of the
   resulting constraint.

   This lives in [core], not [proof] (docs/ARCHITECTURE.md section 1): the dependency
   direction is [core -> proof], so [proof] cannot see [Explanation] and the bridge has
   to sit on the [core] side of the line, calling down into [Baguette_proof.Writer].

   docs/PROOF-FORMAT.md section 2's rule is "prefer [pol] over [rup] everywhere [pol]
   states the reasoning; [rup] makes the checker search" -- [Cut] and [Trivial] follow
   it. [Clause] cannot (see the comment there), and neither, it turns out, can [Linear]
   as [Explanation.t] is shaped today -- see D-0009 (docs/DECISIONS.md) and the comment
   on [emit_linear].

   -------------------------------------------------------------------------------
   Context
   -------------------------------------------------------------------------------

   [Explanation.Trivial] carries no data: it is just "the model constraint itself
   justifies this". That is only meaningful relative to *which* model constraint is
   currently being justified, and the [Explanation.t] type -- frozen for M1-T7, shared
   with agent-core's propagators -- has no field to say so. So [emit] cannot answer
   "which constraint is this about" from the explanation value alone; it has to be told,
   which is what [ctx] is for:

     - [writer]   the proof writer every rule is emitted through.
     - [encoding] lets Justify sanity-check that the literals an explanation mentions
       belong to variables the encoding actually declared, which turns "propagator
       passed garbage" into an immediate, legible error instead of a confusing veripb
       rejection several lines later.
     - [model_id] the lookup: "what is the id of the model constraint this batch of
       explanations is about, right now". A thunk rather than a plain [Writer.cid]
       because the answer can depend on state the caller only has lazily (e.g. a
       constraint not yet posted), and because [for_constraint] below rebinds it
       per-site while sharing everything else.

   A single [ctx] is not pinned to one model constraint for its whole life: a caller
   working through several posted constraints uses [for_constraint ctx model_id] to get
   a view with a different [model_id] but the *same* writer, encoding and memo (the memo
   lives behind a [ref] precisely so that copying the record for [for_constraint] does
   not fork it). Construct one [ctx] near where the writer and encoding themselves live,
   and re-derive per-constraint views from it with [for_constraint] as needed.

   -------------------------------------------------------------------------------
   Memoisation
   -------------------------------------------------------------------------------

   The same [Explanation.t] value can be demanded more than once while conflict
   analysis walks the reason graph (that is exactly why [Explanation.force] itself
   memoises). Emitting it twice would write duplicate proof rules, waste ids, and make
   the proof unreadable, so [emit] keeps its own memo from explanation identity to the
   [Writer.cid] already produced for it.

   Identity, not structural equality, is the only honest key: [Explanation.t] embeds
   closures ([Deferred]'s thunk), which have no useful notion of structural equality
   (and [Hashtbl.hash] on a value that stores a *mutable* memoised result is actively
   dangerous as a hash key -- forcing the thunk changes its representation, so a hash
   computed before forcing would stop matching the bucket after). So the memo is a plain
   association list compared with [==]. That is intentionally simple: the number of
   distinct explanation nodes alive during one conflict's analysis is small, so a linear
   scan costs nothing that matters, and it sidesteps the mutable-hash-key trap entirely.

   [Trivial] is never memoised: it is a constant constructor (all its values are the
   same immediate), it never writes anything, and re-answering [model_id ()] is free.

   Every memo entry is tagged with the writer's level at the moment it was created
   (docs/PROOF-FORMAT.md section 5: [w] wipes every constraint at or above a level).
   [wipe_level] drops the matching memo entries in the same call that wipes the writer,
   so the two stay in lockstep -- a stale memo entry pointing at an id the proof no
   longer contains would otherwise let a later [Cut] silently cite a deleted id. *)

module Lit = Baguette_proof.Lit
module Opb = Baguette_proof.Opb
module Writer = Baguette_proof.Writer
module Pol = Baguette_proof.Writer.Pol
module Encoding = Baguette_proof.Encoding

type memo_entry = { cid : Writer.cid; level : int }

type ctx = {
  writer : Writer.t;
  encoding : Encoding.t;
  model_id : unit -> Writer.cid;
  memo : (Explanation.t * memo_entry) list ref;
      (* Boxed behind a ref so [for_constraint]'s record copy shares it rather than
         forking it: only [model_id] is meant to differ between views of the same
         underlying proof state. *)
}

let create ~writer ~encoding ~model_id = { writer; encoding; model_id; memo = ref [] }

(* A view of [ctx] with a different answer to "what is the current model constraint",
   sharing the writer, encoding and memo. Use this when moving from justifying one
   posted constraint's prunings to another's. *)
let for_constraint ctx model_id = { ctx with model_id }

let find_memo ctx (e : Explanation.t) =
  let rec go = function
    | [] -> None
    | (k, m) :: rest -> if k == e then Some m else go rest
  in
  go !(ctx.memo)

let remember ctx (e : Explanation.t) (cid : Writer.cid) : Writer.cid =
  let level = Writer.current_level ctx.writer in
  ctx.memo := (e, { cid; level }) :: !(ctx.memo);
  cid

(* Backtracking: wipe the writer's level and drop the memo entries it invalidated, in
   one call, so the two structures cannot drift apart. Always call this instead of
   [Writer.wipe_level] directly when a [ctx] is in play. *)
let wipe_level ctx level =
  Writer.wipe_level ctx.writer level;
  ctx.memo := List.filter (fun (_, (m : memo_entry)) -> m.level < level) !(ctx.memo)

let validate_lits ctx lits =
  List.iter
    (fun (l : Lit.t) ->
      let owner = Lit.owner l.Lit.v in
      if not (Encoding.is_declared ctx.encoding owner) then
        invalid_arg
          (Printf.sprintf
             "Justify: literal %s refers to variable %s not declared in this encoding"
             (Lit.to_string l) owner))
    lits

(* Run [thunk] and memoise its result under [e]'s identity, unless it is already
   memoised. *)
let memoized ctx (e : Explanation.t) (thunk : unit -> Writer.cid) : Writer.cid =
  match find_memo ctx e with Some m -> m.cid | None -> remember ctx e (thunk ())

(* [Clause lits] -- rup, not pol.

   A [pol] step is a cutting-planes derivation: its content is *computed* from the ids
   and axioms named in its reverse-Polish expression, so emitting one requires knowing
   which existing constraints combine, by which coefficients, into the target. A
   [Clause] carries none of that: it is a bare list of literals that some propagator
   has already determined imply the pruning (a Hall-set argument, a direct-encoding
   disequality, ...), with no record of *how*. There is nothing for a cutting-planes
   expression to name. [rup] is the only rule in the vocabulary that accepts a bare
   target and searches for its own justification, so it is the only one that fits;
   docs/PROOF-FORMAT.md section 4 makes the same call for [int_ne] and [bool_clause]. *)
let emit_clause ctx lits =
  validate_lits ctx lits;
  Writer.rup_clause ctx.writer
    ~origin:
      (Printf.sprintf "clause(%s)" (String.concat " " (List.map Lit.to_string lits)))
    lits

(* [Linear (terms, rhs)] -- rup of exactly the constraint it states. Not [pol]; see
   D-0009 (docs/DECISIONS.md) for the full story, summarised here because
   docs/PROOF-FORMAT.md section 2 requires a propagator (and by extension, its bridge)
   that can only manage [rup] to say why in its own header.

   The earlier version of this function ignored [terms] and [rhs] entirely and emitted
   [pol <model_id>], restating the model constraint. That was wrong: [Explanation.Linear]
   is used by propagators (see [lib/core/prop/linear.ml]'s [int_lin_le]) to carry a
   restatement of *bound facts*, e.g. "the order-encoding unit literals witnessing the
   current bounds of the other variables" -- a completely different constraint from the
   model row, and the old code silently discarded it.

   The tempting fix -- render [terms >= rhs] as [pol], citing whatever established each
   literal -- does not work, because a [pol] expression cannot state that a literal
   *holds*: a bare literal in one is the trivial axiom [lit >= 0] (true for 0 or 1
   alike), not an assertion that it is 1. Checked directly against veripb 2.2.2:

     f 1                  * model: 1 x1 >= 1
     pol x2
     rup 1 x2 >= 1 ;      * Failed to show '1 x2 >= 1' by reverse unit propagation

   So a bound fact can only be cited by the id of a constraint that already establishes
   it (a decision or an earlier pruning search has logged, per D-0008's levels) -- never
   by naming its literal inside a [pol] expression. [Explanation.t] cannot carry that id
   (D-0003 is still open on whether it ever will), so the only honest rendering today is
   [rup]: state [terms >= rhs] outright and let the checker's own unit-propagation search
   find the already-logged facts that make it true. This is faithful to what the
   explanation claims, unlike the old [pol <model_id>], at the cost of being exactly the
   "checker searches" case docs/PROOF-FORMAT.md section 2 says to avoid when a [pol] is
   available -- it is not available here. *)
let emit_linear ctx terms rhs =
  validate_lits ctx (List.map snd terms);
  Writer.rup ctx.writer
    ~origin:(Printf.sprintf "linear: %s" (Opb.constr_to_string (Opb.ge terms rhs)))
    (Opb.ge terms rhs)

(* [Cut (e1, e2, c1, c2)] -- recurse on both reasons, then combine: c1 * e1 + c2 * e2.

   [Pol.mul] rejects a multiplier below 1, so [c1] and [c2] must be positive; this is
   the same restriction cutting planes always has (a "combination" with a non-positive
   multiplier is not a sound PB addition step). There is no negative-coefficient escape
   hatch here on purpose -- a caller wanting to subtract a reason should be weakening or
   negating literals inside the reason itself, not asking [Cut] to do it, since [Cut]'s
   coefficients are exactly what get handed to [Pol.mul]. *)
let emit_cut ~emit ctx e1 e2 c1 c2 =
  if c1 < 1 || c2 < 1 then
    invalid_arg
      (Printf.sprintf "Justify.emit: Cut coefficients must be >= 1, got (%d, %d)" c1 c2);
  let id1 = emit ctx e1 in
  let id2 = emit ctx e2 in
  Writer.pol ctx.writer
    ~origin:(Printf.sprintf "cut(%d*%d + %d*%d)" c1 id1 c2 id2)
    Pol.(add (mul (id id1) c1) (mul (id id2) c2))

(* [Combine (summands, divisor)] -- docs/DECISIONS.md D-0013: the "weaken, divide, add"
   derivation. One [pol] step: every summand's [Pol.t] fragment added left to right,
   then (unless [divisor = 1]) divided.

   A [Term (c, e)] summand recurses through [emit] exactly as [Cut]'s operands do --
   the recursion can legitimately land on an explanation another propagator instance
   built (its own base a [Model_row] naming *that* instance's row, not this one),
   which is exactly why [Model_row] exists (see explanation.ml's header): the id it
   cites is unambiguous regardless of which [ctx] is doing the recursing.

   A [Weaken lits] summand emits no rule and consumes no id: each [(c, l)] becomes
   [Pol.mul (Pol.axiom l) c], folded together with [Pol.add]. This is the one place a
   bare literal is deliberately allowed into a [pol] expression as the *trivial*
   axiom [l >= 0] (D-0009) -- never to assert [l] holds, only to cancel a term whose
   variable is still sitting at its declared bound. [emit_summand] therefore has two
   return shapes (mint an id vs. build a fragment directly); folding both into one
   [Pol.t] before the single [Writer.pol] call is what keeps the whole [Combine] to
   exactly one proof line, matching every step of D-0013's worked example. *)
let emit_summand ~emit ctx = function
  | Explanation.Term (c, e) ->
      if c < 1 then
        invalid_arg
          (Printf.sprintf "Justify.emit: Combine term coefficient must be >= 1, got %d" c);
      let id = emit ctx e in
      Pol.mul (Pol.id id) c
  | Explanation.Weaken lits ->
      (match lits with
      | [] -> invalid_arg "Justify.emit: Combine's Weaken summand must be non-empty"
      | _ -> ());
      validate_lits ctx (List.map snd lits);
      List.fold_left
        (fun acc (c, l) ->
          if c < 1 then
            invalid_arg
              (Printf.sprintf
                 "Justify.emit: Weaken axiom coefficient must be >= 1, got %d" c);
          Pol.add acc (Pol.mul (Pol.axiom l) c))
        (let c0, l0 = List.hd lits in
         Pol.mul (Pol.axiom l0) c0)
        (List.tl lits)

let emit_combine ~emit ctx summands divisor =
  (match summands with
  | [] -> invalid_arg "Justify.emit: Combine must have at least one summand"
  | _ -> ());
  let expr =
    List.fold_left
      (fun acc s -> Pol.add acc (emit_summand ~emit ctx s))
      (emit_summand ~emit ctx (List.hd summands))
      (List.tl summands)
  in
  let expr = if divisor <= 1 then expr else Pol.div expr divisor in
  Writer.pol ctx.writer
    ~origin:(Printf.sprintf "combine(%d summand(s), / %d)" (List.length summands) divisor)
    expr

(* [emit ctx e] renders [e] into proof rules through [Writer] and returns the id of the
   resulting constraint.

   - [Trivial] costs nothing: it returns [ctx.model_id ()] directly, no rule emitted.
   - [Model_row id] costs nothing either: [id] is already the constraint's id, no
     lookup and no rule (see explanation.ml's header on why this differs from
     [Trivial]).
   - Every other constructor is memoised on [e]'s physical identity (see the module
     header) before doing any work, so asking for the same explanation twice is free
     the second time.
   - [Deferred] is forced -- never call its thunk directly, [Explanation.force] is what
     memoises it -- and the result is recursed on. Forcing happens *inside* the memo
     lookup for the [Deferred] node itself, so a [Deferred] demanded twice neither
     forces its thunk twice (that guarantee is [Explanation.force]'s) nor re-emits the
     inner explanation's rule twice (that guarantee is this memo). *)
let rec emit ctx (e : Explanation.t) : Writer.cid =
  match e with
  | Explanation.Trivial -> ctx.model_id ()
  | Explanation.Model_row id -> id
  | Explanation.Clause lits -> memoized ctx e (fun () -> emit_clause ctx lits)
  | Explanation.Linear (terms, rhs) ->
      memoized ctx e (fun () -> emit_linear ctx terms rhs)
  | Explanation.Cut (e1, e2, c1, c2) ->
      memoized ctx e (fun () -> emit_cut ~emit ctx e1 e2 c1 c2)
  | Explanation.Combine (summands, divisor) ->
      memoized ctx e (fun () -> emit_combine ~emit ctx summands divisor)
  | Explanation.Deferred _ -> memoized ctx e (fun () -> emit ctx (Explanation.force e))
