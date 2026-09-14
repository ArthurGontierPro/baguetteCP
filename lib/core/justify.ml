(* Justify: turn an [Explanation.t] into VeriPB proof rules and hand back the id of the
   resulting constraint.

   This lives in [core], not [proof] (docs/ARCHITECTURE.md section 1): the dependency
   direction is [core -> proof], so [proof] cannot see [Explanation] and the bridge has
   to sit on the [core] side of the line, calling down into [Baguette_proof.Writer].

   docs/PROOF-FORMAT.md section 2's rule is "prefer [pol] over [rup] everywhere [pol]
   states the reasoning; [rup] makes the checker search" -- every constructor below
   follows it except [Clause], which cannot (see the comment there).

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
  match find_memo ctx e with
  | Some m -> m.cid
  | None -> remember ctx e (thunk ())

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
    ~origin:(Printf.sprintf "clause(%s)" (String.concat " " (List.map Lit.to_string lits)))
    lits

(* [Linear (terms, rhs)] -- pol, citing the current model constraint.

   Per the doc comment on [Explanation.Linear], this constructor "renders to pol over
   the model constraint": its contract is that [(terms, rhs)] state exactly the PB
   constraint [ctx.model_id ()] already carries (that promise is the propagator's to
   keep -- Justify has no way to see inside an existing id to check it, since [Writer]
   deliberately does not retain constraint bodies, only ids). Given that, the derivation
   is the simplest one that is still real cutting planes rather than assertion: [pol
   <model_id>], which restates the model constraint under a fresh id. A fresh id is the
   point of not just returning [ctx.model_id ()] the way [Trivial] does: the caller gets
   an id it *owns* and can feed into a later [Cut] or delete independently of the model
   constraint (which nobody owns -- see [Writer.model_ids]). *)
let emit_linear ctx terms rhs =
  validate_lits ctx (List.map snd terms);
  Writer.pol ctx.writer
    ~origin:(Printf.sprintf "linear(... >= %d) over model constraint" rhs)
    (Pol.id (ctx.model_id ()))

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

(* [emit ctx e] renders [e] into proof rules through [Writer] and returns the id of the
   resulting constraint.

   - [Trivial] costs nothing: it returns [ctx.model_id ()] directly, no rule emitted.
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
  | Explanation.Clause lits -> memoized ctx e (fun () -> emit_clause ctx lits)
  | Explanation.Linear (terms, rhs) ->
      memoized ctx e (fun () -> emit_linear ctx terms rhs)
  | Explanation.Cut (e1, e2, c1, c2) ->
      memoized ctx e (fun () -> emit_cut ~emit ctx e1 e2 c1 c2)
  | Explanation.Deferred _ ->
      memoized ctx e (fun () -> emit ctx (Explanation.force e))
