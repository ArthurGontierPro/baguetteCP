(* trace.ml: writing down what a branch learned, so its nogood is plain RUP.
   docs/DECISIONS.md D-0018, task M1-T13.

   ---------------------------------------------------------------------------
   The one-paragraph version
   ---------------------------------------------------------------------------

   [Search] used to log nothing inside a branch and, when the branch failed, assert the
   nogood -- "not all of these decisions hold" -- as a [rup]. veripb rejected it. Three
   decision records (D-0012, D-0014, D-0017) concluded the nogood was unreachable.
   D-0018 records that it is not: the nogood IS plain [rup], and what was missing is
   everything the checker was supposed to unit-propagate *along*. When veripb checks
   [rup c] it negates [c] -- here, asserting every decision -- and then unit-propagates
   over the constraint database, one single constraint at a time. Our database contained
   only the model rows, so it was being asked to re-derive a multi-row bounds fixpoint in
   one step, which PB unit propagation cannot do. It never had to be: the solver already
   knows every step of that fixpoint, and writing each step down as its own line turns
   the re-derivation into a replay.

   So this module walks the trail and emits, per pruning,

       rup 1 <claim> 1 ~<fact_1> 1 ~<fact_2> ... >= 1 ;

   where <claim> is the order literal the pruning established and the <fact_i> are the
   bound facts the propagator actually read ([Store.entry]'s [facts]; for [int_lin_le]
   that is lib/core/prop/linear.ml's [facts_of_snaps]). Read as a clause it says
   "fact_1 and ... and fact_n imply claim", which is a genuine consequence of that one
   model row -- so **no decision ever appears in a trace line**, and every line is
   globally valid on its own. The decisions appear in exactly one place, the nogood,
   which is now RUP because each of these lines is one unit propagation away from the
   next.

   ---------------------------------------------------------------------------
   Lazy, not eager -- and why that is sound here specifically
   ---------------------------------------------------------------------------

   The Glasgow Constraint Solver logs each inference at the moment it is made. We do not:
   nothing is written on a search path that succeeds, and a branch writes its whole trace
   at the moment it fails, by walking the trail. D-0018 permits this for a reason that is
   a property of this codebase and not of the technique, and that has to be preserved:
   [linear.ml]'s [snapshot_source] decides *at push time* which trail entry witnesses
   each bound it read, so a reason forced later still renders the derivation as of the
   moment it was made. [Store.entry]'s [facts] thunk closes over that snapshot, never
   over the live store. A propagator whose thunk reads [Store.get] at force time would
   silently break this -- it would render a *later* bound as the reason for an *earlier*
   pruning -- and the symptom would be a rejected line somewhere else entirely.

   ---------------------------------------------------------------------------
   What gets a line, at which proof level, and who deletes it
   ---------------------------------------------------------------------------

   - **Decisions get no line.** A decision is not implied by anything (search.ml's header
     is right about that, and D-0009 is why [rup] and [pol] both refuse it). The entry
     that opens a level *is* the decision, by construction of [Search.branch], which is
     what [Store.is_level_start] tests.

   - **Level-0 prunings get a line too**, although no decision is active when they are
     made. D-0018 point 1 says "under at least one decision"; that is not sufficient, and
     the reason is worth stating because it is not obvious. When the checker verifies a
     nogood it starts from *nothing* -- it does not inherit the root fixpoint the solver
     reached before branching. Any root-derived bound a branch's trace cites as a fact
     therefore has to be derivable too. In chain_sat, `b >= 1` is a root pruning whose
     line is `rup 1 b_ge_1 >= 1 ;` (its own facts are all still declared bounds, so the
     clause is a unit): a real, checkable consequence of one row, and without it the
     lines above it have a fact the checker cannot reach.

   - **A line is tagged with the decision level of the trail entry that produced it**, not
     with whatever level the writer happens to be on. That is invariant I-X3 ("proof state
     mirrors solver state") taken literally: a pruning and its line have the same
     lifetime, so [Search]'s existing one-[w]-per-backtrack retires exactly the lines
     whose prunings were undone, and a level-1 line survives the wipe of level 2 and is
     still there for level 1's second branch. Level-0 lines are never wiped by anything;
     [permanent_ids] hands them to [Search.solve], which deletes them before [conclusion]
     so invariant I-X2 still holds.

   - **A line is written once per pruning, not once per failing branch.** [n_done] is how
     far down the trail the trace has been written. After a backtrack the trail is
     shorter and the slots are refilled with *different* entries, so [resync] finds the
     longest common prefix by physical identity rather than trusting a length -- there is
     nothing for [Search] to remember to call, and no way for a stale watermark to make
     this module skip a pruning it has not actually written down. That is the whole
     bookkeeping. *)

module Lit = Baguette_proof.Lit
module Writer = Baguette_proof.Writer
module Encoding = Baguette_proof.Encoding

type t = {
  (* The trail entries already given their line, by position. Physical identity is the
     key: see [resync]. *)
  mutable done_ : Store.entry array;
  mutable n_done : int;
  (* Lines written at level 0, which no [w] will ever retire (I-X2). *)
  mutable permanent : Writer.cid list;
  (* Every line this module has written, newest first, wiped ones included. Nothing in
     the solver reads it; it is here so a test can say *which* rules in an emitted proof
     are trace lines and check each one on its own against the .opb -- which is the only
     way to demonstrate the property this whole module exists for, that a trace line is
     a decision-free consequence of the model and needs nothing else in the database.
     See test/unit/test_trace.ml. *)
  mutable ids_rev : Writer.cid list;
}

let create () =
  { done_ = Array.make 64 Store.dummy_entry; n_done = 0; permanent = []; ids_rev = [] }

let permanent_ids t = List.rev t.permanent
let emitted_ids t = List.rev t.ids_rev

let record t ~level cid =
  t.ids_rev <- cid :: t.ids_rev;
  if level = 0 then t.permanent <- cid :: t.permanent

let remember t i (e : Store.entry) =
  if i >= Array.length t.done_ then (
    let bigger = Array.make (Stdlib.max 64 (2 * (i + 1))) Store.dummy_entry in
    Array.blit t.done_ 0 bigger 0 (Array.length t.done_);
    t.done_ <- bigger);
  t.done_.(i) <- e;
  t.n_done <- Stdlib.max t.n_done (i + 1)

(* Drop back to the longest prefix of the trail this module has actually written lines
   for, comparing entries by physical identity. A backtrack shortens the trail and the
   next branch refills those positions with new entries; the lines for the old ones were
   retired by the same [w] that the backtrack triggered. *)
let resync t store =
  let n = Stdlib.min t.n_done (Store.trail_length store) in
  let rec go i =
    if i >= n then n
    else if Store.trail_entry store i == t.done_.(i) then go (i + 1)
    else i
  in
  t.n_done <- go 0

(* ------------------------------------------------------------------ claims *)

(* The order literal a pruning established, per bound. [Encoding] is asked rather than
   [Lit] directly so that a bound which is the variable's *declared* one comes back as
   [Holds] -- the encoding's constant true, docs/PROOF-FORMAT.md section 3 -- and is
   skipped instead of being claimed with a literal that does not exist. [Fails] would
   mean the store holds a domain the encoding says is empty, i.e. I-D1 is broken
   somewhere upstream; say so rather than write a line about it. *)
let claim_of_cond ~what ~name (c : Encoding.cond) =
  match c with
  | Encoding.Cond l -> Some l
  | Encoding.Holds -> None
  | Encoding.Fails ->
      invalid_arg
        (Printf.sprintf "Trace: %s of %s is outside the encoding's declared domain" what
           name)

(* Both bounds are checked: [Domain.set_lo]/[set_hi] move one, but [Domain.fix] moves
   both, and a propagator doing that deserves two lines rather than one silently dropped
   half. A pure hole removal moves neither and produces no line -- correct today (M1 is
   bounds-only, docs/SPEC.md 3.2) and *not* correct for a future domain-consistent
   propagator, which will need a claim in the direct encoding instead; that is M1-T9's
   and M4's business, and this returning [] is where it will show up. *)
let claims encoding (e : Store.entry) name =
  let lo_claim =
    if Domain.lo e.now > Domain.lo e.old then
      claim_of_cond ~what:"the new lower bound" ~name
        (Encoding.ge encoding name (Domain.lo e.now))
    else None
  in
  let hi_claim =
    if Domain.hi e.now < Domain.hi e.old then
      claim_of_cond ~what:"the new upper bound" ~name
        (Encoding.le encoding name (Domain.hi e.now))
    else None
  in
  List.filter_map Fun.id [ lo_claim; hi_claim ]

(* ------------------------------------------------------------------- lines *)

let clause_of ~claim ~facts = claim :: List.map Lit.negate facts

let emit_line (ctx : Justify.ctx) ~origin ~claim ~facts =
  Justify.emit_rup_clause ctx ~origin (clause_of ~claim ~facts)

(* Write every line the trail owes, oldest first, and leave the writer on the level it
   was on. [Search] emits the nogood straight after, at the branch's own level, so this
   must not move it -- the whole ordering D-0018 point 4 exists to protect
   ([set_level]/[w] are a stack the solver mirrors, and a trace that left the writer
   somewhere else would wipe the wrong constraints). *)
let emit (ctx : Justify.ctx) t store =
  resync t store;
  let saved = Writer.current_level ctx.Justify.writer in
  let at = ref saved in
  let n = Store.trail_length store in
  for i = t.n_done to n - 1 do
    let e = Store.trail_entry store i in
    remember t i e;
    if not (Store.is_level_start store i) then
      let name = Store.name store e.Store.var in
      (* [claims] first: a change that moves no bound (a hole, which no M1 propagator
         punches) writes nothing and must not force the [facts] thunk to find that out.
         "Lazy where it is expensive" cuts here too. *)
      match claims ctx.Justify.encoding e name with
      | [] -> ()
      | cs ->
          let facts = e.Store.facts () in
          let level = Store.level_of_index store i in
          List.iter
            (fun claim ->
              if !at <> level then (
                Writer.set_level ctx.Justify.writer level;
                at := level);
              let origin =
                Printf.sprintf "trace: %s from %d fact(s)" (Lit.to_string claim)
                  (List.length facts)
              in
              record t ~level (emit_line ctx ~origin ~claim ~facts))
            cs
  done;
  if !at <> saved then Writer.set_level ctx.Justify.writer saved

(* D-0018 point 3: "a conflict under decisions logs its own reason line first, then the
   nogood". A conflict establishes no bound, so its line is the same clause with the
   claim omitted -- the empty sum over the negated facts, which is GCS's
   [ProofLogger::backtrack] shape applied to the propagator's own reason rather than to
   the guess list. [None] when the propagator did not record any: the line is then
   redundant for [int_lin_le] (a slack < 0 row is detected as violated by the checker's
   own unit propagation once the trace has assigned its bounds) and writing `>= 1 ;`
   over nothing would be a claim of unconditional contradiction, which is false. *)
let conflict_line (ctx : Justify.ctx) t store =
  match Store.take_conflict_facts store with
  | None -> None
  | Some f -> (
      match f () with
      | [] -> None
      | facts ->
          let cid =
            Justify.emit_rup_clause ctx
              ~origin:
                (Printf.sprintf "trace: conflict from %d fact(s)" (List.length facts))
              (List.map Lit.negate facts)
          in
          record t ~level:(Writer.current_level ctx.Justify.writer) cid;
          Some cid)
