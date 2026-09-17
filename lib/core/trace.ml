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

   where <claim> is what the pruning established and the <fact_i> are the bound facts
   the propagator actually read ([Store.entry]'s [facts]; for [int_lin_le] that is
   lib/core/prop/linear.ml's [facts_of_snaps]). Read as a clause it says "fact_1 and
   ... and fact_n imply claim", which is a genuine consequence of that one model row --
   so **no decision ever appears in a trace line**, and every line is globally valid on
   its own. The decisions appear in exactly one place, the nogood, which is now RUP
   because each of these lines is one unit propagation away from the next.

   <claim> is a *clause*, not a literal, and both halves of that sentence earn their
   keep (M1-T56, M1-T57):

   - a bound move claims one order literal, as above;
   - an interior hole claims the two of "x <> v", `x <= v-1 \/ x >= v+1`. That is
     [Encoding.ne_clause_lits], which docs/PROOF-FORMAT.md section 4 already names as
     [int_ne]'s justification -- this module simply never wrote it. Only a claim that
     has to be a *single* literal forces the direct encoding (D-0019 point 3), and a
     trace line's claim never had to be one;
   - a bound the settle strengthened past a hole claims the recorded bound and cites
     the hole's facts as well as the propagator's, so the line is RUP against the
     hole's own line. That one line is therefore **not** a consequence of a single
     model row, and it is the only kind here that is not. It is still decision-free and
     still globally valid; what it needs from the database is a line this module wrote
     itself, earlier, for an earlier trail entry.

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

   - **A hole's line and a settle's line are one mechanism, in that order.** The holes
     a settle walks over are values removed by *earlier* trail entries, and [emit] walks
     the trail oldest first, so the hole's line is in the database before the line that
     rests on it. Before M1-T56 it was in the database only if something else happened
     to cite it -- M1-T44 made the root-conflict path do so, and nothing else did -- and
     the settle's line verified because the checker re-derived the hole from the .opb's
     big-M disequality rows by unit propagation. That works for [int_ne]'s rows and is
     not a property a trace line may rest on. See [line] and I-X9.

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

(* "x <> v" over the *order* encoding: x <= v-1 or x >= v+1. That is
   [Encoding.ne_clause_lits]'s clause, rebuilt here from the two [cond]s so the constant
   halves drop by the same code path as every other claim in this module -- a [Fails]
   half cannot be true and is dropped, a [Holds] half makes the whole clause a tautology
   and there is nothing to write down.

   M1-T56. An order literal cannot state a hole *on its own*, which is what the old
   comment here read as "a pure hole removal produces no line -- correct today (M1 is
   bounds-only)". It was not correct: [int_ne] has punched interior holes since M1-T9,
   and a two-literal clause states one perfectly well. Only a claim that has to be a
   single literal forces the direct encoding (D-0019 point 3), and a trace line's claim
   never had to be.

   A hole is strictly inside its own domain's bounds by construction -- [Domain.classify]
   reports a change as a [Bound] *or* a [Holes] and never both, because a removal at a
   bound settles and tightens that bound instead (I-D2) -- and a domain's bounds are
   inside the declared ones, so both halves are [Cond] for every hole M1 can punch. The
   other two cases are still handled rather than asserted, because "both halves fail"
   is the one that would quietly write the *empty* clause, i.e. an unconditional
   contradiction, which is the worst thing a trace line can say (compare I-P5). *)
let hole_clause encoding name v =
  match (Encoding.le encoding name (v - 1), Encoding.ge encoding name (v + 1)) with
  | Encoding.Holds, _ | _, Encoding.Holds -> None
  | below, above -> (
      match
        List.filter_map
          (function Encoding.Cond l -> Some l | _ -> None)
          [ below; above ]
      with
      | [] ->
          invalid_arg
            (Printf.sprintf "Trace: %s <> %d is unsatisfiable in the encoding" name v)
      | lits -> Some lits)

(* One line this module owes, before its facts are known.

   [claim] is the positive part of the clause: one literal for a bound move, the two of
   "x <> v" for a hole.

   [settled_over] is M1-T57. [Domain.set_lo]/[set_hi] do not stop where the propagator
   asks: [Domain.settle] walks the new bound past any hole it lands on, so [e.now]'s
   bound can be *strictly stronger* than the bound the propagator's facts derive, and
   the difference is exactly the holes walked over (D-0035). A line that claims [e.now]
   from those facts alone claims more than they justify. It is a [rup], so it fails
   loudly rather than silently -- and it has verified anyway, because the checker
   happened to re-derive each hole from the .opb's disequality rows by unit propagation,
   which is a property of [int_ne]'s big-M rows and not something a trace line may rest
   on. I-X9 says what to do instead: the reasons of the holes the settle walked over are
   part of the justification and are cited with it. [settled_over] carries those hole
   values; [settle_facts] turns them into the facts that go in this line's tail, which
   makes the line RUP against the *hole's own trace line* (M1-T56, written first because
   the hole is earlier on the trail) rather than against a coincidence.

   The set is the contiguous run of holes immediately below (or above) the new bound.
   That is an over-approximation of what the settle walked over by at most the holes the
   propagator's asked-for bound had already cleared, and it is empty exactly when no
   settle happened -- so a pruning that landed on a member of the domain writes the byte
   for byte identical line it wrote before. Extra facts only *weaken* the clause, so
   they can cost precision and never soundness; the alternative is the propagator's
   asked-for bound on the trail entry, which is not additive to [Store.entry] and is a
   decision record, not an edit. *)
type line = { claim : Lit.t list; settled_over : int list }

(* The holes of [old] in the contiguous run immediately below [bound], ascending. Every
   member of [old] below [bound] is below this run, so the bound the propagator asked
   for lies inside it or at [bound]. *)
let holes_below old bound =
  let rec go acc v =
    if v >= Domain.lo old && Domain.is_hole old v then go (v :: acc) (v - 1) else acc
  in
  go [] (bound - 1)

(* The same run immediately above [bound], ascending. *)
let holes_above old bound =
  let rec go acc v =
    if v <= Domain.hi old && Domain.is_hole old v then go (v :: acc) (v + 1) else acc
  in
  List.rev (go [] (bound + 1))

(* Both bounds are checked: [Domain.set_lo]/[set_hi] move one, but [Domain.fix] moves
   both, and a propagator doing that deserves two lines rather than one silently dropped
   half. [Domain.classify] is asked rather than the bounds compared by hand because it
   is the module that owns the [Bound]-or-[Holes] disjointness this function relies on,
   and because it is what already recovers the interior holes of a [Holes] change. *)
let lines encoding (e : Store.entry) name =
  match Domain.classify ~old:e.Store.old ~now:e.Store.now with
  | Domain.NoChange -> []
  | Domain.Bound { lo; hi } ->
      let bound_line ~what ~cond ~settled_over =
        Option.map
          (fun l -> { claim = [ l ]; settled_over })
          (claim_of_cond ~what ~name cond)
      in
      let lo_line =
        Option.bind lo (fun b ->
            bound_line ~what:"the new lower bound" ~cond:(Encoding.ge encoding name b)
              ~settled_over:(holes_below e.Store.old b))
      in
      let hi_line =
        Option.bind hi (fun b ->
            bound_line ~what:"the new upper bound" ~cond:(Encoding.le encoding name b)
              ~settled_over:(holes_above e.Store.old b))
      in
      List.filter_map Fun.id [ lo_line; hi_line ]
  | Domain.Holes vs ->
      List.filter_map
        (fun v ->
          Option.map
            (fun claim -> { claim; settled_over = [] })
            (hole_clause encoding name v))
        vs

(* Just the claim clauses, which is what a test wanting to check one line in isolation
   needs (test/unit/test_prop.ml drives every propagator's trace line through this and
   [emit_line]). The facts a settle adds come from the trail, not from the entry, so they
   are [emit]'s business and not visible here -- which is also why this is not the
   function [emit] calls. *)
let claims encoding e name = List.map (fun l -> l.claim) (lines encoding e name)

(* ------------------------------------------------------------------- lines *)

let clause_of ~claim ~facts = claim @ List.map Lit.negate facts

let emit_line (ctx : Justify.ctx) ~origin ~claim ~facts =
  Justify.emit_rup_clause ctx ~origin (clause_of ~claim ~facts)

(* The trail entry that took [v] out of [var]'s domain, looking back from trail position
   [before]. At most one live entry can have done it -- a removed value stays removed
   until the backtrack that pops the entry that removed it -- so this finds the reason
   of a hole that is still there, and finds it at the first hit.

   [None] means a hole with no trail entry behind it, which within M1 means a *declared*
   domain with a gap ([Domain.of_list], for `var {1,3,5}: x`, which the FlatZinc subset
   of docs/SPEC.md 2.1 does not admit). It cites nothing rather than raising: the line is
   then exactly as strong as the one this module wrote before M1-T57, so an encoding that
   grows declared holes degrades to the old behaviour instead of aborting the solve --
   and the .opb would have to state such a hole as a row anyway, which is what the
   checker would then use. *)
let remover store ~before ~var v =
  let rec go i =
    if i < 0 then None
    else
      let e = Store.trail_entry store i in
      if
        Var.equal e.Store.var var
        && Domain.mem e.Store.old v
        && not (Domain.mem e.Store.now v)
      then Some e
      else go (i - 1)
  in
  go (before - 1)

(* Append a fact if it is not already in the tail. The propagator's own facts keep their
   order and are never rewritten, so every line for a pruning that did not settle comes
   out unchanged; only the hole facts are appended, and a hole whose fact the propagator
   already read is not stated twice. *)
let add_fact acc l = if List.exists (Lit.equal l) acc then acc else acc @ [ l ]

let settle_facts store ~before ~var holes base =
  List.fold_left
    (fun acc v ->
      match remover store ~before ~var v with
      | None -> acc
      | Some e -> List.fold_left add_fact acc (e.Store.facts ()))
    base holes

(* Write every line the trail owes, oldest first, and leave the writer on the level it
   was on. [Search] emits the nogood straight after, at the branch's own level, so this
   must not move it -- the whole ordering D-0018 point 4 exists to protect
   ([set_level]/[w] are a stack the solver mirrors, and a trace that left the writer
   somewhere else would wipe the wrong constraints).

   Oldest first is load-bearing for more than readability now: a settle's line is RUP
   against the lines of the holes it walked over (see [line]), and those holes are
   earlier trail entries, so their lines are already in the database when the settle's
   line is checked. *)
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
      (* [claims] first: a change that claims nothing writes nothing and must not force
         the [facts] thunk to find that out. "Lazy where it is expensive" cuts here too.
         Since M1-T56 an interior hole does get a claim, so the cases this skips are the
         ones where the whole change is invisible to the encoding -- a bound that was
         already the declared one. *)
      match lines ctx.Justify.encoding e name with
      | [] -> ()
      | cs ->
          let facts = e.Store.facts () in
          let level = Store.level_of_index store i in
          List.iter
            (fun { claim; settled_over } ->
              let facts =
                settle_facts store ~before:i ~var:e.Store.var settled_over facts
              in
              if !at <> level then (
                Writer.set_level ctx.Justify.writer level;
                at := level);
              let origin =
                Printf.sprintf "trace: %s from %d fact(s)%s"
                  (String.concat " \\/ " (List.map Lit.to_string claim))
                  (List.length facts)
                  (match settled_over with
                  | [] -> ""
                  | vs ->
                      Printf.sprintf ", settled over %s"
                        (String.concat "," (List.map string_of_int vs)))
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
