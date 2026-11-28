(* trace.ml: writing down what a branch learned, so its nogood is plain RUP.
   docs/DECISIONS.md D-0018 (a branch nogood is RUP over the branch's own logged trace),
   task M1-T13 (justifying a conflict reached under decisions).

   ---------------------------------------------------------------------------
   The one-paragraph version
   ---------------------------------------------------------------------------

   When a branch fails, this module writes one proof line per pruning the branch made,
   and the nogood "not all of these decisions hold" then follows by plain [rup]. When
   veripb checks [rup c] it negates [c] (here, asserting every decision) and then
   unit-propagates over the constraint database, one single constraint at a time. A
   database holding only the model rows asks it to re-derive a multi-row bounds fixpoint
   in one step, which PB unit propagation cannot do. The solver already knows every step
   of that fixpoint, and writing each step down as its own line turns the re-derivation
   into a replay.

   History: [Search] used to log nothing inside a branch and assert the nogood as a [rup]
   when the branch failed. veripb rejected it, and three decision records concluded the
   nogood was unreachable: D-0012 (not RUP from the model rows alone), D-0014
   (decision-free lemmas strengthen it but do not close it) and D-0017 (SAT runs fail the
   same way). D-0018 found that the nogood IS plain [rup], and that what was missing was
   everything the checker was supposed to unit-propagate *along*.

   So this module walks the trail and emits, per pruning,

       rup 1 <claim> 1 ~<fact_1> 1 ~<fact_2> ... >= 1 ;

   where <claim> is what the pruning established and the <fact_i> are the bound facts
   the propagator actually read ([Store.entry]'s [reason], materialised by [Reason.lits],
   the ONE place a reason becomes literals since D-0026 made reasons declarative data).
   Read as a clause it says "fact_1 and ... and fact_n imply claim", which is a genuine
   consequence of that one model row, so **no decision ever appears in a trace line**,
   and every line is globally valid. The decisions appear in exactly one place, the
   nogood, which is now RUP because each of these lines is one unit propagation away from
   the next. A line is checked RUP in sequence, against the lines before it, and not
   standalone (D-0039 retired the standalone property).

   <claim> is a *clause*, not a literal, and both halves of that sentence earn their keep
   (M1-T56, which gave a hole removal its line, and M1-T57, which made a settled bound
   cite its holes):

   - a bound move claims one order literal, as above;
   - an interior hole claims the two of "x <> v", `x <= v-1 \/ x >= v+1`. That is
     [Encoding.ne_clause_lits], which docs/PROOF-FORMAT.md section 4 already names as
     [int_ne]'s justification. Only a claim that has to be a *single* literal forces the
     direct encoding (D-0019 point 3: a disequality needs the order encoding, not the
     direct one), and a trace line's claim never has to be one;
   - a bound the settle strengthened past a hole claims the recorded bound and cites the
     hole's facts as well as the propagator's, so the line is RUP against the hole's own
     line. That one line is therefore **not** a consequence of a single model row. A
     pruning that READ a hole is the second member of this case (M7-T13, D-0075: the
     second RUP defect, a propagator that reads a hole and states only bounds):
     `element` is DOMAIN consistent, so its rule 2 reads `dom(idx)` holes included, and
     it cites the hole-puncher's reason the same way, by the same argument and with the
     same I-S4 obligation (a cited hole line must outlive the line citing it). It is
     still decision-free and still globally valid; what it needs from the database is a
     line this module wrote itself, earlier, for an earlier trail entry.

   ---------------------------------------------------------------------------
   Lazy, not eager -- and why that is sound here specifically
   ---------------------------------------------------------------------------

   Nothing is written on a search path that succeeds, and a branch writes its whole trace
   at the moment it fails, by walking the trail. (The Glasgow Constraint Solver logs each
   inference at the moment it is made instead.) D-0018 permits this for a reason that is a
   property of this codebase and not of the technique, and that has to be preserved:
   [linear.ml]'s [snapshot_source] decides *at push time* which trail entry witnesses
   each bound it read, so a reason forced later still renders the derivation as of the
   moment it was made. [Store.entry]'s [reason] IS that snapshot; since M2-T8 (the
   propagator interface with declarative reasons) it is data rather than a thunk, so this
   half cannot read the live store even in principle (D-0026, and I-X6: a deferred
   explanation closes over a snapshot and never reads live store state). The
   justification half is still a thunk and still can: a propagator whose thunk reads
   [Store.get] at force time would render a *later* bound as the reason for an *earlier*
   pruning, and the symptom would be a rejected line somewhere else entirely.

   ---------------------------------------------------------------------------
   What gets a line, at which proof level, and who deletes it
   ---------------------------------------------------------------------------

   - **Decisions get no line.** A decision is not implied by anything (search.ml's header
     is right about that, and D-0009, under which a bound fact in a [pol] needs a
     constraint id and not a literal, is why [rup] and [pol] both refuse it). The entry
     that opens a level *is* the decision, by construction of [Search.branch], which is
     what [Store.is_level_start] tests.

   - **Level-0 prunings get a line too**, although no decision is active when they are
     made. D-0018 point 1 says "under at least one decision"; that is not sufficient, and
     the reason is worth stating because it is not obvious. When the checker verifies a
     nogood it starts from *nothing*: it does not inherit the root fixpoint the solver
     reached before branching. Any root-derived bound a branch's trace cites as a fact
     therefore has to be derivable too. In chain_sat, `b >= 1` is a root pruning whose
     line is `rup 1 b_ge_1 >= 1 ;` (its own facts are all still declared bounds, so the
     clause is a unit): a real, checkable consequence of one row, and without it the
     lines above it have a fact the checker cannot reach.

   - **A line is tagged with the decision level of the trail entry that produced it**, not
     with whatever level the writer happens to be on. That is invariant I-X3 ("proof state
     mirrors solver state") taken literally: a pruning and its line have the same
     lifetime, so the [Writer.wipe_level] [Search] calls at each backtrack retires exactly
     the lines whose prunings were undone, and a level-1 line survives the wipe of level 2
     and is still there for level 1's second branch. (VeriPB 3.0 has no `w` command that
     wipes a level; [Writer.wipe_level] imitates it with explicit deletions of the ids
     tagged at that level or above, D-0024.) Level-0 lines are never wiped by anything;
     [permanent_ids] hands them to [Search.solve], which deletes them before
     [conclusion], so invariant I-X2 (every id is deleted exactly once) still holds.

   - **A hole's line and a settle's line are one mechanism, in that order.** The holes
     a settle walks over are values removed by *earlier* trail entries, and [emit] walks
     the trail oldest first, so the hole's line is in the database before the line that
     rests on it. See [line] and I-X9 (an explanation justifies the bound as recorded on
     the trail, holes walked over included). Before M1-T56 the hole's line was in the
     database only if something else happened to cite it (M1-T44, a correct UNSAT answer
     the checker rejected, made the root-conflict path do so, and nothing else did), and
     the settle's line verified because the checker re-derived the hole from the .opb's
     big-M disequality rows by unit propagation. That works for [int_ne]'s rows and is
     not a property a trace line may rest on.

   - **A line is written once per pruning, not once per failing branch.** [n_done] is how
     far down the trail the trace has been written. After a backtrack the trail is
     shorter and the slots are refilled with *different* entries, so [resync] finds the
     longest common prefix by physical identity rather than trusting a length. There is
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
  (* Lines written at level 0, which no [Writer.wipe_level] will ever retire, so this
     module hands them to the end-of-search sweep (I-X2). *)
  mutable permanent : Writer.cid list;
  (* Every line this module has written, newest first, wiped ones included. Nothing in
     the solver reads it; it is here so a test can say *which* rules in an emitted proof
     are trace lines and check each one on its own against the .opb -- which is the only
     way to demonstrate the property this whole module exists for, that a trace line is
     a decision-free consequence of the model and needs nothing else in the database.
     See test/unit/test_trace.ml. Kept only by a trace made with [~history:true]. *)
  mutable ids_rev : Writer.cid list;
  (* Which lines this module wrote for each trail position, and for a hole line, which
     hole it claims. Parallel to [done_] and keyed the same way. It exists so that when a
     settle line cites a hole, this module can name the *id* of the hole's own line and
     not merely the facts on it -- which is what makes I-S4 checkable. See [citations]. *)
  mutable line_ids : written list array;
  (* The I-S4 record, newest first, under [~history:true]. See [citation] and
     [i_s4_violations]. *)
  mutable cites_rev : citation list;
  (* This module's low-water reader on the store it writes the trace of, registered by
     the first [resync] (see [resync]). From M11-complexity-T5, D-0145, the pass on trace,
     justification and proof writing, item J3 of D-0140's inventory of costs that grow
     with the run. *)
  mutable low_water : (Store.t * int) option;
  (* Whether [ids_rev] and [cites_rev] are kept. They are read by tests only, and kept
     they grow with every line of the run (a cons per trace line, a record per citation),
     which the major GC walks for as long as the run lasts. [create ~history:true] keeps
     them; [Search]'s own trace does not. (D-0145, D-0140 J4.) *)
  history : bool;
}

(* One "line A rests on line B" edge, with the two facts I-S4 is about, **measured at the
   moment of the citation** rather than recomputed afterwards.

   I-S4: "a trace line that cites a hole is supported only while that hole's own line is
   live, so the cited line must outlive the citing line." That is two obligations, and
   they fail in different ways, so they are recorded separately:

     [cited_live]   the cited line is on the page *now*. A settle line whose hole line
                    has already been retired is a [rup] against a database that no longer
                    contains what makes it true (D-0039: RUP in sequence, not standalone).
     [cited_level]  the cited line's level is at or below the citing line's, so the
                    [Writer.wipe_level] that retires the cited one retires the citing one
                    first or with it. This is the *outlives* half, and it is the half that
                    D-0039 point 1 and I-S4 both say is argued rather than measured. A
                    line citing across levels would break it first; M2-T3 (clause
                    learning) was expected to be that line, see [i_s4_verdict].

   [cited_live] is read from [Writer.is_live], which is maintained only under the audit
   (which the CLI turns on by default). [live_known] records whether it was, so a run with
   the audit off reports "not measured" rather than a false violation. The level half is
   always measured: [Writer] keeps no per-id level table this module may read, but the
   levels are exactly the ones this module chose for the two lines itself. *)
(* One line this module wrote, against the trail position it wrote it for. [w_hole] is
   the hole value for a hole line and [None] for a bound line; [w_level] is the level the
   line was filed at, which is the entry's level and not the writer's ambient one. *)
and written = { w_hole : int option; w_cid : Writer.cid; w_level : int }

and citation = {
  citing : Writer.cid;
  cited : Writer.cid;
  citing_level : int;
  cited_level : int;
  cited_live : bool;
  live_known : bool;
  hole : int; (* the hole value whose line is cited -- for the failure message *)
}

let create ?(history = false) () =
  {
    done_ = Array.make 64 Store.dummy_entry;
    n_done = 0;
    permanent = [];
    ids_rev = [];
    line_ids = Array.make 64 [];
    cites_rev = [];
    low_water = None;
    history;
  }

let permanent_ids t = List.rev t.permanent

(* A trace made without [~history:true] has no record to give, and says so rather than
   answering [[]], which a test would read as "no line was written". *)
let need_history what t =
  if not t.history then
    invalid_arg
      (Printf.sprintf
         "Trace.%s: this trace keeps no history; make it with Trace.create ~history:true \
          (M11-complexity-T5)"
         what)

let emitted_ids t =
  need_history "emitted_ids" t;
  List.rev t.ids_rev

(* The I-S4 edges, oldest first. *)
let citations t =
  need_history "citations" t;
  List.rev t.cites_rev

(* I-S4 on one edge: [None] if it holds, [Some message] naming which half broke.

   A pure function of the recorded edge, and public, because the two halves are not
   equally reachable and a gate that could only ask about a whole run could not say so.
   The *liveness* half is reachable today -- retire a hole line and then let a settle
   cite it, which is what test/unit/test_trace.ml's break lane does. The *level* half is
   not: [emit] files a line at the level of the trail entry that produced it, and a
   settle can only walk over holes that already exist, which are at levels at or below
   its own. That is exactly I-S4's argument, and a line citing across levels would
   invalidate it, so the level branch is checked against a constructed edge rather than
   left untested until such a line arrives. M2-T3's learned clauses were expected to be
   the first; as built (lib/core/learned.ml) a learned constraint is written at level 0
   outside this module and records no edge here. *)
let i_s4_verdict c =
  if c.live_known && not c.cited_live then
    Some
      (Printf.sprintf
         "I-S4: line @c%d (level %d) cites @c%d for the hole <> %d, and @c%d is already \
          retired"
         c.citing c.citing_level c.cited c.hole c.cited)
  else if c.cited_level > c.citing_level then
    Some
      (Printf.sprintf
         "I-S4: line @c%d (level %d) cites @c%d (level %d) for the hole <> %d, so `w %d` \
          retires the cited line while the citing line survives"
         c.citing c.citing_level c.cited c.cited_level c.hole c.cited_level)
  else None

(* I-S4 over a whole run: one message per edge that broke it, empty when every cited line
   was live and no deeper than its citer. *)
let i_s4_violations t = List.filter_map i_s4_verdict (citations t)

let record t ~level cid =
  if t.history then t.ids_rev <- cid :: t.ids_rev;
  if level = 0 then t.permanent <- cid :: t.permanent

let remember t i (e : Store.entry) =
  if i >= Array.length t.done_ then (
    let n = Stdlib.max 64 (2 * (i + 1)) in
    let bigger = Array.make n Store.dummy_entry in
    Array.blit t.done_ 0 bigger 0 (Array.length t.done_);
    t.done_ <- bigger;
    let bigger_ids = Array.make n [] in
    Array.blit t.line_ids 0 bigger_ids 0 (Array.length t.line_ids);
    t.line_ids <- bigger_ids);
  t.done_.(i) <- e;
  (* [emit] calls this once per position it is about to write lines for, and only for
     positions at or past [n_done], so any ids recorded here before are from a branch a
     backtrack has since retired. Clear them rather than let a settle cite one. *)
  t.line_ids.(i) <- [];
  t.n_done <- Stdlib.max t.n_done (i + 1)

(* Drop back to the longest prefix of the trail this module has actually written lines
   for, comparing entries by physical identity. A backtrack shortens the trail and the
   next branch refills those positions with new entries; the lines for the old ones were
   retired by the same [Writer.wipe_level] that the backtrack triggered.

   The walk starts at the store's low-water mark for this module, not at position 0
   (D-0145, D-0140 J3). At the previous [resync] the prefix
   [0, n_done) agreed with the trail, and [emit] then filled [done_] up to the trail's
   length; every position below the mark has stayed on the trail, unchanged, since that
   [resync] ([Store.take_low_water]: the trail only shrinks in [Store.undo_to], which
   lowers the mark). So the walk from the mark ends where the walk from 0 ended, and
   [n_done] is what it was. The first call on a store registers the reader and walks from
   0; a trace moved to another store (a test's shape) registers again. *)
let resync t store =
  let start =
    match t.low_water with
    | Some (s, r) when s == store -> Store.take_low_water store r
    | _ ->
        t.low_water <- Some (store, Store.register_low_water store);
        0
  in
  let n = Stdlib.min t.n_done (Store.trail_length store) in
  let rec go i =
    if i >= n then n
    else if Store.trail_entry store i == t.done_.(i) then go (i + 1)
    else i
  in
  t.n_done <- go (Stdlib.min start n)

(* The trail position at which level [k + 1] opened: [Store.level_marks]' [k]-th element,
   read in place (M11-complexity-T5, see [emit_to_page]). *)
let mark_at store k = store.Store.marks.(k).Store.trail_mark

(* ------------------------------------------------------------------ claims *)

(* The order literal a pruning established, per bound. [Encoding] is asked rather than
   [Lit] directly so that a bound which is the variable's *declared* one comes back as
   [Holds] -- the encoding's constant true, docs/PROOF-FORMAT.md section 3 -- and is
   skipped instead of being claimed with a literal that does not exist. [Fails] would
   mean the store holds a domain the encoding says is empty, i.e. I-D1 (lo <= hi for
   every unfixed variable) is broken somewhere upstream; say so rather than write a line
   about it. *)
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

   An order literal cannot state a hole on its own, and a two-literal clause states one
   perfectly well. Only a claim that has to be a single literal forces the direct
   encoding (D-0019 point 3), and a trace line's claim never had to be. Until M1-T56 the
   comment here read that as "a pure hole removal produces no line -- correct today (M1
   is bounds-only)", which was not correct: [int_ne] (M1-T9) has punched interior holes
   since it was written.

   A hole is strictly inside its own domain's bounds by construction -- [Domain.classify]
   reports a change as a [Bound] *or* a [Holes] and never both, because a removal at a
   bound settles and tightens that bound instead (I-D2: holes are never at the bounds) --
   and a domain's bounds are
   inside the declared ones, so both halves are [Cond] for every hole M1 can punch. The
   other two cases are still handled rather than asserted, because "both halves fail"
   is the one that would quietly write the *empty* clause, i.e. an unconditional
   contradiction, which is the worst thing a trace line can say (compare I-P5, every
   change carries its facts, since merged into I-P4). *)
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

   [settled_over] carries the hole values a settle walked over, and [settle_facts] turns
   them into facts that go in this line's tail, which makes the line RUP against the
   *hole's own trace line* (M1-T56, written first because the hole is earlier on the
   trail). That is I-X9: the reasons of the holes the settle walked over are part of the
   justification and are cited with it (M1-T57).

   Why it is needed: [Domain.set_lo]/[set_hi] do not stop where the propagator asks.
   [Domain.settle] walks the new bound past any hole it lands on, so [e.now]'s bound can
   be *strictly stronger* than the bound the propagator's facts derive, and the
   difference is exactly the holes walked over (D-0035: an explanation must justify the
   bound as recorded). A line that claims [e.now] from those facts alone claims more than
   they justify. Before M1-T57 such lines verified anyway, because the checker happened
   to re-derive each hole from the .opb's disequality rows by unit propagation, which is
   a property of [int_ne]'s big-M rows and not something a trace line may rest on.

   The set is the contiguous run of holes immediately below (or above) the new bound.
   That is an over-approximation of what the settle walked over by at most the holes the
   propagator's asked-for bound had already cleared, and it is empty exactly when no
   settle happened -- so a pruning that landed on a member of the domain writes the byte
   for byte identical line it wrote before. Extra facts only *weaken* the clause, so
   they can cost precision and never soundness; the alternative is the propagator's
   asked-for bound on the trail entry, which is not additive to [Store.entry] and is a
   decision record, not an edit.

   [hole] is the value a hole line claims to be removed, and [None] for a bound line. It
   is not part of what gets written -- the claim clause already says it -- it is what lets
   [emit] record *which* of an entry's lines a later settle cites, so that I-S4's edges
   are per-hole rather than per-trail-entry. *)
type line = { claim : Lit.t list; settled_over : int list; hole : int option }

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
          (fun l -> { claim = [ l ]; settled_over; hole = None })
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
            (fun claim -> { claim; settled_over = []; hole = Some v })
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

(* [~origin] rendered on demand (D-0145, D-0140 J6); [emit_line] is the same over a
   string. *)
let emit_line_lazy (ctx : Justify.ctx) ~origin ~claim ~facts =
  Justify.emit_rup_clause_lazy ctx ~origin (clause_of ~claim ~facts)

let emit_line ctx ~origin ~claim ~facts =
  emit_line_lazy ctx ~origin:(fun () -> origin) ~claim ~facts

(* Is this entry's line the BITS arm's? A variable over a wide domain can use the bits
   (binary) encoding instead of the order ladder (M8-bits-encoding, D-0130), and a
   pruning over such a row is not RUP, so it is written as one derivation instead (see
   [emit_to_page]). The unit is the ROW -- a pruning whose row has a bits term anywhere
   is not RUP, whichever variable it pruned -- and the row's owners
   are the claim's owner plus every term the propagator READ, which is the reason's
   scope including the terms whose fact does not materialise ([Reason.owners]'s
   contract). Order-only models short-circuit before touching the reason.
   (M8-bits-encoding-T2: D-0130 section 2's first refinement, D-0132 section 2.5.) *)
let bits_owner (enc : Encoding.t) name = Encoding.is_bits enc name

let bits_arm (enc : Encoding.t) ~claim_owner (facts : Reason.fact list) =
  Encoding.n_bits_vars enc > 0
  && (bits_owner enc claim_owner
     || List.exists (fun f -> bits_owner enc (Reason.fact_owner f)) facts)

let same_clause a b =
  List.equal Lit.equal (List.sort_uniq Lit.compare a) (List.sort_uniq Lit.compare b)

(* [Store.remover] is the trail entry that took a value out of a variable's domain, and
   [settle_facts] below cites that entry's reason. [None] means a hole with no trail entry
   behind it, i.e. a *declared* domain with a gap (what [Domain.of_list] built, for
   `var {1,3,5}: x`). This module then cites nothing rather than raising: the line is
   exactly as strong as the one it wrote before M1-T57, so an encoding that grows
   declared holes degrades to the old behaviour instead of aborting the solve, and the
   .opb would have to state such a hole as a row anyway, which is what the checker would
   then use.

   **No such domain reaches the store, and what guarantees it is named rather than
   implied, so this and [Store.remover]'s header cannot drift apart (M1-T63, which found
   two hedges for a declared hole unreachable):** no function in `lib/` builds one.
   `Domain.of_list` had no caller there and M22-review-T5 moved it to the test helper
   `test/unit/domain_helper.ml`. That is the WHOLE gate, and it is load-bearing. A
   `var {1,3,5}: x` reaches the store as its HULL, and `compile.ml` posts each hole as its
   own `Ne` instance (M7-T11, D-0072: set domains go in the .opb as ladder rows and in
   the solver as propagators), so every hole has a trail entry behind it and
   [Store.remover] returns [Some]. M7-T11 first tried loading the holes into the store
   via [Domain.of_list], and veripb rejected four refutations, because a conflict resting
   on a trail-less hole is justified by a `pol` over model rows that is not
   contradictory. M7-T11 also deleted `reject_set_domain`, which this comment used to
   name as the primary gate. Saying only that SPEC 2.1 "does not admit" a set domain was
   the weaker form: a subset can be widened, whereas the gate is a line of code someone
   has to delete. **If you build a domain with gaps in `lib/` (bring
   [Domain_helper.of_list] back), read D-0072 first.**

   [Store.remover] was a local copy here until M2-T8 moved it to [Store], which had a
   second copy of it in [Linear.find_removal] with the other off-by-one convention. *)

(* Append a fact if it is not already in the tail. The propagator's own facts keep their
   order and are never rewritten, so every line for a pruning that did not settle comes
   out unchanged; only the hole facts are appended, and a hole whose fact the propagator
   already read is not stated twice.

   The accumulator is held REVERSED, newest fact first, so an append is a cons rather
   than [acc @ [l]] (M6-T15, D-0090). The [@] was 5 % of 2014_mario's profile in D-0088,
   the record of M6-T14, which replaced the support and remover scans by per-variable
   trail histories. The dedup asks the same question of the same set of literals, so
   first-occurrence semantics are unchanged, and [settle_facts] reverses once at the end,
   so the order the line is written in is exactly the old one. *)
let add_fact_rev racc l = if List.exists (Lit.equal l) racc then racc else l :: racc

(* [add_fact_rev] over a whole settle, the same list, with the membership test moved to a
   table once the accumulator holds more than [dedup_list_max] facts (D-0216, the
   black-hole root-cost fixes of M11-complexity-T18). The walk was quadratic in a tail's
   facts: on 2011_black-hole_14 under native `table`, a settle
   over many holes brings each remover's facts, and [List.exists] was 19 % of a proved
   node. Below the bound the list walk is kept, which is cheaper than hashing a short
   tail. [Lit.equal] is structural equality, which is what the table compares. *)
let dedup_list_max = 32

type dedup = {
  mutable racc : Lit.t list;
  mutable n : int;
  mutable seen : (Lit.t, unit) Hashtbl.t option;
}

let dedup_of racc = { racc; n = List.length racc; seen = None }

let dedup_add d l =
  match d.seen with
  | Some h ->
      if not (Hashtbl.mem h l) then (
        Hashtbl.replace h l ();
        d.racc <- l :: d.racc)
  | None ->
      if not (List.exists (Lit.equal l) d.racc) then (
        d.racc <- l :: d.racc;
        d.n <- d.n + 1;
        if d.n > dedup_list_max then (
          let h = Hashtbl.create (4 * dedup_list_max) in
          List.iter (fun x -> Hashtbl.replace h x ()) d.racc;
          d.seen <- Some h))

(* The old walk, kept one wave as [position_of]'s [BAGUETTE_DEBUG] cross-check and as
   test_trace's oracle (M6-T15, D-0090). Remove it with the check. *)
let position_of_scan t (e : Store.entry) =
  let rec go i =
    if i >= t.n_done then None else if t.done_.(i) == e then Some i else go (i + 1)
  in
  go 0

(* The trail position this module last wrote lines for [e] at, by physical identity --
   the same key [resync] uses, and for the same reason. [n_done] has already been bumped
   past the entry [emit] is working on, so every position a settle can reach has been
   (re)remembered in this pass or an earlier one and the array agrees with the trail.

   O(1) rather than a walk over [done_] (M6-T15, D-0090; the walk was 39.5 % of
   2014_mario's profile, D-0088). It is exact because [done_.(i)] is only ever set to the
   entry at trail position [i] ([remember]'s one caller is [emit], with [Store.trail_entry
   store i]), and an entry sits at exactly one trail position for its whole life, its
   [Store.entry.pos]. So [e] can be in [done_.(0 .. n_done-1)] only at [e.pos], and the
   walk's first hit -- its only hit -- is [e.pos] iff [done_.(e.pos) == e]. There is no
   second mapping to keep in step: the wipe is still [resync] lowering [n_done] and
   [remember] overwriting a slot, and an entry a backtrack popped can still be "found" at
   its old slot until that slot is refilled, exactly as the walk found it. The [None] case
   is the same test failing. *)
let position_of t (e : Store.entry) =
  let p = e.Store.pos in
  let r = if p >= 0 && p < t.n_done && t.done_.(p) == e then Some p else None in
  Debug.check "M6-T15: Trace.position_of agrees with the walk over done_" (fun () ->
      r = position_of_scan t e);
  r

(* Every line this module wrote for one trail entry: one per bound it moved, or one per
   interior hole it punched (see [lines]). 1UIP clause learning (M2-L3, lib/core/learn.ml)
   asks for all of them: the [rup] of a learned clause is checked against the database as
   it stands, so what its derivation needs LIVE is every line behind every entry the cut
   resolved, not only the hole lines I-S4 is phrased about. *)
let lines_at t (e : Store.entry) =
  match position_of t e with None -> [] | Some i -> t.line_ids.(i)

(* The id of the line this module wrote for [v]'s removal, if it wrote one. [None] covers
   the two honest cases: a remover whose change was a *bound* move that happened to
   exclude [v] (it has a line, but that line claims a bound, not `<> v`, so it is not the
   hole's own line), and a hole the encoding stated as constant-true so no line exists. *)
let hole_line_of t (e : Store.entry) v =
  match position_of t e with
  | None -> None
  | Some i -> List.find_opt (fun w -> w.w_hole = Some v) t.line_ids.(i)

(* The facts the settled-over holes contribute, and -- for I-S4 -- the ids of the lines
   those holes were stated by. The two are gathered together because they come from the
   same [Store.remover] lookup, and because a fact taken from a hole whose line this
   module cannot name is precisely the case I-S4 has nothing to say about. *)
let settle_facts t store ~before ~var holes base =
  match holes with
  | [] -> (base, [])
  | _ ->
      (* Both accumulators reversed, reversed once at the end (M6-T15): same order out. *)
      let d = dedup_of (List.rev base) in
      let rcited =
        List.fold_left
          (fun rcited v ->
            match Store.remover store ~before ~var v with
            | None -> rcited
            | Some e -> (
                List.iter (dedup_add d) (Reason.lits e.Store.reason);
                match hole_line_of t e v with
                | None -> rcited
                | Some w -> (v, w) :: rcited))
          [] holes
      in
      (List.rev d.racc, List.rev rcited)

(* Record one I-S4 edge and, under BAGUETTE_DEBUG, fail at the citation rather than at
   the checker. [Debug.check] is the live gate; [i_s4_violations] is the same verdict as
   data, for a test that wants to perform the break and then ask. *)
let record_citation t (w : Writer.t) ~citing ~citing_level ~cited ~cited_level ~hole =
  (* No page, no edge: under `--no-proof` the writer is null (M9-no-proof-T2, D-0126, the
     solve-without-proof mode). Unreachable in practice under the null writer, because
     [emit] below writes no line, so [hole_line_of] names none to cite; guarded anyway, so
     the list of skipped work D-0126 gives is the list the code enforces. *)
  if Writer.is_null w then ()
  else
    let live_known = Writer.auditing w in
    let cited_live = live_known && Writer.is_live w cited in
    let c = { citing; cited; citing_level; cited_level; cited_live; live_known; hole } in
    if t.history then t.cites_rev <- c :: t.cites_rev;
    Debug.check
      (match i_s4_verdict c with Some m -> m | None -> "I-S4")
      (fun () -> i_s4_verdict c = None)

(* Writing a pruning's derivation AHEAD of its trace line: the whole of what a
   [Needs_derivation] propagator family needs from this module (M4-T1, the first such
   family, all_different's Hall intervals). I-X10 requires every trace line a propagator
   emits to be RUP against the .opb plus the lines before it, and D-0040 found that a
   counting global meets it only with an explicit derivation written first.

   Until M4 every trace line was RUP against the .opb alone, because every pruning
   followed from a SINGLE model constraint whose rows unit-propagate the claim. A
   Hall-interval pruning does not: its claim is a counting argument over n disequality
   rows, and D-0040 measured 3.0.2 refusing exactly that line standalone. The record's
   own remedy is the one sentence this function implements: "emit that derivation as
   explicit `pol` lines *ahead of* its trace line, so the line is RUP in sequence". With
   the derivation on the page the line follows from it by unit propagation, and nothing
   about the line itself changes.

   WHICH ENTRIES. Those with [Store.entry]'s [ahead] set, and nothing else (M7-T17,
   D-0082: derive-ahead is a property of the PROPAGATOR). Whether a pruning's line is RUP
   against the .opb alone is a property of HOW the pruning was inferred, so it is the
   PROPAGATOR that says so, at its own pruning call, through [Store.deriving_ahead]:
   all_different's Hall moves and Regin holes, gcc's capacity pushes, and the counting
   prunings of cumulative, member and circuit. These are the [Needs_derivation] families
   of test/unit/test_trace.ml's I-X10 table, and only the prunings of theirs that count.
   (A conflict can be made under it too, see [conflict_line_to_page].)

   Before M7-T17 the trigger was [Encoding.has_direct] of the pruned variable, a proxy
   for "this variable is in a counting global's scope". It was wrong both ways. It
   OVER-triggered: an [int_lin_le] pruning of an all_different variable got its [pol]
   written ahead of a line that did not need one, and so did every element INDEX
   pruning, which is [Single_row] and verifies without it (measured, D-0082). It
   UNDER-triggered: gcc's counting rows are over the ORDER encoding and name no direct
   literal, so its lines went out bare and 3.0.2 refused them, and M7-T16 bought the
   trigger back by requesting a direct encoding nothing read (D-0078; +13% on
   `2008_debruijn_binary`, all of it `red`). The flag cost one immediate field per trail
   entry and four call sites at the time, and the encoding is no longer consulted here
   at all. A proof of a model with no global constraint was byte-identical across the
   change (measured over the model suite, D-0082), because only those families set the
   flag.

   A [Needs_derivation] family whose pruning does NOT run under [deriving_ahead] writes
   a bare [rup] the checker refuses -- test/unit/test_trace.ml's [test_ix10_derive_ahead]
   is the lane that reddens (measured by removing the call, D-0082).

   A DECISION is skipped, and must be: nothing in the proof establishes one, and
   [Justify.emit] refuses it outright (D-0009, M1-T50).

   The id this mints is an ordinary [pol] at the entry's own level, so the same
   [Writer.wipe_level] that retires the line retires it, and at level 0
   [Search.solve]'s end-of-run sweep does (I-X2). It is not recorded in [t.permanent]:
   this module owns the lines it writes through [emit_line], and an id [Justify] minted
   and memoised is [Justify]'s. *)
let derive_ahead (ctx : Justify.ctx) store (e : Store.entry) =
  if e.Store.ahead then
    (* M11-complexity-T13 (D-0168): the explanation is emitted as it stands, a thunk
       and not its forced head, so that [Justify] records the line on the thunk and
       releases its tree. A released thunk was emitted, so it is no decision, and is not
       forced again just to be asked. *)
    let why = Store.explanation store e in
    match why with
    | Explanation.Deferred th when Explanation.line_of th <> Explanation.No_line ->
        ignore (Justify.emit ctx why : Writer.cid)
    | _ -> (
        match Explanation.force why with
        | Explanation.Decision _ -> ()
        | _ -> ignore (Justify.emit ctx why : Writer.cid))

(* The BITS arm's derivation of one pruning, when its derivation is a bits derivation
   (see [emit_to_page]): the `pol` deriving its trace clause, and the clause. *)
let bits_derived (ctx : Justify.ctx) ~name ~facts (e : Store.entry) why =
  match Explanation.force why with
  | forced when Justify.is_bits_derivation forced ->
      let origin =
        Printf.sprintf "bits trace: %s from %d fact(s)" name (List.length facts)
      in
      Some (Justify.emit_bits_pruning ctx ~origin ~concludes:e.Store.concludes forced)
  | _ -> None

(* Raised by [emit] when its [stop] says yes, between two trail entries, so that a
   --time-limit stop is not delayed by a long trace (M6-T23, D-0149: the overshoot was
   the stop never being asked inside a conflict's trace). Every line already written is
   whole and RUP where it stands (each rests only on the model and on earlier lines,
   oldest first, see the header), so the page is a valid prefix of the branch's trace, and
   the writer is back on the level it was on. What is left unwritten is the lines of the
   entries not yet reached, which nothing on the page cites. *)
exception Stopped

(* Write every line the trail owes, oldest first, and leave the writer on the level it
   was on. [Search] emits the nogood straight after, at the branch's own level, so this
   must not move it: that is the ordering D-0018 point 4 exists to protect (the nogood is
   emitted BEFORE the level is wiped). The writer's level is a stack the solver mirrors
   ([Writer.set_level], [Writer.wipe_level]), and a trace that left the writer somewhere
   else would wipe the wrong constraints.

   Oldest first is load-bearing for more than readability: a settle's line is RUP against
   the lines of the holes it walked over (see [line]), and those holes are earlier trail
   entries, so their lines are already in the database when the settle's line is
   checked. *)
let emit_to_page ?(stop = fun () -> false) (ctx : Justify.ctx) t store =
  resync t store;
  let saved = Writer.current_level ctx.Justify.writer in
  let at = ref saved in
  let n = Store.trail_length store in
  (* The entry's level by a cursor over the level marks (D-0145, D-0140 J5), which only
     moves forward as [i] does, instead of two binary searches per
     entry ([Store.is_level_start] and [Store.level_of_index]). [lv] is the number of
     marks at or below [i], which is [Store.level_of_index store i] (the marks are
     monotone, I-T2: trail entries are strictly ordered by level), and [i] opens a level
     exactly when the last of them is [i], which is [Store.is_level_start]'s test. Nothing
     in this loop opens or closes a level. *)
  let n_levels = Store.level store in
  let lv = ref (Store.level_of_index store t.n_done) in
  for i = t.n_done to n - 1 do
    (* Asked at every entry: one entry's lines (its derivation ahead included) are the
       latency. At every 64th, cable's 120 s limit fired at 123.88 s (D-0149). *)
    if stop () then (
      if !at <> saved then Writer.set_level ctx.Justify.writer saved;
      raise Stopped);
    while !lv < n_levels && mark_at store !lv <= i do
      incr lv
    done;
    let opens = !lv > 0 && mark_at store (!lv - 1) = i in
    Debug.check "M11-T5: Trace's level cursor agrees with Store.level_of_index" (fun () ->
        !lv = Store.level_of_index store i && opens = Store.is_level_start store i);
    let e = Store.trail_entry store i in
    remember t i e;
    (* A thunk forced here was built by the entry's propagator: credit it there in the
       explanation statistics (per-producer node counts, M11-complexity-T15). *)
    if Explanation.stats_on then Explanation.producer := e.Store.prop;
    if not opens then
      let name = Store.name store e.Store.var in
      (* [claims] first: a change that claims nothing writes nothing and must not force
         the [facts] thunk to find that out. "Lazy where it is expensive" cuts here too.
         Since M1-T56 an interior hole does get a claim, so the cases this skips are the
         ones where the whole change is invisible to the encoding -- a bound that was
         already the declared one. *)
      match lines ctx.Justify.encoding e name with
      | [] -> ()
      | cs ->
          (* One materialisation of the reason serves both the facts of the line and
             (M8-bits-encoding-T2) the scope the bits-arm decision reads. *)
          let all_facts = Reason.facts e.Store.reason in
          let facts = Reason.lits_of_facts all_facts in
          let level = !lv in
          (* The level is set here rather than inside the loop below so that the
             derivation and the line it precedes are tagged together; the loop's own
             [set_level] is then a no-op on the first claim and still does its job for a
             settle that spans levels. *)
          if !at <> level then (
            Writer.set_level ctx.Justify.writer level;
            at := level);
          derive_ahead ctx store e;
          (* M8-bits-encoding-T2: the BITS arm. A [Linear] pruning over a row with a
             bits term -- and, since M8-bits-encoding-T3 (D-0134, maxmin over bits by
             selector rows and one Resolve step), a choice derivation such as maxmin's
             over its selector rows -- writes its derivation as ONE `pol` deriving
             exactly its trace clause ([Justify.emit_bits_pruning]); when the line this
             module would have written IS that clause (the usual case) the `ia`'s id is
             the line, else the ordinary `rup` follows it and is RUP in sequence. An
             entry whose claim is a bits atom but whose justification is a [Clause] -- a
             global unit from `soli` (D-0130 section 9), whose bridge is already on the
             page -- keeps its `rup`. *)
          let bits = bits_arm ctx.Justify.encoding ~claim_owner:name all_facts in
          (* A bulk entry (D-0268, [Store.remove_interior]) has one derivation per hole,
             and each hole's line is decided against its own, as each merged entry's line
             was against its entry's; every other entry has one derivation for its lines. *)
          let per_hole = bits && Option.is_some e.Store.per_value in
          let derived =
            if bits && not per_hole then
              bits_derived ctx ~name ~facts e (Store.explanation store e)
            else None
          in
          List.iter
            (fun { claim; settled_over; hole } ->
              let derived =
                match hole with
                | Some v when per_hole ->
                    bits_derived ctx ~name ~facts e (Store.removal_explanation store e v)
                | _ -> derived
              in
              let facts, cited =
                settle_facts t store ~before:i ~var:e.Store.var settled_over facts
              in
              if !at <> level then (
                Writer.set_level ctx.Justify.writer level;
                at := level);
              (* Rendered only if read (D-0145, D-0140 J6): by the writer's audit naming
                 a leaked id, or by the mutation knob. It was a [Printf] and a rendering
                 of the claim per trace line. It holds the claim and a count, not the
                 facts: the audit keeps it while the line is live. *)
              let n_facts = List.length facts in
              let origin () =
                Printf.sprintf "trace: %s from %d fact(s)%s"
                  (String.concat " \\/ " (List.map Lit.to_string claim))
                  n_facts
                  (match settled_over with
                  | [] -> ""
                  | vs ->
                      Printf.sprintf ", settled over %s"
                        (String.concat "," (List.map string_of_int vs)))
              in
              let cid =
                match derived with
                | Some (dcid, dclause) when same_clause dclause (clause_of ~claim ~facts)
                  ->
                    dcid
                | _ -> emit_line_lazy ctx ~origin ~claim ~facts
              in
              record t ~level cid;
              t.line_ids.(i) <-
                { w_hole = hole; w_cid = cid; w_level = level } :: t.line_ids.(i);
              (* I-S4's edges, one per hole line this line rests on. Recorded after the
                 line is on the page so [citing] is a real id, and before the next
                 iteration so the order matches the proof. *)
              List.iter
                (fun (v, w) ->
                  record_citation t ctx.Justify.writer ~citing:cid ~citing_level:level
                    ~cited:w.w_cid ~cited_level:w.w_level ~hole:v)
                cited)
            cs
  done;
  if Explanation.stats_on then Explanation.producer := -1;
  if !at <> saved then Writer.set_level ctx.Justify.writer saved

(* M9-no-proof-T2 (D-0126): under `--no-proof` the writer is null and this module writes
   nothing -- the trail is not walked, no reason is materialised for a line's facts, no
   derivation is written ahead and no [Deferred] thunk is forced. [done_], [line_ids] and
   [permanent] stay empty, so [lines_at], [hole_line_of] and [permanent_ids] answer
   "nothing", which is the truth: a learned clause under this mode rests on lines that
   were never written, and [Learn.supports] reports none. The guard is a wrapper rather
   than a line inside [emit_to_page] so that the function above keeps its shape. *)
let emit ?stop (ctx : Justify.ctx) t store =
  if not (Writer.is_null ctx.Justify.writer) then emit_to_page ?stop ctx t store

(* D-0018 point 3: "a conflict under decisions logs its own reason line first, then the
   nogood". A conflict establishes no bound, so its line is the same clause with the
   claim omitted -- the empty sum over the negated facts, which is GCS's
   [ProofLogger::backtrack] shape applied to the propagator's own reason rather than to
   the guess list. [None] when the propagator did not record any: the line is then
   redundant for [int_lin_le] (a slack < 0 row is detected as violated by the checker's
   own unit propagation once the trace has assigned its bounds) and writing `>= 1 ;`
   over nothing would be a claim of unconditional contradiction, which is false.

   The facts arrive *in* the conflict rather than out of a one-shot slot on the store
   (M2-T7, which also put the reporting instance's id on every conflict).
   [Store.take_conflict_facts] and the [conflict_facts] field it consumed are gone, and
   with them the question the old comment had to answer -- "consumed exactly once,
   immediately, and nothing may run in between" -- because a value passed in cannot be
   stale, cannot be another propagator's, and cannot be consumed twice by accident. The
   clearing of the slot at its three sites ([take_conflict_facts], [Store.new_level],
   [Store.backtrack]) went with it. [Reason.none] materialising to [[]] is exactly what
   the un-armed slot's [None] used to mean, so what gets written is unchanged. *)
let conflict_line_to_page (ctx : Justify.ctx) t (c : Store.conflict) =
  let all_facts = Reason.facts c.Store.c_reason in
  (* M8-bits-encoding-T2: a [Linear] conflict over a row with a bits term is the same
     `pol` as a pruning with no claim, saturated to `~facts >= 1` -- and with NO facts
     (the row's slack below zero on the declared box) it closes at `0 >= k`, pinned by
     `ia >= 1`. That line is written even where the checker would refute the row unaided
     (D-0132 section 1, probe c2: it does here, and not in general), so a bits-row
     conflict always has a line. The scope read is the reason's, declared terms
     included, so a factless conflict still says which row it is about. *)
  let bits =
    Encoding.n_bits_vars ctx.Justify.encoding > 0
    && List.exists
         (fun f -> bits_owner ctx.Justify.encoding (Reason.fact_owner f))
         all_facts
    && Justify.is_bits_derivation c.Store.c_why
  in
  if bits then (
    let cid, _ =
      Justify.emit_bits_pruning ctx
        ~origin:
          (Printf.sprintf "bits trace: conflict from %d fact(s)" (List.length all_facts))
        ~concludes:None c.Store.c_why
    in
    record t ~level:(Writer.current_level ctx.Justify.writer) cid;
    Some cid)
  else
    match Reason.lits_of_facts all_facts with
    | [] -> None
    | facts ->
        (* A conflict made under [Store.deriving_ahead] has its derivation written first
           (M4-T10, D-0096: cumulative, the first family whose conflicts carry facts), so
           the `rup` below is RUP in sequence -- the conflict twin of [derive_ahead] for
           an entry. *)
        if c.Store.c_ahead then ignore (Justify.emit ctx c.Store.c_why : Writer.cid);
        let cid =
          let n_facts = List.length facts in
          Justify.emit_rup_clause_lazy ctx
            ~origin:(fun () -> Printf.sprintf "trace: conflict from %d fact(s)" n_facts)
            (List.map Lit.negate facts)
        in
        record t ~level:(Writer.current_level ctx.Justify.writer) cid;
        Some cid

(* M9-no-proof-T2 (D-0126): under the null writer the conflict's reason is not
   materialised and its derivation is not forced. [Some id] rather than [None], on
   purpose: [None] means "no line, state the derivation yourself", and [Search]'s
   conflict arm answers it by forcing [c_why] to write a `pol` -- exactly the forcing this
   mode exists to skip. The id is the null writer's, distinct and uncited. *)
let conflict_line (ctx : Justify.ctx) t (c : Store.conflict) =
  if Writer.is_null ctx.Justify.writer then
    Some (Writer.fresh ctx.Justify.writer ~origin:"no-proof: conflict line")
  else conflict_line_to_page ctx t c
