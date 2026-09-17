(* The backtrackable domain store.

   Mutation is undone by replaying a trail in reverse. Decision levels are marks into
   that trail. Every entry carries the arena index of the explanation of the change that
   made it, so conflict analysis can walk backwards through reasons (invariant I-T3).

   Invariant I-T1 is the one worth testing directly: backtrack_to restores every domain
   to exactly its state when the level was opened. The reason it holds here is that
   [Domain.t] is immutable - an entry keeps the old value, and restoring is a single
   array write with no aliasing between the saved and the current domain. *)

module Lit = Baguette_proof.Lit

(* The propagator instance that made a change, as the [id] of [Propagator.instance]
   (lib/core/propagator.ml) -- the id that already existed and that [Engine] already
   indexes its watcher lists and trigger masks by. [no_prop] is "no propagator":
   [Search]'s decision pushes, and a direct mutation from a test, are attributed to
   nobody, and that is the right answer for both. See [with_running]. *)
let no_prop = -1

(* "No trail entry supports this bound": it is still the bound the variable was created
   with. Not a valid trail position, so [lo_support]'s caller cannot accidentally index
   with it. *)
let no_support = -1

(* A level mark records where in the trail the level began, and where in the explanation
   arena it began: backtracking rewinds both together, which is what keeps I-T3 true
   (no trail entry survives whose reason has been dropped) and stops the arena growing
   without bound over a long search. *)
type mark = { trail_mark : int; reason_mark : int }

(* One recorded domain change.

   [old] is what the domain was, so backtracking is a single array write (I-T1).
   [now] is what the change *produced*, and it is here because of docs/DECISIONS.md
   D-0018: the trace line a pruning contributes to the proof claims the order literal
   the pruning established, and that literal is a function of the new bound, which
   nothing else on the trail records. D-0018's own consequence list says so; recording
   it is what makes lib/core/trace.ml possible at all. It costs one word and no work --
   [Domain.t] is immutable and [apply] already holds the value it is about to store.

   [reason] is the *other* half of that trace line: the bound facts the propagator
   actually read, negated into the clause's tail. It is deliberately NOT
   [Explanation.lits] of [why] -- that returns the declared-width [Weaken] chain the
   D-0013 [pol] needs, which is a different projection of the same pruning
   (lib/core/reason.ml's header says which, and lib/core/explanation.ml's [owners] says
   what the two do share).

   M2-T8/D-0026: this was a [unit -> Lit.t list] thunk and is now a [Reason.t] -- plain
   declarative data, no closure. Three things follow, and all three were the point:

     - A pruning allocates no closure and captures no environment. What it used to
       capture (a snapshot list, a propagator's term record) is exactly what D-0026
       quotes GCS measuring at ~20% of runtime.
     - The literals are built *later* than before, not earlier: the old thunk bodies
       were cheap because the [Lit.t]s were already allocated eagerly at the call site
       ([Linear.snapshot_source] built [Lit.ge name cur] per term per pruning whether or
       not anyone ever asked). [Reason.lits] is where that allocation happens now, once,
       for the prunings a failing branch actually writes down (ARCHITECTURE, "Deferred
       explanations").
     - It cannot read live store state, because it is not code. The I-X6 obligation on
       this half is discharged by the type. A propagator that does not supply facts
       writes [Reason.none] and cannot do so by omission.

   [why] stays the explanation arena index: I-T3 is still a bounds test.

   [sup_lo]/[sup_hi] are the trail positions that supported [var]'s lower and upper
   bound *before* this entry, or [no_support]. They exist so that "which earlier
   derivation established this bound?" is an O(1) question (see [lo_support] below), and
   they are here rather than in a side structure because backtracking has to restore
   them and [undo_to] already visits exactly this record. Two immediate ints, no
   allocation.

   Note for docs/ARCHITECTURE.md section 3 (the "keep the trail record small" one): this
   record is now eight fields, five of which exist only for the proof and for conflict
   analysis.

   [prop] is the propagator instance that made this change, M2-T7, closing the blocker
   docs/DECISIONS.md D-0011 names against itself: "a pruning's explanation is recorded on
   the trail as { var; old; why } -- **the trail records no propagator identity**. A
   caller walking the trail has the explanation and nothing else, so it cannot tell which
   half produced it, and [Trivial] is unresolvable." It is resolvable now. M2-T3's
   conflict analysis walks this trail and asks, of an entry it did not watch happen,
   which constraint implied it; that question has an answer here rather than needing
   [Explanation] to carry the row.

   It is stamped by [apply] off [t.current_prop], which the ENGINE sets around each
   [run] -- never passed in by the propagator. That is the whole point: no mutator takes
   an id, so a propagator has nothing to get wrong. [Engine.check_attribution] then reads
   the stamp back, on by default, and rejects any entry that does not name the instance
   that just ran or that credits an instance which does not watch the variable it
   changed. That read-back is what stops the field being decoration -- an id that is
   threaded and never read changes no behaviour at all, and would pass every test this
   suite has. *)
type entry = {
  var : Var.t;
  old : Domain.t;
  now : Domain.t;
  why : Explanation.Arena.id;
  reason : Reason.t;
  prop : int;
  sup_lo : int;
  sup_hi : int;
}

(* [lo_sup]/[hi_sup] are indexed by variable and hold the trail position of the entry
   that established that variable's current lower/upper bound, or [no_support] while it
   is still the declared one. Maintained by [apply] in O(1) and restored by [undo_to]
   from the entry's own [sup_lo]/[sup_hi].

   M2-T8 (D-0026) added them to delete a scan, not to add a cache. [Linear] asked "what
   established this bound?" once per term per pruning and answered it by walking the
   trail downwards from the newest entry -- O(|trail|) per term, O(n * |trail|) per
   pruning, and the most expensive thing left in [lib/] after M1-T24 fixed the same
   defect in [Engine.propagate]. The answer was always a single trail position that
   [apply] already knew when it pushed the entry, so it is recorded instead of
   recomputed. See [lo_support] for the equivalence argument, which is the part worth
   checking: the scan and the array agree only because bounds are monotone within a
   level (I-D3) and the array is restored on backtrack. *)
type t = {
  domains : Domain.t array;
  names : string array;
  reasons : Explanation.Arena.t;
  lo_sup : int array;
  hi_sup : int array;
  mutable trail : entry array;
  mutable trail_len : int;
  mutable marks : mark array;
  mutable n_levels : int;
  (* The propagator instance currently running, or [no_prop]. Written only by
     [with_running], read only by [apply] and [conflict] to stamp what they build.
     M2-T7 replaced a [conflict_facts : (unit -> Lit.t list) option] one-shot slot here:
     the facts behind a conflict now travel *in* the [conflict] value the propagator
     returns, so there is no slot to arm, to consume exactly once, or to clear in the
     three places ([take_conflict_facts], [new_level], [backtrack]) that arming it made
     necessary. One mutable field remains, and unlike the slot it is written and cleared
     by the same wrapper in the same call. *)
  mutable current_prop : int;
}

(* A conflict, with the identity of the propagator that reported it.

   [c_prop] is that propagator's instance id (M2-T7). A conflict was already the one
   case D-0011 said was fine -- "reasons are demanded only for *conflicts*, which
   [propagate] returns directly to the engine, so the instance that produced it is
   known" -- but "known to the engine, in a local variable" is not the same as
   "recorded", and [Search] and [Trace] are handed the conflict with the engine's local
   long gone. M2-T3 needs the conflicting constraint to start a 1UIP resolution from.

   [c_reason] is the bound facts behind the conflict, for D-0018 point 3's "a conflict
   under decisions logs its own reason line first". A conflict establishes no bound and
   so has no trail entry to hang them on; before M2-T7 they went through a one-shot
   mutable slot on [t], armed by the propagator immediately before returning and
   consumed immediately by [Trace.conflict_line]. They are a field of the returned value
   now, which is what "consumed exactly once, immediately, and nothing may run in
   between" was trying to approximate.

   M2-T8: it is a [Reason.t] rather than a thunk, and there is no default. A conflict
   with nothing behind it says [Reason.none] and is seen saying it; [Trace.conflict_line]
   then writes no line, because a line over an empty tail claims an unconditional
   contradiction, which is false. The conflict is built from the same
   [Reason.justified] value a pruning is, so the two halves arrive together here too. *)
type conflict = { c_prop : int; c_why : Explanation.t; c_reason : Reason.t }
type outcome = Unchanged | Changed | Conflict of conflict

let dummy_entry =
  {
    var = Var.of_int 0;
    old = Domain.singleton 0;
    now = Domain.singleton 0;
    why = Explanation.Arena.null;
    reason = Reason.none;
    prop = no_prop;
    sup_lo = no_support;
    sup_hi = no_support;
  }

let dummy_mark = { trail_mark = 0; reason_mark = 0 }

let create ~names ~domains =
  if Array.length names <> Array.length domains then
    invalid_arg "Store.create: names and domains differ in length";
  {
    domains = Array.copy domains;
    names = Array.copy names;
    reasons = Explanation.Arena.create ();
    lo_sup = Array.make (Stdlib.max 1 (Array.length domains)) no_support;
    hi_sup = Array.make (Stdlib.max 1 (Array.length domains)) no_support;
    trail = Array.make 64 dummy_entry;
    trail_len = 0;
    marks = Array.make 16 dummy_mark;
    n_levels = 0;
    current_prop = no_prop;
  }

let n_vars t = Array.length t.domains
let get t v = t.domains.(Var.to_int v)
let name t v = t.names.(Var.to_int v)
let level t = t.n_levels

(* The trail position of the entry that established [v]'s current lower (upper) bound, or
   [no_support] while it is still the bound [v] was created with. O(1). Defined here, so
   far above the section that explains it, only because the D-0026 agreement check below
   reads it; the argument for why it is equivalent to the scan it replaced lives at
   "what holds a bound up". *)
let lo_support t v = t.lo_sup.(Var.to_int v)
let hi_support t v = t.hi_sup.(Var.to_int v)
let trail_length t = t.trail_len
let reasons t = t.reasons

(* ------------------------------------------------ who is running (M2-T7) *)

(* [Store] does not know what a propagator is -- [Propagator] depends on this module and
   not the other way round -- so it holds the id as a plain int and trusts its caller for
   nothing except that the id is the one the engine is about to run. That is a weaker
   obligation than it looks: exactly one caller sets it ([Engine.propagate], through
   [with_running]), and the check that the stamp is right lives there too, next to the
   instance whose [inst_vars] it can compare against.

   The alternative considered and rejected was for each propagator to pass its own id to
   every mutator it calls. That is invasive -- every [set_lo]/[set_hi]/[remove] call site
   in prop/ grows an argument -- and, worse, unenforceable: nothing stops a propagator
   passing an id that is not its own, and there is no second source of truth to check it
   against, because the caller IS the authority in that design. Stamping from the engine
   leaves the mutators with no id to get wrong and gives the check something to compare
   against; the one remaining route to a wrong stamp is re-entering [with_running] from
   inside a propagator, which [Engine.check_attribution] refuses. *)
let running t = t.current_prop

(* Run [f] with [id] recorded as the running instance, restoring whatever was recorded
   before. Restoring rather than clearing to [no_prop] so that nesting is not a trap: an
   engine that ever runs a propagator from inside another one gets the right answer, and
   a caller that never nests pays nothing for it.

   [Fun.protect] rather than a plain set/run/restore because a propagator can raise --
   [Checked]'s overflow guard does, by design (I-X8, D-0029) -- and a store left claiming
   a propagator is running when none is would stamp the next change with a stale id.
   The run is over in that case, but "the run is over" is an argument, and this is one
   call per propagator invocation, which is noise next to the invocation. *)
let with_running t id f =
  let saved = t.current_prop in
  t.current_prop <- id;
  Fun.protect ~finally:(fun () -> t.current_prop <- saved) f

(* ------------------------------------------------------------- trail growth *)

let push_entry t e =
  if t.trail_len = Array.length t.trail then (
    let bigger = Array.make (2 * Array.length t.trail) dummy_entry in
    Array.blit t.trail 0 bigger 0 t.trail_len;
    t.trail <- bigger);
  t.trail.(t.trail_len) <- e;
  t.trail_len <- t.trail_len + 1

let push_mark t m =
  if t.n_levels = Array.length t.marks then (
    let bigger = Array.make (2 * Array.length t.marks) dummy_mark in
    Array.blit t.marks 0 bigger 0 t.n_levels;
    t.marks <- bigger);
  t.marks.(t.n_levels) <- m;
  t.n_levels <- t.n_levels + 1

(* ----------------------------------------------------------------- mutation *)

(* The variable of that name, or [None]. Linear in the variable count and only ever
   called from the debug-gated agreement check, so no index is kept for it. *)
let var_named t name =
  let n = Array.length t.names in
  let rec go i =
    if i >= n then None
    else if String.equal t.names.(i) name then Some (Var.of_int i)
    else go (i + 1)
  in
  go 0

(* The predicate, public and unconditional, so that a test can assert it directly rather
   than only through an environment variable read at module initialisation. A check that
   only runs under [BAGUETTE_DEBUG] is a check the suite cannot see fail; test_core.ml
   tests this function on both answers and then re-runs itself with the flag on to prove
   the wiring fires.

   Two directions, and neither is the naive one.

   **Forward.** Every fact the reason actually STATES is about a bound the justification
   could have used: either the derivation MENTIONS that variable's literals, or that bound
   is held up by a trail entry -- in which case the derivation is entitled to cite it by
   id and says nothing about the variable at all. That second arm is not slack, it is
   D-0038: [Explanation.Combine] records how a bound was derived and not what was derived,
   so a [Term (c, e)] citing "the entry that established y >= 2" contains no literal about
   y anywhere. The naive predicate ([Reason.owners] included in [Explanation.owners])
   therefore FIRES ON EVERY CORRECT CITING PRUNING -- found by running it, in
   test_prop.ml's D-0026 scene, not by reading it.

   "Actually states" is the second correction the same way. A fact at its declared bound
   materialises to no literal at all, so it appears in neither half and can contradict
   nothing: [Bool2int] pushing `x <= 1` out of `b <= 1` with `b` still at its declared
   upper bound is a correct pruning whose reason materialises to nothing and whose clause
   mentions only `x`. Requiring a support there fired on three test binaries. Both
   corrections were found by turning BAGUETTE_DEBUG on and watching the check reject
   working code; neither was visible by reading it.

   Requiring a support is the sharpest forward statement available until D-0038 gives a
   conclusion to compare against; see the M2-T8 hand-back for what it consequently does
   not catch.

   **Reverse.** Every variable the derivation weakens out of its own row at the top level
   must be named by the reason ([Explanation.top_weaken_owners] says why top level). This
   is the I-P5 direction: a derivation that read a variable and weakened it away has a
   pruning that depends on it, and a reason that omits it writes a trace line over too
   short a tail. *)
let agreement_holds t (j : Reason.justified) =
  let mentioned = Explanation.owners j.justification in
  let supported fact =
    match var_named t (Reason.fact_owner fact) with
    | None -> false
    | Some v ->
        if Reason.fact_is_lower fact then lo_support t v <> no_support
        else hi_support t v <> no_support
  in
  let named = Reason.owners j.reason in
  List.for_all
    (fun fact ->
      Option.is_none (Reason.lit_of_fact fact)
      || List.mem (Reason.fact_owner fact) mentioned
      || supported fact)
    j.reason
  && List.for_all
       (fun o -> List.mem o named)
       (Explanation.top_weaken_owners j.justification)

(* The failing message carries the offending pair, because "these two disagree" without
   saying which fact and which derivation is a message that sends the reader back to a
   breakpoint. Built only on the failing path, so the enabled-and-passing cost is the
   predicate alone. *)
let check_agreement t (j : Reason.justified) =
  if Debug.enabled && not (agreement_holds t j) then
    failwith
      (Printf.sprintf
         "invariant violated: D-0026: the reason and the justification are about the \
          same pruning -- reason [%s] vs justification %s"
         (Reason.to_string j.reason)
         (Explanation.to_string (Explanation.force j.justification)))

(* A conflict, attributed to whoever is running. The propagator never names itself; see
   [with_running]. It takes the same [Reason.justified] a pruning does, so "a conflict
   with no facts" is [Reason.because Reason.none expl] -- written out, never defaulted;
   see [Reason.none]. *)
let conflict t (j : Reason.justified) =
  check_agreement t j;
  { c_prop = t.current_prop; c_why = j.justification; c_reason = j.reason }

(* The one documented exception to the agreement check, for [apply]'s [Failed] arm alone.

   That arm deliberately pairs the justification of the change that did NOT land with
   [Reason.none], because the facts a *conflict* line needs are strictly more than the
   pruning's (see the comment there). The pair is therefore a real disagreement by the
   check's standard -- the derivation weakens variables the empty reason does not name --
   and it is sound only because nothing writes a trace line for it: [Trace.conflict_line]
   writes nothing over an empty tail, and the propagators that care build their own
   [conflict] with the fuller set.

   It is a separate function rather than a flag on [conflict] so that the exception is one
   named call site that a reader trips over, and so that adding a second one is an edit to
   this file. Found by turning the check on: this arm was the only false positive left in
   the suite once non-materialising facts were skipped. *)
let unattributed_conflict t why =
  { c_prop = t.current_prop; c_why = why; c_reason = Reason.none }

(* The D-0026 agreement check.

   The reason and the justification are two projections of one pruning, and until M2-T8
   they were kept in agreement by a comment. They cannot be compared literal for literal
   -- a [Weaken] summand states a variable's whole declared range while the reason states
   where its bound currently sits, so for a weakened term the two share no literal at all
   (lib/core/explanation.ml's [owners] says this at length). What they must share is the
   *variable scope*: a reason naming a variable the derivation never mentions is a reason
   for a different pruning, which is how a hand-edited propagator drifts.

   Under [BAGUETTE_DEBUG] only, and it FORCES the justification to do it. That is a
   deliberate, documented cost with one sharp edge: forcing at push time is exactly what
   masked the I-X6 violation in [explain_cross_conflict] until M1-T13 (search happened to
   force conflict explanations immediately, so a thunk reading live state read it before
   anything moved). A debug run therefore cannot be the run that catches a *new* I-X6
   violation, and nothing here claims otherwise -- the type discharges I-X6 on the reason
   half (lib/core/reason.ml), and on the justification half it stays an argument that
   test_prop.ml's snapshot tests check by backtracking before forcing. *)
(* Apply a Domain.result, recording the old value so it can be undone.

   Every path through here takes ONE [Reason.justified], which is both halves of
   D-0026 and both of I-P4 and I-P5. There is no second entry point that takes fewer:
   do not add an optional argument and do not add a sibling function that omits the
   reason -- [set_lo_with_facts] was that sibling, and the plain [set_lo] beside it
   silently meaning "no facts" is how [int_ne] pruned factlessly from M1-T9 to M1-T17. *)
let apply t v (r : Domain.result) (j : Reason.justified) =
  let why = j.justification in
  match r with
  | Domain.Unchanged -> Unchanged
  | Domain.Failed ->
      (* Deliberately WITHOUT the pruning's reason. That reason belongs to the change
         that did not land, and the facts a *conflict* line needs are strictly more: the
         crossed opposing bound as well (see lib/core/prop/linear.ml's [cross_conflict]
         and bool2int.ml's push arms, which both build the fuller set and return their
         own [conflict]). Attaching the partial set here would give those unreachable-at-
         the-interface forwarding arms in ne.ml and bool_clause.ml a conflict line over
         too few facts -- a claim that those facts alone are contradictory, which is
         false and which veripb would reject. Before M2-T7 they recorded nothing and got
         no line; they still get no line. *)
      Conflict (unattributed_conflict t why)
  | Domain.Changed d ->
      let i = Var.to_int v in
      let old = t.domains.(i) in
      Debug.check "I-D3: domains only shrink" (fun () ->
          Domain.lo d >= Domain.lo old
          && Domain.hi d <= Domain.hi old
          && Domain.size d < Domain.size old);
      Debug.check "I-D1: a stored domain is non-empty" (fun () ->
          Domain.lo d <= Domain.hi d);
      check_agreement t j;
      let why = Explanation.Arena.add t.reasons why in
      let at = t.trail_len in
      push_entry t
        {
          var = v;
          old;
          now = d;
          why;
          reason = j.reason;
          prop = t.current_prop;
          sup_lo = t.lo_sup.(i);
          sup_hi = t.hi_sup.(i);
        };
      (* The support of a bound this entry moved is this entry. A bound it left alone
         keeps whatever supported it, which is what the saved fields above restore. Both
         are tested: [Domain.fix] moves both, [Domain.remove] of an interior value moves
         neither. *)
      if Domain.lo d > Domain.lo old then t.lo_sup.(i) <- at;
      if Domain.hi d < Domain.hi old then t.hi_sup.(i) <- at;
      t.domains.(i) <- d;
      Changed

(* One mutator per kind of change, each taking one [Reason.justified]. There is no
   factless sibling and no optional argument: see [apply]. *)
let set_lo t v bound j = apply t v (Domain.set_lo (get t v) bound) j
let set_hi t v bound j = apply t v (Domain.set_hi (get t v) bound) j
let remove t v value j = apply t v (Domain.remove (get t v) value) j
let fix t v value j = apply t v (Domain.fix (get t v) value) j

(* ------------------------------------------------------------- backtracking *)

let new_level t =
  push_mark t
    { trail_mark = t.trail_len; reason_mark = Explanation.Arena.length t.reasons }

(* Undoing an entry restores the bound supports it saved as well as the domain. Both
   have to move together or [lo_support] starts naming a trail position that has been
   popped -- I-T3's failure mode one level up, and the reason [lo_support]'s equivalence
   with the scan it replaced holds at all. *)
let undo_to t target =
  while t.trail_len > target do
    let e = t.trail.(t.trail_len - 1) in
    let i = Var.to_int e.var in
    t.domains.(i) <- e.old;
    t.lo_sup.(i) <- e.sup_lo;
    t.hi_sup.(i) <- e.sup_hi;
    t.trail.(t.trail_len - 1) <- dummy_entry;
    t.trail_len <- t.trail_len - 1
  done

let backtrack t =
  if t.n_levels = 0 then invalid_arg "Store.backtrack: already at level 0";
  let m = t.marks.(t.n_levels - 1) in
  undo_to t m.trail_mark;
  Explanation.Arena.truncate t.reasons m.reason_mark;
  t.n_levels <- t.n_levels - 1

let backtrack_to t target_level =
  if target_level < 0 then invalid_arg "Store.backtrack_to: negative level";
  if target_level > t.n_levels then
    invalid_arg "Store.backtrack_to: cannot backtrack forwards";
  while t.n_levels > target_level do
    backtrack t
  done

(* ------------------------------------------------------------------ reading *)

let all_fixed t = Array.for_all Domain.is_fixed t.domains
let snapshot t = Array.copy t.domains

let same_domains t snap =
  Array.length snap = Array.length t.domains
  &&
  let ok = ref true in
  Array.iteri (fun i d -> if not (Domain.equal d snap.(i)) then ok := false) t.domains;
  !ok

(* The trail, most recent first. Conflict analysis walks this. *)
let trail_entries t =
  let acc = ref [] in
  for i = 0 to t.trail_len - 1 do
    acc := t.trail.(i) :: !acc
  done;
  !acc

(* The trail position at which each open level began, oldest level first. I-T2 says these
   are monotone; [check_invariants] asserts it. *)
let level_marks t = List.init t.n_levels (fun i -> t.marks.(i).trail_mark)
let explanation t e = Explanation.Arena.get t.reasons e.why

(* One trail entry by position, oldest first -- the order [Trace] walks, and the order
   the proof's trace lines have to be written in. [trail_entries] above is the other
   direction (newest first) and allocates the whole list; this does neither. *)
let trail_entry t i =
  if i < 0 || i >= t.trail_len then
    invalid_arg
      (Printf.sprintf "Store.trail_entry: %d out of range (len %d)" i t.trail_len);
  t.trail.(i)

(* ------------------------------------------------ what holds a bound up (M2-T8) *)

(* The trail position of the entry that established [v]'s current lower bound, or
   [no_support] while it is still the bound [v] was created with. O(1).

   This replaces lib/core/prop/linear.ml's [find_lo_reason], which answered the same
   question by scanning the trail downwards from the newest entry, once per term per
   pruning. Equivalence, because it is not obvious and because M1-T28 records that the
   *direction* of that scan was load-bearing (scanning upwards returns the OLDEST entry
   that moved the bound, i.e. a superseded reason, and no model in the suite can tell the
   two apart):

     - The scan looked for the newest entry [e] for [v] with [Domain.lo e.old < cur].
       Lower bounds only increase within a level (I-D3), so that entry is exactly the
       last one that increased lo, and every later entry for [v] left lo alone.
     - [apply] writes this array precisely when the change it is applying increases lo,
       so the array holds the last such entry -- the same one.
     - [undo_to] restores the value the entry saved, so a popped entry is never named.

   The remaining difference is the guard. The scan took the *propagator's frozen declared
   bound* and returned nothing when [cur] had not passed it; this array knows only what
   the store was created with. The two differ for a propagator built after something had
   already narrowed the variable (which unit tests do deliberately), so the guard stays
   at the call site where the declared bound lives -- [Linear.snapshot_source] already
   makes exactly that test before asking. *)
(* The entry that took [value] out of [var]'s domain, looking back from trail position
   [before] (exclusive). A value leaves a domain once and stays gone until the backtrack
   that pops the entry that removed it, so there is at most one and this finds it at the
   first hit.

   [None] means a hole with no trail entry behind it, i.e. a *declared* domain with a gap
   ([Domain.of_list], for `var {1,3,5}: x`, which docs/SPEC.md 2.1 does not admit and
   lib/flatzinc/compile.ml's [reject_set_domain] refuses). Callers cite nothing rather
   than raising; lib/core/trace.ml's [remover] header argues why.

   Shared: [Trace] and [Linear] had a copy each ([remover] and [find_removal]), with the
   two off-by-one conventions that invites. This is the [before]-is-exclusive one. *)
let remover t ~before ~var value =
  let rec go i =
    if i < 0 then None
    else
      let e = t.trail.(i) in
      if Var.equal e.var var && Domain.mem e.old value && not (Domain.mem e.now value)
      then Some e
      else go (i - 1)
  in
  go (Stdlib.min (before - 1) (t.trail_len - 1))

(* The values [Domain.settle] walked a bound over on its way to [cur]: the maximal run of
   holes immediately below (above) it in [old]. It stops at the first value [old] still
   held, which is at or beyond whatever bound was actually pushed, so it never claims more
   than the settle did. Empty when the entry's bound is exactly the bound its explanation
   derives, which is every entry in a model with no disequality. *)
let settled_over_lo old ~cur =
  let rec go v acc =
    if v < Domain.lo old || Domain.mem old v then acc else go (v - 1) (v :: acc)
  in
  go (cur - 1) []

let settled_over_hi old ~cur =
  let rec go v acc =
    if v > Domain.hi old || Domain.mem old v then acc else go (v + 1) (v :: acc)
  in
  go (cur + 1) []

(* Every reason [v]'s current lower bound rests on: the entry that moved it, then one per
   hole that entry's settle walked over (M1-T44, I-X9). [[]] exactly when no entry has
   moved it.

   O(1) plus one scan per hole settled over, which is zero holes for every bound in a
   model with no disequality. The hole scan is what is left of the old O(n * |trail|):
   it is per *hole*, not per term, and reaching it at all requires a disequality to have
   punched a hole immediately under a bound another propagator then pushed onto. *)
let reasons_under t v ~support ~settled =
  if support = no_support then []
  else
    let e = t.trail.(support) in
    Explanation.Arena.get t.reasons e.why
    :: List.filter_map
         (fun h ->
           Option.map
             (fun (r : entry) -> Explanation.Arena.get t.reasons r.why)
             (remover t ~before:support ~var:v h))
         (settled e)

let lo_reasons t v =
  reasons_under t v ~support:(lo_support t v) ~settled:(fun (e : entry) ->
      settled_over_lo e.old ~cur:(Domain.lo e.now))

let hi_reasons t v =
  reasons_under t v ~support:(hi_support t v) ~settled:(fun (e : entry) ->
      settled_over_hi e.old ~cur:(Domain.hi e.now))

(* The decision level the entry at trail position [i] belongs to: the number of open
   level marks at or below it (I-T2 makes the marks monotone, so this is a count, not a
   search). Position [marks.(k)] is exactly the *first* entry of level [k+1], which for
   a level opened by [Search.branch] is the decision push itself. *)
let level_of_index t i =
  let l = ref 0 in
  for k = 0 to t.n_levels - 1 do
    if t.marks.(k).trail_mark <= i then incr l
  done;
  !l

(* True when [i] is the first entry of some open level, i.e. the push that opened it.
   [Trace] skips these: a decision is not implied by the model and has no trace line. *)
let is_level_start t i =
  let r = ref false in
  for k = 0 to t.n_levels - 1 do
    if t.marks.(k).trail_mark = i then r := true
  done;
  !r

(* Debug-mode check of the trail invariants. Cheap enough to call after a backtrack in
   tests; linear in the trail, so not something the engine should call per propagation. *)
let check_invariants t =
  (* I-T2: level marks are monotone and within the trail. *)
  let rec monotone prev = function
    | [] -> true
    | m :: rest -> m >= prev && m <= t.trail_len && monotone m rest
  in
  let ok_marks = monotone 0 (level_marks t) in
  (* I-T3: every live trail entry's explanation index resolves. *)
  let ok_reasons = ref true in
  for i = 0 to t.trail_len - 1 do
    if not (Explanation.Arena.mem t.reasons t.trail.(i).why) then ok_reasons := false
  done;
  (* I-D1: no stored domain is empty. *)
  let ok_domains = Array.for_all (fun d -> Domain.lo d <= Domain.hi d) t.domains in
  (* M2-T8: every bound support names a live entry for that variable which moved that
     bound to where it now sits. This is the property [lo_support]'s equivalence with the
     scan it replaced rests on, so it is asserted rather than argued: an array that drifts
     from the trail makes every citation name the wrong derivation, and a wrong citation
     is a proof step about a bound nobody derived. *)
  let ok_support = ref true in
  Array.iteri
    (fun i sup ->
      if sup <> no_support then
        if sup < 0 || sup >= t.trail_len then ok_support := false
        else
          let e = t.trail.(sup) in
          if
            Var.to_int e.var <> i
            || Domain.lo e.old >= Domain.lo e.now
            || Domain.lo e.now <> Domain.lo t.domains.(i)
          then ok_support := false)
    t.lo_sup;
  Array.iteri
    (fun i sup ->
      if sup <> no_support then
        if sup < 0 || sup >= t.trail_len then ok_support := false
        else
          let e = t.trail.(sup) in
          if
            Var.to_int e.var <> i
            || Domain.hi e.old <= Domain.hi e.now
            || Domain.hi e.now <> Domain.hi t.domains.(i)
          then ok_support := false)
    t.hi_sup;
  ok_marks && !ok_reasons && ok_domains && !ok_support

let to_string t =
  String.concat " "
    (Array.to_list
       (Array.mapi
          (fun i d -> Printf.sprintf "%s=%s" t.names.(i) (Domain.to_string d))
          t.domains))
