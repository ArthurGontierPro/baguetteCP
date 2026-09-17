(* The backtrackable domain store.

   Mutation is undone by replaying a trail in reverse. Decision levels are marks into
   that trail. Every entry carries the arena index of the explanation of the change that
   made it, so conflict analysis can walk backwards through reasons (invariant I-T3).

   Invariant I-T1 is the one worth testing directly: backtrack_to restores every domain
   to exactly its state when the level was opened. The reason it holds here is that
   [Domain.t] is immutable - an entry keeps the old value, and restoring is a single
   array write with no aliasing between the saved and the current domain. *)

module Lit = Baguette_proof.Lit

(* No bound facts recorded for this change. A shared closure: no allocation per
   pruning for the propagators that do not (yet) supply one. *)
let no_facts () = []

(* The propagator instance that made a change, as the [id] of [Propagator.instance]
   (lib/core/propagator.ml) -- the id that already existed and that [Engine] already
   indexes its watcher lists and trigger masks by. [no_prop] is "no propagator":
   [Search]'s decision pushes, and a direct mutation from a test, are attributed to
   nobody, and that is the right answer for both. See [with_running]. *)
let no_prop = -1

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

   [facts] is the *other* half of that trace line: the current bound facts the
   propagator actually read, as order literals, negated into the clause's tail. It is
   deliberately NOT [Explanation.lits] of [why] -- that returns the declared-width
   [Weaken] chain the D-0013 [pol] needs, which is a different projection of the same
   pruning (see docs/WORKLOG cross-session note, and lib/core/prop/linear.ml's
   [facts_of_snaps]). A thunk, not a list, so the literals are built only for the
   prunings a failing branch actually has to write down (ARCHITECTURE, "Deferred
   explanations"); [Trace] forces each at most once. A propagator that does not supply
   one gets [no_facts], and its trace line then claims the bound out of the row alone
   -- which veripb accepts exactly when that is true and rejects loudly when it is not,
   so the omission cannot pass silently.

   [why] stays the explanation arena index: I-T3 is still a bounds test.

   [prop] is the propagator instance that made this change, M2-T7, closing the blocker
   docs/DECISIONS.md D-0011 names against itself: "a pruning's explanation is recorded on
   the trail as { var; old; why } -- **the trail records no propagator identity**. A
   caller walking the trail has the explanation and nothing else, so it cannot tell which
   half produced it, and [Trivial] is unresolvable." It is resolvable now. M2-T3's
   conflict analysis walks this trail and asks, of an entry it did not watch happen,
   which constraint implied it; that question has an answer here rather than needing
   [Explanation] to carry the row.

   It is stamped by [apply] off [t.current_prop], which the ENGINE sets around each
   [run] -- never passed in by the propagator. That is the whole point: a propagator
   cannot name an id at all, so it cannot name the wrong one. [Engine.check_attribution]
   then reads the stamp back and rejects any entry credited to an instance that does not
   watch the variable it changed, which is what stops the field being decoration.

   Note for docs/ARCHITECTURE.md section 3 (the "keep the trail record small" one):
   this record is now six fields, three of which exist only for the proof and for
   conflict analysis. *)
type entry = {
  var : Var.t;
  old : Domain.t;
  now : Domain.t;
  why : Explanation.Arena.id;
  facts : unit -> Lit.t list;
  prop : int;
}

type t = {
  domains : Domain.t array;
  names : string array;
  reasons : Explanation.Arena.t;
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

   [c_facts] is the bound facts behind the conflict, for D-0018 point 3's "a conflict
   under decisions logs its own reason line first". A conflict establishes no bound and
   so has no trail entry to hang them on; before M2-T7 they went through a one-shot
   mutable slot on [t], armed by the propagator immediately before returning and
   consumed immediately by [Trace.conflict_line]. They are a field of the returned value
   now, which is what "consumed exactly once, immediately, and nothing may run in
   between" was trying to approximate.

   [no_facts] is the default and means "this conflict records none", exactly as an
   unarmed slot did: [Trace.conflict_line] then writes no line, because a line over an
   empty tail claims an unconditional contradiction, which is false. *)
type conflict = { c_prop : int; c_why : Explanation.t; c_facts : unit -> Lit.t list }
type outcome = Unchanged | Changed | Conflict of conflict

let dummy_entry =
  {
    var = Var.of_int 0;
    old = Domain.singleton 0;
    now = Domain.singleton 0;
    why = Explanation.Arena.null;
    facts = no_facts;
    prop = no_prop;
  }

let dummy_mark = { trail_mark = 0; reason_mark = 0 }

let create ~names ~domains =
  if Array.length names <> Array.length domains then
    invalid_arg "Store.create: names and domains differ in length";
  {
    domains = Array.copy domains;
    names = Array.copy names;
    reasons = Explanation.Arena.create ();
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
   passing an id that is not its own, and the resulting mis-attribution is invisible.
   Stamping from the engine makes attributing a prune to the wrong propagator
   structurally impossible rather than merely discouraged. *)
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

(* A conflict, attributed to whoever is running. The propagator never names itself; see
   [with_running]. [~facts] defaults to [no_facts], which is "this conflict records no
   bound facts" -- the same thing an un-armed [conflict_facts] slot used to mean, and the
   behaviour [Trace.conflict_line] still keys off. *)
let conflict t ?(facts = no_facts) why =
  { c_prop = t.current_prop; c_why = why; c_facts = facts }

(* Apply a Domain.result, recording the old value so it can be undone.
   Every path through here takes an explanation: invariant I-P4 is enforced by this
   signature, so do not add an optional reason argument. *)
let apply t v (r : Domain.result) facts why =
  match r with
  | Domain.Unchanged -> Unchanged
  | Domain.Failed ->
      (* Deliberately WITHOUT [~facts]. [facts] here belongs to the change that did not
         land, and the facts a *conflict* line needs are strictly more: the crossed
         opposing bound as well (see lib/core/prop/linear.ml's [cross_conflict] and
         bool2int.ml's push arms, which both build the fuller set and return their own
         [conflict]). Attaching the partial set here would give those unreachable-at-the-
         interface forwarding arms in ne.ml and bool_clause.ml a conflict line over too
         few facts -- a claim that those facts alone are contradictory, which is false
         and which veripb would reject. Before M2-T7 they recorded nothing and got no
         line; they still get no line. *)
      Conflict (conflict t why)
  | Domain.Changed d ->
      let i = Var.to_int v in
      let old = t.domains.(i) in
      Debug.check "I-D3: domains only shrink" (fun () ->
          Domain.lo d >= Domain.lo old
          && Domain.hi d <= Domain.hi old
          && Domain.size d < Domain.size old);
      Debug.check "I-D1: a stored domain is non-empty" (fun () ->
          Domain.lo d <= Domain.hi d);
      let why = Explanation.Arena.add t.reasons why in
      push_entry t { var = v; old; now = d; why; facts; prop = t.current_prop };
      t.domains.(i) <- d;
      Changed

let set_lo t v bound why = apply t v (Domain.set_lo (get t v) bound) no_facts why
let set_hi t v bound why = apply t v (Domain.set_hi (get t v) bound) no_facts why
let remove t v value why = apply t v (Domain.remove (get t v) value) no_facts why
let fix t v value why = apply t v (Domain.fix (get t v) value) no_facts why

(* The same two pushes, carrying the D-0018 trace reason as well as the explanation.

   Separate functions rather than an [?facts] argument on [set_lo]/[set_hi], because
   those two are passed around as first-class values (test/unit/test_prop.ml does it to
   drive one table of cases through both bounds) and an optional argument in the middle
   of a function type is not erased when the function is used that way -- it changes the
   type and breaks every such caller. Additive is also the right shape for a file three
   sessions read: nothing that compiled before compiles differently now.

   [facts] is NOT the explanation and does not weaken invariant I-P4: [why] is still
   mandatory here exactly as it is above. See [entry] for what the two are each for.

   [remove_with_facts] is the same addition for the third mutator. It was left out when
   the other two landed, on the grounds that "M1 is bounds-only (docs/SPEC.md 3.2) and
   nothing punches a hole" -- which [int_ne] (M1-T9, docs/DECISIONS.md D-0019) made
   untrue in the same round, and the gap was a real bug: a disequality that removes the
   value sitting at [lo] or at [hi] *shrinks the interval*, so it moves a bound, so
   lib/core/trace.ml gives it a trace line -- and with [no_facts] that line stated the
   new bound with an empty reason, i.e. unconditionally, which is simply false and which
   veripb rejects.

   Note what is and is not fixed by having the function. This comment used to end "a
   removal that moves no bound (a hole strictly inside the interval) still gets no line,
   because there is no order literal that states it", and that reasoning was wrong in its
   premise rather than in its conclusion: M1-T56 observed that a claim never had to BE an
   order literal. "x <> v" is the two-literal clause `x <= v-1 or x >= v+1`, which
   docs/PROOF-FORMAT.md section 4 already names as [int_ne]'s justification, so an
   interior hole can state itself without the direct encoding after all. [Trace]'s
   [claims] now writes a line for it, and M1-T57 depends on that: a settled bound cites
   the facts of the holes the settle walked over, which is only possible once those holes
   are on the page. So both cases are covered here now, not just the bound-moving one.
   D-0019 point 3 is still the test of when the direct encoding is genuinely forced, and
   this is not it. *)
let set_lo_with_facts t v bound ~facts why =
  apply t v (Domain.set_lo (get t v) bound) facts why

let set_hi_with_facts t v bound ~facts why =
  apply t v (Domain.set_hi (get t v) bound) facts why

let remove_with_facts t v value ~facts why =
  apply t v (Domain.remove (get t v) value) facts why

(* ------------------------------------------------------------- backtracking *)

let new_level t =
  push_mark t
    { trail_mark = t.trail_len; reason_mark = Explanation.Arena.length t.reasons }

let undo_to t target =
  while t.trail_len > target do
    let e = t.trail.(t.trail_len - 1) in
    t.domains.(Var.to_int e.var) <- e.old;
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
  ok_marks && !ok_reasons && ok_domains

let to_string t =
  String.concat " "
    (Array.to_list
       (Array.mapi
          (fun i d -> Printf.sprintf "%s=%s" t.names.(i) (Domain.to_string d))
          t.domains))
