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

   Note for docs/ARCHITECTURE.md section 3 (the "keep the trail record small" one):
   this record is now five fields, two of which exist only for the proof. *)
type entry = {
  var : Var.t;
  old : Domain.t;
  now : Domain.t;
  why : Explanation.Arena.id;
  facts : unit -> Lit.t list;
}

type t = {
  domains : Domain.t array;
  names : string array;
  reasons : Explanation.Arena.t;
  mutable trail : entry array;
  mutable trail_len : int;
  mutable marks : mark array;
  mutable n_levels : int;
  (* The bound facts behind the conflict a propagator has just reported, for D-0018
     point 3's "a conflict under decisions logs its own reason line first". A conflict
     is not a domain change, so it has no trail entry to hang them on, and
     [Propagator.result] (lib/core/propagator.ml, not this round's to change) carries
     only the [Explanation.t]. See [record_conflict_facts]. *)
  mutable conflict_facts : (unit -> Lit.t list) option;
}

type outcome = Unchanged | Changed | Conflict of Explanation.t

let dummy_entry =
  {
    var = Var.of_int 0;
    old = Domain.singleton 0;
    now = Domain.singleton 0;
    why = Explanation.Arena.null;
    facts = no_facts;
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
    conflict_facts = None;
  }

let n_vars t = Array.length t.domains
let get t v = t.domains.(Var.to_int v)
let name t v = t.names.(Var.to_int v)
let level t = t.n_levels
let trail_length t = t.trail_len
let reasons t = t.reasons

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

(* Apply a Domain.result, recording the old value so it can be undone.
   Every path through here takes an explanation: invariant I-P4 is enforced by this
   signature, so do not add an optional reason argument. *)
let apply t v (r : Domain.result) facts why =
  match r with
  | Domain.Unchanged -> Unchanged
  | Domain.Failed -> Conflict why
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
      push_entry t { var = v; old; now = d; why; facts };
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

   Note what is and is not fixed by having the function: a removal that moves no bound
   (a hole strictly inside the interval) still gets no line, because there is no order
   literal that states it. That is unchanged and still correct for M1 -- see
   lib/core/trace.ml's [claims], and D-0019 point 3 for the test of when the direct
   encoding is genuinely forced. What this makes possible is the bound-moving case, and
   only that. *)
let set_lo_with_facts t v bound ~facts why =
  apply t v (Domain.set_lo (get t v) bound) facts why

let set_hi_with_facts t v bound ~facts why =
  apply t v (Domain.set_hi (get t v) bound) facts why

let remove_with_facts t v value ~facts why =
  apply t v (Domain.remove (get t v) value) facts why

(* ------------------------------------------------------- conflict bound facts *)

(* Called by a propagator on the same call that returns [Propagator.Conflict], and
   consumed exactly once, immediately, by whoever handles that conflict. Nothing else
   may run in between: [Engine.propagate] returns as soon as a propagator conflicts.
   [take_conflict_facts] clears the slot, and so do [new_level]/[backtrack], so a
   propagator that sets it and then does not conflict cannot leak facts into someone
   else's line later. *)
let record_conflict_facts t f = t.conflict_facts <- Some f

let take_conflict_facts t =
  let r = t.conflict_facts in
  t.conflict_facts <- None;
  r

(* ------------------------------------------------------------- backtracking *)

let new_level t =
  t.conflict_facts <- None;
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
  t.conflict_facts <- None;
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
