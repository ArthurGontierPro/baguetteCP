(* The backtrackable domain store.

   Mutation is undone by replaying a trail in reverse. Decision levels are marks into
   that trail. Every entry carries the arena index of the explanation of the change that
   made it, so conflict analysis can walk backwards through reasons (invariant I-T3).

   Invariant I-T1 is the one worth testing directly: backtrack_to restores every domain
   to exactly its state when the level was opened. The reason it holds here is that
   [Domain.t] is immutable - an entry keeps the old value, and restoring is a single
   array write with no aliasing between the saved and the current domain. *)

(* A level mark records where in the trail the level began, and where in the explanation
   arena it began: backtracking rewinds both together, which is what keeps I-T3 true
   (no trail entry survives whose reason has been dropped) and stops the arena growing
   without bound over a long search. *)
type mark = { trail_mark : int; reason_mark : int }

type entry = { var : Var.t; old : Domain.t; why : Explanation.Arena.id }

type t = {
  domains : Domain.t array;
  names : string array;
  reasons : Explanation.Arena.t;
  mutable trail : entry array;
  mutable trail_len : int;
  mutable marks : mark array;
  mutable n_levels : int;
}

type outcome =
  | Unchanged
  | Changed
  | Conflict of Explanation.t

let dummy_entry =
  { var = Var.of_int 0; old = Domain.singleton 0; why = Explanation.Arena.null }

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
  }

let n_vars t = Array.length t.domains
let get t v = t.domains.(Var.to_int v)
let name t v = t.names.(Var.to_int v)
let level t = t.n_levels
let trail_length t = t.trail_len
let reasons t = t.reasons

(* ------------------------------------------------------------- trail growth *)

let push_entry t e =
  if t.trail_len = Array.length t.trail then begin
    let bigger = Array.make (2 * Array.length t.trail) dummy_entry in
    Array.blit t.trail 0 bigger 0 t.trail_len;
    t.trail <- bigger
  end;
  t.trail.(t.trail_len) <- e;
  t.trail_len <- t.trail_len + 1

let push_mark t m =
  if t.n_levels = Array.length t.marks then begin
    let bigger = Array.make (2 * Array.length t.marks) dummy_mark in
    Array.blit t.marks 0 bigger 0 t.n_levels;
    t.marks <- bigger
  end;
  t.marks.(t.n_levels) <- m;
  t.n_levels <- t.n_levels + 1

(* ----------------------------------------------------------------- mutation *)

(* Apply a Domain.result, recording the old value so it can be undone.
   Every path through here takes an explanation: invariant I-P4 is enforced by this
   signature, so do not add an optional reason argument. *)
let apply t v (r : Domain.result) why =
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
      push_entry t { var = v; old; why };
      t.domains.(i) <- d;
      Changed

let set_lo t v bound why = apply t v (Domain.set_lo (get t v) bound) why
let set_hi t v bound why = apply t v (Domain.set_hi (get t v) bound) why
let remove t v value why = apply t v (Domain.remove (get t v) value) why
let fix t v value why = apply t v (Domain.fix (get t v) value) why

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
  let ok_domains =
    Array.for_all (fun d -> Domain.lo d <= Domain.hi d) t.domains
  in
  ok_marks && !ok_reasons && ok_domains

let to_string t =
  String.concat " "
    (Array.to_list
       (Array.mapi
          (fun i d -> Printf.sprintf "%s=%s" t.names.(i) (Domain.to_string d))
          t.domains))
