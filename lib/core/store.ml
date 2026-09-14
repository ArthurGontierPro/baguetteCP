(* The backtrackable domain store.

   Mutation is undone by replaying a trail in reverse. Decision levels are marks into
   that trail. Every entry carries the explanation of the change that made it, so
   conflict analysis can walk backwards through reasons (invariant I-T3).

   Invariant I-T1 is the one worth testing directly: backtrack_to restores every domain
   to exactly its state when the level was opened. *)

type entry = { var : Var.t; old : Domain.t; why : Explanation.t }

type t = {
  domains : Domain.t array;
  names : string array;
  mutable trail : entry list;
  mutable trail_len : int;
  mutable levels : int list;  (* trail_len when each open level began *)
}

type outcome =
  | Unchanged
  | Changed
  | Conflict of Explanation.t

let create ~names ~domains =
  if Array.length names <> Array.length domains then
    invalid_arg "Store.create: names and domains differ in length";
  { domains = Array.copy domains;
    names = Array.copy names;
    trail = [];
    trail_len = 0;
    levels = [] }

let n_vars t = Array.length t.domains
let get t v = t.domains.(Var.to_int v)
let name t v = t.names.(Var.to_int v)
let level t = List.length t.levels

(* Apply a Domain.result, recording the old value so it can be undone.
   Every path through here takes an explanation: invariant I-P4 is enforced by this
   signature, so do not add an optional reason argument. *)
let apply t v (r : Domain.result) why =
  match r with
  | Domain.Unchanged -> Unchanged
  | Domain.Failed -> Conflict why
  | Domain.Changed d ->
      let i = Var.to_int v in
      t.trail <- { var = v; old = t.domains.(i); why } :: t.trail;
      t.trail_len <- t.trail_len + 1;
      t.domains.(i) <- d;
      Changed

let set_lo t v bound why = apply t v (Domain.set_lo (get t v) bound) why
let set_hi t v bound why = apply t v (Domain.set_hi (get t v) bound) why
let remove t v value why = apply t v (Domain.remove (get t v) value) why
let fix t v value why = apply t v (Domain.fix (get t v) value) why

let new_level t = t.levels <- t.trail_len :: t.levels

let rec undo_to t target =
  if t.trail_len > target then
    match t.trail with
    | [] -> assert false
    | e :: rest ->
        t.domains.(Var.to_int e.var) <- e.old;
        t.trail <- rest;
        t.trail_len <- t.trail_len - 1;
        undo_to t target

let backtrack t =
  match t.levels with
  | [] -> invalid_arg "Store.backtrack: already at level 0"
  | mark :: rest ->
      undo_to t mark;
      t.levels <- rest

let rec backtrack_to t target_level =
  if level t > target_level then begin
    backtrack t;
    backtrack_to t target_level
  end

let all_fixed t = Array.for_all Domain.is_fixed t.domains

(* The reasons on the trail, most recent first. Conflict analysis walks this. *)
let trail_entries t = t.trail
