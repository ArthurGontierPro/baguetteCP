(* Explanations: why a value was removed, in a form the proof layer can render.

   This is the design centre of the project. Read docs/SPEC.md section 3.3 and
   docs/ARCHITECTURE.md section 4 before changing it, and note that decision D-0003
   (what "higher-order explanation" means here) is still OPEN and will reshape this type.
   The constructors below are exactly the ones docs/ARCHITECTURE.md section 4 lists; do
   not add to them without a decision record, and when one is added, extend [force],
   [lits] and [to_string] rather than adding a catch-all case - the exhaustiveness
   warning is what will find every site that needs updating.

   [Deferred] exists because most prunings are never asked for a reason. Computing a full
   explanation eagerly for every pruning is the standard way to make a proof-logging
   solver an order of magnitude slower than its unlogged sibling. Forcing memoises: a
   reason can be demanded more than once during conflict analysis. *)

module Lit = Baguette_proof.Lit

type t =
  | Trivial (* The model constraint itself justifies this; no derivation needed. *)
  | Clause of Lit.t list (* These literals together imply the pruning. Renders to rup. *)
  | Linear of (int * Lit.t) list * int
    (* sum a_i l_i >= b. Renders to pol over the model constraint. *)
  | Cut of t * t * int * int
    (* Linear combination: c1 * e1 + c2 * e2, the cutting-planes workhorse. *)
  | Deferred of thunk
(* Computed only if actually needed. *)

and thunk = { mutable forced : t option; mutable compute : unit -> t }

type expl = t

let trivial = Trivial
let clause lits = Clause lits
let linear terms rhs = Linear (terms, rhs)
let cut e1 e2 c1 c2 = Cut (e1, e2, c1, c2)
let deferred compute = Deferred { forced = None; compute }

(* Force to a non-deferred head. Nested [Deferred] is allowed: a thunk may return another
   thunk, and memoisation records the fully forced result at each level. The closure is
   dropped once forced so that whatever it captured - propagator state, coefficient
   arrays - becomes collectable; a memoised thunk must never be re-run anyway. *)
let rec force = function
  | Deferred th -> (
      match th.forced with
      | Some e -> e
      | None ->
          let e = force (th.compute ()) in
          th.forced <- Some e;
          th.compute <- (fun () -> e);
          e)
  | e -> e

let is_forced = function Deferred { forced = None; _ } -> false | _ -> true

(* The forced value if it is already available, without running any thunk. Useful for
   debug printing, which must not have side effects on the memo table. *)
let peek = function Deferred th -> th.forced | e -> Some e

(* Literals mentioned by an explanation, after forcing, without duplicates. Conflict
   analysis walks this. *)
let lits e =
  let seen = Hashtbl.create 16 in
  let acc = ref [] in
  let add l =
    if not (Hashtbl.mem seen l) then (
      Hashtbl.add seen l ();
      acc := l :: !acc)
  in
  let rec go e =
    match force e with
    | Trivial -> ()
    | Clause ls -> List.iter add ls
    | Linear (terms, _) -> List.iter (fun (_, l) -> add l) terms
    | Cut (a, b, _, _) ->
        go a;
        go b
    | Deferred _ -> assert false (* force returns a non-deferred head *)
  in
  go e;
  List.rev !acc

let rec to_string e =
  match e with
  | Trivial -> "trivial"
  | Clause ls -> "clause(" ^ String.concat " " (List.map Lit.to_string ls) ^ ")"
  | Linear (terms, rhs) ->
      Printf.sprintf "linear(%s >= %d)"
        (String.concat " "
           (List.map (fun (a, l) -> Printf.sprintf "%+d %s" a (Lit.to_string l)) terms))
        rhs
  | Cut (a, b, c1, c2) ->
      Printf.sprintf "cut(%d*%s + %d*%s)" c1 (to_string a) c2 (to_string b)
  | Deferred { forced = Some e; _ } -> "deferred[" ^ to_string e ^ "]"
  | Deferred { forced = None; _ } -> "deferred[?]"

(* ------------------------------------------------------------------- arena *)

(* Explanations live in a side arena and the trail stores an index into it
   (docs/ARCHITECTURE.md section 3): trail records stay small and uniform, and
   invariant I-T3 - every trail entry's explanation index resolves - becomes something
   that can be checked with a bounds test.

   The arena is a stack. [truncate] is how backtracking discards the reasons for the
   prunings it is undoing; it is safe because nothing outside the trail holds an [id],
   and anything that wants to survive a backtrack (a learned clause) holds the forced
   [expl] value itself, which the GC keeps alive independently. *)
module Arena = struct
  type id = int
  type t = { mutable items : expl array; mutable len : int }

  (* Not a valid index; [get] on it raises. Lets containers hold a "no reason yet". *)
  let null : id = -1

  let create ?(capacity = 256) () =
    { items = Array.make (Stdlib.max 1 capacity) Trivial; len = 0 }

  let length a = a.len
  let mem a (i : id) = i >= 0 && i < a.len

  let grow a =
    let bigger = Array.make (Stdlib.max 1 (2 * Array.length a.items)) Trivial in
    Array.blit a.items 0 bigger 0 a.len;
    a.items <- bigger

  let add a (e : expl) : id =
    if a.len = Array.length a.items then grow a;
    a.items.(a.len) <- e;
    a.len <- a.len + 1;
    a.len - 1

  let get a (i : id) : expl =
    if not (mem a i) then
      invalid_arg
        (Printf.sprintf "Explanation.Arena.get: %d out of range (len %d)" i a.len);
    a.items.(i)

  (* Force in place, so the memoised result is what the arena holds from now on. *)
  let force_at a (i : id) : expl =
    let e = force (get a i) in
    a.items.(i) <- e;
    e

  let truncate a n =
    if n < 0 then invalid_arg "Explanation.Arena.truncate: negative length";
    if n < a.len then (
      (* Drop the references so the explanations, and anything their thunks captured,
         become collectable. *)
      Array.fill a.items n (a.len - n) Trivial;
      a.len <- n)

  let clear a = truncate a 0
end
