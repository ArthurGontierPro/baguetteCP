(* Explanations: why a value was removed, in a form the proof layer can render.

   This is the design centre of the project. Read docs/SPEC.md section 3.3 and
   docs/ARCHITECTURE.md section 4 before changing it, and note that decision D-0003
   (what "higher-order explanation" means here) is still OPEN and will reshape this type.
   Do not add a constructor without a decision record, and when one is added, extend
   [force], [lits] and [to_string] rather than adding a catch-all case - the
   exhaustiveness warning is what will find every site that needs updating.

   [Deferred] exists because most prunings are never asked for a reason. Computing a full
   explanation eagerly for every pruning is the standard way to make a proof-logging
   solver an order of magnitude slower than its unlogged sibling. Forcing memoises: a
   reason can be demanded more than once during conflict analysis.

   -------------------------------------------------------------------------------
   M1-T12 / docs/DECISIONS.md D-0013: [Model_row], [Combine], [Weaken]
   -------------------------------------------------------------------------------

   D-0013 verified, against veripb 2.2.2, the actual derivation a bounds conflict at
   the root needs: weaken every *other* variable out of the model row with literal
   axioms (sound per D-0009 -- an axiom can never assert a bound, but it *can* weaken
   one away), or, where that variable sits at a bound some earlier step already
   derived, cite that derivation's id instead; then divide by the pushed variable's
   own coefficient. [Trivial]/[Linear]/[Cut] cannot say this:

     - [Linear] carries literals but no constraint id, so it cannot cite "the id that
       already established this bound" (D-0009).
     - [Cut] has two multipliers and no divisor, so it cannot express the division
       D-0010/D-0011 left out.
     - Nothing distinguishes "still at the declared bound, weaken it away" from
       "sitting at a bound some earlier step derived, cite that id" -- D-0013's whole
       point is that these are different operations with a different source.

   [Combine (summands, divisor)] is one [pol] step: every summand added, then (unless
   [divisor = 1]) divided. A [summand] is either [Term (c, e)] -- recursively emit
   [e], the way [Cut] already does, and cite its id scaled by [c] -- or [Weaken lits]
   -- a sum of individually-scaled *literal axioms*, which cancel a term whose
   variable is still sitting at its declared bound. [Weaken] is not a [t]: it is not
   a value anyone can point at and say "this holds", only a piece of arithmetic valid
   solely inside a [Combine]'s sum, which is exactly the D-0009 distinction made
   structural instead of a convention someone has to remember.

   [Model_row] exists because [Trivial] is not enough once a [Combine] cites an
   explanation another propagator *instance* built: [Trivial] means "whatever
   [ctx.model_id] currently points at" (docs/core/justify.ml), a single ambient
   pointer good for exactly one row at a time. D-0011 already found this: two
   propagator instances justify against two different rows, and nothing on the trail
   says which one produced a given pruning. A [Combine] can legitimately hold, in one
   tree, an explanation this instance built (whose own base is its own row) *and* a
   cited explanation another instance built earlier (whose base is *that* instance's
   row) -- two different rows, resolved simultaneously, which one mutable ambient
   pointer cannot do. [Model_row id] names the row explicitly and renders to [id]
   directly, no lookup, so each instance's own base survives being embedded inside
   someone else's derivation. [Trivial] is kept for every existing single-row use
   (decisions' placeholder pushes in search.ml, the pre-D-0013 [Linear]/[Cut] shape
   test_core.ml still exercises) -- it is still correct there, just not general
   enough for a cross-instance [Combine]. *)

module Lit = Baguette_proof.Lit

type t =
  | Trivial (* The model constraint itself justifies this; no derivation needed. *)
  | Clause of Lit.t list (* These literals together imply the pruning. Renders to rup. *)
  | Linear of (int * Lit.t) list * int
    (* sum a_i l_i >= b. Renders to pol over the model constraint. *)
  | Cut of t * t * int * int
    (* Linear combination: c1 * e1 + c2 * e2, the cutting-planes workhorse. Kept for
       existing single-row uses; D-0013's cross-row, divided combination is
       [Combine], below -- see the module header. *)
  | Model_row of int
    (* The id (a Baguette_proof.Writer.cid) of a model constraint already loaded by
       the checker's [f] rule, named explicitly rather than resolved through
       whatever [ctx.model_id] happens to point at right now. See the module
       header. *)
  | Combine of summand list * int
    (* sum of summands, then divide by the int (>= 1; 1 means "do not divide" --
       Justify skips emitting a division step rather than a no-op "1 d"). One
       [Combine] is one [pol] step (D-0013). *)
  | Deferred of thunk
(* Computed only if actually needed. *)

and summand =
  | Term of int * t
    (* coeff * (recursively emit this explanation and cite its resulting id). *)
  | Weaken of (int * Lit.t) list
    (* sum of coeff_i * axiom(lit_i): weakens a variable's contribution out of the
       row it is added to. See the module header -- never meaningful outside a
       [Combine]'s summand list. *)

and thunk = { mutable forced : t option; mutable compute : unit -> t }

type expl = t

let trivial = Trivial
let clause lits = Clause lits
let linear terms rhs = Linear (terms, rhs)
let cut e1 e2 c1 c2 = Cut (e1, e2, c1, c2)
let model_row id = Model_row id

let term coeff e = Term (coeff, e)
let weaken lits = Weaken lits

let combine summands divisor =
  if divisor < 1 then invalid_arg "Explanation.combine: divisor must be >= 1";
  (match summands with
  | [] -> invalid_arg "Explanation.combine: summands must be non-empty"
  | _ -> ());
  Combine (summands, divisor)

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
    | Model_row _ -> ()
    | Clause ls -> List.iter add ls
    | Linear (terms, _) -> List.iter (fun (_, l) -> add l) terms
    | Cut (a, b, _, _) ->
        go a;
        go b
    | Combine (summands, _) -> List.iter go_summand summands
    | Deferred _ -> assert false (* force returns a non-deferred head *)
  and go_summand = function
    | Term (_, e) -> go e
    | Weaken lits -> List.iter (fun (_, l) -> add l) lits
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
  | Model_row id -> Printf.sprintf "model_row(%d)" id
  | Combine (summands, divisor) ->
      Printf.sprintf "combine(%s)%s"
        (String.concat " + " (List.map summand_to_string summands))
        (if divisor = 1 then "" else Printf.sprintf " / %d" divisor)
  | Deferred { forced = Some e; _ } -> "deferred[" ^ to_string e ^ "]"
  | Deferred { forced = None; _ } -> "deferred[?]"

and summand_to_string = function
  | Term (c, e) -> Printf.sprintf "%d*%s" c (to_string e)
  | Weaken lits ->
      "weaken("
      ^ String.concat " " (List.map (fun (c, l) -> Printf.sprintf "%d*%s" c (Lit.to_string l)) lits)
      ^ ")"

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
