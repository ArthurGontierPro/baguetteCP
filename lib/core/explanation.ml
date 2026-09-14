(* Explanations: why a value was removed, in a form the proof layer can render.

   This is the design centre of the project. Read docs/SPEC.md section 3.3 and
   docs/ARCHITECTURE.md section 4 before changing it, and note that decision D-0003
   (what "higher-order explanation" means here) is still OPEN and will reshape this type.

   [Deferred] exists because most prunings are never asked for a reason. Computing a full
   explanation eagerly for every pruning is the standard way to make a proof-logging
   solver an order of magnitude slower than its unlogged sibling. Forcing memoises: a
   reason can be demanded more than once during conflict analysis. *)

module Lit = Baguette_proof.Lit

type t =
  | Trivial
      (* The model constraint itself justifies this; no derivation needed. *)
  | Clause of Lit.t list
      (* These literals together imply the pruning. Renders to rup. *)
  | Linear of (int * Lit.t) list * int
      (* sum a_i l_i >= b. Renders to pol over the model constraint. *)
  | Cut of t * t * int * int
      (* Linear combination: c1 * e1 + c2 * e2, the cutting-planes workhorse. *)
  | Deferred of thunk
      (* Computed only if actually needed. *)

and thunk = { mutable forced : t option; compute : unit -> t }

let trivial = Trivial
let clause lits = Clause lits
let linear terms rhs = Linear (terms, rhs)
let cut e1 e2 c1 c2 = Cut (e1, e2, c1, c2)
let deferred compute = Deferred { forced = None; compute }

(* Force to a non-deferred head. Nested [Deferred] is allowed: a thunk may return another
   thunk, and memoisation records the fully forced result at each level. *)
let rec force = function
  | Deferred th -> (
      match th.forced with
      | Some e -> e
      | None ->
          let e = force (th.compute ()) in
          th.forced <- Some e;
          e)
  | e -> e

(* Literals mentioned by an explanation, after forcing. Used by conflict analysis. *)
let rec lits e =
  match force e with
  | Trivial -> []
  | Clause ls -> ls
  | Linear (terms, _) -> List.map snd terms
  | Cut (a, b, _, _) -> lits a @ lits b
  | Deferred _ -> assert false (* force returns a non-deferred head *)

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
