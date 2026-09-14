(* Literals of the pseudo-Boolean encoding.

   Naming here is normative: see docs/PROOF-FORMAT.md section 3. Proofs are read by
   humans debugging rejected steps, and grep-ability against the FlatZinc model is the
   whole point of a stable scheme. Do not introduce a second one. *)

type pbvar =
  | Ge of string * int  (* x_ge_v : x >= v, the order encoding *)
  | Eq of string * int  (* x_eq_v : x = v,  the direct encoding *)

type t = { v : pbvar; positive : bool }

let pos v = { v; positive = true }
let neg v = { v; positive = false }
let negate l = { l with positive = not l.positive }

(* OPB names allow no '-', so negative values get an 'm' prefix. *)
let int_suffix v = if v < 0 then "m" ^ string_of_int (-v) else string_of_int v

let sanitize name =
  String.map
    (function ('a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_') as c -> c | _ -> '_')
    name

let var_name = function
  | Ge (x, v) -> Printf.sprintf "%s_ge_%s" (sanitize x) (int_suffix v)
  | Eq (x, v) -> Printf.sprintf "%s_eq_%s" (sanitize x) (int_suffix v)

let to_string l =
  if l.positive then var_name l.v else "~" ^ var_name l.v

(* x >= v, as a literal. *)
let ge x v = pos (Ge (x, v))

(* x <= v, which the order encoding expresses as ~(x >= v+1). *)
let le x v = neg (Ge (x, v + 1))

let eq x v = pos (Eq (x, v))
let ne x v = neg (Eq (x, v))

(* ---------------------------------------------------------------------------
   Additions (M1-T4). Everything above this line is frozen: lib/core/explanation.ml
   compiles against it. Add here, do not rewrite above.
   --------------------------------------------------------------------------- *)

(* A FlatZinc [var bool] is order-encoded on [0, 1]: there is exactly one Boolean
   [b_ge_1], and "b is true" is that literal. Deliberately no third constructor —
   a second naming scheme is exactly what docs/PROOF-FORMAT.md section 3 forbids. *)
let bool_true x = ge x 1
let bool_false x = le x 0

let var_compare a b =
  match (a, b) with
  | Ge (x, i), Ge (y, j) | Eq (x, i), Eq (y, j) ->
      let c = String.compare x y in
      if c <> 0 then c else Int.compare i j
  | Ge _, Eq _ -> -1
  | Eq _, Ge _ -> 1

let var_equal a b = var_compare a b = 0

let compare a b =
  let c = var_compare a.v b.v in
  if c <> 0 then c else Bool.compare a.positive b.positive

let equal a b = compare a b = 0

(* The FlatZinc identifier a literal is about, before sanitisation. *)
let owner = function Ge (x, _) -> x | Eq (x, _) -> x
let value = function Ge (_, v) -> v | Eq (_, v) -> v
let is_order = function Ge _ -> true | Eq _ -> false
let is_direct = function Ge _ -> false | Eq _ -> true

(* True when [sanitize] had to rewrite the identifier, i.e. the .opb name and the
   FlatZinc name differ and the mapping must be dumped as a comment. *)
let is_renamed x = String.equal (sanitize x) x = false

let pp fmt l = Format.pp_print_string fmt (to_string l)
