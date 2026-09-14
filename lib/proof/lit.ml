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
