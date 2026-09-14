(* The front end's output: a flat, solver-agnostic description of a FlatZinc model.

   This type is deliberately defined *here* and not in Baguette_core: the dependency
   direction in docs/ARCHITECTURE.md is `flatzinc -> core`, but core is being rewritten
   in parallel (M1-T1..T5) and the front end should not be blocked on its API settling.
   Wiring `Model.t` into the engine is a later task; when it happens, the translation
   lives on the core side of the boundary, not here. *)

type domain =
  | Dbool (* a `var bool`: treated as 0/1 *)
  | Drange of int * int (* inclusive *)
  | Dset of int list (* sorted, duplicate-free, non-empty *)

type var = { v_name : string; v_dom : domain; v_pos : Pos.t }

(* A constraint argument after name resolution: either a literal integer (a parameter,
   a bool, or an inline constant) or an index into [t.vars]. *)
type operand = Const of int | Var of int

(* Linear constraints are normalised: constant entries of the FlatZinc variable array are
   folded into the right-hand side, so [terms] only ever mentions real variables.
   A term list may repeat a variable index; propagators are free to merge. *)
type cstr =
  | Int_lin_le of (int * int) list * int (* sum coeff*x_i <= rhs *)
  | Int_lin_eq of (int * int) list * int (* sum coeff*x_i  = rhs *)
  | Int_lin_ne of (int * int) list * int (* sum coeff*x_i <> rhs *)
  | Int_le of operand * operand (* a <= b *)
  | Int_lt of operand * operand (* a <  b *)
  | Int_eq of operand * operand (* a  = b *)
  | Int_ne of operand * operand (* a <> b *)

type constr = { k : cstr; c_pos : Pos.t }
type var_choice = Input_order | First_fail
type val_choice = Indomain_min | Indomain_max
type search = Int_search of int list * var_choice * val_choice | Seq of search list
type objective = Satisfy | Minimize of operand | Maximize of operand

(* What SPEC 2.2 has to print. Arrays keep their index ranges so the standard FlatZinc
   `array1d(1..2, [...])` output can be reproduced. *)
type output_item =
  | Out_var of string * operand
  | Out_array of string * (int * int) list * operand list

type t = {
  vars : var array;
  constraints : constr list;
  objective : objective;
  search : search list; (* [] means: use the default of SPEC 3.4 *)
  output : output_item list;
}

let nvars t = Array.length t.vars
let var t i = t.vars.(i)

let find_var t name =
  let n = Array.length t.vars in
  let rec go i =
    if i >= n then None
    else if String.equal t.vars.(i).v_name name then Some i
    else go (i + 1)
  in
  go 0

let string_of_domain = function
  | Dbool -> "bool"
  | Drange (l, u) -> Printf.sprintf "%d..%d" l u
  | Dset ns -> "{" ^ String.concat "," (List.map string_of_int ns) ^ "}"

let string_of_operand t = function
  | Const n -> string_of_int n
  | Var i ->
      if i >= 0 && i < Array.length t.vars then t.vars.(i).v_name
      else Printf.sprintf "<var %d>" i

let string_of_terms t terms =
  String.concat " + "
    (List.map
       (fun (c, i) -> Printf.sprintf "%d*%s" c (string_of_operand t (Var i)))
       terms)

let string_of_cstr t = function
  | Int_lin_le (ts, r) -> Printf.sprintf "%s <= %d" (string_of_terms t ts) r
  | Int_lin_eq (ts, r) -> Printf.sprintf "%s = %d" (string_of_terms t ts) r
  | Int_lin_ne (ts, r) -> Printf.sprintf "%s != %d" (string_of_terms t ts) r
  | Int_le (a, b) ->
      Printf.sprintf "%s <= %s" (string_of_operand t a) (string_of_operand t b)
  | Int_lt (a, b) ->
      Printf.sprintf "%s < %s" (string_of_operand t a) (string_of_operand t b)
  | Int_eq (a, b) ->
      Printf.sprintf "%s = %s" (string_of_operand t a) (string_of_operand t b)
  | Int_ne (a, b) ->
      Printf.sprintf "%s != %s" (string_of_operand t a) (string_of_operand t b)

let to_string t =
  let b = Buffer.create 256 in
  Array.iter
    (fun v ->
      Buffer.add_string b
        (Printf.sprintf "var %s: %s\n" (string_of_domain v.v_dom) v.v_name))
    t.vars;
  List.iter
    (fun c ->
      Buffer.add_string b (Printf.sprintf "constraint %s\n" (string_of_cstr t c.k)))
    t.constraints;
  Buffer.add_string b
    (match t.objective with
    | Satisfy -> "solve satisfy\n"
    | Minimize o -> Printf.sprintf "solve minimize %s\n" (string_of_operand t o)
    | Maximize o -> Printf.sprintf "solve maximize %s\n" (string_of_operand t o));
  Buffer.contents b
