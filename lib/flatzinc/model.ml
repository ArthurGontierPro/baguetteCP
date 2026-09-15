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

(* How the values of an output item are to be *written*. SPEC 2.2 prints a `bool` as
   false/true and an integer as a decimal, and the only thing that says which is the
   declaration the `output_var` / `output_array` annotation sits on — an [operand] cannot
   say: [Const 1] is the same word for `1` and for `true`, and the builder folds a bool
   parameter to [Const 1] while resolving names.

   So the type travels *with the output item*, recorded by the builder from the
   declaration's base type at the moment the item is created. It is not re-derived at
   print time from the operand (impossible) nor from the referenced variable's domain
   (possible for [Var], but then [Const] would still have nowhere to get it from, and the
   two cases would print by two different rules). One declaration, one type, one rule. *)
type out_ty = Obool | Oint

(* What SPEC 2.2 has to print. Arrays keep their index ranges so the standard FlatZinc
   `array1d(1..2, [...])` output can be reproduced, and carry a single [out_ty]: an
   array declaration has one base type, so all its elements print the same way. *)
type output_item =
  | Out_var of string * out_ty * operand
  | Out_array of string * (int * int) list * out_ty * operand list

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

(* ------------------------------------------------------- independent solution check *)

(* I-S1: "Every solution printed satisfies every constraint — re-checked independently by
   [Model.check_assignment], not by trusting the propagators."

   This is the oracle, so it is written to be *obviously* right rather than fast or
   clever. It re-reads the model the front end built and re-evaluates it from scratch:
   no domain store, no propagator, no encoding, nothing the solver also uses. The moment
   it shares code with the engine it stops being independent and starts agreeing with the
   engine's bugs.

   Two consequences worth keeping:

   - It evaluates all seven constraint kinds, including [Int_lin_ne] and [Int_ne], for
     which no propagator exists yet. A hole here would be a hole exactly where the solver
     already has one, which is the one place a checker must not be silent.
   - It checks the *declared* domains too, not only the constraints. A solution that
     assigns 7 to a `var 1..3` violates the model just as surely as one that breaks a
     linear constraint, and a bug in the store is more likely to produce the former. *)

let in_domain dom v =
  match dom with
  | Dbool -> v = 0 || v = 1
  | Drange (l, u) -> l <= v && v <= u
  | Dset ns -> List.mem v ns

let check_assignment (t : t) (values : int array) : bool =
  let n = Array.length t.vars in
  if Array.length values <> n then
    invalid_arg
      (Printf.sprintf "Model.check_assignment: expected %d values, got %d" n
         (Array.length values));
  let value = function Const c -> c | Var i -> values.(i) in
  let sum terms = List.fold_left (fun acc (c, i) -> acc + (c * values.(i))) 0 terms in
  let holds (c : constr) =
    match c.k with
    | Int_lin_le (ts, rhs) -> sum ts <= rhs
    | Int_lin_eq (ts, rhs) -> sum ts = rhs
    | Int_lin_ne (ts, rhs) -> sum ts <> rhs
    | Int_le (a, b) -> value a <= value b
    | Int_lt (a, b) -> value a < value b
    | Int_eq (a, b) -> value a = value b
    | Int_ne (a, b) -> value a <> value b
  in
  let domains_ok =
    let ok = ref true in
    Array.iteri (fun i v -> if not (in_domain v.v_dom values.(i)) then ok := false) t.vars;
    !ok
  in
  domains_ok && List.for_all holds t.constraints
