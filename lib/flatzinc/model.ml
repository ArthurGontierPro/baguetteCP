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
  (* ------------------------------------------------------------------ M2, Booleans.

     Every operand below is Boolean: a `var bool` (whose domain is [Dbool], i.e. the
     integers {0, 1} -- docs/DECISIONS.md D-0007) or a folded constant 0/1. The builder
     folds `true`/`false` and bool parameters to [Const 1]/[Const 0] while resolving
     names, exactly as it does for integers, so nothing here needs a second operand
     type; lib/flatzinc/compile.ml checks that each operand really is Boolean and says
     so with a position when it is not.

     [Bool2int] is the exception, and it is the seam the whole Boolean vertical turns
     on: its *first* operand is Boolean and its second is an ordinary integer operand. *)
  | Bool_clause of operand list * operand list
    (* `bool_clause(pos, neg)`: the disjunction
         pos_1 \/ ... \/ pos_p \/ ~neg_1 \/ ... \/ ~neg_q.
       Either list may be empty; both empty is the false clause, which is a legal
       (unsatisfiable) model and not an error -- see compile.ml's ground-constraint
       argument. *)
  | Array_bool_or of operand list * operand
    (* `array_bool_or(as, r)`: r <-> (as_1 \/ ... \/ as_n). Reified, both ways; an
       empty [as] forces r false. *)
  | Array_bool_and of operand list * operand
    (* `array_bool_and(as, r)`: r <-> (as_1 /\ ... /\ as_n). An empty [as] forces r
       true. *)
  | Bool2int of operand * operand
    (* `bool2int(b, x)`: x = b, with b Boolean and x an integer operand. *)
  | Bool_eq of operand * operand (* `bool_eq(a, b)`: a <-> b *)
  | Bool_not of operand * operand (* `bool_not(a, b)`: a <-> ~b *)

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
  | Bool_clause (ps, ns) ->
      Printf.sprintf "bool_clause([%s], [%s])"
        (String.concat ", " (List.map (string_of_operand t) ps))
        (String.concat ", " (List.map (string_of_operand t) ns))
  | Array_bool_or (xs, r) ->
      Printf.sprintf "%s <-> or([%s])" (string_of_operand t r)
        (String.concat ", " (List.map (string_of_operand t) xs))
  | Array_bool_and (xs, r) ->
      Printf.sprintf "%s <-> and([%s])" (string_of_operand t r)
        (String.concat ", " (List.map (string_of_operand t) xs))
  | Bool2int (b, x) ->
      Printf.sprintf "%s = bool2int(%s)" (string_of_operand t x) (string_of_operand t b)
  | Bool_eq (a, b) ->
      Printf.sprintf "%s <-> %s" (string_of_operand t a) (string_of_operand t b)
  | Bool_not (a, b) ->
      Printf.sprintf "%s <-> not %s" (string_of_operand t a) (string_of_operand t b)

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

   - It evaluates **every** constraint kind [cstr] has, and the [holds] match below is
     deliberately exhaustive rather than ending in a catch-all: adding a constructor
     without teaching the oracle about it is then a compile error instead of a
     constraint family the oracle silently reports as satisfied. That is not a
     hypothetical -- the rule was written when [Int_lin_ne] and [Int_ne] had no
     propagator, so a hole here would have been a hole exactly where the solver already
     had one, and the M2 Boolean row was added to this match in the same commit as its
     propagators for the same reason.
   - Booleans are checked as Booleans. [truth] refuses a value that is neither 0 nor 1
     rather than treating everything non-zero as true: a `var bool` holding 2 means the
     store or a propagator is broken, and answering "satisfied" there would launder the
     bug into a plausible-looking solution, which is the one thing I-S1 exists to stop.
     lib/flatzinc/output.ml's [bool_string] refuses the same value for the same reason.
   - It shares no arithmetic with the Boolean propagators, because there is none to
     share: nothing in the M2 row multiplies, so M1-T33's complaint about this oracle
     (D-0029's consequence list: it wraps the way its subject wraps, so it is not
     independent where overflow is concerned) does not reach the Boolean constraints.
     It still stands, unchanged, for the four integer linear kinds.
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
  (* A Boolean operand, read as a Boolean. See the header on why a third value is an
     error and not a falsehood. *)
  let truth op =
    match value op with
    | 0 -> false
    | 1 -> true
    | n ->
        invalid_arg
          (Printf.sprintf
             "Model.check_assignment: a Boolean operand has the non-Boolean value %d" n)
  in
  let holds (c : constr) =
    match c.k with
    | Int_lin_le (ts, rhs) -> sum ts <= rhs
    | Int_lin_eq (ts, rhs) -> sum ts = rhs
    | Int_lin_ne (ts, rhs) -> sum ts <> rhs
    | Int_le (a, b) -> value a <= value b
    | Int_lt (a, b) -> value a < value b
    | Int_eq (a, b) -> value a = value b
    | Int_ne (a, b) -> value a <> value b
    (* The M2 Boolean row, written from the FlatZinc definition of each builtin and
       from nothing in lib/core/prop/: a disjunction is a disjunction, and the two
       reified forms are re-evaluated as the equivalences they are, in both
       directions. An empty [xs] is the identity of its connective -- `or([])` is
       false and `and([])` is true -- which [List.exists] and [List.for_all] already
       give, so there is no empty-array case to get wrong. *)
    | Bool_clause (ps, ns) ->
        List.exists truth ps || List.exists (fun o -> not (truth o)) ns
    | Array_bool_or (xs, r) -> truth r = List.exists truth xs
    | Array_bool_and (xs, r) -> truth r = List.for_all truth xs
    | Bool2int (b, x) -> value x = if truth b then 1 else 0
    | Bool_eq (a, b) -> truth a = truth b
    | Bool_not (a, b) -> truth a <> truth b
  in
  let domains_ok =
    let ok = ref true in
    Array.iteri (fun i v -> if not (in_domain v.v_dom values.(i)) then ok := false) t.vars;
    !ok
  in
  domains_ok && List.for_all holds t.constraints
