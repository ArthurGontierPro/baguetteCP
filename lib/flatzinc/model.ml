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
(* The auxiliary Booleans one M4 arithmetic constraint needs, as indices into [vars].

   [x_sign], when present, is defined as `b <-> x >= 0` and splits the sign of the
   first operand; it is absent when the declared domain of x settles the sign on its
   own. [y_ge] maps a value v to the index of the Boolean defined as `b_v <-> y >= v`,
   for each v strictly inside the declared domain of the case variable y; the two ends
   need no Boolean. [Int_abs] uses only [x_sign] and always has [y_ge = []]. *)
type aux = { x_sign : int option; y_ge : (int * int) list }

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
  (* ------------------------------------------------------- M3, reified forms.

     The reifier (the last operand of each) is Boolean; the constrained operands are
     ordinary integers. SPEC 2.1's M3 row is exactly these four, and they share one
     dispatcher on the solver side (lib/core/prop/reif.ml, roadmap M3-T4), so the two
     comparison forms keep the two-operand shape the unreified builtins have rather
     than being normalised to linear terms here -- compile.ml does that once, in the
     one place that also posts the rows. *)
  | Int_lin_le_reif of (int * int) list * int * operand
    (* `int_lin_le_reif(as, bs, c, r)`: r <-> (sum as*bs <= c). *)
  | Int_le_reif of operand * operand * operand (* r <-> (a <= b) *)
  | Int_eq_reif of operand * operand * operand (* r <-> (a  = b) *)
  | Int_ne_reif of operand * operand * operand (* r <-> (a <> b) *)
  (* ------------------------------------------------- M4, the arithmetic family.

     `int_times(x, y, z)`: x * y = z. `int_div(x, y, q)`: q = x div y, truncating
     toward zero, with y = 0 simply unsupported (docs/SPEC.md 2.1, D-0033).
     `int_abs(x, z)`: z = |x|.

     Each carries an [aux] because none of the three is linear, and the case split
     that makes it linear needs Boolean variables that must exist in [vars] before
     lib/flatzinc/compile.ml builds the store -- which is why the builder creates
     them and the constraint carries their indices, rather than the compiler
     inventing them where it is too late. lib/core/prop/arith.ml's header states
     what rows they guard.

     They are kept as their own constructors rather than decomposed away here so
     that [check_assignment] below judges a solution against the RELATION, exactly
     as docs/SPEC.md states it, and not against the decomposition. An oracle that
     re-checked the decomposition would agree with a decomposition that is wrong. *)
  | Int_times of operand * operand * operand * aux
  | Int_div of operand * operand * operand * aux
  | Int_abs of operand * operand * aux
  (* M4-T1. `all_different_int(xs)`: the operands take pairwise distinct values.
     Kept as the RELATION and not as its pairwise decomposition, for the reason the
     comment above [Int_times] gives -- [check_assignment] must judge a solution
     against what SPEC 2.1 says the constraint means, never against the shape
     lib/flatzinc/compile.ml happens to post for it. *)
  | All_different of operand list
  (* M7-T16. `fzn_global_cardinality(xs, cover, counts)`: for each position i,
     `counts[i]` is exactly how many of `xs` take the value `cover[i]`. The cover is an
     array of CONSTANTS (SPEC 2.1's form, and the only one lib/core/prop/gcc.ml's model
     rows can be built over); the counts are operands, so a fixed cardinality is the
     degenerate case rather than a different constructor.

     Kept as the RELATION for the reason [All_different] is: [check_assignment] must
     judge a solution against what the constraint MEANS, never against the rows
     lib/flatzinc/compile.ml happens to post. That matters more here than anywhere,
     because the whole point of M7-T16 is that the propagator infers things the
     decomposition does not -- an oracle written against the decomposition could not
     tell a stronger propagator from a wrong one.

     Note what the relation does NOT say: nothing constrains an `xs` to take a cover
     value at all. `global_cardinality` is the OPEN form; the closed form is a different
     builtin. *)
  | Global_cardinality of operand list * int array * operand list
  (* M4-T3. `array_int_element(idx, as, c)`: [as] is a CONSTANT array and the index is
     1-BASED, so the relation is `as[idx] = c` with `idx` in `1..|as|`. The array is an
     `int array` and not an `operand list` because SPEC 2.1's M4 row admits only the
     constant form; a var-array element would be a different builtin with a different
     propagator, and representing it as operands here would let the front end build one
     nothing downstream can post.

     The index bound is PART OF THE RELATION and not a side condition: `idx = 0` does not
     make the constraint vacuous, it makes it false. [check_assignment] below says so,
     which is what stops the decomposition from being graded against itself. *)
  | Array_int_element of operand * int array * operand

type constr = { k : cstr; c_pos : Pos.t }

(* M7-T2, extended by M7-T9. The strategies docs/SPEC.md 3.4 admits, one constructor
   each. A strategy that is NOT here is refused by [Builder.search_of_annot]; there is no
   catch-all arm on either of these types anywhere, deliberately, because a catch-all is
   how an unsupported strategy becomes a wrong search instead of a refusal. *)
type var_choice = Input_order | First_fail | Smallest | Largest
type val_choice = Indomain_min | Indomain_max | Indomain_split
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
  | Int_lin_le_reif (ts, rhs, r) ->
      Printf.sprintf "%s <-> (%s <= %d)" (string_of_operand t r) (string_of_terms t ts)
        rhs
  | Int_le_reif (a, b, r) ->
      Printf.sprintf "%s <-> (%s <= %s)" (string_of_operand t r) (string_of_operand t a)
        (string_of_operand t b)
  | Int_eq_reif (a, b, r) ->
      Printf.sprintf "%s <-> (%s = %s)" (string_of_operand t r) (string_of_operand t a)
        (string_of_operand t b)
  | Int_ne_reif (a, b, r) ->
      Printf.sprintf "%s <-> (%s != %s)" (string_of_operand t r) (string_of_operand t a)
        (string_of_operand t b)
  | Int_times (a, b, c, _) ->
      Printf.sprintf "%s = %s * %s" (string_of_operand t c) (string_of_operand t a)
        (string_of_operand t b)
  | Int_div (a, b, c, _) ->
      Printf.sprintf "%s = %s div %s" (string_of_operand t c) (string_of_operand t a)
        (string_of_operand t b)
  | Int_abs (a, c, _) ->
      Printf.sprintf "%s = |%s|" (string_of_operand t c) (string_of_operand t a)
  | All_different xs ->
      Printf.sprintf "all_different([%s])"
        (String.concat ", " (List.map (string_of_operand t) xs))
  | Global_cardinality (xs, cover, counts) ->
      Printf.sprintf "global_cardinality([%s], [%s], [%s])"
        (String.concat ", " (List.map (string_of_operand t) xs))
        (String.concat ", " (List.map string_of_int (Array.to_list cover)))
        (String.concat ", " (List.map (string_of_operand t) counts))
  | Array_int_element (i, vs, c) ->
      Printf.sprintf "%s = [%s][%s]" (string_of_operand t c)
        (String.concat ", " (List.map string_of_int (Array.to_list vs)))
        (string_of_operand t i)

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
     share: nothing in the M2 row multiplies.
   - **M1-T33: the linear sum is evaluated exactly, in arbitrary precision.** It used
     to be `List.fold_left (fun acc (c, i) -> acc + (c * values.(i))) 0`, i.e. the same
     wrapping `+` and `*` as [lib/core/prop/linear.ml] and [lib/proof/encoding.ml]. On
     D-0029's overflow class that oracle agreed with the bug -- and it agreed with it
     *because* the two computed the same wrong product, which is the one failure mode
     an independent check must not have. M1-T23's compile-time cap means the native
     version cannot overflow on any model the front end accepts today, so this was not
     a live defect; it was the oracle's value that was wrong. An independent check that
     shares a failure mode with its subject is not independent, and I-S1's whole worth
     is that independence.

     [Exact] below is written here rather than taken from [Baguette_core.Checked] on
     purpose. [Checked] is what the propagators and the .opb expansion use; sharing it
     would put the oracle back inside its subject's arithmetic, just at a different
     level. It is also a different answer to a different question: [Checked] *detects*
     overflow and raises, so it can only ever say "I cannot evaluate this"; [Exact]
     has no overflow to detect and simply returns the right number, which is what an
     oracle asked "does this assignment satisfy the model" has to be able to do.

     What it is now independent of: OCaml's native integer width. No sum, product or
     comparison below can wrap, so no wrapped product in a propagator or in an .opb row
     can be confirmed by this function.

     What it still shares, stated because the residue matters more than the claim:
       * **The model.** It re-reads the same [Model.t] the compiler read. A coefficient
         the *builder* got wrong, or a term list it folded wrongly, is re-checked as
         written and agreed with. Exactness begins at this function's own arithmetic,
         not at the front end's.
       * **The indexing.** It is handed [values] indexed the same way the printer
         indexes it, so a permutation of variables is invisible to it -- the reason
         test/unit/test_compile.ml asserts [Var.of_int i = Model.var m i] directly.
       * **The answer's existence.** On `=====UNSATISFIABLE=====` there is no
         assignment for it to check at all (D-0029). I-S1 guards SAT answers only;
         UNSAT is guarded by the proof, not by this.
   - It checks the *declared* domains too, not only the constraints. A solution that
     assigns 7 to a `var 1..3` violates the model just as surely as one that breaks a
     linear constraint, and a bug in the store is more likely to produce the former. *)

(* Exact integer arithmetic, sign and magnitude, base 2^30 little-endian.

   Deliberately small and deliberately local: it exists to evaluate `sum a_i v_i` and
   compare it with a right-hand side, and it does nothing else. Base 2^30 is chosen so
   that the inner product of [mul] -- one limb times one limb, plus an accumulator limb,
   plus a carry -- stays below 2^62 and therefore cannot itself wrap on OCaml's 63-bit
   [int]; that bound is asserted as a test rather than left as a comment.

   [of_int] never negates its argument, because [min_int] has no negation: it takes the
   sign first and builds the magnitude with [abs (n mod base)], whose operand is strictly
   between -base and 0 and so always has one. That is the same trap D-0029 records
   [Checked.ceildiv] falling into from the other side. *)
module Exact = struct
  let bits = 30
  let base = 1 lsl bits
  let mask = base - 1

  (* [mag] is little-endian with no leading zero limb; [sign] is -1, 0 or 1, and is 0
     exactly when [mag] is empty. *)
  type t = { sign : int; mag : int array }

  let zero = { sign = 0; mag = [||] }

  let normalise sign mag =
    let n = ref (Array.length mag) in
    while !n > 0 && mag.(!n - 1) = 0 do
      decr n
    done;
    if !n = 0 then zero else { sign; mag = Array.sub mag 0 !n }

  let of_int n =
    if n = 0 then zero
    else
      let sign = if n < 0 then -1 else 1 in
      let limbs = ref [] in
      let k = ref n in
      while !k <> 0 do
        limbs := abs (!k mod base) :: !limbs;
        k := !k / base
      done;
      normalise sign (Array.of_list (List.rev !limbs))

  let cmp_mag a b =
    let la = Array.length a and lb = Array.length b in
    if la <> lb then Stdlib.compare la lb
    else
      let rec go i =
        if i < 0 then 0
        else if a.(i) <> b.(i) then Stdlib.compare a.(i) b.(i)
        else go (i - 1)
      in
      go (la - 1)

  let add_mag a b =
    let la = Array.length a and lb = Array.length b in
    let n = Stdlib.max la lb + 1 in
    let r = Array.make n 0 in
    let carry = ref 0 in
    for i = 0 to n - 1 do
      let s = (if i < la then a.(i) else 0) + (if i < lb then b.(i) else 0) + !carry in
      r.(i) <- s land mask;
      carry := s lsr bits
    done;
    r

  (* Requires |a| >= |b|, which every caller establishes with [cmp_mag] first. *)
  let sub_mag a b =
    let la = Array.length a and lb = Array.length b in
    let r = Array.make la 0 in
    let borrow = ref 0 in
    for i = 0 to la - 1 do
      let s = a.(i) - (if i < lb then b.(i) else 0) - !borrow in
      if s < 0 then (
        r.(i) <- s + base;
        borrow := 1)
      else (
        r.(i) <- s;
        borrow := 0)
    done;
    r

  let add x y =
    if x.sign = 0 then y
    else if y.sign = 0 then x
    else if x.sign = y.sign then normalise x.sign (add_mag x.mag y.mag)
    else
      let c = cmp_mag x.mag y.mag in
      if c = 0 then zero
      else if c > 0 then normalise x.sign (sub_mag x.mag y.mag)
      else normalise y.sign (sub_mag y.mag x.mag)

  let mul x y =
    if x.sign = 0 || y.sign = 0 then zero
    else
      let la = Array.length x.mag and lb = Array.length y.mag in
      let r = Array.make (la + lb) 0 in
      for i = 0 to la - 1 do
        let carry = ref 0 in
        for j = 0 to lb - 1 do
          let cur = r.(i + j) + (x.mag.(i) * y.mag.(j)) + !carry in
          r.(i + j) <- cur land mask;
          carry := cur lsr bits
        done;
        let k = ref (i + lb) in
        while !carry <> 0 do
          let cur = r.(!k) + !carry in
          r.(!k) <- cur land mask;
          carry := cur lsr bits;
          incr k
        done
      done;
      normalise (x.sign * y.sign) r

  let compare x y =
    if x.sign <> y.sign then Stdlib.compare x.sign y.sign
    else if x.sign >= 0 then cmp_mag x.mag y.mag
    else cmp_mag y.mag x.mag

  (* The worst intermediate [mul] can produce, as a plain [int]. Exposed so that the
     "cannot itself wrap" claim in this module's header is a checked assertion in
     test/unit/test_compile.ml and not a comment nobody re-derives. *)
  let widest_mul_intermediate = mask + (mask * mask) + mask
end

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
  (* M1-T33: exact, so the oracle cannot confirm a wrapped product. See the header. *)
  let sum terms =
    List.fold_left
      (fun acc (c, i) ->
        Exact.add acc (Exact.mul (Exact.of_int c) (Exact.of_int values.(i))))
      Exact.zero terms
  in
  let sum_cmp terms rhs = Exact.compare (sum terms) (Exact.of_int rhs) in
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
  (* Each auxiliary Boolean against its own definition: `x_sign <-> x >= 0` and
     `b_v <-> y >= v`. [Int_abs] passes its single operand for both, so its (empty)
     [y_ge] is walked over no values at all. *)
  let aux_holds x y (aux : aux) =
    (match aux.x_sign with None -> true | Some b -> truth (Var b) = (value x >= 0))
    && List.for_all (fun (v, b) -> truth (Var b) = (value y >= v)) aux.y_ge
  in
  let holds (c : constr) =
    match c.k with
    | Int_lin_le (ts, rhs) -> sum_cmp ts rhs <= 0
    | Int_lin_eq (ts, rhs) -> sum_cmp ts rhs = 0
    | Int_lin_ne (ts, rhs) -> sum_cmp ts rhs <> 0
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
    (* M3: each re-evaluated as the equivalence it is, in both directions, from the
       FlatZinc definition and from nothing in lib/core/prop/. *)
    | Int_lin_le_reif (ts, rhs, r) -> truth r = (sum_cmp ts rhs <= 0)
    | Int_le_reif (a, b, r) -> truth r = (value a <= value b)
    | Int_eq_reif (a, b, r) -> truth r = (value a = value b)
    | Int_ne_reif (a, b, r) -> truth r = (value a <> value b)
    (* M4. Written from docs/SPEC.md 2.1 and from nothing in lib/core/prop/, which is
       the discipline this whole function is built on -- see the header. In particular
       it does NOT call [Baguette_core.Arith.is_in_relation], although the roadmap row
       for M4-T4b proposed one shared predicate: that predicate is the solver's, it
       computes its product with [Checked] (the propagators' own arithmetic), and a
       shared product is exactly the shape of agreement D-0029 was about and that the
       [Exact] note above refuses. The anti-drift guarantee the row wanted is kept by
       test, not by sharing: test_prop.ml enumerates small boxes and asserts the two
       agree on every triple.

       The multiplication goes through [Exact], so it cannot wrap. Division and
       absolute value cannot overflow at any value the declared-bound cap admits
       (|min_int| is the one exception and [Checked.bound_fits] refuses it), so they
       are written natively -- [Stdlib.(/)] truncates toward zero, which is exactly
       what SPEC 2.1 and D-0033 require, and [Stdlib.(mod)] is not consulted at all
       here because the quotient alone decides the relation.

       The auxiliary Booleans are checked too, against their own definitions. They are
       ordinary variables of the model by the time a solution is printed, and a
       solution that assigned one of them a value its definition forbids would mean
       the decomposition and the store had parted company. *)
    | Int_times (a, b, c, aux) ->
        Exact.(compare (mul (of_int (value a)) (of_int (value b))) (of_int (value c))) = 0
        && aux_holds a b aux
    | Int_div (a, b, c, aux) ->
        value b <> 0 && value a / value b = value c && aux_holds a b aux
    | Int_abs (a, c, aux) -> value c = abs (value a) && aux_holds a a aux
    (* M4-T1, the relation itself: no pair of operands shares a value. Written as the
       quadratic scan and not as a sorted-list or hashtable test, because the oracle is
       written to be obviously right (see the header) and because a scope this small is
       not where the solver's time goes. *)
    | All_different xs ->
        let vs = List.map value xs in
        let rec distinct = function
          | [] -> true
          | v :: rest -> (not (List.mem v rest)) && distinct rest
        in
        distinct vs
    (* M7-T16, the relation as SPEC 2.1 states it: a tally per cover value, compared
       against that position's count. Written as the obvious scan for [All_different]'s
       reason -- this is the oracle, so it is written to be obviously right. *)
    | Global_cardinality (xs, cover, counts) ->
        let vs = List.map value xs in
        List.for_all2
          (fun cv cnt -> List.length (List.filter (fun v -> v = cv) vs) = value cnt)
          (Array.to_list cover) counts
    (* M4-T3, the relation as SPEC 2.1 states it and not as lib/flatzinc/compile.ml
       posts it: the index is 1-based, it must land inside the array, and the selected
       constant must equal the result. The range test is written out rather than left to
       [Array.get]'s own bounds check, because an out-of-range index must make this
       return [false] and not raise. *)
    | Array_int_element (i, vs, c) ->
        let k = value i in
        k >= 1 && k <= Array.length vs && vs.(k - 1) = value c
  in
  let domains_ok =
    let ok = ref true in
    Array.iteri (fun i v -> if not (in_domain v.v_dom values.(i)) then ok := false) t.vars;
    !ok
  in
  domains_ok && List.for_all holds t.constraints
