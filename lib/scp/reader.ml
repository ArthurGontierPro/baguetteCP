(* `.scp` text to [Model.t]. Built by M23-inputs-T2..T4 (the frame and the arithmetic,
   then the globals without and with auxiliary variables) on the plan D-0228 section 14
   fixed: a reader from `.scp` text to [Model.t] in lib/scp/, nothing more, that takes
   only what baguette propagates or rewrites exactly. D-0230 records the reader as built,
   what it refuses and why, and the choices that plan left open (its section 3).

   The grammar is that of CakeML's `cake_pb_cp`, `cp_parseScript.sml` on branch
   `cp_enc_new` at `930601d6`, version 1, and every constraint means what that commit's
   `cpScript.sml` says it means. The output is the [Model.t] lib/flatzinc/builder.ml
   produces for a FlatZinc file, so lib/flatzinc/compile.ml and everything after it are
   unchanged. No view, no decomposition: a constraint is read when baguette propagates
   it or when its rewriting is exact (D-0228 section 14), and REFUSED otherwise, with
   its position. A file this reader does not read entirely is refused; it is never read
   in part.

   Stricter than cake on purpose, each refused with the position: an undeclared name, a
   repeated variable or constraint name, a variable whose bounds are empty (`lb > ub`),
   a version other than 1, a view, a `;` and a double quote (lib/scp/sexp.ml), an
   integer beyond 63 bits.

   THE FRAME. `( (version 1) (variables (name lb ub) ...) (constraints (name kw args...)
   ...) (prob_type decide | enumerate | (minimize x) | (maximize x)) )`, the four
   sections in that order. `enumerate` is read as `decide`: one solution is searched
   (D-0228 section 14, cake accepts a proof that exhibits one). The file is walked token
   by token and [Sexp.read] is called once per variable and once per constraint, so a
   constraint is converted while the next one is still text (D-0230 section 2).

   VARIABLES. A variable declared `0 1` is a [Model.Dbool] (D-0230 section 3): the
   encoding of a Boolean and of a 0..1 integer is the same (Encoding.declare_bool is
   declare_int 0..1), and the Boolean builtins compile.ml posts accept only a Dbool. Every
   other is a [Model.Drange]. Every variable of the file is printed, in the order of the
   file, as `name = value;` (a .scp has no output item, D-0230 section 3).

   AUXILIARIES are created after the variables of the file (D-0228 section 5: the order
   of creation fixes names and the default branching, so the file's own variables come
   first and keep the order the file gives them), in the order the constraints ask for
   them, and named `scp_<kind>_<n>` (a `_` is appended until
   the name is not one the file declares). They are of four kinds:
   - a CONDITION `(Z op v)` whose Z is not a 0..1 variable is a Boolean b defined by
     `b <-> Z op v` (memoised: one per distinct condition), and a negated 0..1 variable
     that has to stand where a positive Boolean is required is a Boolean nb with
     `bool_not(b, nb)` (memoised);
   - the arithmetic family's sign and ladder Booleans, made by lib/flatzinc/arith_aux.ml,
     the helper builder.ml uses, so the same constraint has the same auxiliaries;
   - what mznlib declares for a global, with the shape mznlib gives it: the selectors of
     `table` (one per row kept) and of `in` (one per position), the (n + 1) * Q state flags
     of `regular`, the n - 1 positions of `circuit` (on 1..n - 1);
   - the index of an `element` whose offset is not 1, `i = Y - off + 1`, because
     array_int_element counts from 1 and cake's `(Y off)` is position Y - off from 0.

   RESTRICTIONS. `in` over constants, the closed global cardinality and `circuit` restrict
   the domain of a variable of the file, as mznlib's `x in S` does in FlatZinc: the domain
   becomes the set (a [Model.Dset] when it has holes). A 0..1 variable keeps its Dbool
   domain and gets `x = v` instead, and a restriction that leaves no value posts the false
   clause (the problem is UNSAT, it is not malformed). A restriction narrows the domain
   from that constraint on: a constraint read earlier was sized on the wider domain, which
   is sound, because every auxiliary it made over a value the domain no longer has is
   fixed by its own definition. *)

module F = Baguette_flatzinc
module Model = F.Model
module Pos = F.Pos
module Error = F.Error
module Checked = Baguette_core.Checked
module Names = Model.Names

type st = {
  file_names : int Names.t; (* a variable of the file -> its index *)
  cnames : unit Names.t; (* constraint names seen *)
  mutable vars : Model.var array; (* slots [0, nvars) used *)
  mutable nvars : int;
  mutable nfile : int; (* how many variables the file declares *)
  mutable built_rev : Model.constr list;
  cond_memo : (int * string * int, int) Hashtbl.t;
  not_memo : (int, int) Hashtbl.t;
  mutable naux : int;
}

let create () =
  {
    file_names = Names.create 1024;
    cnames = Names.create 1024;
    vars = [||];
    nvars = 0;
    nfile = 0;
    built_rev = [];
    cond_memo = Hashtbl.create 64;
    not_memo = Hashtbl.create 64;
    naux = 0;
  }

let push_var st (v : Model.var) =
  let i = st.nvars in
  if i >= Array.length st.vars then (
    let grown = Array.make (max 1024 (2 * i)) v in
    Array.blit st.vars 0 grown 0 i;
    st.vars <- grown);
  st.vars.(i) <- v;
  st.nvars <- i + 1;
  i

let rec fresh_name st base =
  if Names.mem st.file_names base then fresh_name st (base ^ "_") else base

let new_aux st pos kind dom =
  let n = st.naux in
  st.naux <- n + 1;
  let name = fresh_name st (Printf.sprintf "scp_%s_%d" kind n) in
  push_var st { Model.v_name = name; v_dom = dom; v_pos = pos }

let fresh_bool st pos kind = new_aux st pos kind Model.Dbool

let bounds st i =
  match st.vars.(i).Model.v_dom with
  | Model.Dbool -> (0, 1)
  | Model.Drange (l, u) -> (l, u)
  | Model.Dset (n :: ns) -> (List.fold_left min n ns, List.fold_left max n ns)
  | Model.Dset [] -> invalid_arg "Reader.bounds: empty set domain"

let is_bool st i = match st.vars.(i).Model.v_dom with Model.Dbool -> true | _ -> false
let post st pos kw k = st.built_rev <- { Model.k; c_pos = pos; c_id = kw } :: st.built_rev

(* The false clause: `bool_clause([], [])`, which compile.ml posts as the empty row, so
   the problem is UNSAT rather than malformed. *)
let post_false st pos kw = post st pos kw (Model.Bool_clause ([], []))

(* ------------------------------------------------------------------ refusals *)

let refuse pos kw fmt =
  Printf.ksprintf
    (fun why ->
      Error.failf pos "constraint `%s` is refused: %s (docs/DECISIONS.md D-0230)" kw why)
    fmt

let shape pos kw expected =
  Error.failf pos
    "constraint `%s` expects %s, as cake_pb_cp reads it (cp_parseScript.sml)" kw expected

(* `b <-> C(b)`: compile.ml refuses a reifier that occurs in the constraint it reifies,
   because it is not a definition of b. Said here, by the reader, with the constraint's
   position, rather than as a refusal of a builtin the file never wrote. *)
let self_reif pos kw =
  refuse pos kw
    "the variable of the condition occurs in the comparison it reifies, and baguette's \
     reified constraints take a reifier that is defined by them, not one they also \
     constrain"

(* ------------------------------------------------------------------ atoms *)

let atom_int p a = Sexp.int_of_atom p a

let int_of (e : Sexp.t) what =
  match e with
  | Sexp.Atom (a, p) -> (
      match atom_int p a with
      | Some n -> n
      | None -> Error.failf p "%s must be an integer, not `%s`" what a)
  | Sexp.List (_, p) -> Error.failf p "%s must be an integer, not a list" what

let ints_of (e : Sexp.t) what =
  match e with
  | Sexp.List (es, _) -> List.map (fun e -> int_of e what) es
  | Sexp.Atom (_, p) -> Error.failf p "%s must be a list of integers" what

let lookup st p name =
  match Names.find_opt st.file_names name with
  | Some i -> i
  | None ->
      Error.failf p
        "`%s` is not a declared variable. cake_pb_cp reads an undeclared name as a free \
         variable; this reader refuses it, because no model means one (D-0228 section \
         14)"
        name

(* cake's `varc`: an integer, else a variable name. A list here is a view, which version
   1 of the format does not have (D-0228 section 11, the format author's answer: views
   wait for a version 2, so this reader refuses one by name and position). *)
let operand st (e : Sexp.t) : Model.operand =
  match e with
  | Sexp.Atom (a, p) -> (
      match atom_int p a with
      | Some n -> Model.Const n
      | None -> Model.Var (lookup st p a))
  | Sexp.List (_, p) ->
      Error.failf p
        "a list where a variable or an integer is expected: a view, which version 1 of \
         the .scp format does not have, so cake_pb_cp refuses it and so does this reader \
         (D-0228 sections 11 and 13)"

let operands st (e : Sexp.t) what =
  match e with
  | Sexp.List (es, _) -> List.map (operand st) es
  | Sexp.Atom (_, p) -> Error.failf p "%s must be a list of variables and integers" what

let pos_of = Sexp.pos_of

(* ------------------------------------------------------------------ arithmetic *)

let ck pos kw f =
  try f ()
  with Checked.Overflow why ->
    refuse pos kw "a constant moved across the comparison overflows 63 bits (%s)" why

(* sum c_i X_i - [Y] over the variables, and the right-hand side: the constants of the
   terms moved across, and Y when it is one. The FlatZinc builder's fold (lin_terms), so
   a row written by tools/e2e/fzn2scp.py comes back as the row it was written from. *)
let linear st pos kw (cxs : Sexp.t) (y : Sexp.t) =
  let es =
    match cxs with
    | Sexp.List (es, _) -> es
    | Sexp.Atom (_, p) ->
        Error.failf p "constraint `%s`: the linear term must be a list" kw
  in
  let rec pairs acc r = function
    | [] -> (List.rev acc, r)
    | [ e ] ->
        Error.failf (pos_of e) "constraint `%s`: the linear term has an odd length" kw
    | c :: x :: rest -> (
        let c = int_of c "a coefficient" in
        match operand st x with
        | Model.Var i -> pairs ((c, i) :: acc) r rest
        | Model.Const n ->
            pairs acc (ck pos kw (fun () -> Checked.sub r (Checked.mul c n))) rest)
  in
  match operand st y with
  | Model.Const k -> pairs [] k es
  | Model.Var j ->
      let ts, r = pairs [] 0 es in
      (ts @ [ (-1, j) ], r)

let negate pos kw ts r =
  ( List.map (fun (c, i) -> (ck pos kw (fun () -> Checked.neg c), i)) ts,
    ck pos kw (fun () -> Checked.neg r) )

let minus_one pos kw r = ck pos kw (fun () -> Checked.sub r 1)

(* [a - b] as terms and a right-hand side offset: the row a - b + k <= ..., folded. *)
let diff_terms pos kw (a : Model.operand) (b : Model.operand) =
  let t = ref [] and r = ref 0 in
  (match a with
  | Model.Var i -> t := [ (1, i) ]
  | Model.Const n -> r := ck pos kw (fun () -> Checked.neg n));
  (match b with
  | Model.Var j -> t := !t @ [ (-1, j) ]
  | Model.Const n -> r := ck pos kw (fun () -> Checked.add !r n));
  (!t, !r)

(* ------------------------------------------------------------------ comparisons *)

type cmp = Eq | Ne | Le | Lt | Ge | Gt

let cmp_of_kw = function
  | "equals" -> Some Eq
  | "not_equals" -> Some Ne
  | "less_equal" -> Some Le
  | "less_than" -> Some Lt
  | "greater_equal" -> Some Ge
  | "greater_than" -> Some Gt
  | _ -> None

let cmp_of_sym = function
  | "=" -> Some Eq
  | "!=" -> Some Ne
  | "<=" -> Some Le
  | "<" -> Some Lt
  | ">=" -> Some Ge
  | ">" -> Some Gt
  | _ -> None

let holds c (x : int) y =
  match c with
  | Eq -> x = y
  | Ne -> x <> y
  | Le -> x <= y
  | Lt -> x < y
  | Ge -> x >= y
  | Gt -> x > y

let negation = function Eq -> Ne | Ne -> Eq | Le -> Gt | Lt -> Ge | Ge -> Lt | Gt -> Le

(* x c y, unreified. *)
let cmp_cstr c (x : Model.operand) y : Model.cstr =
  match c with
  | Eq -> Model.Int_eq (x, y)
  | Ne -> Model.Int_ne (x, y)
  | Le -> Model.Int_le (x, y)
  | Lt -> Model.Int_lt (x, y)
  | Ge -> Model.Int_le (y, x)
  | Gt -> Model.Int_lt (y, x)

(* r <-> x c y, r a Boolean operand. *)
let cmp_reif pos kw c x y r : Model.cstr =
  match c with
  | Eq -> Model.Int_eq_reif (x, y, r)
  | Ne -> Model.Int_ne_reif (x, y, r)
  | Le -> Model.Int_le_reif (x, y, r)
  | Ge -> Model.Int_le_reif (y, x, r)
  | Lt ->
      let ts, k = diff_terms pos kw x y in
      Model.Int_lin_le_reif (ts, minus_one pos kw k, r)
  | Gt ->
      let ts, k = diff_terms pos kw y x in
      Model.Int_lin_le_reif (ts, minus_one pos kw k, r)

(* ------------------------------------------------------------------ conditions *)

(* A condition `(Z op v)` as a literal over a Boolean variable of the model. *)
type lit = Ltrue | Lfalse | Lpos of int | Lneg of int

let cond st kw (e : Sexp.t) =
  match e with
  | Sexp.List ([ z; Sexp.Atom (o, op_pos); v ], p) -> (
      let c =
        match cmp_of_sym o with
        | Some c -> c
        | None ->
            Error.failf op_pos "`%s` is not a comparison of a condition (= != < <= > >=)"
              o
      in
      let v = int_of v "the value of a condition" in
      match operand st z with
      | Model.Const n -> if holds c n v then Ltrue else Lfalse
      | Model.Var i when is_bool st i -> (
          match (holds c 0 v, holds c 1 v) with
          | false, false -> Lfalse
          | true, true -> Ltrue
          | false, true -> Lpos i
          | true, false -> Lneg i)
      | Model.Var i ->
          let key = (i, o, v) in
          let b =
            match Hashtbl.find_opt st.cond_memo key with
            | Some b -> b
            | None ->
                let b = fresh_bool st p "cond" in
                Hashtbl.replace st.cond_memo key b;
                let x = Model.Var i and k = Model.Const v in
                (* b <-> Z op v, for the six operators *)
                let def =
                  match c with
                  | Eq -> Model.Int_eq_reif (x, k, Model.Var b)
                  | Ne -> Model.Int_ne_reif (x, k, Model.Var b)
                  | Le -> Model.Int_le_reif (x, k, Model.Var b)
                  | Lt ->
                      Model.Int_le_reif (x, Model.Const (minus_one p kw v), Model.Var b)
                  | Ge -> Model.Int_le_reif (k, x, Model.Var b)
                  | Gt ->
                      Model.Int_le_reif
                        (Model.Const (ck p kw (fun () -> Checked.add v 1)), x, Model.Var b)
                in
                post st p kw def;
                b
          in
          Lpos b)
  | e -> Error.failf (pos_of e) "constraint `%s`: a condition is a list (Z op v)" kw

(* The literal as a POSITIVE Boolean operand, for the places that take one. *)
let lit_operand st pos kw = function
  | Ltrue -> Model.Const 1
  | Lfalse -> Model.Const 0
  | Lpos b -> Model.Var b
  | Lneg b ->
      let nb =
        match Hashtbl.find_opt st.not_memo b with
        | Some nb -> nb
        | None ->
            let nb = fresh_bool st pos "not" in
            Hashtbl.replace st.not_memo b nb;
            post st pos kw (Model.Bool_not (Model.Var b, Model.Var nb));
            nb
      in
      Model.Var nb

(* ------------------------------------------------------------------ restrictions *)

(* Restrict variable [i] of the file to the values [vs]. *)
let restrict st pos kw (op : Model.operand) (vs : int list) =
  let vs = List.sort_uniq compare vs in
  match op with
  | Model.Const n -> if not (List.mem n vs) then post_false st pos kw
  | Model.Var i -> (
      let v = st.vars.(i) in
      match v.Model.v_dom with
      | Model.Dbool -> (
          match List.filter (fun x -> x = 0 || x = 1) vs with
          | [] -> post_false st pos kw
          | [ x ] -> post st pos kw (Model.Int_eq (op, Model.Const x))
          | _ -> ())
      | dom -> (
          let keep =
            match dom with
            | Model.Drange (l, u) -> List.filter (fun x -> l <= x && x <= u) vs
            | Model.Dset ds -> List.filter (fun x -> List.mem x ds) vs
            | Model.Dbool -> assert false
          in
          match keep with
          | [] -> post_false st pos kw
          | lo :: _ ->
              let hi = List.fold_left max lo keep in
              let contiguous = List.length keep = hi - lo + 1 in
              let dom' = if contiguous then Model.Drange (lo, hi) else Model.Dset keep in
              if dom' <> dom then st.vars.(i) <- { v with Model.v_dom = dom' }))

(* ------------------------------------------------------------------ the constraints *)

let strip_suffix suf s =
  let n = String.length s and k = String.length suf in
  if n >= k && String.sub s (n - k) k = suf then Some (String.sub s 0 (n - k)) else None

(* (stem, `None` | `If` | `Iff`) as cake's strip_reif_suffix. *)
let reif_of kw =
  match strip_suffix "_iff" kw with
  | Some s -> (s, `Iff)
  | None -> ( match strip_suffix "_if" kw with Some s -> (s, `If) | None -> (kw, `None))

let actx st pos =
  {
    F.Arith_aux.bounds = bounds st;
    fresh = (fun () -> fresh_bool st pos "arith");
    name = (fun i -> st.vars.(i).Model.v_name);
    where = (fun () -> Pos.to_string pos);
  }

let one_constraint st pos kw (args : Sexp.t list) =
  let arity n expected = if List.length args <> n then shape pos kw expected in
  let const_list e what =
    List.map
      (function
        | Model.Const n -> n
        | Model.Var _ ->
            refuse pos kw
              "%s must be constants (baguette's propagator takes no variable there)" what)
      (operands st e what)
  in
  match kw with
  (* ---- linear *)
  | _ when String.length kw > 4 && String.sub kw 0 4 = "lin_" -> (
      let stem, reif = reif_of (String.sub kw 4 (String.length kw - 4)) in
      let c =
        match cmp_of_kw stem with
        | Some c -> c
        | None -> Error.failf pos "`%s` is not a linear comparison cake_pb_cp knows" kw
      in
      let lit, rest =
        match (reif, args) with
        | `None, _ -> (Ltrue, args)
        | `If, _ ->
            refuse pos kw
              "a half reification (`_if`) has no propagator in baguette, and its \
               rewriting through a full one adds a variable D-0228 section 14 does not \
               admit"
        | `Iff, z :: rest -> (cond st kw z, rest)
        | `Iff, [] -> shape pos kw "a condition (Z op v) first"
      in
      match rest with
      | [ cxs; y ] -> (
          let ts, r = linear st pos kw cxs y in
          (* every comparison as one `<=` row, or an equality / a disequality *)
          let le c =
            match c with
            | Le -> Some (ts, r)
            | Lt -> Some (ts, minus_one pos kw r)
            | Ge -> Some (negate pos kw ts r)
            | Gt ->
                let ts', r' = negate pos kw ts r in
                Some (ts', minus_one pos kw r')
            | Eq | Ne -> None
          in
          let plain c =
            match le c with
            | Some (ts, r) -> Model.Int_lin_le (ts, r)
            | None -> if c = Eq then Model.Int_lin_eq (ts, r) else Model.Int_lin_ne (ts, r)
          in
          match lit with
          | Ltrue -> post st pos kw (plain c)
          | Lfalse -> post st pos kw (plain (negation c))
          | Lpos b | Lneg b -> (
              if List.exists (fun (_, i) -> i = b) ts then self_reif pos kw;
              let c = match lit with Lneg _ -> negation c | _ -> c in
              match le c with
              | Some (ts, r) ->
                  post st pos kw (Model.Int_lin_le_reif (ts, r, Model.Var b))
              | None ->
                  refuse pos kw
                    "the reified linear equality and disequality are out until the user \
                     decides (D-0228 section 14: two `lin_less_equal_iff` and an `and` \
                     is mznlib's decomposition, not a propagator)"))
      | _ -> shape pos kw "(c1 X1 ... cn Xn) Y after its optional condition")
  (* ---- the Boolean connectives *)
  | "and" | "or" -> (
      arity 2 "((Z op v) ...) (Y op v)";
      match args with
      | [ Sexp.List (cs, _); r ] -> (
          let ls = List.map (cond st kw) cs in
          let r = cond st kw r in
          match (kw, r) with
          | "or", Ltrue ->
              if not (List.mem Ltrue ls) then
                post st pos kw
                  (Model.Bool_clause
                     ( List.filter_map
                         (function Lpos b -> Some (Model.Var b) | _ -> None)
                         ls,
                       List.filter_map
                         (function Lneg b -> Some (Model.Var b) | _ -> None)
                         ls ))
          | _ ->
              let xs = List.map (lit_operand st pos kw) ls in
              let r = lit_operand st pos kw r in
              post st pos kw
                (if kw = "or" then Model.Array_bool_or (xs, r)
                 else Model.Array_bool_and (xs, r)))
      | _ -> shape pos kw "((Z op v) ...) (Y op v)")
  (* ---- arithmetic *)
  | "plus" | "minus" -> (
      arity 3 "X Y Z";
      match args with
      | [ x; y; z ] ->
          (* x + y - z = 0, x - y - z = 0 *)
          let cy = if kw = "plus" then 1 else -1 in
          let t = ref [] and r = ref 0 in
          List.iter
            (fun (c, e) ->
              match operand st e with
              | Model.Var i -> t := (c, i) :: !t
              | Model.Const n ->
                  r := ck pos kw (fun () -> Checked.sub !r (Checked.mul c n)))
            [ (1, x); (cy, y); (-1, z) ];
          post st pos kw (Model.Int_lin_eq (List.rev !t, !r))
      | _ -> assert false)
  | "neg" -> (
      arity 2 "X Y";
      match args with
      | [ x; y ] ->
          let t = ref [] and r = ref 0 in
          List.iter
            (fun e ->
              match operand st e with
              | Model.Var i -> t := (1, i) :: !t
              | Model.Const n -> r := ck pos kw (fun () -> Checked.sub !r n))
            [ x; y ];
          post st pos kw (Model.Int_lin_eq (List.rev !t, !r))
      | _ -> assert false)
  | "abs" -> (
      arity 2 "X Y";
      match args with
      | [ x; y ] ->
          let x = operand st x and y = operand st y in
          post st pos kw (F.Arith_aux.abs (actx st pos) x y)
      | _ -> assert false)
  | "max" | "min" -> (
      arity 3 "X Y Z";
      match args with
      | [ x; y; z ] ->
          let x = operand st x and y = operand st y and z = operand st z in
          post st pos kw
            (if kw = "max" then Model.Array_int_maximum (z, [ x; y ])
             else Model.Array_int_minimum (z, [ x; y ]))
      | _ -> assert false)
  | "multiply" | "divide" -> (
      arity 3 "X Y Z";
      match args with
      | [ x; y; z ] ->
          let x = operand st x and y = operand st y and z = operand st z in
          let ctx = actx st pos in
          post st pos kw
            (if kw = "multiply" then F.Arith_aux.times ctx x y z
             else F.Arith_aux.div ctx x y z)
      | _ -> assert false)
  (* ---- sorted *)
  | "increasing" | "strictly_increasing" | "decreasing" | "strictly_decreasing" -> (
      arity 1 "(X1 ... Xn)";
      let c =
        match kw with
        | "increasing" -> Le
        | "strictly_increasing" -> Lt
        | "decreasing" -> Ge
        | _ -> Gt
      in
      match operands st (List.hd args) "the sequence" with
      | [] -> ()
      | x0 :: xs ->
          ignore
            (List.fold_left
               (fun a b ->
                 post st pos kw (cmp_cstr c a b);
                 b)
               x0 xs))
  (* ---- counting *)
  | "all_different" ->
      arity 1 "(X1 ... Xn)";
      post st pos kw (Model.All_different (operands st (List.hd args) "the variables"))
  | "gacglobalcardinality" | "boundsglobalcardinality" | "gacglobalcardinalityclosed"
  | "boundsglobalcardinalityclosed" -> (
      arity 3 "(X1 ... Xn) (v1 ... vm) (C1 ... Cm)";
      match args with
      | [ xs; vs; cs ] ->
          let xs = operands st xs "the variables" in
          let vs = ints_of vs "the cover" in
          let cs = operands st cs "the counts" in
          if List.length vs <> List.length cs then
            refuse pos kw
              "%d cover values and %d counts (cake's LIST_REL makes the constraint \
               false; a model that means that can say so with a false clause)"
              (List.length vs) (List.length cs);
          (* closed: every x takes a cover value, as mznlib's x in cover *)
          if strip_suffix "closed" kw <> None then
            List.iter (fun x -> restrict st pos kw x vs) xs;
          post st pos kw (Model.Global_cardinality (xs, Array.of_list vs, cs))
      | _ -> assert false)
  | "count" -> (
      arity 3 "(X1 ... Xn) Y Z";
      match args with
      | [ xs; y; z ] -> (
          let xs = operands st xs "the variables" in
          match operand st y with
          | Model.Const v ->
              post st pos kw (Model.Global_cardinality (xs, [| v |], [ operand st z ]))
          | Model.Var _ ->
              refuse pos kw
                "the counted value is a variable; baguette counts a constant value only \
                 (through global_cardinality)")
      | _ -> assert false)
  | "in" -> (
      arity 2 "(X1 ... Xn) Y";
      match args with
      | [ xs; y ] ->
          let xs = operands st xs "the values" and y = operand st y in
          if List.for_all (function Model.Const _ -> true | Model.Var _ -> false) xs
          then
            restrict st pos kw y
              (List.map (function Model.Const n -> n | Model.Var _ -> 0) xs)
          else
            (* mznlib's fzn_member_int: one selector per position *)
            let bs = List.map (fun _ -> Model.Var (fresh_bool st pos "sel")) xs in
            post st pos kw (Model.Member { Model.mem_x = xs; mem_y = y; mem_b = bs })
      | _ -> assert false)
  (* ---- arrays *)
  | "element" -> (
      arity 3 "(X0 ... Xn-1) (Y off) Z";
      match args with
      | [ xs; Sexp.List ([ y; off ], _); z ] ->
          let vs = Array.of_list (const_list xs "the array's entries") in
          let y = operand st y and off = int_of off "the offset" in
          let z = operand st z in
          (* array_int_element counts from 1: the index is Y - off + 1 *)
          let idx =
            if off = 1 then y
            else
              match y with
              | Model.Const n ->
                  Model.Const (ck pos kw (fun () -> Checked.add (Checked.sub n off) 1))
              | Model.Var j ->
                  let lo, hi = bounds st j in
                  let sh n = ck pos kw (fun () -> Checked.add (Checked.sub n off) 1) in
                  let i = new_aux st pos "idx" (Model.Drange (sh lo, sh hi)) in
                  (* i - Y = 1 - off *)
                  post st pos kw
                    (Model.Int_lin_eq
                       ([ (1, i); (-1, j) ], ck pos kw (fun () -> Checked.sub 1 off)));
                  Model.Var i
          in
          post st pos kw (Model.Array_int_element (idx, vs, z))
      | _ -> shape pos kw "(X0 ... Xn-1) (Y off) Z")
  | "array_max" | "array_min" -> (
      arity 2 "(X1 ... Xn) Y";
      match args with
      | [ xs; y ] -> (
          let xs = operands st xs "the variables" and y = operand st y in
          match xs with
          | [] -> post_false st pos kw (* cake: Y is one of no value *)
          | _ ->
              post st pos kw
                (if kw = "array_max" then Model.Array_int_maximum (y, xs)
                 else Model.Array_int_minimum (y, xs)))
      | _ -> assert false)
  (* ---- channelling *)
  | "inverse" -> (
      arity 2 "((X1 ... Xn) offx) ((Y1 ... Ym) offy)";
      match args with
      | [ Sexp.List ([ f; fo ], _); Sexp.List ([ g; go ], _) ] ->
          post st pos kw
            (Model.Inverse
               {
                 Model.inv_f = operands st f "the first array";
                 inv_fmin = int_of fo "the first offset";
                 inv_g = operands st g "the second array";
                 inv_gmin = int_of go "the second offset";
               })
      | _ -> shape pos kw "((X1 ... Xn) offx) ((Y1 ... Ym) offy)")
  (* ---- scheduling *)
  | "cumulative" -> (
      arity 4 "(x1 ... xn) (w1 ... wn) (h1 ... hn) cap";
      match args with
      | [ ss; ds; rs; cap ] ->
          let ss = operands st ss "the starts" in
          let ds = const_list ds "the durations" and rs = const_list rs "the heights" in
          let cap =
            match operand st cap with
            | Model.Const n -> n
            | Model.Var _ -> refuse pos kw "the capacity must be a constant"
          in
          let n = List.length ss in
          if List.length ds <> n || List.length rs <> n then
            refuse pos kw "%d starts, %d durations and %d heights" n (List.length ds)
              (List.length rs);
          if List.exists (fun d -> d < 0) ds || List.exists (fun r -> r < 0) rs || cap < 0
          then
            refuse pos kw
              "a negative duration, height or capacity (cake's cumulative_sem and \
               baguette's relation are only known to agree on non-negative ones, D-0195)";
          post st pos kw (Model.Cumulative (ss, Array.of_list ds, Array.of_list rs, cap))
      | _ -> assert false)
  (* ---- extensional *)
  | "table" -> (
      arity 2 "((t11 ... t1n) ...) (X1 ... Xn)";
      match args with
      | [ Sexp.List (rows, _); xs ] -> (
          let xs = operands st xs "the variables" in
          let n = List.length xs in
          let rows =
            List.map
              (fun r ->
                match r with
                | Sexp.List (es, p) ->
                    if List.length es <> n then
                      Error.failf p
                        "constraint `%s`: a row of %d values over %d variables (cake \
                         makes the whole constraint false; this reader refuses it)"
                        kw (List.length es) n;
                    List.map
                      (function
                        | Sexp.Atom ("*", p) ->
                            refuse p kw
                              "a wildcard `*`: baguette's table takes plain rows"
                        | e -> int_of e "a table entry")
                      es
                | Sexp.Atom (_, p) ->
                    Error.failf p "constraint `%s`: a row must be a list" kw)
              rows
          in
          (* mznlib's fzn_table_int: the rows every value of which is in its variable's
             domain, one selector each *)
          let in_dom op v =
            match op with
            | Model.Const c -> c = v
            | Model.Var i -> (
                match st.vars.(i).Model.v_dom with
                | Model.Dbool -> v = 0 || v = 1
                | Model.Drange (l, u) -> l <= v && v <= u
                | Model.Dset ds -> List.mem v ds)
          in
          let keep = List.filter (fun r -> List.for_all2 in_dom xs r) rows in
          if n = 0 then (if rows = [] then post_false st pos kw)
          else
            match keep with
            | [] -> post_false st pos kw
            | _ ->
                let ss = List.map (fun _ -> Model.Var (fresh_bool st pos "sel")) keep in
                post st pos kw
                  (Model.Table
                     {
                       Model.tab_x = xs;
                       tab_t = Array.of_list (List.concat keep);
                       tab_s = ss;
                     }))
      | _ -> shape pos kw "((t11 ... t1n) ...) (X1 ... Xn)")
  | "regular" -> (
      arity 4 "(X1 ... Xn) nstates ((edges_0) ...) (f1 ... fk)";
      match args with
      | [ xs; nq; Sexp.List (trans, _); fs ] ->
          let xs = operands st xs "the word" in
          let nq = int_of nq "the number of states" in
          if nq < 0 then refuse pos kw "a negative number of states";
          (* cake's NFA: an edge to a state >= nstates, a state >= nstates and a final
             state >= nstates are dead (nfa_accepts checks q < nstates) *)
          let edges =
            List.mapi
              (fun q e ->
                match e with
                | Sexp.List (es, _) ->
                    List.filter_map
                      (function
                        | Sexp.List ([ v; t ], p) ->
                            let v = int_of v "a symbol"
                            and t = int_of t "a target state" in
                            if t < 0 then Error.failf p "a negative target state";
                            if q < nq && t < nq then Some (q, v, t) else None
                        | e -> Error.failf (pos_of e) "an edge is a list (symbol target)")
                      es
                | Sexp.Atom (_, p) -> Error.failf p "a state's edges are a list")
              trans
            |> List.concat
          in
          let finals = List.filter (fun f -> f < nq) (ints_of fs "the final states") in
          if List.exists (fun f -> f < 0) (ints_of fs "the final states") then
            refuse pos kw "a negative final state";
          if xs = [] then (if not (nq > 0 && List.mem 0 finals) then post_false st pos kw)
          else if nq = 0 || edges = [] || finals = [] then post_false st pos kw
          else
            (* a DFA over the symbols smin..smax, states 1..nq (cake's q is q + 1) *)
            let smin = List.fold_left (fun a (_, v, _) -> min a v) max_int edges in
            let smax = List.fold_left (fun a (_, v, _) -> max a v) min_int edges in
            let w = ck pos kw (fun () -> Checked.add (Checked.sub smax smin) 1) in
            (* A constant letter that labels no edge kills every run, so the constraint is
               false, and the reader says so itself. When this was written
               lib/core/prop/regular.ml raised on a constant letter outside the symbol
               range (an index out of bounds in [forward_reason], reproduced from FlatZinc
               on main: D-0230 section 7). D-0231 has since fixed the propagator, which
               now kills every state of the next layer with nothing to cite
               ([Regular.alphabet_hull]); the reader's check stays, as the direct
               statement that the constraint is false. *)
            let dead_letter = function
              | Model.Const v -> v < smin || v > smax
              | Model.Var _ -> false
            in
            if w > 1_000_000 || nq * w > 10_000_000 then
              refuse pos kw "a transition table of %d states over %d symbols is too large"
                nq w;
            if List.exists dead_letter xs then post_false st pos kw
            else
              let delta = Array.make (nq * w) 0 in
              List.iter
                (fun (q, v, t) ->
                  let k = (q * w) + (v - smin) in
                  if delta.(k) <> 0 && delta.(k) <> t + 1 then
                    refuse pos kw
                      "state %d has two edges on the symbol %d: a nondeterministic \
                       automaton, and baguette's regular takes a deterministic one"
                      q v;
                  delta.(k) <- t + 1)
                edges;
              let n = List.length xs in
              let flags = List.init ((n + 1) * nq) (fun _ -> ()) in
              let flags =
                List.map (fun () -> Model.Var (fresh_bool st pos "flag")) flags
              in
              post st pos kw
                (Model.Regular
                   {
                     Model.r_xs = xs;
                     r_nq = nq;
                     r_smin = smin;
                     r_delta = delta;
                     r_q0 = 1;
                     r_final =
                       Array.of_list
                         (List.sort_uniq compare (List.map (fun f -> f + 1) finals));
                     r_flags = flags;
                   })
      | _ -> shape pos kw "(X1 ... Xn) nstates ((edges_0) ...) (f1 ... fk)")
  (* ---- misc *)
  | "circuit" ->
      arity 1 "(X1 ... Xn)";
      let xs = operands st (List.hd args) "the successors" in
      let n = List.length xs in
      let range = List.init n (fun i -> i) in
      (* cake's circuit_sem: successors in 0..n-1 numbered from 0, one cycle through all *)
      if n = 0 then ()
      else if n = 1 then restrict st pos kw (List.hd xs) [ 0 ]
      else (
        (* mznlib's fzn_circuit, on the index set 0..n-1 with root 0 *)
        post st pos kw (Model.All_different xs);
        List.iteri
          (fun i x ->
            restrict st pos kw x range;
            post st pos kw (Model.Int_ne (x, Model.Const i)))
          xs;
        let ps = List.init (n - 1) (fun _ -> ()) in
        let ps =
          List.map
            (fun () -> Model.Var (new_aux st pos "pos" (Model.Drange (1, n - 1))))
            ps
        in
        post st pos kw (Model.Circuit { Model.cir_x = xs; cir_pos = ps; cir_root = 0 }))
  (* ---- the comparisons, last as in cake's dispatch *)
  | _ -> (
      let stem, reif = reif_of kw in
      match cmp_of_kw stem with
      | None -> refuse pos kw "baguette's .scp reader does not take this keyword"
      | Some c -> (
          let lit, rest =
            match (reif, args) with
            | `None, _ -> (Ltrue, args)
            | `If, _ ->
                refuse pos kw
                  "a half reification (`_if`) has no propagator in baguette (D-0228 \
                   section 14)"
            | `Iff, z :: rest -> (cond st kw z, rest)
            | `Iff, [] -> shape pos kw "a condition (Z op v), then X Y"
          in
          match rest with
          | [ x; y ] -> (
              let x = operand st x and y = operand st y in
              match lit with
              | Ltrue -> post st pos kw (cmp_cstr c x y)
              | Lfalse -> post st pos kw (cmp_cstr (negation c) x y)
              | Lpos b | Lneg b ->
                  if x = Model.Var b || y = Model.Var b then self_reif pos kw;
                  let c = match lit with Lneg _ -> negation c | _ -> c in
                  post st pos kw (cmp_reif pos kw c x y (Model.Var b)))
          | _ -> shape pos kw "X Y after its optional condition"))

(* The keywords cake knows that this reader refuses by name, so the message can say
   which family it is rather than "unknown". *)
let known_refused =
  [
    ( "modulus",
      "baguette decomposes it in FlatZinc, so it has no propagator to read it into" );
    ("parity", "baguette decomposes it in FlatZinc");
    ("element_2d", "no two-dimensional element in baguette");
    ("nvalue", "baguette decomposes it in FlatZinc");
    ("among", "baguette decomposes it in FlatZinc");
    ("at_most_one", "baguette decomposes it in FlatZinc");
    ("all_equal", "baguette decomposes it in FlatZinc");
    ("all_different_except", "baguette decomposes it in FlatZinc");
    ("symmetric_all_different", "baguette decomposes it in FlatZinc");
    ("binpacking", "baguette decomposes it in FlatZinc");
    ("knapsack", "baguette decomposes it in FlatZinc");
    ("min_distance", "no such constraint in baguette");
    ("negative_table", "no negative table in baguette");
    ("smart_table", "no smart table in baguette");
    ("lex_smart_table", "no smart table in baguette");
    ("at_most_one_smart_table", "no smart table in baguette");
    ("mdd", "baguette decomposes it in FlatZinc");
    ("disjunctive", "not read yet: baguette posts it as a cumulative only from FlatZinc");
    ("disjunctive_strict", "baguette decomposes it in FlatZinc");
    ("disjunctive2d", "baguette decomposes it in FlatZinc");
    ("disjunctive2d_strict", "baguette decomposes it in FlatZinc");
    ("cumulative_optional", "optional tasks are decomposed in FlatZinc");
    ("sort", "baguette decomposes it in FlatZinc");
    ("arg_sort", "baguette decomposes it in FlatZinc");
    ("value_precede", "baguette decomposes it in FlatZinc");
    ("seq_precede_chain", "baguette decomposes it in FlatZinc");
  ]

let constraint_ st (e : Sexp.t) =
  match e with
  | Sexp.List (Sexp.Atom (name, np) :: Sexp.Atom (kw, kp) :: args, pos) ->
      if Names.mem st.cnames name then
        Error.failf np
          "the constraint name `%s` is used twice (cake_pb_cp refuses it too)" name;
      Names.replace st.cnames name ();
      (match List.assoc_opt kw known_refused with
      | Some why -> refuse kp kw "%s" why
      | None -> ());
      if String.length kw > 4 && String.sub kw 0 4 = "lex_" then
        refuse kp kw "baguette decomposes the lexicographic constraints in FlatZinc";
      one_constraint st pos kw args
  | e ->
      Error.failf (pos_of e)
        "a constraint is a list (name keyword arguments...), as cake_pb_cp reads it"

(* ------------------------------------------------------------------ the frame *)

let expect_open lx what =
  match Sexp.next lx with
  | Sexp.Open, _ -> ()
  | tok, p -> Error.failf p "expected `(` %s, found %s" what (Sexp.describe tok)

let expect_atom lx a what =
  match Sexp.next lx with
  | Sexp.Tatom b, _ when String.equal a b -> ()
  | tok, p -> Error.failf p "expected `%s` %s, found %s" a what (Sexp.describe tok)

let expect_close lx what =
  match Sexp.next lx with
  | Sexp.Close, _ -> ()
  | tok, p -> Error.failf p "expected `)` %s, found %s" what (Sexp.describe tok)

(* Call [f] on each form of a section, until its `)`. *)
let section_items lx f =
  let rec go () =
    match Sexp.peek lx with
    | Sexp.Close, _ -> ignore (Sexp.next lx)
    | _ ->
        f (Sexp.read lx);
        go ()
  in
  go ()

let variable st (e : Sexp.t) =
  match e with
  | Sexp.List ([ Sexp.Atom (name, np); lb; ub ], _) ->
      if Sexp.int_of_atom np name <> None then
        Error.failf np "the variable name `%s` reads as an integer" name;
      if Names.mem st.file_names name then
        Error.failf np "the variable `%s` is declared twice" name;
      let lb = int_of lb "a lower bound" and ub = int_of ub "an upper bound" in
      if lb > ub then
        Error.failf np
          "the variable `%s` has the bounds %d > %d. cake_pb_cp accepts them (no value, \
           so UNSAT); this reader refuses them, because no model means one (D-0228 \
           section 14)"
          name lb ub;
      let dom = if lb = 0 && ub = 1 then Model.Dbool else Model.Drange (lb, ub) in
      let i = push_var st { Model.v_name = name; v_dom = dom; v_pos = np } in
      Names.replace st.file_names name i
  | e -> Error.failf (pos_of e) "a variable is a list (name lb ub)"

let of_lexer lx : Model.t =
  let st = create () in
  expect_open lx "to open the problem";
  (* (version 1) *)
  (match Sexp.read lx with
  | Sexp.List ([ Sexp.Atom ("version", _); Sexp.Atom (v, vp) ], _) ->
      if v <> "1" then
        Error.failf vp
          "version %s: this reader takes version 1 of the .scp format only, so a later \
           version is never read as version 1 by mistake (D-0228 section 11)"
          v
  | e -> Error.failf (pos_of e) "expected (version 1) as the first section");
  expect_open lx "to open the variables section";
  expect_atom lx "variables" "as the second section";
  section_items lx (variable st);
  st.nfile <- st.nvars;
  expect_open lx "to open the constraints section";
  expect_atom lx "constraints" "as the third section";
  section_items lx (constraint_ st);
  expect_open lx "to open the prob_type section";
  expect_atom lx "prob_type" "as the fourth section";
  let objective =
    match Sexp.read lx with
    | Sexp.Atom (("decide" | "enumerate"), _) -> Model.Satisfy
    | Sexp.List ([ Sexp.Atom ((("minimize" | "maximize") as d), _); Sexp.Atom (x, xp) ], _)
      ->
        let op = Model.Var (lookup st xp x) in
        if d = "minimize" then Model.Minimize op else Model.Maximize op
    | e ->
        Error.failf (pos_of e)
          "the problem type is decide, enumerate, (minimize x) or (maximize x)"
  in
  expect_close lx "to close the prob_type section";
  expect_close lx "to close the problem";
  Sexp.expect_eof lx;
  let vars = Array.sub st.vars 0 st.nvars in
  let output =
    List.init st.nfile (fun i ->
        Model.Out_var (vars.(i).Model.v_name, Model.Oint, Model.Var i))
  in
  F.Builder.normalise_gcc
    { Model.vars; constraints = List.rev st.built_rev; objective; search = []; output }

let of_string ~file s = of_lexer (Sexp.of_string ~file s)

let of_file path =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () -> of_lexer (Sexp.of_channel ~file:path ic))
