(* Ast.model -> Model.t.

   This is where the normative rules of SPEC 2.1 are enforced:

   - a `var int` with no declared domain is rejected with a diagnostic, never defaulted
     to a machine-word range;
   - a builtin outside the implemented set is a hard error that names the builtin,
     never a silent skip.

   [implemented] below is the M1 row of the SPEC 2.1 milestone table. When a propagator
   lands, move its builtin from [planned] to [implemented] in the same commit — that is
   the only place the front end's idea of "supported" is written down. *)

(* SPEC 2.1, milestones M1, M2 and M3. *)
let implemented =
  [
    "int_lin_le";
    "int_lin_eq";
    "int_lin_ne";
    "int_le";
    "int_lt";
    "int_eq";
    "int_ne";
    (* M2, the Boolean row (M2-T1 / M2-T2). *)
    "bool_clause";
    "array_bool_or";
    "array_bool_and";
    "bool2int";
    "bool_eq";
    "bool_not";
    (* M3, the reified row (M3-T2 / M3-T4). *)
    "int_lin_le_reif";
    "int_le_reif";
    "int_eq_reif";
    "int_ne_reif";
    (* M4, the arithmetic row (M4-T4b). *)
    "int_abs";
    "int_times";
    "int_div";
    (* M4, the first global (M4-T1). *)
    "all_different_int";
  ]

(* The rest of the SPEC 2.1 table, with the milestone that will bring it in. Listing
   these separately lets the error say "not yet" rather than "never". *)
let planned = [ ("array_int_element", "M4") ]
let implemented_list = String.concat ", " implemented

type env = {
  scalars : (string, Model.operand) Hashtbl.t;
  arrays : (string, Model.operand array) Hashtbl.t;
  array_dims : (string, (int * int) list) Hashtbl.t;
  mutable vars_rev : Model.var list;
  mutable nvars : int;
  mutable outputs_rev : Model.output_item list;
  (* M4-T4b: how many auxiliary Booleans the arithmetic family has introduced so far.
     It only ever goes up, so the names it makes are unique among themselves; a
     collision with a name the model itself declares is caught by
     lib/flatzinc/compile.ml's [check_name_collisions], which is where the diagnostic
     can say which declaration it clashed with. *)
  mutable naux : int;
}

let new_env () =
  {
    scalars = Hashtbl.create 64;
    arrays = Hashtbl.create 16;
    array_dims = Hashtbl.create 16;
    vars_rev = [];
    nvars = 0;
    outputs_rev = [];
    naux = 0;
  }

let new_var env name dom pos =
  let i = env.nvars in
  env.vars_rev <- { Model.v_name = name; v_dom = dom; v_pos = pos } :: env.vars_rev;
  env.nvars <- i + 1;
  i

(* ------------------------------------------------------------------ name resolution *)

let rec operand env pos (e : Ast.expr) : Model.operand =
  match e with
  | Ast.Int n -> Model.Const n
  | Ast.Bool b -> Model.Const (if b then 1 else 0)
  | Ast.Ident s -> (
      match Hashtbl.find_opt env.scalars s with
      | Some op -> op
      | None ->
          if Hashtbl.mem env.arrays s then
            Error.failf pos "`%s` is an array, but a single value is expected here" s
          else Error.failf pos "undeclared identifier `%s`" s)
  | Ast.Access (s, ix) ->
      let arr =
        match Hashtbl.find_opt env.arrays s with
        | Some a -> a
        | None ->
            if Hashtbl.mem env.scalars s then
              Error.failf pos "`%s` is not an array, so it cannot be indexed" s
            else Error.failf pos "undeclared identifier `%s`" s
      in
      let lo =
        match Hashtbl.find_opt env.array_dims s with Some ((l, _) :: _) -> l | _ -> 1
      in
      let i = const_of env pos (Printf.sprintf "the index of `%s`" s) ix in
      if i < lo || i - lo >= Array.length arr then
        Error.failf pos "index %d is out of bounds for array `%s` (%d..%d)" i s lo
          (lo + Array.length arr - 1)
      else arr.(i - lo)
  | Ast.Array _ ->
      Error.failf pos "an array literal is used where a single value is expected"
  | Ast.Set _ -> Error.failf pos "a set literal is used where a single value is expected"
  | Ast.Range _ -> Error.failf pos "a range is used where a single value is expected"
  | Ast.String _ -> Error.failf pos "a string is used where a single value is expected"
  | Ast.Call (f, _) -> Error.failf pos "`%s(...)` is an annotation, not a value" f

and const_of env pos what e =
  match operand env pos e with
  | Model.Const n -> n
  | Model.Var i ->
      Error.failf pos "%s must be a constant, but variable `%s` was given" what
        (match List.nth_opt (List.rev env.vars_rev) i with
        | Some v -> v.Model.v_name
        | None -> Printf.sprintf "<var %d>" i)

(* Resolve an expression that must denote an array of values. *)
let operands env pos (e : Ast.expr) : Model.operand list =
  match e with
  | Ast.Array es -> List.map (operand env pos) es
  | Ast.Ident s when Hashtbl.mem env.arrays s -> Array.to_list (Hashtbl.find env.arrays s)
  | Ast.Ident s when Hashtbl.mem env.scalars s ->
      Error.failf pos "`%s` is not an array, but an array is expected here" s
  | Ast.Ident s -> Error.failf pos "undeclared identifier `%s`" s
  | _ -> Error.failf pos "expected an array, found `%s`" (Ast.string_of_expr e)

let as_const pos ~builtin ~what (op : Model.operand) =
  match op with
  | Model.Const n -> n
  | Model.Var _ ->
      Error.failf pos "builtin `%s`: %s must be a constant, not a variable" builtin what

(* ------------------------------------------------------------------- declarations *)

let sorted_uniq ns = List.sort_uniq compare ns

let domain_of_base pos name (bt : Ast.base_type) =
  match bt with
  | Ast.Tbool -> Model.Dbool
  | Ast.Tint ->
      Error.failf pos
        "`%s` is declared `var int` with no domain; SPEC 2.1 requires every integer \
         variable to have a finite declared domain (write for example `var 0..10: %s;`)"
        name name
  | Ast.Trange (l, u) ->
      if l > u then Error.failf pos "`%s` has the empty domain %d..%d" name l u
      else Model.Drange (l, u)
  | Ast.Tset [] -> Error.failf pos "`%s` has an empty domain" name
  | Ast.Tset ns -> Model.Dset (sorted_uniq ns)

let check_par_domain pos name (bt : Ast.base_type) n =
  match bt with
  | Ast.Trange (l, u) when n < l || n > u ->
      Error.failf pos "parameter `%s` = %d is outside its declared domain %d..%d" name n l
        u
  | Ast.Tset ns when ns <> [] && not (List.mem n ns) ->
      Error.failf pos "parameter `%s` = %d is outside its declared domain {%s}" name n
        (String.concat "," (List.map string_of_int ns))
  | _ -> ()

(* The declared base type, reduced to what the printer needs (SPEC 2.2: a bool prints as
   false/true, an integer as a decimal). This is where an output item's type is captured,
   and it is the only place it can be: one line later the declaration is gone and all
   that is left is an operand, which for a folded parameter is an indistinguishable
   [Model.Const 1].

   Deliberately total, rather than a detour through [domain_of_base]: that one *rejects*
   a `var int` with no domain, which is right for a scalar declaration but would newly
   reject `array [1..2] of var int: xs = [x, y];`, whose elements carry their own
   declared domains. *)
let out_ty_of_base (bt : Ast.base_type) =
  match bt with
  | Ast.Tbool -> Model.Obool
  | Ast.Tint | Ast.Trange _ | Ast.Tset _ -> Model.Oint

(* A `var bool` aliased to a constant must be aliased to a *Boolean* constant. Nothing
   else in the front end looks at this: [check_par_domain] is about `par` declarations,
   and `bool` has no syntax for a domain to check against. Without it, an ill-typed
   `var bool: b = 3;` would travel all the way to the printer, which can only raise on it
   — an error message about the store, thrown at output time, for a mistake that is right
   here in the declaration. *)
let check_bool_alias pos name (bt : Ast.base_type) (op : Model.operand) =
  match (bt, op) with
  | Ast.Tbool, Model.Const n when n <> 0 && n <> 1 ->
      Error.failf pos
        "`%s` is declared `var bool` but is assigned %d, which is not a Boolean value"
        name n
  | _ -> ()

let record_scalar_output env ty (d : Ast.decl) op =
  if Ast.has_flag_annot "output_var" d.Ast.d_annots then
    env.outputs_rev <- Model.Out_var (d.Ast.d_name, ty, op) :: env.outputs_rev

let dims_of_output_annot pos (args : Ast.expr list) default =
  match args with
  | [ Ast.Array ranges ] ->
      List.map
        (function
          | Ast.Range (l, u) -> (l, u)
          | e ->
              Error.failf pos "`output_array` expects an array of ranges, found `%s`"
                (Ast.string_of_expr e))
        ranges
  | _ -> default

let record_array_output env pos ty (d : Ast.decl) dims elems =
  match Ast.find_call_annot "output_array" d.Ast.d_annots with
  | None -> ()
  | Some args ->
      let dims = dims_of_output_annot pos args dims in
      env.outputs_rev <-
        Model.Out_array (d.Ast.d_name, dims, ty, Array.to_list elems) :: env.outputs_rev

let bind_scalar env pos name op =
  if Hashtbl.mem env.scalars name || Hashtbl.mem env.arrays name then
    Error.failf pos "`%s` is declared more than once" name;
  Hashtbl.replace env.scalars name op

let bind_array env pos name dims elems =
  if Hashtbl.mem env.scalars name || Hashtbl.mem env.arrays name then
    Error.failf pos "`%s` is declared more than once" name;
  Hashtbl.replace env.arrays name elems;
  Hashtbl.replace env.array_dims name dims

let add_par_scalar env (d : Ast.decl) bt =
  let pos = d.Ast.d_pos and name = d.Ast.d_name in
  match d.Ast.d_value with
  | None -> Error.failf pos "parameter `%s` has no value" name
  | Some e -> (
      match operand env pos e with
      | Model.Var _ ->
          Error.failf pos
            "parameter `%s` is assigned a variable; parameters must be fixed" name
      | Model.Const n ->
          check_par_domain pos name bt n;
          bind_scalar env pos name (Model.Const n))

let add_var_scalar env (d : Ast.decl) bt =
  let pos = d.Ast.d_pos and name = d.Ast.d_name in
  (* Run the domain check even when the declaration is an alias: SPEC 2.1 rejects a
     `var int` without a domain unconditionally. *)
  let dom = domain_of_base pos name bt in
  let op =
    match d.Ast.d_value with
    | Some e -> operand env pos e
    | None -> Model.Var (new_var env name dom pos)
  in
  check_bool_alias pos name bt op;
  bind_scalar env pos name op;
  record_scalar_output env (out_ty_of_base bt) d op

let add_par_array env (d : Ast.decl) ix bt =
  let pos = d.Ast.d_pos and name = d.Ast.d_name in
  match d.Ast.d_value with
  | None -> Error.failf pos "parameter array `%s` has no value" name
  | Some e ->
      let ops = operands env pos e in
      List.iter
        (fun op ->
          match op with
          | Model.Var _ ->
              Error.failf pos
                "parameter array `%s` contains a variable; parameters must be fixed" name
          | Model.Const n -> check_par_domain pos name bt n)
        ops;
      let len = List.length ops in
      let lo, hi =
        match ix with
        | Ast.Ix_range (l, u) ->
            if u - l + 1 <> len then
              Error.failf pos
                "array `%s` is declared over %d..%d (%d element(s)) but its initialiser \
                 has %d"
                name l u
                (u - l + 1)
                len
            else (l, u)
        | Ast.Ix_int -> (1, len)
      in
      bind_array env pos name [ (lo, hi) ] (Array.of_list ops)

let add_var_array env (d : Ast.decl) ix bt =
  let pos = d.Ast.d_pos and name = d.Ast.d_name in
  let elems =
    match d.Ast.d_value with
    | Some e ->
        let ops = operands env pos e in
        let len = List.length ops in
        (match ix with
        | Ast.Ix_range (l, u) when u - l + 1 <> len ->
            Error.failf pos
              "array `%s` is declared over %d..%d (%d element(s)) but its initialiser \
               has %d"
              name l u
              (u - l + 1)
              len
        | _ -> ());
        List.iter (check_bool_alias pos name bt) ops;
        Array.of_list ops
    | None -> (
        match ix with
        | Ast.Ix_int ->
            Error.failf pos
              "array `%s` is declared `array[int]` and has no initialiser, so its length \
               is unknown"
              name
        | Ast.Ix_range (l, u) ->
            let dom = domain_of_base pos name bt in
            let len = u - l + 1 in
            if len < 0 then
              Error.failf pos "array `%s` has the empty index set %d..%d" name l u;
            let a = Array.make (max len 0) (Model.Const 0) in
            for k = 0 to len - 1 do
              a.(k) <-
                Model.Var (new_var env (Printf.sprintf "%s[%d]" name (l + k)) dom pos)
            done;
            a)
  in
  let lo, hi =
    match ix with Ast.Ix_range (l, u) -> (l, u) | Ast.Ix_int -> (1, Array.length elems)
  in
  bind_array env pos name [ (lo, hi) ] elems;
  record_array_output env pos (out_ty_of_base bt) d [ (lo, hi) ] elems

let add_decl env (d : Ast.decl) =
  match d.Ast.d_ti with
  | Ast.Par bt -> add_par_scalar env d bt
  | Ast.Var bt -> add_var_scalar env d bt
  | Ast.Arr (ix, Ast.Par bt) -> add_par_array env d ix bt
  | Ast.Arr (ix, Ast.Var bt) -> add_var_array env d ix bt
  | Ast.Arr (_, Ast.Arr _) ->
      Error.failf d.Ast.d_pos
        "`%s`: arrays of arrays are not supported (SPEC 2.1 allows array[int] of a base \
         type only)"
        d.Ast.d_name

(* --------------------------------------------------------------------- constraints *)

let unsupported_builtin pos id =
  match List.assoc_opt id planned with
  | Some ms ->
      Error.failf pos
        "unsupported builtin `%s`: it belongs to the accepted FlatZinc subset but is \
         scheduled for milestone %s (docs/ROADMAP.md); implemented builtins are: %s"
        id ms implemented_list
  | None ->
      Error.failf pos
        "unknown builtin `%s`: it is outside the FlatZinc subset baguette accepts \
         (docs/SPEC.md section 2.1); implemented builtins are: %s"
        id implemented_list

let build_constraint env (c : Ast.constraint_item) =
  let pos = c.Ast.c_pos in
  let id = c.Ast.c_id in
  let arity k =
    let got = List.length c.Ast.c_args in
    if got <> k then
      Error.failf pos "builtin `%s` expects %d argument(s) but was given %d" id k got
  in
  let cmp make =
    arity 2;
    match c.Ast.c_args with
    | [ a; b ] -> make (operand env pos a) (operand env pos b)
    | _ -> Error.failf pos "builtin `%s`: internal arity mismatch" id
  in
  (* `as`, `bs`, `c` folded into (terms, rhs) -- shared by the plain linear builtins
     and by [int_lin_le_reif], which is the same three arguments with a reifier after
     them. Folding it once is the M1-T7 rule that the row and the propagator read one
     normalised list, applied one argument earlier. *)
  let lin_terms ca va ra =
    let coeffs =
      List.map
        (fun op -> as_const pos ~builtin:id ~what:"every coefficient" op)
        (operands env pos ca)
    in
    let vars = operands env pos va in
    let nc = List.length coeffs and nv = List.length vars in
    if nc <> nv then
      Error.failf pos
        "builtin `%s`: the coefficient array has %d element(s) but the variable array \
         has %d"
        id nc nv;
    let rhs0 =
      as_const pos ~builtin:id ~what:"the right-hand side" (operand env pos ra)
    in
    let terms, rhs =
      List.fold_left2
        (fun (ts, r) coeff op ->
          match op with
          | Model.Var i -> ((coeff, i) :: ts, r)
          | Model.Const n -> (ts, r - (coeff * n)))
        ([], rhs0) coeffs vars
    in
    (List.rev terms, rhs)
  in
  let lin_reif make =
    arity 4;
    match c.Ast.c_args with
    | [ ca; va; ra; r ] ->
        let terms, rhs = lin_terms ca va ra in
        make terms rhs (operand env pos r)
    | _ -> Error.failf pos "builtin `%s`: internal arity mismatch" id
  in
  (* A reified comparison: the two operands of the unreified builtin, then the
     reifier. Nothing here checks that the reifier is Boolean -- compile.ml does, where
     the declarations are in hand. *)
  let cmp_reif make =
    arity 3;
    match c.Ast.c_args with
    | [ a; b; r ] -> make (operand env pos a) (operand env pos b) (operand env pos r)
    | _ -> Error.failf pos "builtin `%s`: internal arity mismatch" id
  in
  let lin make =
    arity 3;
    match c.Ast.c_args with
    | [ ca; va; ra ] ->
        let terms, rhs = lin_terms ca va ra in
        make terms rhs
    | _ -> Error.failf pos "builtin `%s`: internal arity mismatch" id
  in
  (* M2: two arrays (`bool_clause`), and an array followed by a scalar (the two
     reified array forms). Nothing here decides whether an operand is Boolean --
     lib/flatzinc/compile.ml does, where the variable declarations are in hand and the
     diagnostic can say which variable and what it was declared as. This function's job
     is arity and shape, exactly as it is for the integer builtins above. *)
  let two_arrays make =
    arity 2;
    match c.Ast.c_args with
    | [ a; b ] -> make (operands env pos a) (operands env pos b)
    | _ -> Error.failf pos "builtin `%s`: internal arity mismatch" id
  in
  let one_array make =
    arity 1;
    match c.Ast.c_args with
    | [ a ] -> make (operands env pos a)
    | _ -> Error.failf pos "builtin `%s`: internal arity mismatch" id
  in
  let array_scalar make =
    arity 2;
    match c.Ast.c_args with
    | [ a; r ] -> make (operands env pos a) (operand env pos r)
    | _ -> Error.failf pos "builtin `%s`: internal arity mismatch" id
  in
  (* ---------------------------------------------------------------- M4-T4b

     The arithmetic family is the first one whose front end CREATES variables. The
     reason is structural and is stated in lib/core/prop/arith.ml's header: x * y = z
     has no linear row, the case split that gives it one is guarded by Booleans, and
     lib/flatzinc/compile.ml builds the store from [Model.vars] as a fixed array --
     so a Boolean invented there would arrive after the store exists. The builder is
     the last place early enough.

     Only the auxiliaries that will actually be USED are created. An auxiliary that
     no row mentions would be a free variable of the model, and
     [Model.check_assignment] checks each one against its own definition, so a free
     one could be assigned a value its definition forbids and turn a correct solution
     into an I-S1 failure. The three rules below therefore have to agree with the
     paths compile.ml takes, and compile.ml is written to make that agreement cheap:
     it posts the definition of every auxiliary the constraint carries before it
     chooses a path, so an auxiliary is never left undefined even if a path stops
     using it. *)
  let var_bounds i =
    match List.nth_opt (List.rev env.vars_rev) i with
    | Some { Model.v_dom = Model.Dbool; _ } -> (0, 1)
    | Some { Model.v_dom = Model.Drange (l, u); _ } -> (l, u)
    | Some { Model.v_dom = Model.Dset (n :: ns); _ } ->
        (List.fold_left Stdlib.min n ns, List.fold_left Stdlib.max n ns)
    | Some { Model.v_dom = Model.Dset []; _ } | None ->
        Error.failf pos "internal: builtin `%s` mentions variable index %d" id i
  in
  let fresh_bool () =
    let n = env.naux in
    env.naux <- n + 1;
    new_var env (Printf.sprintf "X_INTRODUCED_arith_%d" n) Model.Dbool pos
  in
  (* `b <-> x >= 0`, and only when the declared domain of x leaves the sign open. *)
  let sign_bool (x : Model.operand) =
    match x with
    | Model.Const _ -> None
    | Model.Var i ->
        let lo, hi = var_bounds i in
        if lo >= 0 || hi < 0 then None else Some (fresh_bool ())
  in
  (* `b_v <-> y >= v` for every v strictly inside y's declared domain, smallest first.
     Written as a loop and not [List.init], because [List.init]'s evaluation order is
     unspecified and [fresh_bool] has a side effect: a proof whose variable numbering
     changes between runs is a proof nobody can diff. *)
  let ladder_bools (y : Model.operand) =
    match y with
    | Model.Const _ -> []
    | Model.Var j ->
        let lo, hi = var_bounds j in
        let acc = ref [] in
        for v = lo + 1 to hi do
          acc := (v, fresh_bool ()) :: !acc
        done;
        List.rev !acc
  in
  let arity3 f =
    arity 3;
    match c.Ast.c_args with
    | [ a; b; r ] -> f (operand env pos a) (operand env pos b) (operand env pos r)
    | _ -> Error.failf pos "builtin `%s`: internal arity mismatch" id
  in
  let k =
    match id with
    | "int_lin_le" -> lin (fun ts r -> Model.Int_lin_le (ts, r))
    | "int_lin_eq" -> lin (fun ts r -> Model.Int_lin_eq (ts, r))
    | "int_lin_ne" -> lin (fun ts r -> Model.Int_lin_ne (ts, r))
    | "int_le" -> cmp (fun a b -> Model.Int_le (a, b))
    | "int_lt" -> cmp (fun a b -> Model.Int_lt (a, b))
    | "int_eq" -> cmp (fun a b -> Model.Int_eq (a, b))
    | "int_ne" -> cmp (fun a b -> Model.Int_ne (a, b))
    | "bool_clause" -> two_arrays (fun ps ns -> Model.Bool_clause (ps, ns))
    | "array_bool_or" -> array_scalar (fun xs r -> Model.Array_bool_or (xs, r))
    | "array_bool_and" -> array_scalar (fun xs r -> Model.Array_bool_and (xs, r))
    | "bool2int" -> cmp (fun b x -> Model.Bool2int (b, x))
    | "bool_eq" -> cmp (fun a b -> Model.Bool_eq (a, b))
    | "bool_not" -> cmp (fun a b -> Model.Bool_not (a, b))
    (* M4-T1. One array argument, and the operands are kept exactly as written --
       duplicates and constants included. `all_different_int([x, x])` is UNSAT and
       `all_different_int([x, 1])` is `x <> 1`, and both fall out of the pairwise rows
       lib/flatzinc/compile.ml posts with no special case, which is the same reason
       [normalise_terms] is not applied to a linear row's duplicates here. *)
    | "all_different_int" -> one_array (fun xs -> Model.All_different xs)
    | "int_lin_le_reif" -> lin_reif (fun ts rhs r -> Model.Int_lin_le_reif (ts, rhs, r))
    | "int_le_reif" -> cmp_reif (fun a b r -> Model.Int_le_reif (a, b, r))
    | "int_eq_reif" -> cmp_reif (fun a b r -> Model.Int_eq_reif (a, b, r))
    | "int_ne_reif" -> cmp_reif (fun a b r -> Model.Int_ne_reif (a, b, r))
    (* M4. `int_times(x, c, z)` with a constant second factor is c*x = z, an ordinary
       linear equality, so it needs neither ladder nor sign and gets neither.
       `int_div` keeps its sign split whatever the divisor is, because truncation
       toward zero is what the sign decides (D-0033); it drops both auxiliaries only
       when both operands are constants and the quotient is a number. *)
    | "int_times" ->
        arity3 (fun x y z ->
            let aux =
              match y with
              | Model.Const _ -> { Model.x_sign = None; y_ge = [] }
              | Model.Var _ ->
                  let x_sign = sign_bool x in
                  { Model.x_sign; y_ge = ladder_bools y }
            in
            Model.Int_times (x, y, z, aux))
    | "int_div" ->
        arity3 (fun x y q ->
            let aux =
              match (x, y) with
              | Model.Const _, Model.Const _ -> { Model.x_sign = None; y_ge = [] }
              | _ -> { Model.x_sign = sign_bool x; y_ge = ladder_bools y }
            in
            Model.Int_div (x, y, q, aux))
    | "int_abs" ->
        cmp (fun x z -> Model.Int_abs (x, z, { Model.x_sign = sign_bool x; y_ge = [] }))
    | other -> unsupported_builtin pos other
  in
  { Model.k; Model.c_pos = pos }

(* ----------------------------------------------------------- search annotations *)

let rec search_of_annot env pos (a : Ast.expr) =
  match a with
  | Ast.Call ((("int_search" | "bool_search") as nm), args) -> (
      match args with
      | vs :: vsel :: valsel :: _rest ->
          let idxs =
            List.map
              (fun op ->
                match op with
                | Model.Var i -> i
                | Model.Const _ ->
                    Error.failf pos
                      "`%s`: the search array must contain variables, not constants" nm)
              (operands env pos vs)
          in
          let vc =
            match vsel with
            | Ast.Ident "input_order" -> Model.Input_order
            | Ast.Ident "first_fail" -> Model.First_fail
            | e ->
                Error.failf pos
                  "`%s`: unsupported variable-selection strategy `%s`; SPEC 3.4 supports \
                   input_order and first_fail"
                  nm (Ast.string_of_expr e)
          in
          let vl =
            match valsel with
            | Ast.Ident "indomain_min" -> Model.Indomain_min
            | Ast.Ident "indomain_max" -> Model.Indomain_max
            | e ->
                Error.failf pos
                  "`%s`: unsupported value-choice strategy `%s`; SPEC 3.4 supports \
                   indomain_min and indomain_max"
                  nm (Ast.string_of_expr e)
          in
          Some (Model.Int_search (idxs, vc, vl))
      | _ ->
          Error.failf pos
            "`%s` expects at least 3 arguments (variables, variable choice, value choice)"
            nm)
  | Ast.Call ("seq_search", [ Ast.Array subs ]) ->
      Some (Model.Seq (List.filter_map (search_of_annot env pos) subs))
  | Ast.Call ("seq_search", _) ->
      Error.failf pos "`seq_search` expects a single array of search annotations"
  | _ ->
      (* Not a search annotation. Annotations that are not search strategies (for
         example `var_is_introduced`, `defines_var`) carry no obligation for the solver
         and are ignored; only *builtins* are normatively must-error. *)
      None

(* ---------------------------------------------------------------------- entry point *)

let build (m : Ast.model) : Model.t =
  let env = new_env () in
  List.iter (add_decl env) m.Ast.decls;
  let constraints = List.map (build_constraint env) m.Ast.constraints in
  let objective =
    match m.Ast.solve with
    | Ast.Satisfy -> Model.Satisfy
    | Ast.Minimize e -> Model.Minimize (operand env m.Ast.solve_pos e)
    | Ast.Maximize e -> Model.Maximize (operand env m.Ast.solve_pos e)
  in
  let search = List.filter_map (search_of_annot env m.Ast.solve_pos) m.Ast.solve_annots in
  {
    Model.vars = Array.of_list (List.rev env.vars_rev);
    constraints;
    objective;
    search;
    output = List.rev env.outputs_rev;
  }

let of_string ~file src = build (Parser.parse_string ~file src)
let of_file path = build (Parser.parse_file path)
