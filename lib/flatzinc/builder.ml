(* Ast.model -> Model.t.

   This is where the normative rules of SPEC 2.1 are enforced:

   - a `var int` with no declared domain is given the domain the model's own constraints
     imply ([infer_domains], M7-T19, D-0083), and is rejected with a diagnostic if they
     imply none -- never defaulted to a machine-word range;
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
    (* M4, the second (M4-T3). *)
    "array_int_element";
    (* M7-T16, the third: all_different's generalisation. TWO SPELLINGS, and the second
       is not a synonym for convenience: mznlib/fzn_global_cardinality.mzn has to give
       `fzn_global_cardinality' a BODY, because std hands it counts declared `var int'
       with no domain and the decomposition this replaces was what used to imply their
       0..|x| bound. That body states the bound and calls the bodyless
       `baguette_global_cardinality', which is what reaches the .fzn from MiniZinc. The
       fzn_ name stays accepted because the test models are written in it and because a
       hand-written .fzn should not have to know about the library's internals. *)
    "fzn_global_cardinality";
    "baguette_global_cardinality";
  ]

(* The rest of the SPEC 2.1 table, with the milestone that will bring it in. Listing
   these separately lets the error say "not yet" rather than "never".

   M4-T3 emptied this list: every builtin docs/SPEC.md 2.1 names is now implemented. It
   stays, with its machinery, because the next row to widen the subset needs exactly
   this and because an empty list is what [unsupported_builtin] must go on saying
   "never" from. *)
let planned : (string * string) list = []
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
  (* M7-T19 (D-0083): the variables declared `var int` with NO domain, newest first. Each
     holds a placeholder domain until [infer_domains] replaces it; one that inference
     cannot bound is refused by [refuse_unbounded], exactly as SPEC 2.1 refused all of
     them before. *)
  mutable undomained_rev : int list;
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
    undomained_rev = [];
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

(* [Ast.Tint] -- `var int` with no domain -- is not a domain and never reaches here: the
   two declaration sites route it to [new_undomained_var] (M7-T19, D-0083). *)
let domain_of_base pos name (bt : Ast.base_type) =
  match bt with
  | Ast.Tbool -> Model.Dbool
  | Ast.Tint ->
      Error.failf pos "internal: `%s` (`var int`, no domain) reached [domain_of_base]"
        name
  | Ast.Trange (l, u) ->
      if l > u then Error.failf pos "`%s` has the empty domain %d..%d" name l u
      else Model.Drange (l, u)
  | Ast.Tset [] -> Error.failf pos "`%s` has an empty domain" name
  | Ast.Tset ns -> Model.Dset (sorted_uniq ns)

(* ------------------------------------------- M7-T19: bounds inference (D-0083)

   docs/SPEC.md 2.1, as amended 2026-10-01: a `var int` declared with NO domain is given
   the domain its model's own constraints IMPLY, and is refused only if they imply none.
   MiniZinc 2.10 writes these for sums of bounded terms it did not bother to bound
   (D-0079 counted four corpus instances refused for it).

   WHY INFERENCE AND NOT A DEFAULT RANGE. The order encoding is width-proportional
   (D-0028): a default of, say, -10^6..10^6 is two million ladder clauses paid BLIND, for
   every such variable, whatever the model needs. An inferred bound is the width the model
   itself licenses, and nothing the model does not.

   WHY IT IS SOUND. Every rule below derives a bound that EVERY SOLUTION of the one
   constraint it reads satisfies, so the inferred domain contains every value the variable
   takes in any solution of the model: declaring it removes no solution, and the encoded
   model has exactly the solutions of the FlatZinc one. That is the obligation, and it is
   the front end's, like the rest of compile.ml's encoding -- veripb checks the proof
   against the .opb the inferred domain is written into, and cannot see the inference.
   Every arithmetic step is [Baguette_core.Checked] (D-0029: a wrapped bound is a wrong
   domain with an accepted proof); a step that would overflow derives NOTHING for that
   constraint on that pass, it never wraps and never guesses.

   A bound only ever TIGHTENS, and only on an undomained variable; a declared domain is
   read, never changed. If inference crosses the bounds (lo > hi) the model has no
   solution at all, and any domain is then sound: the variable is declared on the hull
   hi..lo of the two crossed bounds and the solver proves the UNSAT as it would any
   other.

   THE RULES (each one line in D-0083). Terms with a constant operand are folded into the
   right-hand side first, and a variable repeated in a row has its coefficients merged.
     int_lin_eq / int_lin_le   solve the row for each term, given the bounds the OTHER
                               terms need (eq: both sides; le: one side)
     int_eq / int_le / int_lt  as the rows a-b = 0, a-b <= 0, a-b <= -1
     bool2int(b, x)            x in 0..1
     int_abs(x, z)             z >= 0; z <= max|x|; x in -hi(z)..hi(z)
     int_times(x, y, z)        z in the four-corner product of x and y (Interval)
     int_div(x, y, q)          |q| <= max|x| (|y| >= 1 wherever the relation holds)
     array_int_element(i,a,c)  i in 1..|a|, c in min(a)..max(a)
     global_cardinality counts each in 0..|xs|
     case split                if c then x = e1 else x = e2, written as int_eq_reif
                               under two-literal bool_clause implications: x in the
                               hull of e1's and e2's bounds
   Everything else (reified forms, int_ne, all_different, clauses) implies no bound and
   is not read. At most [infer_max_passes] passes, stopping at the first pass that changes
   nothing: every intermediate state is sound, so the cap costs precision, never
   soundness. *)

let undomained_placeholder = Model.Drange (0, 0)

let new_undomained_var env name pos =
  let i = new_var env name undomained_placeholder pos in
  env.undomained_rev <- i :: env.undomained_rev;
  i

let infer_max_passes = 64

(* What one constraint says about bounds, over variable indices. *)
type fact =
  | F_lin of (int * int) list * int * bool (* merged terms, rhs, is_equality *)
  | F_range of int * int * int (* var, lo, hi *)
  | F_abs of Model.operand * int (* x, z *)
  | F_times of Model.operand * Model.operand * int (* x, y, z *)
  | F_div of Model.operand * int (* x, q *)
  (* The case split's two inputs (rule "case split" below). [F_reif_eq (x, e, p)]:
     `p -> x = e`, from `int_eq_reif`. [F_imp ((c, pol), p)]: the literal `c = pol`
     implies `p`, from a two-literal `bool_clause`. Neither bounds anything alone. *)
  | F_reif_eq of int * Model.operand * int
  | F_imp of (int * bool) * int

let fact_vars = function
  | F_lin (ts, _, _) -> List.map snd ts
  | F_range (v, _, _) -> [ v ]
  | F_abs (x, z) -> ( match x with Model.Var i -> [ i; z ] | Model.Const _ -> [ z ])
  | F_times (x, y, z) ->
      List.filter_map
        (function Model.Var i -> Some i | Model.Const _ -> None)
        [ x; y; Model.Var z ]
  | F_div (x, q) -> ( match x with Model.Var i -> [ i; q ] | Model.Const _ -> [ q ])
  | F_reif_eq (x, e, _) -> (
      match e with Model.Var j -> [ x; j ] | Model.Const _ -> [ x ])
  | F_imp _ -> []

(* Merge repeated variables and drop zero coefficients; the constant part goes to the
   rhs. Checked, because the folding is arithmetic on model integers. *)
let lin_fact (terms : (int * Model.operand) list) rhs eq =
  let module C = Baguette_core.Checked in
  let tbl = Hashtbl.create 8 and order = ref [] in
  let rhs =
    List.fold_left
      (fun r (a, op) ->
        match op with
        | Model.Const n -> C.sub r (C.mul a n)
        | Model.Var i ->
            (match Hashtbl.find_opt tbl i with
            | Some c -> Hashtbl.replace tbl i (C.add c a)
            | None ->
                order := i :: !order;
                Hashtbl.replace tbl i a);
            r)
      rhs terms
  in
  let ts =
    List.filter_map
      (fun i ->
        let a = Hashtbl.find tbl i in
        if a = 0 then None else Some (a, i))
      (List.rev !order)
  in
  F_lin (ts, rhs, eq)

(* The bound-carrying constraints, read straight from the syntax. A constraint this
   cannot resolve contributes nothing here: the real pass ([build_constraint]) resolves it
   again and reports the error there, with the message it has always had. *)
let facts_of env (c : Ast.constraint_item) : fact list =
  let pos = c.Ast.c_pos in
  let op e = operand env pos e and ops e = operands env pos e in
  let const e =
    match operand env pos e with Model.Const n -> n | Model.Var _ -> raise Not_found
  in
  let var_of = function Model.Var i -> Some i | Model.Const _ -> None in
  try
    match (c.Ast.c_id, c.Ast.c_args) with
    | ("int_lin_eq" | "int_lin_le"), [ ca; va; ra ] ->
        let coeffs =
          List.map (function Model.Const n -> n | _ -> raise Not_found) (ops ca)
        in
        let vs = ops va in
        if List.length coeffs <> List.length vs then []
        else [ lin_fact (List.combine coeffs vs) (const ra) (c.Ast.c_id = "int_lin_eq") ]
    | "int_eq", [ a; b ] -> [ lin_fact [ (1, op a); (-1, op b) ] 0 true ]
    | "int_le", [ a; b ] -> [ lin_fact [ (1, op a); (-1, op b) ] 0 false ]
    | "int_lt", [ a; b ] -> [ lin_fact [ (1, op a); (-1, op b) ] (-1) false ]
    | "bool2int", [ _; x ] -> (
        match var_of (op x) with Some i -> [ F_range (i, 0, 1) ] | None -> [])
    | "int_abs", [ x; z ] -> (
        match var_of (op z) with Some j -> [ F_abs (op x, j) ] | None -> [])
    | "int_times", [ x; y; z ] -> (
        match var_of (op z) with Some j -> [ F_times (op x, op y, j) ] | None -> [])
    | "int_div", [ x; _; q ] -> (
        match var_of (op q) with Some j -> [ F_div (op x, j) ] | None -> [])
    | "array_int_element", [ ia; aa; ra ] -> (
        let vs =
          List.map (function Model.Const n -> n | _ -> raise Not_found) (ops aa)
        in
        let n = List.length vs in
        let idx =
          match var_of (op ia) with Some i when n > 0 -> [ F_range (i, 1, n) ] | _ -> []
        in
        match (var_of (op ra), vs) with
        | Some j, v :: rest ->
            F_range (j, List.fold_left min v rest, List.fold_left max v rest) :: idx
        | _ -> idx)
    | "int_eq_reif", [ a; b; r ] -> (
        match var_of (op r) with
        | None -> []
        | Some p ->
            let a = op a and b = op b in
            List.filter_map Fun.id
              [
                Option.map (fun x -> F_reif_eq (x, b, p)) (var_of a);
                Option.map (fun y -> F_reif_eq (y, a, p)) (var_of b);
              ])
    | "bool_clause", [ pa; na ] -> (
        (* Only the two-literal clauses, and only their implications OF A POSITIVE
           literal -- the case split reads `... -> p`, never `... -> not p`. A constant
           literal makes the clause trivial (true) or drops out (false). *)
        let lits ops truth =
          List.fold_left
            (fun acc o ->
              match (acc, o) with
              | None, _ -> None
              | Some _, Model.Const n when n <> 0 = truth -> None
              | Some l, Model.Const _ -> Some l
              | Some l, Model.Var i -> Some (i :: l))
            (Some []) ops
        in
        match (lits (ops pa) true, lits (ops na) false) with
        | Some [ a; b ], Some [] -> [ F_imp ((a, false), b); F_imp ((b, false), a) ]
        | Some [ a ], Some [ c ] -> [ F_imp ((c, true), a) ]
        | _ -> [])
    | ("fzn_global_cardinality" | "baguette_global_cardinality"), [ xa; _; na ] ->
        let n = List.length (ops xa) in
        List.filter_map
          (fun o -> Option.map (fun i -> F_range (i, 0, n)) (var_of o))
          (ops na)
    | _ -> []
  with Not_found | Error.Error _ | Baguette_core.Checked.Overflow _ -> []

(* The fixpoint. [lo]/[hi] are over EVERY variable; a declared one starts at its declared
   bounds and is never written. Returns the final bounds and the facts, which
   [refuse_unbounded] reads to name a variable's neighbours. *)
let infer_bounds (vars : Model.var array) (undomained : int list) (facts : fact list) =
  let module C = Baguette_core.Checked in
  let n = Array.length vars in
  let lo = Array.make n None and hi = Array.make n None in
  let free = Array.make n false in
  List.iter (fun i -> free.(i) <- true) undomained;
  Array.iteri
    (fun i (v : Model.var) ->
      if not free.(i) then (
        let l, u =
          match v.Model.v_dom with
          | Model.Dbool -> (0, 1)
          | Model.Drange (l, u) -> (l, u)
          | Model.Dset (x :: xs) -> (List.fold_left min x xs, List.fold_left max x xs)
          | Model.Dset [] -> (0, -1)
        in
        lo.(i) <- Some l;
        hi.(i) <- Some u))
    vars;
  let changed = ref false in
  let raise_lo i b =
    if free.(i) then
      match lo.(i) with
      | Some l when l >= b -> ()
      | _ ->
          lo.(i) <- Some b;
          changed := true
  in
  let lower_hi i b =
    if free.(i) then
      match hi.(i) with
      | Some u when u <= b -> ()
      | _ ->
          hi.(i) <- Some b;
          changed := true
  in
  let bounds_of = function
    | Model.Const k -> (Some k, Some k)
    | Model.Var i -> (lo.(i), hi.(i))
  in
  let mag l u = max (C.abs l) (C.abs u) in
  (* sum a*x <= rhs (and >= rhs when [eq]). For each term, the least and greatest the
     OTHER terms can contribute: a running total plus a count of the terms that cannot
     contribute, so a row is O(length), not O(length^2) -- work-task-variation has a row
     with hundreds of terms. *)
  let lin ts rhs eq =
    let contrib (a, i) ~least =
      let want_lo = a > 0 = least in
      match if want_lo then lo.(i) else hi.(i) with
      | Some b -> Some (C.mul a b)
      | None -> None
    in
    let total least =
      List.fold_left
        (fun (s, missing) t ->
          match contrib t ~least with
          | Some c -> (C.add s c, missing)
          | None -> (s, missing + 1))
        (0, 0) ts
    in
    let min_s, min_miss = total true in
    let max_s, max_miss = if eq then total false else (0, 0) in
    List.iter
      (fun ((a, i) as t) ->
        if free.(i) then (
          (* a*x_i <= rhs - (least of the rest) *)
          let own = contrib t ~least:true in
          let rest_miss = min_miss - if own = None then 1 else 0 in
          (if rest_miss = 0 then
             let rest = match own with Some c -> C.sub min_s c | None -> min_s in
             let u = C.sub rhs rest in
             if a > 0 then lower_hi i (C.floordiv u a) else raise_lo i (C.ceildiv u a));
          if eq then
            (* a*x_i >= rhs - (greatest of the rest) *)
            let own = contrib t ~least:false in
            let rest_miss = max_miss - if own = None then 1 else 0 in
            if rest_miss = 0 then
              let rest = match own with Some c -> C.sub max_s c | None -> max_s in
              let l = C.sub rhs rest in
              if a > 0 then raise_lo i (C.ceildiv l a) else lower_hi i (C.floordiv l a)))
      ts
  in
  let apply = function
    | F_lin (ts, rhs, eq) -> lin ts rhs eq
    | F_range (i, l, u) ->
        raise_lo i l;
        lower_hi i u
    | F_abs (x, z) -> (
        raise_lo z 0;
        (match bounds_of x with Some l, Some u -> lower_hi z (mag l u) | _ -> ());
        match (x, hi.(z)) with
        | Model.Var i, Some u ->
            raise_lo i (C.neg u);
            lower_hi i u
        | _ -> ())
    | F_times (x, y, z) -> (
        match (bounds_of x, bounds_of y) with
        | (Some xl, Some xu), (Some yl, Some yu) when xl <= xu && yl <= yu ->
            let p =
              Baguette_core.Interval.product_bounds
                (Baguette_core.Interval.make xl xu)
                (Baguette_core.Interval.make yl yu)
            in
            raise_lo z p.Baguette_core.Interval.lo;
            lower_hi z p.Baguette_core.Interval.hi
        | _ -> ())
    | F_div (x, q) -> (
        match bounds_of x with
        | Some l, Some u ->
            let m = mag l u in
            raise_lo q (C.neg m);
            lower_hi q m
        | _ -> ())
    | F_reif_eq _ | F_imp _ -> ()
  in
  (* THE CASE SPLIT. MiniZinc writes `if c then x = e1 else x = e2 endif` as
       int_eq_reif(x, e1, p1)   int_eq_reif(x, e2, p2)
       bool_clause([p1], [c])   bool_clause([c, p2], [])
     and nothing else bounds x. Every solution has c true or c false; on the true side
     p1 holds and x = e1, on the false side p2 holds and x = e2. So x lies in the HULL of
     what the two sides imply, and only when BOTH sides imply a two-sided bound. A side
     whose implied bounds cross is impossible, and the other side alone bounds x. The
     literal c itself counts as implied on its true side (c may be a reifier). *)
  let reif_by_p = Hashtbl.create 64 and imp = Hashtbl.create 64 in
  List.iter
    (function
      | F_reif_eq (x, e, p) -> if free.(x) then Hashtbl.add reif_by_p p (x, e)
      | F_imp (lit, p) -> Hashtbl.add imp lit p
      | _ -> ())
    facts;
  let cases =
    List.sort_uniq compare (Hashtbl.fold (fun (c, _) _ acc -> c :: acc) imp [])
  in
  let side c pol =
    (* x -> the bounds the side implies for x, intersected over its reifiers *)
    let tbl = Hashtbl.create 8 in
    let ps = Hashtbl.find_all imp (c, pol) @ if pol then [ c ] else [] in
    List.iter
      (fun p ->
        List.iter
          (fun (x, e) ->
            match bounds_of e with
            | Some l, Some u ->
                let l, u =
                  match Hashtbl.find_opt tbl x with
                  | Some (l0, u0) -> (max l l0, min u u0)
                  | None -> (l, u)
                in
                Hashtbl.replace tbl x (l, u)
            | _ -> ())
          (Hashtbl.find_all reif_by_p p))
      ps;
    tbl
  in
  let case_split c =
    let t = side c true and f = side c false in
    let hull x (l1, u1) (l2, u2) =
      match (l1 > u1, l2 > u2) with
      | true, true -> () (* both sides impossible: the model is UNSAT; derive nothing *)
      | true, false ->
          raise_lo x l2;
          lower_hi x u2
      | false, true ->
          raise_lo x l1;
          lower_hi x u1
      | false, false ->
          raise_lo x (min l1 l2);
          lower_hi x (max u1 u2)
    in
    Hashtbl.iter
      (fun x bt -> match Hashtbl.find_opt f x with Some bf -> hull x bt bf | None -> ())
      t
  in
  let pass = ref 0 in
  changed := true;
  while !changed && !pass < infer_max_passes do
    changed := false;
    incr pass;
    List.iter (fun f -> try apply f with C.Overflow _ | Invalid_argument _ -> ()) facts;
    List.iter case_split cases
  done;
  (lo, hi)

(* Replace each undomained variable's placeholder with its inferred domain, and return
   the ones inference could not bound, with what [refuse_unbounded] needs to say why. *)
let infer_domains env (cs : Ast.constraint_item list) =
  if env.undomained_rev = [] then None
  else
    let undomained = List.rev env.undomained_rev in
    let vars = Array.of_list (List.rev env.vars_rev) in
    let facts = List.concat_map (facts_of env) cs in
    let lo, hi = infer_bounds vars undomained facts in
    let unbounded =
      List.filter
        (fun i ->
          match (lo.(i), hi.(i)) with
          | Some l, Some u ->
              (* lo > hi: no solution exists, so any domain is sound; see above. The
                 HULL of the two crossed bounds is used, u..l, which has at least two
                 values. (A singleton would be just as sound; it is avoided because a
                 root-UNSAT row over a singleton-declared variable currently crashes
                 [Justify.emit] -- a pre-existing defect filed as a cross-session
                 request by M7-T19, reproducible with a DECLARED `var 7..7`.) *)
              let l, u = if l > u then (u, l) else (l, u) in
              vars.(i) <- { (vars.(i)) with Model.v_dom = Model.Drange (l, u) };
              false
          | _ -> true)
        undomained
    in
    env.vars_rev <- List.rev (Array.to_list vars);
    match unbounded with [] -> None | _ -> Some (unbounded, vars, facts, lo, hi)

let refuse_unbounded (unbounded, (vars : Model.var array), facts, lo, hi) =
  let i = List.hd unbounded in
  let v = vars.(i) in
  let show = function Some b -> string_of_int b | None -> "none" in
  let mentions = List.filter (fun f -> List.mem i (fact_vars f)) facts in
  let neigh =
    List.sort_uniq compare
      (List.filter (fun j -> j <> i) (List.concat_map fact_vars mentions))
  in
  let describe j =
    let nm = vars.(j).Model.v_name in
    match (lo.(j), hi.(j)) with
    | Some l, Some u -> Printf.sprintf "`%s` (%d..%d)" nm l u
    | l, u -> Printf.sprintf "`%s` (unbounded: lower %s, upper %s)" nm (show l) (show u)
  in
  let rec take k = function x :: r when k > 0 -> x :: take (k - 1) r | _ -> [] in
  let shown = take 6 neigh in
  let neigh_s =
    match neigh with
    | [] -> "it shares no bound-carrying constraint with any variable"
    | _ ->
        Printf.sprintf
          "its neighbours in the %d bound-carrying constraint(s) that mention it are %s%s"
          (List.length mentions)
          (String.concat ", " (List.map describe shown))
          (let more = List.length neigh - List.length shown in
           if more > 0 then Printf.sprintf " and %d more" more else "")
  in
  let others = List.length unbounded - 1 in
  Error.failf v.Model.v_pos
    "`%s` is declared `var int` with no domain, and bounds inference over the model's \
     constraints (docs/SPEC.md section 2.1, D-0083) could not bound it: inferred lower \
     bound %s, upper bound %s; %s.%s SPEC 2.1 requires every integer variable to have a \
     finite domain, declared or inferred, and does not default one to a machine-word \
     range (write for example `var 0..10: %s;`)"
    v.Model.v_name
    (show lo.(i))
    (show hi.(i))
    neigh_s
    (if others > 0 then
       Printf.sprintf " %d other undomained variable(s) could not be bounded either."
         others
     else "")
    v.Model.v_name

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

   Deliberately total, rather than a detour through [domain_of_base]: that one has no
   answer for a `var int` with no domain (M7-T19 routes those to inference instead), and
   `array [1..2] of var int: xs = [x, y];` has elements that carry their own domains. *)
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
  (* M7-T19 (D-0083). An ALIAS needs no domain of its own -- it is its target -- so a
     `var int: x = y;` is no longer refused; a fresh undomained variable waits for
     [infer_domains]. Every other base type is checked here as before. *)
  let op =
    match (d.Ast.d_value, bt) with
    | Some e, _ -> operand env pos e
    | None, Ast.Tint -> Model.Var (new_undomained_var env name pos)
    | None, _ -> Model.Var (new_var env name (domain_of_base pos name bt) pos)
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
            let len = u - l + 1 in
            if len < 0 then
              Error.failf pos "array `%s` has the empty index set %d..%d" name l u;
            let a = Array.make (max len 0) (Model.Const 0) in
            for k = 0 to len - 1 do
              let nm = Printf.sprintf "%s[%d]" name (l + k) in
              a.(k) <-
                Model.Var
                  (match bt with
                  | Ast.Tint -> new_undomained_var env nm pos
                  | _ -> new_var env nm (domain_of_base pos name bt) pos)
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
    (* M7-T16. `fzn_global_cardinality(xs, cover, counts)`. The COVER is an array of
       constants -- SPEC 2.1's form and the only one lib/core/prop/gcc.ml's counting
       rows can be built over -- and [as_const] refuses a variable cover HERE rather
       than in compile.ml so the message carries a source position, the same division
       `array_int_element` below makes for its array.

       The counts are ordinary operands: a count fixed to a number is a variable
       declared on one value, which the propagator handles as the degenerate case.
       compile.ml refuses a literal constant there and says why. *)
    | "fzn_global_cardinality" | "baguette_global_cardinality" -> (
        arity 3;
        match c.Ast.c_args with
        | [ xa; ca; na ] ->
            let cover =
              Array.of_list
                (List.map
                   (fun op ->
                     as_const pos ~builtin:id ~what:"every value of the cover" op)
                   (operands env pos ca))
            in
            Model.Global_cardinality (operands env pos xa, cover, operands env pos na)
        | _ -> Error.failf pos "builtin `%s`: internal arity mismatch" id)
    (* M4-T3. `array_int_element(idx, as, c)`, with `as` an array of CONSTANTS -- the
       only form docs/SPEC.md 2.1 admits. [as_const] is what refuses a variable element,
       and it refuses it HERE rather than in compile.ml so the message carries the
       source position and names the builtin, the same division [lin_terms] makes for a
       linear row's coefficients.

       An empty array and an index whose declared domain misses `1..|as|` are both left
       to fall through: lib/core/prop/element.ml posts a unit row per out-of-range
       position, so both are refuted by the ordinary arithmetic rather than by a special
       case here -- the same reason `all_different_int` above keeps its duplicates. *)
    | "array_int_element" -> (
        arity 3;
        match c.Ast.c_args with
        | [ ia; aa; ra ] ->
            let idx = operand env pos ia in
            let vs =
              Array.of_list
                (List.map
                   (fun op ->
                     as_const pos ~builtin:id ~what:"every element of the array" op)
                   (operands env pos aa))
            in
            Model.Array_int_element (idx, vs, operand env pos ra)
        | _ -> Error.failf pos "builtin `%s`: internal arity mismatch" id)
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
          (* M7-T7. A CONSTANT IN THE SEARCH ARRAY IS SKIPPED, NOT REFUSED.

             This used to `Error.failf` on the first [Model.Const], killing the whole
             model. That was wrong twice over. A constant there is a variable with
             nothing left to decide -- MiniZinc's flattener writes one whenever it fixes
             a variable it had already named in the annotation -- so there is no
             decision to skip: the annotation asks for a search over that array, and a
             search over that array never branches on a fixed element. SKIPPING IT IS
             HONOURING IT, which is what docs/SPEC.md 3.4 requires; refusing the model is
             not a stricter reading of 3.4, it is a different answer to a question 3.4
             does not ask. And it was expensive: over the 436-instance corpus of D-0068
             this single check accounted for 143 of 278 refusals, more than every other
             cause combined.

             An array of ALL constants therefore yields an EMPTY index list, and that is
             a legal phase rather than an error. `compile.ml`'s [phases_of_search] builds
             a phase with an empty [p_vars], and [Search.sequence] skips any phase with
             no unfixed candidate -- so an all-constant phase falls through to the next
             `seq_search` phase, and if there is none, to [Search.spec_order], exactly as
             3.4's "variables no annotation mentions" paragraph says. Nothing downstream
             indexes the array, so an empty one is not a degenerate case there.

             The strategy checks below are deliberately NOT skipped when the array is
             empty: 3.4 says an unsupported strategy MUST be refused, and whether the
             array happens to be all-constant in this instance does not change what the
             annotation asks for. *)
          let idxs =
            List.filter_map
              (fun op -> match op with Model.Var i -> Some i | Model.Const _ -> None)
              (operands env pos vs)
          in
          let vc =
            match vsel with
            | Ast.Ident "input_order" -> Model.Input_order
            | Ast.Ident "first_fail" -> Model.First_fail
            (* M7-T19 (D-0083). The LARGEST current domain first, ties to the earliest
               candidate -- [first_fail]'s tie-break, unchanged. See
               `Search.anti_first_fail`. *)
            | Ast.Ident "anti_first_fail" -> Model.Anti_first_fail
            (* M7-T9. `smallest` selects the variable with the smallest value in its
               domain, `largest` the one with the largest -- read on the domain MINIMUM
               and the domain MAXIMUM respectively, which is the MiniZinc spec's literal
               wording and what Gecode's INT_VAR_MIN_MIN / INT_VAR_MAX_MAX do.
               `Search.smallest` / `Search.largest` carry the argument in full. *)
            | Ast.Ident "smallest" -> Model.Smallest
            | Ast.Ident "largest" -> Model.Largest
            | e ->
                Error.failf pos
                  "`%s`: unsupported variable-selection strategy `%s`; SPEC 3.4 supports \
                   input_order, first_fail, anti_first_fail, smallest and largest"
                  nm (Ast.string_of_expr e)
          in
          let vl =
            match valsel with
            (* M7-T19 (D-0083). Bare `indomain` is the MiniZinc specification's
               "assign values in ascending order", which is `indomain_min`'s branching
               exactly -- `x = lo` first, the rest of the domain as the sibling, and the
               next decision on that variable takes the new minimum. It is the SAME
               search, not an approximation of one, so mapping the spelling is honouring
               the annotation (SPEC 3.4) rather than substituting for it. *)
            | Ast.Ident ("indomain_min" | "indomain") -> Model.Indomain_min
            | Ast.Ident "indomain_max" -> Model.Indomain_max
            (* M7-T9. `indomain_split` bisects, excluding the upper half first -- the
               range midpoint, low branch first. See `Search.indomain_split`. *)
            | Ast.Ident "indomain_split" -> Model.Indomain_split
            (* M7-T12. `indomain_median` was REFUSED here until wave 30, and the
               refusal was correct at the time: a baguette decision was one order
               literal, `x = m` for an interior `m` is two, and its sibling `x <> m` is
               a disjunction (D-0019) that no nogood can name. M7-T12 built the second
               decision shape rather than substituting a bisection -- see
               `Search.branch_assign` and D-0077. The median is the LOWER median, the
               value at index `(size-1)/2` of the domain's values in ascending order
               (Gecode's `INT_VAL_MED`); it counts VALUES, which is what distinguishes
               it from `indomain_split`'s range midpoint. *)
            | Ast.Ident "indomain_median" -> Model.Indomain_median
            | e ->
                Error.failf pos
                  "`%s`: unsupported value-choice strategy `%s`; SPEC 3.4 supports \
                   indomain (as indomain_min), indomain_min, indomain_max, \
                   indomain_split and indomain_median"
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
  | Ast.Call (nm, _)
    when nm = "priority_search"
         || (String.length nm > 7 && String.sub nm (String.length nm - 7) 7 = "_search")
    ->
      (* M7-T2. `float_search`, `set_search` and `priority_search` used to fall into the
         catch-all below and be SILENTLY DROPPED -- the one shape of failure this project
         does not accept, because a dropped search annotation is a different search than
         the model asked for and docs/SPEC.md 3.4 says it MUST be honoured. They are
         named and refused instead. This arm is reached only for a `*_search` the arms
         above did not recognise; `int_search` and `bool_search` never get here. *)
      Error.failf pos
        "unsupported search annotation `%s`: baguette implements `int_search`, \
         `bool_search` and `seq_search`. docs/SPEC.md section 3.4 says a search \
         annotation MUST be honoured when present, so one that cannot be honoured is \
         rejected rather than ignored."
        nm
  | _ ->
      (* Not a search annotation. Annotations that are not search strategies (for
         example `var_is_introduced`, `defines_var`) carry no obligation for the solver
         and are ignored; only *builtins* are normatively must-error. *)
      None

(* ---------------------------------------------------------------------- entry point *)

let build (m : Ast.model) : Model.t =
  let env = new_env () in
  List.iter (add_decl env) m.Ast.decls;
  (* M7-T19 (D-0083): infer the undomained variables' domains BEFORE the constraints are
     built, because the arithmetic family sizes its auxiliaries from domains. One that
     stays unbounded is refused AFTER, so a malformed constraint still reports its own
     error first. *)
  let unbounded = infer_domains env m.Ast.constraints in
  let constraints = List.map (build_constraint env) m.Ast.constraints in
  Option.iter refuse_unbounded unbounded;
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
