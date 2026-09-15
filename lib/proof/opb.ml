(* Writing the .opb model file.

   A PB constraint is  sum_i a_i * l_i  >=  b,  written

       a1 l1 a2 l2 ... >= b ;

   Equalities use '=' instead of '>='. VeriPB loads every constraint in this file
   with the [f] rule, which gives them ids 1..n in the order they appear here; that
   order is therefore part of the interface between this module and [Writer], and
   [Encoding] is what keeps the two in step. See invariant I-X5.

   Naming of the Boolean variables is normative and lives in [Lit]; see
   docs/PROOF-FORMAT.md section 3. *)

type term = int * Lit.t
type relation = Ge | Eq
type constr = { terms : term list; rel : relation; rhs : int }

let ge terms rhs = { terms; rel = Ge; rhs }
let eq terms rhs = { terms; rel = Eq; rhs }

(* A clause  l1 \/ ... \/ lk  is the PB constraint  1 l1 + ... + 1 lk >= 1. *)
let clause lits = ge (List.map (fun l -> (1, l)) lits) 1

(* sum a_i l_i <= b  is  sum (-a_i) l_i >= -b. *)
let le terms rhs = ge (List.map (fun (a, l) -> (-a, l)) terms) (-rhs)

(* An equality line in the .opb is *two* constraints to the checker: it splits
   [= b] into [>= b] and [<= b], which shifts every later constraint id. The [f]
   rule's count and therefore every id in the proof depends on this, so it is the
   count that goes in the header. [Encoding] refuses to emit equalities at all, for
   the same reason. *)
let checker_count c = match c.rel with Ge -> 1 | Eq -> 2
let n_checker_constraints cs = List.fold_left (fun n c -> n + checker_count c) 0 cs
let terms c = c.terms
let relation c = c.rel
let rhs c = c.rhs
let lits c = List.map snd c.terms
let map_terms f c = { c with terms = List.map f c.terms }

(* Merge repeated variables and drop zero coefficients.

   a x + b ~x  =  a x + b (1 - x)  =  (a - b) x + b, so the b moves to the
   right-hand side. Callers that build constraints by concatenation want this;
   [write] does not apply it for them, because the emission order and the exact
   shape of a model constraint are things a proof step may depend on. *)
let normalise c =
  let coef = Hashtbl.create 16 in
  let order = ref [] in
  let rhs = ref c.rhs in
  List.iter
    (fun (a, (l : Lit.t)) ->
      let key = Lit.var_name l.Lit.v in
      if not (Hashtbl.mem coef key) then order := (key, l.Lit.v) :: !order;
      let prev = try fst (Hashtbl.find coef key) with Not_found -> 0 in
      (* a * ~v = a - a * v, so the constant a moves to the right-hand side. *)
      let delta = if l.Lit.positive then a else -a in
      if not l.Lit.positive then rhs := !rhs - a;
      Hashtbl.replace coef key (prev + delta, l.Lit.v))
    c.terms;
  let terms =
    List.rev !order
    |> List.filter_map (fun (key, _) ->
           let a, v = Hashtbl.find coef key in
           if a = 0 then None
           else if a > 0 then Some (a, Lit.pos v)
           else (
             (* a * v = a + (-a) * ~v  with a < 0: the constant a moves right. *)
             rhs := !rhs - a;
             Some (-a, Lit.neg v)))
  in
  { terms; rel = c.rel; rhs = !rhs }

(* The constraint without its terminating " ;". VeriPB 3.0's [red] rule ends at the
   first ";", so its witness has to come before one: `red <body> : <witness> ;`. Every
   other use wants the terminator, which is what [constr_to_string] is. *)
let constr_body c =
  let b = Buffer.create 64 in
  List.iter
    (fun (a, l) -> Buffer.add_string b (Printf.sprintf "%+d %s " a (Lit.to_string l)))
    c.terms;
  Buffer.add_string b (match c.rel with Ge -> ">= " | Eq -> "= ");
  Buffer.add_string b (string_of_int c.rhs);
  Buffer.contents b

let constr_to_string c = constr_body c ^ " ;"

(* An objective is minimised; FlatZinc maximisation is negated by the caller. *)
type objective = { obj_terms : term list; obj_constant : int }

let objective ?(constant = 0) terms = { obj_terms = terms; obj_constant = constant }

let objective_to_string o =
  let b = Buffer.create 64 in
  Buffer.add_string b "min: ";
  List.iter
    (fun (a, l) -> Buffer.add_string b (Printf.sprintf "%+d %s " a (Lit.to_string l)))
    o.obj_terms;
  if o.obj_constant <> 0 then Buffer.add_string b (Printf.sprintf "%+d " o.obj_constant);
  Buffer.add_string b ";";
  Buffer.contents b

let var_names constraints =
  let seen = Hashtbl.create 64 in
  let order = ref [] in
  List.iter
    (fun c ->
      List.iter
        (fun (_, (l : Lit.t)) ->
          let n = Lit.var_name l.Lit.v in
          if not (Hashtbl.mem seen n) then (
            Hashtbl.replace seen n ();
            order := n :: !order))
        c.terms)
    constraints;
  List.rev !order

(* docs/PROOF-FORMAT.md section 3: identifiers that are not valid OPB names are
   rewritten by [Lit.sanitize] and the mapping is dumped as comments at the head of
   the .opb, so that a proof can still be grepped against the model. *)
let rename_comments constraints =
  let seen = Hashtbl.create 8 in
  let acc = ref [] in
  List.iter
    (fun c ->
      List.iter
        (fun (_, (l : Lit.t)) ->
          let x = Lit.owner l.Lit.v in
          if Lit.is_renamed x && not (Hashtbl.mem seen x) then (
            Hashtbl.replace seen x ();
            acc := Printf.sprintf "name %s -> %s" x (Lit.sanitize x) :: !acc))
        c.terms)
    constraints;
  List.rev !acc

(* The header must be written before the constraints and must state the true counts,
   so callers collect constraints first, then write. See invariant I-X5. *)
(* The label a constraint carries in the .opb and is cited by in the proof. VeriPB 3.0
   only; see docs/PROOF-FORMAT.md section 2 and D-0023. It is the row's 1-based
   position, which is also the id the [f] rule gives it -- but the *point* is that the
   proof never has to rely on that agreement again, because it cites the name. *)
let label_of i = Printf.sprintf "@c%d" i

let write ?objective:obj ?(labels = false) oc ~comments ~constraints =
  let names = var_names constraints in
  let obj_names =
    match obj with
    | None -> []
    | Some o -> var_names [ { terms = o.obj_terms; rel = Ge; rhs = 0 } ]
  in
  let nvars =
    let seen = Hashtbl.create 64 in
    List.iter (fun n -> Hashtbl.replace seen n ()) names;
    List.iter (fun n -> Hashtbl.replace seen n ()) obj_names;
    Hashtbl.length seen
  in
  Printf.fprintf oc "* #variable= %d #constraint= %d\n" nvars
    (n_checker_constraints constraints);
  List.iter (fun s -> Printf.fprintf oc "* %s\n" s) (rename_comments constraints);
  List.iter (fun s -> Printf.fprintf oc "* %s\n" s) comments;
  (match obj with
  | None -> ()
  | Some o -> Printf.fprintf oc "%s\n" (objective_to_string o));
  (* A labelled row must be a single constraint: VeriPB 3.0 refuses `@c1 ... = k ;`
     outright ("Expected inequality constraint"), because one name cannot stand for the
     two constraints an `=` splits into. That is the checker enforcing the discipline
     [Encoding.add_constraint] already imposes, so it is not a restriction here -- but
     it is why labelling cannot simply be switched on over an .opb containing `=`. *)
  List.iteri
    (fun i c ->
      if labels then
        match c.rel with
        | Ge -> Printf.fprintf oc "%s %s\n" (label_of (i + 1)) (constr_to_string c)
        | Eq ->
            invalid_arg
              "Opb.write: an `=` row cannot carry a label -- it is two constraints to \
               the checker, and one name cannot name both. Post it as two `>=` rows \
               (Encoding.add_equality)."
      else Printf.fprintf oc "%s\n" (constr_to_string c))
    constraints
