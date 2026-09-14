(* Writing the .opb model file.

   A PB constraint is  sum_i a_i * l_i  >=  b,  written
       a1 l1 a2 l2 ... >= b ;
   Equalities use '=' instead of '>='. *)

type term = int * Lit.t
type relation = Ge | Eq
type constr = { terms : term list; rel : relation; rhs : int }

let ge terms rhs = { terms; rel = Ge; rhs }
let eq terms rhs = { terms; rel = Eq; rhs }

let constr_to_string c =
  let b = Buffer.create 64 in
  List.iter
    (fun (a, l) -> Buffer.add_string b (Printf.sprintf "%+d %s " a (Lit.to_string l)))
    c.terms;
  Buffer.add_string b (match c.rel with Ge -> ">= " | Eq -> "= ");
  Buffer.add_string b (string_of_int c.rhs);
  Buffer.add_string b " ;";
  Buffer.contents b

(* The header must be written before the constraints and must state the true counts,
   so callers collect constraints first, then write. See invariant I-X5. *)
let write oc ~comments ~constraints =
  let nvars =
    let seen = Hashtbl.create 64 in
    List.iter
      (fun c ->
        List.iter (fun (_, l) -> Hashtbl.replace seen (Lit.var_name l.Lit.v) ()) c.terms)
      constraints;
    Hashtbl.length seen
  in
  Printf.fprintf oc "* #variable= %d #constraint= %d\n" nvars (List.length constraints);
  List.iter (fun s -> Printf.fprintf oc "* %s\n" s) comments;
  List.iter (fun c -> Printf.fprintf oc "%s\n" (constr_to_string c)) constraints
