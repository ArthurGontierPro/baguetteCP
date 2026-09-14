(* FlatZinc syntax tree, restricted to the subset in docs/SPEC.md section 2.1.

   The lexer and parser (M1-T6) produce this; builder.ml turns it into a solver model.
   Keep this type honest about the subset: a construct that appears here is a construct
   the solver claims to support, and the spec says unsupported builtins must be a clear
   error rather than a silent skip. *)

type value =
  | Int of int
  | Bool of bool
  | Ident of string
  | Array of value list

type var_kind =
  | VarInt of int * int  (* declared domain, required: see SPEC 2.1 *)
  | VarBool
  | ParInt of int
  | ParBool of bool
  | ParArray of value list

type decl = { d_name : string; d_kind : var_kind; d_annots : string list }

type constraint_item = { c_id : string; c_args : value list; c_annots : string list }

type solve_kind =
  | Satisfy
  | Minimize of value
  | Maximize of value

type model = {
  decls : decl list;
  constraints : constraint_item list;
  solve : solve_kind;
  solve_annots : string list;
}
