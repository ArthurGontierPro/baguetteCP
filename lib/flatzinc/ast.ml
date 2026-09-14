(* FlatZinc syntax tree, restricted to the subset in docs/SPEC.md section 2.1.

   The lexer and parser (M1-T6) produce this; builder.ml turns it into a Model.t.
   Keep this type honest about the subset: a construct that appears here is a construct
   the front end claims to *parse*. Whether the solver can *handle* it is builder.ml's
   judgement, and the spec says an unsupported builtin must be a clear error rather than
   a silent skip.

   The tree is deliberately untyped about builtins: [constraint_item] holds a name and
   argument expressions, and builder.ml owns the table of which names are implemented. *)

type expr =
  | Int of int
  | Bool of bool
  | String of string (* only ever appears inside annotations *)
  | Ident of string
  | Access of string * expr (* x[3] *)
  | Array of expr list
  | Set of int list (* {1, 3, 5} — a set *literal*, used as an int domain *)
  | Range of int * int (* 1..5 — as a value, e.g. inside output_array([1..2]) *)
  | Call of string * expr list (* annotation application, e.g. int_search(...) *)

(* Annotations are just expressions: [::output_var] is [Ident "output_var"] and
   [::output_array([1..2])] is [Call ("output_array", [Array [Range (1, 2)]])]. *)
type annot = expr

type index_set =
  | Ix_range of int * int
  | Ix_int (* array[int] of ... — length comes from the initialiser *)

type base_type =
  | Tbool
  | Tint (* `int` with no domain: legal for a parameter, rejected for a var *)
  | Trange of int * int
  | Tset of int list

type ti = Par of base_type | Var of base_type | Arr of index_set * ti

type decl = {
  d_name : string;
  d_ti : ti;
  d_value : expr option;
  d_annots : annot list;
  d_pos : Pos.t;
}

type constraint_item = {
  c_id : string;
  c_args : expr list;
  c_annots : annot list;
  c_pos : Pos.t;
}

type solve_kind = Satisfy | Minimize of expr | Maximize of expr

type model = {
  decls : decl list;
  constraints : constraint_item list;
  solve : solve_kind;
  solve_annots : annot list;
  solve_pos : Pos.t;
}

let rec string_of_expr = function
  | Int n -> string_of_int n
  | Bool b -> if b then "true" else "false"
  | String s -> "\"" ^ String.escaped s ^ "\""
  | Ident s -> s
  | Access (s, e) -> Printf.sprintf "%s[%s]" s (string_of_expr e)
  | Array es -> "[" ^ String.concat ", " (List.map string_of_expr es) ^ "]"
  | Set ns -> "{" ^ String.concat ", " (List.map string_of_int ns) ^ "}"
  | Range (a, b) -> Printf.sprintf "%d..%d" a b
  | Call (f, args) ->
      Printf.sprintf "%s(%s)" f (String.concat ", " (List.map string_of_expr args))

(* [true] if the annotation list contains a bare [::name]. *)
let has_flag_annot name annots =
  List.exists (function Ident s -> String.equal s name | _ -> false) annots

(* The arguments of the first [::name(...)] annotation, if any. *)
let find_call_annot name annots =
  let rec go = function
    | [] -> None
    | Call (s, args) :: _ when String.equal s name -> Some args
    | _ :: tl -> go tl
  in
  go annots
