(* Recursive-descent parser for the FlatZinc subset of docs/SPEC.md section 2.1.

   Grammar accepted (comments `%...` and `/*...*/` are stripped by the lexer):

     model      ::= item* ; exactly one solve item
     item       ::= predicate-item | decl-item | constraint-item | solve-item
     predicate  ::= "predicate" <anything> ";"            (parsed and discarded)
     decl       ::= ti ":" ident annots [ "=" expr ] ";"
     ti         ::= "array" "[" index "]" "of" ti | "var" base | base
     base       ::= "bool" | "int" | int ".." int | "{" int, ... "}"
     index      ::= "int" | int ".." int
     constraint ::= "constraint" ident "(" expr, ... ")" annots ";"
     solve      ::= "solve" annots ("satisfy" | "minimize" expr | "maximize" expr) ";"
     annots     ::= ( "::" expr )*
     expr       ::= int | "true" | "false" | string | ident | ident "(" args ")"
                  | ident "[" expr "]" | "[" args "]" | "{" ints "}" | expr ".." expr

   Every failure raises Error.Error with the position of the offending token. *)

type state = { toks : Lexer.lexeme array; mutable i : int }

let cur st = st.toks.(st.i).Lexer.tok
let pos st = st.toks.(st.i).Lexer.pos
let advance st = if st.i < Array.length st.toks - 1 then st.i <- st.i + 1

let expect st tok what =
  if cur st = tok then advance st
  else
    Error.failf (pos st) "expected %s but found %s" what (Lexer.string_of_token (cur st))

let expect_ident st what =
  match cur st with
  | Lexer.IDENT s ->
      advance st;
      s
  | t -> Error.failf (pos st) "expected %s but found %s" what (Lexer.string_of_token t)

(* Integer literals may carry an explicit sign: `-8` in a coefficient array, `-1..3` in
   a domain. *)
let parse_int st =
  let bad t =
    Error.failf (pos st) "expected an integer literal but found %s"
      (Lexer.string_of_token t)
  in
  match cur st with
  | Lexer.INT n ->
      advance st;
      n
  | Lexer.MINUS -> (
      advance st;
      match cur st with
      | Lexer.INT n ->
          advance st;
          -n
      | t -> bad t)
  | Lexer.PLUS -> (
      advance st;
      match cur st with
      | Lexer.INT n ->
          advance st;
          n
      | t -> bad t)
  | t -> bad t

let rec parse_expr st =
  let p = pos st in
  let e = parse_primary st in
  if cur st = Lexer.DOTDOT then (
    advance st;
    let e2 = parse_primary st in
    match (e, e2) with
    | Ast.Int a, Ast.Int b -> Ast.Range (a, b)
    | _ -> Error.failf p "a range must have integer literal bounds")
  else e

and parse_primary st =
  let p = pos st in
  match cur st with
  | Lexer.INT _ | Lexer.MINUS | Lexer.PLUS -> Ast.Int (parse_int st)
  | Lexer.TRUE ->
      advance st;
      Ast.Bool true
  | Lexer.FALSE ->
      advance st;
      Ast.Bool false
  | Lexer.STRING s ->
      advance st;
      Ast.String s
  | Lexer.IDENT id ->
      advance st;
      if cur st = Lexer.LPAR then (
        advance st;
        Ast.Call (id, parse_seq st Lexer.RPAR "`)`"))
      else if cur st = Lexer.LBRACK then (
        advance st;
        let ix = parse_expr st in
        expect st Lexer.RBRACK "`]` closing an array access";
        Ast.Access (id, ix))
      else Ast.Ident id
  | Lexer.LBRACK ->
      advance st;
      Ast.Array (parse_seq st Lexer.RBRACK "`]`")
  | Lexer.LBRACE ->
      advance st;
      let es = parse_seq st Lexer.RBRACE "`}`" in
      Ast.Set
        (List.map
           (function
             | Ast.Int n -> n
             | e ->
                 Error.failf p
                   "a set literal may only contain integer literals, found `%s`"
                   (Ast.string_of_expr e))
           es)
  | t -> Error.failf p "expected an expression but found %s" (Lexer.string_of_token t)

(* A comma-separated list terminated by [close], which is consumed. Tolerates a
   trailing comma. *)
and parse_seq st close close_name =
  if cur st = close then (
    advance st;
    [])
  else
    let rec loop acc =
      let e = parse_expr st in
      let acc = e :: acc in
      if cur st = Lexer.COMMA then (
        advance st;
        if cur st = close then (
          advance st;
          List.rev acc)
        else loop acc)
      else (
        expect st close close_name;
        List.rev acc)
    in
    loop []

let parse_annots st =
  let rec loop acc =
    if cur st = Lexer.DCOLON then (
      advance st;
      loop (parse_primary st :: acc))
    else List.rev acc
  in
  loop []

let parse_index_set st =
  match cur st with
  | Lexer.TINT ->
      advance st;
      Ast.Ix_int
  | _ ->
      let lo = parse_int st in
      expect st Lexer.DOTDOT "`..` in an array index set";
      let hi = parse_int st in
      Ast.Ix_range (lo, hi)

let rec parse_ti st =
  match cur st with
  | Lexer.ARRAY ->
      advance st;
      expect st Lexer.LBRACK "`[` after `array`";
      let ix = parse_index_set st in
      expect st Lexer.RBRACK "`]` closing the array index set";
      expect st Lexer.OF "`of` after the array index set";
      Ast.Arr (ix, parse_ti st)
  | Lexer.VAR ->
      advance st;
      Ast.Var (parse_base_type st)
  | _ -> Ast.Par (parse_base_type st)

and parse_base_type st =
  let p = pos st in
  match cur st with
  | Lexer.BOOL ->
      advance st;
      Ast.Tbool
  | Lexer.TINT ->
      advance st;
      Ast.Tint
  | Lexer.LBRACE ->
      advance st;
      let es = parse_seq st Lexer.RBRACE "`}`" in
      Ast.Tset
        (List.map
           (function
             | Ast.Int n -> n
             | e ->
                 Error.failf p
                   "a domain set may only contain integer literals, found `%s`"
                   (Ast.string_of_expr e))
           es)
  | Lexer.SET ->
      Error.failf p
        "`set of int` is not supported: SPEC 1 puts sets of integers out of scope"
  | Lexer.INT _ | Lexer.MINUS | Lexer.PLUS ->
      let lo = parse_int st in
      expect st Lexer.DOTDOT "`..` in a range type";
      let hi = parse_int st in
      Ast.Trange (lo, hi)
  | Lexer.IDENT ("float" | "string") ->
      Error.failf p
        "%s is not supported: SPEC 2.1 restricts types to bool, int and arrays of those"
        (Lexer.string_of_token (cur st))
  | t -> Error.failf p "expected a type but found %s" (Lexer.string_of_token t)

(* `predicate p(var int: x, array[int] of var int: xs);` carries no information for a
   solver that does not support user-defined predicates; SPEC 2.1 does not list them, so
   the declaration is parsed and dropped. A *use* of an undeclared builtin still fails in
   builder.ml, which is where the normative "name the builtin" rule lives. *)
let skip_predicate st =
  let p = pos st in
  advance st;
  let rec loop () =
    match cur st with
    | Lexer.SEMI -> advance st
    | Lexer.EOF -> Error.failf p "unterminated `predicate` declaration (missing `;`)"
    | _ ->
        advance st;
        loop ()
  in
  loop ()

let parse_model st =
  let decls = ref [] in
  let cstrs = ref [] in
  let solve = ref None in
  let rec loop () =
    match cur st with
    | Lexer.EOF -> ()
    | Lexer.PREDICATE ->
        skip_predicate st;
        loop ()
    | Lexer.CONSTRAINT ->
        advance st;
        (* Point diagnostics at the builtin name rather than the `constraint` keyword:
           the normative error of SPEC 2.1 is about the builtin. *)
        let p = pos st in
        let id = expect_ident st "a builtin name after `constraint`" in
        let args =
          if cur st = Lexer.LPAR then (
            advance st;
            parse_seq st Lexer.RPAR "`)`")
          else
            Error.failf (pos st)
              "expected `(` after the builtin name `%s` in a constraint item" id
        in
        let annots = parse_annots st in
        expect st Lexer.SEMI "`;` at the end of the constraint item";
        cstrs := { Ast.c_id = id; c_args = args; c_annots = annots; c_pos = p } :: !cstrs;
        loop ()
    | Lexer.SOLVE ->
        let p = pos st in
        advance st;
        let annots = parse_annots st in
        let kind =
          match cur st with
          | Lexer.SATISFY ->
              advance st;
              Ast.Satisfy
          | Lexer.MINIMIZE ->
              advance st;
              Ast.Minimize (parse_expr st)
          | Lexer.MAXIMIZE ->
              advance st;
              Ast.Maximize (parse_expr st)
          | t ->
              Error.failf (pos st)
                "expected `satisfy`, `minimize` or `maximize` but found %s"
                (Lexer.string_of_token t)
        in
        expect st Lexer.SEMI "`;` at the end of the solve item";
        (match !solve with
        | Some _ -> Error.failf p "a model may contain only one `solve` item"
        | None -> solve := Some (kind, annots, p));
        loop ()
    | _ ->
        let p = pos st in
        let ti = parse_ti st in
        expect st Lexer.COLON "`:` after the type in a declaration";
        let name = expect_ident st "a parameter or variable name" in
        let annots = parse_annots st in
        let value =
          if cur st = Lexer.EQ then (
            advance st;
            Some (parse_expr st))
          else None
        in
        expect st Lexer.SEMI "`;` at the end of the declaration";
        decls :=
          { Ast.d_name = name; d_ti = ti; d_value = value; d_annots = annots; d_pos = p }
          :: !decls;
        loop ()
  in
  loop ();
  match !solve with
  | None -> Error.failf (pos st) "the model has no `solve` item"
  | Some (kind, annots, p) ->
      {
        Ast.decls = List.rev !decls;
        constraints = List.rev !cstrs;
        solve = kind;
        solve_annots = annots;
        solve_pos = p;
      }

let parse_string ~file src = parse_model { toks = Lexer.tokenize ~file src; i = 0 }

let read_file path =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () -> really_input_string ic (in_channel_length ic))

let parse_file path = parse_string ~file:path (read_file path)
