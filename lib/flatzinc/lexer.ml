(* Hand-written FlatZinc lexer.

   Why not ocamllex/menhir: the `menhir` dune stanza needs `(using menhir X.Y)` in
   `dune-project`, and dune-project is owned by another session (see WORKLOG). The
   subset in SPEC 2.1 is small enough that a hand-written scanner plus a recursive
   descent parser is both shorter and gives exact line/column positions for free, which
   the spec's "clear diagnostic" requirement leans on. *)

type token =
  (* keywords *)
  | ARRAY
  | OF
  | VAR
  | BOOL
  | TINT  (* the type keyword `int` *)
  | SET
  | CONSTRAINT
  | SOLVE
  | SATISFY
  | MINIMIZE
  | MAXIMIZE
  | PREDICATE
  | TRUE
  | FALSE
  (* literals *)
  | INT of int
  | IDENT of string
  | STRING of string
  (* punctuation *)
  | COLON
  | DCOLON
  | SEMI
  | COMMA
  | LPAR
  | RPAR
  | LBRACK
  | RBRACK
  | LBRACE
  | RBRACE
  | EQ
  | DOTDOT
  | MINUS
  | PLUS
  | EOF

type lexeme = { tok : token; pos : Pos.t }

let string_of_token = function
  | ARRAY -> "`array`"
  | OF -> "`of`"
  | VAR -> "`var`"
  | BOOL -> "`bool`"
  | TINT -> "`int`"
  | SET -> "`set`"
  | CONSTRAINT -> "`constraint`"
  | SOLVE -> "`solve`"
  | SATISFY -> "`satisfy`"
  | MINIMIZE -> "`minimize`"
  | MAXIMIZE -> "`maximize`"
  | PREDICATE -> "`predicate`"
  | TRUE -> "`true`"
  | FALSE -> "`false`"
  | INT n -> Printf.sprintf "the integer literal %d" n
  | IDENT s -> Printf.sprintf "the identifier `%s`" s
  | STRING s -> Printf.sprintf "the string %S" s
  | COLON -> "`:`"
  | DCOLON -> "`::`"
  | SEMI -> "`;`"
  | COMMA -> "`,`"
  | LPAR -> "`(`"
  | RPAR -> "`)`"
  | LBRACK -> "`[`"
  | RBRACK -> "`]`"
  | LBRACE -> "`{`"
  | RBRACE -> "`}`"
  | EQ -> "`=`"
  | DOTDOT -> "`..`"
  | MINUS -> "`-`"
  | PLUS -> "`+`"
  | EOF -> "end of file"

let keyword = function
  | "array" -> Some ARRAY
  | "of" -> Some OF
  | "var" -> Some VAR
  | "bool" -> Some BOOL
  | "int" -> Some TINT
  | "set" -> Some SET
  | "constraint" -> Some CONSTRAINT
  | "solve" -> Some SOLVE
  | "satisfy" -> Some SATISFY
  | "minimize" -> Some MINIMIZE
  | "maximize" -> Some MAXIMIZE
  | "predicate" -> Some PREDICATE
  | "true" -> Some TRUE
  | "false" -> Some FALSE
  | _ -> None

let is_digit c = c >= '0' && c <= '9'
let is_ident_start c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_'
let is_ident_char c = is_ident_start c || is_digit c

(* Tokenise the whole input. FlatZinc files are small; a token array keeps the parser
   trivially backtrackable and keeps positions attached to every token. *)
let tokenize ~file src =
  let n = String.length src in
  let out = ref [] in
  let i = ref 0 in
  let line = ref 1 in
  let bol = ref 0 in
  let here () = Pos.make file !line (!i - !bol + 1) in
  let newline () =
    incr line;
    bol := !i + 1
  in
  let emit p t = out := { tok = t; pos = p } :: !out in
  while !i < n do
    let c = src.[!i] in
    if c = '\n' then (
      newline ();
      incr i)
    else if c = ' ' || c = '\t' || c = '\r' then incr i
    else if c = '%' then while !i < n && src.[!i] <> '\n' do incr i done
    else if c = '/' && !i + 1 < n && src.[!i + 1] = '*' then begin
      let p = here () in
      i := !i + 2;
      let closed = ref false in
      while not !closed do
        if !i + 1 >= n then Error.failf p "unterminated block comment"
        else if src.[!i] = '*' && src.[!i + 1] = '/' then begin
          i := !i + 2;
          closed := true
        end
        else begin
          if src.[!i] = '\n' then newline ();
          incr i
        end
      done
    end
    else if is_digit c then begin
      let p = here () in
      let start = !i in
      while !i < n && is_digit src.[!i] do
        incr i
      done;
      (* `1..2` is a range, `1.0` is a float literal and floats are out of scope
         (SPEC 1). Distinguish by looking at the character after the dot. *)
      if !i < n && src.[!i] = '.' && not (!i + 1 < n && src.[!i + 1] = '.') then
        Error.failf p
          "floating-point literals are not supported: SPEC 2.1 restricts types to bool \
           and int";
      if !i < n && (src.[!i] = 'e' || src.[!i] = 'E') then
        Error.failf p
          "floating-point literals are not supported: SPEC 2.1 restricts types to bool \
           and int";
      let text = String.sub src start (!i - start) in
      match int_of_string_opt text with
      | Some v -> emit p (INT v)
      | None -> Error.failf p "integer literal `%s` does not fit in an OCaml int" text
    end
    else if is_ident_start c then begin
      let p = here () in
      let start = !i in
      while !i < n && is_ident_char src.[!i] do
        incr i
      done;
      let s = String.sub src start (!i - start) in
      match keyword s with Some t -> emit p t | None -> emit p (IDENT s)
    end
    else if c = '"' then begin
      let p = here () in
      incr i;
      let b = Buffer.create 16 in
      let closed = ref false in
      while not !closed do
        if !i >= n then Error.failf p "unterminated string literal"
        else begin
          let ch = src.[!i] in
          if ch = '"' then begin
            incr i;
            closed := true
          end
          else if ch = '\n' then Error.failf p "unterminated string literal"
          else if ch = '\\' && !i + 1 < n then begin
            (match src.[!i + 1] with
            | 'n' -> Buffer.add_char b '\n'
            | 't' -> Buffer.add_char b '\t'
            | other -> Buffer.add_char b other);
            i := !i + 2
          end
          else begin
            Buffer.add_char b ch;
            incr i
          end
        end
      done;
      emit p (STRING (Buffer.contents b))
    end
    else begin
      let p = here () in
      let two = if !i + 1 < n then String.sub src !i 2 else "" in
      if String.equal two "::" then begin
        i := !i + 2;
        emit p DCOLON
      end
      else if String.equal two ".." then begin
        i := !i + 2;
        emit p DOTDOT
      end
      else begin
        incr i;
        match c with
        | ':' -> emit p COLON
        | ';' -> emit p SEMI
        | ',' -> emit p COMMA
        | '(' -> emit p LPAR
        | ')' -> emit p RPAR
        | '[' -> emit p LBRACK
        | ']' -> emit p RBRACK
        | '{' -> emit p LBRACE
        | '}' -> emit p RBRACE
        | '=' -> emit p EQ
        | '-' -> emit p MINUS
        | '+' -> emit p PLUS
        | _ -> Error.failf p "unexpected character %C" c
      end
    end
  done;
  emit (here ()) EOF;
  Array.of_list (List.rev !out)
