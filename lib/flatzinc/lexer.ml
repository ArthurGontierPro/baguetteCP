(* Hand-written FlatZinc lexer, STREAMING.

   Why not ocamllex/menhir: the `menhir` dune stanza needs `(using menhir X.Y)` in
   `dune-project`, and dune-project is owned by another session (see WORKLOG). The
   subset in SPEC 2.1 is small enough that a hand-written scanner plus a recursive
   descent parser is both shorter and gives exact line/column positions for free, which
   the spec's "clear diagnostic" requirement leans on.

   Memory model (M7-T27 (d), D-0128). The scanner reads the input through a window of
   [window] bytes and holds ONE lexeme of lookahead, which is all the parser (LL(1), it
   never backs up) needs. Nothing is proportional to the file: not the text, which is
   never in memory whole, and not the tokens. Before this, [tokenize] read the file into
   a string and minted a list of positioned lexemes for the whole of it before the parser
   saw the first one -- about 100 bytes per token, which on a 460 MB `.fzn` of 80 M
   tokens is the 8 GiB the Challenge budget allowed, spent before the first variable was
   declared (D-0123's family A).

   A token that straddles the window's edge is copied through a Buffer; one that does
   not is taken straight out of the window. The window is 64 KiB by default and a
   parameter, so a test can shrink it to a few bytes and exercise every straddle.

   Cost (M16-file-review-T5, D-0193). The scanner is O(bytes), and the constant is what
   the Challenge's largest files pay first: on smelt_11 (136 MB, 18.4 M tokens) it was
   530 instructions per token before this review and is 330 after. Three rules keep it there. A run of
   identifier or digit bytes is read against [classes], one table load per byte, never
   through a predicate closure. An integer is folded into its value where its digits
   lie, and only one that straddles the window or does not fit goes through a string
   and [int_of_string_opt], which decides both. A token's start is two ints, and the
   [Pos.t] is made by [pos] when someone asks. What is left per token is the
   identifier's string (the parser keeps it) and one [caml_modify] for [tok]. *)

type token =
  (* keywords *)
  | ARRAY
  | OF
  | VAR
  | BOOL
  | TINT (* the type keyword `int` *)
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

(* ------------------------------------------------------------------- the window *)

type t = {
  file : string;
  buf : Bytes.t;
  (* [read buf off n] puts up to [n] bytes at [off] and returns how many; 0 at the end
     of the input, exactly like [Stdlib.input]. *)
  read : Bytes.t -> int -> int -> int;
  mutable pos : int; (* the next unread byte of [buf] *)
  mutable len : int; (* bytes of [buf] that hold input *)
  mutable base : int; (* offset in the input of [buf.(0)] *)
  mutable line : int;
  mutable bol : int; (* offset in the input of the current line's first byte *)
  (* the one lexeme of lookahead: [tok] is the current token and [tok_line],
     [tok_col] where it starts. [EOF] is sticky: once reached, [advance] does nothing.

     The start is two ints and not a [Pos.t] (M16-file-review-T5, D-0193): a [Pos.t]
     per token was an allocation and a [caml_modify] per token, for a position the
     parser asks for once per item and on an error. [pos] builds it on demand, the
     same record [here] made, so every diagnostic reads as before. *)
  mutable tok : token;
  mutable tok_line : int;
  mutable tok_col : int;
}

let default_window = 65536

(* Slide the window: drop the consumed prefix, move the [len - pos] unread bytes to the
   front and read behind them until at least [need] bytes are in hand or the input ends.
   Returns whether [need] bytes are in hand. [need] is 1 or 2, never more: the scanner
   looks two bytes ahead for `::`, `..`, `/*` and a backslash's escape, nothing else. *)
let slide t need =
  let unread = t.len - t.pos in
  if t.pos > 0 then (
    if unread > 0 then Bytes.blit t.buf t.pos t.buf 0 unread;
    t.base <- t.base + t.pos;
    t.pos <- 0;
    t.len <- unread);
  let cap = Bytes.length t.buf in
  let rec fill () =
    if t.len >= need then true
    else
      let n = t.read t.buf t.len (cap - t.len) in
      if n = 0 then false
      else (
        t.len <- t.len + n;
        fill ())
  in
  fill ()

(* [has1] / [has2]: is there a byte, are there two, at the cursor? Both may slide the
   window, so a byte index taken before them is stale after; the scanner never keeps
   one across these calls except inside [take_while], which copies first. *)
let has1 t = t.pos < t.len || slide t 1
let has2 t = t.pos + 1 < t.len || slide t 2
let peek t = Bytes.unsafe_get t.buf t.pos
let peek2 t = Bytes.unsafe_get t.buf (t.pos + 1)
let skip t = t.pos <- t.pos + 1
let here t = Pos.make t.file t.line (t.base + t.pos - t.bol + 1)

(* The current token starts at the cursor: record where, as [here] would have it. *)
let mark_token t =
  t.tok_line <- t.line;
  t.tok_col <- t.base + t.pos - t.bol + 1

(* Where the current token starts, as a [Pos.t]; [pos_at] for a start the parser kept. *)
let pos_at t line col = Pos.make t.file line col
let pos t = pos_at t t.tok_line t.tok_col
let tok_line t = t.tok_line
let tok_col t = t.tok_col

(* Called with the cursor ON the newline byte, before it is skipped. *)
let newline t =
  t.line <- t.line + 1;
  t.bol <- t.base + t.pos + 1

(* Character classes, one table load per byte (M16-file-review-T5, D-0193). [take_while]
   took the class as a closure and called it once per byte, through [is_ident_char],
   which calls [is_ident_start] and [is_digit]: three calls a byte, about two thirds of
   the lexer's time on a Challenge `.fzn`. The table answers exactly what those
   predicates answer, byte for byte (bit 1: [is_digit]; bit 2: [is_ident_char]). *)
let cls_digit = 1
let cls_ident = 2

let classes =
  String.init 256 (fun i ->
      let c = Char.chr i in
      Char.chr
        ((if is_digit c then cls_digit else 0)
        lor if is_ident_char c then cls_ident else 0))

let in_class cls c = Char.code (String.unsafe_get classes (Char.code c)) land cls <> 0

(* The maximal run of bytes of class [cls] from the cursor, as a string. Taken
   straight out of the window when it ends inside it; copied through a Buffer when it
   reaches the window's edge, because sliding would overwrite it. *)
let take_while t cls =
  let buf = t.buf and len = t.len in
  let start = t.pos in
  let i = ref start in
  while !i < len && in_class cls (Bytes.unsafe_get buf !i) do
    incr i
  done;
  t.pos <- !i;
  if !i < len then Bytes.sub_string buf start (!i - start)
  else
    let b = Buffer.create 32 in
    Buffer.add_subbytes b buf start (!i - start);
    while has1 t && in_class cls (peek t) do
      Buffer.add_char b (peek t);
      skip t
    done;
    Buffer.contents b

(* An integer literal's value, read off the digits where they lie (M16-file-review-T5,
   D-0193): no string is made for it unless it does not fit or straddles the window's
   edge. [None] is "use [take_while] and [int_of_string_opt]", which is the path for
   both of those cases, so the value accepted and the text quoted by the diagnostic are
   [int_of_string_opt]'s. Over decimal digits alone [int_of_string_opt] accepts exactly
   the values up to [max_int]; [acc <= (max_int - d) / 10] is that bound before the
   multiplication can wrap. The cursor moves only when [Some] is returned. *)
let take_int_in_window t =
  let buf = t.buf and len = t.len in
  let rec go i acc =
    if i >= len then None
    else
      let c = Bytes.unsafe_get buf i in
      if is_digit c then
        let d = Char.code c - 48 in
        if acc > (max_int - d) / 10 then None else go (i + 1) ((acc * 10) + d)
      else (
        t.pos <- i;
        Some acc)
  in
  go t.pos 0

(* --------------------------------------------------------------------- scanning *)

(* Skip whitespace and comments, then scan one token, leaving it in [t.tok]. *)
let rec scan t =
  if not (has1 t) then (
    mark_token t;
    t.tok <- EOF)
  else
    let c = peek t in
    if c = '\n' then (
      newline t;
      skip t;
      scan t)
    else if c = ' ' || c = '\t' || c = '\r' then (
      skip t;
      scan t)
    else if c = '%' then (
      while has1 t && peek t <> '\n' do
        skip t
      done;
      scan t)
    else if c = '/' && has2 t && peek2 t = '*' then (
      let p = here t in
      skip t;
      skip t;
      let closed = ref false in
      while not !closed do
        if not (has2 t) then Error.failf p "unterminated block comment"
        else if peek t = '*' && peek2 t = '/' then (
          skip t;
          skip t;
          closed := true)
        else (
          if peek t = '\n' then newline t;
          skip t)
      done;
      scan t)
    else
      let () = mark_token t in
      if is_digit c then (
        let value =
          match take_int_in_window t with
          | Some v -> Ok v
          | None -> Error (take_while t cls_digit)
        in
        (* `1..2` is a range, `1.0` is a float literal and floats are out of scope
           (SPEC 1). Distinguish by looking at the character after the dot. *)
        if has1 t && peek t = '.' && not (has2 t && peek2 t = '.') then
          Error.failf (pos t)
            "floating-point literals are not supported: SPEC 2.1 restricts types to bool \
             and int";
        if has1 t && (peek t = 'e' || peek t = 'E') then
          Error.failf (pos t)
            "floating-point literals are not supported: SPEC 2.1 restricts types to bool \
             and int";
        match value with
        | Ok v -> t.tok <- INT v
        | Error text -> (
            match int_of_string_opt text with
            | Some v -> t.tok <- INT v
            | None ->
                Error.failf (pos t) "integer literal `%s` does not fit in an OCaml int"
                  text))
      else if is_ident_start c then
        let s = take_while t cls_ident in
        match keyword s with Some k -> t.tok <- k | None -> t.tok <- IDENT s
      else if c = '"' then (
        skip t;
        let b = Buffer.create 16 in
        let closed = ref false in
        while not !closed do
          if not (has1 t) then Error.failf (pos t) "unterminated string literal"
          else
            let ch = peek t in
            if ch = '"' then (
              skip t;
              closed := true)
            else if ch = '\n' then Error.failf (pos t) "unterminated string literal"
            else if ch = '\\' && has2 t then (
              (match peek2 t with
              | 'n' -> Buffer.add_char b '\n'
              | 't' -> Buffer.add_char b '\t'
              | other -> Buffer.add_char b other);
              skip t;
              skip t)
            else (
              Buffer.add_char b ch;
              skip t)
        done;
        t.tok <- STRING (Buffer.contents b))
      else if has2 t && c = ':' && peek2 t = ':' then (
        skip t;
        skip t;
        t.tok <- DCOLON)
      else if has2 t && c = '.' && peek2 t = '.' then (
        skip t;
        skip t;
        t.tok <- DOTDOT)
      else (
        skip t;
        t.tok <-
          (match c with
          | ':' -> COLON
          | ';' -> SEMI
          | ',' -> COMMA
          | '(' -> LPAR
          | ')' -> RPAR
          | '[' -> LBRACK
          | ']' -> RBRACK
          | '{' -> LBRACE
          | '}' -> RBRACE
          | '=' -> EQ
          | '-' -> MINUS
          | '+' -> PLUS
          | _ -> Error.failf (pos t) "unexpected character %C" c))

(* ------------------------------------------------------------ the parser's view *)

let cur t = t.tok
let advance t = if t.tok <> EOF then scan t

let make ~file ?(window = default_window) read =
  let t =
    {
      file;
      buf = Bytes.create (max 2 window);
      read;
      pos = 0;
      len = 0;
      base = 0;
      line = 1;
      bol = 0;
      tok = EOF;
      tok_line = 1;
      tok_col = 1;
    }
  in
  scan t;
  t

(* Over a channel: the file is read through the window and is never in memory whole. *)
let of_channel ~file ?window ic = make ~file ?window (input ic)

(* Over a string, through the same window, so the straddling path runs in the unit
   tests too (with a small [window]) and not only on files larger than 64 KiB. *)
let of_string ~file ?window src =
  let n = String.length src in
  let off = ref 0 in
  let read buf at cap =
    let k = min cap (n - !off) in
    Bytes.blit_string src !off buf at k;
    off := !off + k;
    k
  in
  make ~file ?window read
