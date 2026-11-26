(* The s-expressions of a `.scp` file: text to a tree of atoms and lists, every node with
   its position (M23-inputs-T1, D-0228 section 14, D-0230).

   The grammar is the one CakeML's `cake_pb_cp` reads through `mlsexp` (branch
   `cp_enc_new`, `930601d6`): an atom is a maximal run of characters that are neither
   white space nor a parenthesis, a list is `(` forms `)`. Stricter than cake on two
   points, each refused with the position rather than read some other way:

   - a `;` anywhere (cake refuses a comment, and so does this reader: D-0228 section 14);
   - a double quote or a control character other than the four white spaces (cake's reader has
     quoted strings, a `.scp` has no use for one, and an atom with a quote in it would be
     a name the `.opb` cannot carry).

   ITERATIVE AND LINEAR. [read] builds one form with an explicit stack of the lists still
   open, so nesting depth costs heap, never OCaml stack, and every character is looked at
   once. The input is pulled through a fixed 64 KiB buffer, so a 300 MB file is never in
   memory as text. [Reader] does not ask for the whole file as one tree either: it walks
   the frame `( (version 1) (variables ...) (constraints ...) (prob_type ...) )` token by
   token and calls [read] once per variable and once per constraint, so the tree that is
   alive at any moment is one item's (D-0230 section 2). [parse_string] reads one whole
   form and requires the end of the input after it; the unit tests use it. *)

module Pos = Baguette_flatzinc.Pos
module Error = Baguette_flatzinc.Error

type t = Atom of string * Pos.t | List of t list * Pos.t

let pos_of = function Atom (_, p) | List (_, p) -> p

type token = Open | Close | Tatom of string | Eof

type lexer = {
  file : string;
  ic : in_channel option;
  buf : Bytes.t;
  mutable len : int; (* valid bytes in [buf] *)
  mutable i : int; (* next byte to look at *)
  mutable eof : bool;
  mutable line : int;
  mutable col : int;
  atom : Buffer.t;
  mutable peeked : (token * Pos.t) option;
}

let chunk = 65536

let of_channel ~file ic =
  {
    file;
    ic = Some ic;
    buf = Bytes.create chunk;
    len = 0;
    i = 0;
    eof = false;
    line = 1;
    col = 1;
    atom = Buffer.create 64;
    peeked = None;
  }

let of_string ~file s =
  {
    file;
    ic = None;
    buf = Bytes.of_string s;
    len = String.length s;
    i = 0;
    eof = true;
    line = 1;
    col = 1;
    atom = Buffer.create 64;
    peeked = None;
  }

(* The next byte, without consuming it; [None] at the end of the input. *)
let peek_char lx =
  if lx.i < lx.len then Some (Bytes.unsafe_get lx.buf lx.i)
  else if lx.eof then None
  else
    match lx.ic with
    | None ->
        lx.eof <- true;
        None
    | Some ic ->
        let n = input ic lx.buf 0 (Bytes.length lx.buf) in
        lx.i <- 0;
        lx.len <- n;
        if n = 0 then (
          lx.eof <- true;
          None)
        else Some (Bytes.unsafe_get lx.buf 0)

let advance lx c =
  lx.i <- lx.i + 1;
  if c = '\n' then (
    lx.line <- lx.line + 1;
    lx.col <- 1)
  else lx.col <- lx.col + 1

let here lx = Pos.make lx.file lx.line lx.col
let is_space = function ' ' | '\t' | '\n' | '\r' -> true | _ -> false

let refuse_char lx c =
  let p = here lx in
  match c with
  | ';' ->
      Error.failf p
        "`;` in a .scp file: cake_pb_cp's reader has no comment syntax and refuses it, \
         so this reader does too (D-0228 section 14)"
  | '"' ->
      Error.failf p
        "`\"` in a .scp file: a quoted string is not part of the .scp grammar this \
         reader takes (D-0230)"
  | c -> Error.failf p "the byte 0x%02x is not allowed in a .scp file" (Char.code c)

let bad_char c =
  c = ';' || c = '"' || ((Char.code c < 32 || Char.code c = 127) && not (is_space c))

let rec next_raw lx =
  match peek_char lx with
  | None -> (Eof, here lx)
  | Some c when is_space c ->
      advance lx c;
      next_raw lx
  | Some '(' ->
      let p = here lx in
      advance lx '(';
      (Open, p)
  | Some ')' ->
      let p = here lx in
      advance lx ')';
      (Close, p)
  | Some c when bad_char c -> refuse_char lx c
  | Some _ ->
      let p = here lx in
      Buffer.clear lx.atom;
      let rec go () =
        match peek_char lx with
        | Some c when not (is_space c || c = '(' || c = ')') ->
            if bad_char c then refuse_char lx c;
            Buffer.add_char lx.atom c;
            advance lx c;
            go ()
        | _ -> ()
      in
      go ();
      (Tatom (Buffer.contents lx.atom), p)

let next lx =
  match lx.peeked with
  | Some t ->
      lx.peeked <- None;
      t
  | None -> next_raw lx

let peek lx =
  match lx.peeked with
  | Some t -> t
  | None ->
      let t = next_raw lx in
      lx.peeked <- Some t;
      t

let describe = function
  | Open -> "`(`"
  | Close -> "`)`"
  | Tatom a ->
      if String.length a > 40 then Printf.sprintf "the atom `%s...`" (String.sub a 0 40)
      else Printf.sprintf "the atom `%s`" a
  | Eof -> "the end of the file"

(* One complete form, starting at the next token. The stack holds, for every list still
   open, its position and its elements so far, newest first. [loop] and [close_with] call
   each other only in tail position, so the depth of the form costs heap, never stack. *)
let read lx =
  let rec loop stack =
    let tok, p = next lx in
    match tok with
    | Tatom a -> close_with stack (Atom (a, p))
    | Open -> loop ((p, []) :: stack)
    | Close -> (
        match stack with
        | [] -> Error.failf p "`)` with no `(` open"
        | (lp, elems) :: rest -> close_with rest (List (List.rev elems, lp)))
    | Eof -> (
        match stack with
        | [] -> Error.failf p "the file ends where an s-expression was expected"
        | (lp, _) :: _ ->
            Error.failf p
              "the file ends inside the list opened at %d:%d, which is never closed"
              lp.Pos.line lp.Pos.col)
  and close_with stack node =
    match stack with
    | [] -> node
    | (lp, elems) :: rest -> loop ((lp, node :: elems) :: rest)
  in
  loop []

let expect_eof lx =
  match next lx with
  | Eof, _ -> ()
  | tok, p ->
      Error.failf p "%s after the end of the problem: a .scp file is one s-expression"
        (describe tok)

(* Exactly one form, then the end of the input. *)
let parse_string ~file s =
  let lx = of_string ~file s in
  let t = read lx in
  expect_eof lx;
  t

(* Integers as cake's `mlint$fromString` reads them: an optional `-` or `~`, then one or
   more decimal digits, and nothing else. [None] for any other atom, which is then a
   name. A digit string beyond 63 bits is refused with the position: cake reads it as a
   bignum, baguette computes over native integers (SPEC 2.1, D-0029). *)
let int_of_atom p a =
  let n = String.length a in
  let start = if n > 0 && (a.[0] = '-' || a.[0] = '~') then 1 else 0 in
  if n = start then None
  else
    let rec digits k = k >= n || (a.[k] >= '0' && a.[k] <= '9' && digits (k + 1)) in
    if not (digits start) then None
    else
      let neg = start = 1 in
      (* accumulate negatively so that min_int is reachable *)
      let acc = ref 0 in
      for k = start to n - 1 do
        let d = Char.code a.[k] - 48 in
        if !acc < (min_int + d) / 10 then
          Error.failf p "the integer `%s` does not fit in 63 bits" a;
        acc := (!acc * 10) - d
      done;
      if neg then Some !acc
      else if !acc = min_int then
        Error.failf p "the integer `%s` does not fit in 63 bits" a
      else Some (- !acc)
