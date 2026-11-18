(* Literals of the pseudo-Boolean encoding.

   Naming here is normative: see docs/PROOF-FORMAT.md section 3. Proofs are read by
   humans debugging rejected steps, and grep-ability against the FlatZinc model is the
   whole point of a stable scheme. Do not introduce a second one. *)

type pbvar =
  | Ge of string * int (* x_ge_v : x >= v, the order encoding *)
  | Eq of string * int (* x_eq_v : x = v,  the direct encoding *)
  | Bit of string * int
(* x_bit_i : bit i of (x - lo), the BITS encoding (M8-bits-encoding-T2, D-0130 section 4,
   D-0132). A bits variable has no x_ge_v in the .opb; its order atoms keep the name
   x_ge_v and are minted into the proof on demand by [Encoding.ensure_atom]. Nothing in
   lib/core/ ever builds a [Bit]: it is a term of a row the .opb carries and of an
   assignment the checker is handed, and that is all. *)

type t = { v : pbvar; positive : bool }

let pos v = { v; positive = true }
let neg v = { v; positive = false }
let negate l = { l with positive = not l.positive }

(* OPB names allow no '-', so negative values get an 'm' prefix. *)
let int_suffix v = if v < 0 then "m" ^ string_of_int (-v) else string_of_int v

(* M6-T11 (D-0085): the NAMES below are exactly what they were; only how they are built
   changed. [sanitize] returns its argument when no character needs rewriting -- every
   identifier [Compile] has ever been handed that is not a [X_INTRODUCED_...] with a dot
   or a [$]-aux -- instead of copying it through [String.map] (D-0080: [Bytes.map] 15 % of
   2009 black-hole's compile). [var_name] and [to_string] write the name into one buffer
   of the right length instead of going through [Printf.sprintf]'s format interpreter and
   a second concatenation for the [~]. *)
let ident_char = function
  | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> true
  | _ -> false

(* 2026-11-18 (M8-bits-encoding-T3, answering M6-T22's cross-session request: the scan
   below was about 3 % of QR48's proof-mode time, as [go] and [ident_char]). The scan reads
   a 256-entry table in a loop instead of calling [ident_char] from a recursive closure;
   it answers the same question for every byte, so every name is what it was. A memo of
   the answer was tried first and measured useless there: a one-entry memo on the
   string's physical identity left the profile unchanged, because QR48's lines are
   clauses over DIFFERENT variables, and a table keyed on the name would hash it end to
   end, which is the cost being removed (docs/DECISIONS.md D-0134 section 12). *)
let ident_table =
  Bytes.init 256 (fun i -> if ident_char (Char.chr i) then '\001' else '\000')

let needs_sanitize name =
  let n = String.length name in
  let i = ref 0 in
  while
    !i < n
    && Bytes.unsafe_get ident_table (Char.code (String.unsafe_get name !i)) = '\001'
  do
    incr i
  done;
  !i < n

let sanitize name =
  if needs_sanitize name then String.map (fun c -> if ident_char c then c else '_') name
  else name

(* [neg ^ sanitize x ^ mid ^ int_suffix v], in one allocation. [mid] is "_ge_"/"_eq_"/
   "_bit_"; its length is read, not assumed, since M8-bits-encoding-T2 added the five-byte
   one. *)
let render ~neg x mid v =
  let x = sanitize x in
  let digits = string_of_int (abs v) in
  let lx = String.length x and ld = String.length digits and lm = String.length mid in
  let p = if neg then 1 else 0 in
  let m = if v < 0 then 1 else 0 in
  let b = Bytes.create (p + lx + lm + m + ld) in
  if neg then Bytes.unsafe_set b 0 '~';
  Bytes.unsafe_blit_string x 0 b p lx;
  Bytes.unsafe_blit_string mid 0 b (p + lx) lm;
  if v < 0 then Bytes.unsafe_set b (p + lx + lm) 'm';
  Bytes.unsafe_blit_string digits 0 b (p + lx + lm + m) ld;
  Bytes.unsafe_to_string b

let var_name = function
  | Ge (x, v) -> render ~neg:false x "_ge_" v
  | Eq (x, v) -> render ~neg:false x "_eq_" v
  | Bit (x, i) -> render ~neg:false x "_bit_" i

let to_string l =
  match l.v with
  | Ge (x, v) -> render ~neg:(not l.positive) x "_ge_" v
  | Eq (x, v) -> render ~neg:(not l.positive) x "_eq_" v
  | Bit (x, i) -> render ~neg:(not l.positive) x "_bit_" i

(* x >= v, as a literal. *)
let ge x v = pos (Ge (x, v))

(* x <= v, which the order encoding expresses as ~(x >= v+1). *)
let le x v = neg (Ge (x, v + 1))
let eq x v = pos (Eq (x, v))
let ne x v = neg (Eq (x, v))

(* Bit [i] of (x - lo) is set. Only [Encoding] builds one (M8-bits-encoding-T2). *)
let bit x i = pos (Bit (x, i))

(* ---------------------------------------------------------------------------
   Additions (M1-T4). Everything above this line is frozen: lib/core/explanation.ml
   compiles against it. Add here, do not rewrite above.
   --------------------------------------------------------------------------- *)

(* A FlatZinc [var bool] is order-encoded on [0, 1]: there is exactly one Boolean
   [b_ge_1], and "b is true" is that literal. Deliberately no third constructor —
   a second naming scheme is exactly what docs/PROOF-FORMAT.md section 3 forbids. *)
let bool_true x = ge x 1
let bool_false x = le x 0

(* Ge < Eq < Bit across kinds (D-0130 section 3.2: [Bit] sorts after [Eq]). *)
let kind_rank = function Ge _ -> 0 | Eq _ -> 1 | Bit _ -> 2

let var_compare a b =
  match (a, b) with
  | Ge (x, i), Ge (y, j) | Eq (x, i), Eq (y, j) | Bit (x, i), Bit (y, j) ->
      (* [x == y] first (M6-T11): literals of one variable share its identifier string,
         so the common case skips the C call. Same order: [String.compare x x = 0]. *)
      let c = if x == y then 0 else String.compare x y in
      if c <> 0 then c else Int.compare i j
  | _ -> Int.compare (kind_rank a) (kind_rank b)

let var_equal a b = var_compare a b = 0

let compare a b =
  let c = var_compare a.v b.v in
  if c <> 0 then c else Bool.compare a.positive b.positive

let equal a b = compare a b = 0

(* The FlatZinc identifier a literal is about, before sanitisation. *)
let owner = function Ge (x, _) | Eq (x, _) | Bit (x, _) -> x

(* For a [Bit] this is the bit INDEX, not a value of the variable. *)
let value = function Ge (_, v) | Eq (_, v) | Bit (_, v) -> v
let is_order = function Ge _ -> true | Eq _ | Bit _ -> false
let is_direct = function Eq _ -> true | Ge _ | Bit _ -> false
let is_bit = function Bit _ -> true | Ge _ | Eq _ -> false

(* True when [sanitize] had to rewrite the identifier, i.e. the .opb name and the
   FlatZinc name differ and the mapping must be dumped as a comment. *)
let is_renamed x = needs_sanitize x
let pp fmt l = Format.pp_print_string fmt (to_string l)

(* ---------------------------------------------------------------------------
   Views (M4-T0). A view is a RENDERING, not a variable.
   ---------------------------------------------------------------------------

   A view is [s * x + k] with [s = +/-1]: the 1-based index of an
   [array_int_element], the [c - x] of a reversed term, the [x + 1] of an offset.
   The decision this section records is that such a view gets **no PB variables of
   its own**. It renders onto its base's literals, because

       y = s*x + k   ==>   [y >= n]  IS  [x >= n-k]      (s = +1)
                           [y >= n]  IS  [x <= k-n]      (s = -1)

   -- the same 0-1 fact under a change of variable, not a fact that needs relating
   to another one. Both right-hand sides are already expressible: [Lit.t] carries a
   [positive] flag, and [le] is the negated [Ge] the order encoding uses anyway.

   What the alternative costs, since it is the one that looks natural. Minting
   [y_ge_v] would add, per view and per unit of DECLARED WIDTH: one Boolean, one
   ladder rung (PROOF-FORMAT section 3 -- the rungs are load-bearing, they are what
   makes a trace line RUP at all), and one channelling row tying [y_ge_v] to
   [x_ge_(v-k)]. D-0028 measured what declared width does to this project's proofs
   already; a view is precisely the construct that would multiply it, and it would
   buy nothing, since the two families would then have to be re-related by exactly
   the channelling the renaming makes unnecessary. So: rendering.

   The consequence, stated so it is not discovered later: a view has no name. There
   is nothing to sanitise, nothing to collide, and nothing to key a table on --
   which is the M2-T9 trap avoided by construction rather than by care. [sanitize]
   is NON-INJECTIVE, so a view->base map keyed on rendered OPB names would conflate
   [a-b] with [a_b]. There is no such map: the transform below is applied to the
   base's identifier BEFORE any name is rendered, and the identity that matters on
   the solver side is [Var.t], a dense index. *)

(* [apply a x = (if negated then -x else x) + offset]. [s] is carried as a flag
   rather than an int coefficient because the order encoding can express exactly
   these two: a general [a*x + k] does not render onto [x]'s literals at all
   ([y >= n] becomes [x >= ceil((n-k)/a)], which is a different fact family once
   [a] does not divide, and M4 has no need of it). *)
type affine = { negated : bool; offset : int }

let identity = { negated = false; offset = 0 }

(* [v + k]. *)
let shift a k = { a with offset = a.offset + k }

(* [-v]: negating [s*x + k] gives [-s*x - k], so a view of a view is a view, and the
   representation stays flat. *)
let flip a = { negated = not a.negated; offset = -a.offset }
let is_identity a = (not a.negated) && a.offset = 0
let apply a x = (if a.negated then -x else x) + a.offset

(* The base value a view value stands for: the inverse of [apply], which is its own
   shape because [s = s^-1] for [s = +/-1]. *)
let unapply a v =
  let d = v - a.offset in
  if a.negated then -d else d

let affine_equal a b = Bool.equal a.negated b.negated && Int.equal a.offset b.offset

let affine_compare a b =
  let c = Bool.compare a.negated b.negated in
  if c <> 0 then c else Int.compare a.offset b.offset

(* The four renderings. [base] is the base variable's FlatZinc identifier, unsanitised,
   exactly as [ge]/[le]/[eq]/[ne] take it -- the transform happens on the VALUE, never
   on the name, so nothing here can be confused by [sanitize]'s non-injectivity.

   These are the pure forms. They do not know the base's declared bounds, so they do
   not trim [y >= n] to a constant; [Encoding.view_ge] does that, on the committing
   side, exactly as [Encoding.ge] already does for a plain variable. *)
let view_ge base a n =
  let d = n - a.offset in
  if a.negated then le base (-d) else ge base d

let view_le base a n =
  let d = n - a.offset in
  if a.negated then ge base (-d) else le base d

let view_eq base a n = eq base (unapply a n)
let view_ne base a n = ne base (unapply a n)
