(* The text of a proof line, written in place (M20-pernode-T5, D-0209).

   A growable [Bytes] and a write position. The .pbp writer ([Writer]) and the .opb row
   writer ([Opb.output_row]) assemble a line here and hand it to the channel in one
   call. Three things are written straight into the bytes, with nothing allocated and no
   [Printf]:

   - an integer ([int]): its decimal digits, two at a time from a 200-byte table, at
     their final position. [Lit.add_int] wrote them into a scratch and blitted the
     scratch into a [Buffer]; the bytes are the same, [string_of_int]'s.
   - a literal ([lit]): its name, which is [Lit.to_string]'s bytes. The owner part of the
     name -- the sanitised identifier and "_ge_", "_eq_" or "_bit_" -- is rendered ONCE
     per variable and kept in [names] below; a literal is then that prefix, an "m" for a
     negative value and the value's digits.
   - a string or a character.

   WHY THE NAME CACHE CANNOT CHANGE A BYTE. A prefix is a function of the owner's
   CONTENT only ([Lit.sanitize] and a constant), and an entry is used only when its
   owner is the same string ([==], or [String.equal] when the two are distinct copies).
   OCaml strings are immutable, so the entry is exactly what would be rendered now. A
   collision or a miss renders the prefix again and replaces the entry; it costs time,
   never a different byte. The cache is keyed by the identifier, not by the rendered
   name, so [Lit.sanitize]'s non-injectivity (D-0087) does not reach it: two owners that
   sanitise to one name have two entries holding equal prefixes.

   WHAT IS CACHED, AND WHY NOT THE WHOLE NAME. One entry per variable, three prefixes at
   most, so the cache is bounded by the number of slots ([n_slots]) whatever the
   domains' widths. Caching "x_ge_17" itself would be one string per LITERAL, which on a
   wide ladder (D-0197's 22-million-value variable) is the width in strings, and the
   value's digits are two table reads per pair. *)

type t = { mutable b : Bytes.t; mutable pos : int }

let create n = { b = Bytes.create (max n 16); pos = 0 }
let clear t = t.pos <- 0
let length t = t.pos
let contents t = Bytes.sub_string t.b 0 t.pos

(* Room for [k] more bytes. *)
let grow t k =
  let need = t.pos + k in
  let n = ref (2 * Bytes.length t.b) in
  while !n < need do
    n := 2 * !n
  done;
  let b = Bytes.create !n in
  Bytes.blit t.b 0 b 0 t.pos;
  t.b <- b

(* Give back a buffer one huge line grew past [keep] bytes (as [Writer]'s and [Opb]'s
   [Buffer]s were reset). *)
let shrink t ~keep = if Bytes.length t.b > keep then t.b <- Bytes.create 256

let[@inline] char t c =
  if t.pos >= Bytes.length t.b then grow t 1;
  Bytes.unsafe_set t.b t.pos c;
  t.pos <- t.pos + 1

let[@inline] string t s =
  let n = String.length s in
  if t.pos + n > Bytes.length t.b then grow t n;
  Bytes.unsafe_blit_string s 0 t.b t.pos n;
  t.pos <- t.pos + n

(* The line, to the channel, in one call. *)
let output oc t = Stdlib.output oc t.b 0 t.pos

(* ---------------------------------------------------------------------------
   Integers.
   --------------------------------------------------------------------------- *)

(* "00" "01" ... "99": the two digits of [i] are at [2i] and [2i + 1]. *)
let pairs =
  String.init 200 (fun i -> Char.chr (48 + if i land 1 = 0 then i / 20 else i / 2 mod 10))

(* [String.length (string_of_int a)] for [a >= 0]: a comparison tree to eight digits
   (constraint ids reach seven), a loop past them. *)
let n_digits a =
  if a < 10000 then if a < 100 then if a < 10 then 1 else 2 else if a < 1000 then 3 else 4
  else if a < 100000000 then
    if a < 1000000 then if a < 100000 then 5 else 6 else if a < 10000000 then 7 else 8
  else
    let rec go a k = if a < 10 then k else go (a / 10) (k + 1) in
    go (a / 100000000) 9

(* The digits of [a >= 0], written right to left, two at a time, ending at [last]. *)
let put_digits b last a =
  let a = ref a and i = ref last in
  while !a >= 100 do
    let q = !a / 100 in
    let r = 2 * (!a - (100 * q)) in
    Bytes.unsafe_set b !i (String.unsafe_get pairs (r + 1));
    Bytes.unsafe_set b (!i - 1) (String.unsafe_get pairs r);
    i := !i - 2;
    a := q
  done;
  if !a >= 10 then (
    let r = 2 * !a in
    Bytes.unsafe_set b !i (String.unsafe_get pairs (r + 1));
    Bytes.unsafe_set b (!i - 1) (String.unsafe_get pairs r))
  else Bytes.unsafe_set b !i (Char.unsafe_chr (48 + !a))

(* [string_of_int n]'s bytes. [abs min_int] is [min_int], so that one value goes through
   [string_of_int], as it did in [Lit.add_int]. *)
let int t n =
  if n = min_int then string t (string_of_int n)
  else (
    if n < 0 then char t '-';
    let a = abs n in
    let ld = n_digits a in
    if t.pos + ld > Bytes.length t.b then grow t ld;
    put_digits t.b (t.pos + ld - 1) a;
    t.pos <- t.pos + ld)

(* ---------------------------------------------------------------------------
   Literal names.
   --------------------------------------------------------------------------- *)

(* The rendered prefixes of one owner, each made on first use ("" until then: a real
   prefix is never empty, it ends in its "_ge_"/"_eq_"/"_bit_"). *)
type entry = {
  owner : string;
  san : string;
  mutable ge : string;
  mutable eq : string;
  mutable bit : string;
}

let slot_bits = 14
let n_slots = 1 lsl slot_bits
let dummy = { owner = ""; san = ""; ge = ""; eq = ""; bit = "" }

(* Direct-mapped: one entry per slot, the newest owner hashed there. Global, because the
   prefixes are a function of the owner's content and nothing else, so every writer and
   the .opb row writer may share them. An entry is replaced whole, and a prefix once set
   is never changed. *)
let names = Array.make n_slots dummy

(* A cheap hash of [x]: its length and its last eight bytes (or all of them when it is
   shorter), which is where FlatZinc's generated names differ ("X_INTRODUCED_1234_"). It
   only places the entry; the hit test is on the string itself. *)
let slot x =
  let n = String.length x in
  let h =
    if n >= 8 then Int64.to_int (String.get_int64_le x (n - 8))
    else
      let h = ref 0 in
      for i = 0 to n - 1 do
        h := (!h lsl 8) lor Char.code (String.unsafe_get x i)
      done;
      !h
  in
  (* The TOP bits of the product, which every bit of [h] reaches; a name's last bytes
     are the high bits of [h], and they reach no low bit of the product. *)
  (h lxor n * 0x2545F4914F6CDD1D) lsr (Sys.int_size - slot_bits)

let entry x =
  let i = slot x in
  let e = Array.unsafe_get names i in
  if e.owner == x || String.equal e.owner x then e
  else
    let e = { owner = x; san = Lit.sanitize x; ge = ""; eq = ""; bit = "" } in
    Array.unsafe_set names i e;
    e

(* [Lit.to_string l]'s bytes: "~" when negative, the owner's prefix, "m" when the value
   is negative, and the digits of its absolute value. *)
let lit t (l : Lit.t) =
  let v =
    match l.Lit.v with
    | Lit.Ge (x, v) ->
        let e = entry x in
        if String.length e.ge = 0 then e.ge <- e.san ^ "_ge_";
        if not l.Lit.positive then char t '~';
        string t e.ge;
        v
    | Lit.Eq (x, v) ->
        let e = entry x in
        if String.length e.eq = 0 then e.eq <- e.san ^ "_eq_";
        if not l.Lit.positive then char t '~';
        string t e.eq;
        v
    | Lit.Bit (x, i) ->
        let e = entry x in
        if String.length e.bit = 0 then e.bit <- e.san ^ "_bit_";
        if not l.Lit.positive then char t '~';
        string t e.bit;
        i
  in
  if v < 0 then char t 'm';
  int t (abs v)

(* [Lit.var_name v]'s bytes: the positive literal's name. *)
let var t (v : Lit.pbvar) = lit t (Lit.pos v)
