(* The pseudo-Boolean encoding of a FlatZinc model: which variables exist, which
   encodings they have been given, and the constraints that keep those encodings
   consistent with one another.

   docs/PROOF-FORMAT.md section 3 is normative here, and this module is the only
   place that is allowed to know the shape of the encoding:

   - every integer variable gets the *order* encoding, eagerly, in the .opb;
   - the *direct* encoding is introduced lazily, into the .pbp, with [red], only for
     the variables a disequality / element / all_different propagator touches;
   - exactly-one over the direct encoding is *derived* from the channelling, never
     assumed.

   This module also owns the mapping from a model constraint to the id the [f] rule
   will give it. The .opb's line order and the proof's ids are the same thing, and
   keeping them in one place is the only way invariant I-X5 stays true.

   ---------------------------------------------------------------------------
   "Compile is the only door", stated and enforced (M1-T32, from D-0029)
   ---------------------------------------------------------------------------

   D-0029 closed a soundness gap whose shape is worth restating here, because this
   module is where the damage is done rather than where the fix went. A wrapped product
   makes a propagator prune wrongly AND makes the .opb row say something other than the
   model, computed from the same wrapping [*] -- so the two agree, and veripb, which
   only ever sees the .opb, accepts the refutation of a model nobody wrote. There is no
   independent oracle: [Model.check_assignment] wraps the same way, and on an UNSAT
   answer there is no assignment to check at all.

   The fix was a compile-time cap ([Checked.limit], lib/flatzinc/compile.ml). Its
   consequence, recorded in D-0029 and filed as M1-T32, was that THIS MODULE and
   lib/proof/opb.ml still computed unchecked and were safe only because [Compile]
   happened to be the only caller. Nothing stated that, and a second entry point -- a
   future front end, or a test calling [add_int_lin_le] directly -- could still write a
   corrupted row.

   The invariant, stated:

     **No row is committed to the .opb whose arithmetic wrapped.** Every integer this
     module or [Opb] derives from a posted linear row is representable in a native int.

   And enforced, by [check_lin_le_computable] / [check_lin_ne_computable] below, on the
   two functions that commit such a row: [add_int_lin_le] and [add_int_lin_ne]. They are
   preconditions, computed in [Arith]'s overflow-checked operations, and they RAISE
   [Unrepresentable]. They never decline: D-0029's asymmetry ("there is no 'decline'
   available for an artefact that must exist") applies with more force here than to a
   propagator, because this module is the thing that writes the artefact. Under
   [Compile]'s cap neither can fire, so the .opb of every model the CLI accepts is
   byte-for-byte what it was.

   Three things this deliberately does NOT do, said here so they are not mistaken for
   oversights:

   1. **It does not call [Baguette_core.Checked], because it cannot.** [Checked] lives
      in lib/core, and the dependency runs core -> proof (ARCHITECTURE section 1,
      "Dependency direction"); lib/core/dune's `(libraries baguette_proof)` is the edge.
      Inverting it is not on the table. [Arith] below is therefore a local copy of the
      five primitives, and the copy is PINNED: test/unit/test_proof.ml asserts
      [Encoding.Arith] and [Baguette_core.Checked] agree operation by operation over an
      edge-case table. The test layer depends on both libraries even though neither
      depends on the other, which is what makes the duplication checkable rather than a
      second source of truth. [Checked]'s *policy* half -- [limit], [row_fits],
      [bound_fits], and the derivation of the factor 16 -- stays where it is and is NOT
      copied: a FlatZinc compile-time cap does not belong in the PB emitter, and a
      second statement of that envelope is exactly the "copies cannot all stay right"
      failure this tree has already paid for twice.

   2. **The guard is on the committing door, not on the pure expansion.**
      [expand_int_lin_le], [expand_int_lin_ne] and [linear_terms_int_lin_le] are
      documented as the inspect-before-committing forms and stay exactly as they were,
      wrapping arithmetic included. That is deliberate: it is what lets
      test/unit/test_prop.ml's [test_opb_row_wraps_identically] go on demonstrating the
      D-0029 defect on the row itself, which is the evidence this guard exists for.
      Inspecting an expansion is not writing a file.

   3. **It does not make a hand-built row safe.** A caller that assembles an
      [Opb.constr] itself and calls [add_constraint] is outside the guard, because by
      then there is no linear arithmetic left for this module to check. [add_constraint]
      is the lower-level door and always was.

   The bound the guard checks is an upper envelope, not the row itself, so it covers
   lib/proof/opb.ml as well -- [Opb.le]'s negation and [Opb.normalise]'s moving of
   coefficients to the right-hand side are both inside it. See [check_lin_le_computable]
   for the derivation. opb.ml is not read by this guard and needs no change. *)

type cid = Writer.cid

(* The truth value of a bound, once the encoding's constants are taken into account.
   [x >= l] is not a variable: it is the constant true. *)
type cond =
  | Holds (* vacuously true, no literal needed *)
  | Fails (* impossible, no literal exists *)
  | Cond of Lit.t

exception Undeclared of string
exception Redeclared of string
exception Empty_domain of string
exception No_direct_encoding of string
exception Direct_too_large of string * int

(* A declared domain whose order ladder is longer than this module will build.
   Carries the variable's name and its declared bounds -- not the width, because for
   extreme bounds [hi - lo] is itself not representable and the exception exists partly
   to report that case. See [max_order_width] and M1-T54. *)
exception Width_too_large of string * int * int

(* A row whose arithmetic cannot be carried out in a native int, so committing it to
   the .opb would write a different constraint from the one the caller posted. See the
   header, M1-T32. Loud by design: D-0029's "overflow raises; it never wraps and never
   quietly declines". *)
exception Unrepresentable of string

(* ---------------------------------------------------------------------------
   Overflow-checked arithmetic, local to this library.

   A LOCAL COPY of lib/core/checked.ml's five primitives, and the header says why it
   has to be one: core depends on proof, so [Baguette_core.Checked] is not nameable
   here. It is a copy of the OPERATIONS only -- none of [Checked]'s cap, envelope or
   [row_fits] policy is duplicated -- and test/unit/test_proof.ml pins it to the
   original by asserting the two agree case by case. If that test is deleted, this
   module has quietly become a second source of truth about 63-bit arithmetic.

   Every operation returns exactly what the native operator returns whenever the native
   operator is right, so nothing computed through these changes any emitted byte.
   --------------------------------------------------------------------------- *)
module Arith = struct
  let fail fmt = Printf.ksprintf (fun s -> raise (Unrepresentable s)) fmt

  let neg a =
    if a = min_int then fail "-(%d) overflows a 63-bit int (min_int has no negation)" a
    else -a

  let abs a =
    if a = min_int then fail "abs %d overflows a 63-bit int (min_int has no negation)" a
    else Stdlib.abs a

  (* Two's complement addition is exact modulo 2^63, so a sum is wrong exactly when
     both operands share a sign and the result does not. *)
  let add a b =
    let s = a + b in
    if a >= 0 = (b >= 0) && s >= 0 <> (a >= 0) then
      fail "%d + %d overflows a 63-bit int" a b
    else s

  let sub a b =
    let d = a - b in
    if a >= 0 <> (b >= 0) && d >= 0 <> (a >= 0) then
      fail "%d - %d overflows a 63-bit int" a b
    else d

  (* |a| and |b| below 2^30 bound the product by 2^60, which is every coefficient and
     bound a real model has; that fast path costs four comparisons where the exact one
     costs a division. Same split, and the same constant, as [Checked.mul]. *)
  let small = 0x3FFFFFFF

  let mul a b =
    if a >= -small && a <= small && b >= -small && b <= small then a * b
    else if a = 0 || b = 0 then 0
    else if a = -1 then neg b
    else if b = -1 then neg a
    else
      (* [a] is neither 0 nor -1 here, so this divides neither by zero nor by -1. *)
      let p = a * b in
      if p / a <> b then fail "%d * %d overflows a 63-bit int" a b else p
end

(* An .opb line [... = b] is two constraints as far as VeriPB is concerned, so it
   would shift every id after it. We never emit one; see [add_equality]. *)
exception Equality_in_opb

(* Above this many values we refuse to materialise a direct encoding: the proof would
   be larger than the search. A propagator that needs it on a domain this big is a
   design problem, not a budget problem. *)
let max_direct_values = 100_000

type dvar = {
  (* v -> id of   ~x_eq_v \/ x_ge_v          (present iff v > lo) *)
  d_lo : (int, cid) Hashtbl.t;
  (* v -> id of   ~x_eq_v \/ ~x_ge_(v+1)     (present iff v < hi) *)
  d_hi : (int, cid) Hashtbl.t;
  (* v -> id of   x_eq_v \/ ~x_ge_v \/ x_ge_(v+1)   (always present) *)
  d_fwd : (int, cid) Hashtbl.t;
}

type ivar = {
  name : string;
  lo : int;
  hi : int;
  (* v -> id of the consistency constraint  x_ge_(v+1) -> x_ge_v,  for lo < v < hi *)
  consistency : (int, cid) Hashtbl.t;
  mutable direct : dvar option;
}

type t = {
  ints : (string, ivar) Hashtbl.t;
  mutable decl_rev : string list;
  mutable rev_constraints : Opb.constr list;
  mutable n : int; (* ids 1..n have been assigned *)
  mutable objective : Opb.objective option;
  mutable n_aux : int;
  (* How many auxiliary variables this encoding has minted of its own accord
     (M1-T9's disequality rows need one each). Only ever increases, so a name
     handed out once is never handed out again even after a failed candidate.
     See [fresh_aux_name]. *)
  (* Every id this module minted for a DIRECT-ENCODING line: the three channelling
     halves of every [ensure_direct], and every [derive_at_least_one]. M4-T2 added it
     for [is_direct_row], whose one caller is lib/core/search.ml's [rests_on_a_clause]
     -- see that function for why "which currency is this row stated in" is the
     question a root conflict has to answer, and why the id is the only thing that can
     answer it (an [Explanation.Model_row] carries an id and nothing else). Ids are
     minted by [Writer] in one ascending sequence and never reused, so an entry stays
     correct after [retire_direct] drops the [dvar] itself. *)
  direct_cids : (cid, unit) Hashtbl.t;
  mutable direct_wanted_rev : string list;
      (* M4-T1. The variables a propagator has declared it will need the DIRECT
         encoding for, recorded at compile time and materialised by [start_proof].

         Why a request list and not [ensure_direct] at the point of use: the direct
         encoding is written with [red], which needs a [Writer.t], and a propagator
         has none -- [Propagator.propagate] takes a [Store.t] and nothing else, and
         that is not an oversight (lib/core/propagator.ml). An [Explanation.t] is a
         VALUE naming constraint ids (D-0027 point 1, [Explanation.Model_row]), so
         the ids it names must already exist when the propagator builds it. So the
         materialisation happens once, at the top of the proof, for the variables
         [Compile] says will need it, and the propagator reads the ids back out.

         Declared order, not request order, so that the .pbp is byte-identical
         whatever order [Compile] walks the constraints in ([alldiff_direct_vars]
         below sorts by declaration). The determinism lane is what would catch a
         regression here. *)
  alo : (string, cid) Hashtbl.t;
      (* x -> the id of the at-least-one line [derive_at_least_one] wrote for it,
         populated by [start_proof] alongside the direct encoding itself. *)
}

let create () =
  {
    ints = Hashtbl.create 64;
    decl_rev = [];
    rev_constraints = [];
    n = 0;
    objective = None;
    n_aux = 0;
    direct_cids = Hashtbl.create 64;
    direct_wanted_rev = [];
    alo = Hashtbl.create 16;
  }

let find t x =
  match Hashtbl.find_opt t.ints x with Some v -> v | None -> raise (Undeclared x)

let is_declared t x = Hashtbl.mem t.ints x

let domain t x =
  let v = find t x in
  (v.lo, v.hi)

let vars t = List.rev t.decl_rev
let n_constraints t = t.n
let constraints t = List.rev t.rev_constraints

(* Append a constraint to the .opb and hand back the id [f] will give it. *)
let add_constraint t c =
  if Opb.relation c = Opb.Eq then raise Equality_in_opb;
  t.n <- t.n + 1;
  t.rev_constraints <- c :: t.rev_constraints;
  t.n

(* sum a_i l_i = b, as the two inequalities the checker would have split it into
   anyway -- but with ids we control. PROOF-FORMAT section 4 already says
   int_lin_eq is justified as two int_lin_le derivations; this is the same split. *)
let add_equality t terms rhs =
  let geq = add_constraint t (Opb.ge terms rhs) in
  let leq = add_constraint t (Opb.le terms rhs) in
  (geq, leq)

let set_objective t o = t.objective <- Some o
let objective t = t.objective

(* ---------------------------------------------------------------------------
   Order encoding
   --------------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------------
   The width cap (M1-T54, taking D-0028 point 3; decided in D-0041, which is also
   where SPEC 3.1's normative paragraph comes from)
   ---------------------------------------------------------------------------

   The largest declared width [hi - lo] for which this module will build an order
   ladder. Above it, [declare_int] raises [Width_too_large] and allocates nothing.

   Why the cap is HERE. Every integer variable gets the order encoding eagerly
   (PROOF-FORMAT section 3), so a declared width of w is w - 1 ladder clauses in the
   .opb before any constraint is posted, and -- the half that actually hurts -- the row
   expansion [expand_int_lin_le] is Theta(w) literals per variable, which makes every
   justification that cancels this variable's contribution Theta(w) literals long
   (D-0028: "the width is inherited from the encoding, not invented by
   order_reason.ml"). This module is the one that mints that cost. A cap anywhere
   downstream is a cap on a commitment already made.

   Why it is a refusal and not a budget. Three memory-ceiling incidents on 2026-09-16
   were all this shape, and the reason the existing defences did not help is that all
   three act after the allocation is under way: `ulimit -v` and [Mem_guard] (M1-T53)
   kill a run, and scripts/check_test_widths.sh sees only the *syntactic* form of a wide
   domain in a test file. Refusing at the declaration is different in kind -- nothing is
   allocated, and the caller can say which variable and where.

   The number, and why this one. D-0028 measures the shape at a series of widths (two
   variables, one row, refuted at the root having pruned nothing):

     w        .opb     .pbp    solve   verify
     999      126 kB   23.9 kB  50 ms   18 ms   <- test/models/width_root_unsat.fzn
     9 999    1.36 MB  258 kB    —      130 ms
     99 999   14.6 MB  2.78 MB   4 s    1.3 s
     999 999  156 MB   29.8 MB  72 s    12 s

   10 000 is bracketed by measurements on both sides: it is the last width at which a
   whole model's artefacts still fit in a code review (a megabyte of .opb, a quarter of
   a megabyte of proof, a verify in the tens of milliseconds), and one order of
   magnitude below the first row where solving takes seconds and the .opb reaches eight
   figures. It also leaves a factor of ten above [width_root_unsat]'s w = 999, which is
   a deliberate, measured, load-bearing test and must keep passing.

   This is NOT [Checked.limit], and D-0029 point 3 is explicit that it must not become
   it: an overflow cap refuses models whose arithmetic cannot be *computed* and is a
   soundness requirement, while this refuses models whose proof cannot be *stored*, and
   the model it refuses is legal FlatZinc that baguette would otherwise answer
   correctly. Different justification, different bound, and hence SPEC 2.1's own
   sentence and its own decision record.

   The cap is PER VARIABLE, which is what [declare_int] can see. It therefore does not
   bound a model's total ladder: a thousand variables at w = 9 999 is still ten million
   clauses. That gap is deliberate and left open rather than papered over here -- an
   aggregate budget is a different check in a different place, with the awkward property
   that it must name a variable to blame for a total nobody variable caused. *)
let max_order_width = 10_000

(* [lo <= hi] is a precondition. [hi - lo] is not always representable -- min_int..0 is
   a legal pair of 63-bit ints whose width is not one -- so the comparison never
   subtracts unless it has established that it may. Anything this refuses really does
   exceed the cap: in the mixed-sign branch, [hi - lo >= hi] and [hi - lo >= -lo]. *)
let order_width_exceeds ~lo ~hi =
  if lo >= 0 || hi < 0 then
    (* Same sign: hi - lo cannot overflow. *)
    hi - lo > max_order_width
  else
    (* lo < 0 <= hi. Once both magnitudes are inside the cap, hi - lo is at most
       2 * max_order_width, so the last test is safe to evaluate. *)
    hi > max_order_width || lo < -max_order_width || hi - lo > max_order_width

let declare_int t x ~lo ~hi =
  if lo > hi then raise (Empty_domain x);
  (* Before the Hashtbl and before the ladder: a refused declaration leaves no trace
     in [t] and costs no allocation. M1-T54. *)
  if order_width_exceeds ~lo ~hi then raise (Width_too_large (x, lo, hi));
  (match Hashtbl.find_opt t.ints x with
  | Some v when v.lo = lo && v.hi = hi -> raise Exit (* idempotent redeclaration *)
  | Some _ -> raise (Redeclared x)
  | None -> ());
  let v = { name = x; lo; hi; consistency = Hashtbl.create 16; direct = None } in
  Hashtbl.replace t.ints x v;
  t.decl_rev <- x :: t.decl_rev;
  (* docs/PROOF-FORMAT.md section 3: for each lo < v < hi,
        1 ~x_ge_(v+1) 1 x_ge_v >= 1        i.e.  x >= v+1 -> x >= v. *)
  for value = lo + 1 to hi - 1 do
    let c = Opb.clause [ Lit.negate (Lit.ge x (value + 1)); Lit.ge x value ] in
    Hashtbl.replace v.consistency value (add_constraint t c)
  done

let declare_int t x ~lo ~hi = try declare_int t x ~lo ~hi with Exit -> ()

(* A FlatZinc [var bool] is the order encoding on [0, 1]: one variable, b_ge_1. *)
let declare_bool t x = declare_int t x ~lo:0 ~hi:1

(* x >= value *)
let ge t x value =
  let v = find t x in
  if value <= v.lo then Holds else if value > v.hi then Fails else Cond (Lit.ge x value)

(* x <= value *)
let le t x value =
  let v = find t x in
  if value >= v.hi then Holds else if value < v.lo then Fails else Cond (Lit.le x value)

let gt t x value = ge t x (value + 1)
let lt t x value = le t x (value - 1)

(* The id of the consistency constraint  x >= v+1 -> x >= v. *)
let consistency_id t x value =
  let v = find t x in
  Hashtbl.find_opt v.consistency value

(* ---------------------------------------------------------------------------
   Direct encoding, introduced lazily with [red]
   --------------------------------------------------------------------------- *)

let has_direct t x = Option.is_some (find t x).direct

(* x = value, once the direct encoding exists. *)
let eq t x value =
  let v = find t x in
  if value < v.lo || value > v.hi then Fails
  else if v.lo = v.hi then Holds
  else if Option.is_none v.direct then raise (No_direct_encoding x)
  else Cond (Lit.eq x value)

let ne t x value =
  match eq t x value with
  | Holds -> Fails
  | Fails -> Holds
  | Cond l -> Cond (Lit.negate l)

(* x_eq_v  <->  x_ge_v /\ ~x_ge_(v+1),  with the constant halves dropped.

   Order matters. The two [~x_eq_v -> ...] halves go in first, under the witness
   x_eq_v -> 0, which satisfies them and every earlier constraint mentioning the
   fresh variable. The [... -> x_eq_v] half goes in last, under x_eq_v -> 1: its
   own negation supplies the units that discharge the goals the earlier two raise.
   Reversing this order makes VeriPB reject the definition. *)
let ensure_direct t w x =
  let v = find t x in
  match v.direct with
  | Some d -> d
  | None ->
      let size = v.hi - v.lo + 1 in
      if size > max_direct_values then raise (Direct_too_large (x, size));
      let d =
        { d_lo = Hashtbl.create 16; d_hi = Hashtbl.create 16; d_fwd = Hashtbl.create 16 }
      in
      Writer.comment w "direct encoding of %s over [%d, %d]" x v.lo v.hi;
      let z value = Lit.Eq (x, value) in
      for value = v.lo to v.hi do
        let zl = Lit.eq x value in
        let origin = Printf.sprintf "channel %s=%d" x value in
        (* ~x_eq_v \/ x_ge_v, only when x >= v is not the constant true *)
        if value > v.lo then (
          let c = Opb.clause [ Lit.negate zl; Lit.ge x value ] in
          let id = Writer.red w ~origin ~witness:[ (z value, Writer.Zero) ] c in
          Hashtbl.replace t.direct_cids id ();
          Hashtbl.replace d.d_lo value id);
        (* ~x_eq_v \/ ~x_ge_(v+1), only when x >= v+1 is not the constant false *)
        if value < v.hi then (
          let c = Opb.clause [ Lit.negate zl; Lit.le x value ] in
          let id = Writer.red w ~origin ~witness:[ (z value, Writer.Zero) ] c in
          Hashtbl.replace t.direct_cids id ();
          Hashtbl.replace d.d_hi value id);
        (* x_eq_v \/ ~x_ge_v \/ x_ge_(v+1) *)
        let body =
          [ zl ]
          @ (if value > v.lo then [ Lit.negate (Lit.ge x value) ] else [])
          @ if value < v.hi then [ Lit.ge x (value + 1) ] else []
        in
        let id =
          Writer.red w ~origin ~witness:[ (z value, Writer.One) ] (Opb.clause body)
        in
        Hashtbl.replace t.direct_cids id ();
        Hashtbl.replace d.d_fwd value id
      done;
      v.direct <- Some d;
      d

let direct t x =
  match (find t x).direct with Some d -> d | None -> raise (No_direct_encoding x)

(* Exactly-one over x_eq_* MUST be derived, not assumed (PROOF-FORMAT section 3).

   at-least-one: add the  ... -> x_eq_v  clauses for v = lo..hi. Every x_ge_k for
   lo < k <= hi occurs once positively and once negatively, so the whole order family
   cancels and what is left is  sum_v x_eq_v >= 1. *)
let derive_at_least_one t w x =
  let v = find t x in
  let d = direct t x in
  let ids = List.init (v.hi - v.lo + 1) (fun i -> Hashtbl.find d.d_fwd (v.lo + i)) in
  Writer.comment w "at-least-one for %s, derived from the channelling" x;
  let id =
    Writer.pol w
      ~origin:(Printf.sprintf "at-least-one %s" x)
      (Writer.Pol.sum (List.map Writer.Pol.id ids))
  in
  Hashtbl.replace t.direct_cids id ();
  id

(* at-most-one for a pair a < b: take
       ~x_eq_a \/ ~x_ge_(a+1)        (a < hi, since a < b <= hi)
       ~x_eq_b \/ x_ge_b             (b > lo, since b > a >= lo)
   and the consistency chain x_ge_b -> x_ge_(b-1) -> ... -> x_ge_(a+1). Summing
   cancels the whole chain and leaves  ~x_eq_a + ~x_eq_b >= 1. *)
let derive_at_most_one t w x a b =
  let v = find t x in
  let a, b = if a <= b then (a, b) else (b, a) in
  if a = b then invalid_arg "Encoding.derive_at_most_one: equal values";
  if a < v.lo || b > v.hi then invalid_arg "Encoding.derive_at_most_one: out of domain";
  let d = direct t x in
  let chain =
    List.init (max 0 (b - a - 1)) (fun i -> Hashtbl.find v.consistency (a + 1 + i))
  in
  let ids = Hashtbl.find d.d_hi a :: Hashtbl.find d.d_lo b :: chain in
  Writer.comment w "at-most-one for %s: %d and %d are exclusive" x a b;
  Writer.pol w
    ~origin:(Printf.sprintf "at-most-one %s %d %d" x a b)
    (Writer.Pol.sum (List.map Writer.Pol.id ids))

(* Every channelling id for x, so a caller can retire the definition (invariant I-X2). *)
let direct_ids t x =
  match (find t x).direct with
  | None -> []
  | Some d ->
      let acc = ref [] in
      let take h = Hashtbl.iter (fun _ id -> acc := id :: !acc) h in
      take d.d_lo;
      take d.d_hi;
      take d.d_fwd;
      List.sort compare !acc

let retire_direct t w x =
  let ids = direct_ids t x in
  if ids <> [] then (
    Writer.delete_many w ids;
    (find t x).direct <- None)

let retire_all_direct t w = List.iter (fun x -> retire_direct t w x) (vars t)

(* ---------------------------------------------------------------------------
   M4-T1: the direct encoding a global constraint asks for up front
   --------------------------------------------------------------------------- *)

(* "This variable's propagator will cite direct-encoding ids." Called by
   lib/flatzinc/compile.ml for every `all_different_int` scope, before the .opb is
   written; honoured by [start_proof], which is the first moment a [Writer.t] exists.

   Idempotent, and it does NOT write anything: a request recorded twice materialises
   once. It raises [Direct_too_large] here rather than at [start_proof] so the refusal
   names the constraint's own variable at compile time, where the diagnostic can carry
   a source position -- [max_direct_values] is the width refusal this module's header
   points at, and a propagator that needs a direct encoding on a domain that wide is a
   design problem, not a budget problem. *)
let request_direct t x =
  let v = find t x in
  let size = v.hi - v.lo + 1 in
  if size > max_direct_values then raise (Direct_too_large (x, size));
  if not (List.mem x t.direct_wanted_rev) then
    t.direct_wanted_rev <- x :: t.direct_wanted_rev

let direct_requested t = List.filter (fun x -> List.mem x t.direct_wanted_rev) (vars t)

(* The ids a Hall derivation names with [Explanation.Model_row]. Each is [None] exactly
   when the line does not exist, and every [None] here is a CONSTANT, not a gap:

     - [direct_lo_id] at [v = lo]   -- "x_eq_lo -> x >= lo" is the constant true;
     - [direct_hi_id] at [v = hi]   -- "x_eq_hi -> x <= hi" is the constant true;
     - [consistency_id] outside (lo, hi) -- the ladder rung does not exist.

   A caller that adds nothing for a [None] is therefore adding nothing where the
   arithmetic needs nothing. [direct_fwd_id] is always present for an in-domain value,
   which is why it has no such case. *)
let direct_lo_id t x value =
  match (find t x).direct with None -> None | Some d -> Hashtbl.find_opt d.d_lo value

let direct_hi_id t x value =
  match (find t x).direct with None -> None | Some d -> Hashtbl.find_opt d.d_hi value

let direct_fwd_id t x value =
  match (find t x).direct with None -> None | Some d -> Hashtbl.find_opt d.d_fwd value

(* The at-least-one line for [x], derived from the channelling by [start_proof].
   [None] when no direct encoding was requested for [x]. *)
let at_least_one_id t x = Hashtbl.find_opt t.alo x

(* Is this id one of the DIRECT-ENCODING lines this module wrote? (M4-T2.)

   The question it answers is not "who minted this" but "which currency is the row that
   cites it stated in". The order encoding's ladder and the direct encoding's x_eq_v
   family are two different vocabularies, and a [pol] whose operands come from the second
   derives a statement about values, not about the per-variable declared-range chain a
   [Linear] row's division needs (D-0010, lib/core/prop/linear.ml's header). So a
   derivation that names any of these ids is a COUNTING row, and lib/core/search.ml's
   [rests_on_a_clause] uses exactly that to decide how a root conflict citing it closes.

   The pairwise disequality rows [add_all_different] posts are deliberately NOT here:
   they are clauses over ORDER literals, so a derivation may cite one without leaving the
   ladder currency -- and [Ne] does. What marks the counting row is the channelling and
   the at-least-one line, which is why those are what this records. *)
let is_direct_row t id = Hashtbl.mem t.direct_cids id

(* ---------------------------------------------------------------------------
   Assignments
   --------------------------------------------------------------------------- *)

(* Every literal of x, with the polarity that fixing x to [value] gives it. VeriPB's
   [sol] wants an assignment that propagates to a total one; handing it the full
   family of every variable is the way not to have to reason about that. *)
let assignment_lits_of t x value =
  let v = find t x in
  if value < v.lo || value > v.hi then invalid_arg "Encoding.assignment_lits_of";
  let order =
    List.init
      (max 0 (v.hi - v.lo))
      (fun i ->
        let k = v.lo + 1 + i in
        if value >= k then Lit.ge x k else Lit.negate (Lit.ge x k))
  in
  let direct =
    match v.direct with
    | None -> []
    | Some _ ->
        List.init
          (v.hi - v.lo + 1)
          (fun i ->
            let k = v.lo + i in
            if value = k then Lit.eq x k else Lit.ne x k)
  in
  order @ direct

let assignment_lits t bindings =
  List.concat_map (fun (x, value) -> assignment_lits_of t x value) bindings

(* ---------------------------------------------------------------------------
   Output
   --------------------------------------------------------------------------- *)

(* Every row is written as `@cN <row> ;` so the proof can cite it by name (D-0023).

   Labelling is unconditional and there is no knob for it. It used to be optional
   because the .opb had to match the writer's format and format 2.0 had no labels; with
   2.0 gone (D-0046) there is one grammar, so the only thing a switch could still do is
   produce an .opb that every citation in the .pbp fails to parse against. That is why
   the paired [write_opb_for] collapsed into this function rather than being kept as a
   safer spelling of it: the unsafe spelling no longer exists. *)
let write_opb ?(comments = []) t oc =
  Opb.write ?objective:t.objective oc ~comments ~constraints:(constraints t)

(* Start the proof. Must be called after the .opb is complete (invariant I-X5).

   M4-T1: and then materialise every direct encoding [request_direct] asked for, with
   its at-least-one line. Three things about doing it HERE rather than on demand:

   - it is the first moment a [Writer.t] exists, and [red] needs one;
   - it is before the first decision, so the lines sit at level 0 and no [w] retires
     them out from under a derivation that names them (I-S4);
   - the ids are then stable for the whole search, which is what lets a propagator's
     [Explanation] name them as data instead of resolving them at emit time (I-X6).

   PROOF-FORMAT section 3 is normative on the ORDER inside [ensure_direct] and on the
   at-least-one line being *derived* rather than asserted; neither is re-argued here.
   The `red` lines are written over a database that is not yet contradictory, which is
   the condition D-0053 says a `red` must be verified under. Nothing retires these ids
   in this module: lib/core/search.ml sweeps [Writer.live_ids] on both the SAT and the
   UNSAT arm, so I-X2 is discharged there with every other level-0 line. *)
let start_proof t w =
  Writer.header w ~n_model_constraints:t.n;
  List.iter
    (fun x ->
      ignore (ensure_direct t w x);
      Hashtbl.replace t.alo x (derive_at_least_one t w x))
    (direct_requested t)

(* ---------------------------------------------------------------------------
   M1-T7c: expanding an integer linear term into a PB row over the order
   encoding.

   Under the order encoding (docs/SPEC.md 4.2, PROOF-FORMAT section 3), an
   integer variable x with domain [lo, hi] satisfies

       x  =  lo  +  sum_{v = lo+1}^{hi} [x >= v]

   ([x >= v] is 1 when the literal x_ge_v holds, 0 otherwise; x >= lo is the
   constant true and contributes nothing beyond lo itself). Substituting into

       sum_i a_i x_i  <=  rhs

   gives

       sum_i sum_{v = lo_i+1}^{hi_i} a_i [x_i >= v]   <=   rhs - sum_i a_i lo_i

   which is exactly the shape [Opb.le] wants: a list of (coefficient, literal)
   terms over the *unnegated* x_ge_v literals, and a right-hand side. [Opb.le]
   is what negates terms to reach the checker's ">=" form, so this function
   must not also negate -- passing it the substituted "<=" terms unmodified is
   what keeps the sign right for both positive and negative a_i alike.

   A variable with a_i = 0 contributes nothing (skipped outright, so it never
   even touches the constant). A singleton domain (lo_i = hi_i) has no order
   literals at all -- the [List.init] below produces zero terms for it -- and
   contributes only lo_i * a_i to the constant. *)
let linear_terms_int_lin_le t terms =
  List.fold_left
    (fun (acc, const) (a, x) ->
      if a = 0 then (acc, const)
      else
        let v = find t x in
        let const = const + (a * v.lo) in
        let vterms =
          List.init (max 0 (v.hi - v.lo)) (fun i -> (a, Lit.ge x (v.lo + 1 + i)))
        in
        (acc @ vterms, const))
    ([], 0) terms

(* The full row  sum_i a_i x_i <= rhs,  as a normalised [Opb.t]. Exposed on its
   own (not just via [add_int_lin_le]) so a caller -- or a test -- can inspect
   the row before it is committed to the .opb. *)
let expand_int_lin_le t terms rhs =
  let opb_terms, const = linear_terms_int_lin_le t terms in
  Opb.normalise (Opb.le opb_terms (rhs - const))

(* ---------------------------------------------------------------------------
   M1-T32: the precondition that makes "Compile is the only door" enforced rather
   than merely true. Read the header first.
   --------------------------------------------------------------------------- *)

(* The two magnitudes a linear row's arithmetic is bounded by, over the DECLARED
   domains, computed in [Arith] so that measuring the row cannot itself wrap:

     S = sum_i |a_i| * max(|lo_i|, |hi_i|)      the term mass
     W = sum_i |a_i| * (hi_i - lo_i)            the expanded row's coefficient mass

   A term with a_i = 0 contributes nothing, exactly as in
   [linear_terms_int_lin_le] -- the two must skip the same terms or the guard would
   measure a row the expansion does not build. *)
let row_magnitudes t terms =
  List.fold_left
    (fun (s, w) (a, x) ->
      if a = 0 then (s, w)
      else
        let v = find t x in
        let m = Arith.abs a in
        let s = Arith.add s (Arith.mul m (max (Arith.abs v.lo) (Arith.abs v.hi))) in
        let w = Arith.add w (Arith.mul m (Arith.sub v.hi v.lo)) in
        (s, w))
    (0, 0) terms

(* Is every integer derived from  sum_i a_i x_i <= rhs  representable?

   The derivation, and it is an envelope rather than the row itself so that it also
   covers lib/proof/opb.ml, which this module cannot check from the inside:

   - [linear_terms_int_lin_le]'s fold computes each product a_i * lo_i and a running
     constant. Each product is at most S and the running constant is at most S, since a
     partial sum is bounded by the sum of the magnitudes.
   - [expand_int_lin_le] then computes rhs - const, at most |rhs| + S.
   - [Opb.le] negates every coefficient (magnitudes unchanged) and the right-hand side.
   - [Opb.normalise] merges repeated variables -- a merged coefficient is at most W --
     and moves one coefficient per negative or negated term to the right-hand side, a
     total movement of at most W.

   So |rhs| + S + W bounds every intermediate. Computing it in [Arith] and discarding
   the result is the check: if it can be computed, nothing downstream wraps. *)
let check_lin_le_computable t terms rhs ~what =
  let s, w = row_magnitudes t terms in
  try ignore (Arith.add (Arith.add (Arith.abs rhs) s) w : int)
  with Unrepresentable why ->
    raise
      (Unrepresentable
         (Printf.sprintf
            "%s: the row's arithmetic does not fit in a 63-bit int (%s). Committing it \
             would put a constraint in the .opb that is not the one posted, and veripb \
             would verify the wrong model -- see docs/DECISIONS.md D-0029. \
             lib/flatzinc/compile.ml's cap is what keeps this unreachable for a model \
             the CLI accepts; a caller that reaches Encoding directly has to stay inside \
             it too."
            what why))

(* Post  sum_i a_i x_i <= rhs  as a model constraint and hand back its id.
   Terms are (coefficient, integer-variable-name) pairs, matching the shape
   [add_equality] and [add_constraint] already use for term lists elsewhere in
   this module. The expansion always produces a ">=" row (see [expand_int_lin_le]
   above via [Opb.le]), so it never trips [add_constraint]'s refusal of [Eq] --
   there is no separate equality path to keep in sync with I-X5 here.

   This is one of the two committing doors M1-T32 guards. The check runs BEFORE the
   expansion, so a row that cannot be computed never reaches [t.rev_constraints] and
   the encoding is left exactly as it was. *)
let add_int_lin_le t terms rhs =
  check_lin_le_computable t terms rhs ~what:"Encoding.add_int_lin_le";
  add_constraint t (expand_int_lin_le t terms rhs)

(* ---------------------------------------------------------------------------
   M1-T9: disequalities.

   ---------------------------------------------------------------------------
   Part 1 -- saying "x <> v" in the order encoding
   ---------------------------------------------------------------------------

   docs/PROOF-FORMAT.md section 3 introduces the direct encoding with the remark
   that a disequality is what needs it, and that is true of a disequality's
   *literal*: the order encoding has no single Boolean meaning "x = v", so nothing
   in it can be negated to get one. It is *not* true of a disequality's *clause*,
   and a clause is all a [rup] target ever needs:

       x <> v     <->     ~[x >= v]  \/  [x >= v+1]

   -- x is either strictly below v or strictly above it. Both literals are ordinary
   order-encoding literals that the .opb already declares, so [ne_clause_lits] needs
   no new Boolean, no [red] definition, and no channelling. The constant halves drop
   out exactly as they do everywhere else in this module: at [v = decl_lo] the
   literal [x >= v] is the constant true, so [~[x >= v]] is the constant false and
   contributes nothing, leaving the single literal [x >= lo+1]; symmetrically at
   [v = decl_hi]. A variable declared fixed at [v] loses both halves and the clause
   is *empty* -- which is the right answer, being the false clause: "x <> v" is
   unsatisfiable when the model declares x = v.

   This is deliberately not a second naming scheme (section 3's standing warning):
   it introduces no name at all, it spends the two order literals the encoding
   already has. The direct encoding above stays exactly as it was, still the thing
   M4's all_different and element will need -- a *reason* that mentions a hole
   ("x <> v holds") cannot be negated into a clause without a single literal for it,
   which is the case that genuinely forces [ensure_direct]. A disequality
   propagator's reasons are only ever "these variables are fixed to these values",
   whose negation is this clause, so M1-T9 does not reach that case. See the report
   for the docs change this implies.

   ---------------------------------------------------------------------------
   Part 2 -- putting "sum a_i x_i <> c" in the .opb
   ---------------------------------------------------------------------------

   The .opb *must* carry the disequality. It is the artefact the checker validates
   a [conclusion SAT] assignment against, so an .opb that omitted it would be a
   relaxation of the model and would accept a solution the model forbids -- the same
   class of unsoundness [Compile.reject_set_domain] refuses a set domain over.

   A single PB row cannot say [<>]. Two can, with one fresh Boolean [b] selecting
   which side of [c] the sum falls on, and the row's own attainable range as the
   big-M constant (so the unselected side is vacuous rather than merely large):

       L = min over declared domains of sum a_i x_i
       U = max over declared domains of sum a_i x_i

       row A:   sum a_i x_i  -  (U - c + 1) b   <=   c - 1
       row B:   sum a_i x_i  -  (c + 1 - L) b   >=   L

   b = 0 makes A say [sum <= c-1] and B say [sum >= L], which is vacuous; b = 1
   makes B say [sum >= c+1] and A say [sum <= U], vacuous. So the pair is exactly
   [sum <> c] projected onto the model's own variables, and b is determined by any
   solution rather than free (which is what keeps [conclusion SAT] working: search
   hands veripb the model variables' literals only, and whichever of A/B is tight
   unit-propagates b for it -- checked against the checker, not assumed).

   When c is outside [L, U] the disequality is vacuously true and both rows come out
   vacuous of their own accord (the big-M constant goes non-positive and each row
   degenerates to a bound the range already guarantees); there is no special case
   here and none is wanted, for the reason [Compile]'s ground-constraint comment
   gives -- a special case is a place the .opb and the propagator can disagree.

   Both rows go through [add_int_lin_le], so both are ordinary [>=] lines and the
   [=]-counts-as-two trap (section 2's Traps, [Opb.n_checker_constraints]) is not in
   play: [add_int_lin_ne] adds exactly two to [n_constraints] and to the [f] count.
   --------------------------------------------------------------------------- *)

(* The literals of the clause "x <> value", over the order encoding, given the
   variable's *declared* bounds. [[]] is the false clause and means the declared
   domain is the single value [value].

   Takes the bounds rather than reading them from a [t] so that a propagator can
   call it with the declared bounds it froze at construction time (docs/DECISIONS.md
   D-0010 requires that freezing, because the store no longer holds them once
   anything has narrowed the domain) -- the same reason [Order_reason]'s chain
   helpers in lib/core/prop/ take explicit bounds. [ne_clause] below is the
   [t]-reading wrapper for callers that are already on the proof side. *)
let ne_clause_lits ~name ~decl_lo ~decl_hi value =
  if decl_lo > decl_hi then invalid_arg "Encoding.ne_clause_lits: empty declared domain";
  if value < decl_lo || value > decl_hi then
    invalid_arg
      (Printf.sprintf "Encoding.ne_clause_lits: %d is outside %s's declared domain %d..%d"
         value name decl_lo decl_hi);
  (if value > decl_lo then [ Lit.negate (Lit.ge name value) ] else [])
  @ if value < decl_hi then [ Lit.ge name (value + 1) ] else []

(* "x <> value" for a variable this encoding has declared. *)
let ne_clause t x value =
  let v = find t x in
  ne_clause_lits ~name:x ~decl_lo:v.lo ~decl_hi:v.hi value

(* ---------------------------------------------------------------------------
   M4-T1: all_different_int, as pairwise disequality CLAUSES over the order encoding
   ---------------------------------------------------------------------------

   One .opb row per (unordered pair of variables, shared declared value):

       x <> v  \/  z <> v        i.e.   ~x_ge_v \/ x_ge_(v+1) \/ ~z_ge_v \/ z_ge_(v+1)

   spelled with [ne_clause_lits] on each side, so the constant halves drop at the
   declared bounds exactly as they do for `int_ne`.

   WHY NOT [add_int_lin_ne] PER PAIR, which is the obvious reuse and was the first
   shape tried. Two reasons, and the second is the one that decided it:

   1. Size. The big-M pair is 2 rows plus a fresh Boolean per pair, but each row is a
      full-width order-encoding expansion of `x - z`; the clause form is one row per
      shared value, each of at most four literals, and no auxiliary variable at all.

   2. **The Hall justification has to recover a per-value at-most-one line, and it has
      to recover it by [pol].** From this clause form the recovery is five ids and one
      division (lib/core/prop/alldiff.ml, [pair_amo]); from the big-M pair it is a
      derivation that must first re-establish "x_eq_v pins every rung of x's ladder",
      which is the variable's whole declared width, twice, per pair, per value. The
      cheap route is a [rup] -- and a [rup] is exactly what must NOT be in this
      derivation: lib/core/search.ml's [rests_on_a_clause] routes any conflict whose
      derivation rests on an [Explanation.Clause] the D-0022 way, so `conclusion UNSAT`
      would cite the empty clause and every [pol] in the Hall tree would be decorative
      (D-0057, and again in D-0060). A derivation nothing checks is not evidence, and
      this row exists to produce evidence.

   Faithfulness is the same argument [ne_clause_lits] already makes: "x <> v" as a
   clause over order literals introduces no name and no channelling, so the .opb still
   speaks only about the model's own variables and a [conclusion SAT] assignment over
   them decides every row. A pair whose two variables are both declared fixed at [v]
   yields the EMPTY clause, which is the false row -- the right answer, and the same
   degeneracy [ne_clause_lits]'s own header records.

   Returns, for each pair and value, the id of that row, keyed by the two variable
   names in the order given and the value. The caller (lib/flatzinc/compile.ml) hands
   the list to the propagator, which names the ids with [Explanation.Model_row]. *)
let add_all_different t (names : string list) : ((string * string * int) * cid) list =
  let rec pairs = function
    | [] -> []
    | x :: rest -> List.map (fun z -> (x, z)) rest @ pairs rest
  in
  List.concat_map
    (fun (x, z) ->
      let vx = find t x and vz = find t z in
      let lo = Stdlib.max vx.lo vz.lo and hi = Stdlib.min vx.hi vz.hi in
      List.init
        (Stdlib.max 0 (hi - lo + 1))
        (fun i ->
          let v = lo + i in
          let lits =
            ne_clause_lits ~name:x ~decl_lo:vx.lo ~decl_hi:vx.hi v
            @ ne_clause_lits ~name:z ~decl_lo:vz.lo ~decl_hi:vz.hi v
          in
          ((x, z, v), add_constraint t (Opb.clause lits))))
    (pairs names)

(* The least and greatest values [sum a_i x_i] can take over the declared domains.
   Zero coefficients contribute nothing, as everywhere else in this module. *)
let linear_span t terms =
  List.fold_left
    (fun (lo, hi) (a, x) ->
      if a = 0 then (lo, hi)
      else
        let v = find t x in
        if a > 0 then (lo + (a * v.lo), hi + (a * v.hi))
        else (lo + (a * v.hi), hi + (a * v.lo)))
    (0, 0) terms

(* A name for an auxiliary Boolean that no FlatZinc identifier can collide with,
   either as this module's own key or as the .opb name [Lit.sanitize] gives it.

   The key cannot collide because '$' is not a FlatZinc identifier character
   (lib/flatzinc/lexer.ml's [is_ident_start]/[is_ident_char]). The .opb name can, in
   principle -- [sanitize] maps '$' to '_', so "$ne0" and a variable actually called
   "_ne0" would both be "_ne0" -- and a silent collision there would merge two
   variables' literals inside [Opb.normalise], which is exactly the failure
   [Compile.check_name_collisions] exists to prevent for model variables. So the
   candidate is checked against every declared variable's sanitised name and bumped
   until it is free. That check is sound only because every model variable is
   declared before any row is posted, which lib/flatzinc/compile.ml's header states
   as a requirement of its own and which [add_int_lin_le] already relies on. *)
let fresh_aux_name t prefix =
  let taken = Hashtbl.create 64 in
  Hashtbl.iter (fun k _ -> Hashtbl.replace taken (Lit.sanitize k) ()) t.ints;
  let rec go i =
    let cand = Printf.sprintf "$%s%d" prefix i in
    if Hashtbl.mem t.ints cand || Hashtbl.mem taken (Lit.sanitize cand) then go (i + 1)
    else (
      t.n_aux <- i + 1;
      cand)
  in
  go t.n_aux

(* The two rows of [sum a_i x_i <> rhs], as [Opb.t] values, together with the name of
   the auxiliary Boolean they share. Exposed separately from [add_int_lin_ne] for the
   same reason [expand_int_lin_le] is exposed separately from [add_int_lin_le]: so a
   caller -- or a test -- can look at the rows before they are committed to the .opb.

   The aux variable must already be declared (as a bool, i.e. the order encoding on
   [0, 1], D-0007) when this is called; [add_int_lin_ne] is what declares it. *)
let expand_int_lin_ne t terms rhs ~aux =
  let l, u = linear_span t terms in
  let big_a = u - rhs + 1 in
  let big_b = rhs + 1 - l in
  let row_a = expand_int_lin_le t (terms @ [ (-big_a, aux) ]) (rhs - 1) in
  (* sum >= L + big_b * b  is  -sum + big_b * b <= -L. *)
  let row_b =
    expand_int_lin_le t (List.map (fun (a, x) -> (-a, x)) terms @ [ (big_b, aux) ]) (-l)
  in
  (row_a, row_b)

(* Post [sum a_i x_i <> rhs] as two model constraints and hand back both ids, in the
   order they appear in the .opb: (A, B) with A the [sum <= c-1] side. Terms are
   (coefficient, integer-variable-name) pairs, the same shape [add_int_lin_le] takes.

   Declares the auxiliary Boolean as a side effect, so this must be called while the
   .opb is still being built, and the returned ids obey I-X5 like any others. A
   caller that wants the rows without the side effect wants [expand_int_lin_ne]. *)
(* The [int_lin_ne] half of M1-T32's precondition. Its A/B pair is the worst of the
   four arithmetic paths lib/core/checked.ml's header sizes the cap against (path 4),
   so it is the one place where checking only the base row would not be enough.

   Checked here rather than inside [expand_int_lin_ne] for two reasons: that function
   is the inspect-before-committing form, like [expand_int_lin_le] (see the header);
   and this runs before [fresh_aux_name] mints anything, so a refused row leaves no
   auxiliary Boolean declared behind it.

   The auxiliary is a bool on [0, 1], so its contribution to both magnitudes is just
   |coefficient| -- which is why the two augmented rows can be measured before the
   aux exists. That mirrors [expand_int_lin_ne]'s own construction; the two must agree
   about the big-M constants, so the formulas are written the same way round. *)
let check_lin_ne_computable t terms rhs ~what =
  check_lin_le_computable t terms rhs ~what;
  let s, w = row_magnitudes t terms in
  let l, u =
    List.fold_left
      (fun (lo, hi) (a, x) ->
        if a = 0 then (lo, hi)
        else
          let v = find t x in
          if a > 0 then (Arith.add lo (Arith.mul a v.lo), Arith.add hi (Arith.mul a v.hi))
          else (Arith.add lo (Arith.mul a v.hi), Arith.add hi (Arith.mul a v.lo)))
      (0, 0) terms
  in
  let big_a = Arith.add (Arith.sub u rhs) 1 in
  let big_b = Arith.sub (Arith.add rhs 1) l in
  let fits ~big ~rhs' =
    let s = Arith.add s (Arith.abs big) and w = Arith.add w (Arith.abs big) in
    ignore (Arith.add (Arith.add (Arith.abs rhs') s) w : int)
  in
  try
    (* row A:  sum a_i x_i - big_a * aux <= rhs - 1 *)
    fits ~big:big_a ~rhs':(Arith.sub rhs 1);
    (* row B:  -sum a_i x_i + big_b * aux <= -L *)
    fits ~big:big_b ~rhs':(Arith.neg l)
  with Unrepresentable why ->
    raise
      (Unrepresentable
         (Printf.sprintf
            "%s: the disequality's A/B pair does not fit in a 63-bit int (%s). See \
             docs/DECISIONS.md D-0029 and lib/core/checked.ml's envelope, path 4 -- this \
             pair is the widest arithmetic the .opb ever performs."
            what why))

let add_int_lin_ne t terms rhs =
  check_lin_ne_computable t terms rhs ~what:"Encoding.add_int_lin_ne";
  let aux = fresh_aux_name t "ne" in
  declare_bool t aux;
  let row_a, row_b = expand_int_lin_ne t terms rhs ~aux in
  let id_a = add_constraint t row_a in
  let id_b = add_constraint t row_b in
  (id_a, id_b)

(* ---------------------------------------------------------------------------
   M3-T1: reified variables, and the two doors a definition can come through
   ---------------------------------------------------------------------------

   A *reified variable* is a Boolean [b] that stands for a condition [C]:

       b  <->  C

   D-0007 already says what [b] is: a FlatZinc [var bool] is the order encoding on
   [0, 1], one PB variable [b_ge_1], and "b is true" is [Lit.bool_true b]. Reification
   introduces NO new naming scheme (section 3's standing warning) -- a reifier is an
   ordinary Boolean, and that is deliberate: it means every existing propagator,
   [assignment_lits], and every [pol] operand already knows how to talk about one.

   The equivalence is two PB rows. With [C] normalised to  sum a_i l_i >= k  (all
   a_i > 0, [Opb.normalise]) and  A = sum a_i:

     FWD   b -> C        sum a_i l_i  +  k ~b        >= k
     BWD   C -> b        sum a_i ~l_i +  (A-k+1) b   >= A-k+1

   FWD reads: with b true the ~b term vanishes and C is asserted; with b false the term
   pays the whole right-hand side and the row is vacuous. BWD is FWD applied to the
   negation of C, which for a normalised row is  sum a_i ~l_i >= A-k+1. The two
   big-M constants are the smallest that work, which matters: a bigger one is still
   sound but weakens what a propagator can derive from the row by cutting planes.

   [k <= 0] and [k > A] are refused ([Reif_constant]). Such a condition is constant on
   the coefficients alone, so "b <-> C" is not a reification at all, it is a fixed
   Boolean -- and the two rows degenerate (FWD stops mentioning b). The caller decides
   what a fixed Boolean means in its model; this module will not guess. The check is
   SYNTACTIC, over the normalised row: a condition that is constant only because of the
   order ladder is not caught here and does not need to be, since the rows stay correct.

   ---------------------------------------------------------------------------
   The two doors, and why there are two
   ---------------------------------------------------------------------------

   [add_reif]     puts FWD and BWD in the .opb, eagerly, as model rows.
   [define_reif]  puts them in the .pbp, lazily, as two [red] lines.

   They share [reif_rows], so the two cannot disagree about the encoding. Which door a
   definition comes through is NOT a matter of taste:

   * A reified constraint the FlatZinc model states -- [int_le_reif(x, y, b)] -- is
     MODEL information about a bool [b] the model also uses elsewhere. It goes in the
     .opb. [red] cannot introduce it, and the checker is the one that says so: [red]
     preserves satisfiability OF THE DATABASE, so it can only add what the database
     already entails up to the witness. If [b_ge_1] occurs in any row already loaded,
     the witness [b_ge_1 -> 0] has to discharge that row under the substitution, and
     for a model that genuinely constrains b it cannot. veripb refuses it, and
     test/unit/test_proof.ml performs that refusal rather than describing it.

   * A condition the model never named -- one a propagator wants to carry as a single
     literal mid-search -- has no row to sit in, because the .opb was written before
     the propagator ran. That is [define_reif]'s case, and it is the same shape as the
     direct encoding above: lazy, introduced by [red], retired by its own ids.

   [define_reif] therefore has a PRECONDITION, and it is not a style rule: the reifier
   must be FRESH -- not mentioned by any row already in the .opb, nor by the objective.
   [Reif_not_fresh] is raised before a single line is written. The exception exists so
   that a caller reaching for the wrong door finds out here, with the variable's name in
   hand, instead of reading a redundance goal failure out of a checker log.

   ---------------------------------------------------------------------------
   Order of the two [red] lines
   ---------------------------------------------------------------------------

   FWD first, under the witness [b_ge_1 -> 0]; BWD second, under [b_ge_1 -> 1]. This is
   the same rule [ensure_direct] states for the channelling clauses and for the same
   reason. FWD is satisfied outright by b -> 0, and when it goes in first nothing else
   in the database mentions b, so it raises no goal. BWD is satisfied by b -> 1, and the
   one goal it does raise -- FWD under b -> 1, which is C itself -- is discharged by
   BWD's own negation: negating BWD forces b to 0 and leaves exactly C. Swapping the
   two witnesses makes veripb reject the definition, which is also performed rather than
   described.

   Deletion: the caller holds the [reif] value and owes [reif_ids] to invariant I-X2,
   exactly as the caller of [Writer.pol] owes the id it receives. There is no registry
   and no idempotence -- unlike [ensure_direct], which is keyed on a variable, a
   definition is keyed on a CONDITION, and the module has no notion of two conditions
   being the same one. Defining the same condition twice is two definitions and two
   deletions.

   The exceptions are declared here rather than with the others at the top of the file
   so that this whole feature is one contiguous block: several sessions edit this file
   at once, and a block appends where a scattered edit conflicts. *)

(* The condition is constant on its coefficients alone, so [b] is fixed; the bool is
   the value it is fixed to. *)
exception Reif_constant of string * bool

(* [define_reif] was asked to define a reifier that already occurs in the .opb. Use
   [add_reif]: see the header. *)
exception Reif_not_fresh of string

(* The condition mentions the reifier. b <-> C(b) is not a definition. *)
exception Reif_in_condition of string

(* A reifier that is declared but is not a bool on [0, 1] (D-0007). *)
exception Reif_not_boolean of string * int * int

(* A definition, and the two ids that are its whole substance: [r_fwd] is what a
   propagator cites to derive the condition from the reifier, [r_bwd] the reverse. *)
type reif = { r_name : string; r_fwd : cid; r_bwd : cid }

let reif_name r = r.r_name
let reif_lit r = Lit.bool_true r.r_name
let reif_fwd r = r.r_fwd
let reif_bwd r = r.r_bwd

(* Every id the definition minted, for invariant I-X2. *)
let reif_ids r = [ r.r_fwd; r.r_bwd ]

(* A reifier name this encoding has not used. Shares [fresh_aux_name]'s counter with
   the disequality auxiliaries, which only ever increases, so a name handed out once is
   never handed out twice. *)
let fresh_reif_name t = fresh_aux_name t "reif"
let reif_pbvar reifier = (Lit.bool_true reifier).Lit.v

(* Does [reifier]'s Boolean occur in anything already committed to the .opb? *)
let reif_occurs t reifier =
  let target = Lit.var_name (reif_pbvar reifier) in
  let in_terms terms =
    List.exists (fun (_, (l : Lit.t)) -> String.equal (Lit.var_name l.Lit.v) target) terms
  in
  List.exists (fun c -> in_terms (Opb.terms c)) t.rev_constraints
  || match t.objective with None -> false | Some o -> in_terms o.Opb.obj_terms

(* The two rows of  reifier <-> cond,  as [Opb.constr] values. Exposed on its own for
   the reason [expand_int_lin_le] is: a caller -- or a test -- can look at the rows
   before either door commits them. Pure; it touches no encoding state, which is what
   lets the .opb door and the .pbp door share it. *)
let reif_rows ~reifier ~cond =
  if Opb.relation cond = Opb.Eq then
    invalid_arg
      "Encoding.reif_rows: an `=` condition is two constraints and cannot be reified as \
       one pair. Reify the two inequalities separately.";
  let c = Opb.normalise cond in
  let terms = Opb.terms c and k = Opb.rhs c in
  let b = Lit.bool_true reifier in
  let bname = Lit.var_name b.Lit.v in
  if List.exists (fun (_, (l : Lit.t)) -> String.equal (Lit.var_name l.Lit.v) bname) terms
  then raise (Reif_in_condition reifier);
  (* [Opb.normalise] leaves every coefficient strictly positive, so A is the largest
     value the left-hand side can take and 0 the smallest. *)
  let big_a = List.fold_left (fun acc (a, _) -> Arith.add acc a) 0 terms in
  if k <= 0 then raise (Reif_constant (reifier, true));
  if k > big_a then raise (Reif_constant (reifier, false));
  let k' = Arith.add (Arith.sub big_a k) 1 in
  let fwd = Opb.ge ((k, Lit.negate b) :: terms) k in
  let bwd =
    Opb.ge ((k', b) :: List.map (fun (a, (l : Lit.t)) -> (a, Lit.negate l)) terms) k'
  in
  (fwd, bwd)

(* The reifier is a bool (D-0007). Declare it if it is new; refuse it if it is declared
   as something else, because then [b_ge_1] is one rung of a longer ladder and the two
   rows above would be saying something other than what the caller means. *)
let ensure_reif_bool t reifier =
  match Hashtbl.find_opt t.ints reifier with
  | None -> declare_bool t reifier
  | Some v ->
      if not (v.lo = 0 && v.hi = 1) then raise (Reif_not_boolean (reifier, v.lo, v.hi))

(* The .opb door: the model says  reifier <-> cond.  Returns the two ids, FWD first. *)
let add_reif t ~reifier ~cond =
  ensure_reif_bool t reifier;
  let fwd, bwd = reif_rows ~reifier ~cond in
  let id_f = add_constraint t fwd in
  let id_b = add_constraint t bwd in
  (id_f, id_b)

let add_int_lin_le_reif t terms rhs ~reifier =
  check_lin_le_computable t terms rhs ~what:"Encoding.add_int_lin_le_reif";
  add_reif t ~reifier ~cond:(expand_int_lin_le t terms rhs)

(* The .pbp door: introduce  reifier <-> cond  as two [red] lines. See the header for
   the freshness precondition and for why the order of the two is not free. *)
let define_reif t w ~reifier ~cond =
  (* Every refusal happens before the first line is written, so a rejected definition
     leaves neither the encoding nor the proof file changed. *)
  let fwd, bwd = reif_rows ~reifier ~cond in
  if reif_occurs t reifier then raise (Reif_not_fresh reifier);
  ensure_reif_bool t reifier;
  let bv = reif_pbvar reifier in
  let origin = Printf.sprintf "reif %s" reifier in
  Writer.comment w "definition of the reifier %s" reifier;
  let r_fwd = Writer.red w ~origin ~witness:[ (bv, Writer.Zero) ] fwd in
  let r_bwd = Writer.red w ~origin ~witness:[ (bv, Writer.One) ] bwd in
  { r_name = reifier; r_fwd; r_bwd }

(* The same, for a condition given as  sum a_i x_i <= rhs  over declared variables.
   [check_lin_le_computable] guards it for the reason [add_int_lin_le] is guarded: a
   row whose arithmetic wrapped states something other than the caller posted, and a
   .pbp line is no safer to get wrong than a .opb one. *)
let define_reif_int_lin_le t w ~reifier terms rhs =
  check_lin_le_computable t terms rhs ~what:"Encoding.define_reif_int_lin_le";
  define_reif t w ~reifier ~cond:(expand_int_lin_le t terms rhs)

let retire_reif w r = Writer.delete_many w (reif_ids r)

(* ---------------------------------------------------------------------------
   M3-T2 / M3-T4: the same two rows, in the currency a propagator can cite
   ---------------------------------------------------------------------------

   [add_reif] above posts FWD and BWD as [Opb.constr] values built by [reif_rows] --
   literals and big-M constants, assembled here. That is the right shape for
   [define_reif] (a [red] body is literals) and the wrong one for M3-T2, because a
   propagator does not cite a row by rebuilding it: [Linear] cites [Model_row row_id]
   and reproduces the row from *integer terms and a right-hand side* ([Linear.pb_row],
   M2-L6/D-0054, which test_learn.ml pins against every row the suite compiles).

   So M3-T2 needs the two rows as ordinary [int_lin_le] rows. They are:

     FWD   sum a_i x_i  +  K  b  <=  rhs + K       K  = hi - rhs
     BWD  -sum a_i x_i  -  K' b  <=  -rhs - 1      K' = rhs + 1 - lo

   where [(lo, hi)] is [linear_span] of the condition over the DECLARED domains. Read
   FWD: at b = 1 it is the condition; at b = 0 it is `sum <= hi`, which every
   assignment satisfies. Read BWD: at b = 0 it is `sum >= rhs + 1`, the negation; at
   b = 1 it is `sum >= lo`, vacuous. Both big-Ms are the smallest that work, for the
   reason [reif_rows] gives: a bigger one is sound but weakens what a [pol] over the
   row can cut.

   **These are not a second encoding of reification -- they are the SAME two rows.**
   Expand FWD through [expand_int_lin_le] and normalise, and you get exactly
   [reif_rows]'s FWD, coefficient for coefficient: the reifier is a bool on [0, 1]
   (D-0007) whose single rung carries the whole big-M, and the normalised degree of
   the condition IS [hi - rhs]. test/unit/test_proof.ml performs that comparison on
   both rows rather than leaving this paragraph to be believed -- if the two ever drift
   the .opb door would be saying two different things, which is precisely what
   [reif_rows] was made pure and shared to prevent.

   [Reif_constant] is raised on the same condition [reif_rows] raises it on, and from
   the same numbers: [K <= 0] is a condition the declared domains already entail, and
   [K' <= 0] one they already refute. A caller that wants to keep such a model posts
   the reifier's value as a unit row instead -- lib/flatzinc/compile.ml does exactly
   that, because a FlatZinc model is entitled to say something trivially true. *)

(* [vac] is the value of [reifier] at which the row must say nothing. *)
let guard_row terms rhs ~reifier ~big_m ~vac =
  if vac = 1 then (terms @ [ (Arith.neg big_m, reifier) ], rhs)
  else (terms @ [ (big_m, reifier) ], Arith.add rhs big_m)

(* The two big-M constants of  reifier <-> (sum a_i x_i <= rhs),  smallest first as
   above. Pure: it reads declared bounds and computes, and commits nothing. *)
let reif_big_m t terms rhs =
  let lo, hi = linear_span t terms in
  (Arith.sub hi rhs, Arith.add (Arith.sub rhs lo) 1)

(* The .opb door for a model-stated [int_lin_le_reif], as two int_lin_le rows.
   Returns [(fwd_id, bwd_id, k_fwd, k_bwd)]: the ids to cite and the two big-Ms, which
   the caller needs to build the [Linear.t] that cites them -- the propagator's terms
   must be the row's terms or the citation names a constraint it cannot reproduce. *)
let add_int_lin_le_reif_rows t terms rhs ~reifier =
  check_lin_le_computable t terms rhs ~what:"Encoding.add_int_lin_le_reif_rows";
  ensure_reif_bool t reifier;
  let k_fwd, k_bwd = reif_big_m t terms rhs in
  if k_fwd <= 0 then raise (Reif_constant (reifier, true));
  if k_bwd <= 0 then raise (Reif_constant (reifier, false));
  let neg = List.map (fun (a, x) -> (Arith.neg a, x)) terms in
  let f_terms, f_rhs = guard_row terms rhs ~reifier ~big_m:k_fwd ~vac:0 in
  let b_terms, b_rhs =
    guard_row neg (Arith.sub (Arith.neg rhs) 1) ~reifier ~big_m:k_bwd ~vac:1
  in
  let fwd_id = add_int_lin_le t f_terms f_rhs in
  let bwd_id = add_int_lin_le t b_terms b_rhs in
  (fwd_id, bwd_id, k_fwd, k_bwd)

(* ---------------------------------------------------------------------------
   The equality family: four rows, and why it is not two
   ---------------------------------------------------------------------------

   `b <-> (sum = c)` is not one reification of one inequality, and D-0053 says so:
   it needs both directions of the equality under [b], and the DISEQUALITY under
   [~b]. The four rows, with [pos] saying whether [b] means "= c" ([int_eq_reif]) or
   "<> c" ([int_ne_reif]):

     LE   sum a x <= c          guarded, vacuous when the equality side is off
     GE  -sum a x <= -c         guarded likewise
     A    sum a x <= c - 1 + big_a * ne_aux    guarded, vacuous when the
     B   -sum a x <= -c - 1 + big_b * ~ne_aux  disequality side is off

   A and B are [expand_int_lin_ne]'s own pair with one more guard term, and the
   auxiliary Boolean is the same .opb-only one a plain [int_lin_ne] uses: nothing
   propagates over it and nothing cites A or B, exactly as lib/core/prop/ne.ml
   describes for the unguarded pair. LE and GE ARE cited, so their ids come back.

   **Why no [p] and [q].** D-0053 left open where the `p <-> (sum<=c)`,
   `q <-> (sum>=c)`, `b <-> p /\ q` decomposition's two fresh reifiers should live.
   The answer taken here is that they are not needed: the only thing the conjunction
   buys is the direction `(sum = c) -> b`, and A/B already carry it -- they are the
   contrapositive `~b -> (sum <> c)` written as PB rows, which is what
   [add_int_lin_ne] has done since M1-T9. Two fresh reifiers would also have to be
   fresh *store* variables, since something must propagate them, and
   bin/main.ml's [assignment_values] rejects any solver variable outside the model's
   own -- so the decomposition is not merely redundant here, it is not reachable
   without a change on the other side of that bridge. *)
let add_int_lin_eq_reif t terms rhs ~reifier ~pos =
  check_lin_ne_computable t terms rhs ~what:"Encoding.add_int_lin_eq_reif";
  ensure_reif_bool t reifier;
  let lo, hi = linear_span t terms in
  let k_le0 = Arith.sub hi rhs and k_ge0 = Arith.sub rhs lo in
  let big_a = Arith.add k_le0 1 and big_b = Arith.add k_ge0 1 in
  (* The declared domains already settle the equality: this is not a reification and
     the caller decides what a fixed Boolean means in its model, exactly as
     [reif_rows] refuses a constant condition. *)
  if k_le0 < 0 || k_ge0 < 0 then raise (Reif_constant (reifier, not pos));
  if k_le0 = 0 && k_ge0 = 0 then raise (Reif_constant (reifier, pos));
  (* One direction of the equality may still be entailed on its own -- `hi = rhs` makes
     `sum <= rhs` free -- and then the smallest big-M is zero, which would make the
     guard TERM vanish and leave a row saying something unconditionally. One is the
     smallest big-M that still has a guard term to cut against, and the row it produces
     is `sum <= rhs` under the literal and `sum <= rhs + 1` without it, both of which
     every assignment the declared domains allow already satisfies. *)
  let k_le = Stdlib.max 1 k_le0 and k_ge = Stdlib.max 1 k_ge0 in
  let neg = List.map (fun (a, x) -> (Arith.neg a, x)) terms in
  (* The equality side is asserted at [b = 1] iff [pos]; so it must be vacuous at the
     other value, and the disequality side at [pos]'s own. *)
  let vac_eq = if pos then 0 else 1 in
  let vac_ne = 1 - vac_eq in
  let le_terms, le_rhs = guard_row terms rhs ~reifier ~big_m:k_le ~vac:vac_eq in
  let ge_terms, ge_rhs = guard_row neg (Arith.neg rhs) ~reifier ~big_m:k_ge ~vac:vac_eq in
  let aux = fresh_aux_name t "ne" in
  declare_bool t aux;
  let a_terms, a_rhs =
    guard_row
      (terms @ [ (Arith.neg big_a, aux) ])
      (Arith.sub rhs 1) ~reifier ~big_m:big_a ~vac:vac_ne
  in
  let b_terms, b_rhs =
    guard_row (neg @ [ (big_b, aux) ]) (Arith.neg lo) ~reifier ~big_m:big_b ~vac:vac_ne
  in
  (* A degenerate side is a row nothing can be derived from and every assignment
     satisfies; it is posted anyway, because the .opb is the artefact a `conclusion SAT`
     is checked against and a missing row there is a relaxation of the model. *)
  let le_id = add_int_lin_le t le_terms le_rhs in
  let ge_id = add_int_lin_le t ge_terms ge_rhs in
  ignore (add_int_lin_le t a_terms a_rhs : cid);
  ignore (add_int_lin_le t b_terms b_rhs : cid);
  (le_id, ge_id, k_le, k_ge)

(* ---------------------------------------------------------------------------
   Views (M4-T0)
   ---------------------------------------------------------------------------

   A view is [s * x + k] over a DECLARED base variable, or a constant. It has no
   declaration of its own, no ladder, no Boolean and no name: see lib/proof/lit.ml's
   "Views" section for the decision and what the alternative costs.

   This is the committing side of that rendering, in the sense encoding.ml's header
   means: the pure transform lives in [Lit], and the trimming to [Holds]/[Fails] at
   the base's DECLARED bounds happens here, because here is where the declaration is
   known. That split is not cosmetic -- it is what makes a view's [cond] come out of
   the same two comparisons a plain variable's does, rather than out of a second
   copy of them that can drift.

   A constant is not a special case of anything below it. [Const c >= n] is decided
   by comparing two integers, which is what [ge] does for a declared variable whose
   bounds happen to coincide; the constant simply has no ivar to look it up in. It
   never reaches [find], so it is never [Undeclared], and it contributes nothing to
   the .opb -- which is the whole point of admitting constants here rather than
   declaring a width-1 variable for each of them. *)
type view = Const of int | View of string * Lit.affine

let view_of_var x = View (x, Lit.identity)
let view_const c = Const c

(* [v + k] and [-v], flattened: a view of a view is a view (Lit.shift / Lit.flip). *)
let view_shift v k =
  match v with
  | Const c -> Const (Arith.add c k)
  | View (x, a) -> View (x, { a with Lit.offset = Arith.add a.Lit.offset k })

let view_negate = function
  | Const c -> Const (Arith.neg c)
  | View (x, a) ->
      View (x, { Lit.negated = not a.Lit.negated; Lit.offset = Arith.neg a.Lit.offset })

(* The declared bounds of a view, in the view's own units. Used by a caller that has
   to state a view's declared range -- D-0010's chains are measured against the
   DECLARED bound, and for a view that bound is the image of the base's. *)
let view_domain t = function
  | Const c -> (c, c)
  | View (x, a) ->
      let lo, hi = domain t x in
      let l = Lit.apply a lo and h = Lit.apply a hi in
      if a.Lit.negated then (h, l) else (l, h)

(* The translation, in checked arithmetic. [n - offset] is the only subtraction a
   view rendering performs, and a wrapped one would silently name a DIFFERENT
   literal -- the exact failure D-0029 records, one layer down: the .opb row and the
   solver would agree on a name neither of them means. So it raises, like every
   other arithmetic on this side of the module (I-X8's discipline, applied to a
   name rather than to a row). *)
let view_base_value a n = Arith.sub n a.Lit.offset

let view_ge t v value =
  match v with
  | Const c -> if c >= value then Holds else Fails
  | View (x, a) ->
      let d = view_base_value a value in
      if a.Lit.negated then le t x (Arith.neg d) else ge t x d

let view_le t v value =
  match v with
  | Const c -> if c <= value then Holds else Fails
  | View (x, a) ->
      let d = view_base_value a value in
      if a.Lit.negated then ge t x (Arith.neg d) else le t x d

let view_gt t v value = view_ge t v (Arith.add value 1)
let view_lt t v value = view_le t v (Arith.sub value 1)

(* [=] and [<>] on a view are the base's, at the translated value: the direct
   encoding a view needs is the BASE's direct encoding, and asking for one the base
   does not have raises [No_direct_encoding] naming the base -- which is the
   variable the caller would have to introduce it for. *)
let view_eq t v value =
  match v with
  | Const c -> if c = value then Holds else Fails
  | View (x, a) ->
      let d = view_base_value a value in
      eq t x (if a.Lit.negated then Arith.neg d else d)

let view_ne t v value =
  match view_eq t v value with
  | Holds -> Fails
  | Fails -> Holds
  | Cond l -> Cond (Lit.negate l)
