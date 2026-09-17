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
}

let create () =
  {
    ints = Hashtbl.create 64;
    decl_rev = [];
    rev_constraints = [];
    n = 0;
    objective = None;
    n_aux = 0;
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
        (if value > v.lo then
           let c = Opb.clause [ Lit.negate zl; Lit.ge x value ] in
           let id = Writer.red w ~origin ~witness:[ (z value, Writer.Zero) ] c in
           Hashtbl.replace d.d_lo value id);
        (* ~x_eq_v \/ ~x_ge_(v+1), only when x >= v+1 is not the constant false *)
        (if value < v.hi then
           let c = Opb.clause [ Lit.negate zl; Lit.le x value ] in
           let id = Writer.red w ~origin ~witness:[ (z value, Writer.Zero) ] c in
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
  Writer.pol w
    ~origin:(Printf.sprintf "at-least-one %s" x)
    (Writer.Pol.sum (List.map Writer.Pol.id ids))

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

(* [labels] writes each row as `@cN <row> ;` so the proof can cite it by name. That
   is a VeriPB 3.0 feature and nothing else understands it, so it must match the
   writer's format; [write_opb_for] is the form that cannot get that wrong and is
   what callers should use. *)
let write_opb ?(comments = []) ?labels t oc =
  let labels =
    match labels with Some b -> b | None -> Writer.default_format () = Writer.V3_0
  in
  Opb.write ?objective:t.objective ~labels oc ~comments ~constraints:(constraints t)

(* The .opb written for a particular writer: the labels follow its format. The .opb
   and the .pbp are one artefact in two files and disagreeing about labelling makes
   every citation in the proof a parse error, so tie them together here rather than
   at each of the half-dozen call sites. *)
let write_opb_for ?(comments = []) t w oc =
  write_opb ~comments ~labels:(Writer.format w = Writer.V3_0) t oc

(* Start the proof. Must be called after the .opb is complete (invariant I-X5). *)
let start_proof t w = Writer.header w ~n_model_constraints:t.n

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
   unit-propagates b for it -- checked against veripb 2.2.2, not assumed).

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
