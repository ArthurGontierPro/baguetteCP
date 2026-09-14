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
   keeping them in one place is the only way invariant I-X5 stays true. *)

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
}

let create () =
  {
    ints = Hashtbl.create 64;
    decl_rev = [];
    rev_constraints = [];
    n = 0;
    objective = None;
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

let declare_int t x ~lo ~hi =
  if lo > hi then raise (Empty_domain x);
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

let write_opb ?(comments = []) t oc =
  Opb.write ?objective:t.objective oc ~comments ~constraints:(constraints t)

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

(* Post  sum_i a_i x_i <= rhs  as a model constraint and hand back its id.
   Terms are (coefficient, integer-variable-name) pairs, matching the shape
   [add_equality] and [add_constraint] already use for term lists elsewhere in
   this module. The expansion always produces a ">=" row (see [expand_int_lin_le]
   above via [Opb.le]), so it never trips [add_constraint]'s refusal of [Eq] --
   there is no separate equality path to keep in sync with I-X5 here. *)
let add_int_lin_le t terms rhs = add_constraint t (expand_int_lin_le t terms rhs)
