(* int_lin_le: sum_i a_i * x_i <= c, over integer variables with possibly negative
   coefficients.

   Consistency level: BOUNDS (docs/SPEC.md 3.2). This propagator only ever reads and
   writes lo/hi; it never punches a hole. It is the reference propagator (docs/ROADMAP.md
   M1-T7a) - every later propagator in prop/ copies this shape, so the structure below
   (compute once, explain lazily, one pass to fixpoint) is deliberate.

   Algorithm (textbook bounds propagation for a linear inequality):

     slack = c - sum_i min(a_i * x_i)
       where min(a_i * x_i) = a_i * lo(x_i)  if a_i >= 0
                             = a_i * hi(x_i)  if a_i <  0

     - slack < 0            : no assignment in the current box satisfies the
                               constraint -> Conflict.
     - otherwise, for each i with a_i <> 0:
         max_i = min(a_i * x_i) + slack        (* largest value a_i*x_i may take *)
         a_i > 0 :  x_i <= floor(max_i / a_i)  -> tighten hi(x_i)
         a_i < 0 :  x_i >= ceil (max_i / a_i)  -> tighten lo(x_i)

   [slack] is computed once from the pre-propagation bounds, and every push above reads
   only the *other* variables' minima, which do not change as a result of tightening
   [x_i] itself (tightening hi(x_i) never moves lo(x_i), and vice versa for a_i < 0). So a
   single pass over all terms already reaches the bounds-consistent fixpoint; there is no
   need to loop back over the terms already visited. That is what makes [propagate]
   idempotent at the interface (I-P3) after just one pass: calling it again recomputes the
   same slack (now possibly larger, since a variable may have been tightened) and finds
   nothing left to push.

   Declared bounds (docs/DECISIONS.md D-0010): a bound fact has to be stated in the order
   encoding's own currency, x = lo_decl + sum_{v=lo_decl+1}^{hi_decl} [x >= v], which needs
   the variable's *declared* domain, not just its current one. [make] therefore reads each
   variable's domain out of the store at construction time and freezes it into [term] -
   this has to happen before anything (including this propagator, on a later call) has
   narrowed it. The chain itself is built by [Order_reason], shared with every other
   linear-family propagator so the substitution is performed exactly once.

   Proof step this justifies (docs/PROOF-FORMAT.md section 4, `int_lin_le` row; see
   docs/DECISIONS.md D-0009 for why this currently renders as `rup`, not `pol`, and
   D-0010 for the chain shape):

     For a pruning that tightens variable [j] (all other terms i <> j untouched), the
     explanation is

       Cut (Trivial, Linear (units, units_rhs), 1, 1)

     where:
       - [Trivial] stands for the model's own constraint row, sum_i a_i x_i <= c.
       - [units] is, for every i <> j with a_i <> 0, the *chain* of order-encoding
         literals witnessing i's current bound relative to its *declared* one
         (Order_reason.lower_bound_terms / upper_bound_terms):
           a_i > 0 : (a_i, Lit.ge (name x_i) v) for v in decl_lo_i+1 .. lo(x_i)
           a_i < 0 : (-a_i, Lit.le (name x_i) v) for v in hi(x_i) .. decl_hi_i-1
         i.e. exactly the literals the order encoding's own expansion of x_i would put
         in the model row, restricted to the prefix/suffix currently known true/false -
         never a single literal scaled by the raw bound value, which is dimensionally
         wrong (D-0010).
       - [units_rhs] = sum_{i<>j} (that chain's contribution), i.e. exactly the numeric
         value subtracted from [c] to get [slack], now measured relative to each
         variable's declared bound rather than its raw current one.

     A [Conflict] (slack < 0) uses the same shape but over *all* terms (there is no
     excluded [j]). *)

module Lit = Baguette_proof.Lit

(* One term of the sum: coefficient (may be negative or zero; zero terms are inert and
   never generate a bound or appear in an explanation), the variable it multiplies, and
   the variable's *declared* domain, frozen at [make] time (D-0010: the offset an
   explanation needs is the declared bound, which the store no longer holds once this or
   any other propagator has narrowed the domain). *)
type term = { coeff : int; x : Var.t; decl_lo : int; decl_hi : int }
type t = { terms : term list; rhs : int }

let name = "int_lin_le"
let consistency = Propagator.Bounds

let make store raw_terms rhs =
  let terms =
    List.map
      (fun (coeff, x) ->
        let d = Store.get store x in
        { coeff; x; decl_lo = Domain.lo d; decl_hi = Domain.hi d })
      raw_terms
  in
  { terms; rhs }

let vars t = List.map (fun tm -> tm.x) t.terms

(* -------------------------------------------------------------- integer division *)

(* [Stdlib.(/)] truncates toward zero, which is the wrong rounding for a negative
   dividend or divisor: bounds propagation needs floor/ceil of the exact rational
   quotient regardless of sign. [b] is never zero here (callers only apply these to
   nonzero coefficients). *)
let floordiv a b =
  let q = a / b and r = a mod b in
  if r <> 0 && (r < 0) <> (b < 0) then q - 1 else q

let ceildiv a b = -floordiv (-a) b

(* ------------------------------------------------------------------- min/max terms *)

(* The smallest value [a * x] can currently take, given [x]'s domain. *)
let term_min store (tm : term) =
  let d = Store.get store tm.x in
  if tm.coeff >= 0 then tm.coeff * Domain.lo d else tm.coeff * Domain.hi d

(* Everything [linear_of_snapshot] needs about one term's current bound, copied out of
   the store immediately - the explanation that eventually uses it must describe the
   state *at pruning time*, not whatever the store looks like when the reason is finally
   forced (docs/ARCHITECTURE.md, "Deferred explanations"). The declared bound travels
   with the term itself ([tm.decl_lo]/[tm.decl_hi]), fixed since [make]. *)
type snap_entry = { s_coeff : int; s_name : string; s_decl : int; s_bound : int; s_lower : bool }

let snapshot store terms =
  List.filter_map
    (fun (tm : term) ->
      if tm.coeff = 0 then None
      else
        let d = Store.get store tm.x in
        let nm = Store.name store tm.x in
        if tm.coeff >= 0 then
          Some
            { s_coeff = tm.coeff; s_name = nm; s_decl = tm.decl_lo; s_bound = Domain.lo d;
              s_lower = true }
        else
          Some
            { s_coeff = -tm.coeff; s_name = nm; s_decl = tm.decl_hi; s_bound = Domain.hi d;
              s_lower = false })
    terms

(* Turn a snapshot into the [Linear] half of the explanation: sum a_i * B_i >= rhs,
   where each variable contributes the chain [Order_reason] builds for its current
   bound relative to its declared one (D-0010). This is the part of the construction
   that is worth deferring - it allocates a [Lit.t] (and sanitises a name) per chain
   step - so callers only run it inside [Explanation.deferred]. *)
let linear_of_snapshot snap =
  let terms, rhs =
    List.fold_left
      (fun (acc_terms, acc_rhs) e ->
        let ts, r =
          if e.s_lower then
            Order_reason.lower_bound_terms ~coeff:e.s_coeff ~name:e.s_name
              ~decl_lo:e.s_decl e.s_bound
          else
            Order_reason.upper_bound_terms ~coeff:e.s_coeff ~name:e.s_name
              ~decl_hi:e.s_decl e.s_bound
        in
        (acc_terms @ ts, acc_rhs + r))
      ([], 0) snap
  in
  Explanation.linear terms rhs

(* Explanation for tightening the bound of the variable excluded from [others] (or, for
   a conflict, [others] is every term). Cheap eagerly (an int/string snapshot); the
   [Lit.t] chain construction is deferred, per docs/ARCHITECTURE.md "Deferred
   explanations". *)
let explain store others =
  let snap = snapshot store others in
  Explanation.deferred (fun () ->
      Explanation.cut Explanation.trivial (linear_of_snapshot snap) 1 1)

(* All terms except the one at [idx] (by position, not value - a variable could in
   principle appear twice, and each occurrence is excluded independently). *)
let others_except terms idx = List.filteri (fun i _ -> i <> idx) terms

(* ------------------------------------------------------------------------ propagate *)

let propagate t store =
  let mins = List.map (fun tm -> term_min store tm) t.terms in
  let total_min = List.fold_left ( + ) 0 mins in
  let slack = t.rhs - total_min in
  if slack < 0 then Propagator.Conflict (explain store t.terms)
  else begin
    let result = ref Propagator.Fixpoint in
    let conflict = ref None in
    List.iteri
      (fun idx (tm, m) ->
        if !conflict = None && tm.coeff <> 0 then begin
          let max_term = m + slack in
          let d = Store.get store tm.x in
          if tm.coeff > 0 then begin
            let new_hi = floordiv max_term tm.coeff in
            if new_hi < Domain.hi d then begin
              let expl = explain store (others_except t.terms idx) in
              match Store.set_hi store tm.x new_hi expl with
              | Store.Conflict e -> conflict := Some e
              | Store.Changed | Store.Unchanged -> ()
            end
          end
          else begin
            let new_lo = ceildiv max_term tm.coeff in
            if new_lo > Domain.lo d then begin
              let expl = explain store (others_except t.terms idx) in
              match Store.set_lo store tm.x new_lo expl with
              | Store.Conflict e -> conflict := Some e
              | Store.Changed | Store.Unchanged -> ()
            end
          end
        end)
      (List.combine t.terms mins);
    (match !conflict with
    | Some e -> result := Propagator.Conflict e
    | None -> ());
    !result
  end
