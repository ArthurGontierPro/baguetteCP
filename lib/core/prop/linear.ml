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

   Proof step this justifies (docs/PROOF-FORMAT.md section 4, `int_lin_le` row: "the model
   constraint plus order-encoding units, one division"):

     For a pruning that tightens variable [j] (all other terms i <> j untouched), the
     explanation is

       Cut (Trivial, Linear (units, units_rhs), 1, 1)

     where:
       - [Trivial] stands for the model's own constraint row, sum_i a_i x_i <= c.
       - [units] is, for every i <> j with a_i <> 0, the pair (a_i, B_i) where
           B_i = Lit.ge (name x_i) lo(x_i)   if a_i > 0   (* x_i is at least its lo *)
           B_i = Lit.le (name x_i) hi(x_i)   if a_i < 0   (* x_i is at most its hi *)
         i.e. exactly the order-encoding unit literal that witnesses the bound used to
         compute that term's minimum, with the same coefficient it has in the model
         constraint.
       - [units_rhs] = sum_{i<>j} a_i * (that bound value), i.e. exactly the numeric value
         subtracted from [c] to get [slack] (each B_i is trivially true at the moment of
         the pruning, by construction, so this row is a tautological restatement, not an
         additional fact to prove).

     Adding [Trivial] (sum_i a_i x_i <= c) to [units] (sum_{i<>j} a_i x_i >= units_rhs,
     the "true because B_i holds" restatement) cancels every term but [j]'s and leaves
     exactly `a_j * x_j <= c - units_rhs`, which is `a_j * x_j <= max_j` above. Justify is
     expected to finish the derivation with the "one division": divide by |a_j| (floor for
     a_j > 0, the sign-flipping ceil division for a_j < 0) to land on the single pushed
     unit literal. This module does not perform that division itself - it hands over the
     undivided combination, which is exactly the shape the PROOF-FORMAT table promises.

     A [Conflict] (slack < 0) uses the same shape but over *all* terms (there is no
     excluded [j]): [Cut (Trivial, Linear (units, units_rhs), 1, 1)] then states
     `0 <= c - units_rhs < 0`, a direct numeric contradiction - no division needed. *)

module Lit = Baguette_proof.Lit

(* One term of the sum: coefficient (may be negative or zero; zero terms are inert and
   never generate a bound or appear in an explanation) and the variable it multiplies. *)
type term = int * Var.t
type t = { terms : term list; rhs : int }

let name = "int_lin_le"
let consistency = Propagator.Bounds
let make terms rhs = { terms; rhs }
let vars t = List.map snd t.terms

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
let term_min store (a, x) =
  let d = Store.get store x in
  if a >= 0 then a * Domain.lo d else a * Domain.hi d

(* The order-encoding unit literal witnessing that minimum, and the bound value it
   names - [snapshot] below copies both out of the store immediately, since the
   explanation that eventually uses them must describe the state *at pruning time*,
   not whatever the store looks like when the reason is finally forced. *)
let snapshot store terms =
  List.filter_map
    (fun (a, x) ->
      if a = 0 then None
      else
        let d = Store.get store x in
        let nm = Store.name store x in
        let bv = if a >= 0 then Domain.lo d else Domain.hi d in
        Some (a, nm, bv))
    terms

(* Turn a snapshot into the [Linear] half of the explanation: sum a_i * B_i >= rhs,
   where each B_i is the literal for the bound value captured at snapshot time. This is
   the part of the construction that is worth deferring - it allocates a [Lit.t] (and
   sanitises a name) per term - so callers only run it inside [Explanation.deferred]. *)
let linear_of_snapshot snap =
  let lits =
    List.map
      (fun (a, nm, bv) -> if a >= 0 then (a, Lit.ge nm bv) else (a, Lit.le nm bv))
      snap
  in
  let rhs = List.fold_left (fun acc (a, _, bv) -> acc + (a * bv)) 0 snap in
  Explanation.linear lits rhs

(* Explanation for tightening the bound of the variable excluded from [others] (or, for
   a conflict, [others] is every term). Cheap eagerly (an int/string snapshot); the
   [Lit.t] construction is deferred, per docs/ARCHITECTURE.md "Deferred explanations". *)
let explain store others =
  let snap = snapshot store others in
  Explanation.deferred (fun () ->
      Explanation.cut Explanation.trivial (linear_of_snapshot snap) 1 1)

(* All terms except the one for [x] (by physical position, not just value - a variable
   could in principle appear twice; each occurrence is excluded independently is not
   needed here since we exclude by identity of the term pushing, i.e. we build [others]
   once per iteration from the full list minus the current index). *)
let others_except terms idx =
  List.filteri (fun i _ -> i <> idx) terms

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
      (fun idx ((a, x), m) ->
        if !conflict = None && a <> 0 then begin
          let max_term = m + slack in
          let d = Store.get store x in
          if a > 0 then begin
            let new_hi = floordiv max_term a in
            if new_hi < Domain.hi d then begin
              let expl = explain store (others_except t.terms idx) in
              match Store.set_hi store x new_hi expl with
              | Store.Conflict e -> conflict := Some e
              | Store.Changed | Store.Unchanged -> ()
            end
          end
          else begin
            let new_lo = ceildiv max_term a in
            if new_lo > Domain.lo d then begin
              let expl = explain store (others_except t.terms idx) in
              match Store.set_lo store x new_lo expl with
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
