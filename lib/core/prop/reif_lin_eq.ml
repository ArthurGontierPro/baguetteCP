(* int_eq_reif:  b <-> (sum_i a_i x_i = rhs),  and int_ne_reif, which is the same
   author with the reification literal inverted.

   Consistency level: VALUE (docs/SPEC.md 3.2), and the label is chosen the way
   lib/core/prop/ne.ml chooses its own -- as the weaker of the two claims this
   propagator's pieces actually make, because SPEC 3.2 makes the declared level the
   bound on what an explanation may claim:

     - enforce-hold is BOUNDS consistent on `sum = rhs`: it is two [Linear] passes,
       one per direction of the equality, and neither punches a hole.
     - enforce-not-hold is the textbook disequality pass, which removes a VALUE from
       the last unfixed term and is therefore not a bounds-only propagator.

   Declaring VALUE is conservative in the only direction that matters, exactly as
   [Ne]'s header argues for the unreified case. (docs/GLOSSARY.md defines "bounds" and
   "domain" consistent but not "value"; reported there, not invented here.)

   ---------------------------------------------------------------------------
   Why an equality is four rows and not two -- and why there is no `p /\ q`
   ---------------------------------------------------------------------------

   D-0053 records that `b <-> (sum = c)` is NOT one reified inequality: it needs
   `p <-> (sum<=c)`, `q <-> (sum>=c)` and `b <-> p /\ q`, and it leaves open where [p]
   and [q] should live. **This module builds neither.** The four rows
   lib/proof/encoding.ml's [add_int_lin_eq_reif] posts are

     LE   sum a x <= c        }  guarded so they say nothing unless the reification
     GE  -sum a x <= -c       }  literal is TRUE
     A    sum a x <= c - 1 + big_a * ne_aux   }  guarded so they say nothing unless it
     B   -sum a x <= -c - 1 + big_b * ~ne_aux }  is FALSE

   and A/B are [Encoding.expand_int_lin_ne]'s own pair -- the PB encoding of
   `sum <> c` that lib/core/prop/ne.ml has been explaining against since M1-T9 --
   with one extra guard term. The conjunction's whole purpose was the direction
   `(sum = c) -> b`; A and B are its contrapositive `~b -> (sum <> c)` already written
   as rows, so the decomposition buys nothing that is not already in the .opb.

   It also is not reachable as stated. [p] and [q] would have to be propagated, so they
   would have to be *store* variables and not merely .opb names; bin/main.ml's
   [assignment_values] fails on any solver variable outside the model's own, so
   introducing one is a change on the far side of that bridge and not a change here.
   The auxiliary A and B share is an ordinary .opb-only Boolean, the same kind
   [add_int_lin_ne] has always minted, and nothing propagates over it.

   ---------------------------------------------------------------------------
   The three author pieces (roadmap M3-T4)
   ---------------------------------------------------------------------------

     enforce-hold      [Linear] over LE, then [Linear] over GE. With the reification
                       literal true both guards vanish and the pair is an ordinary
                       `sum = c` at bounds consistency, the [Lin_eq] shape (D-0011:
                       two rows, two instances, each citing its own).
     enforce-not-hold  the disequality pass below. Its explanations are [Clause]s --
                       nogoods that name the reifier's own literal alongside the fixed
                       values -- and they are RUP against A and B, which is what makes
                       the guard sound to state: negate the clause and the guards are
                       off, leaving exactly the pair [Ne] already refutes against.
     entailment        LE and GE again. With the literal open neither can move a
                       condition variable and each can push the reifier to FALSE,
                       between them covering "the domains refute `sum = c`" from both
                       sides. The other half, "the domains ENTAIL it", is not a bounds
                       fact at all -- it needs every term fixed -- so it is
                       [entail_equal] below, and its justification is again a [Clause]
                       RUP against A and B.

   The dispatcher (lib/core/prop/reif.ml) supplies the collapse and the contrapositive
   over those three, and [~positive] supplies `int_ne_reif`: the condition this author
   describes is always `sum = c`, and `int_ne_reif` is that condition holding when the
   model's bool is FALSE. Not one line below tests which builtin it is serving.

   Shape, arithmetic and snapshot discipline follow lib/core/prop/ne.ml, which is this
   module's unreified twin: compute once, snapshot the decision eagerly, build the
   literals behind [Explanation.deferred], every product through [Checked]. *)

module Encoding = Baguette_proof.Encoding

(* A term of the condition, with its DECLARED domain frozen at [make] time -- D-0010,
   the same freeze [Linear.make] and [Ne.make] perform and for the same reason: a
   nogood literal is stated relative to the declared bound. *)
type term = { coeff : int; x : Var.t; name : string; decl_lo : int; decl_hi : int }

type payload = {
  p_terms : term list;
  p_rhs : int;
  p_b : Var.t;
  p_bname : string;
  p_wrong : int;
      (* The reifier's value at which `sum = rhs` is FALSE: 0 for int_eq_reif, 1 for
         int_ne_reif. The nogoods below name this value, because a nogood that did not
         mention the reifier would be claiming the disequality unconditionally -- which
         is the I-P5 failure [Ne] shipped between M1-T9 and M1-T17, one level up. *)
}

type t = Reif.t

let consistency = Propagator.Value

(* ------------------------------------------------------------------ explanations *)

(* "not all of these variables take these values while the reifier sits at the value
   that denies the equality". A [Clause], hence a [rup] (D-0026: the justification is
   whatever convinces the checker, and for a self-contained nogood that is unit
   propagation), and RUP against the guarded A/B pair. [pairs] must be a snapshot. *)
let nogood p pairs =
  Explanation.clause
    (List.concat_map
       (fun (tm, v) ->
         Encoding.ne_clause_lits ~name:tm.name ~decl_lo:tm.decl_lo ~decl_hi:tm.decl_hi v)
       pairs
    @ Encoding.ne_clause_lits ~name:p.p_bname ~decl_lo:0 ~decl_hi:1 p.p_wrong)

let explain p pairs = Explanation.deferred (fun () -> nogood p pairs)

(* The reifier's own contribution to the reason half (D-0018 point 3 / D-0026): it is
   fixed at the value the nogood names, so the trace line's tail carries it too. Over a
   bool one of the two halves is always the declared bound and drops at
   [Reason.lit_of_fact], leaving exactly the literal the clause above spends. *)
let reifier_fact p = Reason.fixed_at ~name:p.p_bname ~decl_lo:0 ~decl_hi:1 p.p_wrong

let fixed_facts others =
  List.concat_map
    (fun (o, v) -> Reason.fixed_at ~name:o.name ~decl_lo:o.decl_lo ~decl_hi:o.decl_hi v)
    others

(* The bound a value removal is about to move, and only that one -- [Ne]'s
   [moved_bound_fact], verbatim in shape: stating the other side would state something
   false, and would duplicate the claim's own literal in the clause. *)
let moved_bound_fact tm w d =
  if w = Domain.lo d then [ Reason.at_least ~name:tm.name ~decl:tm.decl_lo w ]
  else if w = Domain.hi d then [ Reason.at_most ~name:tm.name ~decl:tm.decl_hi w ]
  else []

(* [Ne.removal_conclusion], verbatim in shape (D-0043): a removal at a bound concludes
   the bound it settled to, an interior removal concludes nothing a [Reason.fact] can
   state. The walk over holes is the one [Trace] does, so the number stated here and
   the number the trace line claims come from one rule. *)
let removal_conclusion tm w d =
  if w = Domain.lo d then (
    let v = ref (w + 1) in
    while !v <= Domain.hi d && Domain.is_hole d !v do
      incr v
    done;
    Some (Reason.at_least ~name:tm.name ~decl:tm.decl_lo !v))
  else if w = Domain.hi d then (
    let v = ref (w - 1) in
    while !v >= Domain.lo d && Domain.is_hole d !v do
      decr v
    done;
    Some (Reason.at_most ~name:tm.name ~decl:tm.decl_hi !v))
  else None

(* ------------------------------------------------------------------- the pieces *)

let fixed_at store tm = Domain.value (Store.get store tm.x)
let value_of store tm = Domain.lo (Store.get store tm.x)
let all_pairs store terms = List.map (fun tm -> (tm, value_of store tm)) terms

let sum_of store terms =
  List.fold_left
    (fun acc tm -> Checked.add acc (Checked.mul tm.coeff (value_of store tm)))
    0 terms

let others_except terms idx = List.filteri (fun i _ -> i <> idx) terms

let unfixed_positions store terms ~limit =
  let rec go i acc = function
    | [] -> List.rev acc
    | tm :: rest ->
        if List.length acc >= limit then List.rev acc
        else if Option.is_none (fixed_at store tm) then go (i + 1) (i :: acc) rest
        else go (i + 1) acc rest
  in
  go 0 [] terms

(* enforce-not-hold: `sum a x <> rhs` is in force. Identical in structure to
   [Ne.propagate]; every explanation additionally names the reifier. *)
let not_hold p store =
  match unfixed_positions store p.p_terms ~limit:2 with
  | _ :: _ :: _ -> Propagator.Fixpoint
  | [] ->
      if sum_of store p.p_terms <> p.p_rhs then Propagator.Fixpoint
      else
        (* [Ne]'s unreified conflict records NO facts, and can: with everything fixed
           it is unconditional, so [Trace.conflict_line] writes no line and the clause
           is the whole story. Here it is conditional -- on the reifier -- so a line IS
           written, and then every premise has to be on it. Stating only the reifier's
           fact was this module's first version and test/models/reif_eq_branch_unsat.fzn
           is what caught it: the line came out as `rup ~b_ge_1 >= 1`, which is TRUE of
           the model and not reverse-unit-propagable from it, and veripb said so. *)
        let pairs = all_pairs store p.p_terms in
        Propagator.Conflict
          (Store.conflict store
             (Reason.because ~concludes:None
                (reifier_fact p @ fixed_facts pairs)
                (explain p pairs)))
  | [ idx ] -> (
      let tm = List.nth p.p_terms idx in
      let others = others_except p.p_terms idx in
      let rest = Checked.sub p.p_rhs (sum_of store others) in
      if Checked.rem rest tm.coeff <> 0 then Propagator.Fixpoint
      else
        let w = Checked.floordiv rest tm.coeff in
        let d = Store.get store tm.x in
        if not (Domain.mem d w) then Propagator.Fixpoint
        else
          let fixed_others = List.map (fun o -> (o, value_of store o)) others in
          let j =
            Reason.because
              ~concludes:(removal_conclusion tm w d)
              (moved_bound_fact tm w d @ fixed_facts fixed_others @ reifier_fact p)
              (explain p ((tm, w) :: fixed_others))
          in
          match Store.remove store tm.x w j with
          | Store.Conflict e -> Propagator.Conflict e
          | Store.Changed | Store.Unchanged -> Propagator.Fixpoint)

(* The other half of entailment: the domains ENTAIL `sum = rhs`, which over integers
   means every term is fixed and the total lands on [rhs]. Push the reification literal
   true -- i.e. move the reifier off [p_wrong] -- on the nogood that says the two
   cannot both hold.

   This is the piece the `<=` author (lib/core/prop/reif_lin_le.ml) does not need and
   D-0053 said the conjunction channelling would be needed for. It is not: the claim is
   RUP against the guarded A/B pair, which is already in the .opb. *)
let entail_equal p store =
  match unfixed_positions store p.p_terms ~limit:1 with
  | _ :: _ -> Propagator.Fixpoint
  | [] ->
      if sum_of store p.p_terms <> p.p_rhs then Propagator.Fixpoint
      else
        let pairs = all_pairs store p.p_terms in
        let right = 1 - p.p_wrong in
        let concludes =
          Some
            (if right = 1 then Reason.at_least ~name:p.p_bname ~decl:0 1
             else Reason.at_most ~name:p.p_bname ~decl:1 0)
        in
        let j =
          Reason.because ~concludes (fixed_facts pairs) (explain p pairs)
        in
        let r =
          if right = 1 then Store.set_lo store p.p_b 1 j
          else Store.set_hi store p.p_b 0 j
        in
        (match r with
        | Store.Conflict e -> Propagator.Conflict e
        | Store.Changed | Store.Unchanged -> Propagator.Fixpoint)

(* ----------------------------------------------------------------------- make *)

(* [terms] is the condition `sum a_i x_i = rhs`; [reifier] is not among them.
   [positive] is [true] for `int_eq_reif` and [false] for `int_ne_reif`. The four ids
   and two big-Ms come from [Encoding.add_int_lin_eq_reif], which posted the rows; only
   LE and GE are cited, so only their ids are taken.

   Zero-coefficient terms are dropped for the disequality pieces, exactly as [Ne.make]
   drops them: a term that is not part of the constraint must not count towards "how
   many terms are unfixed". They are kept in the [Linear] rows, which skip them
   themselves and must be given the row's own term list unchanged (M2-L6). *)
let make ~le_id ~ge_id ~k_le ~k_ge ~positive store terms rhs ~reifier =
  let vac_eq = if positive then 0 else 1 in
  let guard k = if vac_eq = 1 then (Checked.neg k, 0) else (k, k) in
  let kl, dl = guard k_le and kg, dg = guard k_ge in
  let le =
    Linear.make ~row_id:le_id store (terms @ [ (kl, reifier) ]) (Checked.add rhs dl)
  in
  let ge =
    Linear.make ~row_id:ge_id store
      (List.map (fun (a, x) -> (Checked.neg a, x)) terms @ [ (kg, reifier) ])
      (Checked.add (Checked.neg rhs) dg)
  in
  let p =
    {
      p_terms =
        List.filter_map
          (fun (coeff, x) ->
            if coeff = 0 then None
            else
              let d = Store.get store x in
              Some
                {
                  coeff;
                  x;
                  name = Store.name store x;
                  decl_lo = Domain.lo d;
                  decl_hi = Domain.hi d;
                })
          terms;
      p_rhs = rhs;
      p_b = reifier;
      p_bname = Store.name store reifier;
      p_wrong = vac_eq;
    }
  in
  let rows store =
    match Linear.propagate le store with
    | Propagator.Conflict c -> Propagator.Conflict c
    | Propagator.Fixpoint -> Linear.propagate ge store
  in
  let entail store =
    match rows store with
    | Propagator.Conflict c -> Propagator.Conflict c
    | Propagator.Fixpoint -> entail_equal p store
  in
  Reif.make ~reifier ~positive
    ~vars:(List.map snd terms)
    ~hold:rows ~not_hold:(not_hold p) ~entail store

let vars = Reif.vars
let propagate = Reif.propagate

module Int_eq_reif = struct
  type nonrec t = t

  let name = "int_eq_reif"
  let consistency = consistency
  let vars = vars
  let propagate = propagate
end

module Int_ne_reif = struct
  type nonrec t = t

  let name = "int_ne_reif"
  let consistency = consistency
  let vars = vars
  let propagate = propagate
end
