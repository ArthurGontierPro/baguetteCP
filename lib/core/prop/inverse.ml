(* inverse(f, g): f and g are mutually inverse functions, f[i] = j <-> g[j] = i, every
   value of f in g's index set and every value of g in f's. Reaches the solver as
   `baguette_inverse(f, fmin, g, gmin)` through mznlib/fzn_inverse.mzn (the two offsets
   carry the index sets, FlatZinc arrays being 1-based).

   Consistency level: CHECKING ([consistency] below), with arc consistency on every
   channel pair as what one call actually achieves (section "Consistency level" below).
   Governed by docs/SPEC.md 3.2 (consistency levels) and 3.3 (explanations). Proof shape:
   every pruning is one `rup` against one pair of channel rows, so the family is
   [Single_row] in the I-X10 classification table of test/unit/test_trace.ml (a pruning
   that follows from one model constraint, whose trace line is RUP with nothing derived
   ahead of it).

   Design record: docs/DECISIONS.md D-0146 section 7, the model rows and both stages
   written and probed on the checker before any code. Implementation: D-0151 section 2,
   which built the two stages below (channel filtering here, then all_different over each
   array from cited root lemmas).

   ---------------------------------------------------------------------------
   The .opb rows: std's semantics as CHANNEL clauses, no auxiliary
   ---------------------------------------------------------------------------

   lib/flatzinc/compile.ml's [post_inverse] writes, for every i of f's index set and j of
   g's with j a declared value of f_i (else the row is the constant true), both halves of
   "f_i = j -> g_j = i" and of its mirror, over the ORDER literals:

     CH(i, j)    f_i <> j \/ g_j >= i        f_i <> j \/ g_j <= i
     CH'(j, i)   g_j <> i \/ f_i >= j        g_j <> i \/ f_i <= j

   with every constant half dropped at a declared bound, plus a unit row `f_i >= gmin`
   (resp. `<= gmax`, and the same for g) when a declared domain reaches outside the other
   index set. That is std's fzn_inverse with its reifications removed: nothing in the
   .opb is a consequence the solver computed.

   ---------------------------------------------------------------------------
   Consistency level: CHECKING, and what the call actually achieves
   ---------------------------------------------------------------------------

   One call restricts every value to the other index set, then makes the two arrays agree
   pairwise: j in dom(f_i) <=> i in dom(g_j), both ways. That is arc consistency on each
   CHANNEL pair, which is not domain consistency of `inverse`, because f and g are
   permutations and a value set no matching can cover is only seen by all_different's
   counting. The tag is therefore [Checking], since with every variable fixed a pair that
   disagrees empties one of its two variables. The stronger claim belongs to the
   all_different instances compile.ml posts beside this one over f and over g (stage 2,
   below), which are [Domain] on their own account. After the two passes no pair
   disagrees, so a second call changes nothing (idempotence at the interface, I-P2).

   ---------------------------------------------------------------------------
   The proof: every pruning is ONE `rup`, its facts on its tail
   ---------------------------------------------------------------------------

   Removing i from g_j because j is not in dom(f_i): assume g_j = i and the facts that
   exclude j from f_i; CH'(j, i) pins f_i to j and the facts refute it. The facts are the
   WEAKEST bound that excludes j (f_i >= j+1 when j is below f_i's lower bound, f_i <= j-1
   above its upper one), or, for an interior hole, the facts of the entry that punched it.
   A hole is not a literal, so a reason that reads one cites its remover's facts instead,
   and the remover's own trace line fires once those facts are assumed (the rule D-0075
   set after a reason that read a hole but stated only bounds was refused; element.ml and
   regular.ml do the same). When i is a BOUND of g_j the claim is the settled bound, so
   the tail also carries the bound fact that pins g_j to i. Measured before the module
   existed (D-0146 section 7.2, bench/regular_spike/probe_inverse.sh): a bound prune under
   a fact and an interior hole verify, a prune the facts do not support is refused at the
   RUP wording.

   ORDER ON THE TAIL: the pinning bound facts first, the excluding facts LAST, so
   test/unit/test_mutation.ml's lane that drops a line's last literal drops the fact the
   whole argument rests on.

   The justification is [Explanation.clause] of the claim and the negated facts, that is
   the trace line itself, deferred. No new constructor and no [Store.deriving_ahead]:
   every line is RUP against one CH pair plus the lines already on the page. Emptying a
   variable is reported here, as a conflict on the facts of the pruning that would empty
   it plus the variable's own fixing, never by [Store.apply]'s failing arm, whose
   derivation would be the one pruning's and not the contradiction (the rule element.ml
   states for its empty index).

   ---------------------------------------------------------------------------
   Stage 2: all_different strength, from root lemmas (not in this module)
   ---------------------------------------------------------------------------

   Both arrays are permutations, so all_different(f) and all_different(g) are implied, and
   lib/core/prop/alldiff.ml over each gives the matching's pruning. Its derivations cite
   the pairwise rows `f_i <> j \/ f_k <> j`, which the .opb above does not state and must
   not (an implied row posted as a model row is a stronger model nothing checks). They are
   ROOT LEMMAS, `rup` from CH(i, j) and CH(k, j) at the start of the proof
   ([Encoding.add_cited_lemma]), and alldiff names their ids through its lemma-row hook
   ([?lemma_rows] of [Alldiff.make]). compile.ml posts that; this module does not know
   about it.

   The scan is O(|f| * |g|) per call over the live domains, and allocates only the reasons
   of the prunings it makes. *)

module Lit = Baguette_proof.Lit

(* One position of an array: a variable with its DECLARED bounds, or a constant the
   flattener left in the array. *)
type cell = Fixed of int | Cell of { var : Var.t; name : string; dlo : int; dhi : int }

type t = {
  f : cell array; (* f.(k) is f_(fmin + k); its values lie in g's index set *)
  fmin : int;
  g : cell array; (* g.(k) is g_(gmin + k) *)
  gmin : int;
  vars : Var.t list;
}

let make ~f ~fmin ~g ~gmin =
  let vars =
    List.sort_uniq Var.compare
      (List.filter_map
         (function Cell { var; _ } -> Some var | Fixed _ -> None)
         (Array.to_list f @ Array.to_list g))
  in
  { f; fmin; g; gmin; vars }

let vars t = t.vars
let name = "inverse"
let consistency = Propagator.Checking

exception Found of Store.conflict

(* The live domain of a cell, as lo, hi and a membership test. *)
let dom store = function
  | Fixed c -> (c, c, fun v -> v = c)
  | Cell { var; _ } ->
      let d = Store.get store var in
      (Domain.lo d, Domain.hi d, Domain.mem d)

(* The facts that exclude [v] from [c]'s live domain (the caller knows it is excluded):
   the weakest bound, or the remover of a hole. Nothing for a constant, whose other values
   are not literals. *)
let excl store c v =
  match c with
  | Fixed _ -> []
  | Cell { var; name; dlo; dhi } -> (
      let d = Store.get store var in
      if v < Domain.lo d then [ Reason.at_least ~name ~decl:dlo (v + 1) ]
      else if v > Domain.hi d then [ Reason.at_most ~name ~decl:dhi (v - 1) ]
      else
        match Store.remover store ~before:(Store.trail_length store) ~var v with
        | None -> []
        | Some e -> Reason.facts e.Store.reason)

let clause_expl claim fs =
  Explanation.deferred (fun () ->
      Explanation.clause (claim @ List.map Lit.negate (Reason.lits_of_facts fs)))

let conflict store fs =
  Store.conflict store (Reason.because ~concludes:None fs (clause_expl [] fs))

(* What removing [v] from [d] concludes: the settled bound when [v] is a bound
   (lib/core/prop/ne.ml's [removal_conclusion], the same walk), nothing for a hole. *)
let removal_conclusion ~name ~dlo ~dhi d v =
  if v = Domain.lo d then (
    let u = ref (v + 1) in
    while !u <= Domain.hi d && Domain.is_hole d !u do
      incr u
    done;
    Some (Reason.at_least ~name ~decl:dlo !u))
  else if v = Domain.hi d then (
    let u = ref (v - 1) in
    while !u >= Domain.lo d && Domain.is_hole d !u do
      decr u
    done;
    Some (Reason.at_most ~name ~decl:dhi !u))
  else None

(* Remove [v] from cell [c] on the facts [why] (the excluding facts). A constant equal to
   [v], or a variable fixed at [v], is a conflict on the same facts plus the fixing. *)
let remove store c v why =
  match c with
  | Fixed k -> if k = v then raise (Found (conflict store why))
  | Cell { var; name; dlo; dhi } ->
      let d = Store.get store var in
      if Domain.mem d v then (
        let pin =
          (if v = Domain.lo d && v > dlo then [ Reason.at_least ~name ~decl:dlo v ]
           else [])
          @
          if v = Domain.hi d && v < dhi then [ Reason.at_most ~name ~decl:dhi v ] else []
        in
        let fs = pin @ why in
        if Domain.is_fixed d then raise (Found (conflict store fs));
        let claim =
          (if v > dlo then [ Lit.negate (Lit.ge name v) ] else [])
          @ if v < dhi then [ Lit.ge name (v + 1) ] else []
        in
        match
          Store.remove store var v
            (Reason.because
               ~concludes:(removal_conclusion ~name ~dlo ~dhi d v)
               fs (clause_expl claim fs))
        with
        | Store.Conflict c -> raise (Found c)
        | Store.Changed | Store.Unchanged -> ())

(* Every value of [c] outside [first, last] (the other array's index set) goes, on no
   facts, because the unit rows compile.ml posts for a declared domain that reaches
   outside say so (and, for a constant outside, the empty row it posts). A live domain
   wholly outside is a conflict on the one bound fact that puts it there, against the same
   unit row. *)
let restrict store c ~first ~last =
  match c with
  | Fixed k -> if k < first || k > last then raise (Found (conflict store []))
  | Cell { var; name; dlo; dhi } ->
      let move r =
        match r with
        | Store.Conflict c -> raise (Found c)
        | Store.Changed | Store.Unchanged -> ()
      in
      let d = Store.get store var in
      if Domain.hi d < first then
        raise (Found (conflict store [ Reason.at_most ~name ~decl:dhi (Domain.hi d) ]));
      if Domain.lo d > last then
        raise (Found (conflict store [ Reason.at_least ~name ~decl:dlo (Domain.lo d) ]));
      (if Domain.lo d < first then
         let concl = Reason.at_least ~name ~decl:dlo first in
         move
           (Store.set_lo store var first
              (Reason.because ~concludes:(Some concl) []
                 (clause_expl (Option.to_list (Reason.lit_of_fact concl)) []))));
      let d = Store.get store var in
      if Domain.hi d > last then
        let concl = Reason.at_most ~name ~decl:dhi last in
        move
          (Store.set_hi store var last
             (Reason.because ~concludes:(Some concl) []
                (clause_expl (Option.to_list (Reason.lit_of_fact concl)) [])))

(* One direction of the channel: for every a_i and every index j of b, j not in dom(a_i)
   removes i from b_j. *)
let channel store ~a ~amin ~b ~bmin =
  Array.iteri
    (fun ka ca ->
      let i = amin + ka in
      let _, _, mem = dom store ca in
      Array.iteri
        (fun kb cb ->
          let j = bmin + kb in
          if not (mem j) then
            let _, _, memb = dom store cb in
            if memb i then remove store cb i (excl store ca j))
        b)
    a

let propagate t store =
  try
    let nf = Array.length t.f and ng = Array.length t.g in
    Array.iter (restrict store ~first:t.gmin ~last:(t.gmin + ng - 1)) t.f;
    Array.iter (restrict store ~first:t.fmin ~last:(t.fmin + nf - 1)) t.g;
    channel store ~a:t.f ~amin:t.fmin ~b:t.g ~bmin:t.gmin;
    channel store ~a:t.g ~amin:t.gmin ~b:t.f ~bmin:t.fmin;
    Propagator.Fixpoint
  with Found c -> Propagator.Conflict c
