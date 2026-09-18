(* reduce.ml: REDUCTION as a named, swappable component (M2-L5, D-0044).

   Consistency level: none -- this is not a propagator. Spec section: none yet; the
   governing record is docs/DECISIONS.md D-0044 and its 2026-09-18 amendment.

   ---------------------------------------------------------------------------
   What reduction is, and why it is a component rather than a function
   ---------------------------------------------------------------------------

   PB conflict analysis resolves a conflicting row against the REASON row of one of its
   literals. Unlike clause resolution, adding two PB rows does not in general keep the
   result conflicting: the resolvent's slack can go non-negative and the analysis then
   has nothing left to learn from. The fix, from RoundingSat on, is to REDUCE the reason
   first -- derive from it a weaker-but-conflicting-preserving row in which the resolved
   literal has coefficient 1 -- and then resolve.

   D-0044 decided that this step is a named, swappable component and not code inlined
   into the analysis, because the upgrade path is known in advance and is a sequence of
   DOMINANCE results, not benchmark wins: division beats saturation (Elffers &
   Nordström, IJCAI 2018), [round_to_one] beats division, and Lomis et al. (SAT 2025)
   give two further rules at least as strong again. Whoever plugs the next one in should
   not have to touch lib/core/analysis.ml to do it.

   The shape follows lib/core/analysis.ml's [criterion] (M2-L2): a record carrying its
   own [postcondition], with the instances collected in [reductions]. That is deliberate
   and for the same reason -- see "Each reduction carries its own postcondition" below.

   ---------------------------------------------------------------------------
   The two rules, stated exactly
   ---------------------------------------------------------------------------

   Both take a reason row [C = sum a_i l_i >= b], a PIVOT literal [p] of that row (the
   literal the analysis is resolving on -- in a reason, the literal the row propagated),
   and the set of literals FALSIFIED by the assignment as of the propagation. Write
   [d = a_p] for the pivot's coefficient.

     [division]      weaken away EVERY non-falsified literal except the pivot, then
                     divide by [d], rounding up.
     [round_to_one]  weaken away only those non-falsified literals, other than the
                     pivot, whose coefficient is NOT divisible by [d]; then divide by
                     [d], rounding up.

   [round_to_one] weakens a subset of what [division] weakens, so its result is at least
   as strong, and strictly stronger whenever a non-falsified literal's coefficient
   happens to be a multiple of [d]. Worked case, which is test (a):

     C = 3v + 3u + 1w >= 5,  pivot v (d = 3),  u and w not falsified

       division      weakens u and w:  3v >= 1          / 3  ->  v >= 1
       round_to_one  weakens only w:   3v + 3u >= 4     / 3  ->  v + u >= 2

   and [v + u >= 2] is strictly stronger than [v >= 1] over 0-1 variables.

   WHY WEAKENING A NON-FALSIFIED LITERAL IS FREE, which is the whole trick: slack is
   [sum over the NON-falsified terms of a_i, minus b]. Dropping a non-falsified term
   removes [a] from the sum and [a] from the degree, so the slack is unchanged. Dropping
   a FALSIFIED one would remove [a] from the degree only and raise the slack by [a],
   which is how a reduction loses the conflict. Hence: never weaken a falsified literal,
   and never weaken the pivot.

   ---------------------------------------------------------------------------
   Each reduction carries its own postcondition
   ---------------------------------------------------------------------------

   D-0044's amendment made this point for M2-L2's stopping criterion and it applies here
   unchanged: a guarantee that happens to hold for the rule we implemented first is not a
   property of the TYPE. What both rules here do guarantee is the conflicting invariant --
   the reduced row still propagates the pivot, equivalently still has negative slack once
   the pivot is falsified (these are the same statement; see [propagates]) -- and, for a
   reason that genuinely propagated, slack EXACTLY ZERO with the pivot at coefficient 1.
   That is D-0044's "divide so the reduced reason has slack zero".

   What is NOT shared is how much they keep. [division]'s reduced row mentions nothing
   but the pivot and falsified literals; [round_to_one]'s keeps every non-falsified
   literal whose coefficient is a multiple of the divisor. Each states its own half, so a
   future rule -- saturation (M2-L7), MIR, Lomis et al. -- can state something else
   without a test asserting [round_to_one]'s guarantee about it.

   ---------------------------------------------------------------------------
   How M2-L7 plugs saturation in without touching the analysis
   ---------------------------------------------------------------------------

   [outcome] carries [derive], a function from the explanation that derives the ORIGINAL
   row to the explanation that derives the REDUCED one. Both rules here build the same
   shape, [Combine ([Term (1, e); Weaken ws], d)] -- D-0044's table read off the ADT --
   but nothing in the type says so. Saturation's outcome is [weakened = []],
   [divisor = 1] and [derive = fun e -> Saturate e] once that constructor exists, and it
   is then just another value in [reductions]. No signature moves and lib/core/analysis.ml
   never learns which rule it is holding.

   NOTHING HERE ADDS A CONSTRUCTOR TO lib/core/explanation.ml, and M2-L5 did not need
   one. That is D-0044's table, confirmed against the code: [Weaken lits] followed by
   [Combine (summands, divisor)] says both rules exactly.

   ---------------------------------------------------------------------------
   [falsified] is a predicate, deliberately, and this module reads no store
   ---------------------------------------------------------------------------

   [view] is shown the row, the pivot and a PREDICATE, and nothing else -- the same line
   lib/core/analysis.ml's [view] draws for the same reason. A reduction that could reach
   the store could read live state and render a derivation as of now rather than as of
   the moment of the propagation, which is the wrong side of I-X6. The caller (M2-L6)
   owns freezing that predicate; this module cannot un-freeze it.

   The predicate must be consistent: [falsified l] and [falsified (Lit.negate l)] must
   not both be true. Nothing here checks that -- it is a question about an assignment,
   which is exactly what this module is not shown. *)

module Lit = Baguette_proof.Lit

(* ------------------------------------------------------------------- slack *)

(* Slack of [row] under [falsified]: the sum of the coefficients of the terms that are
   NOT falsified, minus the degree. Negative slack is a conflict; a row propagates a
   literal whose coefficient exceeds the slack.

   [Checked] is used because a reduced row's degree is a difference of sums of
   coefficients and M1-T23's cap is what keeps that from wrapping silently. *)
let slack (row : Learned.t) ~(falsified : Lit.t -> bool) : int =
  let sum =
    List.fold_left
      (fun acc (tm : Learned.term) ->
        if falsified tm.lit then acc else Checked.add acc tm.coeff)
      0 (Learned.terms row)
  in
  Checked.sub sum (Learned.degree row)

let coeff_of (row : Learned.t) (l : Lit.t) : int option =
  List.find_map
    (fun (tm : Learned.term) -> if Lit.equal tm.lit l then Some tm.coeff else None)
    (Learned.terms row)

(* Does [row] propagate [pivot] under [falsified]?

   The textbook condition is [slack < coeff pivot] with the pivot unassigned, hence not
   falsified. Note that it is the SAME statement as "the row is conflicting once the
   pivot is falsified": falsifying the pivot removes its coefficient from the slack sum,
   so the post-slack is [slack - coeff pivot], and that is negative exactly when the
   condition holds. M2-L5's test (b) asks for both halves; they are one fact, and it is
   written down here rather than left for a reader to rediscover. *)
let propagates (row : Learned.t) ~(pivot : Lit.t) ~(falsified : Lit.t -> bool) : bool =
  (not (falsified pivot))
  && match coeff_of row pivot with None -> false | Some c -> slack row ~falsified < c

(* The slack of [row] on the conflict side, i.e. once [pivot] is falsified too. *)
let slack_with_pivot_falsified (row : Learned.t) ~(pivot : Lit.t)
    ~(falsified : Lit.t -> bool) : int =
  slack row ~falsified:(fun l -> falsified l || Lit.equal l pivot)

(* --------------------------------------------------------------- the component *)

(* What a reduction is shown. The row, the literal to resolve on, and whether a literal
   is falsified -- see the module header on why there is no store here. *)
type view = { row : Learned.t; pivot : Lit.t; falsified : Lit.t -> bool }

(* What it produces.

   [reduced] is the row as data, for the analysis and for tests. [weakened] and [divisor]
   are the same step read as arithmetic: [weakened] is the list of LITERAL AXIOMS to add,
   already in the [(coefficient, literal)] form [Explanation.Weaken] wants, which means
   each entry is the NEGATION of the literal being weakened away (adding [a * ~l] to a
   row carrying [a * l] replaces the term by the constant [a]). [derive] is the proof
   step -- see the module header on why it is a function and not a description. *)
type outcome = {
  reduced : Learned.t;
  weakened : (int * Lit.t) list;
  divisor : int;
  derive : Explanation.t -> Explanation.t;
}

(* A named reduction. [reduce] answers [None] when the rule does not apply at all (the
   pivot is not a literal of the row, or it is falsified, so there is nothing to resolve
   on). [postcondition] is what THIS rule guarantees about its own output -- it is not a
   property of [outcome]; see the module header. *)
type t = {
  name : string;
  reduce : view -> outcome option;
  postcondition : view -> outcome -> bool;
}

(* ------------------------------------------------------------------ the rules *)

(* The derivation both rules build: add the literal axioms, then divide. Skipped
   entirely when there is nothing to do -- [Explanation.combine] refuses an empty
   [Weaken] summand, and a [Combine] of one term divided by 1 is a [pol] line that
   restates its operand, which is a line docs/PROOF-FORMAT.md section 2 would rather not
   see written. *)
let derivation ~weakened ~divisor (e : Explanation.t) : Explanation.t =
  match (weakened, divisor) with
  | [], 1 -> e
  | [], _ -> Explanation.combine [ Explanation.term 1 e ] divisor
  | ws, _ -> Explanation.combine [ Explanation.term 1 e; Explanation.weaken ws ] divisor

(* [reduce_by ~keep v] is the shared body: weaken away every non-falsified literal other
   than the pivot for which [keep] says no, then divide by the pivot's coefficient. The
   two rules differ in [keep] and in nothing else. *)
let reduce_by ~(keep : divisor:int -> int -> bool) (v : view) : outcome option =
  if v.falsified v.pivot then None
  else
    match coeff_of v.row v.pivot with
    | None -> None
    | Some divisor ->
        let drop, kept =
          List.partition
            (fun (tm : Learned.term) ->
              (not (Lit.equal tm.lit v.pivot))
              && (not (v.falsified tm.lit))
              && not (keep ~divisor tm.coeff))
            (Learned.terms v.row)
        in
        (* Weakening [a * l] away is adding [a * axiom(~l)]: the term becomes the
           constant [a], so the degree drops by [a]. *)
        let weakened =
          List.map (fun (tm : Learned.term) -> (tm.coeff, Lit.negate tm.lit)) drop
        in
        let degree =
          List.fold_left
            (fun acc (tm : Learned.term) -> Checked.sub acc tm.coeff)
            (Learned.degree v.row) drop
        in
        (* The division is Chvátal-Gomory: every coefficient and the degree rounded UP.
           A degree that has fallen to zero or below is a trivially true row, which is
           what a reduction of a row that was not propagating produces; it is returned
           rather than hidden, and the postcondition is what reports it. *)
        let up x = if x <= 0 then 0 else Checked.ceildiv x divisor in
        let reduced =
          Learned.make
            (List.map (fun (tm : Learned.term) -> (up tm.coeff, tm.lit)) kept)
            (up degree)
        in
        Some { reduced; weakened; divisor; derive = derivation ~weakened ~divisor }

(* The conflicting invariant, which is what both rules are for and what M2-L5's test (b)
   pins: the reduced row still propagates the pivot, its slack is exactly zero, and the
   pivot's coefficient is 1. Shared by both [postcondition]s below -- shared because both
   rules happen to guarantee it, not because the type does. *)
let conflicting_invariant (v : view) (o : outcome) : bool =
  propagates o.reduced ~pivot:v.pivot ~falsified:v.falsified
  && slack o.reduced ~falsified:v.falsified = 0
  && slack_with_pivot_falsified o.reduced ~pivot:v.pivot ~falsified:v.falsified < 0
  && coeff_of o.reduced v.pivot = Some 1

(* RoundingSat's basic reduction: weaken away everything that is not falsified and not
   the pivot, then divide by the pivot's coefficient. The reduced row mentions the pivot
   and falsified literals only, which is its own half of the postcondition. *)
let division : t =
  {
    name = "division";
    reduce = reduce_by ~keep:(fun ~divisor:_ _ -> false);
    postcondition =
      (fun v o ->
        conflicting_invariant v o
        && List.for_all
             (fun (tm : Learned.term) -> Lit.equal tm.lit v.pivot || v.falsified tm.lit)
             (Learned.terms o.reduced));
  }

(* RoundingSat's stronger reduction: weaken away only the non-falsified literals the
   division would round, i.e. those whose coefficient is not a multiple of the divisor.
   Its own half of the postcondition is that it keeps what [division] throws away --
   every non-falsified literal whose coefficient IS a multiple survives, at coefficient
   [a / d]. A test asserting that is a standing proof that [division]'s clause above is
   [division]'s and not the type's. *)
let round_to_one : t =
  {
    name = "roundToOne";
    reduce = reduce_by ~keep:(fun ~divisor a -> a mod divisor = 0);
    postcondition =
      (fun v o ->
        conflicting_invariant v o
        && List.for_all
             (fun (tm : Learned.term) ->
               Lit.equal tm.lit v.pivot || v.falsified tm.lit
               || tm.coeff mod o.divisor <> 0
               || coeff_of o.reduced tm.lit = Some (tm.coeff / o.divisor))
             (Learned.terms v.row));
  }

(* Every reduction this solver has, in the order D-0044 ranks them. M2-L7 appends
   saturation here and nothing else changes. *)
let reductions : t list = [ division; round_to_one ]

let find (name : string) : t option =
  List.find_opt (fun r -> String.equal r.name name) reductions

(* [postcondition_holds r v o] is [r]'s own guarantee, asked by name rather than by a
   caller reaching into the record -- the same courtesy lib/core/analysis.ml extends. *)
let postcondition_holds (r : t) (v : view) (o : outcome) : bool = r.postcondition v o

let outcome_to_string (o : outcome) : string =
  Printf.sprintf "%s  [weakened %s, / %d]" (Learned.to_string o.reduced)
    (if o.weakened = [] then "nothing"
     else
       String.concat " "
         (List.map (fun (c, l) -> Printf.sprintf "%d*%s" c (Lit.to_string l)) o.weakened))
    o.divisor
