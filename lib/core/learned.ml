(* learned.ml: the LEARNED-CONSTRAINT type, its runtime instance, and its proof-side
   introduction and deletion (M2-L1).

   Consistency level: none of its own. A learned constraint does not get a propagator
   family -- see "The bet" below; it is instantiated as a [Linear] instance and prunes at
   [Linear]'s level (BOUNDS, docs/SPEC.md 3.2). Governing records: docs/DECISIONS.md
   D-0044 (the type) and D-0045's addendum (the proof-side lifetime).

   ---------------------------------------------------------------------------
   The type: sum a_i l_i >= b, over Lit.t
   ---------------------------------------------------------------------------

   D-0044 decided that the learned object is a pseudo-Boolean inequality and that a
   CLAUSE is its degree-1, unit-coefficient case rather than a separate type. That is
   what [t] below is, and [of_clause] is not a second constructor -- it is [make] with
   every coefficient 1 and degree 1.

   The argument D-0044 rests on is a property of our encoding: D-0028's order encoding is
   eager, so every atomic constraint x >= v already IS a 0-1 variable in the .opb, and a
   clause over order literals already IS the PB constraint sum l_i >= 1 over those same
   variables. Pumpkin's LLG has to mint an auxiliary variable per literal to cross from a
   clause to a linear inequality; we have nothing to cross.

   [make] normalises: a negative coefficient is absorbed by negating its literal
   (a*l = a + |a|*~l, so the degree grows by |a|), a zero coefficient is dropped, and
   repeated literals are merged. After [make] every coefficient is >= 1, which is the
   form [Opb] and the checker want and the form the reduction rules of M2-L5 assume.

   ---------------------------------------------------------------------------
   The bet -- AND M2-L13 COLLECTED IT THE OTHER WAY (D-0054)
   ---------------------------------------------------------------------------

   docs/ROADMAP.md M2-L1 bet that "a learned row is exactly what [Linear] already
   propagates -- no new propagator family if this holds". **The bet is LOST, deliberately,
   and losing it is M2-L13.** D-0054's reason is one sentence: a PB line for proof logging
   and a PB explanation for solving are different objects, and the conversion below
   decides whether a row may propagate by an ALGEBRAIC IDENTITY OVER THE DECLARED BOX --
   a proof-side test doing a solving-side job. What replaced it is
   lib/core/prop/pb.ml, a slack propagator over the order literals the row already names,
   instantiated by [pb_instance] at the bottom of this file; [Linear] is untouched and
   lib/core/prop/clause.ml is now that propagator's degree-1 face, so the family count
   went up by one and down by nothing.

   The section below is kept BECAUSE the boundary it states is still exactly right about
   [to_linear_row], which survives as the measured counter [Search.n_pb_converts]. Read it
   as a fact about that predicate, not as a description of how a learned row propagates:

     - In the PROOF, D-0044 is right without qualification: the order literals are real
       0-1 variables of the .opb and a [Learned.t] is written out by [to_opb] with no
       conversion and no auxiliary variable.
     - In the SOLVER'S STORE they are not variables at all. The store holds the model's
       integer variables; [x >= v] is a *question about a domain*, not a handle. So a
       runtime instance exists only where the PB row can be read back as a linear row
       over those integer variables, and [to_linear_row] below is exactly the predicate
       for that. It succeeds on:

         * a clause over `var bool`s -- D-0007 order-encodes a Boolean on [0, 1], so its
           ladder has ONE rung and [b >= 1] is the integer b itself. This is the D-0044
           check (test (b)): a degree-1 unit-coefficient [Learned.t] over Boolean order
           literals is the linear row `sum -b_i + sum y_j <= |y| - 1`, and [Linear] on it
           is unit propagation.
         * a model row's own expansion -- [Encoding.linear_terms_int_lin_le] gives every
           rung of a variable's ladder the SAME coefficient a_i, and a uniform run over
           the whole ladder is a_i * (x - lo_i). This is the round-trip (test (a)).
         * a single threshold that is outside the ladder, which is a constant.

       and it FAILS, returning [None], on a threshold strictly inside an integer
       variable's ladder: `[x >= 3]` for x declared 0..5 is not any linear function of x
       over that box, and neither is a sum of two such. There is no rounding of this: a
       1UIP cut over integer variables produces exactly those literals, so **M2-L3 must
       expect [None] from [to_linear_row] on its own output** and either restrict the cut
       to the shapes above or accept that the learned constraint is proof-only until a
       propagator for it exists. Recorded here rather than discovered there.

   Nothing in this module widens [Linear], and since M2-L13 nothing in it builds a
   [Linear.t] either.

   ---------------------------------------------------------------------------
   Why the [Linear.t] is built here instead of through [Linear.make]
   ---------------------------------------------------------------------------

   [Linear.make] reads each variable's domain out of the store at construction time and
   freezes it as the term's DECLARED domain -- its own header says this "has to happen
   before anything ... has narrowed it". A learned constraint is created in the middle of
   search, when domains have been narrowed, so [make] would freeze a narrow box as the
   declared one and every [Order_reason.weaken_declared] chain the instance later builds
   would be short of the ladder the .opb actually contains. The chain would then fail to
   cancel the row's coefficient and the `pol` would derive something other than the bound.

   So the declared bounds come from the ENCODING, which is where the ladder's width is
   defined ([Encoding.domain]), and the [Linear.t] record is built directly. That is a
   deliberate reach into another module's representation and it is confined to
   [to_linear] below. It is not a shortcut around [make]'s checks -- [make] has none
   beyond the freeze -- it is the freeze done against the right source.

   ---------------------------------------------------------------------------
   The proof side: level 0, or the backjump takes it -- D-0045's addendum
   ---------------------------------------------------------------------------

   MEASURED by M2-L1 before it was fixed, and it is exactly what D-0045 predicted:
   [Writer.fresh] tags every id with the writer's current level and [Writer.wipe_level l]
   deletes every id tagged at level >= l. A constraint derived at the conflict level is
   deleted by the backjump that follows, and citing it afterwards is "Trying to access
   constraint with ID 3 that has already been deleted".

   [introduce] therefore emits inside [Justify.with_level ctx 0], which moves the level
   FOR REAL -- the `% level 0` marker goes on the page -- rather than writing our own
   table, which would keep [t.tags] and the emitted proof disagreeing about where the id
   landed (invariant I-X3).

   The consequence for I-X2 is the one M2-L4 will own: a level-0 id is no longer retired
   by any backjump, so somebody must delete it explicitly. That somebody is [retire], and
   until the retention policy exists its caller is whoever called [introduce]. A learned
   constraint is the first object in this solver whose lifetime is not a search level's.

   ---------------------------------------------------------------------------
   Determinism (docs/ROADMAP.md M2-L1 test (e))
   ---------------------------------------------------------------------------

   Nothing in this module iterates a hash table, and no function here returns a list
   whose order depends on one. [make] sorts and merges through [Lit.compare]; the
   grouping in [to_linear_row] is done on a sorted list, not in a [Hashtbl]. The gate
   requires two runs of one binary to be byte-identical, and a learned database iterated
   in hash order is the specific way learning breaks it. There is no [Hashtbl] in this
   file; keep it that way. *)

module Lit = Baguette_proof.Lit
module Opb = Baguette_proof.Opb
module Writer = Baguette_proof.Writer
module Encoding = Baguette_proof.Encoding

(* One term: a strictly positive coefficient on a literal. [make] is the only way to get
   one, and it is what establishes the sign. *)
type term = { coeff : int; lit : Lit.t }

(* sum_i coeff_i * lit_i >= degree. *)
type t = { terms : term list; degree : int }

(* ------------------------------------------------------------------- construction *)

(* Normalise to positive coefficients and merge repeats.

   [a * l] with a < 0 becomes [|a| * ~l] with the degree raised by [|a|], since
   l = 1 - ~l. A zero coefficient contributes nothing at all -- not even to the degree --
   and is dropped, exactly as [Encoding.linear_terms_int_lin_le] drops a zero term.

   Repeated literals are summed. This is not tidying: [Opb.normalise] and the checkers
   both expect a literal to appear once, and a cut that resolves two reasons naming the
   same bound produces repeats by construction (M2-L2's output does), so the merge is on
   the path M2-L3 will take. Sorting by [Lit.compare] makes the result a function of the
   SET of terms and not of the order they were built in, which is test (e).

   M11-complexity-T9 (D-0157): [make_reference] is the body this function had, kept as
   the specification; test_learned.ml compares the two on random rows. [make] gives the
   same row by two shortcuts, neither of which changes an integer:

     - an input already in the order [make] produces (strictly increasing by
       [Lit.compare], so no literal twice, every coefficient >= 1) is that order: the
       fold leaves it as it is, the stable sort leaves it as it is, the merge has nothing
       to merge. It is taken as it stands. [Reduce]'s reduced row, a ladder row, a
       learned row handed back by [Pb] and the sum of [Ladder.instantiate] arrive so.
     - otherwise the sort is [sort_by_lit] below, which is a stable sort and so returns
       exactly the list [List.sort] (a stable merge sort) returns; it is faster on the
       one unsorted input that is long, a model row's expansion, which is a few sorted
       blocks one per variable ([Linear.pb_row]).

   The merge's [a1 + a2] stays unchecked, as it was: it is the reference's arithmetic. *)
let make_reference (raw : (int * Lit.t) list) (degree : int) : t =
  let signed, degree =
    List.fold_left
      (fun (acc, d) (a, l) ->
        if a = 0 then (acc, d)
        else if a > 0 then ((l, a) :: acc, d)
        else ((Lit.negate l, -a) :: acc, d - a))
      ([], degree) raw
  in
  let sorted = List.sort (fun (l1, _) (l2, _) -> Lit.compare l1 l2) (List.rev signed) in
  let rec merge = function
    | [] -> []
    | [ (l, a) ] -> [ { coeff = a; lit = l } ]
    | (l1, a1) :: (l2, a2) :: rest ->
        if Lit.equal l1 l2 then merge ((l1, a1 + a2) :: rest)
        else { coeff = a1; lit = l1 } :: merge ((l2, a2) :: rest)
  in
  { terms = merge sorted; degree }

(* Is [raw] already in [make]'s output order: strictly increasing by [Lit.compare], every
   coefficient >= 1? *)
let rec in_make_order = function
  | [] -> true
  | [ (a, _) ] -> a > 0
  | (a, l1) :: ((_, l2) :: _ as rest) ->
      a > 0 && Lit.compare l1 l2 < 0 && in_make_order rest

(* A stable sort by [Lit.compare] on the literal, equal to [List.sort]'s answer on every
   input (a stable sort has one answer). It cuts the list into its maximal non-decreasing
   RUNS, sorts the runs by their first literal, and keeps the concatenation when every
   run ends strictly below the next one's start: then no literal of one run lies inside
   another's range, so the concatenation is sorted, and two equal literals can only be
   in the same run, in input order, which is stability. When that fails, or when the list
   has many short runs (a learned clause in trail order), it is [List.sort] itself. A
   model row's expansion is one run per variable, so this costs [k log k] comparisons
   for [k] variables instead of [n log n] for [n] rungs. *)
let sort_by_lit (l : (Lit.t * int) list) : (Lit.t * int) list =
  let cmp (l1, _) (l2, _) = Lit.compare l1 l2 in
  let n = List.length l in
  let max_runs = 1 + (n / 8) in
  (* The runs, each in input order, the list of them reversed; [None] past [max_runs]. *)
  let rec runs k acc cur last = function
    | [] -> Some (List.rev cur :: acc)
    | x :: rest ->
        if cmp last x <= 0 then runs k acc (x :: cur) x rest
        else if k + 1 > max_runs then None
        else runs (k + 1) (List.rev cur :: acc) [ x ] x rest
  in
  let full () = List.sort cmp l in
  match l with
  | [] | [ _ ] -> l
  | x :: rest -> (
      match runs 1 [] [ x ] x rest with
      | None -> full ()
      | Some [ _ ] -> l (* one run: already sorted *)
      | Some rev_runs ->
          let by_start =
            List.stable_sort
              (fun r1 r2 -> cmp (List.hd r1) (List.hd r2))
              (List.rev rev_runs)
          in
          let rec last = function
            | [ y ] -> y
            | _ :: ys -> last ys
            | [] -> assert false
          in
          let rec disjoint = function
            | r1 :: (r2 :: _ as rest) -> cmp (last r1) (List.hd r2) < 0 && disjoint rest
            | _ -> true
          in
          if disjoint by_start then List.concat by_start else full ())

let make (raw : (int * Lit.t) list) (degree : int) : t =
  if in_make_order raw then
    { terms = List.map (fun (a, l) -> { coeff = a; lit = l }) raw; degree }
  else
    let signed, degree =
      List.fold_left
        (fun (acc, d) (a, l) ->
          if a = 0 then (acc, d)
          else if a > 0 then ((l, a) :: acc, d)
          else ((Lit.negate l, -a) :: acc, d - a))
        ([], degree) raw
    in
    let sorted = sort_by_lit (List.rev signed) in
    let rec merge = function
      | [] -> []
      | [ (l, a) ] -> [ { coeff = a; lit = l } ]
      | (l1, a1) :: (l2, a2) :: rest ->
          if Lit.equal l1 l2 then merge ((l1, a1 + a2) :: rest)
          else { coeff = a1; lit = l1 } :: merge ((l2, a2) :: rest)
    in
    { terms = merge sorted; degree }

(* D-0044's degenerate case, written as what it is: every coefficient 1, degree 1. *)
let of_clause (lits : Lit.t list) : t = make (List.map (fun l -> (1, l)) lits) 1
let terms t = t.terms

(* The row as [(coefficient, literal)] pairs -- the shape [Propagator.pb_row] has and the
   shape lib/core/prop/pb.ml instantiates from. M2-L13: this is what replaced
   [to_linear_row] on the propagation path. Every coefficient is >= 1, because [make]
   established that. *)
let raw_terms t = List.map (fun tm -> (tm.coeff, tm.lit)) t.terms
let degree t = t.degree
let lits t = List.map (fun tm -> tm.lit) t.terms
let is_empty t = t.terms = []

(* Is this the clause case? Asked by tests, and by anything that wants to know whether a
   [rup] is available (a clause is RUP-checkable; a general PB inequality derived by
   cutting planes is not, which is the whole difficulty Koops et al. exist to solve and
   is M2-L6's problem, not this module's). *)
let is_clause t = t.degree = 1 && List.for_all (fun tm -> tm.coeff = 1) t.terms

(* ------------------------------------------------- M2-L6: PB arithmetic on the row *)

(* An instance's own row ([Propagator.pb_row]) as this type. [make] does the
   normalisation, so a [pb_row] may hand over negative coefficients -- and
   [Linear.pb_row] does, deliberately, so that the sign convention lives in exactly one
   place. *)
let of_pb_row (r : Propagator.pb_row) : t =
  make r.Propagator.r_terms r.Propagator.r_degree

(* [combine a ca b cb] is the cutting-planes ADDITION [ca * a + cb * b], which is what a
   `pol` line of the form [ida ca * idb cb * +] derives. It is the step that eliminates
   the pivot in PB conflict analysis, and the elimination is entirely in the third stage
   below.

   Three stages, and the third is the one a reader will look for:

     1. scale. Every coefficient and the degree multiplied, through [Checked] -- I-X8 and
        D-0029: growth past the cap must [raise], not wrap, and conflict analysis is the
        one place in this solver where coefficients multiply without bound. The raise
        propagates to the caller, which treats it as a reason to FALL BACK to the clause
        path rather than as a crash; see lib/core/pb_analysis.ml.
     2. merge. [make]'s job: repeated literals summed, zero coefficients dropped.
     3. CANCEL COMPLEMENTS. [make] does not do this one, and must not be changed to: it
        merges equal literals, and [l] and [~l] are not equal. But over 0-1 variables
        [l + ~l = 1], so

            p * l  +  n * ~l   =   min(p,n)  +  (p-m) * l  +  (n-m) * ~l,   m = min(p,n)

        and the constant moves across, LOWERING the degree by m. Skipping this stage
        would leave a row that is still sound but is not the row the checker holds: both
        checkers normalise complements away when they read a constraint, so our copy and
        theirs would disagree on every subsequent step, and the first [pol] built on the
        difference would be rejected. That is the whole reason this function exists
        instead of a fold over [make].

   The pivot is cancelled by this stage and by nothing else: the caller arranges that the
   pivot appears with coefficient [k] on one side and [k] on the other, so [p = n] and
   both terms vanish. Nothing here knows which literal was the pivot, which is correct --
   cancellation is arithmetic, not a special case. *)
let combine_reference (a : t) (ca : int) (b : t) (cb : int) : t =
  let scaled t c = List.map (fun tm -> (Checked.mul c tm.coeff, tm.lit)) t.terms in
  let raw = scaled a ca @ scaled b cb in
  let degree = Checked.add (Checked.mul ca a.degree) (Checked.mul cb b.degree) in
  (* Net each pseudo-Boolean variable, keeping both polarities so the constant that
     falls out of the cancellation can be counted exactly once per variable. *)
  let sorted = List.sort (fun (_, l1) (_, l2) -> Lit.var_compare l1.Lit.v l2.Lit.v) raw in
  (* M6-T11 (D-0085): [sorted] is sorted by [Lit.var_compare], so the terms of [l]'s
     variable are exactly the maximal PREFIX that is [var_equal] to [l] -- [span] takes it
     in one pass, where a [List.partition] over the whole remainder made the stage
     quadratic (D-0080: 2008 trucking ~50 % in [var_compare]/[var_equal]/[Learned]). Both
     halves come out in the order [partition] gave them, and [acc] is built reversed and
     reversed once instead of by [acc @ keep], so the terms reach [make] in the same order
     and every [Checked] operation runs on the same operands in the same sequence. *)
  let span v group =
    let rec go mine = function
      | ((_, m) as x) :: rest when Lit.var_equal v m.Lit.v -> go (x :: mine) rest
      | rest -> (List.rev mine, rest)
    in
    go [] group
  in
  let rec cancel racc dropped = function
    | [] -> (List.rev racc, dropped)
    | (_, l) :: _ as group ->
        let mine, others = span l.Lit.v group in
        let side positive =
          List.fold_left
            (fun s (c, m) -> if m.Lit.positive = positive then Checked.add s c else s)
            0 mine
        in
        let p = side true and n = side false in
        let m = min p n in
        let keep =
          List.filter
            (fun (c, _) -> c > 0)
            [
              (Checked.sub p m, { Lit.v = l.Lit.v; Lit.positive = true });
              (Checked.sub n m, { Lit.v = l.Lit.v; Lit.positive = false });
            ]
        in
        cancel (List.rev_append keep racc) (Checked.add dropped m) others
  in
  let terms, dropped = cancel [] 0 sorted in
  make_reference terms (Checked.sub degree dropped)

(* ------------------------------------- M11-complexity-T9: the same sums, in one walk

   D-0157. [combine_reference] above is the specification and stays, word for word, as
   what test_learned.ml and the [BAGUETTE_DEBUG] cross-check compare against. What it
   costs is the shape, not the arithmetic: two scaled copies and an append, a sort of the
   whole row by variable, a list per variable, then [make]'s fold, reversal, second sort
   and merge -- for every elimination of a PB analysis, on a row that is often hundreds
   of terms and gets one short reason added. D-0153's profile put 45 % of a bits run in
   the GC, much of it here.

   Both inputs are [make]'s output, so their terms are already sorted by [Lit.compare],
   which sorts by variable first. The sum is then a MERGE of two sorted lists, one
   variable at a time, which is what RoundingSat does with its coefficient array: [walk]
   reads every term of the smaller variable at the two heads, nets the two polarities
   exactly as stage 3 does, and emits at most one term. The answer is the reference's,
   term for term:

     - the same terms: per variable the reference sums the scaled coefficients of each
       polarity (p, n), keeps [p - m] on [l] and [n - m] on [~l] when positive, adds
       [m = min p n] to what the degree loses. [walk] computes the same p, n and m. With
       multipliers >= 0 and coefficients >= 1, p and n are >= 0, so at most one side
       survives, which is why [walk] emits at most one term;
     - the same order: the reference's [make] sorts by [Lit.compare] and merges equal
       literals; one term per variable, emitted in increasing variable order, is that
       order already;
     - the same degree, [ca * da + cb * db - dropped].

   And the same OVERFLOW, which is the part that needs an argument rather than a
   reading. [walk] does its sums in plain [int], and it runs only when none of the
   reference's [Checked] operations can overflow; otherwise the reference runs and
   raises where it always raised, with the same message. The guard is [mass]: with
   [M = ca * mass a + cb * mass b <= max_int] (mass = |degree| + the sum of the
   coefficients), every integer the reference forms is at most M in absolute value -- a
   scaled coefficient or degree, a side sum (part of one polarity's scaled mass), the
   [dropped] total (at most half the scaled coefficient mass), and the final degree (at
   most the scaled degrees plus [dropped]). An operation overflows only when its exact
   result is out of range, so none does.

   [walk] also checks, rather than assumes, that its inputs are in [make]'s order: the
   variables it visits must strictly increase. [Learned.t] is a public record, and a row
   that was not built by [make] gets the reference, never a wrong merge. *)

(* |degree| + the sum of the coefficients, or [-1] when a coefficient is below 1 or the
   sum passes [max_int]. *)
let mass t =
  let rec go s = function
    | [] -> s
    | tm :: rest ->
        if tm.coeff < 1 || s > max_int - tm.coeff then -1 else go (s + tm.coeff) rest
  in
  if t.degree = min_int then -1 else go (abs t.degree) t.terms

(* [c * mass t], or [-1] when it is not representable or [c] is negative. *)
let scaled_mass c t =
  if c < 0 then -1
  else
    let m = mass t in
    if m < 0 then -1 else if c = 0 then 0 else if m > max_int / c then -1 else c * m

(* [x + y] for two results of [scaled_mass], or [-1]. *)
let add_mass x y = if x < 0 || y < 0 || x > max_int - y then -1 else x + y

(* The normal form of [ca * a + cb * b] over two term lists sorted by [Lit.compare] (one
   may hold several terms of a variable, both polarities included), as [(terms,
   dropped)]; [None] when a list is not sorted. Plain arithmetic: the caller has
   established that nothing overflows. A term whose literal and coefficient are an
   input's (a multiplier of 1, the variable on one side only) is that input's record,
   which is the same value and allocates nothing. *)
let walk ca (a : term list) cb (b : term list) : (term list * int) option =
  let rec sums c v p n = function
    | tm :: rest when Lit.var_equal tm.lit.Lit.v v ->
        if tm.lit.Lit.positive then sums c v (p + (c * tm.coeff)) n rest
        else sums c v p (n + (c * tm.coeff)) rest
    | rest -> (p, n, rest)
  in
  let emit v positive c la la' lb lb' =
    match (la, lb) with
    | tm :: _, _
      when la' != la && ca = 1 && tm.coeff = c && tm.lit.Lit.positive = positive ->
        tm
    | _, tm :: _
      when lb' != lb && cb = 1 && tm.coeff = c && tm.lit.Lit.positive = positive ->
        tm
    | _ -> { coeff = c; lit = { Lit.v; positive } }
  in
  let rec go started prev la lb acc dropped =
    let next =
      match (la, lb) with
      | [], [] -> None
      | ta :: _, [] -> Some ta.lit.Lit.v
      | [], tb :: _ -> Some tb.lit.Lit.v
      | ta :: _, tb :: _ ->
          let va = ta.lit.Lit.v and vb = tb.lit.Lit.v in
          Some (if Lit.var_compare va vb <= 0 then va else vb)
    in
    match next with
    | None -> Some (List.rev acc, dropped)
    | Some v ->
        if started && Lit.var_compare prev v >= 0 then None
        else
          let p, n, la' = sums ca v 0 0 la in
          let p, n, lb' = sums cb v p n lb in
          let m = if p < n then p else n in
          let acc =
            if p > m then emit v true (p - m) la la' lb lb' :: acc
            else if n > m then emit v false (n - m) la la' lb lb' :: acc
            else acc
          in
          go true v la' lb' acc (dropped + m)
  in
  match (a, b) with
  | [], [] -> Some ([], 0)
  | tm :: _, _ | [], tm :: _ -> go false tm.lit.Lit.v a b [] 0

let equal (x : t) (y : t) =
  Int.equal x.degree y.degree
  && List.equal
       (fun s u -> Int.equal s.coeff u.coeff && Lit.equal s.lit u.lit)
       x.terms y.terms

(* [combine_reference]'s answer, raise included, by [walk] wherever [mass] says no
   [Checked] operation of the reference could overflow. *)
let combine (a : t) (ca : int) (b : t) (cb : int) : t =
  let fast =
    if add_mass (scaled_mass ca a) (scaled_mass cb b) < 0 then None
    else walk ca a.terms cb b.terms
  in
  match fast with
  | None -> combine_reference a ca b cb
  | Some (terms, dropped) ->
      let r = { terms; degree = (ca * a.degree) + (cb * b.degree) - dropped } in
      Debug.check "M11-T9: Learned.combine equals combine_reference" (fun () ->
          equal r (combine_reference a ca b cb));
      r

(* [add_multiples ~before row [(m1, r1); ...; (mk, rk)]] is the fold

     List.fold_left (fun acc (m, r) -> before (); combine acc 1 r m) row summands

   -- [Ladder.lift] adding one ladder row per rung -- and returns what the fold returns,
   raise included. The fold is k merges of a row that does not shrink, k times the row
   for a lift of k rungs (cargo's lift was minutes of it, D-0149); the answer is ONE
   merge of the row with the summands' scaled terms, sorted together.

   That one merge is the fold's answer because cancellation keeps a running total. For a
   variable, let P and N be the total positive and negative mass the row and the first j
   summands put on it. After the fold's j-th [combine] the variable carries [P - N] on
   its positive literal when that is positive, [N - P] on its negative one otherwise, and
   the degree has lost [min P N] for it in all: true after the first step, which
   normalises every variable of the row, and kept by each further step, since netting
   [P - N + dp] against [dn] leaves [P + dp - (N + dn)] and adds [min (P + dp - N) dn]
   to the [N] already dropped, which is [min (P + dp) (N + dn)] in all. One merge nets P
   against N once and drops the same [min P N]. With no summand the fold is [row]
   itself, not normalised, and so is this.

   The guard is the [combine] one, over the whole fold: every integer the fold forms is
   at most [mass row + sum (m_j * mass r_j)] in absolute value, for the same reasons, so
   when that is representable no step overflows, and otherwise the fold itself runs.
   [before] is asked once per summand in both cases; it is [Ladder.lift]'s stop, which
   raises to abandon the lift, and nothing between two of its calls can raise in the
   one-merge case, so it raises at the same call. *)
let add_multiples ?(before = fun () -> ()) (row : t) (summands : (int * t) list) : t =
  let fold () =
    List.fold_left
      (fun acc (m, r) ->
        before ();
        combine acc 1 r m)
      row summands
  in
  let bound =
    List.fold_left (fun acc (m, r) -> add_mass acc (scaled_mass m r)) (mass row) summands
  in
  match summands with
  | [] -> row
  | _ when bound < 0 -> fold ()
  | _ -> (
      let scaled =
        List.concat_map
          (fun (m, r) ->
            List.map (fun tm -> { coeff = m * tm.coeff; lit = tm.lit }) r.terms)
          summands
      in
      let scaled = List.stable_sort (fun s u -> Lit.compare s.lit u.lit) scaled in
      match walk 1 row.terms 1 scaled with
      | None -> fold ()
      | Some (terms, dropped) ->
          List.iter (fun _ -> before ()) summands;
          let degree =
            List.fold_left (fun d (m, r) -> d + (m * r.degree)) row.degree summands
            - dropped
          in
          let r = { terms; degree } in
          Debug.check "M11-T9: Learned.add_multiples equals the fold of combine"
            (fun () ->
              equal r
                (List.fold_left
                   (fun acc (m, s) -> combine_reference acc 1 s m)
                   row summands));
          r)

(* M11-complexity-T9 (D-0157): into one buffer, where it was a [Printf.sprintf] per term
   and a [String.concat]; the same bytes ([Lit.add_int] is [string_of_int]'s digits,
   [Lit.add_sanitized] is [Lit.to_string]'s pieces, lib/proof/lit.ml). [Retention.add]
   keys every learned row by it. *)
let to_string t =
  let b = Buffer.create 64 in
  List.iteri
    (fun i tm ->
      if i > 0 then Buffer.add_char b ' ';
      Buffer.add_char b '+';
      Lit.add_int b tm.coeff;
      Buffer.add_char b ' ';
      Lit.add_sanitized b (Lit.sanitize (Lit.owner tm.lit.Lit.v)) tm.lit)
    t.terms;
  Buffer.add_string b " >= ";
  Lit.add_int b t.degree;
  Buffer.contents b

(* --------------------------------------------------------------------- proof side *)

(* The constraint as the .opb/.pbp writes it. [Opb.ge] is already the checkers' own
   normal form for a ">=" and [make] has already made every coefficient positive, so
   there is nothing to negate here. *)
let to_opb t = Opb.ge (List.map (fun tm -> (tm.coeff, tm.lit)) t.terms) t.degree

(* Put the learned constraint on the page and hand back its id.

   AT LEVEL 0, unconditionally -- see the module header. That is the whole of M2-L1's
   proof-side half and the reason [Justify.with_level] exists.

   [rup] is the rule, which is D-0044's staging and not a permanent choice: a learned
   CLAUSE is a single [rup] line, the checker re-derives the intermediate resolvents by
   unit propagation, and the cut choice costs nothing in proof size. A general PB
   inequality is not RUP-derivable and M2-L6 owes it a [pol] built from the reduction
   steps; that path will call [Justify.with_level] in exactly the same place, which is
   why the bracket is not folded into this function's body. [is_clause] is what a caller
   asks before trusting the [rup].

   I-X2: the id returned is an id you must delete, with [retire]. Nothing else will --
   a backjump will not, which is the point. *)
let introduce ctx t ~origin : Writer.cid =
  Justify.with_level ctx 0 (fun () -> Writer.rup (Justify.writer ctx) ~origin (to_opb t))

(* The other half of I-X2, and a separate function rather than a comment on [introduce]
   because a learned constraint's lifetime is a policy (M2-L4) and not a scope. *)
let retire ctx (id : Writer.cid) = Writer.delete (Justify.writer ctx) id

(* ------------------------------------------------- the runtime instance (the bet) *)

(* The PB row rewritten over the positive order literals only, as a sorted
   [(name, threshold, coefficient)] list plus a constant that moves to the left-hand
   side. A negated literal ~[x >= v] is [1 - [x >= v]], so it contributes its coefficient
   to the constant and minus its coefficient to the rung.

   [None] for a direct-encoding ([Eq]) literal: the direct encoding is a set of 0-1
   variables with no order to read a bound off (D-0019, D-0040), so there is no linear
   form and saying so is the honest answer.

   M11-complexity-T4 (D-0152, D-0140 L2): sorted by [rung_compare], which is the order
   the polymorphic [compare] gives a [(string, int, int)] triple ([String.compare] on the
   name, then [Int.compare] on the threshold, then on the coefficient), without the
   polymorphic call per comparison. [List.sort] sees the same signs, so the list is the
   same. [to_linear_row] runs on every learned clause, for [--stats]'s [convertible]. *)
let rung_compare (x1, v1, c1) (x2, v2, c2) =
  match String.compare x1 x2 with
  | 0 -> ( match Int.compare v1 v2 with 0 -> Int.compare c1 c2 | c -> c)
  | c -> c

let ladder_form t =
  let rec go acc const = function
    | [] -> Some (List.sort rung_compare acc, const)
    | { coeff; lit } :: rest -> (
        match lit.Lit.v with
        | Lit.Eq _ | Lit.Bit _ -> None (* no ladder form over a bit: D-0130 section 7.5 *)
        | Lit.Ge (x, v) ->
            if lit.Lit.positive then go ((x, v, coeff) :: acc) const rest
            else go ((x, v, -coeff) :: acc) (const + coeff) rest)
  in
  go [] 0 t.terms

(* One variable's rungs, read back as a linear contribution.

   [rungs] is that variable's [(threshold, coefficient)] pairs, sorted and with the zeros
   already dropped; [(lo, hi)] is its DECLARED domain, i.e. the ladder the .opb actually
   contains. The answer is [Some (a, k)] meaning "contributes a * x, plus the constant
   k", or [None] meaning the row has no linear form over this variable.

   Three cases, and they are the whole of the boundary the module header states:

     - a threshold at or below [lo] is the constant true and a threshold above [hi] is
       the constant false. Neither depends on x. These are folded away first, so a row
       that happens to mention an out-of-range rung is not refused for it.
     - the remaining rungs must be EXACTLY [lo+1 .. hi], each with the same coefficient
       a. Then sum_v a*[x >= v] = a*(x - lo), because the order encoding's own identity
       is x = lo + sum_{v=lo+1}^{hi} [x >= v] (docs/PROOF-FORMAT.md section 3). A `var
       bool` has hi = lo + 1, so a single rung satisfies this and the clause case falls
       out of the general rule rather than being special-cased.
     - anything else -- a gap in the run, or two rungs at different coefficients -- has
       no linear form. This is where an interior threshold on an integer variable lands.

   Note that "exactly the ladder" is checked by construction (length and consecutiveness)
   rather than by set membership: a row with a rung repeated would otherwise pass the
   length test, and [make] has already merged repeats, so the two agree. *)
let linear_of_rungs ~lo ~hi rungs =
  let const = ref 0 in
  let inside =
    List.filter
      (fun (v, c) ->
        if v <= lo then (
          const := !const + c;
          false)
        else if v > hi then false
        else true)
      rungs
  in
  match inside with
  | [] -> Some (0, !const)
  | (v0, a) :: _ ->
      let width = hi - lo in
      let consecutive =
        v0 = lo + 1
        && List.length inside = width
        && List.for_all2
             (fun (v, c) i -> v = lo + 1 + i && c = a)
             inside
             (List.init (List.length inside) Fun.id)
      in
      if consecutive then Some (a, !const - (a * lo)) else None

(* The whole row as `sum c_i x_i <= rhs` over integer variable NAMES, or [None] when it
   has no such form. [Linear] is a "<=" propagator and this module's [t] is a ">=", so
   the sign flips exactly once, here.

   Derivation, spelled out because the sign is the thing to get wrong:
     sum_i a_i * (x_i - lo_i) + K  >=  degree            (from the rungs)
     sum_i a_i x_i                 >=  degree - K'       where K' folds the -a_i*lo_i
     sum_i (-a_i) x_i              <=  K' - degree
*)
let to_linear_row t ~decl =
  match ladder_form t with
  | None -> None
  | Some (rungs, const0) ->
      (* [rungs] is sorted by (name, threshold), so a variable's rungs are contiguous.
         D-0152 (D-0140 L2): so they are taken as the maximal prefix with [x]'s name, in
         one pass, which is what [List.partition] over the whole remainder returned on a
         sorted list (the same rungs in the same order, and the same remainder), where
         the partition made the grouping quadratic in the clause. *)
      let rec span x mine = function
        | (y, v, c) :: rest when String.equal x y -> span x ((v, c) :: mine) rest
        | others -> (List.rev mine, others)
      in
      let rec group = function
        | [] -> []
        | (x, v, c) :: rest ->
            let mine, others = span x [] rest in
            (x, (v, c) :: mine) :: group others
      in
      let groups = group rungs in
      let rec fold acc const = function
        | [] -> Some (List.rev acc, const)
        | (x, rungs) :: rest -> (
            match decl x with
            | None -> None
            | Some (lo, hi) -> (
                let rungs =
                  List.filter
                    (fun (_, c) -> c <> 0)
                    (List.sort
                       (fun (v1, c1) (v2, c2) ->
                         match Int.compare v1 v2 with 0 -> Int.compare c1 c2 | c -> c)
                       rungs)
                in
                match linear_of_rungs ~lo ~hi rungs with
                | None -> None
                | Some (0, k) -> fold acc (const + k) rest
                | Some (a, k) -> fold ((-a, x) :: acc) (const + k) rest))
      in
      Option.map (fun (terms, const) -> (terms, const - t.degree)) (fold [] const0 groups)

(* Pack the row for the engine, as a PB CONSTRAINT over the order literals it already
   names -- lib/core/prop/pb.ml, which is D-0054's solving-side object and reads LIVE
   domains. [None] when a literal has no bound to move ([Lit.Eq]) or names a variable
   this store or this encoding does not know; [Pb.atom_of] holds both refusals and the
   reason for each.

   M2-L13 REPLACED [to_linear] AND [instance] WITH THIS, and the replacement is the whole
   of the row. Those two built a [Linear.t] through [to_linear_row], i.e. they asked
   whether the PB row could be read back as an integer linear row over the DECLARED box,
   and propagated only if it could. D-0050 called that "the right predicate used as the
   wrong gate" and D-0054 named why: an algebraic identity over the declared box is a
   PROOF-side test, and whether a row is worth propagating is a SOLVING-side question.
   Neither function had a caller in lib/ -- the bet of "no new propagator family" was
   never actually collected -- so what M2-L13 removed was a designated path, not a live
   one.

   [to_linear_row] itself stays, above, and is now only what bin/main.ml has always
   called it: MEASURED ONLY. [Search.n_pb_converts] and [Learn.converts] read it, nothing
   propagates through it, and test/unit/test_learned.ml keeps the D-0044 boundary it pins
   by building the [Linear.t] itself.

   The two readings are NOT ordered, which is worth knowing before anyone reverses this:
   on a row that is a model row's own expansion the linear reading is STRICTLY STRONGER,
   because the slack rule is blind to the ladder rows that tie one rung to the next
   (lib/core/prop/pb.ml's "Consistency level" section, and lib/core/pb_analysis.ml's
   [Postcondition_failed] section for the same arithmetic on the analysis side). On a
   1UIP-shaped row with a threshold strictly inside a ladder the linear reading does not
   exist at all. This function is the one that always exists.

   [~row_id] is the id [introduce] returned, and the instance DOES expose a
   [Propagator.pb_row] built from it -- unlike the learned clause, which exposes none.
   That is not an inconsistency between the two, it is D-0054's two objects finally both
   being present for the same constraint: the row this instance propagates is the row on
   the page, so it is citable, it is frozen, and PB conflict analysis can resolve against
   it. Leaving it [None] is not neutral: [Engine.row_of] would answer [None], and
   lib/core/pb_analysis.ml would fall back to the clause path on every conflict a learned
   instance reports -- MEASURED on the php models, where omitting it cut the rows learned
   on php_wide_unsat from 30 to 2 and grew the tree instead of shrinking it.

   The terms handed over are the row's own, i.e. the DECLARED-bound object, which is what
   [Propagator.pb_row]'s comment requires ("a row that moved with the search would be the
   wrong side of I-X6"). The propagator beside it reads live domains. Same constraint,
   two readings, which is the whole of D-0054.

   [~bump] is M2-L13's BREAK and is 0 everywhere but in test/unit/test_pb.ml. It raises
   the degree of the propagated constraint above the degree of the row on the page, so
   the instance enforces something the proof does not state. Nothing about the ANSWER
   changes on an unsatisfiable model, which is the whole reason the break exists: the
   only oracle for a wrong slack rule is the checker. It is a parameter rather than a
   test-local copy of this function because a break that exercises a copy of the code
   proves nothing about the code.

   [~id] must be [Engine.next_id] of the engine it is about to be added to -- [Engine.add]
   checks that and says why. *)
let pb_instance ~id ~row_id ?(bump = 0) store ~decl t : Propagator.instance option =
  let row _store =
    Some
      {
        Propagator.r_terms = raw_terms t;
        Propagator.r_degree = t.degree;
        Propagator.r_cid = row_id;
      }
  in
  Option.map
    (fun p ->
      Propagator.pack ~id ~row (module Pb.Learned_pb : Propagator.S with type t = Pb.t) p)
    (Pb.of_terms store ~decl ~degree:(t.degree + bump) (raw_terms t))

(* The declared-domain lookup an [Encoding] provides, in the shape [pb_instance] wants.
   Kept here rather than in [Encoding] because it is this module's question: [Encoding]
   already answers it, it just answers it by raising. *)
let decl_of_encoding enc name =
  if Encoding.is_declared enc name then Some (Encoding.domain enc name) else None
