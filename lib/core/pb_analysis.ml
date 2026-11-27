(* pb_analysis.ml: PSEUDO-BOOLEAN conflict analysis -- eliminate the pivot by linear
   combination and reduction, with 1UIP clause learning (lib/core/learn.ml, M2-L3) as the
   fallback (M2-L6).

   Consistency level: none -- this is not a propagator. Governing records:
   docs/DECISIONS.md D-0044 (the learned object is a PB inequality with the clause as
   its degree-1 case, and the reduction rule is a swappable component) and its 2026-09-18
   amendment (the cut is a second swappable axis, and a guarantee of one rule is not a
   property of the type); docs/INVARIANTS.md I-X6 (an explanation reads a frozen
   snapshot, never live domains), I-X8 / D-0029 (coefficient growth past the cap raises
   [Checked.Overflow], never wraps), I-S4 (a cited line must outlive the line citing
   it).

   ---------------------------------------------------------------------------
   What this does that lib/core/learn.ml cannot
   ---------------------------------------------------------------------------

   Clause learning resolves the IMPLICATION GRAPH: nodes are bound facts, and what comes
   out is a clause, the negation of a conjunction. That is sound and it is what a SAT
   solver does, but it throws away the arithmetic. A row like [3x + 3y + z >= 5] enters
   conflict analysis as "these bounds are inconsistent" and leaves as a disjunction of
   negated bounds, which is a much weaker statement than the row itself.

   This module resolves the ROWS. The conflicting constraint and every reason are taken as
   the pseudo-Boolean inequalities the .opb literally contains ([Propagator.pb_row], which
   exists for this and nothing else), and the pivot is eliminated by

       C' = 1 * C  +  a * reduce(R)

   where [a] is the pivot's coefficient in [C] and [reduce] is the reduction component of
   lib/core/reduce.ml (M2-L5), which weakens and divides [R] so that the pivot's
   coefficient in it is 1 and the addition cancels the pivot exactly. What comes out is
   a general PB inequality, and that is the whole justification for this module: it can
   be STRICTLY STRONGER than the clause the same conflict yields -- see "Where the PB row
   has a linear reading and the clause has none" below.

   ---------------------------------------------------------------------------
   Koops et al. (CP 2025), sections 5 and 6 -- what was taken from them
   ---------------------------------------------------------------------------

   READ, at https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CP.2025.21 (LIPIcs
   vol. 340, "Practically Feasible Proof Logging for Pseudo-Boolean Optimization"). Three
   things from it bear on the emission path here, and one of them turned out to be a
   checker-side fact rather than an emitter-side obligation:

     - MERGING ADJACENT WEAKENING STEPS is section 5.4 point 2, and it is CakePB's
       optimisation, not ours: "CakePB now makes a syntactic simplification pass on pol
       lines, where adjacent literal weakening steps are merged into a single simultaneous
       step internally, and adjacent additions of literal axioms (possibly multiplied by
       constants) are also merged." The consequence for an emitter is that the weakening
       axioms of one reduction should be written ADJACENTLY on one [pol] line, which is
       exactly the shape [Explanation.Weaken] already has -- one summand carrying the
       whole list -- so M2-L5's [derivation] needed no change. Recorded because the
       obvious alternative (one [pol] per weakened literal) is the shape that would defeat
       the checker's pass, and nothing else in the tree says not to write it.
     - PARTIAL WEAKENING BEFORE A NON-NORMALISED DIVISION is section 3's MIR machinery:
       the paper weakens on a set [P] by "add[ing] literal axioms to reduce the
       coefficients to the largest multiple of the divisor d" rather than removing the
       literal outright, and its worked [pol] is `pol 29 ~x1 + 3 d` -- literal axioms,
       then a division, on one line. Our [Reduce] rules both weaken a literal AWAY
       entirely. Partial weakening is strictly stronger and would be a THIRD reduction in
       lib/core/reduce.ml's [reductions] rather than a change here: it is the same
       [Combine ([Term (1, e); Weaken ws], d)] shape with a smaller [ws] coefficient. Not
       taken in this row -- M2-L5 owns that list and a new rule owes its own
       postcondition and its own tests -- and left written down here because it is the
       cheapest strength still on the table. See "What is left" at the foot of this file.
     - ANNOTATED RUP for constraints simplified by units (section 5.2) is why the fallback
       path's single [rup] is not a compromise: RoundingSat does the same thing for the
       same reason, having measured that the explicit cutting-planes alternative "causes
       performance issues during proof checking" and "would require ... a quadratic number
       of steps overall".

   ---------------------------------------------------------------------------
   The stopping criterion is SLACK-BASED, and that is not a detail
   ---------------------------------------------------------------------------

   Learning the first ASSERTIVE constraint gives the highest backjump in a SAT solver.
   Le Berre et al. (arXiv 2107.13085) show there is NO SUCH GUARANTEE for PB constraints,
   because a PB constraint propagates by slack rather than by "all but one literal
   falsified". So an assertive constraint is not a sufficient stop condition, and -- the
   part that bites -- a derived row carrying SEVERAL conflict-level literals can still be
   perfectly good and must be ACCEPTED rather than resolved away.

   [assertive_slack] below is therefore stated in slack and counts nothing. It stops when
   the row conflicts or propagates under the assignment WITH THE CONFLICT LEVEL UNDONE,
   which is a question about coefficients and degrees; the number of conflict-level
   literals never enters it. The implication-graph cut of lib/core/analysis.ml (M2-L2)
   deliberately scoped its 1UIP assertion to
   [Analysis.one_uip]'s own [postcondition] and left [Analysis.conflict_side] accepting
   two conflict-level literals precisely so that this row would not have to re-generalise
   it. It has not been re-generalised: [Analysis.one_uip] is untouched and its
   postcondition is still its own.

   [first_resolution] is the second criterion, and it is here for the reason a second
   implementation always is -- a component with one instance is a constant wearing a
   record. It stops after exactly one elimination, guarantees nothing about levels, and
   says so.

   ---------------------------------------------------------------------------
   [falsified] is frozen AT THE PROPAGATION, and this is the I-X6 obligation
   ---------------------------------------------------------------------------

   lib/core/reduce.ml reads no store on purpose and says whose job this is: "The caller
   (M2-L6) owns freezing that predicate; this module cannot un-freeze it." Here is the
   discharge, and it is not the obvious one.

   The obvious predicate is "falsified under the assignment as it stands at the conflict".
   That is WRONG for a reduction, and wrong in a way that would have shown up as a
   100% fallback rate rather than as an unsound proof. A reason row [R] propagated its
   pivot at trail position [at]; [Reduce]'s postcondition demands that the reduced row
   have slack EXACTLY ZERO, and that holds for the assignment as of [at], not as of the
   conflict. By the conflict, strictly more literals of [R] are falsified, the slack sum
   is smaller, and [Reduce.conflicting_invariant]'s [slack = 0] clause simply fails -- so
   every reduction would be rejected by its own postcondition and every conflict would
   fall back.

   So [bounds_before] reconstructs each variable's domain as of just before [at], out of
   the trail entries' own [old]/[now] pair, and [falsified_before] answers from that. The
   store is read, but only for values the trail already fixes; nothing here can see a
   domain the propagation did not see. That is I-X6 on this half.

   [falsified_before] answers from the variable's bound history in O(log moves), with
   the same answers, and [bounds_before] stays as the specification it is checked against
   under [BAGUETTE_DEBUG]. Still never a live read. The scan it replaced was a downward
   walk of the trail per literal query, four to five queries per term per elimination
   (M11-complexity-T4, D-0144: learning and PB analysis without their quadratic
   lists).

   ---------------------------------------------------------------------------
   Where the PB row has a linear reading and the clause has none (D-0044's fork, from
   the other side)
   ---------------------------------------------------------------------------

   A PB row resolved from model rows can often be read back as an integer linear row
   ([Learned.to_linear_row] accepts it) over a conflict whose 1UIP clause has no such
   reading. The reason is uniformity. [Encoding.linear_terms_int_lin_le] gives every rung
   of a variable's ladder the SAME coefficient, so a model row's expansion is
   ladder-UNIFORM; a positive linear combination of ladder-uniform rows is
   ladder-uniform; and [Reduce.round_to_one] keeps a non-falsified literal exactly when
   its coefficient is divisible by the divisor, at [a / d] -- so a uniform run survives a
   division as a uniform run. A clause, by contrast, names single thresholds, and
   [to_linear_row] returns [None] on a threshold strictly INSIDE an integer variable's
   ladder (D-0044's amendment, lib/core/learned.ml's header).

   "Can often" is not "always": the falsified literals kept by a reduction are an
   arbitrary subset of a ladder and break uniformity at once. So this is not a theorem
   and is not claimed as one -- it is a possibility the clause path does not have, and
   [Search.n_pb_converts] (`pb-convert` in `--stats`) measures how often it is realised
   rather than asserting that it is. Since M2-L13 the answer steers nothing: every
   learned row propagates through lib/core/prop/pb.ml whether or not it converts.

   The clause side, measured 2026-09-18 (M2-L4) by solving every model in test/models/
   with `--stats` and summing the `learned` and `convertible` lines: **13 of 88** learned
   clauses convert, concentrated in the Boolean models. That is why clause learning
   (M2-L3) first took fork (ii) of D-0044's amendment and kept its clauses proof-only,
   until M2-L13 gave every learned row a propagator. The denominator was 86 here until
   M2-L4 re-ran it, stale by `ladder_lift_unsat`'s two clauses, neither of which
   converts; the numerator was and is right. Stated because the correction is the same
   shape as the two M2-L11 made below: a figure copied forward across a task that added
   a model.

   ---------------------------------------------------------------------------
   I-S4 for a [pol]: a PB derivation cites only lines that outlive it
   ---------------------------------------------------------------------------

   A derivation built here cites model rows and level-0 bridge rows and nothing else, so
   every line it cites outlives the line citing it (I-S4). lib/core/learn.ml's header
   discharges I-S4's "outlives" half for its own [rup] by observing that a [rup] names no
   id, and then hands the question here: "A [pol] citing a hole line across levels WOULD
   be a violation, and the reduction steps of PB conflict analysis (M2-L6) are the first
   thing that could write one."

   They do not write one, and the reason is structural rather than lucky. Every leaf of a
   derivation this module builds is an [Explanation.Model_row] carrying a
   [Propagator.pb_row]'s [r_cid] -- a row of the .opb, introduced before the proof's first
   decision and retired by nothing. The only other summand is [Explanation.Weaken], which
   is literal axioms and names no id at all. No hole line, no trace line, no
   conflict-level id is ever cited. [cited_ids] returns the set so a test can assert it
   rather than a reader having to take this paragraph's word for it, and [Search] checks
   it under [Debug].

   The bits encoding adds ONE kind of leaf, and it keeps the discharge: a row with a bits
   term is instantiated through its atoms' bridges and its bound rows (lib/core/ladder.ml,
   "The bits arm"; M8-bits-encoding, D-0153). The bound rows are .opb rows. A bridge is a
   `red` line, minted by [Encoding.ensure_atom] at LEVEL 0 and never deleted before the
   conclusion (D-0132 section 2.8, the bits encoding for [Linear]) -- so it, too, is
   deleted by no backjump ([Writer.wipe_level], which imitates the `w` command VeriPB
   3.0 lacks, deletes only ids tagged at the levels it undoes), and outlives every line
   that cites it. Still no hole line, trace line or conflict-level id.

   ---------------------------------------------------------------------------
   The integer propagator is STRONGER than PB propagation on the same row, and the
   ladder lift that answers it
   ---------------------------------------------------------------------------

   Measured while building this module (M2-L6), and not anticipated by D-0044. The answer
   is the ladder lift of lib/core/ladder.ml (M2-L11).

   [Reduce]'s postcondition requires that the reason row PROPAGATED the pivot, i.e. that
   its slack under the assignment at the propagation was below the pivot's coefficient.
   For a model row expanded over an order encoding, that is often false even though the
   integer propagator legitimately made the pruning. Worked case, and it is not exotic --
   it is [int_lin_le] doing its ordinary job:

     3a + 2b <= 14,  a, b declared 0..4,  and lo(b) = 4 already established.

   [Linear] deduces a <= 2, correctly. The row's PB form is

     3~[a>=1] + 3~[a>=2] + 3~[a>=3] + 3~[a>=4] + 2~[b>=1] + ... + 2~[b>=4] >= 6

   and with b at 4 every [b] term is falsified, leaving slack (3+3+3+3) - 6 = 6. The
   pivot ~[a>=3] has coefficient 3, and 3 > 6 is false: the row ALONE does not
   PB-propagate it. It cannot -- the fact that ~[a>=3] entails ~[a>=4] lives in the
   LADDER constraints, which are separate rows of the .opb (D-0028, docs/PROOF-FORMAT.md
   section 3), and a single row knows nothing about them.

   So [Postcondition_failed] is not a defect in [Reduce] and not a defect in
   [bounds_before]. It is the honest report that the reason for this pruning is the model
   row PLUS a ladder chain, which is exactly what [Linear] already builds as an
   [Explanation] ([Order_reason.weaken_declared]; D-0010, a bound fact is a chain of
   order literals). M2-L11 gives the same chain to THIS module as a row --
   lib/core/ladder.ml -- and [step] below retries the reduction on the lifted row when
   the bare one fails.

   Where the PB path does succeed without any of that -- test/models/backjump_lineq_unsat
   .fzn, 3 of 3 conflicts, no fallback -- it is because the prunings there are at ladder
   ENDS, where the row's own slack is tight enough to propagate without the ladder's help.

   TWO CORRECTIONS TO M2-L6'S OWN NUMBERS, both found by M2-L11 and both worth having in
   front of whoever reads this section next.

     1. [Postcondition_failed] is NOT "the dominant non-[No_row] fallback", which is what
        this heading used to say. Counted over the 38 models on 2026-09-18: of 50
        fallbacks, [No_pivot] is 26, [No_row] is 21 (int_ne 12, bool_clause 3,
        array_bool_or 3, array_bool_and 2, bool_not 1, bool_eq 1) and
        [Postcondition_failed] is 2. The scene the paragraph above describes is real and
        the reasoning about it is right; it is simply not where the traffic is. The
        traffic is conflicts whose conflict-level literals all rest on DECISIONS, which
        nothing can resolve away.
     2. "every learned row is the empty contradiction, 36 of 36" does not hold either. See
        [Search.n_pb_nondegenerate]: it is 26 of 36 NON-degenerate, and the degenerate
        ones are the int_lin_eq family alone.

   ---------------------------------------------------------------------------
   The fallback is permanent, and it is most of the traffic
   ---------------------------------------------------------------------------

   D-0044 records that the clause path is permanent and not transitional, because the
   other solvers that learn linear constraints (IntSat, HaifaCSP, Pumpkin's LLG) all need
   the same fallback. [fallback] below is the reason why, enumerated, and every
   constructor is a measured outcome rather than an error. The most frequent are
   [No_pivot] and [No_row] (26 and 21 of 50 in the count above):

     - [No_pivot]: no falsified conflict-level literal established by a propagation is
       left; what remains rests on DECISIONS, which nothing can resolve away.
     - [No_row]: [Ne], [Bool_clause] and [Bool2int] expose no PB row, because a
       disequality is a pair of big-M rows and a clause propagator is not a single
       inequality either. Any conflict whose conflicting constraint or whose first
       resolvable reason is one of those falls back immediately.
     - [Not_conflicting] is the condition D-0044 names in its own sentence. With
       [division] or [round_to_one] it should not fire -- both reduce to slack zero, and
       adding a slack-zero row to a conflicting one keeps it conflicting -- so a
       non-trivial count here is evidence about a NEW reduction (saturation was one, task
       M2-L7, closed unbuilt) and not about this loop. It is checked every step
       regardless, because "should not fire" is exactly the kind of claim that stops being
       true when the component it rests on is swapped.
     - [Overflow] is I-X8 / D-0029. Coefficients multiply here and nowhere else in the
       solver, so this is where growth past [Checked]'s cap is met. It RAISES inside
       [Learned.combine] and is caught here, which is the only place it may be caught:
       the answer to overflow is to learn a clause instead, never to wrap and never to
       abandon the solve.
     - [Pivot_not_in_reason] is an attribution or encoding mismatch and is the one arm
       that indicates a defect somewhere else. It is a fallback rather than a raise
       because a wrong learned constraint is a soundness bug and a missing one is not.

   ---------------------------------------------------------------------------
   Determinism
   ---------------------------------------------------------------------------

   No [Hashtbl] is iterated and every list is built in a fixed order: the row's terms
   come from [Learned.make], which sorts, and the pivot is chosen by a total order on
   trail positions. scripts/check_determinism.sh requires two runs to emit a
   byte-identical proof, and a learned row whose terms came out of a hash table is the
   way that breaks. *)

module Lit = Baguette_proof.Lit
module Opb = Baguette_proof.Opb
module Writer = Baguette_proof.Writer
module Encoding = Baguette_proof.Encoding

(* ------------------------------------------------------- the frozen assignment *)

(* The domain of [v] as of just BEFORE trail position [at].

   Read off the trail's own record rather than the store's current state -- see the header
   on I-X6. Three cases and they are exhaustive:

     - the newest entry on [v] strictly below [at] holds the answer in its [now];
     - if there is none, [v] had not moved by [at], so the OLDEST entry on [v] at or above
       [at] holds it in its [old];
     - if there is no entry on [v] at all, [v] has not moved in this search and the
       store's current domain is still the one [at] saw.

   [Domain.t] is a value, so reading [e.old] cannot observe a later narrowing. *)
let bounds_before store ~at v =
  let n = Store.trail_length store in
  let rec down i =
    if i < 0 then None
    else
      let e = Store.trail_entry store i in
      if Var.equal e.Store.var v then Some (Domain.lo e.Store.now, Domain.hi e.Store.now)
      else down (i - 1)
  in
  let rec up i best =
    if i >= n then best
    else
      let e = Store.trail_entry store i in
      if Var.equal e.Store.var v then Some (Domain.lo e.Store.old, Domain.hi e.Store.old)
      else up (i + 1) best
  in
  match down (min (at - 1) (n - 1)) with
  | Some b -> b
  | None -> (
      match up at None with
      | Some b -> b
      | None ->
          let d = Store.get store v in
          (Domain.lo d, Domain.hi d))

(* Is [l] falsified by the assignment as of just before trail position [at]?

   [[x >= k]] is false exactly when [hi x < k]; its negation is false exactly when
   [lo x >= k]. An [Eq] literal (the direct encoding, which the solver does not reason
   on: D-0019, D-0040) has no bound to read and is reported NOT falsified, which is the
   safe direction: [Reduce] weakens away what is not falsified, and weakening a literal
   that happens to be falsified only raises the slack, which [Reduce]'s own
   postcondition then rejects -- a fallback, not a wrong row. No [Linear.pb_row]
   contains one, so this arm is unreached today and is written to be
   unreachable-and-safe rather than unreachable-and-absent. A [Bit] literal is answered
   the same way; the bits arm of lib/core/ladder.ml removes every bit from a row before
   the analysis resolves on it. *)
let falsified_before_scan store ~at (l : Lit.t) =
  match l.Lit.v with
  | Lit.Eq _ | Lit.Bit _ -> false
  | Lit.Ge (name, k) -> (
      match Store.var_named store name with
      | None -> false
      | Some v ->
          let lo, hi = bounds_before store ~at v in
          if l.Lit.positive then hi < k else lo >= k)

(* [Store.var_named store] that remembers the last name it answered, by the name's
   physical identity: a row asks about one variable's literals in a run, all carrying the
   one string the store named it with, and the hash is then paid once per run. Any other
   string, equal or not, is looked up. [falsified_before] uses it (D-0157), and so does
   the analysis's [falsified_at] memo (see [falsified_at_with]; M16-file-review-T3,
   D-0191, which took the hashing costs out of learning). *)
let var_named_last store =
  let last = ref None in
  fun name ->
    match !last with
    | Some (n, v) when n == name -> v
    | _ ->
        let v = Store.var_named store name in
        last := Some (name, v);
        v

(* The same answer as [falsified_before_scan] above, case for case, from [v]'s bound
   history in O(log moves) instead of the two trail walks of [bounds_before]. [Reduce]
   and [Ladder] ask it four to five times per term per elimination, so the walk was paid
   trail-length times that per PB step (M11-complexity-T4, D-0144, item P1 of the cost
   inventory D-0140).

   [[x >= k]] is false before [at] iff [hi x <= k - 1] then, i.e. iff that bound had been
   established strictly below [at] or held from the start. A bound only tightens along the
   trail (I-D3), so:

     - if it does not hold NOW, it held at no earlier position either: [false];
     - otherwise [Store.var_support] names the one live entry that established it, and
       the answer is whether that entry sits strictly below [at]: [bounds_before] reads
       the bound off the newest entry on [v] below [at], which includes that entry's
       tightening exactly when that entry is among them;
     - [no_support] while it holds now means no entry established it: it held in the
       domain [v] was created with, which is what [bounds_before] reconstructs at every
       [at] (the oldest entry's [old], or the store's domain when [v] has no entry).

   The negation [~[x >= k]] is the same question on the lower bound with value [k]. The
   scan stays as the [BAGUETTE_DEBUG] cross-check, as [falsified_at_scan] does for
   [falsified_at].

   Applied to [store] and [~at] alone it is a predicate that remembers the last name it
   looked up, by the name's physical identity, in front of [Store.var_named]'s hash
   (M11-complexity-T9, D-0157). A step asks it of one reason's terms over and over, and
   [Ladder.instantiate]'s binary search asks it of one variable's atoms O(log w) times in
   a row. A name is a name: the same string answers the same variable. *)
let falsified_before store ~at =
  let var_named = var_named_last store in
  fun (l : Lit.t) ->
    let r =
      match l.Lit.v with
      | Lit.Eq _ | Lit.Bit _ -> false
      | Lit.Ge (name, k) -> (
          match var_named name with
          | None -> false
          | Some v ->
              let d = Store.get store v in
              let positive = l.Lit.positive in
              let holds_now = if positive then Domain.hi d < k else Domain.lo d >= k in
              if not holds_now then false
              else
                let p =
                  if positive then Store.var_support store v ~is_lower:false ~value:(k - 1)
                  else Store.var_support store v ~is_lower:true ~value:k
                in
                p = Store.no_support || p < at)
    in
    Debug.check "M11-T4: falsified_before agrees with the trail scan" (fun () ->
        r = falsified_before_scan store ~at l);
    r

(* The same question at the conflict, i.e. with the whole trail in force. *)
let falsified_now store (l : Lit.t) =
  falsified_before store ~at:(Store.trail_length store) l

(* The trail position at which [l] became falsified, or [Store.no_support] when it is not
   falsified. A literal its declared domain already falsifies is reported at position 0
   (see the cases below). Used to pick the pivot (the most recently falsified
   conflict-level literal) and to find the entry whose instance is the reason. A literal
   falsified by the declared domain alone has no entry of its own and must never be a
   pivot, since nothing propagated it. It is not one: position 0 is a root entry, below
   any conflict level PB analysis runs at, or, when the root has none, the decision that
   opened level 1, which has no reason and which [pivot_of] therefore skips. *)
let falsified_at_scan store (l : Lit.t) =
  (* ONE pass over the trail, not the O(trail^2) of asking [falsified_before] at every
     position (each of which scanned the trail again). Measured on a real instance
     (MiniZinc Challenge 2011 costas-array, 15.dzn): PB analysis was 5.8 s of a 15 s run
     at 0.44 s a conflict, nearly all of it here (M6-T9, the study of why corpus
     instances time out). The answer is the SAME position the quadratic form returned,
     case for case, and the proof artefacts of the whole model suite are byte-identical
     across the change (D-0080, the profile of where a 300 s run goes):

       - [v] has no trail entry: the domain is the store's, constant over the trail, so
         the first position (0) if it falsifies [l], else none;
       - the NEWEST entry's [now] does not falsify [l]: not falsified now, none;
       - the OLDEST entry's [old] already falsifies [l]: position 0, exactly as the
         quadratic form returned (a change of that answer would need a decision
         record);
       - otherwise the first entry on [v] whose [now] falsifies [l]. Between two
         entries on [v] the reconstructed domain does not move, so no other position
         can be the first. *)
  match l.Lit.v with
  | Lit.Eq _ | Lit.Bit _ -> Store.no_support
  | Lit.Ge (name, k) -> (
      match Store.var_named store name with
      | None -> Store.no_support
      | Some v ->
          let n = Store.trail_length store in
          let fals (d : Domain.t) =
            if l.Lit.positive then Domain.hi d < k else Domain.lo d >= k
          in
          if n = 0 then Store.no_support
          else
            let first = ref (-1) and last = ref (-1) in
            for i = 0 to n - 1 do
              if Var.equal (Store.trail_entry store i).Store.var v then (
                if !first < 0 then first := i;
                last := i)
            done;
            if !first < 0 then if fals (Store.get store v) then 0 else Store.no_support
            else if not (fals (Store.trail_entry store !last).Store.now) then
              Store.no_support
            else if fals (Store.trail_entry store !first).Store.old then 0
            else
              let rec go i =
                if i > !last then Store.no_support
                else
                  let e = Store.trail_entry store i in
                  if Var.equal e.Store.var v && fals e.Store.now then i else go (i + 1)
              in
              go !first)

(* The same position as [falsified_at_scan] above, case for case, from [v]'s bound
   history in O(log moves) instead of one pass over the whole trail per literal
   (M6-T14, D-0088: per-variable trail histories replace the trail scans). [fals] reads
   only the bounds, so the scan's cases collapse: not falsified now -> none; otherwise the
   first bound-mover on [v] whose [now] falsifies, which [Store.var_support] returns
   unless the declared bound already falsified (the scan's "position 0" cases, a moverless
   [v] included). An empty trail is the scan's own [none] and is kept. The scan stays one
   wave as the [BAGUETTE_DEBUG] cross-check. *)
(* [falsified_at] with the name lookup handed in: [analyse] passes [var_named_last],
   because the rows it reads put a wide variable's order literals side by side, all
   under one name. [Store.var_named] there was 5.5 % of 2019_fox-geese-corn's samples
   (D-0191). The lookup returns what [Store.var_named] returns, so
   the position is the same. *)
let falsified_at_with ~var_named store (l : Lit.t) =
  let at =
    match l.Lit.v with
    | Lit.Eq _ | Lit.Bit _ -> Store.no_support
    | Lit.Ge (name, k) -> (
        match var_named name with
        | None -> Store.no_support
        | Some v ->
            let d = Store.get store v in
            let fals_now = if l.Lit.positive then Domain.hi d < k else Domain.lo d >= k in
            if Store.trail_length store = 0 || not fals_now then Store.no_support
            else
              let at =
                if l.Lit.positive then
                  Store.var_support store v ~is_lower:false ~value:(k - 1)
                else Store.var_support store v ~is_lower:true ~value:k
              in
              if at = Store.no_support then 0 else at)
  in
  Debug.check "M6-T14: falsified_at agrees with the trail scan" (fun () ->
      at = falsified_at_scan store l);
  at

let falsified_at store l = falsified_at_with ~var_named:(Store.var_named store) store l

(* The decision level at which [l] became falsified; 0 when it is falsified by the
   declared domain or not falsified at all. *)
let level_of store (l : Lit.t) =
  let at = falsified_at store l in
  if at = Store.no_support then 0 else Store.level_of_index store at

(* ------------------------------------------------------- the criterion *)

(* What a criterion is shown: the row under construction, the conflict level, how many
   eliminations have happened, and -- the field that makes this criterion slack-based
   rather than a literal count -- [c_level_of], the level at which each literal became
   falsified. Frozen functions, not a store: a criterion that could reach the store could
   read live state, which is the wrong side of I-X6's line, and lib/core/analysis.ml drew
   the same line for the same reason. *)
type view = {
  c_row : Learned.t;
  c_conflict_level : int;
  c_steps : int;
  c_level_of : Lit.t -> int;
}

type criterion = {
  crit_name : string;
  stop : view -> bool;
  postcondition : view -> bool;
      (* What THIS criterion guarantees about the row it stopped on. It is not a property
         of [view]; see the header, and lib/core/analysis.ml's [criterion] for the same
         decision taken first. *)
}

(* Slack of [v.c_row] under the assignment restricted to levels <= [lvl]: the sum of the
   coefficients of the terms NOT falsified by then, minus the degree. *)
let slack_at v lvl =
  let sum =
    List.fold_left
      (fun acc (tm : Learned.term) ->
        if v.c_level_of tm.Learned.lit <= lvl then acc
        else Checked.add acc tm.Learned.coeff)
      0 (Learned.terms v.c_row)
  in
  Checked.sub sum (Learned.degree v.c_row)

(* Does the row conflict, or propagate something, under the assignment up to [lvl]?

   Both halves are one slack question. Negative slack is a conflict outright; a literal
   still unfalsified at [lvl] whose coefficient exceeds the slack is propagated. Nothing
   here counts literals at any level, which is the point -- see the header. *)
let asserts_at v lvl =
  let s = slack_at v lvl in
  s < 0
  || List.exists
       (fun (tm : Learned.term) ->
         v.c_level_of tm.Learned.lit > lvl && tm.Learned.coeff > s)
       (Learned.terms v.c_row)

(* ------------------------------------------------------- the levels the ROW names

   Two quantities, and neither is a dependency set: that is the finding of M2-L15
   (backjumping on the PB row; D-0056, the backjump rests on the decision closure and a
   PB row cannot supply one). They are computed here because this is where the frozen
   [view] is, and they are carried on [t] as DATA for lib/core/search.ml to compare
   against the decision closure's. Nothing in this module acts on them.

   [row_levels] is the set of decision levels at which this row's literals became
   falsified -- the PB analogue of [Analysis.cited_levels], level 0 dropped for the same
   reason (a literal falsified at its declared bound is not a decision).

   [asserting_level] is the PB analogue of [Analysis.backjump_level]: the DEEPEST level
   the row still says something at, i.e. the smallest [lvl] with [asserts_at v lvl]. In a
   SAT solver this number IS the backjump level. Here it is a number and nothing more,
   and the reason is exactly Le Berre et al. (arXiv 2107.13085): over PB there is no
   theorem taking "the row still propagates at [lvl]" to "the conflict does not rest on
   the decisions between [lvl] and the conflict level". [assertive_slack] already refuses
   to count literals for that reason; this refuses to backjump for it. *)
let row_levels v =
  List.rev
    (List.sort_uniq Int.compare
       (List.filter_map
          (fun (tm : Learned.term) ->
            let l = v.c_level_of tm.Learned.lit in
            if l > 0 then Some l else None)
          (Learned.terms v.c_row)))

(* Scans UP from 0 and takes the first level that asserts, so the answer is the deepest
   jump the row itself would license. [c_conflict_level] is returned when no lower level
   does -- "this row licenses no jump at all", which is a real outcome and not a failure:
   [assertive_slack] guarantees [conflict_level - 1] asserts, but [first_resolution]
   guarantees nothing, and a row learned under it can land here. *)
let asserting_level_reference v =
  let rec scan lvl =
    if lvl >= v.c_conflict_level then v.c_conflict_level
    else if asserts_at v lvl then lvl
    else scan (lvl + 1)
  in
  scan 0

(* [asserting_level_reference] above, in one pass over the terms instead of one per
   level: the reference is levels x terms, once per learned row, and the levels are the
   search depth (M11-complexity-T4, D-0144).

   At level [lvl] the unfalsified terms are those with [c_level_of > lvl], so the slack
   sum at [lvl + 1] is the one at [lvl] minus the coefficients falsified exactly at
   [lvl + 1], and the largest unfalsified coefficient is a suffix maximum over levels.
   Levels at or below 0 are falsified at every [lvl] scanned and are left out; levels at
   or above the conflict level are unfalsified at every [lvl] scanned and are bucketed
   there.

   The [Checked] operations are the reference's, value for value, so an overflow raises
   where it raised and with the same message (it reaches [Fallback (Overflow m)]). The
   level-0 sum is accumulated over the terms in list order with [Checked.add], which is
   exactly the reference's first sum; every later sum is that one minus nonnegative
   coefficients (a row's coefficients are >= 1, [Learned.make]), so it cannot overflow and
   the reference's own additions for it could not either. Each level's [Checked.sub] of
   the degree is then the reference's, on the same two integers. *)
let asserting_level v =
  let cl = v.c_conflict_level in
  if cl <= 0 then cl
  else
    let at_lvl = Array.make (cl + 1) 0 and max_at = Array.make (cl + 1) 0 in
    let s0 =
      List.fold_left
        (fun acc (tm : Learned.term) ->
          let l = v.c_level_of tm.Learned.lit in
          if l <= 0 then acc
          else
            let b = if l > cl then cl else l in
            let c = tm.Learned.coeff in
            at_lvl.(b) <- at_lvl.(b) + c;
            if c > max_at.(b) then max_at.(b) <- c;
            Checked.add acc c)
        0 (Learned.terms v.c_row)
    in
    (* max_at.(b) becomes the largest coefficient at any level >= b *)
    for b = cl - 1 downto 1 do
      if max_at.(b + 1) > max_at.(b) then max_at.(b) <- max_at.(b + 1)
    done;
    let degree = Learned.degree v.c_row in
    let rec scan lvl sum =
      if lvl >= cl then cl
      else
        let s = Checked.sub sum degree in
        (* the terms unfalsified at [lvl] sit at levels >= lvl + 1 *)
        if s < 0 || max_at.(lvl + 1) > s then lvl
        else scan (lvl + 1) (sum - at_lvl.(lvl + 1))
    in
    scan 0 s0

(* THE criterion (docs/ROADMAP.md M2-L6 test (a2)). Stop as soon as the row would still
   say something after the conflict level is undone -- that is, as soon as it conflicts or
   propagates at [conflict_level - 1].

   Read what this does NOT say. It does not say "one conflict-level literal". A row
   carrying five of them satisfies this the moment its slack at the lower level is small
   enough, and is accepted. That is Le Berre et al.'s point and it is the reason
   [Analysis.one_uip]'s postcondition could not simply have been reused.

   At least one elimination is required before stopping, because the row before any
   elimination is the conflicting constraint itself: already on the page, already
   citable, and learning it would put a copy of a model row into the proof for nothing.
   See [analyse]'s [Nothing_to_learn]. *)
(* DO NOT REINTRODUCE LITERAL COUNTING HERE. The criterion is stated in slack precisely
   because Le Berre et al. (arXiv 2107.13085) show assertiveness gives NO BACKJUMP
   GUARANTEE over PB constraints, and an optimisation that counts conflict-level literals
   because it is cheaper or "matches the SAT solver" does not surface as a wrong answer --
   it surfaces as worse backjumps, which nothing in this repo measures. *)
let assertive_slack =
  let ok v = v.c_steps >= 1 && asserts_at v (v.c_conflict_level - 1) in
  { crit_name = "assertive-slack"; stop = ok; postcondition = ok }

(* The second criterion: stop after exactly one elimination. It guarantees nothing about
   levels and says so, which is what makes it useful -- it is the standing proof that
   [assertive_slack]'s postcondition is [assertive_slack]'s and not a property of the
   type. lib/core/analysis.ml's [conflict_side] is here for the same reason. *)
let first_resolution =
  {
    crit_name = "first-resolution";
    stop = (fun v -> v.c_steps >= 1);
    postcondition = (fun v -> v.c_steps >= 1);
  }

let criteria = [ assertive_slack; first_resolution ]
let find_criterion name = List.find_opt (fun c -> String.equal c.crit_name name) criteria
let postcondition_holds (c : criterion) (v : view) = c.postcondition v

(* ------------------------------------------------------- the outcome *)

(* Why PB analysis handed the conflict back to the clause path. Every one of these is a
   measured outcome, not an error; see the header. *)
type fallback =
  | No_row of string  (** an instance exposes no PB row -- which instance, by name *)
  | Not_conflicting  (** the combination stopped being conflicting: D-0044's condition *)
  | Overflow of string  (** I-X8 / D-0029: coefficient growth past [Checked]'s cap *)
  | Pivot_not_in_reason
  | No_pivot  (** no falsified conflict-level literal is left to resolve on *)
  | Reduction_declined
      (** [Reduce] said [None]: the pivot is not a literal of the reason, or the
          predicate reports it falsified. The latter is the interesting one -- it means
          the frozen assignment is inconsistent at the pivot. *)
  | Postcondition_failed of int * int
      (** [Reduce]'s own postcondition did not hold on its output, with (slack of the
          reduced row, coefficient of the pivot in the reason). A reason that genuinely
          propagated gives slack exactly 0, so a non-zero here says the row fetched for
          this entry did not propagate this pivot under the reconstructed assignment --
          which is a statement about [bounds_before], not about [Reduce]. Carried as
          numbers because the alternative is a counter nobody can act on. *)
  | Nothing_to_learn  (** the criterion stopped before any elimination happened *)
  | Diverged of int
  | Stopped
      (** M6-T23 (D-0149): the search's stop (the time limit) fired during the
          analysis, which was abandoned so that the stop lands at the next node *)
  | Too_long of int
      (** M21-memory-T3 (D-0226): the row this analysis carries has more terms than
          [max_terms] allows (the count is the row's), so the conflict is learned as its
          clause alone. Only under BAGUETTE_PB_MAX_TERMS. *)
  | Mixed_row of string
      (** M8-bits-encoding (D-0153): a row with a bits term whose blocks could not be
          instantiated (lib/core/ladder.ml, "The bits arm"), with what could not be
          read. Not expected from a compiled model -- every block there is [a * 2^i] over
          a variable the encoding knows -- and a fallback rather than a raise for the
          reason [Pivot_not_in_reason] is. *)

let fallback_to_string = function
  | No_row n -> Printf.sprintf "no PB row for instance %s" n
  | Not_conflicting -> "the combination stopped being conflicting"
  | Overflow m -> Printf.sprintf "coefficient growth past the cap: %s" m
  | Pivot_not_in_reason -> "the pivot is not a literal of the reason row"
  | No_pivot -> "no falsified conflict-level literal left to resolve on"
  | Reduction_declined -> "the reduction declined: pivot absent or reported falsified"
  | Postcondition_failed (s, d) ->
      Printf.sprintf "the reduction's postcondition failed (reduced slack %d, divisor %d)"
        s d
  | Nothing_to_learn -> "the criterion stopped before any elimination"
  | Diverged n -> Printf.sprintf "did not terminate after %d eliminations" n
  | Stopped -> "the search's stop fired during the analysis"
  | Mixed_row m -> Printf.sprintf "a mixed row's bits block was not instantiated: %s" m
  | Too_long n -> Printf.sprintf "the row has %d terms, over BAGUETTE_PB_MAX_TERMS" n

(* THE SIZE GUARD on learned PB rows, off by default ([0]); M21-memory-T3, D-0226. With
   [N > 0] the analysis gives up as soon as the row it carries -- the conflict row, or
   the row after any elimination -- has more than [N] terms, and the conflict is learned
   as the 1UIP clause alone, which the search learns anyway (PB analysis is ADDITIVE,
   lib/core/search.ml's [pb] note). So the guard WEAKENS a long PB row to its clause: no
   row of more than [N] terms is derived, put on the page, held by the database or
   propagated, and the eliminations that would have built one are not done.

   Why it exists: on 2015 mapping mesh3x3_2 the learned PB rows have a median of 10 terms
   and a p90 of 457 (D-0221 section 5, the measurement of the retention default), every
   wake of one walks all of them ([Pb.pass]), and PB analysis plus those walks are 83 % of
   the cycles. D-0197 section 6 (the record of the stack overflow on 32-million-term rows)
   asked for a row length cap. This CHANGES the search, so it is a switch, and D-0226 has
   the measurement and the option table. Read once, at start-up, like every BAGUETTE_*
   switch of lib/core. *)
let max_terms =
  match Option.bind (Sys.getenv_opt "BAGUETTE_PB_MAX_TERMS") int_of_string_opt with
  | Some n when n > 0 -> n
  | _ -> 0

type t = {
  row : Learned.t;  (** the learned PB inequality *)
  derivation : Explanation.t;  (** the cutting-planes derivation of exactly [row] *)
  steps : int;  (** eliminations performed *)
  pivots : Lit.t list;  (** the literals eliminated, in order *)
  reduction_name : string;
  criterion_name : string;
  antecedents : int list;  (** constraint ids the derivation cites, first-seen order *)
  antecedent_rows : Learned.t list;
      (** the same rows as data, in the same order. Carried so that M2-L6's test (e)
          can brute-force the entailment -- "these premises imply this conclusion" --
          rather than take the [pol] on trust. A cutting-planes derivation is sound at
          EVERY 0-1 point, not only at the ladder-consistent ones, so that oracle is
          never vacuous even when the model itself is unsatisfiable.

          The LADDER rows a lift cites ([Ladder.lift], M2-L11) are in here too, and they
          must be. Without them the premise set is not ladder-closed, and the conclusion
          genuinely is not entailed by it -- which is the whole finding the ladder lift
          answers, restated as an oracle failure. *)
  ladder_rungs : int;
      (** ladder rows cited by [Ladder.lift] across all eliminations, i.e. how much of
          the reason came from the order encoding rather than from the model row. 0
          means this analysis is exactly the one it would be without the lift. *)
  bits_bridges : int;
      (** bridge and bound rows cited to instantiate bits blocks (D-0153), over the
          conflict row and every reason. 0 means no row of this analysis had a bits
          term. *)
  levels : int list;
      (** M2-L15: the decision levels this row's literals are falsified at, DESCENDING,
          level 0 dropped -- the same shape and ordering as [Analysis.decision_levels] so
          that the two can be compared without either side reordering. NOT A DEPENDENCY
          SET. See [row_levels] above and lib/core/search.ml's [pb_level_verdict]. *)
  asserting_level : int;
      (** M2-L15: the deepest level this row still asserts at. The SAT solver's backjump
          level, computed and deliberately not used. See [asserting_level] above. *)
  conflict_level : int;  (** the level the conflict was found at, for the comparison *)
}

type result = Learned_row of t | Fallback of fallback

(* Monomorphic tables for the analysis (M11-complexity-T4, D-0144): a literal keyed
   through [Lit.equal], an id through [Int.equal], never the polymorphic compare. *)
module Lit_tbl = Hashtbl.Make (struct
  type t = Lit.t

  let equal = Lit.equal
  let hash = Hashtbl.hash
end)

module Int_tbl = Hashtbl.Make (Int)

(* A question about literals, remembered for ONE ROW's literals by their physical
   identity, in row order (M11-complexity-T9, D-0157).

   Each elimination reads the row it holds several times over -- the pivot choice, the
   criterion's slack and its propagation test, the conflict check after the combination
   -- and each read asked [falsified_at] of every term again, through [fat_memo], whose
   key is a [Lit.t]: a hash of the literal's name and a [Lit.equal] in the bucket, four
   times per term per step. [Reduce] and [Ladder] likewise ask [falsified_before] of the
   reason's terms four or five times each. Every one of those reads walks the row's
   terms first to last and asks about [tm.lit], the very record the row holds, so the
   next literal asked is the one after the last one answered, or a few further on (a
   reduced row skips the terms it weakened away). A pointer comparison at most [window]
   places ahead finds it, and its answer is computed once per row instead of once per
   read. A literal found nowhere near -- the pivot built by [Lit.negate], a term a
   combination rebuilt -- is answered by [f] itself.

   The answers are [f]'s: [f] is a function of the literal for the whole call (the trail
   does not move while [analyse] runs, and a reason's predicate is frozen at its
   position, I-X6), so remembering an answer changes how often [f] runs and nothing
   else. *)
let window = 4

let row_memo (lits : Lit.t array) (f : Lit.t -> int) : Lit.t -> int =
  let n = Array.length lits in
  let unknown = min_int (* no answer of [f] here is min_int: a position, or 0/1 *) in
  let ans = Array.make n unknown in
  let cur = ref 0 in
  let rec find i k l =
    if k > window || i >= n then -1
    else if lits.(i) == l then i
    else find (i + 1) (k + 1) l
  in
  fun l ->
    let i = find !cur 0 l in
    let i = if i >= 0 then i else find 0 0 l in
    if i < 0 then f l
    else (
      cur := i + 1;
      let a = ans.(i) in
      if a <> unknown then a
      else
        let a = f l in
        ans.(i) <- a;
        a)

(* A predicate, through [row_memo]. *)
let row_memo_bool (lits : Lit.t array) (p : Lit.t -> bool) : Lit.t -> bool =
  let m = row_memo lits (fun l -> if p l then 1 else 0) in
  fun l -> m l = 1

(* The array is made with a STATIC literal and then filled, never with one of the row's
   own (D-0191). [Array.make] of more than 256 words whose initial
   value is a young block runs a whole minor collection first (the runtime will not
   create that many major-to-minor pointers at once), and a row's literals are young: a
   combination or [Learned.of_pb_row] has just built them. A conflict row over a few
   wide order-encoded terms is longer than that, so every analysis of one paid a minor
   collection here: on 2019_fox-geese-corn (3 000 nodes, no proof) 306 of the run's 1 509,
   a fifth of its promoted words, and 35 % of its samples under this function with the
   major slices they brought. [filler] is a constant the compiler places outside the
   heap, and every cell is overwritten before the array is read. *)
let filler : Lit.t = { Lit.v = Lit.Ge ("", 0); positive = true }

let lits_array (row : Learned.t) : Lit.t array =
  match Learned.terms row with
  | [] -> [||]
  | terms ->
      let a = Array.make (List.length terms) filler in
      List.iteri (fun i (tm : Learned.term) -> a.(i) <- tm.Learned.lit) terms;
      a

(* ------------------------------------------------------- reading a derivation *)

(* Every constraint id the derivation cites. The I-S4 discharge in the header is a claim
   about this list: it holds model-row ids and nothing else. Recursion is over the ADT
   rather than a catch-all, so a constructor added to [Explanation] stops compiling here
   and whoever adds it says what it cites. *)
let cited_ids (e : Explanation.t) : int list =
  (* Built reversed and turned round once, the ids taken in a table (M11-complexity-T4,
     D-0144); the same ids in the same first-seen order as the [List.mem]/[@] it was. *)
  let seen = Int_tbl.create 16 in
  let acc = ref [] in
  let add id =
    if not (Int_tbl.mem seen id) then (
      Int_tbl.replace seen id ();
      acc := id :: !acc)
  in
  let rec go (e : Explanation.t) =
    match e with
    | Explanation.Model_row id -> add id
    | Explanation.Combine { summands; divisor = _; _ } -> List.iter summand summands
    | Explanation.Cut { e1 = a; e2 = b; c1 = _; c2 = _; _ } ->
        go a;
        go b
    (* A RELEASED thunk (M11-complexity-T13, D-0168) has no tree: [force] builds it
       again from the closure, the same derivation (explanation.ml's header), and it is
       not kept. *)
    | Explanation.Deferred _ -> go (Explanation.force e)
    (* M8-bits-encoding-T3 (D-0134): a choice derivation cites its parts' rows. *)
    | Explanation.Resolve { parts; _ } -> List.iter go parts
    | Explanation.Decision _ | Explanation.Clause { lits = _; _ } | Explanation.Linear _
      ->
        ()
  and summand = function
    | Explanation.Term (_, e) -> go e
    | Explanation.Weaken _ -> ()
    | Explanation.Linear_term r -> List.iter go r.lt_cited
    (* A [Defining] cites the id of the line establishing a literal, resolved from
       [Justify]'s claim index at emit time (M4-T7 let an explanation ask for that id) --
       which is exactly the trace-line citation the I-S4 discharge above says this module
       never makes, and which this function could not report even if it did. Nothing here
       builds one; if that changes, the discharge has to be rewritten before this case
       can. *)
    | Explanation.Defining (_, l) ->
        invalid_arg
          (Printf.sprintf
             "Pb_analysis.cited_ids: a Defining summand (%s) cites a line resolved at \
              emit time, not a model row. See the I-S4 discharge in this module's \
              header."
             (Lit.to_string l))
  in
  go e;
  List.rev !acc

(* ------------------------------------------------------- the loop *)

let coeff_of (row : Learned.t) (l : Lit.t) =
  List.find_map
    (fun (tm : Learned.term) ->
      if Lit.equal tm.Learned.lit l then Some tm.Learned.coeff else None)
    (Learned.terms row)

exception Give_up of fallback

(* Eliminate the pivot by linear combination and reduction.

   [row_of] is [Engine.row_of] partially applied -- the instance's PB row, or [None]. It
   is passed rather than the engine for the reason lib/core/analysis.ml passes [vars_of]:
   this module is shown two narrow questions about the engine and cannot reach anything
   else.

   [name_of] is only for the [No_row] message and may answer anything; a fallback reason
   nobody can read is a counter with no diagnosis behind it. *)
let analyse ?(stop = fun () -> false) ?(bits = Ladder.no_bits) store (c : Store.conflict)
    ~(row_of : int -> Propagator.pb_row option) ~(name_of : int -> string)
    ~(ladder_id : string -> int -> int option) ~(break_ladder : bool)
    ~(reduction : Reduce.t) ~(criterion : criterion) : result =
  let conflict_level = Store.level store in
  let max_steps = Store.trail_length store + 1 in
  (* The trail does not move while [analyse] runs, so [falsified_at] is a pure function
     of the literal for the whole call; asked once per term per step by the pivot and
     once per term per criterion check by [level_of], it is memoised here (M6-T9).
     [Lit.t] holds no closure and nothing mutable, so structural hashing is sound; the
     table is only ever looked up, never iterated, so no emitted byte depends on its
     order. It is keyed through [Lit.equal] rather than the polymorphic compare of a
     plain [Hashtbl] (M11-complexity-T4, D-0144); [Lit.equal] is structural equality on
     the same record, so the same lookups hit.

     The table made here is replaced, empty, by one sized at the conflict row once that
     row is known and longer than 64 (below), because a table that grows re-hashes every
     literal it holds at each doubling: a third of the memo's cost on
     2019_fox-geese-corn, some of whose conflict rows run past 256 literals (see
     [lits_array]; D-0191). Nothing reads it before then. *)
  let fat_memo = ref (Lit_tbl.create 64) in
  let var_named = var_named_last store in
  let falsified_at store l =
    match Lit_tbl.find_opt !fat_memo l with
    | Some i -> i
    | None ->
        let i = falsified_at_with ~var_named store l in
        Lit_tbl.add !fat_memo l i;
        i
  in
  (* The ids [antecedents] already holds, so that the dedup below is a lookup instead of
     a [List.mem] over the list so far (D-0144). *)
  let cited = Int_tbl.create 16 in
  (* [antecedents], [rows] and [pivots] are carried REVERSED through the loop and turned
     round once when it stops (M11-complexity-T4, D-0144: they were appended with [@],
     quadratic in the steps); [cited] holds the ids taken. *)
  let add (antecedents, rows) cid r =
    if Int_tbl.mem cited cid then (antecedents, rows)
    else (
      Int_tbl.replace cited cid ();
      (cid :: antecedents, r :: rows))
  in
  (* A row with a bits term is INSTANTIATED before anything resolves on it (D-0153) --
     every bits block replaced through its bridge at the bound in force under [falsified],
     or at [pivot]'s own atom for the pruned block (lib/core/ladder.ml, "The bits arm"). A
     row with none is returned as it is, with the model row as its derivation, which is
     every row at [--bits-above none]: the analysis is then the one it would be without
     the bits arm, line for line.
     The rows added are returned as [(id, row)] premises. *)
  let bridges = ref 0 in
  let instantiated r0 ~cid ~pivot ~falsified =
    if not (Ladder.has_bits r0) then (r0, Explanation.model_row cid, [])
    else
      match Ladder.instantiate ~bits ~row:r0 ~pivot ~falsified with
      | Error m -> raise (Give_up (Mixed_row m))
      | Ok i ->
          bridges := !bridges + List.length i.Ladder.added;
          ( i.Ladder.inst,
            Ladder.derive_instantiated i (Explanation.model_row cid),
            List.map (fun (_, id, r) -> (id, r)) i.Ladder.added )
  in
  (* A row is read through [row_memo] over its own literals -- [at_of] below -- built
     once per row and shared by every read of it: the pivot choice, the conflict check
     after the combination that made it, and the criterion's view (D-0157). The view's
     [c_level_of] is [falsified_at]'s level. *)
  let at_of row = row_memo (lits_array row) (falsified_at store) in
  let view row at_of steps =
    {
      c_row = row;
      c_conflict_level = conflict_level;
      c_steps = steps;
      c_level_of =
        (fun l ->
          let at = at_of l in
          if at = Store.no_support then 0 else Store.level_of_index store at);
    }
  in
  (* The literal to resolve on: falsified, established at the conflict level by an entry
     that rests on facts (a decision rests on none and is never resolved away -- the same
     root rule lib/core/analysis.ml states), and the most RECENT such, which is what makes
     the walk terminate: every elimination's pivot is strictly below the last. Returned
     with its coefficient in the row (D-0157): a row names a literal once
     ([Learned.make]), so this is the coefficient [coeff_of row l] would find by a second
     scan of the row. *)
  let pivot_of row at_of =
    List.fold_left
      (fun best (tm : Learned.term) ->
        let l = tm.Learned.lit in
        let at = at_of l in
        if at = Store.no_support then best
        else if Store.level_of_index store at <> conflict_level then best
        else if Reason.is_empty (Store.trail_entry store at).Store.reason then best
        else
          match best with
          | Some (_, b, _) when b >= at -> best
          | _ -> Some (l, at, tm.Learned.coeff))
      None (Learned.terms row)
  in
  let step row at_of_row expl steps pivots antecedents rows lifts =
    match pivot_of row at_of_row with
    | None -> raise (Give_up No_pivot)
    | Some (l, at, a) ->
        let e = Store.trail_entry store at in
        let reason_row =
          match row_of e.Store.prop with
          | None -> raise (Give_up (No_row (name_of e.Store.prop)))
          | Some r -> r
        in
        let r0 = Learned.of_pb_row reason_row in
        (* The pivot in the REASON is the complement: the conflict row carries [l]
           falsified, and the entry propagated [~l] true. *)
        let p = Lit.negate l in
        (* Frozen at the propagation, not at the conflict. This is the I-X6 discharge and
           the header says why it cannot be the conflict-time predicate. *)
        let falsified_at_prop = falsified_before store ~at in
        (* D-0153: the reason's bits blocks, at the bounds the propagation read and at
           the pivot's own atom. [r] is [r0] when it has none. *)
        let r, base, bridge_rows =
          instantiated r0 ~cid:reason_row.Propagator.r_cid ~pivot:(Some p)
            ~falsified:falsified_at_prop
        in
        (* D-0157: the same predicate, remembered for [r]'s literals, which [Reduce] and
           [Ladder.lift] read term by term several times over. *)
        let falsified = row_memo_bool (lits_array r) falsified_at_prop in
        if coeff_of r p = None then raise (Give_up Pivot_not_in_reason);
        (* One attempt at the reduction, as a result rather than a raise, so that the
           M2-L11 ladder lift below can be a RETRY on the same pivot instead of a second
           copy of this block. *)
        let attempt candidate =
          let v = { Reduce.row = candidate; pivot = p; falsified } in
          match reduction.Reduce.reduce v with
          | None -> Error Reduction_declined
          | Some o ->
              if Reduce.postcondition_holds reduction v o then Ok o
              else
                Error
                  (Postcondition_failed
                     (Reduce.slack o.Reduce.reduced ~falsified, o.Reduce.divisor))
        in
        (* The ladder lift (lib/core/ladder.ml, M2-L11) is a RETRY. The bare model row
           often does NOT PB-propagate the pivot our integer propagator legitimately
           deduced, because the strength is in the order encoding's ladder implications
           and those are separate .opb rows (D-0028). The bare row is tried FIRST and
           unchanged -- so a conflict the bare row handles takes exactly the derivation it
           would take without the lift, and the lift is purely additive -- and the lift is
           the retry when it fails.

           A lift that does not help is not an error: the ORIGINAL failure is reported, so
           [pb_fallback_rev]'s diagnosis still names the condition that actually stopped
           the reduction rather than the rescue that also did not. *)
        let o, wrap, lift =
          match attempt r with
          | Ok o -> (o, (fun e -> e), None)
          | Error e0 -> (
              let lifted =
                try Ladder.lift ~stop ~row:r ~pivot:p ~falsified ~ladder_id () with
                | Checked.Overflow m -> raise (Give_up (Overflow m))
                | Ladder.Stopped -> raise (Give_up Stopped)
              in
              match lifted with
              | None -> raise (Give_up e0)
              | Some lt -> (
                  match attempt lt.Ladder.lifted with
                  | Ok o -> (o, Ladder.derive ~break:break_ladder lt, Some lt)
                  | Error _ -> raise (Give_up e0)))
        in
        (* I-X8 / D-0029: [Learned.combine] multiplies through [Checked], which RAISES
           past the cap. Caught here and turned into a fallback -- never wrapped, and
           never allowed to abandon the solve. [a] is the pivot's coefficient in [row],
           from [pivot_of]. *)
        let row' =
          try Learned.combine row 1 o.Reduce.reduced a
          with Checked.Overflow m -> raise (Give_up (Overflow m))
        in
        (* D-0044's named condition, checked every step. See the header on why it should
           not fire for the reductions that exist today and is checked anyway. *)
        let at_of' = at_of row' in
        let v' = view row' at_of' (steps + 1) in
        if not (slack_at v' conflict_level < 0) then raise (Give_up Not_conflicting);
        let expl' =
          Explanation.combine
            [ Explanation.term 1 expl; Explanation.term a (o.Reduce.derive (wrap base)) ]
            1
        in
        (* The model row is the premise as the .opb holds it ([r0]), and the bridges a
           bits block was instantiated through are premises beside it. *)
        let acc = add (antecedents, rows) reason_row.Propagator.r_cid r0 in
        let acc = List.fold_left (fun acc (cid, br) -> add acc cid br) acc bridge_rows in
        (* The ladder rows are PREMISES of this derivation and are recorded as such. The
           entailment oracle reads [antecedent_rows], and a premise it was not shown is a
           premise it would wrongly report the conclusion as independent of. *)
        let antecedents, rows =
          match lift with
          | None -> acc
          | Some lt ->
              List.fold_left (fun acc (cid, lr) -> add acc cid lr) acc lt.Ladder.rows
        in
        let lifts =
          match lift with None -> lifts | Some lt -> lifts + lt.Ladder.rungs
        in
        (row', at_of', expl', l :: pivots, antecedents, rows, lifts)
  in
  try
    let conflict_row =
      match row_of c.Store.c_prop with
      | None -> raise (Give_up (No_row (name_of c.Store.c_prop)))
      | Some r -> r
    in
    let row0_opb = Learned.of_pb_row conflict_row in
    (* D-0153: the conflict row's bits blocks, at the bounds in force at the conflict. *)
    let row0, expl0, bridge_rows0 =
      instantiated row0_opb ~cid:conflict_row.Propagator.r_cid ~pivot:None
        ~falsified:(falsified_before store ~at:(Store.trail_length store))
    in
    (* If our reconstruction of the conflicting row is not actually conflicting, the row
       we built is not the row the store conflicted on. That is a real disagreement and it
       falls back rather than deriving from a premise the search does not share. *)
    let lits0 = lits_array row0 in
    if Array.length lits0 > 64 then fat_memo := Lit_tbl.create (Array.length lits0);
    let at_of0 = row_memo lits0 (falsified_at store) in
    if not (slack_at (view row0 at_of0 0) conflict_level < 0) then
      raise (Give_up Not_conflicting);
    let rec loop row at_of_row expl steps pivots antecedents rows lifts =
      (if max_terms > 0 then
         let n = List.length (Learned.terms row) in
         if n > max_terms then raise (Give_up (Too_long n)));
      let v = view row at_of_row steps in
      if criterion.stop v then
        if steps = 0 then raise (Give_up Nothing_to_learn)
        else
          Learned_row
            {
              row;
              derivation = expl;
              steps;
              pivots = List.rev pivots;
              reduction_name = reduction.Reduce.name;
              criterion_name = criterion.crit_name;
              antecedents = List.rev antecedents;
              antecedent_rows = List.rev rows;
              ladder_rungs = lifts;
              bits_bridges = !bridges;
              (* M2-L15, from the FROZEN view and at the moment the criterion stopped --
                 not recomputed later against a store that has moved (I-X6). *)
              levels = row_levels v;
              asserting_level = asserting_level v;
              conflict_level;
            }
      else if steps >= max_steps then raise (Give_up (Diverged steps))
      else if stop () then raise (Give_up Stopped)
      else
        let row', at_of', expl', pivots', antecedents', rows', lifts' =
          step row at_of_row expl steps pivots antecedents rows lifts
        in
        loop row' at_of' expl' (steps + 1) pivots' antecedents' rows' lifts'
    in
    Int_tbl.replace cited conflict_row.Propagator.r_cid ();
    let antecedents0, rows0 =
      List.fold_left
        (fun acc (cid, br) -> add acc cid br)
        ([ conflict_row.Propagator.r_cid ], [ row0_opb ])
        bridge_rows0
    in
    loop row0 at_of0 expl0 0 [] antecedents0 rows0 0
  with
  | Give_up f -> Fallback f
  (* Anything that overflows anywhere in the walk is a fallback, never an abandoned
     solve. The combination and the ladder lift are wrapped above, but the SLACK of a
     combined row is a sum too, and the criterion asks for it on every step ([slack_at]
     via [stop]/[asserts_at]). On 2014_rectangle-packing (MiniZinc Challenge) that sum
     passed 2^62 and the raise reached bin/main.ml's internal-overflow arm, exit 4,
     ending the run, before this catch existed (M6-T9). *)
  | Checked.Overflow m -> Fallback (Overflow m)

(* ------------------------------------------------------- the proof side *)

(* What [analyse] is told about the bits encoding (D-0153), read off the context the
   proof is written through. [Ladder.no_bits] when no variable is on bits,
   which is every run at [--bits-above none], so the closure below is never built there.
   [bridge] is [Encoding.ensure_atom]: it MINTS the atom's `red` pair at level 0 the first
   time the atom is named (lib/core/ladder.ml, "It MINTS, unlike [lift]"). *)
let bits_of_ctx (ctx : Justify.ctx) : Ladder.bits =
  let enc = ctx.Justify.encoding and w = ctx.Justify.writer in
  if Encoding.n_bits_vars enc = 0 then Ladder.no_bits
  else
    {
      Ladder.bits_var =
        (fun x ->
          if not (Encoding.is_declared enc x) then None
          else
            match Encoding.bits_n enc x with
            | None -> None
            | Some n ->
                let lo, hi = Encoding.domain enc x in
                Some (lo, hi, n));
      bridge = (fun x v -> Encoding.ensure_atom enc w x v);
      bound_rows = (fun x -> Encoding.bound_lines enc w x);
    }

(* Put the learned PB row on the page and hand back its id.

   AT LEVEL 0 and STATING WHAT IT DERIVES, and both halves matter:

     - level 0, for exactly the reason lib/core/learned.ml's [introduce] gives: a
       constraint derived at the conflict level is deleted by the backjump that follows,
       and the checker then rejects the next line that cites it -- "Trying to access
       constraint with ID 3 that has already been deleted". [Justify.with_level] moves the
       level for real, in the proof, rather than only in our own table.
     - stating, through [Justify.emit_stating], because a bare [pol] derives whatever the
       cutting-planes expression evaluates to and says nothing about what we THINK it
       derived. With the claim on the page the checker's `ia` compares the two, so a
       disagreement between [Learned.combine]'s arithmetic and the checker's surfaces
       here, as a rejected line, instead of propagating silently into whatever cites this
       row. That is this row's own arithmetic being checked by the proof rather than by a
       test, and it is available only because the learned object is a [pol] -- the clause
       path's [rup] has nothing to state.

   I-X2: the id handed back is an id the caller must delete (lib/core/retention.ml does).
   Nothing else will, because no backjump's deletions reach level 0. *)
let introduce ctx (t : t) : Writer.cid =
  Justify.with_level ctx 0 (fun () ->
      Justify.emit_stating ctx ~claim:(Learned.to_opb t.row) t.derivation)

let to_string (t : t) =
  Printf.sprintf "[%s/%s] %s | %d step(s), pivots %s | cites %s" t.criterion_name
    t.reduction_name (Learned.to_string t.row) t.steps
    (String.concat " " (List.map Lit.to_string t.pivots))
    (String.concat "," (List.map string_of_int t.antecedents))

(* ---------------------------------------------------------------------------
   What is left on the PB row: one strength not taken, two questions answered
   ---------------------------------------------------------------------------

   This note was written for whoever took M2-L7 (saturation as a second reduction, since
   closed unbuilt) or the next PB task. Item 1 is still open; items 2 and 3 are answered
   and say how.

   1. PARTIAL WEAKENING, per Koops et al. section 3 (see the header). A third [Reduce.t],
      not a change here: weaken a non-falsified literal's coefficient DOWN to the largest
      multiple of the divisor instead of removing the literal, so it survives the division
      at [floor (a / d)] instead of vanishing. It is free by the same slack argument
      lib/core/reduce.ml gives -- dropping [a mod d] from a non-falsified term removes it
      from both the slack sum and the degree -- and it dominates [round_to_one] as
      [round_to_one] dominates [division].
   2. A RUNTIME INSTANCE for the learned row. **DONE, M2-L13, and not the way this said.**
      It read "[Learned.instance] already builds one when [to_linear_row] accepts". That
      was the plan D-0054 rejected: [to_linear_row] is an algebraic identity over the
      DECLARED box, a proof-side test standing in for a solving-side one, and gating
      propagation on it means propagating only the rows the proof pipeline happens to
      emit in a convertible shape. [Learned.instance] is gone; [Learned.pb_instance]
      builds a lib/core/prop/pb.ml slack propagator over the order literals the row
      already names, which always exists, and [Search.register_learned_pb] registers it
      with the retention citation M2-L4's policy needs.
   3. BACKJUMPING ON THE PB ROW. **ANSWERED, M2-L15, and the answer is that the decision
      closure is RIGHT and not merely safe.** This note used to hand the question on,
      because M2-L13 made a PB row propagate and "that would change the calculation" had
      stopped being hypothetical. It did change the calculation -- just not on this side
      of it. See lib/core/search.ml's [pb_level_verdict], which has the argument in full;
      the decision record is D-0056 (the backjump rests on the decision closure, and a PB
      row cannot supply one).

      The quantity this module can offer is [levels] and [asserting_level] above, and
      neither is in the currency the backjump is stated in. lib/core/search.ml's backjump
      in the default DFS loop is not "undo to level B and resume": it is a FILTER on the
      branch nogood, and the
      nogood is a clause over DECISION literals that the checker RUP-verifies. Dropping a
      level from it is claiming the conflict does not rest on that decision, which is a
      claim about the decision closure and about nothing else. A PB row's [levels] answers
      a different question -- at which levels its literals became falsified -- and
      [asserting_level] answers a third, which is the one Le Berre et al. warn carries no
      backjump guarantee at all.

      What M2-L13 DID change is the closure, and it changed it in the right direction
      without anyone writing code: a learned PB instance's pruning is a trail entry with
      reason facts, so [Analysis.analyse ~scope:Everywhere] resolves straight through it
      and the closure it returns already accounts for the row's antecedents. The
      calculation was redone by the walk, not by this module.

      MEASURED, not argued (M2-L15 test (a)), over the 44 models on 2026-09-21: 103
      conflicts reach both analyses, the two level sets AGREE on 26 and differ on 77, and
      on **76 of those 77 the PB set is a STRICT SUBSET of the closure's** -- it names
      fewer decisions, so filtering the branch nogood by it drops literals the conflict
      genuinely rests on and licenses a jump that is not justified. Three of the 76 are
      the empty contradiction, whose [levels] is [[]]: filtering by it leaves the EMPTY
      CLAUSE. Exactly one conflict goes the other way (width_sat_depth: the closure names
      one level, {26}, and the row names all 26 -- harmless as a backjump, and the
      clearest single picture of the currency mismatch there is).

      And the CDCL instinct has a number too: on 76 of the 103, [asserting_level] is below
      EVERY level the closure names, i.e. the row would resume beneath every decision the
      conflict rests on. That is Le Berre et al.'s warning as a measurement.

      [Search.backjump_on_pb] is the break that takes the narrower set. On the php scene
      it gets a SMALLER TREE (20 nodes against 35) and still answers UNSAT -- a wrong
      backjump looks like an improvement from everywhere except the proof -- and veripb
      3.0.2 rejects its nogood. test/unit/test_pb.ml runs it and asserts the whole
      sentence of the rejection. *)
