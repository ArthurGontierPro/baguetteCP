(* learn.ml: 1UIP clause learning over order literals, its semantic minimisation, its
   `rup` derivation and the backjump it licenses (M2-L3).

   Consistency level: none -- this is not a propagator. Governing records:
   docs/DECISIONS.md D-0044 and its 2026-09-18 amendment (the type and the fork below),
   D-0045's addendum (the proof-side lifetime), D-0018 point 4 (the ordering), and
   docs/INVARIANTS.md I-S4 (the debt this row discharges).

   This module assembles parts three earlier rows built and adds nothing to the proof
   vocabulary: [Analysis] (M2-L2) supplies the cut, [Learned] (M2-L1) supplies the
   constraint and its level-0 introduction, [Justify.with_level] (M2-L1) supplies the
   bracket, and [Search] does the branching. What is new here is the minimisation, the
   dependency set the backjump rests on, and the I-S4 support check.

   ---------------------------------------------------------------------------
   D-0044's fork, decided: (ii), PROOF-ONLY
   ---------------------------------------------------------------------------

   D-0044's amendment says [Learned.to_linear_row] returns [None] on a threshold strictly
   inside an integer variable's ladder, which is exactly what a 1UIP cut over integer
   variables produces, and it makes whoever assembles the cut choose between

     (i)  restricting the cut to the shapes that convert, or
     (ii) accepting a proof-only learned constraint.

   **This row takes (ii), and the reason is not convenience.** (i) would make the learned
   object a runtime propagator, and a runtime propagator is what a 1UIP *asserting*
   backjump needs: after undoing to the backjump level the clause is unit, and the search
   resumes only because something propagates it. Nothing here propagates it, so a resume
   would re-reach the same fixpoint, re-take the same decision and re-derive the same
   conflict -- an outright loop, not a slow search. Taking (i) to avoid that would have
   silently restricted learning to Boolean models: [conversion_rate] below counts how
   often the cut converts, so that claim is measured rather than assumed, and M2-L4 has
   the number when it writes the retention policy.

   So the learned clause here is exactly what (ii) says: sound, on the page, correctly
   deleted, and not propagating. What it does NOT do is drive the backjump, and this
   module does not pretend otherwise -- see the next section, which is the part a reader
   will otherwise assume is the 1UIP cut's job.

   ---------------------------------------------------------------------------
   The backjump rests on the DECISION CLOSURE, not on the 1UIP cut
   ---------------------------------------------------------------------------

   It is tempting to backjump to [Analysis.backjump_level] of the 1UIP cut and skip every
   branch between there and the conflict. That is right in a CDCL solver and it is WRONG
   here, and the difference is worth stating because the cut offers the field:

     - a 1UIP cut carries exactly one conflict-level literal and its other literals sit at
       levels <= B. After undoing to B the clause is unit, which is a statement about what
       still HOLDS. It licenses the asserting backjump *provided something propagates the
       unit*, which under (ii) nothing does.
     - the levels a 1UIP cut names are NOT a dependency set. A node at level j that is not
       a root rests on further facts, at levels the cut never names, because
       [Analysis.analyse] under its default scope resolves the conflict level only.
       Skipping a branch on that basis would skip a subtree nothing had refuted, and the
       search would answer UNSAT on a satisfiable model.

   So the backjump here is conflict-directed backjumping over the FULL decision closure:
   [Analysis.analyse ~scope:Everywhere ~criterion:decision_closure] resolves every
   non-root node away at every level, so its cut is over decisions, declared bounds and
   factless prunings alone, and the decision levels it names really are the levels the
   conflict rests on ([Analysis.decision_levels] states that argument at the point it is
   read). [levels] below is that set.

   What the search then does with it is one rule, and it is sound by a one-line argument
   rather than by CDCL's progress argument:

       a branch nogood is a clause every literal of which is FALSE under the decisions in
       force. If it names no literal of level [lvl], it is already false under the
       decisions ABOVE [lvl] -- so it refutes the sibling branch too, which differs from
       this one only at [lvl], and the sibling need not be explored.

   Nothing is skipped that a valid clause does not already refute, so there is no
   completeness obligation to discharge and no resume loop to bound.

   ---------------------------------------------------------------------------
   Semantic minimisation over order literals
   ---------------------------------------------------------------------------

   The ladder makes [x >= 5] entail [x >= 4]. In a clause -- which is what a nogood is --
   that shows up as a pair of literals over one variable in one direction, one of which
   is redundant, and dropping the redundant one strictly STRENGTHENS the clause. Which
   one is redundant is decided by the fact each literal negates:

     - the cut holds the facts [x >= 4] and [x >= 5]; their conjunction is [x >= 5], so
       the clause is [~[x >= 5]] and [~[x >= 4]] is dropped -- among NEGATIVE literals
       over one variable, keep the LARGEST threshold;
     - dually the facts [x <= 3] and [x <= 1] conjoin to [x <= 1], whose negation is
       [x >= 2] -- among POSITIVE literals over one variable, keep the SMALLEST threshold.

   [Weakest] is the same reduction with both comparisons flipped, and it is not a second
   policy anyone should want: it keeps the literal whose fact is implied by the one it
   drops, so the clause claims strictly more than the cut supports and the checker
   rejects it. It exists so that a test can perform exactly that break and watch the
   rejection, which is this row's test (a2) -- see test/unit/test_learn.ml.

   A direct-encoding ([Lit.Eq]) literal has no ladder to read (D-0019, D-0040) and is
   never merged with anything, including another [Eq] literal on the same variable.

   [Analysis.add_node] already keeps the stronger of two facts about one slot, so a cut
   coming out of [Analysis] is already reduced and [minimise] is a no-op on it. The
   reduction is NOT idle: the branch nogood is built from the DECISION stack, and
   first-fail/indomain_min branches the same variable in the same direction at several
   levels along one path ([x >= 1] at one level, [x >= 2] at the next), so the nogood
   really does carry redundant thresholds and really is shortened here. That is where the
   break bites, and it bites on a shipped model rather than on a scene built for it.

   ---------------------------------------------------------------------------
   I-S4, discharged -- and what it turns out to be about
   ---------------------------------------------------------------------------

   I-S4 says a line citing a hole is supported only while the hole's own line is live, and
   docs/INVARIANTS.md records that it holds "by the level discipline rather than by a
   check", with the explicit note that the argument does not cover a learned clause citing
   across levels. This row produces exactly such a clause, so the check is owed here.

   Made, and it splits in two, because the two halves are not equally applicable:

     - LIVE AT DERIVATION. The learned clause is a [rup]: the checker verifies it against
       the database as it stands when it reads the line. Every hole line the cut folded in
       ([Analysis.folds]) must therefore be on the page at that moment. This is a real
       obligation, it is what forces the derivation to precede the `w` that retires its
       level, and [support_check] below measures it rather than arguing it. It is the
       half test (b) breaks.
     - OUTLIVES. [Trace.i_s4_verdict]'s second half -- the cited line's level must be at
       or below the citing line's -- is the *proxy* the level discipline provides for
       "the cited line is still there when the citing line is used again". It does not
       apply to this clause, and saying why is the discharge rather than a waiver: a
       [rup] names no id. There is nothing for a deletion to dangle. A [pol] citing a
       hole line across levels WOULD be a violation, and M2-L6's reduction steps are the
       first thing that could write one -- [crossings] below reports the crossings as
       data so that the day a [pol] replaces this [rup], the numbers are already there.

   So [support_check] returns the liveness verdicts and [crossings] the level crossings,
   and the caller gates on the first and records the second.

   ---------------------------------------------------------------------------
   Determinism (this row's test (f))
   ---------------------------------------------------------------------------

   No [Hashtbl] is iterated here and every list is built in a fixed order: [minimise]
   folds left and preserves first-appearance order, [levels] comes out of
   [Analysis.decision_levels] which sorts, and the nogood is ordered by descending level
   to match [Search]'s own decision stack. A learned database iterated in hash order is
   the specific way learning breaks `scripts/check_determinism.sh`; there is no database
   here at all, and when M2-L4 adds one it inherits this obligation. *)

module Lit = Baguette_proof.Lit
module Writer = Baguette_proof.Writer

(* ------------------------------------------------------- semantic minimisation *)

(* [Strongest] is the reduction. [Weakest] is the break; see the header. *)
type policy = Strongest | Weakest

(* The slot two literals must share before either can subsume the other: one variable,
   one direction of the ladder. An [Eq] literal gets no slot -- [None] means "never
   merged", which is the honest answer for the direct encoding. *)
let slot (l : Lit.t) =
  match l.Lit.v with Lit.Ge (x, _) -> Some (x, l.Lit.positive) | Lit.Eq _ -> None

let threshold (l : Lit.t) = Lit.value l.Lit.v

(* Of two clause literals in one slot, the one to keep. See the header for the two
   directions and why [Weakest] is unsound on purpose. *)
let keep policy a b =
  let va = threshold a and vb = threshold b in
  let bigger = if va >= vb then a else b in
  let smaller = if va <= vb then a else b in
  match (policy, a.Lit.positive) with
  | Strongest, false -> bigger
  | Strongest, true -> smaller
  | Weakest, false -> smaller
  | Weakest, true -> bigger

(* The reduction over a clause carrying one payload per literal -- a decision level for a
   branch nogood, [()] for a bare clause. First-appearance order is preserved, and when
   two literals merge the payload of the SURVIVOR is kept: for a nogood that is the level
   whose decision the surviving literal actually negates, which is what [Search] then
   reads to decide whether a branch can be skipped. *)
let minimise_with policy (xs : (Lit.t * 'a) list) : (Lit.t * 'a) list =
  List.fold_left
    (fun acc ((l, _) as item) ->
      match slot l with
      | None -> acc @ [ item ]
      | Some s ->
          let merged = ref false in
          let out =
            List.map
              (fun ((m, _) as other) ->
                if (not !merged) && slot m = Some s then (
                  merged := true;
                  if Lit.equal (keep policy m l) m then other else item)
                else other)
              acc
          in
          if !merged then out else out @ [ item ])
    [] xs

let minimise ?(policy = Strongest) (lits : Lit.t list) : Lit.t list =
  List.map fst (minimise_with policy (List.map (fun l -> (l, ())) lits))

(* ------------------------------------------------------------- the learned object *)

type t = {
  l_lits : Lit.t list; (* the 1UIP clause over order literals, minimised *)
  l_clause : Learned.t; (* the same thing as D-0044's type *)
  l_cut : Analysis.t; (* the 1UIP cut it came from *)
  l_closure : Analysis.t; (* the decision closure the backjump rests on *)
  l_levels : int list; (* decision levels the conflict rests on, DESCENDING *)
  l_converts : bool; (* would [Learned.to_linear_row] accept it? measured, not used *)
}

let lits t = t.l_lits
let clause t = t.l_clause
let cut t = t.l_cut
let closure t = t.l_closure
let levels t = t.l_levels
let converts t = t.l_converts

(* Analyse one conflict both ways. [None] when either walk fails or when the 1UIP walk
   produced nothing to learn; the caller then behaves exactly as it did before this row
   existed, which is why every arm here is a plain [None] and not an exception.

   Both postconditions are CHECKED rather than assumed: [Analysis] reports
   [stopped_by_criterion] precisely so that a caller can tell "the criterion said stop"
   from "the walk ran out of nodes first", and a decision closure that did not close is
   not a dependency set. *)
let at_conflict ?(policy = Strongest) store (c : Store.conflict)
    ~(vars_of : int -> Var.t list option) ~(decl : string -> (int * int) option) :
    t option =
  match Analysis.analyse store c ~vars_of ~criterion:Analysis.one_uip with
  | Error _ -> None
  | Ok cut -> (
      if not (Analysis.postcondition_holds Analysis.one_uip cut) then None
      else
        match
          Analysis.analyse ~scope:Analysis.Everywhere store c ~vars_of
            ~criterion:Analysis.decision_closure
        with
        | Error _ -> None
        | Ok closure ->
            if not (Analysis.postcondition_holds Analysis.decision_closure closure) then
              None
            else
              let ls = minimise ~policy (Analysis.lits cut) in
              if ls = [] then None
              else
                let cl = Learned.of_clause ls in
                Some
                  {
                    l_lits = ls;
                    l_clause = cl;
                    l_cut = cut;
                    l_closure = closure;
                    l_levels = Analysis.decision_levels closure;
                    l_converts = Learned.to_linear_row cl ~decl <> None;
                  })

(* Put the learned clause on the page, at level 0, through M2-L1's own entry point.

   I-X2: the id handed back is an id the caller must delete. [Search.solve] does, on
   every path, before the conclusion. *)
let introduce ctx t : Writer.cid =
  Learned.introduce ctx t.l_clause
    ~origin:
      (Printf.sprintf "M2-L3 1UIP learned clause (%s)"
         (String.concat " " (List.map Lit.to_string t.l_lits)))

(* ------------------------------------------------------------------ I-S4 *)

(* One hole line the cut's derivation rests on: the hole value, the id of the line that
   states it, and that line's level. *)
type support = { s_hole : int; s_var : string; s_cid : Writer.cid; s_level : int }

(* Every hole line the 1UIP cut folded in. [Analysis.folds] records one entry per fold it
   performed, and [Trace] knows which line it wrote for each hole; a hole no line of ours
   states is not reported, because that is the case I-S4 has nothing to say about (it
   rests on the model's own rows -- I-X10, and [Trace.settle_facts] makes the same
   distinction for the same reason). *)
let supports store trace (t : t) : support list =
  List.filter_map
    (fun (f : Analysis.fold) ->
      match Store.var_named store f.Analysis.fold_var with
      | None -> None
      | Some v -> (
          match
            Store.remover store ~before:f.Analysis.fold_into ~var:v f.Analysis.fold_value
          with
          | None -> None
          | Some e -> (
              match Trace.hole_line_of trace e f.Analysis.fold_value with
              | None -> None
              | Some w ->
                  Some
                    {
                      s_hole = f.Analysis.fold_value;
                      s_var = f.Analysis.fold_var;
                      s_cid = w.Trace.w_cid;
                      s_level = w.Trace.w_level;
                    })))
    (Analysis.folds t.l_cut)

(* The LIVE-AT-DERIVATION half of I-S4, as messages -- empty when it holds. See the
   header for why this half applies to a [rup] and the "outlives" half does not.

   Measurable only under the audit ([Writer.is_live] is maintained there), so a run with
   the audit off reports nothing rather than a false verdict -- the same honesty
   [Trace.record_citation] shows with its [live_known]. *)
let support_check (w : Writer.t) (ss : support list) : string list =
  if not (Writer.auditing w) then []
  else
    List.filter_map
      (fun s ->
        if Writer.is_live w s.s_cid then None
        else
          Some
            (Printf.sprintf
               "I-S4: the learned clause's derivation folds the hole %s <> %d, whose \
                line @c%d (level %d) is ALREADY RETIRED. The derivation must precede the \
                `w` that retires its level (D-0018 point 4)."
               s.s_var s.s_hole s.s_cid s.s_level))
      ss

(* The level crossings, as data: a hole line above level 0 that the level-0 learned
   clause rests on. NOT a violation -- see the header -- and reported so that M2-L6's
   [pol], for which it WOULD be one, does not have to discover the numbers. *)
let crossings (ss : support list) = List.filter (fun s -> s.s_level > 0) ss
