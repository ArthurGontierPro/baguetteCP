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

   **THE LAST CLAUSE OF THAT IS NO LONGER TRUE, and the fork was resolved from the other
   end.** This said "the learned clause here is ... not propagating", and M2-L12 gave the
   clause a propagator (lib/core/prop/clause.ml, registered by
   [Search.register_learned]). M2-L13 then removed the fork itself: D-0054 says the
   conversion question was the wrong one, because [to_linear_row] is a PROOF-side test,
   and lib/core/prop/pb.ml propagates the learned row as a PB constraint over the order
   literals it already names whether or not it converts. So (i) is not "restrict the cut"
   any more and (ii) is not "proof-only" any more; what survives of this section is the
   measurement [l_converts] takes and the LOOP argument above, which is the reason a
   learned constraint needs a consumer at all.

   So the learned clause here is exactly what (ii) said: sound, on the page, correctly
   deleted -- and, since M2-L12/M2-L13, propagating. What it does NOT do is drive the backjump, and this
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
   read). [levels] below is that set -- computed, since M7-T27 (a3), by
   [Analysis.dependency_levels], the same walk over memoised citations instead of over
   facts rebuilt at every conflict; the walk over facts stays as its reference.

   What the search then does with it is one rule, and it is sound by a one-line argument
   rather than by CDCL's progress argument:

       a branch nogood is a clause every literal of which is FALSE under the decisions in
       force. If it names no literal of level [lvl], it is already false under the
       decisions ABOVE [lvl] -- so it refutes the sibling branch too, which differs from
       this one only at [lvl], and the sibling need not be explored.

   Nothing is skipped that a valid clause does not already refute, so there is no
   completeness obligation to discharge and no resume loop to bound.

   **M2-L15 RE-ASKED THIS AND THE ANSWER STOOD, with numbers.** M2-L13 gave the learned PB
   row a runtime propagator, which made lib/core/pb_analysis.ml's closing note's premise
   true and its question live: with a row that propagates, is the closure still right or
   only safe? Right, and the reason is the second bullet above generalised one step -- the
   nogood is a clause over DECISIONS, and a PB row's levels answer a question about
   falsification, not about dependence. Measured over the 44 models: the two sets differ on
   77 of 103 conflicts and on 76 of those the PB set is a strict SUBSET, so the rule would
   jump too high, not too low. [Search.backjump_on_pb] takes it and veripb rejects the
   nogood. See lib/core/search.ml's [pb_level_verdict]; the decision record is owed and
   is noted in M2-L15's handoff rather than numbered from a worktree.

   What M2-L13 did change is [Analysis.analyse ~scope:Everywhere]'s own answer: a learned
   PB instance's pruning is a trail entry with reason facts, so the walk resolves through
   it and [l_levels] already accounts for the row's antecedents. The calculation was
   redone by the walk.

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
  match l.Lit.v with
  | Lit.Ge (x, _) -> Some (x, l.Lit.positive)
  | Lit.Eq _ | Lit.Bit _ -> None

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
   reads to decide whether a branch can be skipped.

   M11-complexity-T4 (D-0140 S5, D-0144). This was a fold that appended with [acc @ [item]]
   and looked each slot up by a [List.map] over the whole accumulator with a POLYMORPHIC
   [slot m = Some s]: quadratic in the clause, and the branch nogood is as long as the
   decision stack (147 on mspsp, 226 on openshop), once per conflict. It is now one cell
   per slot, found through a table keyed by the slot, and the cells kept in
   first-appearance order. Same output, element for element: a slot's cell is created
   where the fold appended the slot's first literal, and every later literal of the slot
   replaces the cell's content exactly when the fold's [List.map] replaced it ([keep]
   does not return [m]). The table is only looked up, never iterated, so no output
   depends on its order. [minimise_with_reference] is the old fold, kept as the
   specification test/unit/test_learn.ml checks this against.

   M16-file-review-T3 (D-0191): the table is created at the clause's length, where it
   started at 16 and doubled, re-hashing every slot it held at each doubling; and a slot
   hashes its name and adds the direction, where [Hashtbl.hash] walked the pair. On
   2011_roster, whose learned clauses are nearly all of 16 literals or more, this function
   was 6 % of the run's samples, a third of it the doublings. Neither changes an answer:
   the table is looked up, never iterated. *)
module Slot_tbl = Hashtbl.Make (struct
  type t = string * bool

  let equal (a, p) (b, q) = String.equal a b && Bool.equal p q
  let hash (a, p) = (2 * Hashtbl.hash a) + Bool.to_int p
end)

let minimise_with policy (xs : (Lit.t * 'a) list) : (Lit.t * 'a) list =
  match xs with
  | [] | [ _ ] -> xs
  | _ ->
      let cells = Slot_tbl.create (List.length xs) in
      let rev =
        List.fold_left
          (fun rev ((l, _) as item) ->
            match l.Lit.v with
            | Lit.Eq _ | Lit.Bit _ -> ref item :: rev
            | Lit.Ge (x, _) -> (
                let s = (x, l.Lit.positive) in
                match Slot_tbl.find_opt cells s with
                | Some cell ->
                    let m = fst !cell in
                    if not (Lit.equal (keep policy m l) m) then cell := item;
                    rev
                | None ->
                    let cell = ref item in
                    Slot_tbl.add cells s cell;
                    cell :: rev))
          [] xs
      in
      List.rev_map ( ! ) rev

let minimise_with_reference policy (xs : (Lit.t * 'a) list) : (Lit.t * 'a) list =
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

(* ------------------------------------------- clause minimisation (M19-config-T6) *)

(* WHICH of [Analysis.minimise_cut]'s rules run, read once from BAGUETTE_MINIMISE (D-0241):
   [off] none, [root] the level-0 rule, [rec] the level-0 rule and the recursive one with
   the abstract-level filter, [rec-nofilter] the same without the filter (a measurement
   arm). Anything else FAILS, the discipline of BAGUETTE_CDCL: a run that silently used
   the default because the spelling was wrong is the trap CLAUDE.md records twice. The
   rules, and why the learned clause stays the `rup` it was, are [Analysis.minimise_cut]'s
   header. *)
type minimisation =
  | Min_off
  | Min_root
  | Min_rec
  | Min_rec_nofilter
  | Min_break_unchecked
(* the break: [Analysis.min_config]'s [min_break_unchecked]. Tests only, so no
   spelling of BAGUETTE_MINIMISE selects it. *)

let default_minimisation = Min_off

let minimisation_name = function
  | Min_off -> "off"
  | Min_root -> "root"
  | Min_rec -> "rec"
  | Min_rec_nofilter -> "rec-nofilter"
  | Min_break_unchecked -> "break-unchecked"

let min_config = function
  | Min_off -> Analysis.min_off
  | Min_root -> { Analysis.min_off with Analysis.min_root = true }
  | Min_rec -> { Analysis.min_off with min_root = true; min_recursive = true }
  | Min_rec_nofilter ->
      {
        Analysis.min_off with
        min_root = true;
        min_recursive = true;
        min_level_filter = false;
      }
  | Min_break_unchecked -> { Analysis.min_off with min_break_unchecked = true }

let minimisation =
  ref
    (match Sys.getenv_opt "BAGUETTE_MINIMISE" with
    | None | Some "" -> default_minimisation
    | Some ("off" | "0") -> Min_off
    | Some "root" -> Min_root
    | Some ("rec" | "1" | "on") -> Min_rec
    | Some "rec-nofilter" -> Min_rec_nofilter
    | Some v ->
        prerr_endline
          (Printf.sprintf
             "baguette: BAGUETTE_MINIMISE=%S is not a setting. Use off, root, rec or \
              rec-nofilter."
             v);
        exit 2)

(* The measurement BAGUETTE_MINIMISE_STATS=1 prints at exit, on stderr: for every learned
   clause, its width as the 1UIP walk left it, what each rule WOULD remove from it (taken
   on the same cut whatever the setting, so one run measures every arm), what [minimise]
   below removes from it, and its width as learned. Off, none of it is computed. *)
type min_stats = {
  mutable ms_clauses : int;
  mutable ms_lits : int; (* literals of the cut's clause, before any rule *)
  mutable ms_root : int; (* ... false at the root *)
  mutable ms_rec : int; (* ... removed by the recursive rule on top of [root] *)
  mutable ms_rec_nofilter : int; (* ... the same without the abstract-level filter *)
  mutable ms_dominated : int; (* ... removed by [minimise] (same variable, same side) *)
  mutable ms_learned : int; (* literals of the clauses as learned *)
  ms_hist_before : int array;
  ms_hist_after : int array;
}

(* [2] counts the widths only, without the shadow runs of every rule, so that a timed run
   can carry it: the shadow runs are three extra [Analysis.minimise_cut] per conflict. *)
let min_stats_level =
  match Sys.getenv_opt "BAGUETTE_MINIMISE_STATS" with
  | Some "1" -> 1
  | Some "2" -> 2
  | _ -> 0

let min_stats_on = min_stats_level > 0
let hist_buckets = 66

let min_stats =
  {
    ms_clauses = 0;
    ms_lits = 0;
    ms_root = 0;
    ms_rec = 0;
    ms_rec_nofilter = 0;
    ms_dominated = 0;
    ms_learned = 0;
    ms_hist_before = Array.make hist_buckets 0;
    ms_hist_after = Array.make hist_buckets 0;
  }

let bump_hist h w = h.(min w (hist_buckets - 1)) <- h.(min w (hist_buckets - 1)) + 1

let print_min_stats () =
  let s = min_stats in
  let hist h =
    String.concat ","
      (List.filter_map
         (fun (i, n) -> if n = 0 then None else Some (Printf.sprintf "%d:%d" i n))
         (Array.to_list (Array.mapi (fun i n -> (i, n)) h)))
  in
  Printf.eprintf
    "minimise: setting=%s clauses=%d lits=%d root=%d rec=%d rec_nofilter=%d dominated=%d \
     learned=%d\n\
     minimise-hist-before: %s\n\
     minimise-hist-after: %s\n\
     %!"
    (minimisation_name !minimisation)
    s.ms_clauses s.ms_lits s.ms_root s.ms_rec s.ms_rec_nofilter s.ms_dominated
    s.ms_learned (hist s.ms_hist_before) (hist s.ms_hist_after)

let () = if min_stats_on then at_exit print_min_stats

(* ------------------------------------------------------------- the learned object *)

type t = {
  l_lits : Lit.t list; (* the 1UIP clause over order literals, minimised *)
  l_clause : Learned.t; (* the same thing as D-0044's type *)
  l_cut : Analysis.t; (* the 1UIP cut it came from *)
  l_levels : int list;
      (* decision levels the conflict rests on, DESCENDING: the decision closure's,
         read through [Analysis.dependency_levels] since M7-T27 (a3) *)
  l_converts : bool;
      (* Would [Learned.to_linear_row] accept it? MEASURED, NOT USED, and since M2-L13
         that is the whole of what the predicate is for: D-0054 took it out of the
         propagation path, so this is a statistic about the SHAPE of the cut and never a
         gate on whether it may propagate. *)
  l_levelled : (Lit.t * int) list;
      (* M19-config-T10 (D-0219): [l_lits] with the decision level of each literal, in the
         same order. The CDCL loop reads its ASSERTING level off it (the second-highest
         level), which the decision closure's [l_levels] is not. *)
  l_lbd : int;
      (* M2-L4's retention score: the number of distinct decision levels the MINIMISED
         clause's literals sit at -- Glucose's "literal block distance". Taken after
         minimisation on purpose: [minimise] merges two literals over one variable in one
         direction, and those two can sit at different levels, so an LBD read off the
         unminimised cut can be strictly larger than the clause's own. Computed here
         because this is where both the levels and the survivors are in hand; what is
         done with it is [Retention]'s business, not this module's. *)
  l_min_supports : int list;
      (* M19-config-T6 (D-0241): trail positions of the entries the minimisation's
         removals rest on. Their lines are what the checker replays to re-derive a dropped
         literal, so [supports] counts them. Empty when nothing was dropped. *)
}

let lits t = t.l_lits
let clause t = t.l_clause
let cut t = t.l_cut
let levels t = t.l_levels
let converts t = t.l_converts
let lbd t = t.l_lbd
let levelled t = t.l_levelled

(* Analyse one conflict both ways. [None] when either walk fails or when the 1UIP walk
   produced nothing to learn; the caller then behaves exactly as it did before this row
   existed, which is why every arm here is a plain [None] and not an exception.

   The 1UIP postcondition is CHECKED rather than assumed: [Analysis] reports
   [stopped_by_criterion] precisely so that a caller can tell "the criterion said stop"
   from "the walk ran out of nodes first". The decision closure's postcondition holds by
   construction of [Analysis.dependency_levels], which since M7-T27 (a3) computes the
   closure's level set over memoised citations rather than by re-walking the facts at
   every conflict (D-0124's second addendum); a closure that does not close is its
   [Error], and not a dependency set. *)
(* M19-config-T10 (D-0219): [~closure:false] skips the decision closure and leaves
   [l_levels] empty. The CDCL loop backjumps on the clause's own asserting level and never
   reads the closure, so it does not pay for the second walk, and an [Error] of that walk
   no longer costs it the clause. The default is the walk, as before. *)
(* M19-config-T6 (D-0241): [?minimisation] picks [Analysis.minimise_cut]'s rules, applied
   to the 1UIP cut after its postcondition is checked and before [minimise]; the default is
   [!minimisation], BAGUETTE_MINIMISE's. [l_cut] is the cut as minimised. *)
let measure_minimisation store raw policy =
  let width cut = List.length (Analysis.lits_levelled cut) in
  let w = width raw in
  let s = min_stats in
  s.ms_clauses <- s.ms_clauses + 1;
  s.ms_lits <- s.ms_lits + w;
  bump_hist s.ms_hist_before w;
  if min_stats_level = 1 then (
    let count cfg =
      let r = Analysis.minimise_cut ~config:(min_config cfg) store raw in
      r.Analysis.mr_root + r.Analysis.mr_recursive
    in
    let root = count Min_root in
    s.ms_root <- s.ms_root + root;
    s.ms_rec <- s.ms_rec + (count Min_rec - root);
    s.ms_rec_nofilter <- s.ms_rec_nofilter + (count Min_rec_nofilter - root);
    s.ms_dominated <-
      s.ms_dominated
      + (w - List.length (minimise_with policy (Analysis.lits_levelled raw))))

let at_conflict ?(policy = Strongest) ?(closure = true) ?minimisation:m store
    (c : Store.conflict) ~(vars_of : int -> Var.t list option)
    ~(decl : string -> (int * int) option) : t option =
  match Analysis.analyse store c ~vars_of ~criterion:Analysis.one_uip with
  | Error _ -> None
  | Ok raw -> (
      if not (Analysis.postcondition_holds Analysis.one_uip raw) then None
      else
        let m = match m with Some m -> m | None -> !minimisation in
        let mr = Analysis.minimise_cut ~config:(min_config m) store raw in
        if min_stats_on then measure_minimisation store raw policy;
        let cut = mr.Analysis.mr_cut in
        match if closure then Analysis.dependency_levels store c ~vars_of else Ok [] with
        | Error _ -> None
        | Ok levels ->
            (* One minimisation, read two ways. [Analysis.lits_levelled] is
               [Analysis.lits] with each literal's level attached and in the same order
               (it is 1:1 by construction -- see its comment), so [List.map fst] of this
               is exactly [minimise ~policy (Analysis.lits cut)] and the clause is
               unchanged by M2-L4. [test_learn.ml]'s [minimise_agrees_with_levelled]
               pins that equality rather than leaving it as a claim in this comment. *)
            let levelled = minimise_with policy (Analysis.lits_levelled cut) in
            let ls = List.map fst levelled in
            if min_stats_on && ls <> [] then (
              min_stats.ms_learned <- min_stats.ms_learned + List.length ls;
              bump_hist min_stats.ms_hist_after (List.length ls));
            if ls = [] then None
            else
              let cl = Learned.of_clause ls in
              Some
                {
                  l_lits = ls;
                  l_clause = cl;
                  l_cut = cut;
                  l_levels = levels;
                  l_converts = Learned.to_linear_row cl ~decl <> None;
                  l_levelled = levelled;
                  l_lbd = List.length (List.sort_uniq Int.compare (List.map snd levelled));
                  l_min_supports = mr.Analysis.mr_supports;
                })

(* Put the learned clause on the page, at level 0, through M2-L1's own entry point.

   I-X2: the id handed back is an id the caller must delete. [Search.solve] does, on
   every path, before the conclusion. *)
(* M11-complexity-T4 (D-0140 J6, D-0144): the origin is built only for a writer that
   keeps it. The null writer of a --no-proof run ([Writer.is_null]) drops [~origin]
   unread in [Writer.fresh], so rendering every literal of every learned clause into a
   string there was work nothing read. A writer that writes keeps it (the audit stores it
   per live id, the mutation knob matches it), so it is built exactly as before; making it
   lazy there is the writer's change, requested in WORKLOG.md. The origin is never written
   to the .pbp, so neither arm can change a byte. *)
let introduce ctx t : Writer.cid =
  let origin =
    if Writer.is_null (Justify.writer ctx) then ""
    else
      Printf.sprintf "M2-L3 1UIP learned clause (%s)"
        (String.concat " " (List.map Lit.to_string t.l_lits))
  in
  Learned.introduce ctx t.l_clause ~origin

(* ------------------------------------------------------------------ I-S4 *)

(* One line on the page that the cut's derivation rests on: what it states, the id of the
   line, and that line's level. [s_hole] is the hole value for a hole line and [None] for
   a bound line. *)
type support = { s_hole : int option; s_var : string; s_cid : Writer.cid; s_level : int }

let support_of_written (w : Trace.written) ~var =
  {
    s_hole = w.Trace.w_hole;
    s_var = var;
    s_cid = w.Trace.w_cid;
    s_level = w.Trace.w_level;
  }

(* Every line the 1UIP cut's derivation rests on.

   TWO sources, and taking only the second would be taking I-S4's phrasing for its
   substance:

     - the line behind every node's SUPPORTING ENTRY. The learned clause is a [rup]: the
       checker re-derives it by unit propagation over the database as it stands, and what
       it propagates along are exactly the trace lines of the entries the walk resolved
       (D-0039, D-0021). Retire one and the [rup] is checked against a database that no
       longer contains what makes it true.
     - the HOLE line behind every fold ([Analysis.folds]). This is the set I-S4 is
       literally about, and it is a subset of what the derivation needs rather than the
       whole of it.

   A line this module cannot name is not reported, because that is the case I-S4 has
   nothing to say about: the step rests on the model's own rows (I-X10), which no `w` can
   retire. [Trace.settle_facts] makes the same distinction for the same reason.

   Deduplicated by id, in first-seen order -- one entry can support several nodes.

   M11-complexity-T4 (D-0140 L1, D-0144): the dedup was a [List.exists] over the list so
   far and the append an [acc @ [s]], quadratic in the number of supports, on every
   learned clause (the I-S4 check is always on). The ids already taken are now a table
   and the list is built reversed and reversed once: the same first-seen entries in the
   same order. *)
module Int_tbl = Hashtbl.Make (Int)

let supports store trace (t : t) : support list =
  let seen = Int_tbl.create 32 in
  let rev = ref [] in
  let add s =
    if not (Int_tbl.mem seen s.s_cid) then (
      Int_tbl.replace seen s.s_cid ();
      rev := s :: !rev)
  in
  List.iter
    (fun (n : Analysis.node) ->
      if n.Analysis.support <> Store.no_support then
        let e = Store.trail_entry store n.Analysis.support in
        List.iter
          (fun w -> add (support_of_written w ~var:(Store.name store e.Store.var)))
          (Trace.lines_at trace e))
    (Analysis.nodes t.l_cut);
  List.iter
    (fun p ->
      let e = Store.trail_entry store p in
      List.iter
        (fun w -> add (support_of_written w ~var:(Store.name store e.Store.var)))
        (Trace.lines_at trace e))
    t.l_min_supports;
  List.iter
    (fun (f : Analysis.fold) ->
      match Store.var_named store f.Analysis.fold_var with
      | None -> ()
      | Some v -> (
          match
            Store.remover store ~before:f.Analysis.fold_into ~var:v f.Analysis.fold_value
          with
          | None -> ()
          | Some e -> (
              match Trace.hole_line_of trace e f.Analysis.fold_value with
              | None -> ()
              | Some w -> add (support_of_written w ~var:f.Analysis.fold_var))))
    (Analysis.folds t.l_cut);
  List.rev !rev

let describe s =
  match s.s_hole with
  | Some h -> Printf.sprintf "the hole %s <> %d" s.s_var h
  | None -> Printf.sprintf "the bound line for %s" s.s_var

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
               "I-S4: the learned clause's derivation rests on %s, whose line @c%d \
                (level %d) is ALREADY RETIRED. The derivation must precede the `w` that \
                retires its level (D-0018 point 4)."
               (describe s) s.s_cid s.s_level))
      ss

(* The level crossings, as data: a hole line above level 0 that the level-0 learned
   clause rests on. NOT a violation -- see the header -- and reported so that M2-L6's
   [pol], for which it WOULD be one, does not have to discover the numbers. *)
let crossings (ss : support list) = List.filter (fun s -> s.s_level > 0) ss
