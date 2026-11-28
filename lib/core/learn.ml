(* learn.ml: from one conflict to one learned clause. [at_conflict] runs the 1UIP walk of
   lib/core/analysis.ml, minimises the clause it cuts over order literals, and computes
   the decision levels the conflict rests on; [introduce] puts the clause on the page as a
   `rup` at level 0; [supports] and [support_check] verify that every line the `rup`
   rests on is still live. Task M2-L3 built it.

   Two search loops consume it. The default depth-first search ([Search.dfs]) writes a
   branch nogood and uses [l_levels] to skip siblings the nogood already refutes (the
   second section below). The CDCL loop ([Search.cdcl], enabled by --cdcl or
   BAGUETTE_CDCL=1, off by default) backjumps instead to the learned clause's asserting
   level, read off [l_levelled], where the clause propagates and no branch nogood is
   written (D-0219); --chrono N makes it backtrack chronologically when that jump would
   be long (D-0224).

   Consistency level: none -- this is not a propagator. Governing records:
   docs/DECISIONS.md D-0044, which decided that the learned object is a PB inequality
   with the clause as its degree-1 case, and its 2026-09-18 amendment, which raised the
   fork discussed below; D-0045's addendum, which found that a learned constraint is
   tagged with the writer's current level and so must be introduced at level 0 to
   survive the backjump (the proof-side lifetime); D-0018 point 4, which requires the
   nogood to be written before its level is wiped (the ordering); and
   docs/INVARIANTS.md I-S4, a trace line citing a hole is supported only while the hole's
   own line is live (the debt this module discharges, see the last section but one).

   The module assembles parts three earlier tasks built and adds nothing to the proof
   vocabulary: [Analysis] (M2-L2, the implication graph and the cut as data) supplies the
   cut, [Learned] (M2-L1, the learned-constraint type and its proof-side introduction and
   deletion) supplies the constraint and its level-0 introduction, [Justify.with_level]
   (M2-L1) supplies the bracket that sets the writer's level, and [Search] does the
   branching. What is new here is the minimisation, the dependency set the backjump
   rests on, and the I-S4 support check.

   ---------------------------------------------------------------------------
   The learned clause propagates, and the fork that once said otherwise
   ---------------------------------------------------------------------------

   The learned clause is sound, on the page at level 0, deleted by the retention policy
   when it is evicted, and propagating: lib/core/prop/clause.ml propagates it once
   [Search.register_learned] registers it (M2-L12), and lib/core/prop/pb.ml propagates a
   learned PB row over the order literals it names (M2-L13). What it does NOT do is drive
   the default search's backjump; see the next section, which is the part a reader will
   otherwise assume is the 1UIP cut's job.

   Why a learned constraint needs a consumer at all is the LOOP argument. A 1UIP
   *asserting* backjump undoes to the backjump level, where the clause is unit, and the
   search resumes only because something propagates that unit. Without a propagator the
   resume re-reaches the same fixpoint, re-takes the same decision and re-derives the
   same conflict: an outright loop, not a slow search.

   The history, because [l_converts] still carries it. D-0044's amendment noted that
   [Learned.to_linear_row] returns [None] on a threshold strictly inside an integer
   variable's ladder, which is exactly what a 1UIP cut over integer variables produces,
   and it made whoever assembles the cut choose between

     (i)  restricting the cut to the shapes that convert, or
     (ii) accepting a proof-only learned constraint.

   M2-L3 took (ii), and not for convenience: (i) would have silently restricted learning
   to Boolean models, so [l_converts] recorded per learned clause whether the cut
   converts, and M2-L4 had that number when it wrote the retention policy. M2-L12 then
   gave the clause a propagator, and M2-L13 removed the fork itself: D-0054 found that a
   proof line and a propagation explanation are different objects, that [to_linear_row]
   is a PROOF-side test, and that pb.ml propagates the learned row whether or not it
   converts. So (i) no longer means "restrict the cut" and (ii) no longer means
   "proof-only"; what survives of the fork is the measurement [l_converts] takes.

   ---------------------------------------------------------------------------
   The default backjump rests on the DECISION CLOSURE, not on the 1UIP cut
   ---------------------------------------------------------------------------

   In the default search it is tempting to backjump to [Analysis.backjump_level] of the
   1UIP cut and skip every branch between there and the conflict. That is right in the
   CDCL loop and WRONG in [Search.dfs], and the difference is worth stating because the
   cut offers the field:

     - a 1UIP cut carries exactly one conflict-level literal and its other literals sit at
       levels <= B. After undoing to B the clause is unit, which is a statement about what
       still HOLDS. It licenses the asserting backjump *provided the search re-enters
       level B and lets the clause propagate there*, which is what [Search.cdcl] does and
       what [Search.dfs], which re-enters through a branch nogood, does not.
     - the levels a 1UIP cut names are NOT a dependency set. A node at level j that is not
       a root rests on further facts, at levels the cut never names, because
       [Analysis.analyse] under its default scope ([At_conflict_level]) resolves the
       conflict level only. Skipping a branch on that basis would skip a subtree nothing
       had refuted, and the search would answer UNSAT on a satisfiable model.

   So the backjump of [Search.dfs] is conflict-directed backjumping over the FULL decision
   closure: [Analysis.analyse ~scope:Everywhere ~criterion:decision_closure] resolves
   every non-root node away at every level, so its cut is over decisions, declared bounds
   and factless prunings alone, and the decision levels it names really are the levels the
   conflict rests on ([Analysis.decision_levels] states that argument at the point it is
   read). [levels] below is that set, computed by [Analysis.dependency_levels], the same
   walk over memoised citations instead of over facts rebuilt at every conflict (M7-T27
   (a3), D-0124's second addendum); the walk over facts stays as its reference.

   What the search then does with it is one rule, and it is sound by a one-line argument
   rather than by CDCL's progress argument:

       a branch nogood is a clause every literal of which is FALSE under the decisions in
       force. If it names no literal of level [lvl], it is already false under the
       decisions ABOVE [lvl] -- so it refutes the sibling branch too, which differs from
       this one only at [lvl], and the sibling need not be explored.

   Nothing is skipped that a valid clause does not already refute, so there is no
   completeness obligation to discharge and no resume loop to bound.

   The closure stays right, and not merely safe, when the learned row propagates (D-0056,
   task M2-L15). The nogood is a clause over DECISIONS, and a PB row's levels answer a
   question about falsification, not about dependence: the second bullet above,
   generalised one step. M2-L15 re-asked it once M2-L13 gave the learned PB row a
   runtime propagator, which made the premise of lib/core/pb_analysis.ml's closing note
   true and its question live. Measured over the 44 models: the two sets differ on 77 of
   103 conflicts and on 76 of those the PB set is a strict SUBSET, so the PB rule would
   jump too high, not too low. [Search]'s [config.backjump_on_pb] takes it and veripb
   rejects the nogood; see lib/core/search.ml's [pb_level_verdict].

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
   rejection, which is M2-L3's test (a2) -- see test/unit/test_learn.ml.

   A direct-encoding ([Lit.Eq]) literal, [x = v], has no ladder to read, because no
   [x = v] entails another (the order encoding, not the direct one, is what disequality
   and all_different reason over: D-0019, D-0040). It is never merged with anything,
   including another [Eq] literal on the same variable.

   [Analysis.add_node] already keeps the stronger of two facts about one slot, so a cut
   coming out of [Analysis] is already reduced and [minimise] is a no-op on it. The
   reduction is NOT idle: the branch nogood is built from the DECISION stack, and
   first-fail/indomain_min branches the same variable in the same direction at several
   levels along one path ([x >= 1] at one level, [x >= 2] at the next), so the nogood
   really does carry redundant thresholds and really is shortened here. That is where the
   break bites, and it bites on a shipped model rather than on a scene built for it.

   On the 1UIP cut itself this reduction removes nothing, as measured by M19-config-T6
   (D-0241): 0 literals of 135 million, over 230 Challenge instances at 20 000 nodes.
   What does shorten a learned clause is the other two kinds, which
   [Analysis.minimise_cut] removes before this reduction runs: literals FALSE AT THE ROOT
   (7 % of them) and literals the kept ones re-derive through the implication graph,
   MiniSat's recursive minimisation (17 % more). BAGUETTE_MINIMISE selects them (default
   off); the soundness argument is the header of [Analysis.minimise_cut]'s section.

   ---------------------------------------------------------------------------
   I-S4, discharged -- and what it turns out to be about
   ---------------------------------------------------------------------------

   I-S4 says a line citing a hole is supported only while the hole's own line is live, and
   docs/INVARIANTS.md records that it holds "by the level discipline rather than by a
   check", with the explicit note that the argument does not cover a learned clause citing
   across levels. This module produces exactly such a clause, so the check is owed here.

   It splits in two, because the two halves are not equally applicable:

     - LIVE AT DERIVATION. The learned clause is a [rup]: the checker verifies it against
       the database as it stands when it reads the line. Every hole line the cut folded in
       ([Analysis.folds]) must therefore be on the page at that moment. This is a real
       obligation, it is what forces the derivation to precede the wipe that retires its
       level ([Writer.wipe_level], explicit deletions standing in for the level wipe
       VeriPB 3.0 does not have, D-0024), and [support_check] below measures it rather
       than arguing it. It is the half test (b) breaks.
     - OUTLIVES. [Trace.i_s4_verdict]'s second half -- the cited line's level must be at
       or below the citing line's -- is the *proxy* the level discipline provides for
       "the cited line is still there when the citing line is used again". It does not
       apply to this clause, and saying why is the discharge rather than a waiver: a
       [rup] names no id. There is nothing for a deletion to dangle. A [pol] citing a
       hole line across levels WOULD be a violation, and the reduction steps of PB
       conflict analysis (M2-L6) are the first thing that could write one --
       [crossings] below reports the crossings as data so that the day a [pol] replaces
       this [rup], the numbers are already there.

   So [support_check] returns the liveness verdicts and [crossings] the level crossings,
   and the caller gates on the first and records the second.

   ---------------------------------------------------------------------------
   Determinism (M2-L3's test (f))
   ---------------------------------------------------------------------------

   No [Hashtbl] is iterated here and every list is built in a fixed order: [minimise]
   folds left and preserves first-appearance order, [levels] comes out of
   [Analysis.decision_levels] which sorts, and the nogood is ordered by descending level
   to match [Search]'s own decision stack. The tables below are looked up, never
   iterated. A learned database iterated in hash order is the specific way learning
   breaks `scripts/check_determinism.sh`; this module keeps no database, and the one that
   does, lib/core/retention.ml (M2-L4), inherits this obligation. *)

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

   The work is linear in the clause: one cell per slot, found through a table keyed by
   the slot, and the cells kept in first-appearance order. [minimise_with_reference] is
   the quadratic fold this replaced, kept as the specification test/unit/test_learn.ml
   checks this against, and the output is the same element for element: a slot's cell is
   created where the fold appended the slot's first literal, and every later literal of
   the slot replaces the cell's content exactly when the fold's [List.map] replaced it
   ([keep] does not return [m]). The table is only looked up, never iterated, so no
   output depends on its order.

   Why it matters: the branch nogood is as long as the decision stack (147 on mspsp, 226
   on openshop), once per conflict, and the fold appended with [acc @ [item]] and looked
   each slot up by a [List.map] over the whole accumulator with a POLYMORPHIC
   [slot m = Some s]. Replaced by M11-complexity-T4 (item S5 of D-0140's inventory of
   costs that grow with the run, D-0144).

   The table is created at the clause's length, and a slot hashes its name and adds the
   direction. It used to start at 16 and double, re-hashing every slot at each doubling,
   and [Hashtbl.hash] walked the pair: on 2011_roster, whose learned clauses are nearly
   all of 16 literals or more, this function was 6 % of the run's samples, a third of it
   the doublings (M16-file-review-T3, the file-by-file review of learning, D-0191).
   Neither change alters an answer, because the table is looked up, never iterated. *)
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

(* WHICH of [Analysis.minimise_cut]'s rules run, read once from BAGUETTE_MINIMISE (D-0241,
   which built these rules and kept the default [off] because the score did not move
   beyond the noise): [off] none, [root] the level-0 rule, [rec] the level-0 rule and the
   recursive one with the abstract-level filter, [local] the level-0 rule and the
   recursive one looking one step back only, [rec-nofilter] the recursive one without the
   filter (a measurement arm). Anything else FAILS, the discipline of BAGUETTE_CDCL: a
   run that silently used the default because the spelling was wrong is the trap
   CLAUDE.md records twice. The rules, and why the learned clause stays the `rup` it was,
   are in the header of [Analysis.minimise_cut]'s section. *)
type minimisation =
  | Min_off
  | Min_root
  | Min_rec
  | Min_rec_nofilter
  | Min_local
  | Min_break_unchecked
(* the break: [Analysis.min_config]'s [min_break_unchecked]. Tests only, so no
   spelling of BAGUETTE_MINIMISE selects it. *)

let default_minimisation = Min_off

let minimisation_name = function
  | Min_off -> "off"
  | Min_root -> "root"
  | Min_rec -> "rec"
  | Min_rec_nofilter -> "rec-nofilter"
  | Min_local -> "local"
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
  | Min_local ->
      { Analysis.min_off with min_root = true; min_recursive = true; min_local = true }
  | Min_break_unchecked -> { Analysis.min_off with min_break_unchecked = true }

let minimisation =
  ref
    (match Sys.getenv_opt "BAGUETTE_MINIMISE" with
    | None | Some "" -> default_minimisation
    | Some ("off" | "0") -> Min_off
    | Some "root" -> Min_root
    | Some ("rec" | "1" | "on") -> Min_rec
    | Some "rec-nofilter" -> Min_rec_nofilter
    | Some "local" -> Min_local
    | Some v ->
        prerr_endline
          (Printf.sprintf
             "baguette: BAGUETTE_MINIMISE=%S is not a setting. Use off, root, local, rec \
              or rec-nofilter."
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
  mutable ms_local : int; (* ... by the one-step (local) rule on top of [root] *)
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
    ms_local = 0;
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
    "minimise: setting=%s clauses=%d lits=%d root=%d rec=%d rec_nofilter=%d local=%d \
     dominated=%d learned=%d\n\
     minimise-hist-before: %s\n\
     minimise-hist-after: %s\n\
     %!"
    (minimisation_name !minimisation)
    s.ms_clauses s.ms_lits s.ms_root s.ms_rec s.ms_rec_nofilter s.ms_local s.ms_dominated
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
      (* [l_lits] with the decision level of each literal, in the same order. The CDCL
         loop reads its ASSERTING level off it (the second-highest level), which the
         decision closure's [l_levels] is not (M19-config-T10, D-0219). *)
  l_lbd : int;
      (* The retention score of lib/core/retention.ml (M2-L4): the number of distinct
         decision levels the MINIMISED clause's literals sit at -- Glucose's "literal
         block distance". Taken after minimisation on purpose: [minimise] merges two
         literals over one variable in one direction, and those two can sit at different
         levels, so an LBD read off the unminimised cut can be strictly larger than the
         clause's own. Computed here because this is where both the levels and the
         survivors are in hand; what is done with it is [Retention]'s business, not this
         module's. *)
  l_min_supports : int list;
      (* Trail positions of the entries the minimisation's removals rest on
         (M19-config-T6, D-0241). Their lines are what the checker replays to re-derive a
         dropped literal, so [supports] counts them. Empty when nothing was dropped. *)
}

let lits t = t.l_lits
let clause t = t.l_clause
let cut t = t.l_cut
let levels t = t.l_levels
let converts t = t.l_converts
let lbd t = t.l_lbd
let levelled t = t.l_levelled

(* Under BAGUETTE_MINIMISE_STATS, the counts [min_stats] accumulates for one learned
   clause: its width as the 1UIP walk left it, and at level 1 what each rule would remove
   from that same cut, whatever the setting. *)
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
    s.ms_local <- s.ms_local + (count Min_local - root);
    s.ms_dominated <-
      s.ms_dominated
      + (w - List.length (minimise_with policy (Analysis.lits_levelled raw))))

(* Analyse one conflict both ways: the 1UIP walk for the clause, and the decision closure
   for the levels the default search's backjump rests on. [None] when either walk fails
   or when the 1UIP walk produced nothing to learn; the caller then behaves exactly as it
   did without learning, which is why every arm here is a plain [None] and not an
   exception.

   The 1UIP postcondition is CHECKED rather than assumed: [Analysis] reports
   [stopped_by_criterion] precisely so that a caller can tell "the criterion said stop"
   from "the walk ran out of nodes first". The decision closure's postcondition holds by
   construction of [Analysis.dependency_levels], which computes the closure's level set
   over memoised citations rather than by re-walking the facts at every conflict
   (M7-T27 (a3), D-0124's second addendum); a closure that does not close is its
   [Error], and not a dependency set.

   [~closure:false] skips the decision closure and leaves [l_levels] empty
   (M19-config-T10, D-0219, the CDCL loop). That loop backjumps on the clause's own
   asserting level and never reads the closure, so it does not pay for the second walk,
   and an [Error] of that walk does not cost it the clause. The default is the walk.

   [?minimisation] picks [Analysis.minimise_cut]'s rules, applied to the 1UIP cut after
   its postcondition is checked and before [minimise] (M19-config-T6, D-0241); the
   default is [!minimisation], BAGUETTE_MINIMISE's. [l_cut] is the cut as minimised. *)
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
               unchanged by computing [l_lbd] from it. [test_learn.ml]'s
               [minimise_agrees_with_levelled] pins that equality rather than leaving it
               as a claim in this comment. *)
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

(* Put the learned clause on the page as a `rup` at level 0, through [Learned.introduce]
   (M2-L1), so that the backjump that follows does not wipe it.

   I-X2 (every constraint id is deleted exactly once): the id handed back is an id the
   caller must delete. The caller hands it to lib/core/retention.ml, which deletes it on
   eviction, and [Search.solve] sweeps what is left with [Retention.retire_all] before
   the conclusion.

   The origin, a comment kept per live id by the audit and matched by the mutation knob,
   is built only for a writer that keeps it. The null writer of a --no-proof run
   ([Writer.is_null]) drops [~origin] unread in [Writer.fresh], so rendering every
   literal of every learned clause into a string there was work nothing read. A writer
   that writes keeps it, so it is built exactly as before. The writer has had lazy forms
   since D-0145 ([Writer.rup_lazy]), but [Learned.introduce] takes a string, so the test
   stays here. The origin is never written to the .pbp, so neither arm can change a byte.
   Introduced by M11-complexity-T4 (item J6 of D-0140's inventory, D-0144). *)
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
   line, and that line's level. [s_hole] is the removed run [(a, b)] of a hole line
   ([(v, v)] for one hole, a bulk entry's gap since D-0269) and [None] for a bound line. *)
type support = {
  s_hole : (int * int) option;
  s_var : string;
  s_cid : Writer.cid;
  s_level : int;
}

let support_of_written (w : Trace.written) ~var =
  {
    s_hole = w.Trace.w_hole;
    s_var = var;
    s_cid = w.Trace.w_cid;
    s_level = w.Trace.w_level;
  }

(* Every line the 1UIP cut's derivation rests on.

   THREE sources, and taking only the last would be taking I-S4's phrasing for its
   substance:

     - the line behind every node's SUPPORTING ENTRY. The learned clause is a [rup]: the
       checker re-derives it by unit propagation over the database as it stands, and what
       it propagates along are exactly the trace lines of the entries the walk resolved
       (D-0021: every pruning has a trace line; D-0039: those lines are RUP in sequence,
       not
   standalone). Retire one and the [rup] is checked against a database that no
       longer contains what makes it true.
     - the line behind every entry a minimisation removal rests on ([l_min_supports]):
       the checker replays those lines to re-derive a literal the minimisation dropped.
     - the HOLE line behind every fold ([Analysis.folds]). This is the set I-S4 is
       literally about, and it is a subset of what the derivation needs rather than the
       whole of it.

   A line this module cannot name is not reported, because that is the case I-S4 has
   nothing to say about: the step rests on the model's own rows, against which every
   trace line is RUP (I-X10), and no level wipe can retire a model row.
   [Trace.settle_facts] makes the same distinction for the same reason.

   Deduplicated by id, in first-seen order -- one entry can support several nodes. The
   ids already taken are a table and the list is built reversed and reversed once, which
   keeps the work linear on every learned clause (the I-S4 check is always on). It was a
   [List.exists] over the list so far and an [acc @ [s]], quadratic in the number of
   supports (M11-complexity-T4, item L1 of D-0140's inventory, D-0144). *)
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
  | Some (h, h') when h = h' -> Printf.sprintf "the hole %s <> %d" s.s_var h
  | Some (a, b) -> Printf.sprintf "the gap %s not in %d..%d" s.s_var a b
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
   clause rests on. NOT a violation -- see the header -- and reported so that a [pol] of
   PB conflict analysis (M2-L6), for which it WOULD be one, does not have to discover the
   numbers. *)
let crossings (ss : support list) = List.filter (fun s -> s.s_level > 0) ss
