(* analysis.ml: the implication graph and the cut, AS DATA (M2-L2, D-0044).

   Consistency level: none -- this is not a propagator. Spec section: none yet; the
   governing record is docs/DECISIONS.md D-0044 and its 2026-09-18 amendment.

   ---------------------------------------------------------------------------
   What this module does, and the four things it deliberately does NOT do
   ---------------------------------------------------------------------------

   [analyse] walks back from a [Store.conflict] through the implication graph and
   returns a CUT: a list of bound facts whose conjunction is inconsistent with the
   model. The clause a later row will learn is the negation of that conjunction, i.e.
   [lits] below; the PB inequality M2-L1 will learn is the same object at degree 1
   (D-0044: "a clause is the degree-1, unit-coefficient case").

   It learns nothing, it backjumps nowhere, it attaches nothing to the engine and it
   emits no proof line. M2-L2 is split from M2-L3 precisely so that the cut can be
   checked against a brute-force oracle before anything depends on it. Four consequences
   worth stating, because each is a thing a reader will look for and not find:

     - no [Writer] call and no dependency on lib/proof beyond [Lit] (which is data);
     - no mutation of the store: [analyse] takes it and reads it. The one exception
       since M7-T27 (a3) is [dependency_levels], which writes a MEMO onto each entry it
       reaches ([Store.entry.cites]): what that entry's reason cites, which the entry
       already states and which cannot change while it is on the trail. See the last
       section of this file;
     - no [Reason.justified] is CONSTRUCTED here. This module consumes reasons that
       propagators built; it never builds one;
     - no registration with [Engine].

   ---------------------------------------------------------------------------
   The graph: three edges, each an existing O(1) question
   ---------------------------------------------------------------------------

   A node is a [Reason.fact] -- one bound, frozen at the value a propagator read (see
   lib/core/reason.ml on why it is frozen: I-X6 is discharged by the type on this half,
   and nothing here reads a live domain to decide what a reason says).

     - "which trail entry established this bound?"  [Store.lo_support]/[hi_support],
       O(1), M2-T8. See [support_of] for the one case where it is not the answer and
       [Store.bound_support]'s binary search over the bound's history is (M6-T14).
     - "which constraint made that entry?"          [Store.entry]'s [prop], M2-T7/I-T4.
     - "which bounds did that constraint read?"     the entry's [Reason.t], walked by
       [Reason.owners]' sibling logic without materialising a [Lit.t].

   ---------------------------------------------------------------------------
   Why the support is not always [lo_support], and why that is not a regression
   ---------------------------------------------------------------------------

   [lo_support v] names the entry that established v's CURRENT lower bound. The facts a
   reason states are frozen at older, weaker values, and a later entry may have pushed
   the bound further. Resolving [x >= 3] against the entry that established [x >= 7]
   would be sound (it derives something stronger, which still implies the fact) but it
   would walk UP the trail, and the walk would not terminate.

   So [support_of] takes a [~before] bound -- the trail position of the entry whose
   reason produced the fact -- and asks for the entry that established the fact STRICTLY
   BELOW it. [lo_support] is tried first and is the answer in the common case (nothing
   moved the bound again between the read and the conflict); when it is not, the unique
   entry that pushed the bound past [value] is found -- it exists and is unique because
   bounds are monotone within a level (I-D3) and [undo_to] pops entries whose effect is
   gone. Until M6-T14 that was a downward scan of the trail, once per fact per step, so
   quadratic in trail depth over an analysis; it is now [Store.bound_support], a binary
   search over the variable's bound history (D-0088), with the scan kept as a
   [BAGUETTE_DEBUG] cross-check. [o1_supports] and [scanned_supports] count the two
   paths ([scanned] now meaning "the history answered"), so a test can assert the O(1)
   path is the one actually taken rather than assuming it.

   That [~before] discipline is also the termination argument: every fact a resolution
   step introduces has a support strictly below the step's own, so the largest expandable
   support strictly decreases and the walk stops in at most one step per trail entry.
   [max_resolutions] is a belt-and-braces cap on top of that argument, not instead of it.

   ---------------------------------------------------------------------------
   Roots: what is never expanded
   ---------------------------------------------------------------------------

   A node is a ROOT, kept in the cut and never resolved away, when

     - it has no supporting entry at all (the bound is still the declared one -- it
       materialises to no literal, [Reason.lit_of_fact] returns [None], and it is in the
       cut only so that [Reason.owners]' notion of scope survives the walk); or
     - its supporting entry rests on no facts ([Reason.is_empty]) AND is either a level
       start or settled over no hole ([rests_on_nothing]). That is a DECISION (search.ml
       pushes [Reason.none] beside [Explanation.decision] -- D-0018/D-0037), a constraint
       posted at this level, or a pruning that genuinely follows from a model row alone
       -- a learned unit or an improving bound re-applied by [Search.apply_globals] is
       the common one.

   A factless pruning that SETTLED over a hole is not a root (M7-T31, D-0148). Its trace
   line claims the bound the trail landed on and cites the facts of every hole it walked
   over ([Trace.settle_facts]), so it rests on those holes exactly as a propagator's
   settle does, and it is expanded the same way: into the reasons of the holes' removers
   (see "Holes" below). Treated as a root it pinned its own level and dropped the levels
   the holes rest on, and on 2017_hrc_exp1-1-5670 a learned unit re-applied at level 61
   that settled over a hole punched at level 41 left level 41 out of a branch nogood the
   checker then refused. A DECISION that settles stays a root: it is assumed, and the
   settle step is [Search.bridges]' line, with its own protection of the levels below.

   Keeping the last kind rather than dropping it is the conservative choice and it is
   deliberate. Dropping a node that "rests on nothing" would give a shorter, stronger
   clause -- and would be WRONG for a decision, which rests on nothing precisely because
   it is assumed rather than derived. There is no way to tell the two apart from the
   reason alone ([Store.is_level_start] distinguishes a decision from a mid-level
   factless pruning, and [factless] reports the latter for anyone who wants to look;
   I-P5's history -- [Store.remove] and [Store.fix] recording [no_facts] silently from
   M1-T9 to M1-T17 -- is why that list is reported rather than assumed empty).

   ---------------------------------------------------------------------------
   Holes: the fold, and why it is not a special case of anything
   ---------------------------------------------------------------------------

   An [int_ne] removal claims a CLAUSE ([Encoding.ne_clause_lits], M1-T56) and not a
   literal, so it is non-asserting: there is no single order literal for "x <> v" and a
   hole therefore cannot be a graph node in the usual way. The documented rule is to fold
   the hole's reason into the bound move that CONSUMED it -- which is exactly the shape
   [Store.lo_reasons]/[hi_reasons] already has for the proof side (M1-T44, I-X9): the
   entry that moved the bound, plus one contribution per hole [Domain.settle] walked
   over. [expand] does the same walk over [Store.settled_over_lo]/[settled_over_hi] and
   [Store.remover], and records every fold it performs in [folds].

   It is recorded rather than merely performed because a hole dropped silently is
   invisible: the cut still looks well formed, still holds on the trail, and is simply
   over too few facts. Test (d) of this row asserts the fold FIRED, and separately that
   the cut without the folded facts is not a valid nogood.

   ---------------------------------------------------------------------------
   The stopping criterion is a COMPONENT, and 1UIP is not a property of the cut
   ---------------------------------------------------------------------------

   D-0044's amendment of 2026-09-18 is the reason [criterion] is a record rather than a
   constant. Learning the first assertive clause gives the highest backjump IN A SAT
   SOLVER; Le Berre et al. (arXiv 2107.13085) state there is no such guarantee in the
   presence of PB constraints, because a PB constraint propagates by SLACK rather than by
   "all but one literal falsified" -- so a derived constraint can carry SEVERAL
   conflict-level literals and still be asserting. The clausal stopping rule does not
   merely do worse there; it measures the wrong thing.

   Therefore each criterion carries its OWN [postcondition]. "Exactly one literal from
   the conflict level" is [one_uip]'s postcondition and nobody else's. M2-L6 plugs in a
   slack-based criterion with a postcondition of its own and the 1UIP assertion cannot
   redden for it, because it is not stated about the cut -- it is stated about the
   criterion that produced the cut. Writing it as an invariant of [t] would have been
   writing it at the wrong altitude.

   [conflict_side] is here as the second criterion for the same reason a second
   implementation always is: a component with one instance is a constant wearing a
   record. It stops immediately, so its cut is the conflicting constraint's own reason,
   unexpanded -- trivially sound, non-asserting, and carrying as many conflict-level
   literals as the conflict had. It is the shape M2-L6 must be free to accept.

   ---------------------------------------------------------------------------
   Determinism, and one note for M2-L3
   ---------------------------------------------------------------------------

   Every list here is built in a fixed order and no [Hashtbl] is iterated: the gate
   requires two runs to produce byte-identical output and a cut accumulated in a hash set
   is the textbook way to lose that.

   For M2-L3: each node records the [level] at which its bound was established, and
   [cited_levels]/[backjump_level] read them. I-S4 -- a cited hole line must outlive the
   line citing it -- holds today by an argument about the level discipline that
   EXPLICITLY does not cover a learned clause citing across levels, which is what this
   cut becomes. Nothing here can violate it, because nothing here emits a line; but the
   per-node level is recorded so that whoever takes M2-L3 can check it without walking
   the trail a second time. That check is M2-L3's debt, not this row's. *)

module Lit = Baguette_proof.Lit

(* ------------------------------------------------------------------ facts *)

(* [Reason] exposes the owner and the direction of a fact but not its value, which the
   walk needs to ask "did this entry establish it?". Matched with [_] so that a field
   added to [Reason.fact] is not a compile error here. *)
let fact_value = function
  | Reason.At_least { value; _ } | Reason.At_most { value; _ } -> value

(* ------------------------------------------------------------------ the cut *)

(* One literal of the cut, with everything the walk learned about where it came from.

   [support] is the trail position of the entry that established this bound, or
   [Store.no_support] when it is still the declared one. [implied_by] is that entry's
   [prop] (M2-T7) -- the constraint that implied the bound -- or [Store.no_prop].
   [level] is the decision level that entry belongs to, or 0 when there is no entry.

   [root] is "this node is never resolved away" -- see the header. It is recorded on the
   node rather than recomputed because a [criterion]'s postcondition is shown the nodes
   and not the store, deliberately: a criterion that could reach the store could read
   live state, which is the wrong side of I-X6's line. *)
type node = {
  fact : Reason.fact;
  level : int;
  support : int;
  implied_by : int;
  root : bool;
  slot : int;
      (* [2 * v + 1] for a lower bound and [2 * v] for an upper one, [v] the variable the
         store names [fact]'s owner ([Store.var_named], read once by [locate]), or -1
         when the store knows no such name. The KEY [Frontier] merges on: two facts share
         a slot iff they share a name and a direction (D-0191). *)
}

(* One hole folded into a bound move, per the rule in the header. [fold_into] is the
   trail position of the bound move that consumed the hole; [fold_prop] is the instance
   that punched it. *)
type fold = { fold_var : string; fold_value : int; fold_prop : int; fold_into : int }

type t = {
  nodes : node list;
      (* The cut. The CONJUNCTION of these facts is inconsistent with the model; the
         clause to learn is their negation, [lits]. *)
  conflict_level : int;
  conflict_prop : int;
  criterion_name : string;
  stopped_by_criterion : bool;
      (* [false] means the walk ran out of expandable nodes before the criterion said
         stop. The cut is still sound; the criterion's postcondition may not hold, and a
         caller that cares is expected to look rather than to assume. *)
  antecedents : int list;
      (* Every propagator instance the cut RESTS ON: the conflicting one, every entry
         resolved away, and every hole-punching entry folded in. I-X10 says a pruning
         that rests on several model rows owes an explicit derivation (D-0040); this is
         the list of rows M2-L3 owes it over. First-seen order. *)
  folds : fold list;
  factless : int list;
      (* Trail positions of root entries that rest on no facts and are NOT a level start,
         i.e. not decisions. A search that pushes one decision per level never produces
         one; a second constraint posted at a level already open does, and so would the
         I-P5 shape that let [int_ne] prune factlessly from M1-T9 to M1-T17. Reported
         rather than assumed empty, because that defect was invisible for eight tasks. *)
  resolutions : int;
  o1_supports : int;
  scanned_supports : int;
}

type error =
  | Misattributed of { at : int; claimed : int; var : string }
    (* [entry.prop] at trail position [at] names an instance that does not exist or
       does not watch [var]. The graph is corrupt: M2-L3 would derive the learned
       clause over the wrong model row. *)
  | Diverged of int

let error_to_string = function
  | Misattributed { at; claimed; var } ->
      Printf.sprintf
        "Analysis: trail entry %d credits instance %d, which does not watch %s" at claimed
        var
  | Diverged n -> Printf.sprintf "Analysis: did not terminate after %d resolutions" n

(* ------------------------------------------------------- the criterion *)

(* What a criterion is shown. Deliberately the nodes and the conflict level and nothing
   else: a criterion that needed the store would be a criterion that could read live
   state, which is the wrong side of I-X6's line. M2-L6's slack criterion needs the
   coefficients of the constraint under construction, which is a field to add to this
   view when M2-L1's [Learned.t] exists -- not a store. *)
type view = {
  v_nodes : node list Lazy.t;
  v_conflict_level : int;
  v_at_conflict_level : int;
      (* How many of [v_nodes] sit at [v_conflict_level]. D-0152 (D-0140 A1): carried so
         [one_uip] stops on a count the walk keeps, and [v_nodes] is lazy so that a
         criterion that reads only the count never has the list built. *)
}

(* The view of a finished node list, counted here. *)
let view_of nodes ~conflict_level =
  {
    v_nodes = Lazy.from_val nodes;
    v_conflict_level = conflict_level;
    v_at_conflict_level =
      List.length (List.filter (fun n -> n.level = conflict_level) nodes);
  }

(* [stop] decides when the walk ends. [postcondition] is what THIS criterion guarantees
   about the cut it produced, and it is the only place a rule like 1UIP may be written
   down. See the header. *)
type criterion = { crit_name : string; stop : view -> bool; postcondition : view -> bool }

let count_at_conflict_level v = v.v_at_conflict_level

(* The clause path (M2-L3): resolve conflict-level facts away until one is left. The
   postcondition is the 1UIP rule and it is scoped to this value. *)
let one_uip =
  {
    crit_name = "1UIP";
    stop = (fun v -> count_at_conflict_level v <= 1);
    postcondition = (fun v -> count_at_conflict_level v <= 1);
  }

(* The conflicting constraint's own reason, unexpanded. Sound, non-asserting, and it may
   carry several conflict-level literals -- which is exactly why it is here: it is the
   standing proof that [one_uip]'s postcondition is a property of [one_uip] and not of
   the cut. It guarantees nothing about levels and says so. *)
let conflict_side =
  { crit_name = "conflict-side"; stop = (fun _ -> true); postcondition = (fun _ -> true) }

(* The other end: resolve until every conflict-level node is a root, i.e. until the cut
   is over the assumptions themselves. This is what M1's [Search] already learns without
   any analysis at all (D-0018's branch nogood over the negated decisions), so it is the
   baseline any cut has to beat rather than a candidate for M2-L3 -- and it is the third
   value that makes [criterion] a component with a range rather than a two-valued flag.
   Its postcondition is its own and says nothing about counts. *)
let every_conflict_level_node_is_a_root v =
  List.for_all (fun n -> n.level <> v.v_conflict_level || n.root) (Lazy.force v.v_nodes)

let decision_cut =
  {
    crit_name = "decision-cut";
    stop = every_conflict_level_node_is_a_root;
    postcondition = every_conflict_level_node_is_a_root;
  }

(* The FULL closure: resolve every non-root node away, at every level, until the cut is
   over roots alone. Used with [~scope:Everywhere] below and with nothing else -- under
   the default scope the walk cannot expand a node below the conflict level, so this
   criterion would simply never be satisfied and [stopped_by_criterion] would report
   [false]. [analyse] says so rather than leaving it to be discovered.

   M2-L3 needs it and [decision_cut] is not it. [decision_cut] stops when every
   CONFLICT-LEVEL node is a root and leaves the lower levels unexpanded, so the set of
   levels its cut names is NOT a dependency set: a node at level j that is not a root
   rests on further facts, at unknown levels, that the cut does not name. A backjump that
   skipped a level on that basis would skip a branch nothing had refuted. This criterion
   resolves until no such node is left, so every node IS a decision, a declared bound or
   a factless pruning that settled over no hole, and the levels it names really are the
   levels the conflict rests on. See lib/core/learn.ml for the argument written out.

   LEVEL 0 IS NOT EXPANDED (M7-T27 (a2), D-0124 addendum). A node at level 0 rests on
   level-0 facts only -- its support entry precedes every level mark, and so does every
   entry its reason cites ([support_of]'s [~before]) -- so expanding it can add nothing
   but level-0 nodes, and level 0 is what [decision_levels] drops. The set of levels the
   closure names is therefore the same whether level 0 is resolved away or kept as it
   stands, and the postcondition says exactly that: every node ABOVE level 0 is a root.
   Measured reason: on pattern-set-mining the closure re-expanded every root-level
   Linear entry at every conflict, 146 055 reason materialisations of ~3 600 facts in
   300 s, 13% of the nodes; since D-0124 a reason is rebuilt on each ask, so that was
   the whole of (a)'s time cost. *)
let every_node_above_root_is_a_root v =
  List.for_all (fun n -> n.root || n.level = 0) (Lazy.force v.v_nodes)

let decision_closure =
  {
    crit_name = "decision-closure";
    stop = every_node_above_root_is_a_root;
    postcondition = every_node_above_root_is_a_root;
  }

let criteria = [ one_uip; conflict_side; decision_cut; decision_closure ]

(* Which nodes the walk is allowed to resolve away.

   [At_conflict_level] is M2-L2's own and the default: 1UIP and its siblings only ever
   need to resolve the conflict level, and expanding below it would make every cut the
   decision closure. [Everywhere] is M2-L3's, for [decision_closure] above, and since
   M7-T27 (a2) it means every level ABOVE 0: see [decision_closure] for why level 0 adds
   nothing to a dependency set, and note that a root CONFLICT (conflict level 0) under
   the default scope still resolves level 0, as 1UIP at the root always did. The
   termination argument is unchanged and does not depend on which one is in force: every
   fact a resolution introduces has a support strictly below the step's own
   ([support_of]'s [~before]), so the largest expandable support strictly decreases
   whatever the set of expandable nodes is. *)
type scope = At_conflict_level | Everywhere

(* A slot ([2 * variable + direction], so a non-negative int) as a table key: the
   identity is its hash and [Int.equal] its comparison. M16-file-review-T3 (D-0191): the
   decision closure's cell table was a polymorphic [(int, int) Hashtbl.t], a [caml_hash]
   and a [compare_val] per probe and a re-hash of every cell at each doubling, and
   [Frontier] hashed a fact's NAME, a string, at every merge and removal. Neither table is
   iterated in an order that reaches an output: the closure's is folded into a list the
   caller sorts, the frontier's is only looked up. *)
module Slot_tbl = Hashtbl.Make (struct
  type t = int

  let equal = Int.equal
  let hash x = x land max_int
end)

(* ------------------------------------------------------- the walk *)

(* Did [e] establish [value] in this direction? True for exactly one entry per
   (variable, direction, value) that is still live, by I-D3's monotonicity. The predicate
   lives in [Store] since M6-T14 so that the history search and this scan share it. *)
let establishes = Store.establishes

(* The downward trail walk [support_of] used until M6-T14 (D-0088): the newest entry
   strictly below [before] on a variable of [v]'s name that establishes [value]. Linear
   in the trail, once per fact per resolution step, so quadratic in trail depth over an
   analysis -- the walk the 2014_mario / 2023_chessboard profiles put at the top.
   [Store.bound_support] answers the same question by binary search over the variable's
   bound history; this scan survives for one wave as the [BAGUETTE_DEBUG] cross-check in
   [support_of] and as test_analysis's oracle, and is otherwise dead.

   [v] is [Store.var_named store name]. M6-T11 (D-0085): the scan used to compare
   [String.equal (Store.name store e.var) name] at every entry -- D-0080 measured ~60 % of
   2016 prize-collecting's self time in it. [Store.name_rep] maps each entry's variable to
   the first variable of its name, so the integer test below holds on exactly the entries
   the string test did, duplicate names included. *)
let scan_support store ~before ~v ~is_lower ~value =
  let rec go i =
    if i < 0 then Store.no_support
    else
      let e = Store.trail_entry store i in
      if Var.equal (Store.name_rep store e.Store.var) v && establishes e ~is_lower ~value
      then i
      else go (i - 1)
  in
  go (min (before - 1) (Store.trail_length store - 1))

(* The trail position that established [fact], looking strictly below [before]. Returns
   the position, whether the O(1) array answered it ([false]: the bound history did), and
   the fact's slot (see [node]), which the variable found on the way gives for free. See
   the header. *)
let locate store ~before fact =
  let name = Reason.fact_owner fact in
  let is_lower = Reason.fact_is_lower fact in
  let value = fact_value fact in
  match Store.var_named store name with
  | None -> (Store.no_support, false, -1)
  | Some v ->
      let slot = (2 * Var.to_int v) + if is_lower then 1 else 0 in
      let fast =
        if is_lower then Store.lo_support store v else Store.hi_support store v
      in
      if
        fast <> Store.no_support && fast < before
        && establishes (Store.trail_entry store fast) ~is_lower ~value
      then (fast, true, slot)
      else
        let at = Store.bound_support store ~before v ~is_lower ~value in
        Debug.check "M6-T14: the bound history agrees with the trail scan" (fun () ->
            at = scan_support store ~before ~v ~is_lower ~value);
        (at, false, slot)

(* [locate] without the slot. *)
let support_of store ~before fact =
  let at, fast, _ = locate store ~before fact in
  (at, fast)

(* Is the entry at trail position [p] a ROOT: does its trace line rest on nothing a
   decision supports? A decision does by definition. A pruning without facts does only if
   its bound move walked over no hole, because a settle's line cites the holes' facts
   ([Trace.settle_facts]) and so rests on whatever punched them (M7-T31, D-0148; see the
   header's "Roots"). Both bounds are asked: an entry that moved neither, or moved one
   onto a value its old domain held, settled over nothing. *)
let rests_on_nothing store p (e : Store.entry) =
  Reason.is_empty e.Store.reason
  && (Store.is_level_start store p
     || Store.settled_over_lo e.Store.old ~cur:(Domain.lo e.Store.now) = []
        && Store.settled_over_hi e.Store.old ~cur:(Domain.hi e.Store.now) = [])

let same_slot a b =
  String.equal (Reason.fact_owner a.fact) (Reason.fact_owner b.fact)
  && Reason.fact_is_lower a.fact = Reason.fact_is_lower b.fact

(* Of two facts about the same bound of the same variable, the one that implies the
   other: the order encoding's ladder makes [x >= 5] entail [x >= 4], so keeping only the
   strongest is sound and strictly shortens the learned clause. This is the cheap half of
   the semantic minimisation M2-L3 owes in full; it is here because without it the 1UIP
   count would see two thresholds for one variable as two conflict-level literals. *)
let stronger a b =
  if Reason.fact_is_lower a.fact then
    if fact_value a.fact >= fact_value b.fact then a else b
  else if fact_value a.fact <= fact_value b.fact then a
  else b

let add_node nodes n =
  let found = ref false in
  let out =
    List.map
      (fun m ->
        if same_slot m n then (
          found := true;
          stronger m n)
        else m)
      nodes
  in
  if !found then out else out @ [ n ]

(* [add_node] above is the SPECIFICATION of the frontier merge and stays as the reference
   a test compares against; [Frontier] is what [analyse] runs (M6-T16, D-0092).

   [List.fold_left (fun acc f -> add_node acc (mk f)) rest facts] is O(|rest| * |facts|)
   per resolution step: every [add_node] maps the whole frontier and then appends with
   [@]. On 2014_mario that was the top of the profile after M6-T15 (D-0090). [Frontier]
   computes the same sequence with one hash lookup per incoming fact:

     - the frontier is a list of CELLS in frontier order, and a per-bound table from the
       variable's name to its cell, so "is this slot already in the frontier?" is O(1);
     - a fact whose slot is present merges INTO the cell, in place, as the [stronger] of
       the two -- and on a tie [stronger m n] keeps the EXISTING [m], exactly as
       [add_node] does;
     - a fact whose slot is new gets a new cell appended after every existing one, in
       first-arrival order; later facts for that slot merge into it and do not move it.
       FIRST OCCURRENCE WINS the position; [stronger] decides the content;
     - [remove] (the node a resolution step expands) drops the cell AND its table entry,
       so a later fact on that slot is a new slot appended at the end -- which is what
       [List.filter] followed by [add_node] did.

   A first version (in this same row) rebuilt a polymorphic [(string * bool) Hashtbl]
   from the whole frontier at every step. It was byte-identical and 1.36x on mario, and
   0.91x on 2023_chessboard: [caml_hash] and [compare_val] on the tuple keys, re-hashing
   every frontier node every step, cost more than the short [String.equal] scans they
   replaced. The table here persists across the walk, is keyed on the bare name with a
   monomorphic [String] table per bound direction, and hashes only incoming facts.
   M16-file-review-T3 (D-0191): keyed on the node's [slot] instead, an int [locate]
   computes from the variable it looks up anyway, so a merge or a removal no longer
   hashes the name; the name tables remain for a node without a slot.

   [mk] is applied to the facts in order, once each, so [mk_node]'s counters and its
   [Bad] exception fire in the same order as before.

   M11-complexity-T4 (D-0152, D-0140 A1): THE 1UIP LOOP WITHOUT A PASS OVER THE FRONTIER
   PER RESOLUTION. Each step used to rebuild the node list ([nodes], a [List.map]), count
   its conflict-level nodes for [one_uip] (a filter and a length), fold it for the
   expandable node of largest support, append the fresh cells with [@] and filter the
   expanded cell out: five passes over the frontier per step, so a conflict cost its
   resolutions times its frontier. Now:

     - a cell carries its creation number [seq], and a removed cell is marked dead and
       left where it is. [rev_cells] is every cell ever made, newest first, so the live
       ones in [seq] order are the old [cells] list exactly: cells were only ever
       appended in creation order and filtered out;
     - [at_level] counts the live cells whose node sits at [conflict_level], kept at the
       three places a cell's node changes (created, merged, removed). It is the count
       [one_uip] stops on, which [view] now carries;
     - [best] is a max-heap of (support, seq) over the expandable nodes, pushed whenever
       a cell takes a node, and cleaned lazily: an entry is current while its cell is
       live and still holds that very node (a node is never re-used, [mk] builds a new
       one per fact, so physical equality cannot see an old node come back). Its top is
       the expandable node of largest support, ties to the smallest [seq], i.e. the
       EARLIEST cell -- which is what the fold over the cells returned, since it kept the
       first of equal supports.

   [remove] finds the cell through the table, where it filtered the list. Under
   BAGUETTE_DEBUG [analyse] checks the count and the heap's answer against the passes
   they replaced, at every step. [create ()] with no level and no [expandable] keeps the
   old merge-only behaviour, which test_analysis.ml compares against [add_node]. *)
module Frontier = struct
  (* The table keyed by a name, [String.equal] and [String.hash] (D-0236). *)
  module H = Baguette_proof.Name_tbl

  type cell = { mutable cur : node; seq : int; mutable alive : bool }
  type entry = { e_support : int; e_seq : int; e_cell : cell; e_node : node }

  type t = {
    slots : cell Slot_tbl.t;
    lo : cell H.t;
    hi : cell H.t;
    mutable rev_cells : cell list;
    mutable next_seq : int;
    conflict_level : int;
    expandable : node -> bool;
    mutable at_level : int;
    mutable heap : entry array;
    mutable heap_n : int;
  }

  let create ?(conflict_level = min_int) ?(expandable = fun _ -> false) () =
    {
      slots = Slot_tbl.create 64;
      lo = H.create 8;
      hi = H.create 8;
      rev_cells = [];
      next_seq = 0;
      conflict_level;
      expandable;
      at_level = 0;
      heap = [||];
      heap_n = 0;
    }

  (* A node's cell, keyed by its slot, or by its name and direction when it has none
     (a name the store does not know, or a test's hand-built node). The two never meet:
     a name has a slot in every node or in none. *)
  let table f n = if Reason.fact_is_lower n.fact then f.lo else f.hi

  let find f n =
    if n.slot >= 0 then Slot_tbl.find_opt f.slots n.slot
    else H.find_opt (table f n) (Reason.fact_owner n.fact)

  let bind f n c =
    if n.slot >= 0 then Slot_tbl.replace f.slots n.slot c
    else H.replace (table f n) (Reason.fact_owner n.fact) c

  let unbind f n =
    if n.slot >= 0 then Slot_tbl.remove f.slots n.slot
    else H.remove (table f n) (Reason.fact_owner n.fact)

  let nodes f =
    List.fold_left (fun acc c -> if c.alive then c.cur :: acc else acc) [] f.rev_cells

  let at_conflict_level f = f.at_level

  (* [a] comes out of the heap before [b]. *)
  let above a b =
    a.e_support > b.e_support || (a.e_support = b.e_support && a.e_seq < b.e_seq)

  let push f c =
    let n = c.cur in
    if f.expandable n then (
      let e = { e_support = n.support; e_seq = c.seq; e_cell = c; e_node = n } in
      if f.heap_n = Array.length f.heap then (
        let bigger = Array.make (Stdlib.max 16 (2 * f.heap_n)) e in
        Array.blit f.heap 0 bigger 0 f.heap_n;
        f.heap <- bigger);
      let i = ref f.heap_n in
      f.heap_n <- f.heap_n + 1;
      while !i > 0 && above e f.heap.((!i - 1) / 2) do
        f.heap.(!i) <- f.heap.((!i - 1) / 2);
        i := (!i - 1) / 2
      done;
      f.heap.(!i) <- e)

  let pop_top f =
    f.heap_n <- f.heap_n - 1;
    let last = f.heap.(f.heap_n) in
    let i = ref 0 and placed = ref false in
    while not !placed do
      let l = (2 * !i) + 1 and r = (2 * !i) + 2 in
      let b = if l < f.heap_n && above f.heap.(l) last then l else !i in
      let b =
        if r < f.heap_n && above f.heap.(r) (if b = !i then last else f.heap.(b)) then r
        else b
      in
      if b = !i then (
        if !i < f.heap_n then f.heap.(!i) <- last;
        placed := true)
      else (
        f.heap.(!i) <- f.heap.(b);
        i := b)
    done

  (* The expandable node of largest support, ties to the earliest cell, or [None]. *)
  let rec best f =
    if f.heap_n = 0 then None
    else
      let e = f.heap.(0) in
      if e.e_cell.alive && e.e_cell.cur == e.e_node then Some e.e_node
      else (
        pop_top f;
        best f)

  let level_count f n = if n.level = f.conflict_level then 1 else 0

  let add_all f facts ~mk =
    List.iter
      (fun x ->
        let n = mk x in
        match find f n with
        | Some c ->
            let s = stronger c.cur n in
            if s != c.cur then (
              f.at_level <- f.at_level - level_count f c.cur + level_count f s;
              c.cur <- s;
              push f c)
        | None ->
            let c = { cur = n; seq = f.next_seq; alive = true } in
            f.next_seq <- f.next_seq + 1;
            bind f n c;
            f.rev_cells <- c :: f.rev_cells;
            f.at_level <- f.at_level + level_count f n;
            push f c)
      facts

  (* Drop [n]'s cell, as [analyse]'s [List.filter] on slot AND value did. The frontier
     holds one cell per slot, so this removes [n]'s slot whenever [n] is in it. *)
  let remove f n =
    match find f n with
    | Some c when fact_value c.cur.fact = fact_value n.fact ->
        c.alive <- false;
        f.at_level <- f.at_level - level_count f c.cur;
        unbind f n
    | Some _ | None -> ()
end

(* An insertion-ordered set of ints: [to_list] is the elements in FIRST-OCCURRENCE order,
   which is what [if not (List.mem p l) then l @ [ p ]] produced, in O(1) per [add]
   instead of O(length). [analyse]'s antecedent list (M6-T16). *)
module Uniq = struct
  type t = { seen : (int, unit) Hashtbl.t; mutable rev : int list }

  let create () = { seen = Hashtbl.create 16; rev = [] }

  let add u p =
    if not (Hashtbl.mem u.seen p) then (
      Hashtbl.replace u.seen p ();
      u.rev <- p :: u.rev)

  let to_list u = List.rev u.rev
end

exception Bad of error

(* The one place [entry.prop] is READ rather than carried, shared by [analyse] and
   [dependency_levels]. An id that names no instance, or an instance that does not watch
   the variable the entry changed, is a corrupt graph and stops the walk -- it does not
   produce a cut with a wrong antecedent in it. M2-T7 stamps the field and
   [Engine.check_attribution] checks it at the moment of the pruning; this checks it again
   at the moment it is USED, which is the check that makes the field load-bearing here
   rather than decorative.

   [watches] is [List.exists (Var.equal var)] without the partial application, which
   allocated a closure per check (D-0236: -0.3 % per node on elitserien handball12, -0.6 %
   on costas13). The check is still O(arity); an O(1) "does instance i watch v" belongs
   to [Engine] (D-0191's request). *)
let rec watches var = function
  | [] -> false
  | v :: vs -> Var.equal v var || watches var vs

let check_attribution store ~(vars_of : int -> Var.t list option) ~at ~prop ~var =
  if prop <> Store.no_prop then
    match vars_of prop with
    | Some vs when watches var vs -> ()
    | _ -> raise (Bad (Misattributed { at; claimed = prop; var = Store.name store var }))

let analyse ?(scope = At_conflict_level) store (c : Store.conflict)
    ~(vars_of : int -> Var.t list option) ~(criterion : criterion) : (t, error) result =
  let conflict_level = Store.level store in
  let max_resolutions = Store.trail_length store + 1 in
  let o1 = ref 0 and scanned = ref 0 and resolutions = ref 0 in
  (* Both accumulate in arrival order; [folds] is kept reversed and turned round once at
     the end (M6-T16). *)
  let antecedents = Uniq.create () and folds_rev = ref [] in
  let add_antecedent p = if p <> Store.no_prop then Uniq.add antecedents p in
  let check_attr = check_attribution store ~vars_of in
  let mk_node ~before fact =
    let support, fast, slot = locate store ~before fact in
    if fast then incr o1 else incr scanned;
    if support = Store.no_support then
      { fact; level = 0; support; implied_by = Store.no_prop; root = true; slot }
    else
      let e = Store.trail_entry store support in
      check_attr ~at:support ~prop:e.Store.prop ~var:e.Store.var;
      {
        fact;
        level = Store.level_of_index store support;
        support;
        implied_by = e.Store.prop;
        root = rests_on_nothing store support e;
        slot;
      }
  in
  (* The facts a hole-consuming bound move rests on, per the rule in the header, with
     every fold recorded. *)
  let hole_facts (e : Store.entry) ~at ~is_lower =
    let holes =
      if is_lower then Store.settled_over_lo e.Store.old ~cur:(Domain.lo e.Store.now)
      else Store.settled_over_hi e.Store.old ~cur:(Domain.hi e.Store.now)
    in
    List.concat_map
      (fun h ->
        match Store.remover store ~before:at ~var:e.Store.var h with
        | None -> []
        | Some (r : Store.entry) ->
            check_attr ~at ~prop:r.Store.prop ~var:r.Store.var;
            add_antecedent r.Store.prop;
            folds_rev :=
              {
                fold_var = Store.name store e.Store.var;
                fold_value = h;
                fold_prop = r.Store.prop;
                fold_into = at;
              }
              :: !folds_rev;
            Reason.facts r.Store.reason)
      holes
  in
  let expandable n =
    (not n.root)
    &&
    match scope with
    | At_conflict_level -> n.level = conflict_level
    | Everywhere -> n.level > 0
  in
  let best_expandable nodes =
    List.fold_left
      (fun acc n ->
        if not (expandable n) then acc
        else match acc with Some m when m.support >= n.support -> acc | _ -> Some n)
      None nodes
  in
  let frontier = Frontier.create ~conflict_level ~expandable () in
  (* D-0152 (D-0140 A1): the criterion is shown the walk's count and a lazy node list,
     and the next node comes off [Frontier.best]; see [Frontier]. Under BAGUETTE_DEBUG
     both are checked against the passes over the list they replaced. *)
  let view () =
    {
      v_nodes = lazy (Frontier.nodes frontier);
      v_conflict_level = conflict_level;
      v_at_conflict_level = Frontier.at_conflict_level frontier;
    }
  in
  let rec loop () =
    let v = view () in
    Debug.check "D-0152: the frontier's conflict-level count is the filter's" (fun () ->
        v.v_at_conflict_level
        = (view_of (Lazy.force v.v_nodes) ~conflict_level).v_at_conflict_level);
    if criterion.stop v then Frontier.nodes frontier
    else
      let next = Frontier.best frontier in
      Debug.check "D-0152: the frontier's best node is the fold's" (fun () ->
          match (next, best_expandable (Frontier.nodes frontier)) with
          | None, None -> true
          | Some a, Some b -> a == b
          | _ -> false);
      match next with
      | None -> Frontier.nodes frontier
      | Some n ->
          if !resolutions >= max_resolutions then raise (Bad (Diverged !resolutions));
          incr resolutions;
          let at = n.support in
          let e = Store.trail_entry store at in
          add_antecedent e.Store.prop;
          Frontier.remove frontier n;
          let added =
            Reason.facts e.Store.reason
            @ hole_facts e ~at ~is_lower:(Reason.fact_is_lower n.fact)
          in
          Frontier.add_all frontier added ~mk:(mk_node ~before:at);
          loop ()
  in
  try
    if c.Store.c_prop <> Store.no_prop && vars_of c.Store.c_prop = None then
      raise
        (Bad
           (Misattributed
              { at = -1; claimed = c.Store.c_prop; var = "<the conflicting row>" }));
    add_antecedent c.Store.c_prop;
    Frontier.add_all frontier
      (Reason.facts c.Store.c_reason)
      ~mk:(mk_node ~before:(Store.trail_length store));
    let nodes = loop () in
    let stopped = criterion.stop (view_of nodes ~conflict_level) in
    let factless =
      List.filter_map
        (fun n ->
          if
            n.root && n.support <> Store.no_support
            && not (Store.is_level_start store n.support)
          then Some n.support
          else None)
        nodes
    in
    Ok
      {
        nodes;
        conflict_level;
        conflict_prop = c.Store.c_prop;
        criterion_name = criterion.crit_name;
        stopped_by_criterion = stopped;
        antecedents = Uniq.to_list antecedents;
        folds = List.rev !folds_rev;
        factless;
        resolutions = !resolutions;
        o1_supports = !o1;
        scanned_supports = !scanned;
      }
  with Bad e -> Error e

(* ------------------------------------------------------- reading a cut *)

let facts t : Reason.fact list = List.map (fun n -> n.fact) t.nodes

(* The learned clause: the negation of the cut's conjunction, over order literals. A fact
   still at its declared bound has no literal ([Reason.lit_of_fact] returns [None]) and
   contributes nothing -- its negation is the constant false, and a false disjunct is not
   a weakening but a wrong line (lib/core/reason.ml's header). *)
let lits t = List.map Lit.negate (Reason.lits_of_facts (facts t))

(* The same clause, each literal paired with the decision level of the node it came from.

   [lits] goes through [Reason.lits], which is a [filter_map] and therefore loses the
   correspondence with [nodes]; a caller that wants both has to rebuild it here or guess
   at the alignment, and guessing is how a score ends up attributed to the wrong literal.
   So this applies [Reason.lit_of_fact] to each node directly: it drops exactly the nodes
   [lits] drops (a fact still at its declared bound has no literal), keeps node order, and
   is 1:1 by construction rather than by coincidence.

   M2-L4 reads it to compute an LBD -- the number of distinct levels a learned clause's
   literals sit at. That number has to be taken AFTER minimisation (two literals over one
   variable in one direction can sit at different levels and one of them is dropped), so
   the levels have to travel with the literals rather than be counted here. *)
let lits_levelled t : (Lit.t * int) list =
  List.filter_map
    (fun n ->
      match Reason.lit_of_fact n.fact with
      | None -> None
      | Some l -> Some (Lit.negate l, n.level))
    t.nodes

let nodes t = t.nodes
let folds t = t.folds
let antecedents t = t.antecedents
let at_level t l = List.filter (fun n -> n.level = l) t.nodes
let cited_levels t = List.sort_uniq Int.compare (List.map (fun n -> n.level) t.nodes)

(* The DECISION levels the cut names, descending -- level 0 dropped, because level 0 is
   not a decision and a fact still at its declared bound is recorded there too.

   Read this off a cut produced with [~scope:Everywhere] and [decision_closure] and it is
   a sound dependency set: every node above level 0 is then a root, so every node is a
   decision, a level-0 fact (dropped here, and resting on level-0 facts only -- see
   [decision_closure]) or a factless pruning that settled over no hole (globally valid,
   but recorded at the level it happened at and therefore kept -- conservative, which is
   the safe direction here; one that settled is expanded, see [rests_on_nothing]).
   Read it off a 1UIP cut and it is NOT one; see [decision_closure]. *)
let decision_levels t = List.rev (List.filter (fun l -> l > 0) (cited_levels t))

(* Where a clause over this cut would become asserting: the second-highest level it
   cites, which is the level M2-L3 attaches the learned clause at. 0 when the cut cites
   at most one level. *)
let backjump_level t =
  match List.rev (cited_levels t) with _ :: second :: _ -> second | _ -> 0

let postcondition_holds (crit : criterion) t =
  crit.postcondition (view_of t.nodes ~conflict_level:t.conflict_level)

(* Every fact in the cut holds in the store as it stands. Half of this row's oracle; the
   other half (that the model plus the cut is unsatisfiable) needs the model and lives in
   the test. *)
let holds_on_trail store t =
  List.for_all
    (fun n ->
      match Store.var_named store (Reason.fact_owner n.fact) with
      | None -> false
      | Some v ->
          let d = Store.get store v in
          if Reason.fact_is_lower n.fact then Domain.lo d >= fact_value n.fact
          else Domain.hi d <= fact_value n.fact)
    t.nodes

let to_string t =
  Printf.sprintf "[%s] %s | levels %s | res %d | folds %d" t.criterion_name
    (Reason.to_string_facts (facts t))
    (String.concat "," (List.map string_of_int (cited_levels t)))
    t.resolutions (List.length t.folds)

(* ------------------------------------- clause minimisation (M19-config-T6, D-0241) *)

(* SHORTER LEARNED CLAUSES, by two rules applied to a finished cut. Each removal drops a
   node of the cut whose fact the checker re-derives for itself, by unit propagation,
   from the facts that stay -- so the learned clause stays the `rup` it was (D-0018), and
   the proof writes nothing new.

   ROOT. A node whose bound was established at level 0 is dropped. Its fact holds at the
   root, and its literal in the clause is false there forever: the clause is the same
   constraint on every node the search will visit, only wider. The checker re-derives the
   fact because every level-0 trail entry has its trace line on the page (lib/core/trace.ml,
   "Level-0 prunings get a line too") or rests on one model row (I-X10), and level-0 lines
   are never retired by a `w`. D-0238 section 5's `~e_ge_1` is the example.

   RECURSIVE (MiniSat's, Sorensson and Biere 2009, over order literals). A node above level
   0 and below the conflict level is dropped when every fact its supporting entry read
   ([Reason.facts], plus the holes it settled over, as [analyse] expands them) is
   DERIVABLE:
     - at its declared bound, or established at level 0, or
     - implied by a cut node of the same slot (ladder order: [x >= 7] implies [x >= 3])
       that is either established strictly BEFORE the entry reading the fact, or kept, or
     - established by an entry that is not a root and whose own facts are all derivable,
       recursively, and memoised per (entry, direction).
   The checker's unit propagation replays exactly that: the kept literals' negations are
   assumed, each derivable fact is the claim of a trace line all of whose other literals
   are already falsified, and the removed node's line then propagates its fact. That is
   the same replay a node the 1UIP walk resolved away gets, at a lower level; the lines
   are on the page because [Trace] writes the whole trail when a branch fails, and they
   are live because the clause is written before the `w` that retires any of their
   levels (I-S4, [Learn.support_check]).

   WHY "STRICTLY BEFORE, OR KEPT". The ladder gives a forward edge the SAT version does
   not have: [x >= 7] can be established AFTER the entry that read [x >= 3]. Two cut
   nodes could then each be implied through the other (y >= 2 read x >= 3; x >= 7 read
   y >= 2) and both be dropped, which is a wrong clause. Allowing a cut node as a
   justifier only when its entry precedes the reader's, or when it is kept (decided
   before, since nodes are decided in DECREASING trail order), makes every edge between
   two dropped nodes point strictly backwards on the trail: no cycle, and the induction
   on trail position is the soundness argument. Inside the recursion only the first
   half applies, which keeps the memo a property of the entry alone.

   THE ABSTRACT-LEVEL FILTER (MiniSat's): an intermediate entry at a level no cut node
   sits at fails at once. In SAT that is exact; here an entry at level j can read only
   facts from below j, so the filter is a heuristic that may miss a removal and never
   allows a wrong one ([~level_filter:false] measures what it misses).

   The conflict level is never touched: under 1UIP it holds one node, the asserting one,
   and dropping it would leave a clause that asserts nothing. A cut taken at level 0 is
   returned as it is (its clause is the root refutation's business). *)

(* [min_break_unchecked] is the BREAK, as [Learn.Weakest] is minimisation's: it drops every
   node strictly between level 0 and the conflict level without asking whether it is
   derivable, so the clause claims more than the trail supports and the checker must refuse
   it. It exists for test/unit/test_learn.ml's lane, which shows the line really rests on
   the literals the rules keep (D-0066: a `rup` line can be vacuous). *)
type min_config = {
  min_root : bool;
  min_recursive : bool;
  min_level_filter : bool;
  min_break_unchecked : bool;
}

let min_off =
  {
    min_root = false;
    min_recursive = false;
    min_level_filter = true;
    min_break_unchecked = false;
  }

type min_result = {
  mr_cut : t;
  mr_root : int; (* literal-bearing nodes dropped by ROOT *)
  mr_recursive : int; (* ... and by RECURSIVE *)
  mr_supports : int list;
      (* trail positions of the entries the removals rest on, for [Learn.supports] *)
}

let has_lit n = Reason.lit_of_fact n.fact <> None

(* A node's identity among the cut's: its entry and its direction (one entry moves one
   variable, and may move both of its bounds). *)
let node_key n = (2 * n.support) + if Reason.fact_is_lower n.fact then 1 else 0

module Int_tbl_min = Hashtbl.Make (Int)

(* [a]'s fact implies [g], on one slot. *)
let implies_fact (a : Reason.fact) (g : Reason.fact) =
  if Reason.fact_is_lower g then fact_value a >= fact_value g
  else fact_value a <= fact_value g

let minimise_cut ?(config = min_off) store (cut : t) : min_result =
  let unchanged = { mr_cut = cut; mr_root = 0; mr_recursive = 0; mr_supports = [] } in
  if
    cut.conflict_level = 0
    || (not config.min_root) && (not config.min_recursive)
       && not config.min_break_unchecked
  then unchanged
  else if not (config.min_recursive || config.min_break_unchecked) then
    (* ROOT alone: one pass, no table. *)
    let at_root n = n.support <> Store.no_support && has_lit n && n.level = 0 in
    let n_root = List.length (List.filter at_root cut.nodes) in
    if n_root = 0 then unchanged
    else
      {
        mr_cut = { cut with nodes = List.filter (fun n -> not (at_root n)) cut.nodes };
        mr_root = n_root;
        mr_recursive = 0;
        mr_supports = [];
      }
  else
    let cl = cut.conflict_level in
    let by_slot = Slot_tbl.create 64 in
    List.iter (fun n -> if n.slot >= 0 then Slot_tbl.replace by_slot n.slot n) cut.nodes;
    let abstract l = 1 lsl (l land 61) in
    let levels_mask = List.fold_left (fun m n -> m lor abstract n.level) 0 cut.nodes in
    (* Decided so far, by node support: [true] dropped, absent undecided or kept. *)
    let dropped = Int_tbl_min.create 16 in
    let kept = Int_tbl_min.create 16 in
    let memo = Int_tbl_min.create 64 in
    let used = ref [] in
    (* Every fact the entry at [at] read, as [analyse] expands it (its reason, then the
       reasons of the holes it settled over), satisfies [ok]. Short-circuits, and asks for
       the holes' removers only once the reason itself has passed: a remover is a search
       of the hole log, and on work-task it was most of what this rule cost. *)
    let entry_ok (e : Store.entry) ~at ~is_lower ok =
      List.for_all ok (Reason.facts e.Store.reason)
      &&
      let holes =
        if is_lower then Store.settled_over_lo e.Store.old ~cur:(Domain.lo e.Store.now)
        else Store.settled_over_hi e.Store.old ~cur:(Domain.hi e.Store.now)
      in
      List.for_all
        (fun h ->
          match Store.remover store ~before:at ~var:e.Store.var h with
          | None -> true
          | Some (r : Store.entry) -> List.for_all ok (Reason.facts r.Store.reason))
        holes
    in
    (* Does a cut node on [g]'s slot imply [g] and may it justify a reader at [before]? *)
    let by_cut g ~slot ~before ~top =
      slot >= 0
      &&
      match Slot_tbl.find_opt by_slot slot with
      | None -> false
      | Some m ->
          m.support <> Store.no_support && implies_fact m.fact g
          && (m.support < before || (top && Int_tbl_min.mem kept (node_key m)))
    in
    let rec derivable g ~before ~top =
      let pos, _, slot = locate store ~before g in
      pos = Store.no_support
      || Store.level_of_index store pos = 0
      || by_cut g ~slot ~before ~top
      || entry_derivable pos ~is_lower:(Reason.fact_is_lower g)
    and entry_derivable pos ~is_lower =
      let key = (2 * pos) + if is_lower then 1 else 0 in
      match Int_tbl_min.find_opt memo key with
      | Some b -> b
      | None ->
          let e = Store.trail_entry store pos in
          let lvl = Store.level_of_index store pos in
          let ok =
            (not (rests_on_nothing store pos e))
            && ((not config.min_level_filter) || levels_mask land abstract lvl <> 0)
            &&
            (* Provisionally false: the recursion only goes backwards, so this is never
               read before it is overwritten, and it bounds the walk if it ever were. *)
            (Int_tbl_min.replace memo key false;
             entry_ok e ~at:pos ~is_lower (fun f -> derivable f ~before:pos ~top:false))
          in
          Int_tbl_min.replace memo key ok;
          if ok then used := pos :: !used;
          ok
    in
    let n_root = ref 0 and n_rec = ref 0 in
    (* Nodes in DECREASING support order; see the header for why. *)
    let order = List.stable_sort (fun a b -> Int.compare b.support a.support) cut.nodes in
    List.iter
      (fun n ->
        if n.support = Store.no_support || not (has_lit n) then ()
        else if n.level = 0 then
          if config.min_root then (
            Int_tbl_min.replace dropped (node_key n) ();
            incr n_root)
          else Int_tbl_min.replace kept (node_key n) ()
        else if config.min_break_unchecked && n.level < cl then (
          Int_tbl_min.replace dropped (node_key n) ();
          incr n_rec)
        else if
          config.min_recursive && n.level < cl && (not n.root)
          &&
          let e = Store.trail_entry store n.support in
          entry_ok e ~at:n.support ~is_lower:(Reason.fact_is_lower n.fact) (fun f ->
              derivable f ~before:n.support ~top:true)
        then (
          Int_tbl_min.replace dropped (node_key n) ();
          used := n.support :: !used;
          incr n_rec)
        else Int_tbl_min.replace kept (node_key n) ())
      order;
    if !n_root = 0 && !n_rec = 0 then unchanged
    else
      let nodes =
        List.filter
          (fun n ->
            n.support = Store.no_support
            || (not (has_lit n))
            || not (Int_tbl_min.mem dropped (node_key n)))
          cut.nodes
      in
      {
        mr_cut = { cut with nodes };
        mr_root = !n_root;
        mr_recursive = !n_rec;
        mr_supports = List.rev !used;
      }

(* ------------------------------------- the dependency levels, memoised (M7-T27 a3) *)

(* [dependency_levels] is [decision_levels] of [analyse ~scope:Everywhere
   ~criterion:decision_closure] -- the SAME set, for the same conflict -- computed
   without materialising a reason the closure has already walked once. D-0124's second
   addendum is the record.

   WHY A MEMO OF LEVELS PER ENTRY WOULD BE WRONG, which is what D-0124's first addendum
   proposed. The closure's answer is not the union, over the facts the conflict rests
   on, of "the decision levels this fact rests on". [Frontier] keeps ONE node per bound
   slot (a variable and a direction) and resolves the STRONGER of two facts on the same
   slot, dropping the weaker without expanding it: a decision [x >= 2] at level 1, cited
   by a level-1 pruning, is dropped when a decision [x >= 3] at level 2 is already in the
   frontier, because [x >= 3] entails it. That drop is what makes the closure of a
   bound-split search name {2} rather than {1, 2} (test_analysis.ml, scene 5). It is
   sound -- the cut still entails the dropped fact, so it is still a nogood -- and it is
   strictly better, since the backjump then skips level 1. A per-entry set of levels
   cannot see it: whether [x >= 2] is dropped depends on what ELSE is in the frontier
   when it arrives, a property of the conflict and not of the entry. So a union of
   per-entry level sets is a SUPERSET of the closure's answer: sound, weaker, and not
   the search this project measures itself against byte for byte.

   WHAT IS MEMOISED INSTEAD is exactly what the walk needs from an entry: its CITATIONS,
   the trail position that established each fact its reason read (and each fact the
   reasons of the holes its bound move settled over read), with that position's level,
   direction and root-ness packed into one int. That is a property of the entry alone --
   [support_of ~before:p] answers from positions strictly below [p], and everything
   below a live entry is frozen (I-T1, the argument D-0124 makes for [Store.history]) --
   so it is computed on the entry's first visit, stored on it ([Store.entry.cites]), and
   dies with the record; nothing invalidates it on backtrack because [Store.apply]
   allocates a fresh record for every push. Citations at level 0 or without a support
   are not kept: such a node contributes no level, and the only node it could shadow by
   [stronger] is a weaker fact on the same slot, which sits below it on the trail and
   is therefore at level 0 too. The memo is O(cited facts above level 0) per entry,
   8 bytes each, for the entries a closure reaches, against the 7 to 17 words per term
   of every pruning that D-0124 removed.

   THE WALK over citations is [analyse]'s walk with the facts left out: a cell per slot
   holding the highest cited position; the highest expandable cell resolved first
   ([best_expandable]); a cited position merged into an existing cell only when it is
   higher ([stronger]: on one slot a later position is a stronger bound, by I-D3, and
   the same position is the same fact); the cell removed when its position is expanded
   ([Frontier.remove]); a decision or a factless pruning that settled over no hole
   ([rests_on_nothing]) never expanded; level 0 never entered. The answer is the set of levels of the cells left,
   which are all roots above level 0: [decision_closure]'s postcondition, by
   construction. Under BAGUETTE_DEBUG the walk over facts runs beside it and the two
   answers must agree; test_analysis.ml compares them on every scene.

   Per conflict this costs one hash step per citation of each entry resolved, in place
   of one [Reason.facts] per entry (3 600 facts rebuilt from the history, 122 033 times
   per 300 s on pattern-set-mining, D-0124's addendum) and one [support_of] per fact.
   Entries persist across the conflicts of a subtree and so do their memos. *)

(* One citation. The level sits in the high bits, then the position, then a root bit and
   a direction bit, so that the integer order is the position order (a higher position
   is at the same or a higher level). Positions and levels are bounded at 2^30, which a
   trail cannot reach in 15 GB. *)
let pack ~pos ~level ~root ~is_lower =
  assert (pos >= 0 && pos < 1 lsl 30 && level >= 0 && level < 1 lsl 30);
  (level lsl 32) lor (pos lsl 2) lor (if root then 2 else 0) lor if is_lower then 1 else 0

let cite_pos c = (c lsr 2) land 0x3FFF_FFFF
let cite_level c = c lsr 32
let cite_root c = c land 2 <> 0
let cite_is_lower c = c land 1 <> 0

(* The citation of [fact] as read by the entry at [before] (the trail length, for the
   conflict's own reason), or [None] for a fact at its declared bound or established at
   level 0. [check] is the attribution check, run on the supporting entry whatever its
   level, so that a corrupt graph is refused on first contact exactly as [mk_node]
   refuses it. *)
let cite store ~check ~before fact =
  let s, _ = support_of store ~before fact in
  if s = Store.no_support then None
  else
    let e = Store.trail_entry store s in
    check ~at:s ~prop:e.Store.prop ~var:e.Store.var;
    let level = Store.level_of_index store s in
    if level = 0 then None
    else
      Some
        (pack ~pos:s ~level ~root:(rests_on_nothing store s e)
           ~is_lower:(Reason.fact_is_lower fact))

(* [memo_entries]/[memo_ints] count the memos built and the ints they hold, over the run:
   an upper bound on what the memo ever held live (a memo dies with its entry), printed
   under --stats as `cites` so that the memory question is answered by a number. *)
(* The citations of the entry at [p]: its memo, or computed once and stored. The holes
   follow [analyse]'s rule: the reasons of the holes the entry's bound move settled over,
   in the direction it moved -- [settled_over_lo] when the lower bound moved,
   [settled_over_hi] when the upper did. An entry moves one bound ([Store.fix], which
   moves both, has no caller in lib/), so this is [hole_facts] for the one direction a
   node on that entry can have; for a two-bound entry it would be the union over both
   directions, a superset of either node's folds and sound. Each remover's attribution
   is checked as [hole_facts] checks it. *)
let memo_entries = ref 0
let memo_ints = ref 0

let cites_of store ~check p =
  let e = Store.trail_entry store p in
  match e.Store.cites with
  | Some a -> a
  | None ->
      let out = ref [] in
      let add fact =
        match cite store ~check ~before:p fact with
        | None -> ()
        | Some c -> out := c :: !out
      in
      List.iter add (Reason.facts e.Store.reason);
      let fold holes =
        List.iter
          (fun h ->
            match Store.remover store ~before:p ~var:e.Store.var h with
            | None -> ()
            | Some (r : Store.entry) ->
                check ~at:p ~prop:r.Store.prop ~var:r.Store.var;
                List.iter add (Reason.facts r.Store.reason))
          holes
      in
      if Domain.lo e.Store.now > Domain.lo e.Store.old then
        fold (Store.settled_over_lo e.Store.old ~cur:(Domain.lo e.Store.now));
      if Domain.hi e.Store.now < Domain.hi e.Store.old then
        fold (Store.settled_over_hi e.Store.old ~cur:(Domain.hi e.Store.now));
      let a = Array.of_list (List.rev !out) in
      incr memo_entries;
      memo_ints := !memo_ints + Array.length a;
      e.Store.cites <- Some a;
      a

(* A max-heap of citations by position, cleaned lazily: a popped citation is acted on
   only if its slot's cell still holds it, so a citation pushed twice (its cell removed
   by an expansion and re-created by a later arrival) is expanded once per cell, which
   is what [Frontier] does. *)
module Heap = struct
  type t = { mutable a : int array; mutable n : int }

  let create () = { a = Array.make 64 0; n = 0 }

  let push h c =
    if h.n = Array.length h.a then (
      let bigger = Array.make (2 * h.n) 0 in
      Array.blit h.a 0 bigger 0 h.n;
      h.a <- bigger);
    let i = ref h.n in
    h.n <- h.n + 1;
    while !i > 0 && cite_pos h.a.((!i - 1) / 2) < cite_pos c do
      h.a.(!i) <- h.a.((!i - 1) / 2);
      i := (!i - 1) / 2
    done;
    h.a.(!i) <- c

  let pop h =
    if h.n = 0 then None
    else
      let top = h.a.(0) in
      h.n <- h.n - 1;
      let last = h.a.(h.n) in
      let i = ref 0 and placed = ref false in
      while not !placed do
        let l = (2 * !i) + 1 and r = (2 * !i) + 2 in
        let best = if l < h.n && cite_pos h.a.(l) > cite_pos last then l else !i in
        let best =
          if
            r < h.n
            && cite_pos h.a.(r) > cite_pos (if best = !i then last else h.a.(best))
          then r
          else best
        in
        if best = !i then (
          h.a.(!i) <- last;
          placed := true)
        else (
          h.a.(!i) <- h.a.(best);
          i := best)
      done;
      Some top
end

(* The closure's CELLS, slot -> the citation the cell holds, as a DENSE array indexed by
   slot rather than a hash table (M20-pernode-T4, D-0236). A slot is [2 * v + direction]
   for a store variable [v], so [2 * Store.n_vars] cells cover every key; [Slot_tbl] cost
   a hash, a closure call and a [Some] per probe, 3 to 4 % of elitserien handball12's
   instructions without the proof.

   The arrays are a SCRATCH kept between conflicts, because allocating and clearing
   [2 * n] cells per conflict would cost what the table did. A cell is current only if its
   [stamp] is the walk's [epoch], which [open_walk] bumps, so nothing is cleared and a
   cell written by an earlier conflict, or for another store, reads as empty. [touched]
   lists the slots written in this walk, once each, which is what the final fold reads.
   One walk at a time: [dependency_levels] is the only user and does not re-enter itself
   (its debug cross-check runs [analyse], which does not use this). Citations are
   non-negative ([pack]), so [-1] is the empty cell. Nothing reads the cells in an order
   that reaches an output: the levels are sorted at the end, as they were from the
   table's fold. *)
module Cells = struct
  type t = {
    mutable cit : int array;
    mutable stamp : int array;
    mutable epoch : int;
    mutable touched : int array;
    mutable n_touched : int;
  }

  let empty = -1

  let scratch =
    { cit = [||]; stamp = [||]; epoch = 0; touched = Array.make 64 0; n_touched = 0 }

  let open_walk ~n_slots =
    let s = scratch in
    if Array.length s.cit < n_slots then (
      s.cit <- Array.make n_slots empty;
      s.stamp <- Array.make n_slots 0);
    s.epoch <- s.epoch + 1;
    s.n_touched <- 0;
    s

  let find s k = if s.stamp.(k) = s.epoch then s.cit.(k) else empty

  let set s k c =
    if s.stamp.(k) <> s.epoch then (
      s.stamp.(k) <- s.epoch;
      if s.n_touched = Array.length s.touched then (
        let bigger = Array.make (2 * s.n_touched) 0 in
        Array.blit s.touched 0 bigger 0 s.n_touched;
        s.touched <- bigger);
      s.touched.(s.n_touched) <- k;
      s.n_touched <- s.n_touched + 1);
    s.cit.(k) <- c

  let remove s k = s.cit.(k) <- empty

  let fold_live s f acc =
    let acc = ref acc in
    for i = 0 to s.n_touched - 1 do
      let c = s.cit.(s.touched.(i)) in
      if c <> empty then acc := f c !acc
    done;
    !acc
end

(* The decision levels the conflict rests on, descending, level 0 dropped: what
   [decision_levels] reads off the decision closure, see the section header. [Error]
   when the graph is corrupt or the walk does not close, as [analyse] reports them. *)
let dependency_levels store (c : Store.conflict) ~(vars_of : int -> Var.t list option) :
    (int list, error) result =
  let check = check_attribution store ~vars_of in
  let max_resolutions = Store.trail_length store + 1 in
  let resolutions = ref 0 in
  (* Slot -> the citation its cell holds, see [Cells]. *)
  let cells = Cells.open_walk ~n_slots:(2 * Store.n_vars store) in
  let heap = Heap.create () in
  let slot c =
    let e = Store.trail_entry store (cite_pos c) in
    (2 * Var.to_int e.Store.var) + if cite_is_lower c then 1 else 0
  in
  let insert c =
    let k = slot c in
    let held = Cells.find cells k in
    if held <> Cells.empty && cite_pos held >= cite_pos c then ()
    else (
      Cells.set cells k c;
      if not (cite_root c) then Heap.push heap c)
  in
  let rec loop () =
    match Heap.pop heap with
    | None -> ()
    | Some c ->
        let k = slot c in
        if Cells.find cells k = c then (
          if !resolutions >= max_resolutions then raise (Bad (Diverged !resolutions));
          incr resolutions;
          Cells.remove cells k;
          Array.iter insert (cites_of store ~check (cite_pos c)));
        loop ()
  in
  try
    if c.Store.c_prop <> Store.no_prop && vars_of c.Store.c_prop = None then
      raise
        (Bad
           (Misattributed
              { at = -1; claimed = c.Store.c_prop; var = "<the conflicting row>" }));
    let before = Store.trail_length store in
    List.iter
      (fun f -> match cite store ~check ~before f with None -> () | Some c -> insert c)
      (Reason.facts c.Store.c_reason);
    loop ();
    let levels =
      List.rev
        (List.sort_uniq Int.compare
           (Cells.fold_live cells (fun c acc -> cite_level c :: acc) []))
    in
    Debug.check
      "M7-T27 (a3): the memoised closure names the levels the walk over facts does"
      (fun () ->
        match analyse ~scope:Everywhere store c ~vars_of ~criterion:decision_closure with
        | Ok t -> decision_levels t = levels
        | Error _ -> false);
    Ok levels
  with Bad e -> Error e
