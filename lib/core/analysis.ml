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
     - its supporting entry rests on no facts ([Reason.is_empty]). That is a DECISION
       (search.ml pushes [Reason.none] beside [Explanation.decision] -- D-0018/D-0037),
       a constraint posted at this level, or a pruning that genuinely follows from a
       model row alone.

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
type view = { v_nodes : node list; v_conflict_level : int }

(* [stop] decides when the walk ends. [postcondition] is what THIS criterion guarantees
   about the cut it produced, and it is the only place a rule like 1UIP may be written
   down. See the header. *)
type criterion = { crit_name : string; stop : view -> bool; postcondition : view -> bool }

let count_at_conflict_level v =
  List.length (List.filter (fun n -> n.level = v.v_conflict_level) v.v_nodes)

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
  List.for_all (fun n -> n.level <> v.v_conflict_level || n.root) v.v_nodes

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
   a factless pruning, and the levels it names really are the levels the conflict rests
   on. See lib/core/learn.ml for the argument written out.

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
  List.for_all (fun n -> n.root || n.level = 0) v.v_nodes

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
   the position and whether the O(1) array answered it ([false]: the bound history did).
   See the header. *)
let support_of store ~before fact =
  let name = Reason.fact_owner fact in
  let is_lower = Reason.fact_is_lower fact in
  let value = fact_value fact in
  match Store.var_named store name with
  | None -> (Store.no_support, false)
  | Some v ->
      let fast =
        if is_lower then Store.lo_support store v else Store.hi_support store v
      in
      if
        fast <> Store.no_support && fast < before
        && establishes (Store.trail_entry store fast) ~is_lower ~value
      then (fast, true)
      else
        let at = Store.bound_support store ~before v ~is_lower ~value in
        Debug.check "M6-T14: the bound history agrees with the trail scan" (fun () ->
            at = scan_support store ~before ~v ~is_lower ~value);
        (at, false)

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

   [mk] is applied to the facts in order, once each, so [mk_node]'s counters and its
   [Bad] exception fire in the same order as before. *)
module Frontier = struct
  module H = Hashtbl.Make (struct
    type t = string

    let equal = String.equal
    let hash (s : string) = Hashtbl.hash s
  end)

  type cell = { mutable cur : node }
  type t = { lo : cell H.t; hi : cell H.t; mutable cells : cell list }

  let create () = { lo = H.create 64; hi = H.create 64; cells = [] }
  let table f n = if Reason.fact_is_lower n.fact then f.lo else f.hi
  let nodes f = List.map (fun c -> c.cur) f.cells

  let add_all f facts ~mk =
    let fresh = ref [] in
    List.iter
      (fun x ->
        let n = mk x in
        let tbl = table f n and name = Reason.fact_owner n.fact in
        match H.find_opt tbl name with
        | Some c -> c.cur <- stronger c.cur n
        | None ->
            let c = { cur = n } in
            H.replace tbl name c;
            fresh := c :: !fresh)
      facts;
    if !fresh <> [] then f.cells <- f.cells @ List.rev !fresh

  (* Drop [n]'s cell, as [analyse]'s [List.filter] on slot AND value did. The frontier
     holds one cell per slot, so this removes [n]'s slot whenever [n] is in it. *)
  let remove f n =
    let hit = ref false in
    f.cells <-
      List.filter
        (fun c ->
          let m = c.cur in
          if same_slot m n && fact_value m.fact = fact_value n.fact then (
            hit := true;
            false)
          else true)
        f.cells;
    if !hit then H.remove (table f n) (Reason.fact_owner n.fact)
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
   rather than decorative. *)
let check_attribution store ~(vars_of : int -> Var.t list option) ~at ~prop ~var =
  if prop <> Store.no_prop then
    match vars_of prop with
    | Some vs when List.exists (Var.equal var) vs -> ()
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
    let support, fast = support_of store ~before fact in
    if fast then incr o1 else incr scanned;
    if support = Store.no_support then
      { fact; level = 0; support; implied_by = Store.no_prop; root = true }
    else
      let e = Store.trail_entry store support in
      check_attr ~at:support ~prop:e.Store.prop ~var:e.Store.var;
      {
        fact;
        level = Store.level_of_index store support;
        support;
        implied_by = e.Store.prop;
        root = Reason.is_empty e.Store.reason;
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
  let frontier = Frontier.create () in
  let rec loop () =
    let nodes = Frontier.nodes frontier in
    if criterion.stop { v_nodes = nodes; v_conflict_level = conflict_level } then nodes
    else
      match best_expandable nodes with
      | None -> nodes
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
    let stopped = criterion.stop { v_nodes = nodes; v_conflict_level = conflict_level } in
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
   [decision_closure]) or a factless pruning (globally valid, but recorded at the level
   it happened at and therefore kept -- conservative, which is the safe direction here).
   Read it off a 1UIP cut and it is NOT one; see [decision_closure]. *)
let decision_levels t = List.rev (List.filter (fun l -> l > 0) (cited_levels t))

(* Where a clause over this cut would become asserting: the second-highest level it
   cites, which is the level M2-L3 attaches the learned clause at. 0 when the cut cites
   at most one level. *)
let backjump_level t =
  match List.rev (cited_levels t) with _ :: second :: _ -> second | _ -> 0

let postcondition_holds (crit : criterion) t =
  crit.postcondition { v_nodes = t.nodes; v_conflict_level = t.conflict_level }

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
   ([Frontier.remove]); a decision or factless pruning ([Reason.is_empty]) never
   expanded; level 0 never entered. The answer is the set of levels of the cells left,
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
        (pack ~pos:s ~level
           ~root:(Reason.is_empty e.Store.reason)
           ~is_lower:(Reason.fact_is_lower fact))

(* The citations of the entry at [p]: its memo, or computed once and stored. The holes
   follow [analyse]'s rule: the reasons of the holes the entry's bound move settled over,
   in the direction it moved -- [settled_over_lo] when the lower bound moved,
   [settled_over_hi] when the upper did. An entry moves one bound ([Store.fix], which
   moves both, has no caller in lib/), so this is [hole_facts] for the one direction a
   node on that entry can have; for a two-bound entry it would be the union over both
   directions, a superset of either node's folds and sound. Each remover's attribution
   is checked as [hole_facts] checks it. *)
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

(* The decision levels the conflict rests on, descending, level 0 dropped: what
   [decision_levels] reads off the decision closure, see the section header. [Error]
   when the graph is corrupt or the walk does not close, as [analyse] reports them. *)
let dependency_levels store (c : Store.conflict) ~(vars_of : int -> Var.t list option) :
    (int list, error) result =
  let check = check_attribution store ~vars_of in
  let max_resolutions = Store.trail_length store + 1 in
  let resolutions = ref 0 in
  (* Slot -> the citation its cell holds. Looked up and never iterated for an ordered
     result: the levels are sorted at the end. *)
  let cells : (int, int) Hashtbl.t = Hashtbl.create 64 in
  let heap = Heap.create () in
  let slot c =
    let e = Store.trail_entry store (cite_pos c) in
    (2 * Var.to_int e.Store.var) + if cite_is_lower c then 1 else 0
  in
  let insert c =
    let k = slot c in
    match Hashtbl.find_opt cells k with
    | Some held when cite_pos held >= cite_pos c -> ()
    | _ ->
        Hashtbl.replace cells k c;
        if not (cite_root c) then Heap.push heap c
  in
  let rec loop () =
    match Heap.pop heap with
    | None -> ()
    | Some c ->
        let k = slot c in
        (match Hashtbl.find_opt cells k with
        | Some held when held = c ->
            if !resolutions >= max_resolutions then raise (Bad (Diverged !resolutions));
            incr resolutions;
            Hashtbl.remove cells k;
            Array.iter insert (cites_of store ~check (cite_pos c))
        | _ -> ());
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
           (Hashtbl.fold (fun _ c acc -> cite_level c :: acc) cells []))
    in
    Debug.check
      "M7-T27 (a3): the memoised closure names the levels the walk over facts does"
      (fun () ->
        match analyse ~scope:Everywhere store c ~vars_of ~criterion:decision_closure with
        | Ok t -> decision_levels t = levels
        | Error _ -> false);
    Ok levels
  with Bad e -> Error e
