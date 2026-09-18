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
     - no mutation of the store: [analyse] takes it and reads it;
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
       O(1), M2-T8. See [support_of] for the one case where it is not the answer and a
       scan is needed instead.
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
   moved the bound again between the read and the conflict); when it is not, a downward
   scan finds the unique entry that pushed the bound past [value], which exists and is
   unique because bounds are monotone within a level (I-D3) and [undo_to] pops entries
   whose effect is gone. [o1_supports] and [scanned_supports] count the two paths, so a
   test can assert the O(1) path is the one actually taken rather than assuming it.

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

let criteria = [ one_uip; conflict_side; decision_cut ]

(* ------------------------------------------------------- the walk *)

(* Did [e] establish [value] in this direction? True for exactly one entry per
   (variable, direction, value) that is still live, by I-D3's monotonicity. *)
let establishes (e : Store.entry) ~is_lower ~value =
  if is_lower then Domain.lo e.Store.old < value && Domain.lo e.Store.now >= value
  else Domain.hi e.Store.old > value && Domain.hi e.Store.now <= value

let scan_support store ~before ~name ~is_lower ~value =
  let rec go i =
    if i < 0 then Store.no_support
    else
      let e = Store.trail_entry store i in
      if
        String.equal (Store.name store e.Store.var) name && establishes e ~is_lower ~value
      then i
      else go (i - 1)
  in
  go (min (before - 1) (Store.trail_length store - 1))

(* The trail position that established [fact], looking strictly below [before]. Returns
   the position and whether the O(1) array answered it. See the header. *)
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
      else (scan_support store ~before ~name ~is_lower ~value, false)

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

exception Bad of error

let analyse store (c : Store.conflict) ~(vars_of : int -> Var.t list option)
    ~(criterion : criterion) : (t, error) result =
  let conflict_level = Store.level store in
  let max_resolutions = Store.trail_length store + 1 in
  let o1 = ref 0 and scanned = ref 0 and resolutions = ref 0 in
  let antecedents = ref [] and folds = ref [] in
  let add_antecedent p =
    if p <> Store.no_prop && not (List.mem p !antecedents) then
      antecedents := !antecedents @ [ p ]
  in
  (* The one place [entry.prop] is READ rather than carried. An id that names no
     instance, or an instance that does not watch the variable the entry changed, is a
     corrupt graph and stops the walk -- it does not produce a cut with a wrong
     antecedent in it. M2-T7 stamps the field and [Engine.check_attribution] checks it at
     the moment of the pruning; this checks it again at the moment it is USED, which is
     the check that makes the field load-bearing here rather than decorative. *)
  let check_attr ~at ~prop ~var =
    if prop <> Store.no_prop then
      match vars_of prop with
      | Some vs when List.exists (Var.equal var) vs -> ()
      | _ ->
          raise (Bad (Misattributed { at; claimed = prop; var = Store.name store var }))
  in
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
            folds :=
              !folds
              @ [
                  {
                    fold_var = Store.name store e.Store.var;
                    fold_value = h;
                    fold_prop = r.Store.prop;
                    fold_into = at;
                  };
                ];
            r.Store.reason)
      holes
  in
  let expandable n = (not n.root) && n.level = conflict_level in
  let best_expandable nodes =
    List.fold_left
      (fun acc n ->
        if not (expandable n) then acc
        else match acc with Some m when m.support >= n.support -> acc | _ -> Some n)
      None nodes
  in
  let rec loop nodes =
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
          let rest =
            List.filter
              (fun m -> not (same_slot m n && fact_value m.fact = fact_value n.fact))
              nodes
          in
          let added =
            e.Store.reason @ hole_facts e ~at ~is_lower:(Reason.fact_is_lower n.fact)
          in
          loop
            (List.fold_left (fun acc f -> add_node acc (mk_node ~before:at f)) rest added)
  in
  try
    if c.Store.c_prop <> Store.no_prop && vars_of c.Store.c_prop = None then
      raise
        (Bad
           (Misattributed
              { at = -1; claimed = c.Store.c_prop; var = "<the conflicting row>" }));
    add_antecedent c.Store.c_prop;
    let start =
      List.fold_left
        (fun acc f -> add_node acc (mk_node ~before:(Store.trail_length store) f))
        [] c.Store.c_reason
    in
    let nodes = loop start in
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
        antecedents = !antecedents;
        folds = !folds;
        factless;
        resolutions = !resolutions;
        o1_supports = !o1;
        scanned_supports = !scanned;
      }
  with Bad e -> Error e

(* ------------------------------------------------------- reading a cut *)

let facts t : Reason.t = List.map (fun n -> n.fact) t.nodes

(* The learned clause: the negation of the cut's conjunction, over order literals. A fact
   still at its declared bound has no literal ([Reason.lit_of_fact] returns [None]) and
   contributes nothing -- its negation is the constant false, and a false disjunct is not
   a weakening but a wrong line (lib/core/reason.ml's header). *)
let lits t = List.map Lit.negate (Reason.lits (facts t))
let nodes t = t.nodes
let at_level t l = List.filter (fun n -> n.level = l) t.nodes
let cited_levels t = List.sort_uniq Int.compare (List.map (fun n -> n.level) t.nodes)

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
    (Reason.to_string (facts t))
    (String.concat "," (List.map string_of_int (cited_levels t)))
    t.resolutions (List.length t.folds)
