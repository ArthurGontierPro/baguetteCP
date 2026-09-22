(* all_different_int: the variables take pairwise distinct values.

   Consistency level: BOUNDS (docs/SPEC.md 3.2, docs/GLOSSARY.md). This propagator reads
   and writes lo/hi only; it never punches a hole. That is stage 1 of the two-stage
   design docs/ROADMAP.md M4-T1/M4-T2 and docs/GCS-COMPARISON.md section 3 both specify --
   "one constraint, one propagator, the consistency tag choosing the shape" -- and the
   second stage (Regin, domain-consistent) is deliberately NOT here. D-0004 is the record
   and it is OPEN: bounds first, precisely so that the matching/SCC pass has a working,
   proof-logged baseline to be evaluated against. [stage_bounds] below is named for that
   split, and [propagate] is the one place a second stage would be sequenced.

   ---------------------------------------------------------------------------
   Filtering: Hall intervals
   ---------------------------------------------------------------------------

   An interval [a, b] is a HALL INTERVAL when the number of variables whose current
   domain is contained in it is exactly its width b - a + 1: those variables use up
   every value of [a, b] between them, so no other variable may take one.

     - more contained variables than values  -> Conflict (pigeonhole);
     - exactly as many                       -> for every OTHER variable y,
                                                  lo(y) in [a, b] => lo(y) := b + 1
                                                  hi(y) in [a, b] => hi(y) := a - 1.

   A variable y outside the Hall set has lo(y) < a or hi(y) > b (otherwise it would be
   in the set), so each push above leaves a non-empty domain and the two can never both
   fire on one y. Only intervals whose endpoints are a current lo and a current hi can
   be Hall intervals, which is what bounds the enumeration; the loop repeats until a
   pass changes nothing, which is what makes [propagate] idempotent at the interface
   (I-P3) rather than by a one-pass argument like [Linear]'s.

   The enumeration is O(n * d^2) per pass and is the naive complete one, not Puget's
   O(n log n). That is a deliberate M4-T1 choice: this row is an experiment about the
   JUSTIFICATION, the models it may ship are bounded to single/low-double-digit domains
   by the memory rule, and an algorithm whose completeness is evident is worth more here
   than one whose completeness is a citation. The consistency oracle (M2-T10, D-0059,
   BAGUETTE_CONSISTENCY=1) is what checks the claim either way.

   ---------------------------------------------------------------------------
   Justification -- the multi-row Hall derivation (D-0027, roadmap M4-T1)
   ---------------------------------------------------------------------------

   D-0027 is the permission: D-0011's "one instance justifies against exactly one model
   row" is a rule about NAMING rows, not counting them, and a derivation may cite any
   number. This module is the first thing in the tree that spends that permission, and
   it spends it hard -- a single pruning's [Combine] names, transitively, one at-least-one
   line per Hall variable, one at-most-one line per Hall value, and a channelling id per
   value of every variable in sight. Every one of them is named with
   [Explanation.Model_row], which is exactly the constructor D-0015 added for this.

   The counting argument, as cutting planes. Write V = [a, b], k = |V|, H the Hall set,
   y the variable being pruned, and x_eq_v for the direct encoding
   (lib/proof/encoding.ml, introduced with [red] at [start_proof]).

     ALO_i    sum_{v in V and decl(x_i)} x_i_eq_v >= 1          one per Hall variable
     AMO_v    sum_{x in P_v} ~x_eq_v >= |P_v| - 1               one per Hall value,
                over P_v = the variables of H + {y} whose DECLARED domain holds v

   Adding them all pairs every x_i_eq_v against its own ~x_i_eq_v, so the whole Hall set
   cancels to a constant, and what survives is

     sum_{v in V and decl(y)} ~y_eq_v  >=  |V and decl(y)|

   -- y takes none of the Hall values. With no y at all and |H| > k the same sum leaves
   [0 >= |H| - k], a contradiction. Turning the excluded values into a BOUND is then the
   forward channelling clause x_eq_v \/ ~x_ge_v \/ x_ge_(v+1) summed up the interval,
   which telescopes to ~y_ge_lo(y) + y_ge_(b+1) >= 1 (see [prune_summands]).

   Three things that are worth saying because each was a choice:

   1. **No [Explanation.Clause] anywhere in the tree, and that is load-bearing.** The
      cheap way to recover a per-value at-most-one line is a [rup] over the direct
      encoding. It would work, and it would make every [pol] in this file decorative:
      lib/core/search.ml's [rests_on_a_clause] routes a root conflict whose derivation
      rests on a clause the D-0022 way, so `conclusion UNSAT` cites the empty clause and
      nothing the checker does depends on the Hall arithmetic being right (D-0057 and
      D-0060 are two prior findings of exactly that). So the at-most-one line is
      recovered by [pol] instead -- [pair_amo] -- and lib/proof/encoding.ml's
      [add_all_different] posts the pairwise CLAUSE rows rather than big-M rows precisely
      to make that recovery five ids and one division.

   2. **A current bound appears as a literal in the derived row, and is cancelled by the
      id of the line that establishes it where there is one.** [excl] derives
      ~x_ge_lo(x) \/ ~x_eq_v rather than ~x_eq_v, so before cancellation the row is the
      globally valid `~<bound facts> \/ <the pruning>` shape lib/core/prop/ne.ml's clause
      already has, sound at any level. Citing the trail entry the way [Linear] does still
      does not fit -- a cited [Linear] derives a statement in the order encoding's ladder
      currency (D-0010, lib/core/ladder.ml's header), not the unit x_ge_c >= 1 the
      counting needs -- which is why M4-T7 gave [Explanation] the one thing that does:
      [Defining], a summand carrying the id of the UNIT line that states the fact. See
      [moved_bound_cancels] below.

   3. **[Weaken] is used for its D-0009 meaning and twice over.** Once to drop the
      excluded values the pruning does not need ([Lit.eq y v] as the trivial axiom
      y_eq_v >= 0), and once as the degenerate at-most-one: where only ONE variable in
      scope can take a value, the "at most one of them does" line is literally the
      literal axiom ~x_eq_v >= 0, and writing it as a [Weaken] summand rather than
      special-casing it keeps the counting uniform.

   3'. **One new [Explanation] summand, and it is the only thing in this file that is
      not [Combine]/[Weaken]/[Model_row].** M4-T1 built the whole derivation without one
      (D-0061) and got everything except the cancellation in item 2, where it had to fall
      back on [Explanation.clause [lit]]. M4-T7 replaced that stand-in with
      [Explanation.defining], whose record is D-0009's own: see explanation.ml's header
      for why it is a summand rather than a [t].

   ---------------------------------------------------------------------------
   Snapshotting and I-X6
   ---------------------------------------------------------------------------

   Every number a derivation depends on -- the interval, each variable's current and
   declared bounds -- is snapshotted into [snap] records at the moment of the pruning
   and the thunk reads nothing else from the store. What the thunk DOES read live is
   [Encoding]'s constraint ids, and that is not an I-X6 violation for the reason I-X6
   is about: those ids are written once, by [Encoding.start_proof], before the first
   decision, and never move. Reading them later gives the same answer as reading them
   now. (They do not exist at all when no proof is being written, which is why
   [cid_of] says so rather than raising [Not_found] several layers down.) *)

module Lit = Baguette_proof.Lit
module Encoding = Baguette_proof.Encoding

(* A variable, and the five numbers any part of the derivation may ask about it. The
   declared pair is frozen at [make] time for D-0010's reason ([Order_reason]'s header);
   the current pair is frozen per pruning. *)
(* Why a DECLARED value is no longer available to a variable, and therefore how the
   derivation is allowed to cancel its [x_eq_v] term out of that variable's
   at-least-one line. (M4-T2.)

   The Hall counting needs, per Hall variable, [sum_{v in S and decl(x)} x_eq_v >= 1]
   for the Hall value set [S], and it gets there from the declared-range at-least-one
   line by cancelling one term per declared value outside [S]. Each cancellation has to
   name a line that ESTABLISHES that the value is gone, at DEGREE-preserving strength --
   a [Weaken] axiom cancels the term but costs the degree (D-0009), so there is no
   weakening shortcut here and the four cases below are the whole of what is available.

   [Gone_below]/[Gone_above] are M4-T1's case: the value is outside the variable's
   current window and [excl] derives the globally valid `~<the bound> \/ ~x_eq_v` from
   the channelling and the ladder rungs.

   The other two are interior HOLES, which bounds consistency never had to look at and
   which Regin both reads and creates. A hole has no ladder chain to it; what states it
   is the trail entry that punched it, and lib/core/trace.ml writes that entry's line as
   `x <= v-1 \/ x >= v+1 \/ ~<facts>` in the ORDER encoding. Two ids of the channelling
   turn that into the direct encoding's currency, which is why both cases are expressible
   without a new constructor:

     - [Gone_hole_root]: the hole was established at LEVEL 0, so `~x_eq_v >= 1` is a
       consequence of the model on its own and [Explanation.defining] cites it as a unit
       -- exactly D-0064's per-bound rule, applied per hole. The cancellation is exact,
       nothing is left in the row, and a root conflict built on it still closes.
     - [Gone_hole facts]: the hole rests on a decision, so the unit would be FALSE. What
       is globally valid is the implication, and [Explanation.clause] states it:
       `~x_eq_v \/ ~facts`, RUP against the hole's own trace line plus two channelling
       halves. The facts stay in the derived row and are carried into the pruning's
       [Reason] alongside, which is what keeps the trace line true (I-P5). The price is
       that the derivation now contains a [Clause], so a ROOT conflict resting on one
       closes the D-0022 way -- see lib/core/search.ml's [rests_on_a_clause]. *)
type gone = Gone_below | Gone_above | Gone_hole_root | Gone_hole of Reason.t

type snap = {
  s_var : Var.t;
  s_name : string;
  s_dlo : int;
  s_dhi : int;
  s_lo : int;
  s_hi : int;
  (* Whether each current bound was established AT THE ROOT -- i.e. the trail entry
     supporting it belongs to level 0, or it has never moved off the declared bound.
     This is what decides whether [moved_bound_cancels] may cite a line for it, and it
     is a fact about where the bound CAME FROM, not about the level the solver is at
     now: a root-established bound is a consequence of the model and stays citable
     however deep the search has gone. *)
  s_lo_root : bool;
  s_hi_root : bool;
  (* Every DECLARED value this variable can no longer take, ascending, with the reason
     the derivation may cite for it. Snapshotted with everything else (I-X6): the hole
     entries close over the trail as it stood at the pruning, and the thunk never looks
     again. For a hole-free domain -- every domain M4-T1 ever saw -- this is two runs of
     [Gone_below]/[Gone_above] and costs no trail walk at all. *)
  s_gone : (int * gone) list;
}

type term = { x : Var.t; name : string; decl_lo : int; decl_hi : int }

type t = {
  terms : term array;
  enc : Encoding.t;
  (* The var-value-pair count above which [propagate] returns after stage 1 -- see the
     staging comment at the bottom of this file. *)
  cutoff : int;
  (* (x, z, v) -> the id of the .opb row "x <> v \/ z <> v", both orders of the pair
     present so a lookup never has to know which way [add_all_different] listed it. *)
  rows : (string * string * int, int) Hashtbl.t;
}

let name = "all_different_int"

(* DOMAIN, as of M4-T2, and the enumeration argument at [regin_pass] is what earns it:
   every value with no support is witnessed by a Hall set that this scans for, so the
   fixpoint leaves no unsupported value behind. The M2-T10 oracle
   (BAGUETTE_CONSISTENCY=1) holds this declaration to that, at every search node.

   It is also what tells [Engine] to wake this instance on an interior HOLE and not only
   on a bound move ([trigger_of_consistency]): a bounds-only trigger would starve a pass
   that reads [Domain.mem], which is precisely what the old [Bounds] tag would now buy. *)
let consistency = Propagator.Domain

(* GCS's measured threshold, in var-value pairs. *)
let default_cutoff = 256

(* [rows] is what [Encoding.add_all_different] returned, and the encoding is the live
   one: see the module header on I-X6. Reads each variable's domain, so it must be
   called before anything has narrowed it -- the same requirement, for the same D-0010
   reason, that [Linear.make] and [Ne.make] state. *)
let make ?(cutoff = default_cutoff) store enc ~rows vars =
  let tbl = Hashtbl.create (2 * List.length rows) in
  List.iter
    (fun ((x, z, v), cid) ->
      Hashtbl.replace tbl (x, z, v) cid;
      Hashtbl.replace tbl (z, x, v) cid)
    rows;
  let terms =
    Array.of_list
      (List.map
         (fun x ->
           let d = Store.get store x in
           { x; name = Store.name store x; decl_lo = Domain.lo d; decl_hi = Domain.hi d })
         vars)
  in
  { terms; enc; cutoff; rows = tbl }

let vars t = Array.to_list (Array.map (fun tm -> tm.x) t.terms)

(* The level the trail entry supporting this bound was pushed at, or 0 for a bound that
   has never moved. [Store.level_of_index] counts the open level marks at or below the
   entry, so this is the level the bound BELONGS to and not the one in force now. *)
let established_at_root store v ~lower =
  let sup = if lower then Store.lo_support store v else Store.hi_support store v in
  sup = Store.no_support || Store.level_of_index store sup = 0

let range a b = List.init (Stdlib.max 0 (b - a + 1)) (fun i -> a + i)

(* The trail POSITION of the entry that took [value] out of [var], or [None].

   [Store.remover] answers the same question with the entry, and the entry is not enough
   here: what decides whether a hole may be cited as a unit is the LEVEL it was
   established at, and [Store.entry] does not carry one ([Store.level_of_index] counts
   the level marks at or below a position instead). Same rule, same "a value leaves a
   domain once and stays gone until the backtrack that pops the entry that removed it",
   so this finds at most one and stops at the first hit.

   [None] is a hole with no trail entry behind it -- a declared gap, which
   lib/flatzinc/compile.ml's [reject_set_domain] refuses, so no model reaches it. *)
let remover_index store ~var value =
  let rec go i =
    if i < 0 then None
    else
      let e = Store.trail_entry store i in
      if
        Var.equal e.Store.var var && Domain.mem e.Store.old value
        && not (Domain.mem e.Store.now value)
      then Some i
      else go (i - 1)
  in
  go (Store.trail_length store - 1)

let hole_cite store var value =
  match remover_index store ~var value with
  | Some i when Store.level_of_index store i = 0 -> Gone_hole_root
  | Some i -> Gone_hole (Store.trail_entry store i).Store.reason
  | None -> Gone_hole Reason.none

(* [s_gone], ascending: below the window, then the holes inside it, then above. The
   order is what makes an [alo_over] over an INTERVAL value set emit exactly the
   summands M4-T1's [alo_window] emitted, in the same order, so stage 1's proofs are
   unchanged byte for byte. *)
let gone_of store tm d =
  let lo = Domain.lo d and hi = Domain.hi d in
  let holes =
    if not (Domain.has_holes d) then []
    else
      List.filter_map
        (fun v -> if Domain.mem d v then None else Some (v, hole_cite store tm.x v))
        (range lo hi)
  in
  List.map (fun v -> (v, Gone_below)) (range tm.decl_lo (lo - 1))
  @ holes
  @ List.map (fun v -> (v, Gone_above)) (range (hi + 1) tm.decl_hi)

let snap_of store tm =
  let d = Store.get store tm.x in
  {
    s_var = tm.x;
    s_name = tm.name;
    s_dlo = tm.decl_lo;
    s_dhi = tm.decl_hi;
    s_lo = Domain.lo d;
    s_hi = Domain.hi d;
    s_lo_root = established_at_root store tm.x ~lower:true;
    s_hi_root = established_at_root store tm.x ~lower:false;
    s_gone = gone_of store tm d;
  }

(* ------------------------------------------------------------------ explanations *)

(* An id this derivation must name, or a legible failure. [None] here means the proof
   line does not exist, which happens for exactly one reason: no proof is being written,
   so [Encoding.start_proof] never materialised the direct encoding. A propagator that
   built an explanation nobody will render has done nothing wrong; one that renders a
   [Model_row] pointing at a line that is not on the page has, and it would show up as a
   veripb rejection a long way from here. *)
let cid_of what = function
  | Some id -> id
  | None ->
      invalid_arg
        (Printf.sprintf
           "Alldiff: %s has no constraint id. The direct encoding is materialised by \
            Encoding.start_proof, from the Encoding.request_direct calls \
            lib/flatzinc/compile.ml makes for every all_different scope; an explanation \
            forced without one means the two have drifted apart."
           what)

let row t s1 s2 v =
  match Hashtbl.find_opt t.rows (s1.s_name, s2.s_name, v) with
  | Some id -> id
  | None ->
      invalid_arg
        (Printf.sprintf
           "Alldiff: no model row for %s <> %d \\/ %s <> %d. Encoding.add_all_different \
            posts one per pair per SHARED declared value, so this means the pair's \
            declared domains do not both contain %d."
           s1.s_name v s2.s_name v v)

let model_row id = Explanation.model_row id
let cite id = Explanation.term 1 (model_row id)

(* The at-most-one line for ONE PAIR at one value:  ~x_eq_v + ~z_eq_v >= 1.

   The five ids are the pair's own .opb clause and the four channelling halves

     M          ~x_ge_v \/ x_ge_(v+1) \/ ~z_ge_v \/ z_ge_(v+1)     (the model row)
     d_lo(x,v)  ~x_eq_v \/ x_ge_v          d_hi(x,v)  ~x_eq_v \/ ~x_ge_(v+1)
     d_lo(z,v)  ...                        d_hi(z,v)  ...

   Each channelling line cancels exactly one of M's order literals to a constant, so
   adding all five leaves [n_x ~x_eq_v + n_z ~z_eq_v >= 1] where n_x is how many of x's
   two halves EXIST -- one of them is the constant true at a declared bound, and
   [Encoding.direct_lo_id]/[direct_hi_id] answer [None] there for exactly that reason.
   Padding each side up to coefficient 2 with its own literal axiom (D-0009: an axiom
   asserts nothing, and here it only adds a term) makes the shape uniform, and one
   division by 2 gives the line. *)
let pair_amo t sx sz v =
  let halves s =
    List.filter_map Fun.id
      [ Encoding.direct_lo_id t.enc s.s_name v; Encoding.direct_hi_id t.enc s.s_name v ]
  in
  let hx = halves sx and hz = halves sz in
  let pad s n =
    if n >= 2 then []
    else [ Explanation.weaken [ (2 - n, Lit.negate (Lit.eq s.s_name v)) ] ]
  in
  Explanation.combine
    ((cite (row t sx sz v) :: List.map cite (hx @ hz))
    @ pad sx (List.length hx)
    @ pad sz (List.length hz))
    2

(* At-most-one over a SET of variables at one value: sum_{x in ss} ~x_eq_v >= |ss| - 1.

   Pairwise at-most-one does not give this by summing -- adding all C(m,2) pairs and
   dividing by m-1 gives degree ceil(m/2), not m-1 -- so it is built by induction on the
   set, which is where [Combine]'s divisor does its second piece of real work:

     A over S (|S| = m, degree m-1), plus the m pairs (u, x) for x in S, gives
        m * (sum_S ~x_eq_v + ~u_eq_v)  >=  (m-1)^2 + m  =  m(m-1) + 1
     and dividing by m rounds the degree UP to m, which is |S + {u}| - 1.

   [ss] has at least two members; the caller handles the shorter cases, and the one-member
   case is not a weaker line but a different rule (a bare literal axiom) -- see
   [core_summands]. *)
let amo t ss v =
  match ss with
  | [] | [ _ ] -> invalid_arg "Alldiff.amo: at least two variables"
  | first :: second :: rest ->
      let rec grow acc have = function
        | [] -> acc
        | u :: more ->
            let m = List.length have in
            let step =
              Explanation.combine
                (Explanation.term (m - 1) acc
                :: List.map (fun s -> Explanation.term 1 (pair_amo t u s v)) have)
                m
            in
            grow step (have @ [ u ]) more
      in
      grow (pair_amo t first second v) [ first; second ] rest

(* "x cannot take v", for a v outside x's CURRENT window but inside its declared one,
   as a globally valid line carrying the bound it rests on as a literal:

     v < lo(x):   ~x_ge_lo(x) \/ ~x_eq_v     from d_hi(x,v) and the ladder rungs
                                             v+1 .. lo(x)-1, which telescope
     v > hi(x):   x_ge_(hi(x)+1) \/ ~x_eq_v  from d_lo(x,v) and the rungs
                                             hi(x)+1 .. v-1

   The rungs are [Encoding.consistency_id]'s rows, x_ge_(u+1) -> x_ge_u, which exist for
   every u strictly inside the declared range -- and every u this asks for is, because
   v is inside the declared range and the current bound it is being compared against is
   strictly inside it too (if it were not, there would be no such v). *)
let excl t s v =
  if v < s.s_lo then
    Explanation.combine
      (cite (cid_of "d_hi" (Encoding.direct_hi_id t.enc s.s_name v))
      :: List.map
           (fun u ->
             cite (cid_of "ladder rung" (Encoding.consistency_id t.enc s.s_name u)))
           (range (v + 1) (s.s_lo - 1)))
      1
  else if v > s.s_hi then
    Explanation.combine
      (cite (cid_of "d_lo" (Encoding.direct_lo_id t.enc s.s_name v))
      :: List.map
           (fun u ->
             cite (cid_of "ladder rung" (Encoding.consistency_id t.enc s.s_name u)))
           (range (s.s_hi + 1) (v - 1)))
      1
  else invalid_arg "Alldiff.excl: the value is inside the current window"

(* One cancellation, per [gone]'s four cases -- see that type for the argument. Every
   one of them is a SUMMAND of the at-least-one line's [Combine], every one cancels
   exactly one [x_eq_v] term and leaves the degree at 1, and none of them is a new
   constructor: M4-T1 spent [Combine]/[Weaken]/[Model_row], M4-T7 spent [Defining], and
   this row spends nothing. *)
(* How many cancellations of each kind this process has built. Not diagnostics: the
   [Gone_hole] branch is the one only a DECISION can reach, and a test that cannot tell
   whether its sweep reached it is a test that reports coverage it does not have
   (test/unit/test_prop.ml's Regin sweep is the caller). Two int refs, incremented where
   the choice is made, is the only thing that can say so exactly -- reading it off the
   .pbp is a proxy, and a proxy that silently stops matching is worse than no check. *)
let root_hole_cancels = ref 0
let deep_hole_cancels = ref 0

let exclude_summand t s v g =
  match g with
  | Gone_below | Gone_above -> Explanation.term 1 (excl t s v)
  | Gone_hole_root ->
      incr root_hole_cancels;
      Explanation.defining 1 (Lit.ne s.s_name v)
  | Gone_hole r ->
      incr deep_hole_cancels;
      Explanation.term 1
        (Explanation.clause (Lit.ne s.s_name v :: List.map Lit.negate (Reason.lits r)))

(* The at-least-one line for a Hall variable, narrowed from its DECLARED range to the
   Hall interval:  sum_{v in [a,b] and decl(x)} x_eq_v >= 1, plus the bound literals
   [excl] carried in.

   [Encoding.at_least_one_id] is the declared-range line, itself derived from the
   channelling at [start_proof] (PROOF-FORMAT section 3: exactly-one is derived, never
   asserted). Adding one [excl] per declared value outside [a, b] cancels that value's
   term against a unit and leaves the degree at 1. Every such value is outside the
   variable's current window too, because a Hall variable's window is inside [a, b]. *)
(* M4-T2 generalised this from an INTERVAL to an arbitrary value set, which is the
   whole of what Regin needs from the derivation: a matching-based Hall set saturates a
   SET of values that need not be contiguous, and everything else about the counting is
   unchanged. [keep] is membership of that set.

   The excluded values are read off [s_gone] rather than recomputed, because the
   *reason* each one is gone is what decides which line cancels it. For an interval
   [keep] this is value-for-value and order-for-order what M4-T1 computed: a Hall
   variable's window is inside the interval, so every declared value outside the
   interval is outside the window too, and no hole of its is ever excluded. *)
let alo_over t s ~keep =
  Explanation.combine
    (cite (cid_of "at-least-one" (Encoding.at_least_one_id t.enc s.s_name))
    :: List.filter_map
         (fun (v, g) -> if keep v then None else Some (exclude_summand t s v g))
         s.s_gone)
    1

(* The counting argument itself: one at-least-one per Hall variable, one at-most-one per
   Hall value over whichever variables could take it. [extra] is the variable being
   pruned, which joins the at-most-one lines but contributes no at-least-one -- that
   asymmetry is exactly why the sum leaves ITS terms behind and cancels everything else.

   A value only one variable in scope can take gets a literal axiom instead of an
   at-most-one line: "at most one of {x} takes v" IS ~x_eq_v >= 0, and a value no
   variable can take gets nothing, because there is no term to cancel. *)
let core_summands t ~vals ~halls ~extra =
  let all = halls @ Option.to_list extra in
  let keep v = List.mem v vals in
  List.map (fun s -> Explanation.term 1 (alo_over t s ~keep)) halls
  @ List.concat_map
      (fun v ->
        match List.filter (fun s -> s.s_dlo <= v && v <= s.s_dhi) all with
        | [] -> []
        | [ s ] -> [ Explanation.weaken [ (1, Lit.negate (Lit.eq s.s_name v)) ] ]
        | ss -> [ Explanation.term 1 (amo t ss v) ])
      vals

(* The bound literals [alo_window] leaves in the row, cancelled by the lines that
   already state those bounds. Until M4-T7 this was the one place in this module where
   the reified explanation ADT did not reach; read this and explanation.ml's [Defining]
   section together before changing it.

   [alo_window] narrows a Hall variable's at-least-one line with one [excl] per declared
   value outside the interval, and each [excl] carries the bound it rests on into the sum
   as a literal: [a - decl_lo] copies of ~x_ge_lo(x), and [decl_hi - b] of x_ge_(hi(x)+1).
   For a PRUNING, leaving them there is already right -- the derived row is then the
   globally valid "the pruning, disjoined with the bounds it read", which is the shape
   [Ne] already has. For a CONFLICT it is not enough: lib/core/search.ml cites a root
   conflict's derivation to `conclusion UNSAT`, and a row with literals left in it is not
   contradicting, which 3.0.2 says in as many words ("The constraint with ID n is not
   contradicting, as specified by the hint") and which M1-T17 already found from the
   other end.

   Cancelling them needs "the id of the line that establishes this bound fact" -- D-0009's
   open ADT gap, which M4-T7 closed with [Explanation.defining]. It resolves through
   [Justify.defining_lit] to the UNIT line already stating the bound (the trace line, in
   practice), minting one only if there is none, and the cancellation is exact: the term
   goes and the degree stays. Two things follow, and both are the row's point:

   - the derivation no longer contains an [Explanation.Clause], so
     [Search.rests_on_a_clause] is false for it and `conclusion UNSAT` cites THIS
     module's [pol] rather than the D-0022 empty clause. M4-T1's stand-in
     ([Explanation.clause [lit]]) was the same arithmetic wearing a label the search reads
     as "not numeric", which is D-0061's recorded cost.
   - the test is now PER BOUND and is the level the bound was ESTABLISHED at, not the
     level the solver is at. A bound the root fixpoint set is a consequence of the model,
     so its unit line is true and citable at any depth; a bound a decision set is not, and
     a unit line for it would be false. M4-T1 could only say "level 0 or nothing" and
     switched the whole cancellation off under a decision; this says it bound by bound, so
     a Hall inference made three decisions deep still cancels whatever the root
     established. [snap.s_lo_root]/[s_hi_root] carry the test, snapshotted with everything
     else the derivation reads (I-X6).

   A bound that is neither -- moved under a decision -- is simply not cancelled, and the
   row keeps its literal, which is exactly the sound shape the first paragraph describes. *)

(* The Hall variables' share: one copy of ~x_ge_lo(x) per declared value below the
   interval and one of x_ge_(hi(x)+1) per declared value above it, which is exactly how
   many [excl] summands [alo_window] added in each direction. A Hall variable's window is
   inside [a, b], so [below > 0] implies its lo really has moved and [Lit.ge] below names
   a literal the encoding has (likewise [above] and [Lit.le]). *)
let hall_cancels ~keep ~halls =
  List.concat_map
    (fun s ->
      let count want =
        List.length (List.filter (fun (v, g) -> (not (keep v)) && g = want) s.s_gone)
      in
      let below = count Gone_below and above = count Gone_above in
      (if below > 0 && s.s_lo_root then
         [ Explanation.defining below (Lit.ge s.s_name s.s_lo) ]
       else [])
      @
      if above > 0 && s.s_hi_root then
        [ Explanation.defining above (Lit.le s.s_name s.s_hi) ]
      else [])
    halls

(* The pruned variable's own share, and it is ONE copy in ONE direction: the telescoping
   channelling sum leaves ~y_ge_lo(y) on a lower push and y_ge_(hi(y)+1) on an upper one,
   and nothing else of y's survives. [y] has no [alo_window] -- that asymmetry is the
   whole reason its terms are what the derivation is left holding -- so it must not be
   handed to [moved_bound_cancels], which counts a Hall variable's [excl] summands.

   The same per-bound root test as above, and for the same reason. *)
let target_cancel ~y ~lower =
  if lower then
    if y.s_lo > y.s_dlo && y.s_lo_root then
      [ Explanation.defining 1 (Lit.ge y.s_name y.s_lo) ]
    else []
  else if y.s_hi < y.s_dhi && y.s_hi_root then
    [ Explanation.defining 1 (Lit.le y.s_name y.s_hi) ]
  else []

(* A pruning: raise lo(y) past the Hall interval, or lower hi(y) below it.

   After the core sum, y's excluded values are stated as [sum ~y_eq_v >= |...|] over
   every Hall value y's DECLARED domain holds. Two more groups turn that into a bound:

     - a literal axiom [Lit.eq y v] per value the pruning does not need, which drops that
       term and one unit of degree (D-0009's weakening, in its own direction);
     - the forward channelling clause y_eq_v \/ ~y_ge_v \/ y_ge_(v+1) for each value it
       does, which telescopes: every rung between the ends cancels, leaving
       ~y_ge_lo(y) + y_ge_(b+1) >= 1 for a lower push and ~y_ge_a + y_ge_(hi(y)+1) >= 1
       for an upper one. Those are the bound the propagator just set, disjoined with the
       bound it read -- again the [Ne] shape, and globally valid. *)
let prune_summands t ~a ~b ~halls ~y ~lower =
  let keep, drop =
    if lower then (range y.s_lo b, range (Stdlib.max a y.s_dlo) (y.s_lo - 1))
    else (range a y.s_hi, range (y.s_hi + 1) (Stdlib.min b y.s_dhi))
  in
  core_summands t ~vals:(range a b) ~halls ~extra:(Some y)
  @ List.map (fun v -> Explanation.weaken [ (1, Lit.eq y.s_name v) ]) drop
  @ List.map
      (fun v -> cite (cid_of "d_fwd" (Encoding.direct_fwd_id t.enc y.s_name v)))
      keep

(* THE OTHER END OF AN EMPTYING PUSH (M4-T2, and a defect M4-T1 shipped latent).

   [pass]'s pigeonhole arm pushes a CONTAINED variable's lower bound to [b + 1], which is
   past its current upper bound, and relies on [Store.apply]'s [Failed] arm to turn that
   into the conflict. For the conflict to be PROVABLE the row has to come out [0 >= 1],
   and the telescoping channelling sum leaves [y_ge_(b+1)] in it. M4-T1's reading was
   that this literal is the constant false and drops -- which is true exactly when
   [b + 1 > decl_hi(y)], and that is what every model M4-T1 and M4-T7 reached happened to
   satisfy. It is NOT true when y's upper bound has MOVED: then [b + 1] is a literal the
   encoding really has, the row derives the perfectly valid [y >= b + 1] instead of a
   contradiction, and 3.0.2 answers "the constraint with ID n is not contradicting".
   Measured, on the first model whose Regin holes let an `int_lin_le` settle a bound past
   them.

   What closes it is the ladder: the rungs [y_ge_(u+1) -> y_ge_u] for u in
   [hi(y) + 1 .. b] telescope to [~y_ge_(b+1) + y_ge_(hi(y)+1) >= 1], which turns the
   residue into [y_ge_(hi(y)+1)], and the line stating y's own upper bound cancels that
   exactly -- D-0064's [Defining], and its per-bound root test, once more.

   The test [b + 1 > y.s_hi] is what tells the two arms apart and is not a heuristic: in
   the [n = k] arm the pushed variable is NOT contained, so its upper bound is strictly
   above [b] and the residue IS the pruning and must stay; in the [n > k] arm it is
   contained, so the push always oversteps. Only the lower direction needs this, because
   [pass] only ever empties a domain downward-out-of ([push ~lower:true]); the mirror
   case is written out in this comment rather than in code because nothing reaches it. *)
let overshoot_cancel t ~b ~y ~lower =
  if lower && b + 1 > y.s_hi && y.s_hi < y.s_dhi && y.s_hi_root then
    List.map
      (fun u -> cite (cid_of "ladder rung" (Encoding.consistency_id t.enc y.s_name u)))
      (range (y.s_hi + 1) b)
    @ [ Explanation.defining 1 (Lit.le y.s_name y.s_hi) ]
  else []

let prune_expl t ~a ~b ~halls ~y ~lower =
  Explanation.deferred (fun () ->
      Explanation.combine
        (prune_summands t ~a ~b ~halls ~y ~lower
        @ hall_cancels ~keep:(fun v -> a <= v && v <= b) ~halls
        @ target_cancel ~y ~lower
        @ overshoot_cancel t ~b ~y ~lower)
        1)

(* ------------------------------------------------------ M4-T2: a VALUE is removed

   The same counting, stopped one step earlier. After [core_summands] over a tight set
   [halls] saturating the value set [vals], with [y] joining the at-most-one lines and
   contributing no at-least-one, the row is

     sum_{w in vals and decl(y)} ~y_eq_w  >=  |vals and decl(y)|   (+ what [halls]
                                                                    could not cancel)

   -- "y takes NONE of the Hall values". M4-T1 turned that into a BOUND by adding the
   forward channelling clause for the values it kept, which telescopes; a domain-
   consistent pruning wants one value instead, so every other value is dropped by a
   literal axiom ([Weaken], D-0009's own direction: it cancels the term and costs the one
   unit of degree that term was carrying) and what is left is

     ~y_eq_value >= 1   (+ the same leftovers)

   which is the pruning, disjoined with the facts it rests on -- the [Ne] shape, sound at
   any level. Nothing here is new machinery: it is [core_summands] plus [Weaken]. *)
let remove_summands t ~vals ~halls ~y ~value =
  let mine = List.filter (fun w -> y.s_dlo <= w && w <= y.s_dhi) vals in
  core_summands t ~vals ~halls ~extra:(Some y)
  @ List.filter_map
      (fun w ->
        if w = value then None else Some (Explanation.weaken [ (1, Lit.eq y.s_name w) ]))
      mine

let remove_expl t ~vals ~halls ~y ~value =
  let keep v = List.mem v vals in
  Explanation.deferred (fun () ->
      Explanation.combine
        (remove_summands t ~vals ~halls ~y ~value @ hall_cancels ~keep ~halls)
        1)

(* THE PIGEONHOLE over a value SET, which is the M4-T2 shape of the sentence this
   module's header already makes about an interval: with no [extra] at all and one more
   variable than there are values, every term of the core sum cancels and the degree does
   not, so the row is [0 >= 1].

   [halls] here is the WHOLE violating set -- |halls| = |vals| + 1 -- and that one
   difference is the whole difference between a pruning and a refutation. It is reported
   the way [pass] reports its own: handed to a mutator that must fail, so
   [Store.apply]'s [Failed] arm pairs it with [Reason.none] and no `rup` conflict line
   claims a counting argument as reverse unit propagation (I-X10, D-0040). *)
let conflict_expl t ~vals ~halls =
  let keep v = List.mem v vals in
  Explanation.deferred (fun () ->
      Explanation.combine
        (core_summands t ~vals ~halls ~extra:None @ hall_cancels ~keep ~halls)
        1)

(* ---------------------------------------------------------------------- reasons *)

(* A Hall variable is in the set because BOTH its bounds are where they are, so both are
   facts. [Reason.lit_of_fact] drops the ones sitting at a declared bound, which is the
   same test [excl] makes when it decides whether a value is outside the window -- the
   two cannot disagree because both read the same snapshot. *)
let hall_facts ~keep halls =
  List.concat_map
    (fun s ->
      [
        Reason.at_least ~name:s.s_name ~decl:s.s_dlo s.s_lo;
        Reason.at_most ~name:s.s_name ~decl:s.s_dhi s.s_hi;
      ]
      (* M4-T2. A hole the derivation had to cancel with [Gone_hole] leaves that hole's
         OWN facts in the row, so they are facts this pruning rests on and the trace
         line's tail owes them (I-P5). Only the EXCLUDED holes: a hole inside the value
         set is never cancelled, contributes nothing, and naming it would put a fact in
         the tail that the derivation does not read. For an interval value set there are
         no excluded holes at all, which is why stage 1's reasons are unchanged. *)
      @ List.concat_map
          (fun (v, g) -> match g with Gone_hole r when not (keep v) -> r | _ -> [])
          s.s_gone)
    halls

let prune_reason ~keep halls y ~lower =
  (if lower then Reason.at_least ~name:y.s_name ~decl:y.s_dlo y.s_lo
   else Reason.at_most ~name:y.s_name ~decl:y.s_dhi y.s_hi)
  :: hall_facts ~keep halls

(* A value removal reads no bound of [y] -- the counting is over DECLARED domains and
   [y]'s window never enters the row. Both of [y]'s bounds are named anyway, and that is
   deliberate rather than sloppy: the derivation's top level weakens [y]'s own [y_eq_w]
   terms away, so [Explanation.top_weaken_owners] names [y] and D-0026's agreement check
   requires the reason to name it too. A tail with a fact the derivation did not need is
   a WEAKER trace line, which is sound; a tail missing one is I-P5. *)
let remove_reason ~keep halls y =
  Reason.at_least ~name:y.s_name ~decl:y.s_dlo y.s_lo
  :: Reason.at_most ~name:y.s_name ~decl:y.s_dhi y.s_hi
  :: hall_facts ~keep halls

(* ------------------------------------------------------------------- propagation *)

(* The variables whose current window sits inside [a, b]. *)
let contained snaps ~a ~b = List.filter (fun s -> a <= s.s_lo && s.s_hi <= b) snaps

exception Found of Store.conflict
exception Moved

(* One pass: every candidate interval, in a fixed order, pushing what it can. Returns
   [true] if anything moved, so [propagate] can re-run; raises [Found] on a conflict,
   which is the one non-local exit -- a conflict abandons the pass, and unwinding
   through the interval loops with a flag would be the same control flow spelled longer.

   Candidate endpoints are the current lo and hi values, which is the standard
   restriction: a Hall interval can always be shrunk to one whose ends are a variable's
   bounds without losing any variable from its set.

   It also returns as soon as one push lands ([Moved]), so every interval it examines is
   examined against a CURRENT snapshot rather than one a push earlier in the same pass
   has invalidated. Re-snapshotting is the cheap half of this loop and a stale Hall set
   is the kind of thing that is sound by luck -- containment computed from wider, older
   bounds is a subset of the true one -- which is not a property worth resting on. *)
let pass t store =
  let snaps = Array.to_list (Array.map (snap_of store) t.terms) in
  let los = List.sort_uniq compare (List.map (fun s -> s.s_lo) snaps) in
  let his = List.sort_uniq compare (List.map (fun s -> s.s_hi) snaps) in
  (* One push, with both halves of D-0026 built from the same snapshot. Returns through
     [Found]/[Moved]; a push that changes nothing (the bound is already there) falls
     through, which is how [Unchanged] can happen at all here. *)
  let push ~halls ~a ~b ~y ~lower x bound =
    let j =
      Reason.because
        ~concludes:
          (Some
             (if lower then Reason.at_least ~name:y.s_name ~decl:y.s_dlo bound
              else Reason.at_most ~name:y.s_name ~decl:y.s_dhi bound))
        (prune_reason ~keep:(fun v -> a <= v && v <= b) halls y ~lower)
        (prune_expl t ~a ~b ~halls ~y ~lower)
    in
    match
      if lower then Store.set_lo store x bound j else Store.set_hi store x bound j
    with
    | Store.Conflict c -> raise (Found c)
    | Store.Changed -> raise Moved
    | Store.Unchanged -> ()
  in
  List.iter
    (fun a ->
      List.iter
        (fun b ->
          if b >= a then
            let all_in = contained snaps ~a ~b in
            let k = b - a + 1 in
            let n = List.length all_in in
            (* THE PIGEONHOLE, REALISED AS A PRUNING THAT EMPTIES A DOMAIN, and that is
               not a roundabout way to call [Store.conflict] -- it is what makes the
               conflict provable.

               [Store.conflict] takes the propagator's own reason facts, and
               lib/core/trace.ml's [conflict_line] then writes `rup ~fact ... >= 1` --
               "these bounds are jointly impossible". For a Hall conflict that claim IS
               the Hall argument, so it is not reverse unit propagation and 3.0.2 refuses
               it. Pushing one surplus variable out of an interval it is confined to
               reaches the same contradiction through [Store.apply]'s [Failed] arm, which
               pairs the derivation with [Reason.none] -- deliberately, and its own
               comment says why -- so no conflict line is written and what closes the
               root is this module's derivation, which really does derive [0 >= 1].

               [all_in] is split rather than used whole: the Hall set must be EXACTLY as
               big as the interval for the counting to cancel, so the first [k] are the
               set and the (k+1)th is the variable pushed out of it. Which [k] is
               immaterial to soundness and fixed by [t.terms] order for determinism. *)
            if n > k then
              let halls = List.filteri (fun i _ -> i < k) all_in in
              let y = List.nth all_in k in
              push ~halls ~a ~b ~y ~lower:true y.s_var (b + 1)
            else if n = k then
              Array.iter
                (fun tm ->
                  let y = snap_of store tm in
                  if not (List.exists (fun s -> s.s_name = y.s_name) all_in) then
                    if a <= y.s_lo && y.s_lo <= b then
                      push ~halls:all_in ~a ~b ~y ~lower:true tm.x (b + 1)
                    else if a <= y.s_hi && y.s_hi <= b then
                      push ~halls:all_in ~a ~b ~y ~lower:false tm.x (a - 1))
                t.terms)
        his)
    los;
  false

(* Stage 1 of the two-stage design (D-0004, GCS-COMPARISON section 3): Hall intervals
   over bounds. A second stage -- the matching/SCC pass M4-T2 owns -- would be sequenced
   after this one *in this function*, and would run only when this pass inferred nothing,
   so that cheaper propagators react first. Nothing about the interface below has to
   change for it: [consistency] would become [Domain] and this loop would keep its shape.
   It is not written, and this comment is not a promise that it is nearly written. *)
(* ================================================== M4-T2: stage 2, Regin's matching

   THE FILTERING. Build the value graph (a variable on one side, a value on the other,
   an edge when the value is in the variable's current domain) and take a maximum
   matching. An edge that lies in NO maximum matching is a value no solution of the
   constraint can give that variable, and removing all of them is domain consistency.

   THE JUSTIFICATION, which is the part this row exists to settle. D-0004 has said since
   2026-09-14 that Regin's pruning "does not have an obvious cheap justification". It
   has one, it is the SAME counting argument M4-T1 already built, and the bridge is a
   fact about matchings rather than anything new about proofs:

     Let M be a matching saturating the variables, u a variable, v = M(u), and let
     K be {u} together with every variable reachable from u in the digraph
     "x -> x' when M(x') is in dom(x)". If no variable of K has a FREE value (one M
     leaves unmatched) in its domain, then for every x in K and every w in dom(x), w is
     M(x') for some x' -- and x' is reachable from x, hence in K. So

         N(K) = M(K)   and   |N(K)| = |K|

     -- K is a HALL SET, and its value set N(K) is exactly the set M matches it to. Any
     y outside K therefore takes none of those values.

     And conversely: if (y, v) is in no maximum matching then, writing u = M^-1(v), u can
     reach neither y nor a free value (either would be an augmenting alternating walk
     giving a matching that contains (y, v)), so the K built from u is tight, contains v
     in its value set, and excludes y. **Every Regin pruning is witnessed by a Hall set**,
     and enumerating K over every u is therefore COMPLETE -- which is what lets this
     declare [Domain] rather than "stronger than bounds by an amount nobody measured".

   So the derivation is [core_summands] over that K and that value set: one at-least-one
   line per member of K, one at-most-one line per value of N(K) over K + {y}, and the
   whole of K cancels. The only thing M4-T1's version could not do is the one thing a
   non-interval value set forces -- narrowing a Hall variable's at-least-one line past an
   interior HOLE -- and [gone] above is that, in the existing ADT.

   **No new [Explanation] constructor.** The no-new-constructor rule has been spent once
   in nine rows (D-0064) and is not spent here.

   THE CONFLICT is the same statement one member short. If no matching saturates the
   variables, the failed augmenting search from the first unmatched variable x0 has
   visited a set of values B, every one of them matched (or it would have augmented) to a
   variable it then visited; so A = {x0} + the variables matching B has N(A) = B and
   |A| = |B| + 1. Removing B from x0 empties x0's domain -- dom(x0) is inside B -- and the
   emptying is what makes the conflict provable, for the reason [pass] states above at
   length: [Store.apply]'s [Failed] arm pairs the derivation with [Reason.none] so no
   `rup` conflict line claims the counting argument as reverse unit propagation.

   THE ALGORITHM is Kuhn's augmenting path and a reachability sweep per variable, which
   is O(n^2 d) per pass rather than Regin's O(n^2 d) matching plus one Tarjan SCC pass.
   Deliberately, and for M4-T1's reason restated: this row is an experiment about the
   JUSTIFICATION, the models it may ship are bounded to single/low-double-digit domains
   by the memory rule, and the SCC decomposition is an OPTIMISATION of the enumeration
   above -- the strongly connected components ARE the sets K, found once instead of n
   times. An implementation whose completeness is the paragraph above is worth more here
   than one whose completeness is a citation. *)

(* D-0043's conclusion for a value removal. Same rule as lib/core/prop/ne.ml's
   [removal_conclusion] and for the same reason: removing a value AT a bound settles that
   bound past any holes above (below) it and concludes the bound it landed on, while
   removing an interior value concludes `x <> v`, which is a two-literal clause and not a
   [Reason.fact] in either direction. *)
let removal_conclusion y d w =
  if w = Domain.lo d then (
    let v = ref (w + 1) in
    while !v <= Domain.hi d && Domain.is_hole d !v do
      incr v
    done;
    Some (Reason.at_least ~name:y.s_name ~decl:y.s_dlo !v))
  else if w = Domain.hi d then (
    let v = ref (w - 1) in
    while !v >= Domain.lo d && Domain.is_hole d !v do
      decr v
    done;
    Some (Reason.at_most ~name:y.s_name ~decl:y.s_dhi !v))
  else None

(* One removal, with both halves of D-0026 built from the same snapshot, returning
   through [Found]/[Moved] exactly as [pass]'s [push] does. *)
let remove_one t store ~halls ~vals ~y_tm value =
  let y = snap_of store y_tm in
  let d = Store.get store y_tm.x in
  let keep v = List.mem v vals in
  let j =
    Reason.because
      ~concludes:(removal_conclusion y d value)
      (remove_reason ~keep halls y)
      (remove_expl t ~vals ~halls ~y ~value)
  in
  match Store.remove store y_tm.x value j with
  | Store.Conflict c -> raise (Found c)
  | Store.Changed -> raise Moved
  | Store.Unchanged -> ()

(* One Regin pass. Raises [Moved] as soon as one removal lands, for the reason [pass]
   gives: every set it reasons about is then computed from a CURRENT snapshot rather than
   one an earlier removal in the same pass has invalidated. *)
let regin_pass t store =
  let n = Array.length t.terms in
  if n > 0 then (
    let doms = Array.map (fun tm -> Store.get store tm.x) t.terms in
    let values =
      Array.of_list
        (List.sort_uniq compare (List.concat_map Domain.to_list (Array.to_list doms)))
    in
    let nv = Array.length values in
    let holds i vi = Domain.mem doms.(i) values.(vi) in
    (* [mval.(i)] is the index of the value matched to variable [i], [mvar.(vi)] the
       variable matched to value [vi]; [-1] is unmatched on both sides. *)
    let mval = Array.make n (-1) and mvar = Array.make (Stdlib.max 1 nv) (-1) in
    let rec augment i seen =
      let rec go vi =
        if vi >= nv then false
        else if (not (holds i vi)) || seen.(vi) then go (vi + 1)
        else (
          seen.(vi) <- true;
          if mvar.(vi) = -1 || augment mvar.(vi) seen then (
            mvar.(vi) <- i;
            mval.(i) <- vi;
            true)
          else go (vi + 1))
      in
      go 0
    in
    let failed = ref None in
    for i = 0 to n - 1 do
      if Option.is_none !failed then
        let seen = Array.make (Stdlib.max 1 nv) false in
        if not (augment i seen) then failed := Some (i, seen)
    done;
    let snaps_of pick =
      List.filter_map
        (fun i -> if pick i then Some (snap_of store t.terms.(i)) else None)
        (range 0 (n - 1))
    in
    match !failed with
    | Some (x0, seen) -> (
        (* No matching saturates the scope. [seen] is the value set B the failed
           augmenting search reached; every one of those values is matched (an unmatched
           one would have ended the search successfully), and A is those variables
           together with x0, so N(A) = B and |A| = |B| + 1. *)
        let vals =
          List.filter_map
            (fun vi -> if seen.(vi) then Some values.(vi) else None)
            (range 0 (nv - 1))
        in
        let halls =
          snap_of store t.terms.(x0)
          :: List.filter_map
               (fun vi ->
                 if seen.(vi) then Some (snap_of store t.terms.(mvar.(vi))) else None)
               (range 0 (nv - 1))
        in
        let x0_tm = t.terms.(x0) in
        let j =
          Reason.because ~concludes:None Reason.none (conflict_expl t ~vals ~halls)
        in
        (* Must fail: the bound is one past the variable's own upper bound. *)
        match Store.set_lo store x0_tm.x (Domain.hi doms.(x0) + 1) j with
        | Store.Conflict c -> raise (Found c)
        | Store.Changed | Store.Unchanged ->
            invalid_arg
              "Alldiff.regin_pass: the emptying push did not fail, so the pigeonhole \
               derivation would be attached to a change that landed")
    | None ->
        List.iter
          (fun u ->
            (* [ink]: {u} and everything reachable from it. *)
            let ink = Array.make n false in
            ink.(u) <- true;
            let stack = ref [ u ] in
            while !stack <> [] do
              let i = List.hd !stack in
              stack := List.tl !stack;
              for j = 0 to n - 1 do
                if (not ink.(j)) && mval.(j) >= 0 && holds i mval.(j) then (
                  ink.(j) <- true;
                  stack := j :: !stack)
              done
            done;
            (* A free value anywhere in the set means it is not tight: the set can
               absorb one more value than it has members. *)
            let free_reachable =
              List.exists
                (fun i ->
                  ink.(i)
                  && List.exists
                       (fun vi -> mvar.(vi) = -1 && holds i vi)
                       (range 0 (nv - 1)))
                (range 0 (n - 1))
            in
            if not free_reachable then
              let vals =
                List.sort_uniq compare
                  (List.filter_map
                     (fun i -> if ink.(i) then Some values.(mval.(i)) else None)
                     (range 0 (n - 1)))
              in
              let halls = snaps_of (fun i -> ink.(i)) in
              List.iter
                (fun y ->
                  if not ink.(y) then
                    List.iter
                      (fun v ->
                        if Domain.mem doms.(y) v then
                          remove_one t store ~halls ~vals ~y_tm:t.terms.(y) v)
                      vals)
                (range 0 (n - 1)))
          (range 0 (n - 1)))

(* Stage 1, unchanged: Hall intervals over bounds. Returns whether it moved anything, so
   [propagate] can decide whether to go on to stage 2. *)
let rec stage_bounds t store ~moved =
  if try pass t store with Moved -> true then stage_bounds t store ~moved:true
  else moved

let rec stage_regin t store =
  if
    try
      regin_pass t store;
      false
    with Moved -> true
  then stage_regin t store

(* THE STAGING, and it is a measurement of GCS's rather than a choice of ours
   (docs/GCS-COMPARISON.md section 3, docs/ROADMAP.md M4-T2): above 256 var-value pairs
   the cheap pass returns WITHOUT an idempotence claim, so the propagators that are
   cheaper than a matching get to react to what it inferred before the matching work is
   paid for; at or below the cutoff both stages run in one call, because the staging
   itself costs a wake-up that a small instance does not earn back.

   "Without an idempotence claim" is about this CALL and not about I-P3. The instance
   watches its own variables, so the prunings stage 1 just made re-enqueue it
   ([Engine.watchers_of_new_entries]), and at the engine's fixpoint -- which is the state
   I-P2 and the M2-T10 consistency oracle are both statements about -- stage 1 has
   nothing left to say and stage 2 has run. [Engine.check_fixpoint] is what would catch
   it if that were not so, and it re-runs this function directly.

   The cutoff is a field rather than a constant so that a test can drive both branches;
   it is NOT re-measured here, and no model in this suite comes within two orders of
   magnitude of it, so every shipped proof takes the both-stages-in-one-call branch. *)
let pair_count t store =
  Array.fold_left (fun acc tm -> acc + Domain.size (Store.get store tm.x)) 0 t.terms

let propagate t store =
  try
    let moved = stage_bounds t store ~moved:false in
    if (not moved) || pair_count t store <= t.cutoff then stage_regin t store;
    Propagator.Fixpoint
  with Found c -> Propagator.Conflict c
