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

   2. **A current bound appears as a literal in the derived row, not as a cited id.**
      [excl] derives ~x_ge_lo(x) \/ ~x_eq_v rather than ~x_eq_v, so the final row is the
      globally valid `~<bound facts> \/ <the pruning>` shape lib/core/prop/ne.ml's clause
      already has, and it is sound at any level with no citation of anything the search
      established. The alternative -- citing the trail entry that moved the bound, as
      [Linear] does -- does not fit: a cited [Linear] explanation derives a statement in
      the order encoding's ladder currency (D-0010, lib/core/ladder.ml's header), not the
      unit x_ge_c >= 1 this counting argument needs.

   3. **[Weaken] is used for its D-0009 meaning and twice over.** Once to drop the
      excluded values the pruning does not need ([Lit.eq y v] as the trivial axiom
      y_eq_v >= 0), and once as the degenerate at-most-one: where only ONE variable in
      scope can take a value, the "at most one of them does" line is literally the
      literal axiom ~x_eq_v >= 0, and writing it as a [Weaken] summand rather than
      special-casing it keeps the counting uniform.

   Nothing here needed a new [Explanation] constructor. [Combine] (with its divisor,
   which [pair_amo] and [amo] both need and neither could fake), [Weaken] and
   [Model_row] carried the whole derivation.

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
type snap = {
  s_var : Var.t;
  s_name : string;
  s_dlo : int;
  s_dhi : int;
  s_lo : int;
  s_hi : int;
}

type term = { x : Var.t; name : string; decl_lo : int; decl_hi : int }

type t = {
  terms : term array;
  enc : Encoding.t;
  (* (x, z, v) -> the id of the .opb row "x <> v \/ z <> v", both orders of the pair
     present so a lookup never has to know which way [add_all_different] listed it. *)
  rows : (string * string * int, int) Hashtbl.t;
}

let name = "all_different_int"
let consistency = Propagator.Bounds

(* [rows] is what [Encoding.add_all_different] returned, and the encoding is the live
   one: see the module header on I-X6. Reads each variable's domain, so it must be
   called before anything has narrowed it -- the same requirement, for the same D-0010
   reason, that [Linear.make] and [Ne.make] state. *)
let make store enc ~rows vars =
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
  { terms; enc; rows = tbl }

let vars t = Array.to_list (Array.map (fun tm -> tm.x) t.terms)

let snap_of store tm =
  let d = Store.get store tm.x in
  {
    s_var = tm.x;
    s_name = tm.name;
    s_dlo = tm.decl_lo;
    s_dhi = tm.decl_hi;
    s_lo = Domain.lo d;
    s_hi = Domain.hi d;
  }

(* ------------------------------------------------------------------ explanations *)

let range a b = List.init (Stdlib.max 0 (b - a + 1)) (fun i -> a + i)

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

(* The at-least-one line for a Hall variable, narrowed from its DECLARED range to the
   Hall interval:  sum_{v in [a,b] and decl(x)} x_eq_v >= 1, plus the bound literals
   [excl] carried in.

   [Encoding.at_least_one_id] is the declared-range line, itself derived from the
   channelling at [start_proof] (PROOF-FORMAT section 3: exactly-one is derived, never
   asserted). Adding one [excl] per declared value outside [a, b] cancels that value's
   term against a unit and leaves the degree at 1. Every such value is outside the
   variable's current window too, because a Hall variable's window is inside [a, b]. *)
let alo_window t s ~a ~b =
  let outside = List.filter (fun v -> v < a || v > b) (range s.s_dlo s.s_dhi) in
  Explanation.combine
    (cite (cid_of "at-least-one" (Encoding.at_least_one_id t.enc s.s_name))
    :: List.map (fun v -> Explanation.term 1 (excl t s v)) outside)
    1

(* The counting argument itself: one at-least-one per Hall variable, one at-most-one per
   Hall value over whichever variables could take it. [extra] is the variable being
   pruned, which joins the at-most-one lines but contributes no at-least-one -- that
   asymmetry is exactly why the sum leaves ITS terms behind and cancels everything else.

   A value only one variable in scope can take gets a literal axiom instead of an
   at-most-one line: "at most one of {x} takes v" IS ~x_eq_v >= 0, and a value no
   variable can take gets nothing, because there is no term to cancel. *)
let core_summands t ~a ~b ~halls ~extra =
  let all = halls @ Option.to_list extra in
  List.map (fun s -> Explanation.term 1 (alo_window t s ~a ~b)) halls
  @ List.concat_map
      (fun v ->
        match List.filter (fun s -> s.s_dlo <= v && v <= s.s_dhi) all with
        | [] -> []
        | [ s ] -> [ Explanation.weaken [ (1, Lit.negate (Lit.eq s.s_name v)) ] ]
        | ss -> [ Explanation.term 1 (amo t ss v) ])
      (range a b)

(* The bound literals [alo_window] leaves in the row, cancelled by the lines that
   already state those bounds -- and the one place in this module where the reified
   explanation ADT does not reach, so read this before changing it.

   [alo_window] narrows a Hall variable's at-least-one line with one [excl] per declared
   value outside the interval, and each [excl] carries the bound it rests on into the sum
   as a literal: [a - decl_lo] copies of ~x_ge_lo(x), and [decl_hi - b] of x_ge_(hi(x)+1).
   For a PRUNING that is exactly right -- the derived row is then the globally valid
   "the pruning, disjoined with the bounds it read", which is the shape [Ne] already has.
   For a CONFLICT it is not enough: lib/core/search.ml cites a root conflict's derivation
   to `conclusion UNSAT`, and a row with literals left in it is not contradicting, which
   3.0.2 says in as many words ("The constraint with ID n is not contradicting, as
   specified by the hint") and which M1-T17 already found from the other end.

   Cancelling them needs the ONE THING [Explanation.t] cannot say: "the id of the line
   that establishes this bound fact". That is D-0009's open ADT gap verbatim, and
   [Justify.defining_lit] is the lookup built for it that still has no caller --
   [Model_row] can name an id but nothing in the value can ASK for one. So the cancellation
   goes through [Explanation.clause], whose [Justify.emit_clause] consults the M2-T9 claim
   index and hands back the trace line that already states the bound, minting nothing.
   Two consequences, and both are findings rather than details:

   - it is sound only at LEVEL 0, where a bound fact is a consequence of the model rather
     than of a decision, so [moved] is empty under a decision and the pure form is what is
     emitted there. That is not a loss: only a root conflict's derivation is cited as a
     contradiction, and under a decision D-0018's nogood is what closes the branch.
   - a conflict that needs it does rest on a clause, so [Search.rests_on_a_clause] routes
     it the D-0022 way and this module's [pol] is decorative FOR THAT CONFLICT (D-0057).
     It is not decorative for a conflict that needs no cancellation -- every Hall variable
     still at its declared bounds -- and test/models/alldiff_hall_unsat.fzn is that case,
     with `conclusion UNSAT` citing the Hall [pol] itself. *)
let states lit = Explanation.clause [ lit ]

(* The Hall variables' share: one copy of ~x_ge_lo(x) per declared value below the
   interval and one of x_ge_(hi(x)+1) per declared value above it, which is exactly how
   many [excl] summands [alo_window] added in each direction. *)
let moved_bound_cancels ~a ~b ~halls ~level =
  if level > 0 then []
  else
    List.concat_map
      (fun s ->
        let below = Stdlib.max 0 (a - s.s_dlo) and above = Stdlib.max 0 (s.s_dhi - b) in
        (if below > 0 then [ Explanation.term below (states (Lit.ge s.s_name s.s_lo)) ]
         else [])
        @
        if above > 0 then [ Explanation.term above (states (Lit.le s.s_name s.s_hi)) ]
        else [])
      halls

(* The pruned variable's own share, and it is ONE copy in ONE direction: the telescoping
   channelling sum leaves ~y_ge_lo(y) on a lower push and y_ge_(hi(y)+1) on an upper one,
   and nothing else of y's survives. [y] has no [alo_window] -- that asymmetry is the
   whole reason its terms are what the derivation is left holding -- so it must not be
   handed to [moved_bound_cancels], which counts a Hall variable's [excl] summands. *)
let target_cancel ~y ~lower ~level =
  if level > 0 then []
  else if lower then
    if y.s_lo > y.s_dlo then [ Explanation.term 1 (states (Lit.ge y.s_name y.s_lo)) ]
    else []
  else if y.s_hi < y.s_dhi then [ Explanation.term 1 (states (Lit.le y.s_name y.s_hi)) ]
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
  core_summands t ~a ~b ~halls ~extra:(Some y)
  @ List.map (fun v -> Explanation.weaken [ (1, Lit.eq y.s_name v) ]) drop
  @ List.map
      (fun v -> cite (cid_of "d_fwd" (Encoding.direct_fwd_id t.enc y.s_name v)))
      keep

let prune_expl t ~a ~b ~halls ~y ~lower ~level =
  Explanation.deferred (fun () ->
      Explanation.combine
        (prune_summands t ~a ~b ~halls ~y ~lower
        @ moved_bound_cancels ~a ~b ~halls ~level
        @ target_cancel ~y ~lower ~level)
        1)

(* ---------------------------------------------------------------------- reasons *)

(* A Hall variable is in the set because BOTH its bounds are where they are, so both are
   facts. [Reason.lit_of_fact] drops the ones sitting at a declared bound, which is the
   same test [excl] makes when it decides whether a value is outside the window -- the
   two cannot disagree because both read the same snapshot. *)
let hall_facts halls =
  List.concat_map
    (fun s ->
      [
        Reason.at_least ~name:s.s_name ~decl:s.s_dlo s.s_lo;
        Reason.at_most ~name:s.s_name ~decl:s.s_dhi s.s_hi;
      ])
    halls

let prune_reason halls y ~lower =
  (if lower then Reason.at_least ~name:y.s_name ~decl:y.s_dlo y.s_lo
   else Reason.at_most ~name:y.s_name ~decl:y.s_dhi y.s_hi)
  :: hall_facts halls

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
  let level = Store.level store in
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
        (prune_reason halls y ~lower)
        (prune_expl t ~a ~b ~halls ~y ~lower ~level)
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
let rec stage_bounds t store =
  if try pass t store with Moved -> true then stage_bounds t store

let propagate t store =
  try
    stage_bounds t store;
    Propagator.Fixpoint
  with Found c -> Propagator.Conflict c
