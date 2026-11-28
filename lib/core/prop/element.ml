(* array_int_element(idx, as, c): the 1-based index [idx] selects [as[idx]], which is
   [c]. [as] is an array of CONSTANTS (docs/SPEC.md 2.1's M4 row; a var-array element is
   not in the subset).

   Consistency level: DOMAIN (docs/SPEC.md 3.2, docs/GLOSSARY.md). It is not a claim
   made on the shape of the algorithm: for a constant array the two filtering rules
   below are the whole support condition, so the fixpoint IS the domain-consistent one,
   and the brute-force consistency oracle (BAGUETTE_CONSISTENCY=1, M2-T10) holds this
   module to it. (This was the first propagator to declare DOMAIN. D-0059, which made
   the tag checked, had predicted that the [Bounds]/[Domain] distinction would start
   doing separating work at an `all_different` or an `element`.)

   Proof shape (docs/SPEC.md 3.3): every pruning is one [Combine], a `pol` over the
   constraint's .opb rows, the index's channelling and the result's ladder rungs (see
   "The derivations" below). The trace line of a pruning is RUP once earlier lines are
   on the page, so nothing is written ahead of it; a conflict under a decision writes its
   derivation ahead of its line.

     dom(idx) := { p in dom(idx) : as[p] in dom(c) }
     dom(c)   := { as[p]        : p in dom(idx)    }

   Each value of [idx] has exactly one support in [c] and each value of [c] is supported
   by whichever positions carry it, so neither rule can leave an unsupported value
   behind and no third rule is missing. That is why [element] over constants is the
   cheap global: the matching a general element needs is a lookup here.

   ---------------------------------------------------------------------------
   The index is a VIEW onto the FlatZinc variable, not an auxiliary (D-0058)
   ---------------------------------------------------------------------------

   [pos] is [View.shift (View.of_var idx) (-1)]: the 0-based array offset, as a lens
   onto the 1-based FlatZinc variable. It is NOT an auxiliary variable with a
   channelling constraint. D-0058 decided that a view is a rendering onto its base's
   literals, with no literals of its own, and that distinction is the point of this
   module rather than a detail of it. An auxiliary [p = idx - 1] has a domain
   of its own, so every value this propagator excludes from [p] would have to travel
   back to [idx] through the channel -- a bounds-consistent step -- and the [Domain]
   claim above would be quietly false for [idx] itself. With a view there is no step at
   which to lose it: [View.remove] IS [Store.remove] on [idx] at the translated value,
   pushing one ordinary trail entry against [idx].

   The one constraint D-0058 leaves: a view's [=] is the BASE's [=]. So every literal and
   every id on the proof side is [idx]'s, at the base value [Lit.unapply imap p], and
   lib/flatzinc/compile.ml calls [Encoding.request_direct] on [idx] itself and never on
   the view. That is also why the rows below are spelled with [Encoding.ne_clause] on the
   base rather than with [Encoding.view_eq]: a view's [=] would resolve to the base's
   anyway, and the .opb has no direct literals to name in the first place (see the rows
   section).

   [res] is a view too, which is how a constant [c] is handled with no special case
   ([View.Const]): the rows below collapse to units through [Encoding.view_ge]'s
   [Holds]/[Fails], and a push against a constant reports the same [Store.outcome] a
   variable would. The index is always an [Affine] view -- compile.ml decomposes a
   constant index to an ordinary [int_eq] rather than admitting a second degenerate
   case here.

   ---------------------------------------------------------------------------
   The .opb rows, and why they are clauses over the ORDER encoding
   ---------------------------------------------------------------------------

   Per position [p] in [idx]'s declared domain, writing w = as[p]:

     r_ge(p)   ~idx_eq_p  \/  c >= w
     r_le(p)   ~idx_eq_p  \/  c <= w
     r_out(p)  ~idx_eq_p                        for p outside the array

   Two rows and not one because "c = w" is not a row: the .opb holds no equalities
   ([Encoding.add_constraint] refuses [Opb.Eq]), and the pair is exactly the split
   [Encoding.add_equality] already makes for the same reason. Each is spelled with
   [Encoding.view_ge]/[view_le], so a bound that the declared domain already forces
   drops out and the row degenerates to the unit [idx <> p] -- which is the right row
   for "position p asks c for a value c cannot hold", and it is the reason a model whose
   array leaves the result's declared range refutes by arithmetic rather than by luck.

   [~idx_eq_p] IS NOT WHAT THE ROWS SAY, and the difference is not cosmetic. The direct
   encoding does not exist in the .opb at all: [Encoding.start_proof] introduces it into
   the PROOF with [red], with its channelling, long after these rows are written, so a
   row naming [idx_eq_p] would name a variable the model file never defines and the .opb
   would stop deciding its own solutions. So the guard above is spelled
   [Encoding.ne_clause] -- "idx <> p" over the ORDER encoding, the same two-literal form
   lib/core/prop/ne.ml uses and the same one [Encoding.add_all_different] posts. The
   [~idx_eq_p] form every derivation below is written in is then RECOVERED by [pol], in
   [implies_ge]/[implies_le]/[implies_out]: adding the two channelling halves cancels
   both order literals and one division gives the unit. That is alldiff.ml's [pair_amo]
   trick, for the same reason (the next paragraph but one).

   ONLY THE INDEX NEEDS THE DIRECT ENCODING, and only the index gets one. The result is
   spoken about in order literals throughout: [c >= w], [c <= w], and for a hole the
   two-literal clause [~c_ge_v \/ c_ge_(v+1)] that lib/core/prop/ne.ml already derives.
   That halves the direct-encoding width this constraint costs (a justification's size
   is proportional to declared width, D-0028),
   and it is what lets the result's own ladder rungs ([Encoding.consistency_id]) do the
   telescoping every derivation below leans on.

   NO [Explanation.Clause] ON THE MAIN PATHS. The clause rows above are recovered by
   [pol], never by [rup], for the reason lib/core/prop/alldiff.ml's header gives (its
   item 1, D-0061): when this was written, search.ml routed a root conflict whose
   derivation rested on a clause to the empty clause instead (D-0022), so `conclusion
   UNSAT` did not depend on the [pol] arithmetic and every [pol] here would have been
   decorative (D-0057 and D-0060 found that by accident). That routing is gone since
   D-0131 (every root conflict closes on its trace), and the rule stands. The two places
   a clause does appear are named where they are used and are both about a hole SOMEONE
   ELSE punched.

   ---------------------------------------------------------------------------
   The derivations
   ---------------------------------------------------------------------------

   Every one is a [Combine] over model rows and ladder rungs. The two shapes:

   1. EXCLUDING A POSITION. w = as[p] is outside the result's current window, so p is
      impossible. Adding r_ge(p) to the rungs hi(c)+1 .. w-1, which telescope to
      [~c_ge_w \/ c_ge_(hi+1)], cancels c_ge_w and leaves

        ~idx_eq_p  \/  c_ge_(hi(c)+1)

      -- the pruning disjoined with the bound it read, globally valid at any level,
      which is the shape lib/core/prop/ne.ml's clause already has. Below the window is
      the mirror image through r_le(p). For w a HOLE in the result, r_ge(p) and r_le(p)
      together with the line that punched the hole pair off both of c's literals and
      leave [2 ~idx_eq_p >= 1], one division by 2 from the unit.

   2. PRUNING THE RESULT. Start from [Encoding.at_least_one_id] -- "idx takes one of its
      declared values", derived from the channelling at [start_proof], never asserted
      (PROOF-FORMAT section 3) -- and narrow it to the LIVE positions by adding one
      shape-1 line per dead position, each cancelling its own term. That gives

        sum_{p live} idx_eq_p  \/  <the bound literals the exclusions carried>  >=  1

      Then one line per live position, saying what that position forces about c, all
      concluding the SAME literal after their own rungs telescope. Every idx_eq_p pairs
      off against its negation, L of them for L live positions, and dividing by L leaves
      the single literal: a bound push, or -- padding the two sides up to a common
      coefficient with literal axioms (D-0009, the same [Weaken] use alldiff's [pair_amo]
      makes) -- the two-literal [c <> v] of an interior hole.

   A conflict is the L = 0 case and needs no separate argument: with every declared
   position excluded, the at-least-one line has nothing left and the sum IS [0 >= 1].
   That is why [propagate] checks for the emptying removal BEFORE making it rather than
   letting [Store.apply]'s [Failed] arm report it -- that arm would hand back the
   derivation of the ONE position it was removing, which is not contradicting.

   WHAT A CONFLICT READ, and why it says so (D-0101, built by M7-T25). An empty-index
   conflict is reached with exactly one position p still in dom(idx), and as[p] is not in
   dom(c). Its FACTS are, per declared position q, the facts behind whichever
   [pos_gone] arm excludes q: the result bound as[q] lies beyond ([c <= hi] or
   [c >= lo]); the index bound q lies beyond; for a hole in c at as[q], the REMOVER's
   facts (a hole is cited through its remover, never as a bound fact: D-0075 found the
   defect of reading a hole and stating only bounds, D-0084 its embedded form);
   for an interior index hole punched under a decision, its puncher's facts. Under a
   decision the derivation above then leaves exactly the negations of those facts --
   "not all of these bounds hold" -- so `rup ~facts >= 1` is unit propagation against it.
   [conflict_facts] collects them and [no_position_conflict] reports them under
   [Store.deriving_ahead], so the derivation is on the page before the line
   ([Store.conflict]'s [c_ahead], introduced for cumulative by D-0096). That is what
   lets 1UIP learning resolve from an element conflict; until M7-T25 the reason was
   [Reason.none] at every depth (D-0091) and nothing was learned.
   The line is ALSO RUP in sequence without the derivation, by the [Single_row] argument
   below: the one live position's rows plus the index ladder and the earlier trace lines
   of every index removal (measured, D-0101) -- the [pol] ahead is what makes that not a
   thing the line has to rely on. At the ROOT the reason stays [Reason.none]: there is no
   branch to learn from and the derivation itself closes to [0 >= 1].

   ---------------------------------------------------------------------------
   Trace lines: a [Single_row] family, on the [Ne] precedent
   ---------------------------------------------------------------------------

   I-X10 requires every trace line to be RUP against the .opb plus the lines before it.
   It holds by an enumeration over the propagator set, kept as a classification table in
   test/unit/test_trace.ml: a [Single_row] family's pruning follows from ONE model
   constraint, a [Needs_derivation] family's needs a derivation written ahead. The
   question I-X10 asks of a new member is whether its trace line is RUP once the facts on
   the line's own tail are assumed. It is, and the reason is the one [Ne] already relies
   on: "one model constraint" is a rule about the CONSTRAINT and not about the row count,
   and `array_int_element` is one constraint posted as 2n rows, the way `int_lin_ne` is
   one constraint posted as two big-M rows whose selector the checker's own unit
   propagation fills in.

     - an INDEX pruning: negate the claim, i.e. assume idx = p. The single row r_ge(p) or
       r_le(p) then forces a bound on the result that the result's own ladder refutes.
       One row and the ladder, and the ladder is the .opb's encoding of the variable
       itself rather than a second constraint (the distinction lib/core/prop/pb.ml's
       entry in test_trace.ml's table already draws).
     - a RESULT pruning: negate the claim and every position whose value disagrees is
       excluded by its own row; the index's ladder then has nothing left. Several rows,
       all of this constraint.

   MEASURED, not argued, for the second one: the result has no direct encoding at all,
   so [Trace.derive_ahead] did not fire for a result pruning even under the old
   trigger, and all seven element models
   plus a scene built to defeat it -- an index HOLE punched by an `int_ne`, so the result
   pruning rests on something [Reason.t] has no fact for -- verify with nothing written
   ahead of their lines. The hole case works because the hole's OWN trace line is already
   on the page: [Trace.emit] writes oldest first, and a trace line is RUP in sequence
   against the .opb plus earlier trace lines (D-0039; I-S4 for a hole's own line), the
   same support a settle line already leans on. It is
   not a second model constraint in I-X10's sense.

   AMENDED BY D-0075 (M7-T13), A HOLE READ UNDER A DECISION. "all seven element models
   plus a scene built to defeat it ... verify" was true of those scenes and false in
   general: the scene that defeats it needs the hole's own trace line to carry a TAIL (a
   hole punched under a decision, not at level 0) AND the pruning that reads the hole to
   fail deeper, so that a line is written for it at all. `2012_tpp` is that scene and
   test/models/element_index_hole_rup_sat.fzn is it reduced. The repair is on the REASON
   side ([index_hole_facts]/[result_hole_facts]), so the cost is that such a line is no
   longer a single-row consequence -- I-X10 gains a second member of the kind
   lib/core/trace.ml's header already names for a settle.

   The index side is measured the same way (D-0082, M7-T17). Before that,
   [derive_ahead] fired on [has_direct], which is true for the index because the
   derivations genuinely cite its direct ids, so a [pol] went ahead of every index line
   whether or not one was needed. The trigger is now [Store.entry]'s [ahead], which this
   module never sets, and every element model -- `element_index_hole_rup_sat`, SAT,
   among them -- verifies with nothing written ahead of an index line either. That is
   [Single_row] measured on both sides.

   AMENDED BY D-0084 (M7-T21), THREE TIMES, AND NONE OF THE THREE IS ABOUT A TRACE LINE.
   Each is about a DERIVATION that some other line embeds, which is how the 26 corpus
   rejections D-0080 found were invisible to every lane above: the trace lines were
   right.

     - A FOREIGN INDEX HOLE ([index_hole_clause]). The [pos_gone] arm for a position the
       index lost to someone else wrote the bare unit [~idx_eq_p]. That is RUP only for a
       level-0 hole. Under a decision it is the corpus's 23-of-26 shape
       `rup +1 ~<v>_eq_<k> >= 1 ;`, written when a second element's factless conflict
       forces this instance's [hole_expl] through [excl_hole]. It now carries the
       puncher's facts. test/models/element_foreign_hole_rup_sat.fzn.
     - ROOT RESIDUE ([alo_of]'s [cancel], [filter_index]). A pruning derivation kept
       every residue literal, so one embedded in another instance's ROOT conflict left
       literals nothing counted. Root-established residue is now cancelled where the
       derivation is built. test/models/element_shared_result_root_unsat.fzn.
     - CURRENCY ([in_order_currency]). An interior index removal concluded [~idx_eq_p],
       while [excl_hole] -- reached when this index is another instance's RESULT -- pairs
       off ORDER literals. It now concludes `~idx_ge_p \/ idx_ge_(p+1)`, like every other
       hole in the store. test/models/element_crossed_root_unsat.fzn.

   The case D-0084 left "not verified" is settled (M7-T22, D-0086): [excl_hole] trusts the
   remover's derivation to conclude the hole in the ORDER currency, and an element result
   that is also in an all_different scope can have its hole punched by Regin, whose
   removal used to conclude over the DIRECT encoding. alldiff.ml now converts an interior
   Regin removal to the order clause itself ([in_order_currency], the forward channelling
   row with divisor 1), so there is one convention for every hole in the store and nothing
   here bridges. test/models/alldiff_regin_hole_element_unsat.fzn is the lane.

   ---------------------------------------------------------------------------
   Snapshotting: a derivation reads the pruning's moment, never the live store (I-X6)
   ---------------------------------------------------------------------------

   Every derivation below is built from the domains as they stood at the moment of the
   pruning. Nothing inside a thunk reads a live domain. What the thunks do read is
   [Encoding]'s constraint ids, which [start_proof] writes once before the first decision
   and never moves -- the same exemption alldiff.ml's header argues.

   REASONS ON DEMAND (D-0214, built by M20-pernode-T2). A pruning reads nothing it does
   not need to DECIDE (which value goes, what the push concludes): it records a [frame]
   -- the index's and the result's domains (versions that read as they were while the
   pruning's entry is on the trail, D-0222), and the trail cut at the push
   ([Store.history], D-0124) -- and both halves of the pruning are built from that
   frame when they are first asked for. The reason is a [Reason.Later] (D-0124's
   channel for a reason materialised later from the trail's history, the one [Linear]
   uses); the derivation's [pos_gone] walk, the removers it looks up and the residue it
   cancels move inside the [Explanation.deferred] that already wrapped it. Every lookup
   that used to be "hoisted to its call site" for I-X6 ([Store.remover],
   [Store.lo_support], the level of an entry) is now answered by the history, which can
   only answer for positions below the pruning, so I-X6 holds by what the readers can
   see rather than by when they run. The frame section below argues why the values are
   the ones the eager code read; the proof bytes are the same on every test model
   (D-0214 section 2).

   ONE STORE CHANGE FOR A RESULT'S GAP (D-0268, M18-coverage-T9). The interior half of
   rule 2 removes every unsupported interior value of the result in ONE store change,
   [View.remove_interior] (store.ml's bulk rule), where it made one change per value. The
   values share a reason already (a pass reads the index's bounds and holes once,
   D-0155) and keep one derivation each, [hole_expl], built when asked and memoised per
   value. Each per-value derivation reads the frame taken before the change plus a
   [pending] record saying which of the change's values come before it, so it reads
   exactly what a per-value removal's own frame read: the values of the same pass below
   it as holes, each with its own derivation (see [frame]). The trace writes one line
   per value in ascending order with the shared facts, as before, so the proof is the
   same bytes (D-0268 measures it); what goes is one trail entry, one frame, one
   [Later] reason and one closure per value: 15.4 million entries of 657 bytes at the
   root of liner-sf fm3_11 (D-0265). A result that IS the index (one variable on both
   sides) keeps one change per value, since a removal there moves the index the next
   value's frame reads.

   COST (the file-by-file review of the propagators, M16-file-review-T2, D-0190; and
   D-0214). A pass is O(n_decl + w_res). A pruning costs two domain reads and one
   history record; the O(n_decl) walk of the dead positions, and the hole facts, are
   paid only when a reason or a derivation is asked for (the trace, conflict analysis,
   or BAGUETTE_DEBUG's agreement check at the push). Without learning or proof nothing
   asks, and building them eagerly was 28 % of a javarouting node (D-0207, the per-node
   cost breakdown). *)

module Lit = Baguette_proof.Lit
module Encoding = Baguette_proof.Encoding
module Opb = Baguette_proof.Opb

(* The ids of this instance's own rows, by position. A position absent from [r_ge] has
   no such row because the row is VACUOUS -- [c >= as[p]] is forced by the result's
   declared domain, so the clause is the constant true. That is not a gap: the same
   condition makes the derivation that would have cited it unreachable, and [row_ge]
   below says so rather than handing back a wrong id. *)
type rows = {
  r_ge : (int, int) Hashtbl.t;
  r_le : (int, int) Hashtbl.t;
  r_out : (int, int) Hashtbl.t;
}

type t = {
  pos : View.t; (* the 0-based array offset, as a view onto the index variable *)
  res : View.t;
  values : int array;
  enc : Encoding.t;
  rows : rows;
  ibase : Var.t;
  iname : string;
  imap : Lit.affine; (* base value = Lit.unapply imap position *)
  idlo : int;
  idhi : int; (* the INDEX BASE's declared bounds *)
  decl_pos : int list; (* every position the index may declare, ascending *)
  rname : string option; (* [None] for a constant result *)
  rdlo : int;
  rdhi : int;
}

let name = "array_int_element"
let consistency = Propagator.Domain
let vars t = View.vars t.pos @ View.vars t.res

(* ------------------------------------------------------------------- the .opb rows *)

(* Posted by lib/flatzinc/compile.ml before the .opb is written, over the views it is
   about to hand [make]. It lives here rather than in lib/proof/encoding.ml (where
   [add_all_different] is) so that the rows and the derivations that cite them are read
   together; [Encoding.add_constraint] is the committing door either way. *)
let post_rows enc ~(index_name : string) ~(imap : Lit.affine) ~(result : Encoding.view)
    ~(values : int array) ~(positions : int list) : rows =
  let rows =
    { r_ge = Hashtbl.create 16; r_le = Hashtbl.create 16; r_out = Hashtbl.create 4 }
  in
  let n = Array.length values in
  let post tbl p guard cond =
    match cond with
    | Encoding.Holds -> () (* the clause is the constant true: no row, and none needed *)
    | Encoding.Fails ->
        Hashtbl.replace tbl p (Encoding.add_constraint enc (Opb.clause guard))
    | Encoding.Cond l ->
        Hashtbl.replace tbl p (Encoding.add_constraint enc (Opb.clause (guard @ [ l ])))
  in
  List.iter
    (fun p ->
      let bp = Lit.unapply imap p in
      let lo, hi = Encoding.domain enc index_name in
      if bp >= lo && bp <= hi then
        (* "idx <> p", over the order encoding. Empty exactly when the index is declared
           fixed at [p], where it is the constant FALSE and the row degenerates to its
           result half -- which is right: the index IS p, so p's demand on c is
           unconditional. *)
        let guard = Encoding.ne_clause enc index_name bp in
        if p < 0 || p >= n then
          Hashtbl.replace rows.r_out p (Encoding.add_constraint enc (Opb.clause guard))
        else (
          post rows.r_ge p guard (Encoding.view_ge enc result values.(p));
          post rows.r_le p guard (Encoding.view_le enc result values.(p))))
    positions;
  rows

(* ------------------------------------------------------------------ construction *)

(* Reads both views' domains, so it must be called before anything has narrowed them --
   the requirement [Linear.make] and [Alldiff.make] state, and for the same reason: a
   derivation speaks in the DECLARED ladder's currency (D-0010, a bound fact is a chain
   of order literals counted from the declared bound). *)
let make store enc ~rows ~(pos : View.t) ~(res : View.t) ~(values : int array) =
  let ibase =
    match View.base_var pos with
    | Some v -> v
    | None ->
        invalid_arg
          "Element.make: the index must be a view onto a variable -- a constant index is \
           decomposed to int_eq by lib/flatzinc/compile.ml"
  in
  let imap = match View.map_of pos with Some m -> m | None -> assert false in
  let d = Store.get store ibase in
  let idlo = Domain.lo d and idhi = Domain.hi d in
  let ends = [ Lit.apply imap idlo; Lit.apply imap idhi ] in
  let plo = List.fold_left Int.min (List.hd ends) ends in
  let phi = List.fold_left Int.max (List.hd ends) ends in
  let rd = View.domain store res in
  {
    pos;
    res;
    values;
    enc;
    rows;
    ibase;
    iname = Store.name store ibase;
    imap;
    idlo;
    idhi;
    decl_pos = List.init (phi - plo + 1) (fun i -> plo + i);
    rname = Option.map (Store.name store) (View.base_var res);
    rdlo = Domain.lo rd;
    rdhi = Domain.hi rd;
  }

(* The declared positions, which is what [post_rows] must be given so that every row a
   derivation may cite exists. Exposed because compile.ml posts the rows before [make]
   has anything to read them off. *)
let declared_positions store ~(pos : View.t) =
  match (View.base_var pos, View.map_of pos) with
  | Some v, Some m ->
      let d = Store.get store v in
      let a = Lit.apply m (Domain.lo d) and b = Lit.apply m (Domain.hi d) in
      let lo = Int.min a b and hi = Int.max a b in
      List.init (hi - lo + 1) (fun i -> lo + i)
  | _ ->
      invalid_arg "Element.declared_positions: the index must be a view onto a variable"

(* ------------------------------------------------------------------- explanations *)

let range a b = List.init (Int.max 0 (b - a + 1)) (fun i -> a + i)
let cite id = Explanation.term 1 (Explanation.model_row id)

let need what = function
  | Some id -> id
  | None ->
      invalid_arg
        (Printf.sprintf
           "Element: %s has no constraint id. Every id this module names is posted by \
            Element.post_rows or materialised by Encoding.start_proof from the \
            Encoding.request_direct calls lib/flatzinc/compile.ml makes for an \
            array_int_element's index and result; a forced explanation without one means \
            the two have drifted apart."
           what)

let row_ge t p = need "r_ge" (Hashtbl.find_opt t.rows.r_ge p)
let row_le t p = need "r_le" (Hashtbl.find_opt t.rows.r_le p)
let row_out t p = need "r_out" (Hashtbl.find_opt t.rows.r_out p)

(* [~x_ge_(u+1) \/ x_ge_u], the ladder rung every telescoping sum below is built from.
   It exists for every [u] strictly inside the declared range, which is exactly the
   range each caller asks over. *)
let res_rung t u =
  match t.rname with
  | None ->
      invalid_arg
        "Element: a constant result has no ladder -- no rung should be asked for"
  | Some x -> need "result ladder rung" (Encoding.consistency_id t.enc x u)

let idx_rung t u = need "index ladder rung" (Encoding.consistency_id t.enc t.iname u)
let base_of t p = Lit.unapply t.imap p

(* ---- recovering the direct form of a row (the [pair_amo] trick) ---- *)

(* The channelling halves of [idx = p] that EXIST. [direct_lo_id] is [None] at the
   declared lower bound and [direct_hi_id] at the declared upper one, where the
   implication is the constant true -- and [Encoding.ne_clause] drops exactly the same
   order literal at exactly the same bound, which is what keeps the sum below balanced
   without either side having to know about the other. *)
let idx_halves t p =
  let bp = base_of t p in
  List.filter_map Fun.id
    [ Encoding.direct_lo_id t.enc t.iname bp; Encoding.direct_hi_id t.enc t.iname bp ]

(* A row of this instance's, restated over the DIRECT literal of the index.

   The row says [idx <> p \/ R] with [idx <> p] spelled as up to two order literals;
   each channelling half [~idx_eq_p \/ <the negation of one of them>] cancels one of
   them and contributes one [~idx_eq_p]. With [h] halves present the sum is
   [R + h ~idx_eq_p >= 1], and dividing by [h] leaves [R \/ ~idx_eq_p] -- the form every
   derivation below is written in. [h = 0] is the declared-fixed index, where the row
   already IS [R] and the divisor is 1. *)
let restate t row p =
  let halves = idx_halves t p in
  let h = List.length halves in
  Explanation.combine (cite row :: List.map (fun id -> cite id) halves) (Int.max 1 h)

let implies_ge t p = restate t (row_ge t p) p
let implies_le t p = restate t (row_le t p) p
let implies_out t p = restate t (row_out t p) p

(* ---- shape 1: why a position is impossible ---- *)

(* [~idx_eq_p \/ c_ge_(hi+1)], for as[p] above the result's current window. *)
let excl_above t p ~bhi:hi =
  let w = t.values.(p) in
  Explanation.combine
    (Explanation.term 1 (implies_ge t p)
    ::
    (* Above the result's DECLARED range there is no [c >= w] literal to cancel and no
       ladder to walk down: [Encoding.view_ge] answered [Fails], so r_ge(p) is already
       the unit row and [implies_ge] already derives [~idx_eq_p] outright. Asking for a
       rung outside the declared range is how this read before it was measured, and
       [res_rung] refuses rather than inventing one. *)
    (if w > t.rdhi then []
     else List.map (fun u -> cite (res_rung t u)) (range (hi + 1) (w - 1))))
    1

(* [~idx_eq_p \/ ~c_ge_lo], for as[p] below it. *)
let excl_below t p ~blo:lo =
  let w = t.values.(p) in
  Explanation.combine
    (Explanation.term 1 (implies_le t p)
    ::
    (if w < t.rdlo then []
     else List.map (fun u -> cite (res_rung t u)) (range (w + 1) (lo - 1))))
    1

(* [~idx_eq_p], for as[p] a HOLE in the result: r_ge(p) and r_le(p) pair off against the
   hole's own two-literal line, leaving [2 ~idx_eq_p >= 1]. *)
let excl_hole t p ~hole =
  Explanation.combine
    [
      Explanation.term 1 (implies_ge t p);
      Explanation.term 1 (implies_le t p);
      Explanation.term 1 hole;
    ]
    2

let excl_out t p = implies_out t p

(* [~idx_eq_p \/ <the index bound that excluded p>], for a position outside the INDEX's
   own current window -- the same telescoping alldiff.ml's [excl] does, in the index's
   base-value space. *)
let idx_excl_below t p ~blo =
  let bp = base_of t p in
  Explanation.combine
    (cite (need "index d_hi" (Encoding.direct_hi_id t.enc t.iname bp))
    :: List.map (fun u -> cite (idx_rung t u)) (range (bp + 1) (blo - 1)))
    1

let idx_excl_above t p ~bhi =
  let bp = base_of t p in
  Explanation.combine
    (cite (need "index d_lo" (Encoding.direct_lo_id t.enc t.iname bp))
    :: List.map (fun u -> cite (idx_rung t u)) (range (bhi + 1) (bp - 1)))
    1

(* ---------------------------------------------------------------- the frame (D-0214)

   WHAT A PRUNING RECORDS, so that its reason and its derivation can be built when they
   are asked for rather than at the pruning. Most prunings are never asked: building
   them eagerly was 57 % of this module's samples on javarouting, about 28 % of a node
   without learning or proof (D-0207 section 5 item 3; the frame is M20-pernode-T2's).

   Everything the eager code read at a pruning was one of four things, and a [frame] holds
   each of them as of that moment:

     - the index's and the result's DOMAINS ([di], [dr]): VERSIONS (D-0222, a
       [Domain.t]'s holes are a prefix of a log that only grows while the pruning's
       entry is on the trail, lib/core/domain.ml), so holding the pointer IS holding the
       domain then. [dr] is the result BASE's domain, read through [View.lo_in] and its
       twins; for a constant result it is never read;
     - which trail entry REMOVED a value ([remover_at]), its ARENA explanation
       ([removal_explanation_at], the entry's derivation of that value: its arena
       explanation, or one value's of a bulk entry, D-0268) and whether a trail position
       is at the ROOT ([at_root_at]);
     - which entry SUPPORTS a bound ([Store.lo_support_at]/[hi_support_at]).

   The last three are answered from [h], the trail cut at the pruning ([Store.history],
   D-0124). While the pruning's entry is on the trail every position below it holds the
   record it held at the push (I-T1: a backtrack restores exactly, and nothing below a
   live entry is rewritten), so each of them answers exactly what the live store
   answered then: [Store.remover] with [~before] at the cut finds the same entry (the first
   entry on the variable whose [now] lost the value, kept iff it lies below the cut), a
   level mark below the cut is the same mark, and [support_before] walks back past the
   cut. So a reason or a derivation rebuilt from the frame is the one the eager code built,
   value for value; the bytes do not move (D-0214 section 2).

   The three readers ([Store.remover_at], [Store.removal_explanation_at], [Store.at_root_at])
   live in store.ml's history section (moved there by M21-memory-T3, D-0222, as D-0214
   had asked); each is one call on a position below the cut, and none can read past it. *)
type frame = { h : Store.history; di : Domain.t; dr : Domain.t; pend : pending option }

(* THE VALUES OF ONE BULK REMOVAL THAT COME BEFORE [p_upto] (D-0268). The interior rule
   removes its result's unsupported values as ONE store change ([Store.remove_interior])
   where it used to make one per value, ascending. Each per-value derivation used to read
   a frame taken just before its own removal, so it saw the values of the same pass
   below it as holes already, each with its own remover; a dead position carrying such
   a value is then excluded by [excl_hole] citing that value's derivation, where a value
   above it is still in the result. A per-value derivation of the bulk reads the frame
   taken before the bulk, plus this record: [w] counts as a hole iff [p_in w] (it is one
   of the bulk's values) and [w < p_upto] (it came before), and its remover's derivation
   is [p_expl w], the bulk's own, memoised. So [res_mem] and [hole_line] below answer
   exactly what the per-value frame answered, and the derivation is the same tree, value
   for value. Values are the VIEW's, as [res_mem]'s argument is. *)
and pending = { p_upto : int; p_in : int -> bool; p_expl : int -> Explanation.t }

let frame t store =
  let di = Store.get store t.ibase in
  {
    h = Store.history store;
    di;
    dr = (match View.base_var t.res with Some rv -> Store.get store rv | None -> di);
    pend = None;
  }

let pending_gone fr w =
  match fr.pend with Some p -> w < p.p_upto && p.p_in w | None -> false

let remover_at = Store.remover_at
let removal_explanation_at = Store.removal_explanation_at
let at_root_at = Store.at_root_at
let res_lo t fr = View.lo_in fr.dr t.res
let res_hi t fr = View.hi_in fr.dr t.res
let res_mem t fr w = View.mem_in fr.dr t.res w && not (pending_gone fr w)

(* The trail entry that punched [bp] out of the index, or [None]. [Store.remover]
   answers from the variable's own entry history by binary search (D-0088), and it is
   the entry a backward walk of the whole trail would find: the
   walk's predicate (on [ibase], [bp] in [old], not in [now]) is [Store.remover_scan]'s,
   started at the same position, and [Store.remover] agrees with that scan under
   [BAGUETTE_DEBUG] by physical equality. Read from the frame's history (I-X6, D-0214).
   (That walk was the code until D-0155, M11-complexity-T8: [index_hole_clause] and
   [conflict_facts] each repeated it over every dead position, O(positions x trail) per
   pruning.) *)
let index_hole_puncher t fr bp = remover_at fr.h ~var:t.ibase bp

(* The line that took [w] out of the result, or [None] when nothing did.

   Read from the frame's HISTORY, never from the live store: which trail entry witnesses a
   hole can change or vanish on a backtrack between the pruning and whenever the
   explanation is rendered, which is I-X6 and the trap lib/core/prop/linear.ml's
   [explain_cross_conflict] header describes at length. Until D-0214 that was ensured by
   reading it eagerly at the call site; the history answers the same entry later.

   The entry this finds always punched a HOLE rather than moved a bound, and that is
   forced by the caller's guard rather than checked here: the caller has already
   established [lo(c) <= w <= hi(c)], and a bound move that removed [w] would have left
   [w] outside the current bounds, since bounds only tighten. *)
let hole_line t fr w =
  match fr.pend with
  | Some p when w < p.p_upto && p.p_in w -> Some (p.p_expl w)
  | _ -> (
      match View.base_var t.res with
      | None -> None
      | Some rv ->
          let bw =
            match t.res with
            | View.Affine { map; _ } -> Lit.unapply map w
            | View.Const _ -> w
          in
          Option.map
            (fun e -> removal_explanation_at fr.h e bw)
            (remover_at fr.h ~var:rv bw))

(* An interior INDEX hole that this propagator did not punch, as the clause a summand
   may cite (D-0084, built by M7-T21).

   THE RULE: a hole punched at level 0 is the bare unit [~idx_eq_p]; a hole punched
   under a decision is `~idx_eq_p \/ ~<the puncher's facts>`.

   WHY. The bare unit was once used for both, asserted as a [rup]. It is RUP only when the
   hole is a consequence of the model alone, which is true of a hole punched at LEVEL 0
   and false of one punched under a decision: the hole's own trace line is `~idx_ge_p \/
   idx_ge_(p+1) \/ ~<the puncher's facts>`, and with nothing assumed but [idx_eq_p] those
   facts are not falsified, so unit propagation never fires it. 3.0.2 refuses the line,
   `test/models/element_foreign_hole_rup_sat.fzn` is the scene, and it is the 23-of-26
   shape D-0080 found in the corpus (`rup +1 ~<v>_eq_<k> >= 1 ;` at a level > 0, empty
   tail). The line is reached only when ANOTHER element's derivation embeds this one --
   [excl_hole] cites the result hole's remover's explanation, which is this module's
   [hole_expl] -- and that derivation is forced, which a factless conflict does when
   search.ml writes its derivation on the page (the arm D-0040 introduced).

   The repair is alldiff.ml's [Gone_hole] arm, verbatim in kind: carry the PUNCHER's
   facts into the clause, `~idx_eq_p \/ ~facts`, which is RUP against the hole's own
   trace line plus the channelling halves (assume idx_eq_p and the facts; the halves set
   idx_ge_p and ~idx_ge_(p+1); the hole's line is then falsified). The leftover literals
   stay in the row, which is the same globally valid "pruning disjoined with what it
   read" every other arm of [pos_gone] already derives. A level-0 hole keeps the bare unit
   -- it is RUP there, and keeping it leaves every proof that never reaches a deep foreign
   hole byte-identical. The remover is found from the frame's history (I-X6, D-0214).

   THE PUNCHER IS FOUND WHEN THIS IS CALLED, ITS LITERALS ARE NOT (M11-complexity-T11).
   The clause used to be materialised here, so every pruning of this instance copied every
   foreign hole's puncher's literals once per dead position -- O(dead x facts) words per
   entry, with facts growing along the branch. On 2011_black-hole_9 (--no-proof, node 40,
   the same trail of 24 928 entries) the live heap goes from 1 193 MB to 291 MB, the
   arena's share from 965 MB to 63 MB. What the thunk keeps is the puncher's [Reason.t],
   which is frozen data (a [Facts] list, or a [Later] reading a history that is live as
   long as the puncher is on the trail -- and the puncher is BELOW this pruning, so it
   outlives every arena slot that can hold this thunk). The literals, their order and the
   clause are the ones the eager call built, so every proof byte is the same. *)
let index_hole_clause t fr bp =
  let unit = Lit.negate (Lit.eq t.iname bp) in
  match index_hole_puncher t fr bp with
  | Some e when not (at_root_at fr.h e.Store.pos) ->
      let reason = e.Store.reason in
      Explanation.deferred (fun () ->
          Explanation.clause (unit :: List.map Lit.negate (Reason.lits reason)))
  | Some _ | None -> Explanation.clause [ unit ]

(* WHAT A SHAPE-1 LINE LEAVES BEHIND, so that a conflict can cancel it.

   Each arm of [pos_gone] derives [~idx_eq_p] disjoined with AT MOST ONE bound literal --
   the bound it read. For a PRUNING that residue is exactly right: it makes the derived
   row the globally valid "the pruning, disjoined with the bounds it rests on", the shape
   lib/core/prop/ne.ml's clause already has, sound at any level. For a CONFLICT it is
   fatal -- a row with literals left in it is not contradicting, which 3.0.2 says in as
   many words ("The constraint with ID n is not contradicting, as specified by the hint")
   and which this row measured on its own two-element scene before it was tracked.

   So the residue is carried out of [pos_gone] as data rather than recomputed, because
   the count has to be EXACT: one copy of the cancelling line per copy of the literal,
   and the arms that leave nothing (a value outside the result's DECLARED range, where
   the literal does not exist at all) must contribute nothing. Recomputing that from the
   domains at the conflict site is the kind of agreement-by-comment D-0026 exists to
   refuse (D-0026 keeps a pruning's reason and its justification as two values built
   together, so that they cannot drift). *)
type residue =
  | R_none
  | R_res_hi of int (* leaves [c_ge_(hi+1)]; cancelled by the line stating c <= hi *)
  | R_res_lo of int (* leaves [~c_ge_lo];    cancelled by the line stating c >= lo *)
  | R_idx_lo of int
  | R_idx_hi of int

(* Why position [p] is not available, as a line deriving [~idx_eq_p] -- possibly
   disjoined with bound literals of the result or of the index, which is the globally
   valid form and the one a PRUNING wants.

   The last two arms are the only [Explanation.Clause] in this module, and both are the
   case "an interior hole in the INDEX, punched by something that is not this
   propagator" -- today only [Ne] can do that. A clause is what alldiff.ml reaches for in
   the same position and for the same reason: [Explanation.t] cannot ask for "the id of
   the line that states this fact" (D-0009's open ADT gap), and [Justify.emit_clause]
   consults the claim index (M2-T9, literal to defining proof line, filled by [Trace])
   and mints nothing. The cost is stated rather than
   hidden: a conflict whose derivation reaches one of these arms rests on a clause.
   Until D-0131 that routed it the D-0022 way and left this module's [pol] decorative
   FOR THAT CONFLICT; every root conflict now closes on its trace instead. *)
let pos_gone t fr p =
  let n = Array.length t.values in
  (* WHICH ARM is decided from the frame; BUILDING it is deferred, and the split is not
     stylistic. The arm depends on the store and must be pinned at the moment of the
     pruning (I-X6), which the frame is (D-0214). The construction depends on [Encoding]'s constraint
     ids, which do not exist at all until [Encoding.start_proof] runs -- a unit test that
     propagates without writing a proof is the ordinary case, and forcing the lookup
     eagerly would make it raise [need]'s diagnostic where nothing is wrong. *)
  let later f = Explanation.deferred f in
  if p < 0 || p >= n then (later (fun () -> excl_out t p), R_none)
  else
    let w = t.values.(p) in
    let rlo = res_lo t fr and rhi = res_hi t fr in
    if w > rhi then
      ( later (fun () -> excl_above t p ~bhi:rhi),
        if w > t.rdhi then R_none else R_res_hi rhi )
    else if w < rlo then
      ( later (fun () -> excl_below t p ~blo:rlo),
        if w < t.rdlo then R_none else R_res_lo rlo )
    else if not (res_mem t fr w) then
      match hole_line t fr w with
      | Some hole -> (later (fun () -> excl_hole t p ~hole), R_none)
      | None -> (Explanation.clause [ Lit.negate (Lit.eq t.iname (base_of t p)) ], R_none)
    else
      (* as[p] is still available, so p left dom(idx) for a reason of the index's own. *)
      let bp = base_of t p in
      let dlo = Domain.lo fr.di and dhi = Domain.hi fr.di in
      if bp < dlo then (later (fun () -> idx_excl_below t p ~blo:dlo), R_idx_lo dlo)
      else if bp > dhi then (later (fun () -> idx_excl_above t p ~bhi:dhi), R_idx_hi dhi)
      else (index_hole_clause t fr bp, R_none)

(* ---- shape 2: what the live positions force about the result ---- *)

(* [sum_{p live} idx_eq_p \/ <lits> >= 1]: the declared at-least-one line, narrowed by
   one [pos_gone] per dead position. Each cancels its own term and leaves the degree at
   1, exactly as alldiff.ml's [alo_over] does over a Hall set. *)
(* A bound the SEARCH established, cited by [Explanation.Defining] (D-0064: a summand
   that carries the id of the unit line stating a bound fact; lib/core/explanation.ml's
   header, "[Defining], and why it is a SUMMAND"). M4-T3 built this module before that
   constructor existed and stood in with [Explanation.term c (Explanation.clause [l])] --
   the right arithmetic wearing the wrong label, per explanation.ml's own words -- which
   cancels the term but, because a [Clause] may be any width, is not an EXACT
   cancellation, and trips the search of that time into routing every conflict that used
   it the D-0022 way (`conclusion UNSAT` citing the empty clause, this module's own [pol]
   left decorative; that routing is gone since D-0131). [Explanation.defining] cites a
   UNIT line and is exact, so a root conflict built only from [Defining] summands closes
   on its own [pol].

   [established_at_root] mirrors lib/core/prop/alldiff.ml's function of the same name
   (kept as two functions because alldiff.ml was another task's file when this was
   written, and because this one reads a history where alldiff's reads the store):
   whether the trail entry supporting a bound was pushed at the root, true for a bound
   that has never moved. A bound the ROOT fixpoint set is a consequence of the model and
   stays true and citable at ANY search depth; one a DECISION set is not (D-0064's level
   rule) -- so, unlike the old blanket "only at [Store.level store] = 0", the check below
   is per LITERAL, not per conflict, and it fires above level 0 exactly when the specific
   bound cited happened to be a root one. It reads a HISTORY, never the store: the support
   arrays are live store state that a later backtrack can invalidate, which is why
   alldiff.ml's [snap_of] snapshots [s_lo_root]/[s_hi_root] before wrapping anything in
   [deferred]. [Store.lo_support_at] walks the support back to below the cut, and a level
   mark below the cut does not move while the cut is live, so the answer is the one the
   store gave at the cut (D-0214). The conflict paths pass the live history
   ([Store.history store]), where it is the store's own answer. *)
let established_at_root h v ~lower =
  let sup = if lower then Store.lo_support_at h v else Store.hi_support_at h v in
  sup = Store.no_support || at_root_at h sup

(* One cancelling line per copy of each residue literal, when established at root;
   otherwise the group contributes nothing and the residue's term stays in the
   at-least-one row uncancelled -- not a loss, because only a ROOT conflict's derivation
   must close to [0 >= 1] on its own, and under a decision the branch is closed by its
   nogood, which is RUP over the branch's trace lines (D-0018), regardless. The values are
   read off the residues rather than from the store, so the line cancelled is the bound
   the exclusion actually read, and the multiplicity is the number of exclusions that read
   it. Reads the frame only (see above), so it may run inside the [Explanation.deferred]
   its caller wraps around the combine (D-0214). *)
let residue_cancel t fr ~dead =
  let rn = match t.rname with Some x -> x | None -> "" in
  let group sel lit_of var_opt ~lower =
    match List.filter_map (fun (_, r) -> sel r) dead with
    | [] -> []
    | vs -> (
        match var_opt with
        | None -> []
        | Some var ->
            if established_at_root fr.h var ~lower then
              [ Explanation.defining (List.length vs) (lit_of (List.hd vs)) ]
            else [])
  in
  group
    (function R_res_hi h -> Some h | _ -> None)
    (fun h -> Lit.le rn h)
    (View.base_var t.res) ~lower:false
  @ group
      (function R_res_lo l -> Some l | _ -> None)
      (fun l -> Lit.ge rn l)
      (View.base_var t.res) ~lower:true
  @ group
      (function R_idx_lo l -> Some l | _ -> None)
      (fun l -> Lit.ge t.iname l)
      (Some t.ibase) ~lower:true
  @ group
      (function R_idx_hi h -> Some h | _ -> None)
      (fun h -> Lit.le t.iname h)
      (Some t.ibase) ~lower:false

(* Membership in [live] through a table (D-0155, M11-complexity-T8), where it was a
   [List.mem] per declared position -- O(|decl_pos| x |live|) on every pruning's eager
   explanation, and [filter_result] builds one per hole it punches. Same positions, same
   order: the walk is still over [t.decl_pos]. *)
module Int_tbl = Hashtbl.Make (Int)

let int_set l =
  let s = Int_tbl.create ((2 * List.length l) + 1) in
  List.iter (fun x -> Int_tbl.replace s x ()) l;
  s

(* [alive] is [int_set live], built by the caller (a lever of the file-by-file review,
   M16-file-review-T2, D-0190), so that
   [filter_result] builds it once per pass for its two pushes and every hole it punches,
   where each of them built its own. The same table answers the same [mem]. *)
let dead_positions t fr ~alive =
  List.filter_map
    (fun p -> if Int_tbl.mem alive p then None else Some (pos_gone t fr p))
    t.decl_pos

(* [cancel] is [residue_cancel] over the same [dead], computed by the caller from the
   same frame (D-0084, M7-T21). THE RULE: a pruning's derivation cancels its
   root-established residue too, not only a conflict's. WHY: the argument that "only a
   ROOT conflict's derivation must close" is true of THIS module's conflicts and false of
   a derivation EMBEDDED in one: [excl_hole] cites the remover of
   a result hole by its explanation, which is another element instance's [hole_expl] when
   two elements share a result, and that instance's residue then arrives uncounted in a
   root conflict that must close. 3.0.2: "The constraint with ID n is not contradicting"
   (test/models/element_shared_result_root_unsat.fzn). Cancelling the root-established
   residue HERE makes a pruning derivation at the root exact, so whatever embeds it gets
   exactly `~idx_eq_p` or `c <> v` and nothing else. Above the root it cancels only what
   the root established, which leaves the row stronger and still globally valid. *)
let alo_of t ~dead ~cancel =
  Explanation.deferred (fun () ->
      Explanation.combine
        (cite (need "at-least-one" (Encoding.at_least_one_id t.enc t.iname))
         :: List.map (fun (e, _) -> Explanation.term 1 e) dead
        @ cancel)
        1)

(* [~idx_eq_p \/ ~c_ge_(b+1)] for a live position whose value is at most [b]. *)
let at_most_from t p ~b =
  Explanation.combine
    (Explanation.term 1 (implies_le t p)
    :: List.map (fun u -> cite (res_rung t u)) (range (t.values.(p) + 1) b))
    1

(* [~idx_eq_p \/ c_ge_a] for a live position whose value is at least [a]. *)
let at_least_from t p ~a =
  Explanation.combine
    (Explanation.term 1 (implies_ge t p)
    :: List.map (fun u -> cite (res_rung t u)) (range a (t.values.(p) - 1)))
    1

(* The dead positions and the cancellation of their residue, read from the frame (D-0214)
   when the derivation is first forced rather than at the pruning. The [lazy] is kept by the
   closure, so a re-forcing after [Justify] releases the thunk cites the same position
   thunks the first forcing did, exactly as the list the eager code built and captured. *)
let dead_and_cancel t fr ~alive =
  lazy
    (Store.check_history fr.h;
     let dead = dead_positions t fr ~alive:(Lazy.force alive) in
     (dead, residue_cancel t fr ~dead))

let push_hi_expl t fr ~live ~alive ~b =
  let dc = dead_and_cancel t fr ~alive in
  Explanation.deferred (fun () ->
      let dead, cancel = Lazy.force dc in
      Explanation.combine
        (Explanation.term 1 (alo_of t ~dead ~cancel)
        :: List.map (fun p -> Explanation.term 1 (at_most_from t p ~b)) live)
        (List.length live))

let push_lo_expl t fr ~live ~alive ~a =
  let dc = dead_and_cancel t fr ~alive in
  Explanation.deferred (fun () ->
      let dead, cancel = Lazy.force dc in
      Explanation.combine
        (Explanation.term 1 (alo_of t ~dead ~cancel)
        :: List.map (fun p -> Explanation.term 1 (at_least_from t p ~a)) live)
        (List.length live))

(* [~c_ge_v \/ c_ge_(v+1)] -- "c <> v" -- for a value no live position carries. The two
   halves arrive with different coefficients ([na] positions below [v], [nb] above), so
   each is padded up to their maximum with its own literal axiom before the division:
   D-0009's weakening, used exactly as alldiff.ml's [pair_amo] uses it. *)
let hole_expl t fr ~live ~alive ~v =
  (* [m = 0] below is exactly [live = []]: [v] is carried by no live position, so every
     live position is below or above it. Refused here, at the pruning, as before D-0214. *)
  if live = [] then
    invalid_arg "Element.hole_expl: no live position, which is a conflict and not a hole";
  let rn = match t.rname with Some x -> x | None -> assert false in
  let dc = dead_and_cancel t fr ~alive in
  Explanation.deferred (fun () ->
      let dead, cancel = Lazy.force dc in
      let below = List.filter (fun p -> t.values.(p) < v) live in
      let above = List.filter (fun p -> t.values.(p) > v) live in
      let na = List.length below and nb = List.length above in
      let m = Int.max na nb in
      let pad k lit = if k > 0 then [ Explanation.weaken [ (k, lit) ] ] else [] in
      Explanation.combine
        (Explanation.term 1 (alo_of t ~dead ~cancel)
         :: List.map (fun p -> Explanation.term 1 (at_most_from t p ~b:(v - 1))) below
        @ List.map (fun p -> Explanation.term 1 (at_least_from t p ~a:(v + 1))) above
        @ pad (m - na) (Lit.negate (Lit.ge rn v))
        @ pad (m - nb) (Lit.ge rn (v + 1)))
        m)

(* ---------------------------------------------------------------------- reasons *)

(* The bounds this propagator reads. Both views, always, because both filtering rules
   read both -- and an over-stated fact is a weaker trace line, never an unsound one,
   where an under-stated one breaks I-P5 (every bound move carries the facts its trace
   line negates). [Reason.lit_of_fact] drops whichever are still at
   their declared value. The index's HOLES are not here and cannot be -- [Reason.t] has no
   fact for one. The discharge that used to be written here was WRONG, and D-0075 is the
   record of it: it said the checker re-derives the hole from this constraint's own
   rows or "from the hole's own earlier trace line", and the second half does not hold: a
   hole's trace line has a TAIL, and `rup` cannot fire it unless that tail is falsified.
   What closes the gap is [index_hole_facts]/[result_hole_facts] below, which put the
   PUNCHER's reason on this line's tail. Read them before the I-X10 section of the module
   header, whose measurement did not reach this case. *)
let bound_facts t fr =
  let idx =
    [
      Reason.at_least ~name:t.iname ~decl:t.idlo (Domain.lo fr.di);
      Reason.at_most ~name:t.iname ~decl:t.idhi (Domain.hi fr.di);
    ]
  in
  match t.rname with
  | None -> idx
  | Some rn ->
      idx
      @ [
          Reason.at_least ~name:rn ~decl:t.rdlo (res_lo t fr);
          Reason.at_most ~name:rn ~decl:t.rdhi (res_hi t fr);
        ]

(* ------------------------------------------------------------------ hole facts

   THE RULE (D-0075, built by M7-T13): a pruning that READ a hole carries, on its trace
   line's tail, the reason of the entry that punched the hole.

   WHY. [bound_facts] above cannot state the holes, and the old belief that the checker
   re-derives them "from the hole's own earlier trace line" is false; `2012_tpp` is where
   it was caught. A hole's own trace line is a clause with its own
   TAIL -- the facts the propagator that punched the hole read. [rup] is unit propagation,
   so that line only fires once its tail is falsified, and the tail is not falsified by
   negating a line that never mentions it. The reproducer is
   `test/models/element_index_hole_rup_sat.fzn`, where the result push had NO tail at all
   (every bound still at its declared value) and the line said, unconditionally, something
   the model does not entail.

   So the facts have to travel. [Reason.t] still has no fact for a hole -- and a hole fact
   could not go on a clause tail anyway, since the negation of `x <> v` is the CONJUNCTION
   `x >= v /\ x <= v` and a clause tail holds literals. What travels instead is the reason
   of the trail entry that PUNCHED the hole, which is bound facts and does fit. That is
   lib/core/trace.ml's [settle_facts] technique, applied one step earlier: there the line
   for a settled bound cites the hole's facts, here the line for a pruning that READ a hole
   cites them.

   Which holes: rule 2 (the result's bounds) reads dom(idx), so a result pruning carries
   the INDEX's holes; rule 1 reads dom(c), so an index pruning carries the RESULT's. Both
   are collected over the whole current window rather than over the holes the pruning
   provably leaned on -- an over-stated reason is a weaker line, never an unsound one, the
   same trade [bound_facts] makes. [None] from [Store.remover] is a hole behind no trail
   entry, which `lib/` cannot produce: since D-0072 a set domain's holes are punched by
   propagators at the root, so each has a remover (see [Store.remover]'s header). Citing
   nothing there is what trace.ml does and leaves the line exactly as strong as it was. *)
(* THE DEDUPLICATION, in first-occurrence order, in linear time (D-0155,
   M11-complexity-T8). Until D-0155 this was [List.mem f acc] then [acc @ [f]] per fact:
   quadratic in the facts collected, each step a POLYMORPHIC compare of records holding
   `X_INTRODUCED_` names, and 99 % of `2011_black-hole_10`'s run (measured in D-0151
   section 2). The list it returns is the one the old fold returned, element for element:
   the seed is kept whole and in order (duplicates inside it included, exactly as the fold
   never examined them), and every later fact is appended iff no equal fact precedes it.
   Equality is structural on the two constructors, which is what [List.mem]'s [=] was on
   this type; [Fact_tbl] only makes it monomorphic and hashed. The ORDER is load-bearing:
   it is the order of a trace line's tail, which the proof diff compares byte for byte. *)
module Fact_tbl = Hashtbl.Make (struct
  type t = Reason.fact

  let equal (a : t) (b : t) =
    match (a, b) with
    | At_least x, At_least y ->
        x.value = y.value && x.decl = y.decl && String.equal x.name y.name
    | At_most x, At_most y ->
        x.value = y.value && x.decl = y.decl && String.equal x.name y.name
    | At_least _, At_most _ | At_most _, At_least _ -> false

  let hash (f : t) =
    match f with
    | At_least { name; value; decl } -> Hashtbl.hash (0, name, value, decl)
    | At_most { name; value; decl } -> Hashtbl.hash (1, name, value, decl)
end)

type fact_acc = { seen : unit Fact_tbl.t; mutable rev : Reason.fact list }

let fact_acc seed =
  let seen = Fact_tbl.create 16 in
  List.iter (fun f -> Fact_tbl.replace seen f ()) seed;
  { seen; rev = List.rev seed }

let add_to acc fs =
  List.iter
    (fun f ->
      if not (Fact_tbl.mem acc.seen f) then (
        Fact_tbl.add acc.seen f ();
        acc.rev <- f :: acc.rev))
    fs

let acc_facts acc = List.rev acc.rev

(* [seed] followed by the facts of [fs] that are neither in [seed] nor earlier in [fs]. *)
let add_facts seed fs =
  match fs with
  | [] -> seed
  | _ ->
      let acc = fact_acc seed in
      add_to acc fs;
      acc_facts acc

let remover_facts h ~var v =
  match remover_at h ~var v with None -> [] | Some e -> Reason.facts e.Store.reason

let holes_of d =
  List.filter (fun v -> not (Domain.mem d v)) (range (Domain.lo d + 1) (Domain.hi d - 1))

(* [d] is [var]'s domain in the frame [h] belongs to. *)
let hole_facts h ~var d =
  let acc = fact_acc [] in
  List.iter (fun v -> add_to acc (remover_facts h ~var v)) (holes_of d);
  acc_facts acc

(* The facts behind the INDEX's interior holes: what a RESULT pruning read beyond bounds. *)
let index_hole_facts t fr = hole_facts fr.h ~var:t.ibase fr.di

(* The facts behind the RESULT's interior holes: what an INDEX pruning read beyond bounds.
   Over the result's BASE domain, so no view value has to be translated back -- the facts
   are the same either way and this needs no [View] inverse. *)
let result_hole_facts t fr =
  match View.base_var t.res with None -> [] | Some rv -> hole_facts fr.h ~var:rv fr.dr

(* What a value removal concludes (the [Reason.fact] carried on its [justified] value,
   D-0043), on the INDEX's base variable: a removal at a
   bound settles and concludes the bound it settled to, an interior one concludes a
   two-literal clause, which is not a [Reason.fact] and is [None]. The same partition
   lib/core/prop/ne.ml's [removal_conclusion] makes, over the same [Domain] shape. *)
let removal_conclusion t d bw =
  if bw = Domain.lo d then (
    let v = ref (bw + 1) in
    while !v <= Domain.hi d && Domain.is_hole d !v do
      incr v
    done;
    Some (Reason.at_least ~name:t.iname ~decl:t.idlo !v))
  else if bw = Domain.hi d then (
    let v = ref (bw - 1) in
    while !v >= Domain.lo d && Domain.is_hole d !v do
      decr v
    done;
    Some (Reason.at_most ~name:t.iname ~decl:t.idhi !v))
  else None

(* ------------------------------------------------------------------- propagation *)

exception Found of Store.conflict

let live_positions t store = List.filter (fun p -> View.mem store t.pos p) t.decl_pos

(* The result's base variable is the index's (one variable on both sides). *)
let shares_index t =
  match View.base_var t.res with Some rv -> Var.equal rv t.ibase | None -> false

(* WHAT AN EMPTY-INDEX CONFLICT READ, per dead position, arm by arm (D-0101, M7-T25).

   This is [pos_gone]'s case split replayed to say which FACTS each arm's line rests on,
   rather than which line it is. It must agree with [pos_gone] arm for arm, because the
   conflict line `rup ~facts >= 1` is RUP only if every literal the derivation leaves
   behind is falsified by assuming the facts -- and what each arm leaves behind is:

     - outside the array, or a value outside the result's DECLARED range: nothing (the
       row is already the unit [~idx_eq_p]);
     - as[p] above hi(c): [c_ge_(hi+1)], so the fact [c <= hi];
     - as[p] below lo(c): [~c_ge_lo], so the fact [c >= lo];
     - as[p] a HOLE in c: [excl_hole] embeds the remover's own derivation, which leaves
       the remover's residue -- the negation of the REMOVER'S facts (a hole is cited
       through its remover, never as a bound fact: D-0075, D-0084); a declared hole
       leaves nothing;
     - p below lo(idx) / above hi(idx): [~idx_ge_lo] / [idx_ge_(hi+1)], so the index
       bound;
     - p an interior INDEX hole: [index_hole_clause] carries the puncher's facts negated
       when the puncher acted under a decision, and nothing for a level-0 hole.

   Each arm reads exactly what [pos_gone] reads (the same frame: [res_lo]/[res_hi],
   [hole_line]'s remover, [index_hole_puncher]), taken at the conflict and used at once.
   A fact at its declared value materialises to no literal, matching an arm that leaves
   none. Root-established residue that [residue_cancel] cancels is still listed: a root
   fact is harmless on a tail (Analysis drops root nodes from every cut), and listing it
   keeps this function free of a second copy of the cancellation rule. *)
(* A BREAK, for test/unit/test_learn.ml alone: drop the result hole's remover's facts
   from the conflict's reason, which is the D-0075 mistake made again on this line. The
   conflict line then claims more than the derivation ahead of it supports, and 3.0.2
   refuses it (test/models/element_learn_hole_sat.fzn). Never set outside that lane. *)
let break_hole_facts = ref false

let conflict_facts t fr =
  let n = Array.length t.values in
  let rlo = res_lo t fr and rhi = res_hi t fr in
  let dlo = Domain.lo fr.di and dhi = Domain.hi fr.di in
  let puncher_facts bp =
    match index_hole_puncher t fr bp with
    | Some e when not (at_root_at fr.h e.Store.pos) -> Reason.facts e.Store.reason
    | Some _ | None -> []
  in
  let of_pos p =
    if p < 0 || p >= n then []
    else
      let w = t.values.(p) in
      let rn () = Option.get t.rname in
      if w > rhi then
        if w > t.rdhi then [] else [ Reason.at_most ~name:(rn ()) ~decl:t.rdhi rhi ]
      else if w < rlo then
        if w < t.rdlo then [] else [ Reason.at_least ~name:(rn ()) ~decl:t.rdlo rlo ]
      else if not (res_mem t fr w) then
        match View.base_var t.res with
        | None -> []
        | Some rv -> if !break_hole_facts then [] else remover_facts fr.h ~var:rv w
      else
        let bp = base_of t p in
        if bp < dlo then [ Reason.at_least ~name:t.iname ~decl:t.idlo dlo ]
        else if bp > dhi then [ Reason.at_most ~name:t.iname ~decl:t.idhi dhi ]
        else puncher_facts bp
  in
  let acc = fact_acc [] in
  List.iter (fun p -> add_to acc (of_pos p)) t.decl_pos;
  acc_facts acc

(* Every declared position is impossible, so the at-least-one line has nothing left and
   the sum IS [0 >= 1] -- once the bound literals the exclusions carried are cancelled.

   AT THE ROOT: [Reason.none], deliberately. With no decision there is no branch to
   learn from, and every residue the root established is cancelled by [residue_cancel],
   so the derivation itself closes to [0 >= 1], and search.ml's root arm writes it on
   the page before the empty clause. The
   facts genuinely ARE none there in the sense that matters -- each one a root
   consequence of the model -- and keeping the arm factless keeps every root refutation
   byte-identical.

   UNDER A DECISION (D-0101, M7-T25): the facts [conflict_facts] collects, and the
   conflict is made under [Store.deriving_ahead]. Until M7-T25 this arm was factless too
   (D-0091's finding), which is sound -- search.ml wrote the factless conflict's
   derivation on the page (the arm D-0040 introduced) and the full decision nogood closed
   the branch -- but it handed [Learn.at_conflict] an
   empty cut, so no element conflict ever produced a 1UIP clause. With facts,
   [Trace.conflict_line] writes `rup ~facts >= 1`, and that line is the counting
   argument, NOT reverse unit propagation over the rows (each r_ge/r_le row leaves a
   two-literal [idx <> p] that unit propagation cannot sum). So the derivation goes on
   the page FIRST ([Store.conflict]'s [c_ahead], the mechanism D-0096 introduced, with
   cumulative.ml as the template): under a
   decision it derives "not all of these bounds hold", every literal of which is the
   negation of a fact listed here, and the `rup` is then unit propagation against that
   one line. *)
let no_position_conflict t store =
  (* A conflict is consumed where it is raised, so its reason is not deferred (D-0124,
     which made pruning reasons later, keeps conflicts eager); the frame is only the
     shared way of reading. *)
  let fr = frame t store in
  let dead = dead_positions t fr ~alive:(int_set []) in
  let cancel = residue_cancel t fr ~dead in
  let why =
    Explanation.deferred (fun () ->
        Explanation.combine
          (cite (need "at-least-one" (Encoding.at_least_one_id t.enc t.iname))
           :: List.map (fun (e, _) -> Explanation.term 1 e) dead
          @ cancel)
          1)
  in
  if Store.level store = 0 then
    Store.conflict store (Reason.because ~concludes:None Reason.none why)
  else
    let facts = conflict_facts t fr in
    Store.deriving_ahead store (fun () ->
        Store.conflict store (Reason.because ~concludes:None facts why))

(* The three ways a pruning of the RESULT can run into a bound the result already has.
   Each derivation below concludes a single order literal, so the contradiction is that
   literal against the line that states its negation, walked to a common rung. Written
   out rather than routed through one helper because the three ladders run in different
   directions and collapsing them would hide which. *)

(* Pushing lo(c) to [a] against hi(c) = [h < a]: [c_ge_a] against [~c_ge_(h+1)], joined
   by the rungs between them. Above the declared range there is no [c_ge_a] at all and
   the derivation is already [0 >= 1]. *)
let lo_push_conflict t store ~expl ~a ~h =
  let cite_defining =
    Option.is_some t.rname && a <= t.rdhi
    && established_at_root (Store.history store)
         (Option.get (View.base_var t.res))
         ~lower:false
  in
  Explanation.deferred (fun () ->
      if not cite_defining then expl
      else
        let rn = Option.get t.rname in
        Explanation.combine
          (Explanation.term 1 expl
          :: Explanation.defining 1 (Lit.le rn h)
          :: List.map (fun u -> cite (res_rung t u)) (range (h + 1) (a - 1)))
          1)

let hi_push_conflict t store ~expl ~b ~l =
  let cite_defining =
    Option.is_some t.rname && b >= t.rdlo
    && established_at_root (Store.history store)
         (Option.get (View.base_var t.res))
         ~lower:true
  in
  Explanation.deferred (fun () ->
      if not cite_defining then expl
      else
        let rn = Option.get t.rname in
        Explanation.combine
          (Explanation.term 1 expl
          :: Explanation.defining 1 (Lit.ge rn l)
          :: List.map (fun u -> cite (res_rung t u)) (range (b + 1) (l - 1)))
          1)

(* Removing the last value: [~c_ge_v \/ c_ge_(v+1)] against the two lines that pin
   [c = v]. Either half is absent at a declared bound, where the residue it would cancel
   is the constant false and the derivation is that much closer to [0 >= 1] already; a
   half whose bound was established under a DECISION rather than the root is treated the
   same way -- omitted, not cited (D-0064's level rule: only a bound established at the
   root has a true unit line), which is why the two halves are
   checked independently rather than gating the whole function on one level. *)
let hole_conflict t store ~expl ~v =
  let lo_ok, hi_ok =
    match t.rname with
    | None -> (false, false)
    | Some _ ->
        let rv = Option.get (View.base_var t.res) in
        let h = Store.history store in
        ( v > t.rdlo && established_at_root h rv ~lower:true,
          v < t.rdhi && established_at_root h rv ~lower:false )
  in
  Explanation.deferred (fun () ->
      match t.rname with
      | None -> expl
      | Some rn -> (
          let halves =
            (if lo_ok then [ Explanation.defining 1 (Lit.ge rn v) ] else [])
            @ if hi_ok then [ Explanation.defining 1 (Lit.le rn v) ] else []
          in
          match halves with
          | [] -> expl
          | _ -> Explanation.combine (Explanation.term 1 expl :: halves) 1))

let conflict_of store why =
  Store.conflict store (Reason.because ~concludes:None Reason.none why)

(* ONE CURRENCY FOR A HOLE (D-0084, M7-T21). An INTERIOR index removal states
   `idx <> p` the way every other hole
   in the store is stated -- over the ORDER encoding, `~idx_ge_p \/ idx_ge_(p+1)` -- and
   not in this module's working currency [~idx_eq_p]. The forward channelling line
   [idx_eq_p \/ ~idx_ge_p \/ idx_ge_(p+1)] converts one into the other exactly.

   The trail entry's explanation is a CONTRACT with whoever embeds it, and the one
   embedder is [excl_hole]: when this index is ANOTHER element's RESULT, that instance
   excludes a position by citing this hole's remover's explanation and pairing it off
   against its own two order-literal rows. Handed `~idx_eq_p` instead, nothing cancelled
   and a root conflict did not close (test/models/element_crossed_root_unsat.fzn: two
   elements, each one's index the other's result). [pos_gone]'s own derivations are
   untouched: they build [~idx_eq_p] directly and never read this entry's explanation.
   A removal AT a bound is a bound move, which no one embeds, and keeps its form. *)
let in_order_currency t bw expl =
  match Encoding.direct_fwd_id t.enc t.iname bw with
  | None -> expl
  | Some fwd -> Explanation.combine [ Explanation.term 1 expl; cite fwd ] 1

(* Rule 1: dom(idx) := { p : as[p] in dom(c) }. Returns whether a removal landed.

   EVERY DEDUCTION IN ONE PASS (I-P6: a pass applies every deduction its reading
   justifies). This module takes no pass snapshot: every removal reads the store LIVE --
   [View.mem] for the position, [d] for the conclusion's shape, and its own [frame] for
   the reason ([bound_facts]/[result_hole_facts], built when asked, D-0214) -- so
   continuing after a landed removal reads exactly what a restarted pass would have read.
   Until M6-T19 the pass restarted at the first removal that landed, so an index with k
   dead positions cost k + 1 walks of [decl_pos]. *)
let filter_index t store =
  let n = Array.length t.values in
  let moved = ref false in
  (* The result's hole facts, read ONCE per pass rather than once per removal (D-0155,
     M11-complexity-T8). A removal here moves the INDEX and nothing else, so while the
     result's base variable is a different variable its holes and their removers are the
     same at every removal of the pass, and the list is the one each removal used to
     rebuild. Forced at the first removal, before which this pass has written nothing.
     When the result IS the index (one variable on both sides), every removal re-reads. *)
  let shares_index =
    match View.base_var t.res with Some rv -> Var.equal rv t.ibase | None -> false
  in
  (* The pass's FIRST removal's frame, and the result's hole facts read from it when a
     reason first asks (D-0214) -- the list the eager code built at that removal. *)
  let first = ref None in
  let res_holes fr =
    if shares_index then lazy (result_hole_facts t fr)
    else
      match !first with
      | Some l -> l
      | None ->
          let l = lazy (result_hole_facts t fr) in
          first := Some l;
          l
  in
  List.iter
    (fun p ->
      if View.mem store t.pos p then
        let dead = p < 0 || p >= n || not (View.mem store t.res t.values.(p)) in
        if dead then (
          (* The emptying removal is reported as the counting conflict rather than made,
             because the [Failed] arm would hand back this ONE position's derivation and
             that is not contradicting. *)
          if View.size store t.pos <= 1 then raise (Found (no_position_conflict t store));
          let fr = frame t store in
          let bw = base_of t p in
          (* The residue is cancelled where the ROOT established it and kept where a
             decision did: kept, the derived row is the globally valid "pruning
             disjoined with the bounds it read"; cancelled, a root derivation is exact,
             which is what [excl_hole] needs when it embeds this entry's explanation in
             another instance's root conflict (M7-T21, D-0084; see [alo_of]).

             The conclusion is decided now (the store checks it at the push, D-0214);
             the position's line, the cancellation and the facts are read from [fr] when
             first asked. [gone] is kept by the closure so that a re-forcing cites the same
             thunk, as the eager pair did. *)
          let concludes = removal_conclusion t fr.di bw in
          let gone =
            lazy
              (Store.check_history fr.h;
               let expl, r = pos_gone t fr p in
               (expl, residue_cancel t fr ~dead:[ (expl, r) ]))
          in
          let holes = res_holes fr in
          let j =
            Reason.because_later ~concludes ~empty:false
              (fun () ->
                Store.check_history fr.h;
                add_facts (bound_facts t fr) (Lazy.force holes))
              (Explanation.deferred (fun () ->
                   let expl, cancel = Lazy.force gone in
                   let exact =
                     if cancel = [] then expl
                     else Explanation.combine (Explanation.term 1 expl :: cancel) 1
                   in
                   if concludes = None then in_order_currency t bw exact else exact))
          in
          match View.remove store t.pos p j with
          | Store.Conflict c -> raise (Found c)
          | Store.Changed ->
              Propagator.count_deduction ();
              moved := true
          | Store.Unchanged -> ()))
    t.decl_pos;
  !moved

(* Rule 2: dom(c) := { as[p] : p in dom(idx) }. Returns whether a push landed. The two
   bound pushes and the hole removals are independent -- a bound push reads the other
   bound live, and the holes are interior to the domain read after both -- so they are
   applied in one pass (I-P6, one snapshot, every deduction) for [filter_index]'s
   reason. *)
let filter_result t store =
  let moved = ref false in
  let live = live_positions t store in
  if live = [] then raise (Found (no_position_conflict t store));
  let vals = List.map (fun p -> t.values.(p)) live in
  (* Built at the first pruning that needs it, once for the pass ([dead_positions]). *)
  let alive = lazy (int_set live) in
  let a = List.fold_left Int.min (List.hd vals) vals in
  let b = List.fold_left Int.max (List.hd vals) vals in
  (* The index's hole facts, built at the first pruning that needs it, not on every pass
     (D-0155, M11-complexity-T8). Most passes prune nothing, and this list (one remover's
     reason per index hole, a [Later] materialised for each) was then built for nobody.
     Nothing in this pass writes the store before the first [justified] call, so the list
     is the one the eager [let] built.

     Since D-0214, not even then: the first pruning's FRAME is what the pass keeps, and
     the list is read from it when a reason is first asked for, then shared by every
     pruning of the pass, as the eager list was. [empty] is [false]: [bound_facts] states
     the index's two bounds whatever they are. Each pruning checks its OWN history, the
     one its entry sits on, which is above the first one's. *)
  let facts = ref None in
  let reason_of fr =
    let shared =
      match !facts with
      | Some l -> l
      | None ->
          let l = lazy (add_facts (bound_facts t fr) (index_hole_facts t fr)) in
          facts := Some l;
          l
    in
    Reason.Later
      {
        compute =
          (fun () ->
            Store.check_history fr.h;
            Lazy.force shared);
        empty = false;
      }
  in
  let justified fr ~concludes expl =
    let reason = reason_of fr in
    { Reason.reason; justification = Explanation.deferred (fun () -> expl); concludes }
  in
  (if a > View.lo store t.res then
     let h = View.hi store t.res in
     let fr = frame t store in
     let expl = push_lo_expl t fr ~live ~alive ~a in
     let concludes =
       Option.map (fun rn -> Reason.at_least ~name:rn ~decl:t.rdlo a) t.rname
     in
     match View.set_lo store t.res a (justified fr ~concludes expl) with
     | Store.Conflict _ ->
         raise (Found (conflict_of store (lo_push_conflict t store ~expl ~a ~h)))
     | Store.Changed ->
         Propagator.count_deduction ();
         moved := true
     | Store.Unchanged -> ());
  (if b < View.hi store t.res then
     let l = View.lo store t.res in
     let fr = frame t store in
     let expl = push_hi_expl t fr ~live ~alive ~b in
     let concludes =
       Option.map (fun rn -> Reason.at_most ~name:rn ~decl:t.rdhi b) t.rname
     in
     match View.set_hi store t.res b (justified fr ~concludes expl) with
     | Store.Conflict _ ->
         raise (Found (conflict_of store (hi_push_conflict t store ~expl ~b ~l)))
     | Store.Changed ->
         Propagator.count_deduction ();
         moved := true
     | Store.Unchanged -> ());
  (* Interior values no live position carries -- the half of DOMAIN consistency that
     [Bounds] would not do, and the reason D-0059 (which made the consistency tag
     checked) names [element] as a place the tag starts separating. Only reachable for a
     result with a variable behind it; a constant result is already decided by the two
     pushes above. *)
  (match t.rname with
  | None -> ()
  | Some _ -> (
      let d = View.domain store t.res in
      let carried = int_set vals in
      let lo = Domain.lo d and hi = Domain.hi d in
      let unsupported v = Domain.mem d v && not (Int_tbl.mem carried v) in
      if shares_index t then
        (* The result IS the index (one variable on both sides): a removal moves the index
           too, so each value's frame must be its own, and the values go one at a time. *)
        for v = lo + 1 to hi - 1 do
          if unsupported v then
            let fr = frame t store in
            let expl = hole_expl t fr ~live ~alive ~v in
            match View.remove store t.res v (justified fr ~concludes:None expl) with
            | Store.Conflict _ ->
                raise (Found (conflict_of store (hole_conflict t store ~expl ~v)))
            | Store.Changed ->
                Propagator.count_deduction ();
                moved := true
            | Store.Unchanged -> ()
        done
      else
        (* ONE store change for every unsupported interior value (D-0268): the values
           ascending, one reason (the pass's shared facts, which every per-value removal
           carried already), and a derivation per value, built when asked from the frame
           taken now plus the [pending] record (see [frame]). *)
        let buf = ref (Array.make 16 0) and n = ref 0 in
        for v = lo + 1 to hi - 1 do
          if unsupported v then (
            if !n = Array.length !buf then (
              let bigger = Array.make (2 * !n) 0 in
              Array.blit !buf 0 bigger 0 !n;
              buf := bigger);
            !buf.(!n) <- v;
            incr n)
        done;
        if !n > 0 then
          let vs = if !n = Array.length !buf then !buf else Array.sub !buf 0 !n in
          let fr = frame t store in
          let p_in w = w > lo && w < hi && unsupported w in
          let memo = ref None in
          let rec expl_of v =
            let tbl =
              match !memo with
              | Some tb -> tb
              | None ->
                  let tb = Int_tbl.create 16 in
                  memo := Some tb;
                  tb
            in
            match Int_tbl.find_opt tbl v with
            | Some e -> e
            | None ->
                let fv = { fr with pend = Some { p_upto = v; p_in; p_expl = expl_of } } in
                let inner = hole_expl t fv ~live ~alive ~v in
                let e = Explanation.deferred (fun () -> inner) in
                Int_tbl.replace tbl v e;
                e
          in
          match View.remove_interior store t.res vs (reason_of fr) ~justify:expl_of with
          | Store.Conflict _ -> assert false (* an interior removal leaves both bounds *)
          | Store.Changed ->
              for _ = 1 to !n do
                Propagator.count_deduction ()
              done;
              moved := true
          | Store.Unchanged -> ()));
  !moved

let pass t store =
  Propagator.count_pass ();
  let a = filter_index t store in
  let b = filter_result t store in
  a || b

let rec to_fixpoint t store = if pass t store then to_fixpoint t store

let propagate t store =
  try
    to_fixpoint t store;
    Propagator.Fixpoint
  with Found c -> Propagator.Conflict c
