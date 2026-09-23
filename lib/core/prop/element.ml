(* array_int_element(idx, as, c): the 1-based index [idx] selects [as[idx]], which is
   [c]. [as] is an array of CONSTANTS (docs/SPEC.md 2.1's M4 row; a var-array element is
   not in the subset).

   Consistency level: DOMAIN (docs/SPEC.md 3.2, docs/GLOSSARY.md). This is the first
   propagator in the tree that declares it, and D-0059 said in as many words that the
   [Bounds]/[Domain] tag "does no separating work on anything currently shipped" and
   would start doing so at an `all_different` or an `element`. It is not a claim made on
   the shape of the algorithm: for a constant array the two filtering rules below are
   the whole support condition, so the fixpoint IS the domain-consistent one, and the
   M2-T10 oracle (BAGUETTE_CONSISTENCY=1) holds this module to it.

     dom(idx) := { p in dom(idx) : as[p] in dom(c) }
     dom(c)   := { as[p]        : p in dom(idx)    }

   Each value of [idx] has exactly one support in [c] and each value of [c] is supported
   by whichever positions carry it, so neither rule can leave an unsupported value
   behind and no third rule is missing. That is why [element] over constants is the
   cheap global: the matching a general element needs is a lookup here.

   ---------------------------------------------------------------------------
   The index is a VIEW, and that is the whole of D-0058
   ---------------------------------------------------------------------------

   [pos] is [View.shift (View.of_var idx) (-1)]: the 0-based array offset, as a lens
   onto the 1-based FlatZinc variable. It is NOT an auxiliary variable with a
   channelling constraint, and D-0058 is the record of why that distinction is the
   point of this row rather than a detail of it. An auxiliary [p = idx - 1] has a domain
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
   (I-X5, [Encoding.add_constraint] refuses [Opb.Eq]), and the pair is exactly the split
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
   trick, for the same reason -- a [rup] would be cheaper and would make every [pol] here
   decorative.

   ONLY THE INDEX NEEDS THE DIRECT ENCODING, and only the index gets one. The result is
   spoken about in order literals throughout: [c >= w], [c <= w], and for a hole the
   two-literal clause [~c_ge_v \/ c_ge_(v+1)] that lib/core/prop/ne.ml already derives.
   That halves the direct-encoding width this row costs -- width-proportional, D-0028 --
   and it is what lets the result's own ladder rungs ([Encoding.consistency_id]) do the
   telescoping every derivation below leans on.

   NO [Explanation.Clause] ON THE MAIN PATHS, and that is load-bearing for the same
   reason it is in lib/core/prop/alldiff.ml: lib/core/search.ml's [rests_on_a_clause]
   routes a root conflict whose derivation rests on a clause the D-0022 way, so
   `conclusion UNSAT` would cite the empty clause and every [pol] here would be
   decorative (D-0057, D-0060, and D-0061 is the row that avoided it). The clause rows
   above are recovered by [pol], never by [rup]. The two places a clause does appear are
   named where they are used and are both about a hole SOMEONE ELSE punched.

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

   ---------------------------------------------------------------------------
   I-X10: this is a [Single_row] family, on the [Ne] precedent
   ---------------------------------------------------------------------------

   I-X10 holds by an enumeration over the propagator set, and the question it asks of a
   new member is whether its trace line is RUP once the facts on the line's own tail are
   assumed. It is, and the reason is the one [Ne] already relies on: "one model
   constraint" is a rule about the CONSTRAINT and not about the row count, and
   `array_int_element` is one constraint posted as 2n rows, the way `int_lin_ne` is one
   constraint posted as two big-M rows whose selector the checker's own unit propagation
   fills in.

     - an INDEX pruning: negate the claim, i.e. assume idx = p. The single row r_ge(p) or
       r_le(p) then forces a bound on the result that the result's own ladder refutes.
       One row and the ladder, and the ladder is the .opb's encoding of the variable
       itself rather than a second constraint (the distinction lib/core/prop/pb.ml's
       entry in test_trace.ml's table already draws).
     - a RESULT pruning: negate the claim and every position whose value disagrees is
       excluded by its own row; the index's ladder then has nothing left. Several rows,
       all of this constraint.

   MEASURED, not argued, for the second one: the result has no direct encoding at all, so
   [Trace.derive_ahead] does not fire for a result pruning, and all seven element models
   plus a scene built to defeat it -- an index HOLE punched by an `int_ne`, so the result
   pruning rests on something [Reason.t] has no fact for -- verify with nothing written
   ahead of their lines. The hole case works because the hole's OWN trace line is already
   on the page: [Trace.emit] writes oldest first, which is I-S4/D-0039's "RUP against the
   .opb plus earlier trace lines", the same support a settle line already leans on. It is
   not a second model constraint in I-X10's sense.

   The index side is not measured the same way and cannot easily be: [has_direct] is true
   for the index, because the derivations genuinely cite its direct ids, so
   [derive_ahead] writes a [pol] ahead of every index line whether or not one is needed.
   Its over-triggering is deliberate and its own comment says so.

   ---------------------------------------------------------------------------
   Snapshotting and I-X6
   ---------------------------------------------------------------------------

   Every derivation below is built from the domains as they stand at the moment of the
   pruning and is wrapped in [Explanation.deferred] only at the outermost push site, with
   the snapshot already taken. Nothing inside a thunk reads a live domain. What the
   thunks do read is [Encoding]'s constraint ids, which [start_proof] writes once before
   the first decision and never moves -- the same exemption alldiff.ml's header argues.
   The one lookup that must happen eagerly is [Store.remover]'s, hoisted to its call site
   for the reason lib/core/prop/linear.ml's [explain_cross_conflict] spells out. *)

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
   the same D-0010 requirement [Linear.make] and [Alldiff.make] state, and for the same
   reason: a derivation speaks in the DECLARED ladder's currency. *)
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
  let plo = List.fold_left Stdlib.min (List.hd ends) ends in
  let phi = List.fold_left Stdlib.max (List.hd ends) ends in
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
      let lo = Stdlib.min a b and hi = Stdlib.max a b in
      List.init (hi - lo + 1) (fun i -> lo + i)
  | _ ->
      invalid_arg "Element.declared_positions: the index must be a view onto a variable"

(* ------------------------------------------------------------------- explanations *)

let range a b = List.init (Stdlib.max 0 (b - a + 1)) (fun i -> a + i)
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
  Explanation.combine (cite row :: List.map (fun id -> cite id) halves) (Stdlib.max 1 h)

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

(* The line that took [w] out of the result, or [None] when nothing did.

   Read EAGERLY at the call site, never inside a thunk: which trail entry witnesses a
   hole can change or vanish on a backtrack between now and whenever the explanation is
   rendered, which is I-X6 and the trap lib/core/prop/linear.ml's
   [explain_cross_conflict] header describes at length.

   The entry this finds always punched a HOLE rather than moved a bound, and that is
   forced by the caller's guard rather than checked here: the caller has already
   established [lo(c) <= w <= hi(c)], and a bound move that removed [w] would have left
   [w] outside the current bounds, since bounds only tighten. *)
let hole_line t store w =
  match View.base_var t.res with
  | None -> None
  | Some rv ->
      Option.map (Store.explanation store)
        (Store.remover store ~before:(Store.trail_length store) ~var:rv w)

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
   refuse. *)
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
   consults the M2-T9 claim index and mints nothing. The cost is stated rather than
   hidden: a conflict whose derivation reaches one of these arms rests on a clause, so
   [Search.rests_on_a_clause] routes it the D-0022 way and this module's [pol] is
   decorative FOR THAT CONFLICT. It is not decorative for any conflict that does not --
   which is every conflict a model without a disequality on the index can reach. *)
let pos_gone t store p =
  let n = Array.length t.values in
  (* WHICH ARM is decided now, from the live domains; BUILDING it is deferred, and the
     split is not stylistic. The arm depends on the store and must be pinned at the
     moment of the pruning (I-X6). The construction depends on [Encoding]'s constraint
     ids, which do not exist at all until [Encoding.start_proof] runs -- a unit test that
     propagates without writing a proof is the ordinary case, and forcing the lookup
     eagerly would make it raise [need]'s diagnostic where nothing is wrong. *)
  let later f = Explanation.deferred f in
  if p < 0 || p >= n then (later (fun () -> excl_out t p), R_none)
  else
    let w = t.values.(p) in
    let rlo = View.lo store t.res and rhi = View.hi store t.res in
    if w > rhi then
      ( later (fun () -> excl_above t p ~bhi:rhi),
        if w > t.rdhi then R_none else R_res_hi rhi )
    else if w < rlo then
      ( later (fun () -> excl_below t p ~blo:rlo),
        if w < t.rdlo then R_none else R_res_lo rlo )
    else if not (View.mem store t.res w) then
      match hole_line t store w with
      | Some hole -> (later (fun () -> excl_hole t p ~hole), R_none)
      | None -> (Explanation.clause [ Lit.negate (Lit.eq t.iname (base_of t p)) ], R_none)
    else
      (* as[p] is still available, so p left dom(idx) for a reason of the index's own. *)
      let d = Store.get store t.ibase in
      let bp = base_of t p in
      let dlo = Domain.lo d and dhi = Domain.hi d in
      if bp < dlo then (later (fun () -> idx_excl_below t p ~blo:dlo), R_idx_lo dlo)
      else if bp > dhi then (later (fun () -> idx_excl_above t p ~bhi:dhi), R_idx_hi dhi)
      else (Explanation.clause [ Lit.negate (Lit.eq t.iname bp) ], R_none)

(* ---- shape 2: what the live positions force about the result ---- *)

(* [sum_{p live} idx_eq_p \/ <lits> >= 1]: the declared at-least-one line, narrowed by
   one [pos_gone] per dead position. Each cancels its own term and leaves the degree at
   1, exactly as alldiff.ml's [alo_window] does over a Hall interval. *)
let dead_positions t store ~live =
  List.filter_map
    (fun p -> if List.mem p live then None else Some (pos_gone t store p))
    t.decl_pos

let alo_of t ~dead =
  Explanation.deferred (fun () ->
      Explanation.combine
        (cite (need "at-least-one" (Encoding.at_least_one_id t.enc t.iname))
        :: List.map (fun (e, _) -> Explanation.term 1 e) dead)
        1)

let alo t store ~live = alo_of t ~dead:(dead_positions t store ~live)

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

let push_hi_expl t store ~live ~b =
  let dead = dead_positions t store ~live in
  Explanation.deferred (fun () ->
      Explanation.combine
        (Explanation.term 1 (alo_of t ~dead)
        :: List.map (fun p -> Explanation.term 1 (at_most_from t p ~b)) live)
        (List.length live))

let push_lo_expl t store ~live ~a =
  let dead = dead_positions t store ~live in
  Explanation.deferred (fun () ->
      Explanation.combine
        (Explanation.term 1 (alo_of t ~dead)
        :: List.map (fun p -> Explanation.term 1 (at_least_from t p ~a)) live)
        (List.length live))

(* [~c_ge_v \/ c_ge_(v+1)] -- "c <> v" -- for a value no live position carries. The two
   halves arrive with different coefficients ([na] positions below [v], [nb] above), so
   each is padded up to their maximum with its own literal axiom before the division:
   D-0009's weakening, used exactly as alldiff.ml's [pair_amo] uses it. *)
let hole_expl t store ~live ~v =
  let dead = dead_positions t store ~live in
  let below = List.filter (fun p -> t.values.(p) < v) live in
  let above = List.filter (fun p -> t.values.(p) > v) live in
  let na = List.length below and nb = List.length above in
  let m = Stdlib.max na nb in
  if m = 0 then
    invalid_arg "Element.hole_expl: no live position, which is a conflict and not a hole";
  let rn = match t.rname with Some x -> x | None -> assert false in
  let pad k lit = if k > 0 then [ Explanation.weaken [ (k, lit) ] ] else [] in
  Explanation.deferred (fun () ->
      Explanation.combine
        (Explanation.term 1 (alo_of t ~dead)
         :: List.map (fun p -> Explanation.term 1 (at_most_from t p ~b:(v - 1))) below
        @ List.map (fun p -> Explanation.term 1 (at_least_from t p ~a:(v + 1))) above
        @ pad (m - na) (Lit.negate (Lit.ge rn v))
        @ pad (m - nb) (Lit.ge rn (v + 1)))
        m)

(* ---------------------------------------------------------------------- reasons *)

(* The bounds this propagator reads. Both views, always, because both filtering rules
   read both -- and an over-stated fact is a weaker trace line, never an unsound one,
   where an under-stated one is I-P5. [Reason.lit_of_fact] drops whichever are still at
   their declared value. The index's HOLES are not here and cannot be -- [Reason.t] has no
   fact for one -- and that is the gap I-X10 has to be discharged around: the checker
   re-derives the hole itself, from this constraint's own rows or from the hole's own
   earlier trace line, rather than being told about it on this line's tail. See the I-X10
   section of the module header, where it is measured. *)
let bound_facts t store =
  let d = Store.get store t.ibase in
  let idx =
    [
      Reason.at_least ~name:t.iname ~decl:t.idlo (Domain.lo d);
      Reason.at_most ~name:t.iname ~decl:t.idhi (Domain.hi d);
    ]
  in
  match t.rname with
  | None -> idx
  | Some rn ->
      idx
      @ [
          Reason.at_least ~name:rn ~decl:t.rdlo (View.lo store t.res);
          Reason.at_most ~name:rn ~decl:t.rdhi (View.hi store t.res);
        ]

(* ------------------------------------------------------------------ hole facts

   M7-T13 / D-0075. [bound_facts] above says the index's HOLES "are not here and cannot
   be", and that the checker re-derives them "from this constraint's own rows or from the
   hole's own earlier trace line". The second half of that sentence is FALSE as stated,
   and `2012_tpp` is where it was caught. A hole's own trace line is a clause with its own
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
   same trade [bound_facts] makes. [None] from [Store.remover] is a declared hole, which
   `lib/` cannot produce (see [Store.remover]'s header and D-0072); citing nothing there
   is what trace.ml does and leaves the line exactly as strong as it was. *)
let add_facts acc fs =
  List.fold_left (fun acc f -> if List.mem f acc then acc else acc @ [ f ]) acc fs

let remover_facts store ~var v =
  match Store.remover store ~before:(Store.trail_length store) ~var v with
  | None -> []
  | Some e -> e.Store.reason

let holes_of d =
  List.filter (fun v -> not (Domain.mem d v)) (range (Domain.lo d + 1) (Domain.hi d - 1))

(* The facts behind the INDEX's interior holes: what a RESULT pruning read beyond bounds. *)
let index_hole_facts t store =
  let d = Store.get store t.ibase in
  List.fold_left
    (fun acc v -> add_facts acc (remover_facts store ~var:t.ibase v))
    [] (holes_of d)

(* The facts behind the RESULT's interior holes: what an INDEX pruning read beyond bounds.
   Over the result's BASE domain, so no view value has to be translated back -- the facts
   are the same either way and this needs no [View] inverse. *)
let result_hole_facts t store =
  match View.base_var t.res with
  | None -> []
  | Some rv ->
      let d = Store.get store rv in
      List.fold_left
        (fun acc v -> add_facts acc (remover_facts store ~var:rv v))
        [] (holes_of d)

(* D-0043's conclusion for a value removal, on the INDEX's base variable: a removal at a
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
exception Moved

let live_positions t store = List.filter (fun p -> View.mem store t.pos p) t.decl_pos

(* A bound the SEARCH established, cited by [Explanation.Defining] (D-0064,
   docs/DECISIONS.md D-0064; lib/core/explanation.ml's header, "[Defining], and why it
   is a SUMMAND"). M4-T3 branched before that constructor existed and stood in with
   [Explanation.term c (Explanation.clause [l])] -- the right arithmetic wearing the
   wrong label, per explanation.ml's own words -- which cancels the term but, because a
   [Clause] may be any width, is not an EXACT cancellation, and trips
   [Search.rests_on_a_clause] into routing every conflict that uses it the D-0022 way
   (`conclusion UNSAT` citing the empty clause, this module's own [pol] left decorative).
   [Explanation.defining] cites a UNIT line and is exact, so a root conflict built only
   from [Defining] summands closes on its own [pol].

   [established_at_root] mirrors lib/core/prop/alldiff.ml:179's function of the same
   name (that module is M4-T2's, not duplicated here as a shared function, since
   alldiff.ml is read-only to this task): the level the trail entry supporting a bound
   was pushed at, or 0 for a bound that has never moved. A bound the ROOT fixpoint set
   is a consequence of the model and stays true and citable at ANY search depth; one a
   DECISION set is not (D-0064's level rule) -- so, unlike the old blanket "only at
   [Store.level store] = 0", the check below is per LITERAL, not per conflict, and it
   fires above level 0 exactly when the specific bound cited happened to be a root one.
   Every call site below computes it EAGERLY, never inside an [Explanation.deferred]
   thunk: the support arrays this reads are live store state that a later backtrack can
   invalidate, the same reason alldiff.ml's [snap_of] snapshots [s_lo_root]/[s_hi_root]
   before wrapping anything in [deferred]. *)
let established_at_root store v ~lower =
  let sup = if lower then Store.lo_support store v else Store.hi_support store v in
  sup = Store.no_support || Store.level_of_index store sup = 0

(* One cancelling line per copy of each residue literal, when established at root;
   otherwise the group contributes nothing and the residue's term stays in the
   at-least-one row uncancelled -- not a loss, because only a ROOT conflict's derivation
   is cited as a contradiction, and under a decision D-0018's nogood closes the branch
   regardless. The values are read off the residues rather than from the store, so the
   line cancelled is the bound the exclusion actually read, and the multiplicity is the
   number of exclusions that read it. Called EAGERLY (see above), never inside the
   [Explanation.deferred] its caller wraps around the combine. *)
let residue_cancel t store ~dead =
  let rn = match t.rname with Some x -> x | None -> "" in
  let group sel lit_of var_opt ~lower =
    match List.filter_map (fun (_, r) -> sel r) dead with
    | [] -> []
    | vs -> (
        match var_opt with
        | None -> []
        | Some var ->
            if established_at_root store var ~lower then
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

(* Every declared position is impossible, so the at-least-one line has nothing left and
   the sum IS [0 >= 1] -- once the bound literals the exclusions carried are cancelled.

   [Reason.none], deliberately: lib/core/trace.ml's [conflict_line] writes a [rup] over
   the reason's facts, claiming those bounds are jointly impossible -- and for this
   conflict that claim is the counting argument itself, not reverse unit propagation,
   which 3.0.2 refuses. With no facts no line is written and what closes the root is this
   derivation, which really does derive the contradiction. alldiff.ml reaches the same
   arrangement through [Store.apply]'s [Failed] arm; saying it here is the same thing
   said where it can be read. *)
let no_position_conflict t store =
  let dead = dead_positions t store ~live:[] in
  let cancel = residue_cancel t store ~dead in
  Store.conflict store
    (Reason.because ~concludes:None Reason.none
       (Explanation.deferred (fun () ->
            Explanation.combine
              (cite (need "at-least-one" (Encoding.at_least_one_id t.enc t.iname))
               :: List.map (fun (e, _) -> Explanation.term 1 e) dead
              @ cancel)
              1)))

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
    && established_at_root store (Option.get (View.base_var t.res)) ~lower:false
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
    && established_at_root store (Option.get (View.base_var t.res)) ~lower:true
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
   same way -- omitted, not cited (D-0064's level rule), which is why the two halves are
   checked independently rather than gating the whole function on one level. *)
let hole_conflict t store ~expl ~v =
  let lo_ok, hi_ok =
    match t.rname with
    | None -> (false, false)
    | Some _ ->
        let rv = Option.get (View.base_var t.res) in
        ( v > t.rdlo && established_at_root store rv ~lower:true,
          v < t.rdhi && established_at_root store rv ~lower:false )
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

(* Rule 1: dom(idx) := { p : as[p] in dom(c) }. *)
let filter_index t store =
  let n = Array.length t.values in
  List.iter
    (fun p ->
      if View.mem store t.pos p then
        let dead = p < 0 || p >= n || not (View.mem store t.res t.values.(p)) in
        if dead then (
          (* The emptying removal is reported as the counting conflict rather than made,
             because the [Failed] arm would hand back this ONE position's derivation and
             that is not contradicting. *)
          if View.size store t.pos <= 1 then raise (Found (no_position_conflict t store));
          let d = Store.get store t.ibase in
          let bw = base_of t p in
          (* The residue is DISCARDED for a pruning, and that is the whole point of it
             being tracked separately: the derived row keeps its bound literal and is the
             globally valid "pruning disjoined with the bounds it read". Only a conflict
             has to cancel it. *)
          let expl, _ = pos_gone t store p in
          let j =
            Reason.because ~concludes:(removal_conclusion t d bw)
              (add_facts (bound_facts t store) (result_hole_facts t store))
              (Explanation.deferred (fun () -> expl))
          in
          match View.remove store t.pos p j with
          | Store.Conflict c -> raise (Found c)
          | Store.Changed -> raise Moved
          | Store.Unchanged -> ()))
    t.decl_pos

(* Rule 2: dom(c) := { as[p] : p in dom(idx) }. *)
let filter_result t store =
  let live = live_positions t store in
  if live = [] then raise (Found (no_position_conflict t store));
  let vals = List.map (fun p -> t.values.(p)) live in
  let a = List.fold_left Stdlib.min (List.hd vals) vals in
  let b = List.fold_left Stdlib.max (List.hd vals) vals in
  let facts = add_facts (bound_facts t store) (index_hole_facts t store) in
  let justified ~concludes expl =
    Reason.because ~concludes facts
      (Explanation.deferred (fun () -> expl))
  in
  (if a > View.lo store t.res then
     let h = View.hi store t.res in
     let expl = push_lo_expl t store ~live ~a in
     let concludes =
       Option.map (fun rn -> Reason.at_least ~name:rn ~decl:t.rdlo a) t.rname
     in
     match View.set_lo store t.res a (justified ~concludes expl) with
     | Store.Conflict _ ->
         raise (Found (conflict_of store (lo_push_conflict t store ~expl ~a ~h)))
     | Store.Changed -> raise Moved
     | Store.Unchanged -> ());
  (if b < View.hi store t.res then
     let l = View.lo store t.res in
     let expl = push_hi_expl t store ~live ~b in
     let concludes =
       Option.map (fun rn -> Reason.at_most ~name:rn ~decl:t.rdhi b) t.rname
     in
     match View.set_hi store t.res b (justified ~concludes expl) with
     | Store.Conflict _ ->
         raise (Found (conflict_of store (hi_push_conflict t store ~expl ~b ~l)))
     | Store.Changed -> raise Moved
     | Store.Unchanged -> ());
  (* Interior values no live position carries -- the half of DOMAIN consistency that
     [Bounds] would not do, and the reason D-0059 names [element] as a place the tag
     starts separating. Only reachable for a result with a variable behind it; a constant
     result is already decided by the two pushes above. *)
  match t.rname with
  | None -> ()
  | Some _ ->
      let d = View.domain store t.res in
      List.iter
        (fun v ->
          if Domain.mem d v && not (List.mem v vals) then
            let expl = hole_expl t store ~live ~v in
            match View.remove store t.res v (justified ~concludes:None expl) with
            | Store.Conflict _ ->
                raise (Found (conflict_of store (hole_conflict t store ~expl ~v)))
            | Store.Changed -> raise Moved
            | Store.Unchanged -> ())
        (range (Domain.lo d + 1) (Domain.hi d - 1))

let pass t store =
  filter_index t store;
  filter_result t store

let rec to_fixpoint t store =
  match pass t store with () -> () | exception Moved -> to_fixpoint t store

let propagate t store =
  try
    to_fixpoint t store;
    Propagator.Fixpoint
  with Found c -> Propagator.Conflict c
