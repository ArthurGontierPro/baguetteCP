(* Explanations: HOW THE CHECKER IS CONVINCED that a value could be removed -- the
   derivation, in a form the proof layer can render.

   This is the design centre of the project. Read docs/SPEC.md section 3.3 and
   docs/ARCHITECTURE.md section 4 before changing it.

   D-0003 ("what does higher-order explanation mean here?") is RESOLVED, by D-0026, and
   the resolution split this type's job in two rather than reshaping it. *Which facts*
   justify a pruning is now declarative data in lib/core/reason.ml; *how the checker is
   convinced* is this type, unchanged, and it is the project's (a)-claim: [Combine] with
   a divisor, [Weaken], [Model_row], and [Term (coeff, t)] recursing into another
   justification -- an explanation taking explanations as arguments. Nothing about that
   was flattened by D-0026 and nothing about it should be.

   What changed here in M2-T8 is what this type is *not* asked to do any more. It no
   longer doubles as the reason: no propagator projects an [Explanation.t] to get the
   bound facts a trace line negates, and [Store.entry] no longer carries a second,
   closure-valued reason channel beside it. The one new function is [owners], which
   exists so the two halves can be *checked* against each other instead of kept in
   agreement by a comment.

   Do not add a constructor without a decision record -- D-0026 authorises the split, not
   a new constructor -- and when one is added, extend [force], [lits] and [to_string]
   rather than adding a catch-all case: the exhaustiveness warning is what will find
   every site that needs updating.

   -------------------------------------------------------------------------------
   M8-bits-encoding-T2 / docs/DECISIONS.md D-0132: [Linear_term], ONE summand for a
   term of a linear row, carrying the term's SNAPSHOT rather than its rendering
   -------------------------------------------------------------------------------

   D-0132 section 2.4 is this constructor's decision record (D-0130 section 8 designed a
   [Weaken_declared] for the declared and assumed cases only; this is that constructor
   grown to cover the cited case too, and the reason is stated there). What a term of
   [Linear]'s row contributes to the D-0013 derivation was, until T2, decided by [Linear]
   at construction: a [Weaken] of the full declared-range axiom chain when the bound it
   read was the declared one or rested on a decision, one [Term] per cited explanation
   otherwise. Both renderings spell the ORDER encoding -- the chain is Theta(w) literals
   named `x_ge_v`, and a [Term] expects the cited line to be D-0013's full-range row --
   and a variable on the BITS encoding has neither: no `x_ge_v` in the .opb, and a cited
   line that is a clause over atoms. So a term is now carried as what [Linear] READ --
   its coefficient, its name, its declared bounds, the bound value at the snapshot and
   the explanations that bound rests on -- and the TWO renderings live in
   lib/core/justify.ml: the order arm renders a [Linear_term] exactly as it rendered the
   [Weaken]/[Term] it replaces (the `pol` text at `--bits-above none` is byte-identical,
   the determinism gate holds it), and the bits arm cites the term's bridge
   ([Encoding.ensure_atom]) or bound line ([Encoding.bound_lines]) once, whatever the
   width. The substrate contract of D-0130 section 3.1 holds as a type: no field here
   names a representation, and nothing in lib/core/prop/ can spell a bit.

   [Weaken], [Term] and [Defining] stay, with their other producers: the enumerating
   families (alldiff, gcc, element, cumulative), which are order-only by D-0130
   section 3.4, and [Pb_analysis]'s reductions.

   -------------------------------------------------------------------------------
   M8-bits-encoding-T3 / docs/DECISIONS.md D-0134: [Resolve], the sum of saturated
   derivations -- resolution on a choice encoding's selectors, in one `pol`
   -------------------------------------------------------------------------------

   D-0134 section 2.2 is this constructor's decision record. A family whose order
   encoding is one clause row per VALUE (maxmin, D-0095) cannot post those rows over a
   bits variable (its atoms do not exist when the .opb is closed, D-0130 section 3.4),
   so over bits it posts one big-M SELECTOR row per operand and a clause over the
   selectors, and a pruning that was one row restated becomes a derivation: each
   selector row plus the bounds it reads, saturated to a clause on its selector, the
   clauses summed with the selector clause, saturated. [Resolve] is that shape as data:
   a list of derivations to saturate and sum. It is the first constructor whose parts'
   [Linear_term]s include the CLAIM variable, carrying the negation of the claim as the
   bound assumed, because the claim is cancelled inside every part and not left over as
   the one term a [Combine] divides and then closes with the pruned variable's atom.

   [Deferred] exists because most prunings are never asked for a reason. Computing a full
   explanation eagerly for every pruning is the standard way to make a proof-logging
   solver an order of magnitude slower than its unlogged sibling. Forcing memoises: a
   reason can be demanded more than once during conflict analysis.

   -------------------------------------------------------------------------------
   M11-complexity-T13 / docs/DECISIONS.md D-0168: releasing a written thunk
   -------------------------------------------------------------------------------

   D-0166 section 5 option B, decided by D-0167 item 6. Once [Justify.emit] has written a
   thunk's derivation, the thunk records the line ([line]: the id, the level, and what
   [Justify] needs to tell whether the line is still on the page) and drops its tree; the
   memo cells that emission made for nodes the closure BUILT are taken out with it. Until
   then the tree stayed reachable from [forced], from the closure [force] put in place of
   the original, and from the memo's keys, for as long as the trail entry stood: 1.16 GB
   of all_different derivations on 2011_black-hole_9 at node 40 (D-0166 section 4).

   Why every proof byte is the same, reader by reader:

   - A later [emit] of the thunk. The memo answered it (or its forced head) with the id
     for as long as no wipe had reached the level it was written at; the line answers
     under exactly that condition ([Justify.live_line]).
   - [emit] after that level was wiped. The same physical tree used to be written again,
     every cell of it gone with the wipe. Now the closure is forced again and that tree
     is written. It is the same derivation because a thunk closes over a SNAPSHOT (I-X6);
     under BAGUETTE_DEBUG every release forces the closure a second time and refuses to
     go on unless [same_derivation] holds, and every later forcing is compared with the
     original, which a released thunk then keeps. The memo answers the two trees alike
     because a node of the tree either is CAPTURED -- a value the closure did not build,
     like another entry's eager explanation, held physically by both forcings -- and
     keeps its cell, so it is found as before; or is BUILT, new at every forcing and
     reachable from nothing but its tree, so that no lookup can present it again.
   - Which is which: every node is built by the smart constructors, and while a thunk is
     forced they record what they build and look up every operand they are handed among
     it (the FRAME, below the type). A forcing that was handed nothing it had not built
     captured nothing: its cells all go, and no second forcing is paid. One that may have
     captured ([captures]) is forced a second time at its release, and a node the two
     forcings hold physically in common keeps its cell; if the two differ, the thunk is
     not released at all and keeps its tree and its cells, as before T13.
   - BAGUETTE_DEBUG checks the two halves of that split: a hit, inside a thunk's
     emission, on a cell the emission did not make must be a captured node (the second
     forcing holds it), and a cell taken out must never be asked for again (the ghost
     table in [Justify]); and a forcing that recorded no capture must share no node with
     its second forcing.
   - [lits] (the D-0026 agreement walk, under BAGUETTE_DEBUG), [Pb_analysis.cited_ids],
     and the readers that match on a forced head: [force] forces a released thunk again,
     without memoising, and they read the same derivation.

   The header of [thunk] below used to say a thunk is the ONLY shared node of a
   derivation. That is not what the code does, and T13 measured it: on
   test/models/alldiff_regin_hole_element_unsat.fzn a conflict's derivation holds an
   eager [Combine] the trace had already written as another entry's line, and 39 cells of
   the suite are captured nodes first written inside another thunk's emission
   (element_foreign_hole_*, element_shared_result_root_unsat). The release does not rest
   on that sentence; it rests on the captured/built split, which the frame records rather
   than assumes. What it does rest on: a closure hands nobody a node it built (a cache
   that kept one and handed it to a later forcing would make that node captured there and
   built here, and the ghost check is what would see it), and every node is built through
   the smart constructors (a direct [Term (c, e)] in a closure would hide its operand from
   the frame; nothing in lib/ builds one).

   -------------------------------------------------------------------------------
   M1-T12 / docs/DECISIONS.md D-0013: [Model_row], [Combine], [Weaken]
   -------------------------------------------------------------------------------

   D-0013 verified, against the checker, the actual derivation a bounds conflict at
   the root needs: weaken every *other* variable out of the model row with literal
   axioms (sound per D-0009 -- an axiom can never assert a bound, but it *can* weaken
   one away), or, where that variable sits at a bound some earlier step already
   derived, cite that derivation's id instead; then divide by the pushed variable's
   own coefficient. [Trivial]/[Linear]/[Cut] cannot say this:

     - [Linear] carries literals but no constraint id, so it cannot cite "the id that
       already established this bound" (D-0009).
     - [Cut] has two multipliers and no divisor, so it cannot express the division
       D-0010/D-0011 left out.
     - Nothing distinguishes "still at the declared bound, weaken it away" from
       "sitting at a bound some earlier step derived, cite that id" -- D-0013's whole
       point is that these are different operations with a different source.

   [Combine (summands, divisor)] is one [pol] step: every summand added, then (unless
   [divisor = 1]) divided. A [summand] is either [Term (c, e)] -- recursively emit
   [e], the way [Cut] already does, and cite its id scaled by [c] -- or [Weaken lits]
   -- a sum of individually-scaled *literal axioms*, which cancel a term whose
   variable is still sitting at its declared bound. [Weaken] is not a [t]: it is not
   a value anyone can point at and say "this holds", only a piece of arithmetic valid
   solely inside a [Combine]'s sum, which is exactly the D-0009 distinction made
   structural instead of a convention someone has to remember.

   [Model_row] exists because [Trivial] was not enough once a [Combine] cites an
   explanation another propagator *instance* built: [Trivial] meant "whatever
   [ctx.model_id] currently points at" (lib/core/justify.ml), a single ambient
   pointer good for exactly one row at a time. D-0011 already found this: two
   propagator instances justify against two different rows, and nothing on the trail
   says which one produced a given pruning. A [Combine] can legitimately hold, in one
   tree, an explanation this instance built (whose own base is its own row) *and* a
   cited explanation another instance built earlier (whose base is *that* instance's
   row) -- two different rows, resolved simultaneously, which one mutable ambient
   pointer cannot do. [Model_row id] names the row explicitly and renders to [id]
   directly, no lookup, so each instance's own base survives being embedded inside
   someone else's derivation.

   -------------------------------------------------------------------------------
   M1-T31 / M1-T50: [Trivial] is gone, and [Decision] is not its replacement
   -------------------------------------------------------------------------------

   [Trivial] had exactly two producers left: [Linear.make] without a [row_id], and
   search.ml's two decision pushes. The first is now impossible ([~row_id] is
   required), and the second was never what [Trivial] said. "The model constraint
   itself justifies this" is *false* of a decision: a decision is an assumption the
   search made, not a consequence of any row. Calling it [Trivial] is what let
   [Justify.emit] answer [ctx.model_id ()] and emit `pol <own row> <own row> +` --
   M1-T50, a proof step that does not say what the explanation says.

   So the constructor now carries what a decision actually is: [Decision lit], the
   order literal the search assumed. Two consequences follow, and both are the point:

   - **It has no constraint id, and never will.** Nothing in the proof establishes a
     decision. D-0009 is why: a [pol] cannot assert a literal (a bare literal in one
     is the trivial axiom [lit >= 0]) and a [rup] cannot derive one that is not a
     consequence. The decisions enter the proof in exactly one place, negated, in the
     branch's nogood -- D-0018 and lib/core/trace.ml's header say so already. A
     [Decision] is therefore not citable, and [term]/[cut] below refuse to build a
     summand out of one rather than leaving [Justify] to discover it.
   - **It is not silent.** [Trivial]'s [lits] was [[]], so a reason set that rested on
     a decision named nothing at all -- the omission D-0035 says becomes unsoundness
     once M2-T3 builds learned clauses from it. [Decision lit]'s [lits] is [[lit]].

   With [Trivial] gone, [Justify.ctx] has no [model_id] field at all: the ambient row
   is not "discouraged", it is unrepresentable. Every row a derivation names, it names
   with [Model_row].

   -------------------------------------------------------------------------------
   M4-T7 / docs/DECISIONS.md D-0009: [Defining], and why it is a SUMMAND
   -------------------------------------------------------------------------------

   D-0009's sentence is "a bound fact in a [pol] needs a constraint id, not a literal",
   and until now this type could say only the first half of it. [Weaken lits] puts a
   bare literal into a [pol] as the TRIVIAL AXIOM [l >= 0] -- which asserts nothing and,
   arithmetically, cancels the term at the cost of one unit of degree per copy.
   [Defining (c, l)] is the other half: [c] copies of the id of the line that
   ESTABLISHES [l], which cancels the same term and KEEPS the degree. The two are the
   same shape of arithmetic with the two different sources D-0013 says are different
   operations, and they now sit next to each other instead of one of them being a gap.

   It is a [summand] and not a [t], for exactly the reason [Weaken] is: it is a piece of
   arithmetic valid only inside a [Combine]'s sum, not a value anyone can point at and
   say "this holds". Nobody may [emit] it on its own, no [Cut] may take it as an
   operand, and conflict analysis never has to decide what a bare one means.

   THE LINE IT CITES IS ALWAYS A UNIT, by construction: [Justify] resolves it through
   [defining_lit], which is [defining_line] on the one-literal clause, and states [l]
   outright as a unit if no line has. That is what makes it sound to cancel with, and it
   is also the whole difference from the [Explanation.clause [lit]] stand-in M4-T1 used
   (D-0061). A [Clause] summand may cite a clause of any width, whose cancellation does
   NOT behave, which is why lib/core/search.ml's [rests_on_a_clause] conservatively
   refuses to let a root conflict rest on one; a [Defining] cites a unit, the
   cancellation is exact, and the row really does come out contradicting. The stand-in
   was the right arithmetic wearing the wrong label, and the label is what the search
   reads.

   WHO MAY BUILD ONE. A caller must know that [l] is a consequence of the MODEL, not of
   a decision -- a unit line for a decision-established bound would be a false claim and
   the checker would refuse it (rightly). lib/core/prop/alldiff.ml's test is the level at
   which the bound was established ([Store.lo_support] / [Store.level_of_index]), not the
   level the solver is at now, which is the difference between "sound only at level 0"
   and "sound for anything the root fixpoint established, at any level". *)

module Lit = Baguette_proof.Lit

type t =
  | Decision of Lit.t
    (* An assumption the search made: [lit] holds *because we said so*, on this
       branch only. Nothing derives it, so it has no constraint id and can never be
       a [pol] operand -- see the module header. *)
  | Clause of Lit.t list (* These literals together imply the pruning. Renders to rup. *)
  | Linear of (int * Lit.t) list * int
    (* sum a_i l_i >= b. Renders to pol over the model constraint. *)
  | Cut of t * t * int * int
    (* Linear combination: c1 * e1 + c2 * e2, the cutting-planes workhorse. Kept for
       existing single-row uses; D-0013's cross-row, divided combination is
       [Combine], below -- see the module header. *)
  | Model_row of int
    (* The id (a Baguette_proof.Writer.cid) of a model constraint already loaded by
       the checker's [f] rule, named explicitly rather than resolved through
       whatever [ctx.model_id] happens to point at right now. See the module
       header. *)
  | Combine of summand list * int
    (* sum of summands, then divide by the int (>= 1; 1 means "do not divide" --
       Justify skips emitting a division step rather than a no-op "1 d"). One
       [Combine] is one [pol] step (D-0013). *)
  | Resolve of t list
    (* M8-bits-encoding-T3, D-0134 section 2.2: the SUM of the listed derivations, each
       first saturated to the clause it derives (a [Combine] is summed, divided and
       saturated; a [Model_row] is cited as it stands), saturated again -- resolution on
       the literals that cancel between them, as ONE `pol` step. The literals that
       cancel are a choice encoding's selectors: maxmin's `b_i -> m <= x_i` rows summed
       with `\/ b_i` (and, by the same shape, int_lin_ne's A/B pair on `_neN`). The
       clause it derives is the union of its parts' literals less the cancelled pairs,
       and every part's [Linear_term] is read for that clause -- including the one that
       carries the NEGATION of the claim as the bound it assumed (section 2.3): no atom
       is added for the claim at the end, unlike a [Combine]'s bits rendering. Rendered
       by the bits arm ([Justify.emit_bits_pruning]) as an entry's trace line; a bare
       [Justify.emit] meets one only as a CITATION from an order-arm derivation and
       answers the line stating the clause it derives (D-0134 section 5). *)
  | Deferred of thunk
(* Computed only if actually needed. *)

and summand =
  | Term of int * t
    (* coeff * (recursively emit this explanation and cite its resulting id). *)
  | Weaken of (int * Lit.t) list
    (* sum of coeff_i * axiom(lit_i): weakens a variable's contribution out of the
       row it is added to. See the module header -- never meaningful outside a
       [Combine]'s summand list. *)
  | Defining of int * Lit.t
    (* coeff * the id of the line that ESTABLISHES this literal -- D-0009's missing
       half, resolved by [Justify.defining_lit] and always a UNIT line. Cancels the
       same term [Weaken] would and keeps the degree. Like [Weaken], it is not a [t]:
       see the module header. *)
  | Linear_term of linear_term
(* One term of [Linear]'s row, as the snapshot it took of it (M8-bits-encoding-T2,
   D-0132 section 2.4 -- the module header says why). Like [Weaken] and [Defining] it is
   not a [t]; it is rendered only inside a [Combine]. *)

and linear_term = {
  lt_coeff : int; (* the row's own coefficient on this variable; never 0 *)
  lt_name : string; (* the FlatZinc identifier, frozen (a reason must be spellable) *)
  lt_decl_lo : int;
  lt_decl_hi : int;
  lt_value : int;
      (* the bound the row read at the snapshot: lo for [lt_coeff >= 0], hi otherwise
         (D-0013's case split, [Reason.bound_for_coeff]) *)
  lt_cited : t list;
      (* the derivations that bound rests on -- the entry that moved it and any hole its
         settle walked over (M1-T44) -- or [] when it is the declared bound or rests on a
         decision (I-X9's exception: weakened over its declared range, the trace line
         carries the claim) *)
}

and thunk = {
  mutable forced : t option;
  compute : unit -> t;
      (* the ORIGINAL closure, never replaced: a released thunk is forced again through
         it (M11-complexity-T13, D-0168) *)
  mutable mark : int;
  mutable line : line;
  mutable captures : bool;
      (* the last forcing's tree holds a node the closure did not build ([citable] below):
         [Justify] then tells built nodes from captured ones by forcing it again before it
         releases it (M11-complexity-T13, D-0168) *)
}
(* [mark]: the walk that last visited this thunk ([lits] below). A thunk is the shared
   node of a derivation that matters -- a trail entry's explanation is one thunk cited by
   every later derivation that rests on it (an eager explanation can be shared too, see
   "releasing a written thunk" above) -- so marking thunks is what makes a walk linear in
   the DAG rather than exponential in its depth of sharing. Found on 2010_depot_placement
   under BAGUETTE_DEBUG, where [Store.agreement_holds] walks every pruning's derivation:
   a 60 s run was still walking after 22 h, all of it in [lits].

   [line]: the line [Justify.emit] wrote for this thunk, once it has written one, and
   then [forced] is [None] for good: the thunk is RELEASED (see the section on releasing
   below). *)

(* The line a released thunk's derivation was written as: its constraint id, the
   writer's level when it was written, and what [Justify] needs to tell whether that line
   is still on the page ([epoch], [owner]: its own wipe count and its own identity, so a
   line written through one [Justify.ctx] is never cited by another). This module only
   stores it; [Justify] alone writes and reads it. *)
and line = No_line | Line of { cid : int; level : int; epoch : int; owner : int }

type expl = t

(* ------------------------------------------------- what a forcing builds (T13)

   M11-complexity-T13 (D-0168). While a thunk is forced, a FRAME records the last
   [ring_size] nodes the smart constructors below built ([note]), and every operand a
   constructor is handed ([citable]: a [Term]'s, a [Cut]'s, a [Resolve] part, a
   [Linear_term]'s cited explanation) is looked up among them by identity. An operand that
   is a memoisable node ([Clause], [Linear], [Cut], [Combine], [Resolve]) and is not found
   is one the closure did not build in this forcing -- CAPTURED, or built so long before
   that it left the ring -- and the frame says so. A thunk whose tree may hold a captured
   node is released only after a second forcing has told the two kinds apart (see
   [Justify.emit_thunk]); one whose tree holds none is released without it, which is what
   keeps the release free: a second forcing of a cumulative or all_different closure is as
   dear as the first (D-0168 measured +5 % to +37 % instructions with it on every
   release). The ring is scanned newest first, and a closure builds an operand just
   before it wraps it, so the lookup is a few comparisons. It is exact in one direction
   only, which is the one that matters: a node found in the ring was built in this
   forcing; a node not found is treated as captured. Every [t] is built through these
   constructors in lib/ (a direct [Term (c, e)] would bypass the check; nothing in lib/
   builds one, and the guard [citable] already makes the constructors the only door, for
   M1-T50's sake). *)
let ring_size = 256

type frame = {
  ring : t array;
  mutable pos : int;
  mutable n : int;
  mutable captured : bool;
}

let frames : frame array ref = ref [||]
let depth = ref 0

let open_frame () =
  if !depth = Array.length !frames then
    frames :=
      Array.append !frames
        (Array.init (Stdlib.max 4 !depth) (fun _ ->
             {
               ring = Array.make ring_size (Model_row 0);
               pos = 0;
               n = 0;
               captured = false;
             }));
  let f = !frames.(!depth) in
  f.pos <- 0;
  f.n <- 0;
  f.captured <- false;
  incr depth;
  f

(* Close the innermost frame and drop what its ring holds, so that a frame kept for reuse
   does not keep the last tree it saw alive. *)
let close_frame f =
  decr depth;
  Array.fill f.ring 0 f.n (Model_row 0)

let note e =
  if !depth > 0 then (
    let f = !frames.(!depth - 1) in
    f.ring.(f.pos) <- e;
    f.pos <- (f.pos + 1) land (ring_size - 1);
    if f.n < ring_size then f.n <- f.n + 1);
  e

let built_here f e =
  let rec go k i =
    k < f.n && (f.ring.(i) == e || go (k + 1) ((i - 1) land (ring_size - 1)))
  in
  go 0 ((f.pos - 1) land (ring_size - 1))

(* An operand handed to a constructor inside a forcing. *)
let operand e =
  if !depth > 0 then
    match e with
    | Deferred _ | Model_row _ | Decision _ -> ()
    | Clause _ | Linear _ | Cut _ | Combine _ | Resolve _ ->
        let f = !frames.(!depth - 1) in
        if (not f.captured) && not (built_here f e) then f.captured <- true

let decision lit = Decision lit
let clause lits = note (Clause lits)
let linear terms rhs = note (Linear (terms, rhs))
let model_row id = Model_row id
let weaken lits = Weaken lits

(* [defining c l]: cite, [c] times, the line that establishes [l]. The coefficient is
   checked here rather than inside [Justify] so that a caller building nonsense hears
   about it where it built it -- the same bargain [combine] makes. *)
let defining coeff lit =
  if coeff < 1 then invalid_arg "Explanation.defining: coefficient must be >= 1";
  Defining (coeff, lit)

(* The guard that keeps M1-T50 from coming back by a different route.

   A [Cut] operand and a [Combine]'s [Term] are both "emit this explanation and cite
   the id it produced" (lib/core/justify.ml's [emit_cut] and [emit_summand]). A
   [Decision] has no id to cite -- it is an assumption, not a derivation -- so there
   is no id for either of them to name, and the old code's answer was to fall through
   to whatever row was ambient. This refuses at the point the mistake is made, not
   several layers down inside [Justify] where the cited value is no longer in view.

   The caller's correct move is the one lib/core/prop/linear.ml makes: a term whose
   bound rests on a decision is *weakened* out of the row with declared-width axioms
   (D-0009 -- an axiom cannot assert a bound but it can weaken one away), and the
   decision's literal is carried by the D-0018 trace line instead. *)
let citable what e =
  match e with
  | Decision l ->
      invalid_arg
        (Printf.sprintf
           "Explanation.%s: a decision (%s) has no constraint id and cannot be cited. \
            Weaken the term out of the row instead -- see explanation.ml's header."
           what (Lit.to_string l))
  | e ->
      operand e;
      e

let cut e1 e2 c1 c2 = note (Cut (citable "cut" e1, citable "cut" e2, c1, c2))
let term coeff e = Term (coeff, citable "term" e)

(* [resolve parts]: the parts are cited (summed) and so cannot be decisions; two is the
   least that can resolve on anything (D-0134 section 2.2). *)
let resolve parts =
  (match parts with
  | [] | [ _ ] -> invalid_arg "Explanation.resolve: at least two derivations to resolve"
  | _ -> ());
  note (Resolve (List.map (citable "resolve") parts))

(* [Linear_term] and its readings (M8-bits-encoding-T2). The term is DECLARED when the
   bound it read is the declared one in its own direction, and then has no literal:
   [Reason.lit_of_fact]'s rule, restated here because this module cannot see [Reason]
   (reason.ml depends on this one). *)
let linear_term ~coeff ~name ~decl_lo ~decl_hi ~value cited =
  if coeff = 0 then
    invalid_arg "Explanation.linear_term: a zero coefficient is not a term";
  Linear_term
    {
      lt_coeff = coeff;
      lt_name = name;
      lt_decl_lo = decl_lo;
      lt_decl_hi = decl_hi;
      lt_value = value;
      lt_cited = List.map (citable "linear_term") cited;
    }

let lt_declared r =
  if r.lt_coeff >= 0 then r.lt_value <= r.lt_decl_lo else r.lt_value >= r.lt_decl_hi

(* The bound fact as a literal: [x >= value] for a positive coefficient, [x <= value]
   for a negative one; [None] at the declared bound. *)
let lt_lit r =
  if lt_declared r then None
  else if r.lt_coeff >= 0 then Some (Lit.ge r.lt_name r.lt_value)
  else Some (Lit.le r.lt_name r.lt_value)

let lt_width r = r.lt_decl_hi - r.lt_decl_lo

(* The literals of D-0013's declared-range weakening of this term, in the order
   [Order_reason.weaken_declared] lists them: the ORDER arm's rendering of a term whose
   bound is not cited (declared, or resting on a decision), kept here so [lits] can say
   what that rendering names without calling into prop/. Empty for a fixed variable. *)
let lt_axiom_lits r =
  let width = lt_width r in
  if width <= 0 then []
  else if r.lt_coeff > 0 then
    List.init width (fun i -> Lit.ge r.lt_name (r.lt_decl_lo + 1 + i))
  else List.init width (fun i -> Lit.le r.lt_name (r.lt_decl_lo + i))

let combine summands divisor =
  if divisor < 1 then invalid_arg "Explanation.combine: divisor must be >= 1";
  (match summands with
  | [] -> invalid_arg "Explanation.combine: summands must be non-empty"
  | _ -> ());
  note (Combine (summands, divisor))

let deferred compute =
  Deferred { forced = None; compute; mark = 0; line = No_line; captures = false }

(* One fresh mark per walk; a thunk's [mark] equals it iff this walk has seen it. *)
let marks = ref 0

let fresh_mark () =
  incr marks;
  !marks

(* How many times a RELEASED thunk was forced again (M11-complexity-T13), for
   [BAGUETTE_MEMO_STATS]: [reforced_emit] counts the forcings [Justify] made to write the
   derivation again after its line was wiped, [reforced] every one. *)
let reforced = ref 0
let reforced_emit = ref 0
let released = ref 0

(* [same_derivation a b]: [a] and [b] are the same derivation -- the question
   [Justify] asks of a thunk's tree and a second forcing of it before it releases the
   thunk, and [force] asks under BAGUETTE_DEBUG of every forcing after. A thunk is compared
   by identity, never descended into: a cited thunk is a shared node, and the second
   forcing must cite the same one. Everything else is compared by structure, and a node
   the two trees hold PHYSICALLY in common (a value the closure captured rather than
   built) is not descended into either: it is pushed on [captured]. *)
let same_derivation ?(captured = ref []) a b =
  let rec go a b =
    if a == b then (
      (* a [Model_row] or a [Decision] has no memo cell, and is no capture that matters *)
      (match a with
      | Deferred _ | Model_row _ | Decision _ -> ()
      | Clause _ | Linear _ | Cut _ | Combine _ | Resolve _ -> captured := a :: !captured);
      true)
    else
      match (a, b) with
      | Deferred x, Deferred y -> x == y
      | Decision l, Decision m -> Lit.equal l m
      | Clause ls, Clause ms -> List.equal Lit.equal ls ms
      | Linear (ts, r), Linear (us, s) ->
          r = s && List.equal (fun (c, l) (d, m) -> c = d && Lit.equal l m) ts us
      | Cut (a1, a2, c1, c2), Cut (b1, b2, d1, d2) ->
          c1 = d1 && c2 = d2 && go a1 b1 && go a2 b2
      | Model_row i, Model_row j -> i = j
      | Combine (ss, d), Combine (ts, e) -> d = e && List.equal summand ss ts
      | Resolve ps, Resolve qs -> List.equal go ps qs
      | _ -> false
  and summand s t =
    match (s, t) with
    | Term (c, a), Term (d, b) -> c = d && go a b
    | Weaken ls, Weaken ms ->
        List.equal (fun (c, l) (d, m) -> c = d && Lit.equal l m) ls ms
    | Defining (c, l), Defining (d, m) -> c = d && Lit.equal l m
    | Linear_term r, Linear_term q ->
        r.lt_coeff = q.lt_coeff
        && String.equal r.lt_name q.lt_name
        && r.lt_decl_lo = q.lt_decl_lo && r.lt_decl_hi = q.lt_decl_hi
        && r.lt_value = q.lt_value
        && List.equal go r.lt_cited q.lt_cited
    | _ -> false
  in
  go a b

(* Every node of the trees under [roots], thunks excepted and not descended into: what a
   captured value holds that the memo could have a cell for. *)
let nodes_under roots =
  let acc = ref [] in
  let rec go e =
    match e with
    | Deferred _ | Decision _ | Model_row _ -> ()
    | Clause _ | Linear _ -> acc := e :: !acc
    | Cut (a, b, _, _) ->
        acc := e :: !acc;
        go a;
        go b
    | Combine (ss, _) ->
        acc := e :: !acc;
        List.iter summand ss
    | Resolve ps ->
        acc := e :: !acc;
        List.iter go ps
  and summand = function
    | Term (_, e) -> go e
    | Linear_term r -> List.iter go r.lt_cited
    | Weaken _ | Defining _ -> ()
  in
  List.iter go roots;
  !acc

(* Force to a non-deferred head. Nested [Deferred] is allowed: a thunk may return another
   thunk, and memoisation records the fully forced result at each level.

   Until M11-complexity-T13 the closure was replaced, once forced, by one returning the
   result, so that what it captured became collectable. It is kept now: a RELEASED thunk
   (one whose line [Justify] has written, [line <> No_line]) holds no tree, and a later
   read forces it again through the closure, without memoising, so that the tree is
   collectable again as soon as that reader is done with it. The closure is the snapshot
   I-X6 says it closes over, and D-0164 measured what the closures hold on
   2011_black-hole_9 at node 40: about 15 MB.

   Under BAGUETTE_DEBUG a released thunk keeps its original tree ([release]), and every
   forcing again is compared with it ([same_derivation]): the measurement of the claim
   the release rests on. The tree returned is the new one in both modes, so a debug run
   presents the memo the same nodes a normal run does. *)
let rec force = function
  | Deferred th -> (
      match th.line with
      | No_line -> (
          match th.forced with
          | Some e -> e
          | None ->
              let e = compute th in
              th.forced <- Some e;
              e)
      | Line { cid; _ } ->
          incr reforced;
          let e = compute th in
          (match th.forced with
          | Some original when not (same_derivation original e) ->
              failwith
                (Printf.sprintf
                   "invariant violated: I-X6 (M11-complexity-T13): the released thunk of \
                    line %d, forced again, is not the derivation it was written from"
                   cid)
          | _ -> ());
          e)
  | e -> e

(* Force [th]'s closure once more, outside the memoisation and the counts: what a re-forcing
   would return. For [Justify]'s check before it releases. *)
and reforce th = compute th

(* Run [th]'s closure inside a frame and force what it returns. [captures] is set when the
   tree may hold a node the closure did not build: an operand the frame did not see built,
   or a root it did not see built (a closure returning a captured value, or another thunk,
   whose tree is that thunk's). *)
and compute th =
  let f = open_frame () in
  let v =
    match th.compute () with
    | v -> v
    | exception ex ->
        close_frame f;
        raise ex
  in
  let root_built =
    match v with
    | Deferred _ -> false
    | Model_row _ | Decision _ -> true
    | Clause _ | Linear _ | Cut _ | Combine _ | Resolve _ -> built_here f v
  in
  th.captures <- f.captured || not root_built;
  close_frame f;
  force v

(* Whether the last forcing of [th] may have captured a node ([compute]). *)
let captures th = th.captures

(* The line of a released thunk, or [No_line]. *)
let line_of th = th.line

(* Undo a release: [th] holds [tree] again and no line, as a thunk forced and never
   released does. For [Justify], when a second forcing is not the same derivation. *)
let keep th tree =
  th.line <- No_line;
  th.forced <- Some tree

(* RELEASE [th]: record the line its derivation was written as and drop the tree (kept
   under BAGUETTE_DEBUG, see [force]). The module header's section on releasing says why
   that writes the same proof. *)
let release th (l : line) =
  (match l with No_line -> invalid_arg "Explanation.release: no line" | Line _ -> ());
  if th.line = No_line then incr released;
  th.line <- l;
  if not Debug.enabled then th.forced <- None

let is_forced = function Deferred { forced = None; _ } -> false | _ -> true

(* The forced value if it is already available, without running any thunk. Useful for
   debug printing, which must not have side effects on the memo table. *)
let peek = function Deferred th -> th.forced | e -> Some e

(* Literals mentioned by an explanation, after forcing, without duplicates. Conflict
   analysis walks this. *)
let lits e =
  let seen = Hashtbl.create 16 in
  let acc = ref [] in
  let add l =
    if not (Hashtbl.mem seen l) then (
      Hashtbl.add seen l ();
      acc := l :: !acc)
  in
  let mark = fresh_mark () in
  let rec go e =
    match e with
    | Deferred th when th.mark = mark -> ()
    | Deferred th ->
        th.mark <- mark;
        head (force e)
    | e -> head e
  and head = function
    (* A decision's reason set is exactly the literal it assumed. [Trivial]'s was
       empty, which is the dependency D-0035 says becomes unsoundness in M2-T3. *)
    | Decision l -> add l
    | Model_row _ -> ()
    | Clause ls -> List.iter add ls
    | Linear (terms, _) -> List.iter (fun (_, l) -> add l) terms
    | Cut (a, b, _, _) ->
        go a;
        go b
    | Combine (summands, _) -> List.iter go_summand summands
    | Resolve parts -> List.iter go parts
    | Deferred _ -> assert false (* force returns a non-deferred head *)
  and go_summand = function
    | Term (_, e) -> go e
    | Weaken lits -> List.iter (fun (_, l) -> add l) lits
    (* The literal a [Defining] cites is a bound fact the derivation RESTS on, so it
       belongs in the reason set at least as much as a weakened one does (D-0035). *)
    | Defining (_, l) -> add l
    (* What the ORDER rendering would name: the axiom chain where nothing is cited, the
       cited derivations otherwise. The bits rendering names the term's one atom instead,
       but [owners] is what every caller reads and it is the same either way. *)
    | Linear_term r -> (
        match r.lt_cited with
        | [] -> List.iter add (lt_axiom_lits r)
        | es -> List.iter go es)
  in
  go e;
  List.rev !acc

(* The FlatZinc identifiers this derivation mentions, after forcing, without
   duplicates -- [lits] projected through [Lit.owner].

   D-0026 split the reason off this type, and the two halves then have to be checked
   against each other rather than kept in agreement by a comment. Literal-for-literal
   they do NOT agree and must not: the reason states where a bound currently *sits*,
   while a [Weaken] summand states the variable's whole *declared* range (D-0013), so
   the two projections of one pruning share no literal for a weakened term. What they do
   share is the variable scope, and that is what [Store.apply]'s D-0026 check compares:
   a reason naming a variable this derivation never mentions is a reason for a different
   pruning. See [Reason.owners] for the other side of the comparison. *)
let owners e =
  List.sort_uniq String.compare (List.map (fun l -> Lit.owner l.Lit.v) (lits e))

(* The variables this derivation WEAKENS out of its own row, at the top level only.

   "Weakens out" is the D-0009 move: an axiom cannot assert a bound but it can cancel a
   term whose variable is still where it was, so a [Weaken] summand is the derivation
   saying "I read this variable and chose not to cite anything for it". Such a variable
   must therefore appear in the reason -- if it does not, the trace line claims its bound
   over a shorter tail than the pruning actually rested on, which is the I-P5 failure
   [int_ne] shipped between M1-T9 and M1-T17 and the one M1-T50 found on the decision
   path.

   TOP LEVEL ONLY, and that is not a shortcut. Recursing through a [Term] would descend
   into an explanation *another propagator instance* built, whose own [Weaken] summands
   are about that row's other variables and have nothing to do with this pruning's reason
   (that is exactly what [Model_row] exists for -- explanation.ml's header). There is no
   way to tell "my own sub-derivation" from "someone else's cited one" in the tree, so
   the check stays where the question is well posed. *)
let top_weaken_owners e =
  match force e with
  | Combine (summands, _) ->
      List.sort_uniq String.compare
        (List.concat_map
           (function
             | Weaken lits -> List.map (fun (_, l) -> Lit.owner l.Lit.v) lits
             (* A cited bound fact is read by this derivation exactly as a weakened one
                is, and the reason owes the same account of it -- more so, since the
                derivation names the line that established it. *)
             | Defining (_, l) -> [ Lit.owner l.Lit.v ]
             | Term _ -> []
             (* An uncited term is weakened out of the row (declared or assumed), and the
                reason owes the same account of it a [Weaken] got. *)
             | Linear_term r -> if r.lt_cited = [] then [ r.lt_name ] else [])
           summands)
  | _ -> []

let rec to_string e =
  match e with
  | Decision l -> "decision(" ^ Lit.to_string l ^ ")"
  | Clause ls -> "clause(" ^ String.concat " " (List.map Lit.to_string ls) ^ ")"
  | Linear (terms, rhs) ->
      Printf.sprintf "linear(%s >= %d)"
        (String.concat " "
           (List.map (fun (a, l) -> Printf.sprintf "%+d %s" a (Lit.to_string l)) terms))
        rhs
  | Cut (a, b, c1, c2) ->
      Printf.sprintf "cut(%d*%s + %d*%s)" c1 (to_string a) c2 (to_string b)
  | Model_row id -> Printf.sprintf "model_row(%d)" id
  | Combine (summands, divisor) ->
      Printf.sprintf "combine(%s)%s"
        (String.concat " + " (List.map summand_to_string summands))
        (if divisor = 1 then "" else Printf.sprintf " / %d" divisor)
  | Resolve parts ->
      Printf.sprintf "resolve(%s)" (String.concat " | " (List.map to_string parts))
  | Deferred { forced = Some e; _ } -> "deferred[" ^ to_string e ^ "]"
  | Deferred { forced = None; line = Line { cid; _ }; _ } ->
      Printf.sprintf "deferred[released, line %d]" cid
  | Deferred { forced = None; _ } -> "deferred[?]"

and summand_to_string = function
  | Term (c, e) -> Printf.sprintf "%d*%s" c (to_string e)
  | Weaken lits ->
      "weaken("
      ^ String.concat " "
          (List.map (fun (c, l) -> Printf.sprintf "%d*%s" c (Lit.to_string l)) lits)
      ^ ")"
  | Defining (c, l) -> Printf.sprintf "%d*defining(%s)" c (Lit.to_string l)
  | Linear_term r ->
      Printf.sprintf "term(%+d*%s@%d in %d..%d%s)" r.lt_coeff r.lt_name r.lt_value
        r.lt_decl_lo r.lt_decl_hi
        (match r.lt_cited with
        | [] -> if lt_declared r then "" else ", assumed"
        | es -> ", cites " ^ String.concat " + " (List.map to_string es))

(* ------------------------------------------------------------------- arena *)

(* Explanations live in a side arena and the trail stores an index into it
   (docs/ARCHITECTURE.md section 3): trail records stay small and uniform, and
   invariant I-T3 - every trail entry's explanation index resolves - becomes something
   that can be checked with a bounds test.

   The arena is a stack. [truncate] is how backtracking discards the reasons for the
   prunings it is undoing; it is safe because nothing outside the trail holds an [id],
   and anything that wants to survive a backtrack (a learned clause) holds the forced
   [expl] value itself, which the GC keeps alive independently. *)
module Arena = struct
  type id = int
  type t = { mutable items : expl array; mutable len : int }

  (* Not a valid index; [get] on it raises. Lets containers hold a "no reason yet". *)
  let null : id = -1

  (* What an arena slot holds when nothing occupies it. [mem] bounds every [get], so
     it is never observable; it exists only so [truncate] can drop its references and
     let the GC collect what a discarded reason's thunk captured. [Trivial] played
     this role until M1-T31 deleted it, and the empty clause is a deliberate
     replacement rather than an arbitrary one: [Trivial] was a *plausible* reason, so
     a slot that leaked read as "the model row justifies this" and nothing complained,
     which is the failure mode this whole task is about. The empty clause renders as a
     claimed contradiction and fails at the checker on sight. *)
  let vacant : expl = Clause []

  let create ?(capacity = 256) () =
    { items = Array.make (Stdlib.max 1 capacity) vacant; len = 0 }

  let length a = a.len
  let mem a (i : id) = i >= 0 && i < a.len

  let grow a =
    let bigger = Array.make (Stdlib.max 1 (2 * Array.length a.items)) vacant in
    Array.blit a.items 0 bigger 0 a.len;
    a.items <- bigger

  let add a (e : expl) : id =
    if a.len = Array.length a.items then grow a;
    a.items.(a.len) <- e;
    a.len <- a.len + 1;
    a.len - 1

  let get a (i : id) : expl =
    if not (mem a i) then
      invalid_arg
        (Printf.sprintf "Explanation.Arena.get: %d out of range (len %d)" i a.len);
    a.items.(i)

  (* Force in place, so the memoised result is what the arena holds from now on. *)
  let force_at a (i : id) : expl =
    let e = force (get a i) in
    a.items.(i) <- e;
    e

  let truncate a n =
    if n < 0 then invalid_arg "Explanation.Arena.truncate: negative length";
    if n < a.len then (
      (* Drop the references so the explanations, and anything their thunks captured,
         become collectable. *)
      Array.fill a.items n (a.len - n) vacant;
      a.len <- n)

  let clear a = truncate a 0
end
