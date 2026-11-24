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
   [Justify] needs to tell whether the line is still on the page) and drops its tree
   (until M11-complexity-T15 the memo cells that emission made for nodes the closure
   BUILT were taken out with it; since T15 every node carries its own line). Until
   then the tree stayed reachable from [forced], from the closure [force] put in place of
   the original, and from the memo's keys, for as long as the trail entry stood: 1.16 GB
   of all_different derivations on 2011_black-hole_9 at node 40 (D-0166 section 4).

   Why every proof byte is the same, reader by reader:

   - A later [emit] of the thunk. The memo answered it (or its forced head) with the id
     for as long as no wipe had reached the level it was written at; the line answers
     under exactly that condition ([Justify.live]).
   - [emit] after that level was wiped. The same physical tree used to be written again,
     every cell of it gone with the wipe. Now the closure is forced again and that tree
     is written. It is the same derivation because a thunk closes over a SNAPSHOT (I-X6);
     under BAGUETTE_DEBUG every release forces the closure a second time and refuses to
     go on unless [same_derivation] holds, and every later forcing is compared with the
     original, which a released thunk then keeps. The memo answers the two trees alike
     because a node of the tree either is CAPTURED -- a value the closure did not build,
     like another entry's eager explanation, held physically by both forcings -- and
     carries its own line, so it is found as before; or is BUILT, new at every forcing
     and reachable from nothing but its tree, so that no lookup can present it again.
   - [lits] (the D-0026 agreement walk, under BAGUETTE_DEBUG), [Pb_analysis.cited_ids],
     and the readers that match on a forced head: [force] forces a released thunk again,
     without memoising, and they read the same derivation.

   M11-complexity-T15 removed what T13 needed to tell CAPTURED from BUILT nodes (a frame
   recording every build while a thunk was forced, and a second forcing at the release
   when the tree might hold a node the closure had not built): that split existed to
   take a released tree's memo cells out of a table, and since T15 a node's line is a
   field of the node, so no table holds a node and there is nothing to take out. T13
   measured, and the sentence stays true, that a thunk is not the only shared node of a
   derivation (39 captured cells on the suite: an eager [Combine] the trace had already
   written as another entry's line); with the line on the node that sharing needs no
   bookkeeping, since the node is the same value for every derivation that holds it.

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
  | Clause of { lits : Lit.t list; mutable line : line; hid : int }
    (* These literals together imply the pruning. Renders to rup. *)
  | Linear of { terms : (int * Lit.t) list; rhs : int; mutable line : line; hid : int }
    (* sum a_i l_i >= b. Renders to pol over the model constraint. *)
  | Cut of { e1 : t; e2 : t; c1 : int; c2 : int; mutable line : line; hid : int }
    (* Linear combination: c1 * e1 + c2 * e2, the cutting-planes workhorse. Kept for
       existing single-row uses; D-0013's cross-row, divided combination is
       [Combine], below -- see the module header. *)
  | Model_row of int
    (* The id (a Baguette_proof.Writer.cid) of a model constraint already loaded by
       the checker's [f] rule, named explicitly rather than resolved through
       whatever [ctx.model_id] happens to point at right now. See the module
       header. *)
  | Combine of { summands : summand list; divisor : int; mutable line : line; hid : int }
    (* sum of summands, then divide by the int (>= 1; 1 means "do not divide" --
       Justify skips emitting a division step rather than a no-op "1 d"). One
       [Combine] is one [pol] step (D-0013). *)
  | Resolve of { parts : t list; mutable line : line; hid : int }
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
(* Computed only if actually needed.

   M11-complexity-T15 (the DAG spike): the five constructors a line is written for
   ([Clause], [Linear], [Cut], [Combine], [Resolve]) carry that line ([line]: [No_line]
   until [Justify] writes one, the same record a thunk keeps) and an identity [hid] (0
   unless BAGUETTE_HASHCONS=1, see "hash-consing" below). The memo that was a table in
   [Justify] keyed by physical identity is this field: a node remembers its own line, so
   a lookup is a field read and nothing outside the node holds it. Build them through
   the smart constructors; a pattern reads the fields it needs and ends in [_]. *)

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
  tid : int; (* M11-complexity-T15: the identity a hash-consed parent hashes it by *)
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

(* ------------------------------------------------------ hash-consing (T15)

   M11-complexity-T15, D-0172 (D-0140 J1). Every node a line can be written for is
   HASH-CONSED when it is built: a node whose content equals a node whose line is on the
   page IS that node, so an identical derivation built twice is one value, its line is
   written once and every later build cites it ([Justify.memoized]). It replaces D-0158's
   share mode, which found the same lines by rendering every miss: here the identical node
   is found at its build and its emission is one field read. The key is SHALLOW: the
   constructor, its integers and literals, and every operand by its own identity ([hid]
   for a node, [tid] for a thunk, the id for a [Model_row]), which is sound because the
   operands are themselves hash-consed, so two equal operands are one value. The table
   holds the written nodes only (see [table]).

   M16-file-review-T4 (D-0192): a node's [hid] is its content hash, computed once at its
   build, so every later lookup of the node ([hc_written], [hc_wipe]) hashes it in one
   read; equality still compares the operands by identity. The table and its two walks
   are written out ([Hc], [summands_hash], [same_summands]) rather than built from
   [Hashtbl.Make] and [List.fold_left]/[List.equal] over closures. The answers are the
   same, so the bytes are: 2011_cyclic-rcpsp_easy_6 with the proof, whose alldiff hands
   this module 2.27 M [Combine] builds and 51 M summands in 2 000 nodes (2.0 M of them
   identical to a written node), went from 52.7 to 47.3 G instructions, the same proof.

   ON BY DEFAULT (D-0172, decided by the orchestrator on the user's delegation, D-0167
   item 3). BAGUETTE_HASHCONS=0 turns it off for comparison: [hid] and [tid] are then 0,
   nothing is hashed, every build is a value of its own and each copy writes its own line,
   which is the proof main wrote before D-0172 byte for byte. [set_hashcons] is the same
   switch for a test. *)
let hashcons =
  ref (match Sys.getenv_opt "BAGUETTE_HASHCONS" with Some "0" -> false | _ -> true)

let stats_on =
  match Sys.getenv_opt "BAGUETTE_MEMO_STATS" with
  | Some ("1" | "true" | "yes" | "on") -> true
  | _ -> false

let hid_counter = ref 0

let fresh_hid () =
  if !hashcons || stats_on then (
    incr hid_counter;
    !hid_counter)
  else 0

let mix h x = (h * 31) + x

let lit_hash (l : Lit.t) =
  let k, x, v =
    match l.Lit.v with
    | Lit.Ge (x, v) -> (0, x, v)
    | Lit.Eq (x, v) -> (1, x, v)
    | Lit.Bit (x, i) -> (2, x, i)
  in
  mix (mix (mix (Hashtbl.hash x) v) k) (Bool.to_int l.Lit.positive)

let[@inline] operand_id = function
  | Clause r -> r.hid
  | Linear r -> r.hid
  | Cut r -> r.hid
  | Combine r -> r.hid
  | Resolve r -> r.hid
  | Deferred th -> th.tid
  | Model_row i -> mix 4 i
  | Decision l -> lit_hash l

let[@inline] same_operand a b =
  a == b || match (a, b) with Model_row i, Model_row j -> i = j | _ -> false

let same_terms = List.equal (fun (c, l) (d, m) -> c = d && Lit.equal l m)

let same_summand s t =
  match (s, t) with
  | Term (c, a), Term (d, b) -> c = d && same_operand a b
  | Weaken ls, Weaken ms -> same_terms ls ms
  | Defining (c, l), Defining (d, m) -> c = d && Lit.equal l m
  | Linear_term r, Linear_term q ->
      r.lt_coeff = q.lt_coeff && r.lt_value = q.lt_value && r.lt_decl_lo = q.lt_decl_lo
      && r.lt_decl_hi = q.lt_decl_hi
      && String.equal r.lt_name q.lt_name
      && List.equal same_operand r.lt_cited q.lt_cited
  | _ -> false

(* M16-file-review-T4 (D-0192): the two walks a lookup makes over a [Combine]'s summands,
   written as loops. They were [List.fold_left] and [List.equal] over a closure, one
   [caml_apply2] and two calls per summand; alldiff's derivations hand this module 51 M
   summands in 2 000 nodes of 2011_cyclic-rcpsp_easy_6. A summand physically shared by
   the two lists is equal without being read. *)
let summand_hash h = function
  | Term (c, e) -> mix (mix (mix h 1) c) (operand_id e)
  | Weaken ls -> List.fold_left (fun h (c, l) -> mix (mix h c) (lit_hash l)) (mix h 2) ls
  | Defining (c, l) -> mix (mix (mix h 3) c) (lit_hash l)
  | Linear_term r ->
      List.fold_left
        (fun h e -> mix h (operand_id e))
        (mix (mix (mix (mix h 4) (Hashtbl.hash r.lt_name)) r.lt_coeff) r.lt_value)
        r.lt_cited

let rec summands_hash h = function
  | [] -> h
  | Term (c, e) :: rest -> summands_hash (mix (mix (mix h 1) c) (operand_id e)) rest
  | s :: rest -> summands_hash (summand_hash h s) rest

let rec same_summands a b =
  match (a, b) with
  | [], [] -> true
  | Term (c, x) :: a', Term (d, y) :: b' ->
      c = d && same_operand x y && same_summands a' b'
  | s :: a', t :: b' -> (s == t || same_summand s t) && same_summands a' b'
  | _ -> false

let rec parts_hash h = function
  | [] -> h
  | e :: rest -> parts_hash (mix h (operand_id e)) rest

let rec same_parts a b =
  match (a, b) with
  | [], [] -> true
  | e :: a', f :: b' -> same_operand e f && same_parts a' b'
  | _ -> false

(* The content hashes, one per constructor a line is written for: the constructor, its
   integers and literals, and every operand by its [operand_id]. *)
let clause_hash lits = List.fold_left (fun h l -> mix h (lit_hash l)) 1 lits land max_int

let linear_hash terms rhs =
  List.fold_left (fun h (c, l) -> mix (mix h c) (lit_hash l)) (mix 2 rhs) terms
  land max_int

let cut_hash e1 e2 c1 c2 =
  mix (mix (mix (mix 3 c1) c2) (operand_id e1)) (operand_id e2) land max_int

let combine_hash summands divisor = summands_hash (mix 5 divisor) summands land max_int
let resolve_hash parts = parts_hash 7 parts land max_int

(* M16-file-review-T4 (D-0192): a node's [hid] IS its content hash, computed once when it
   is built. It was a counter, an identity, and the table hashed the node's content at
   every lookup, five times over for a node that is written and wiped (its build, the two
   lookups of [hc_written] and the two of [hc_wipe]). An operand's [hid] serves its parent's
   hash as the counter did: two operands that are one value have one [hid]. Two DIFFERENT
   values may now share one -- the twins of a content written twice, [hc_written] below --
   and their parents' hashes then collide, which [hc_equal] tells apart, since it compares
   operands by identity as before. 0 when hash-consing is off (unless the stats are on),
   as before: nothing is hashed. *)
let hashing () = !hashcons || stats_on

(* A node built while hash-consing was off has [hid] 0 (a test switches with
   [set_hashcons]); its content hash is computed when asked, so it hashes as it did. *)
let content_hash e =
  match e with
  | Clause r -> clause_hash r.lits
  | Linear r -> linear_hash r.terms r.rhs
  | Cut r -> cut_hash r.e1 r.e2 r.c1 r.c2
  | Combine r -> combine_hash r.summands r.divisor
  | Resolve r -> resolve_hash r.parts
  | Model_row _ | Decision _ | Deferred _ -> 0

(* [x.hid <> y.hid] with both nonzero: two contents hashed apart, unequal. *)
let[@inline] apart (h : int) (k : int) = h <> k && h <> 0 && k <> 0

(* Equal content: the constructor, its integers and literals, the operands by identity. *)
let hc_equal a b =
  a == b
  ||
  match (a, b) with
  | Clause x, Clause y -> (not (apart x.hid y.hid)) && List.equal Lit.equal x.lits y.lits
  | Linear x, Linear y ->
      (not (apart x.hid y.hid)) && x.rhs = y.rhs && same_terms x.terms y.terms
  | Cut x, Cut y ->
      (not (apart x.hid y.hid))
      && x.c1 = y.c1 && x.c2 = y.c2 && same_operand x.e1 y.e1 && same_operand x.e2 y.e2
  | Combine x, Combine y ->
      (not (apart x.hid y.hid))
      && x.divisor = y.divisor
      && same_summands x.summands y.summands
  | Resolve x, Resolve y -> (not (apart x.hid y.hid)) && same_parts x.parts y.parts
  | _ -> false

let hc_hash e =
  let h = operand_id e in
  match e with
  | (Clause _ | Linear _ | Cut _ | Combine _ | Resolve _) when h <> 0 -> h
  | _ -> content_hash e

(* M16-file-review-T4 (D-0192): the table is written out here rather than taken from
   [Hashtbl.Make], whose code calls [equal] and [hash] as unknown closures ([caml_apply2]
   for every bucket entry compared). Buckets of nodes, at most one node of a content (the
   only writer is [hc_enter], which replaces), doubled when it holds twice as many nodes
   as buckets, as [Hashtbl] does. It is never iterated, so its layout reaches no byte. *)
module Hc = struct
  (* [epoch] counts the times a node LEFT the table (D-0216): a wipe that took one out, a
     twin that replaced it, a reset. Adding a node displaces no node of another content,
     so a node seen in the table at an epoch is still there while the epoch has not
     moved ([reuse_epoch], [rebuilds_to]). *)
  type tbl = { mutable buckets : t list array; mutable size : int; mutable epoch : int }

  let create n = { buckets = Array.make n []; size = 0; epoch = 0 }
  let length t = t.size
  let index t h = h land (Array.length t.buckets - 1)

  let reset t =
    t.buckets <- Array.make 4096 [];
    t.size <- 0;
    t.epoch <- t.epoch + 1

  let find_opt t e =
    let rec go = function
      | [] -> None
      | x :: r -> if hc_equal e x then Some x else go r
    in
    go t.buckets.(index t (hc_hash e))

  let mem t e = Option.is_some (find_opt t e)

  let resize t =
    let old = t.buckets in
    let b = Array.make (2 * Array.length old) [] in
    t.buckets <- b;
    Array.iter
      (List.iter (fun x ->
           let i = index t (hc_hash x) in
           b.(i) <- x :: b.(i)))
      old

  (* [e] in the place of the node of its content, or added. *)
  let replace t e =
    let i = index t (hc_hash e) in
    let rec take = function
      | [] -> None
      | x :: r -> (
          if hc_equal e x then Some r
          else match take r with Some r' -> Some (x :: r') | None -> None)
    in
    match take t.buckets.(i) with
    | Some rest ->
        t.buckets.(i) <- e :: rest;
        t.epoch <- t.epoch + 1
    | None ->
        t.buckets.(i) <- e :: t.buckets.(i);
        t.size <- t.size + 1;
        if t.size > 2 * Array.length t.buckets then resize t

  (* [e] itself out, if it is the node of its content. *)
  let remove_node t e =
    let i = index t (hc_hash e) in
    if List.memq e t.buckets.(i) then (
      t.buckets.(i) <- List.filter (fun x -> x != e) t.buckets.(i);
      t.size <- t.size - 1;
      t.epoch <- t.epoch + 1)

  (* [e] itself is the node of its content in the table. *)
  let holds t e = List.memq e t.buckets.(index t (hc_hash e))
end

(* The table holds the nodes whose LINE is on the page, by the content of the node, and
   only those. [Justify] enters a node when it writes its line ([hc_written], at the
   writer's level) and takes it out when that level is wiped ([hc_wipe]), so a build
   whose content equals a written node returns that node, and [Justify] cites its line.
   Two other scopings were tried and measured, and both are wrong for a reason worth
   keeping:

   - a WEAK table (a node stays while anything reaches it): the answer then depends on
     whether the collector has run, and the proof's bytes moved with every allocation
     anywhere (the same run with BAGUETTE_MEMO_STATS on wrote a different proof);
   - a table scoped by the STORE's level at the build: it never answers, because the
     identical rebuilds come after the level that built the first copy was undone, while
     the first copy's line, written at a shallower level, is still on the page
     (2013_rcpsp_11 at 300 nodes: 0 identical builds found, against 67 264 with the weak
     table).

   What the table answers is a function of the lines on the page, so the bytes are a
   function of the search. *)
let table : Hc.tbl = Hc.create 4096
let hc_by_level : t list array ref = ref (Array.make 64 [])
let hc_hi = ref (-1)

let rec hc_written e level =
  let twin_at_or_below =
    match Hc.find_opt table e with
    | Some x when x != e -> (
        match x with
        | Clause { line = Line { level = l; _ }; _ }
        | Linear { line = Line { level = l; _ }; _ }
        | Cut { line = Line { level = l; _ }; _ }
        | Combine { line = Line { level = l; _ }; _ }
        | Resolve { line = Line { level = l; _ }; _ } ->
            l <= level
        | _ -> false)
    | _ -> false
  in
  (* Two nodes of one content are both written when the second was built before the first
     was written. The table keeps the one whose line lives longer, the shallower. *)
  if not twin_at_or_below then hc_enter e level

and hc_enter e level =
  Hc.replace table e;
  if level >= Array.length !hc_by_level then (
    let a = Array.make (2 * (level + 1)) [] in
    Array.blit !hc_by_level 0 a 0 (Array.length !hc_by_level);
    hc_by_level := a);
  !hc_by_level.(level) <- e :: !hc_by_level.(level);
  if level > !hc_hi then hc_hi := level

let hc_wipe level =
  for l = level to !hc_hi do
    List.iter (fun e -> Hc.remove_node table e) !hc_by_level.(l);
    !hc_by_level.(l) <- []
  done;
  if !hc_hi >= level then hc_hi := level - 1

(* For a test that needs both modes in one process: switch, and forget every written
   node (a node written under the other mode must not answer a build under this one). *)
let set_hashcons on =
  hashcons := on;
  Hc.reset table;
  hc_by_level := Array.make 64 [];
  hc_hi := -1

(* BAGUETTE_MEMO_STATS: how many nodes of each constructor were built, and how many of
   those builds were IDENTICAL to a node still reachable (a hash-consing hit), per
   constructor and per producer -- the propagator running when the node was built
   ([producer], set by [Engine] around a run and by [Trace] around an entry's lines). The
   identical builds are counted whether or not hash-consing is on: off, the table is
   still consulted when the stats are asked for, and a hit is counted and discarded. *)
(* The instance id of the propagator building now, or -1; [producer_name] is [Engine]'s
   [name_of], installed when the stats are on. *)
let producer = ref (-1)
let producer_name : (int -> string) ref = ref (fun _ -> "other")
let producer_label () = if !producer < 0 then "other" else !producer_name !producer
let hc_by : (string, int ref * int ref) Hashtbl.t = Hashtbl.create 32

let tag = function
  | Clause _ -> "clause"
  | Linear _ -> "linear"
  | Cut _ -> "cut"
  | Combine _ -> "combine"
  | Resolve _ -> "resolve"
  | _ -> "other"

let count key hit =
  let b, h =
    match Hashtbl.find_opt hc_by key with
    | Some p -> p
    | None ->
        let p = (ref 0, ref 0) in
        Hashtbl.replace hc_by key p;
        p
  in
  incr b;
  if hit then incr h

(* Off, with the stats asked for, the table still takes the written nodes: a build
   identical to one of them is counted, and the value returned is still the new build, so
   nothing the solver writes changes. *)
(* The table is looked into only when it holds something: under `--no-proof`, and before
   the first line, nothing is ever written, so a build pays one length read and is not
   hashed (the scaling lane measured rcpsp_11 without the proof +0.68 % of its late cost per
   node with the hash paid on every build, D-0172 section 8). *)
let built e =
  if !hashcons then (
    let e' =
      if Hc.length table = 0 then e
      else match Hc.find_opt table e with Some x -> x | None -> e
    in
    if stats_on then count (producer_label () ^ "\t" ^ tag e) (e' != e);
    e')
  else if stats_on then (
    count (producer_label () ^ "\t" ^ tag e) (Hc.mem table e);
    e)
  else e

(* ------------------------------------------------- reusing a build (D-0216)

   A build that hits the table costs the build: the operands are made, the summand list
   is allocated and hashed, and the bucket is compared, all to be handed back a node that
   already exists. Alldiff's Hall derivations are rebuilt per pruning (D-0172 section 1),
   so most of their builds are hits: on 2011_black-hole_10 under native `table`, the 156
   removals one 47-variable Hall set licenses rebuild 8.3 M pairwise at-most-one nodes,
   nearly all of them hits (78 468 `pol` lines are written in all), 55 G instructions at
   the root. A caller that builds a node as a DETERMINISTIC function of a key (the same
   leaves, the same operands obtained the same way) may keep the node it got and hand it
   back instead of building again, when building again would return that very node. That is the case exactly when the node is the table's
   node of its content and so is every node it cites: [built] then answers each operand's
   rebuild and the node's own rebuild with those nodes, one level at a time. [rebuilds_to]
   checks that, SHALLOWLY: the node and its direct operands. The caller supplies the
   induction below them by having obtained those operands the same way (a reused node, or
   a build). A thunk or a decision operand answers [false]: it is cited by identity and a
   rebuild makes a new one.

   [reuse_epoch] is [Hc]'s count of nodes that left the table, or -1 when no build can hit
   (hash-consing off, the table empty, or BAGUETTE_MEMO_STATS, whose counts are of builds):
   a node checked at an epoch is still in the table while the epoch is unchanged, so a
   caller re-checks only after a node left. Nothing here changes what a build returns, so
   the bytes are the builds' bytes. *)
let reuse_epoch () =
  if !hashcons && (not stats_on) && Hc.length table > 0 then table.Hc.epoch else -1

let operand_held = function
  | (Clause _ | Linear _ | Cut _ | Combine _ | Resolve _) as e -> Hc.holds table e
  | Model_row _ -> true
  | Decision _ | Deferred _ -> false

let summand_held = function
  | Term (_, e) -> operand_held e
  | Weaken _ | Defining _ -> true
  | Linear_term r -> List.for_all operand_held r.lt_cited

let rebuilds_to e =
  reuse_epoch () >= 0
  &&
  match e with
  | Clause _ | Linear _ -> Hc.holds table e
  | Cut r -> Hc.holds table e && operand_held r.e1 && operand_held r.e2
  | Combine r -> Hc.holds table e && List.for_all summand_held r.summands
  | Resolve r -> Hc.holds table e && List.for_all operand_held r.parts
  | Model_row _ | Decision _ | Deferred _ -> false

let () =
  if stats_on then
    at_exit (fun () ->
        let rows = Hashtbl.fold (fun k (b, h) acc -> (k, !b, !h) :: acc) hc_by [] in
        let rows = List.sort (fun (_, _, a) (_, _, b) -> compare b a) rows in
        List.iter
          (fun (k, b, h) ->
            Printf.eprintf "baguette: hashcons\t%s\tbuilt=%d\tidentical=%d\n" k b h)
          rows)

let decision lit = Decision lit

let clause lits =
  built
    (Clause { lits; line = No_line; hid = (if hashing () then clause_hash lits else 0) })

let linear terms rhs =
  built
    (Linear
       {
         terms;
         rhs;
         line = No_line;
         hid = (if hashing () then linear_hash terms rhs else 0);
       })

(* M21-memory-T3 (D-0223): the citation of a model row is SHARED, one block per id. A
   counting family cites a ladder as one [Term (1, Model_row id)] per rung, and on
   2026_tdtsp_10_53 the trees kept alive held 26 M of them, 8 words each (the [Model_row]
   block, the [Term] block, the list cell) for one integer of content (D-0218 section 5,
   OCaml's factor 8 on this kind). Interned, a citation costs its list cell. Nothing can
   tell a shared one from a fresh one: [Model_row] and [Term] are immutable, every reader
   matches them by structure, and the hash-consing key compares a [Model_row] by its id
   ([summand_hash], [hc_equal]), never by identity. So the bytes are the same by
   construction. Ids above [intern_cap] are built fresh, so the table is at most
   [intern_cap] words. *)
let intern_cap = 1 lsl 22
let no_row = Weaken []
let cited_rows : summand array ref = ref [||]

let cite_row id =
  if id < 0 || id >= intern_cap then Term (1, Model_row id)
  else (
    if id >= Array.length !cited_rows then (
      let a =
        Array.make (Stdlib.min intern_cap (Stdlib.max 1024 (2 * (id + 1)))) no_row
      in
      Array.blit !cited_rows 0 a 0 (Array.length !cited_rows);
      cited_rows := a);
    match Array.unsafe_get !cited_rows id with
    | Term _ as s -> s
    | _ ->
        let s = Term (1, Model_row id) in
        Array.unsafe_set !cited_rows id s;
        s)

let model_row id = match cite_row id with Term (_, m) -> m | _ -> Model_row id
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
let refuse_decision what l =
  invalid_arg
    (Printf.sprintf
       "Explanation.%s: a decision (%s) has no constraint id and cannot be cited. Weaken \
        the term out of the row instead -- see explanation.ml's header."
       what (Lit.to_string l))

(* Inlined (M16-file-review-T4, D-0192): it is asked once per summand alldiff builds, and
   was 1.5 % of 2011_cyclic-rcpsp_easy_6's samples as a call. *)
let[@inline] citable what e = match e with Decision l -> refuse_decision what l | e -> e

let cut e1 e2 c1 c2 =
  let e1 = citable "cut" e1 and e2 = citable "cut" e2 in
  built
    (Cut
       {
         e1;
         e2;
         c1;
         c2;
         line = No_line;
         hid = (if hashing () then cut_hash e1 e2 c1 c2 else 0);
       })

let term coeff e =
  match e with
  | Model_row id when coeff = 1 -> cite_row id
  | _ -> Term (coeff, citable "term" e)

(* [resolve parts]: the parts are cited (summed) and so cannot be decisions; two is the
   least that can resolve on anything (D-0134 section 2.2). *)
let resolve parts =
  (match parts with
  | [] | [ _ ] -> invalid_arg "Explanation.resolve: at least two derivations to resolve"
  | _ -> ());
  let parts = List.map (citable "resolve") parts in
  built
    (Resolve
       { parts; line = No_line; hid = (if hashing () then resolve_hash parts else 0) })

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
  built
    (Combine
       {
         summands;
         divisor;
         line = No_line;
         hid = (if hashing () then combine_hash summands divisor else 0);
       })

let born : (int, int) Hashtbl.t = Hashtbl.create (if stats_on then 4096 else 1)

let deferred compute =
  let tid = fresh_hid () in
  if stats_on then Hashtbl.replace born tid !producer;
  Deferred { forced = None; compute; mark = 0; line = No_line; tid }

(* The line a node remembers ([No_line] for a [Decision], a [Model_row] or a thunk, whose
   line [Justify] reads through [line_of]), and the writing of it. *)
let node_line = function
  | Clause r -> r.line
  | Linear r -> r.line
  | Cut r -> r.line
  | Combine r -> r.line
  | Resolve r -> r.line
  | Decision _ | Model_row _ | Deferred _ -> No_line

let set_node_line e l =
  match e with
  | Clause r -> r.line <- l
  | Linear r -> r.line <- l
  | Cut r -> r.line <- l
  | Combine r -> r.line <- l
  | Resolve r -> r.line <- l
  | Decision _ | Model_row _ | Deferred _ ->
      invalid_arg "Explanation.set_node_line: not a node a line is written for"

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
   BAGUETTE_DEBUG asks of a thunk's tree and a second forcing of it when [Justify]
   releases the thunk, and of every forcing after (I-X6). A thunk is compared by identity,
   never descended into: a cited thunk is a shared node, and the second forcing must cite
   the same one. Everything else is compared by structure; the [line] a node carries is
   not part of what it derives and is not compared. *)
let same_derivation a b =
  let rec go a b =
    a == b
    ||
    match (a, b) with
    | Deferred x, Deferred y -> x == y
    | Decision l, Decision m -> Lit.equal l m
    | Clause x, Clause y -> List.equal Lit.equal x.lits y.lits
    | Linear x, Linear y -> x.rhs = y.rhs && same_terms x.terms y.terms
    | Cut x, Cut y -> x.c1 = y.c1 && x.c2 = y.c2 && go x.e1 y.e1 && go x.e2 y.e2
    | Model_row i, Model_row j -> i = j
    | Combine x, Combine y ->
        x.divisor = y.divisor && List.equal summand x.summands y.summands
    | Resolve x, Resolve y -> List.equal go x.parts y.parts
    | _ -> false
  and summand s t =
    match (s, t) with
    | Term (c, a), Term (d, b) -> c = d && go a b
    | Weaken ls, Weaken ms -> same_terms ls ms
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
   the release rests on. The tree returned is the new one in both modes. *)
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
   would return. For BAGUETTE_DEBUG's check when [Justify] releases. *)
and reforce th = compute th

and compute th =
  if stats_on then (
    (* a build inside the closure is the producer's that made the thunk *)
    let p = !producer in
    (match Hashtbl.find_opt born th.tid with Some b -> producer := b | None -> ());
    let v = th.compute () in
    producer := p;
    force v)
  else force (th.compute ())

(* The line of a released thunk, or [No_line]. *)
let line_of th = th.line

(* RELEASE [th]: record the line its derivation was written as and drop the tree (kept
   under BAGUETTE_DEBUG, see [force]). Since M11-complexity-T15 nothing else has to let go
   of the tree: every node of it carries its own line, and no table holds a node. *)
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
    | Clause r -> List.iter add r.lits
    | Linear r -> List.iter (fun (_, l) -> add l) r.terms
    | Cut r ->
        go r.e1;
        go r.e2
    | Combine r -> List.iter go_summand r.summands
    | Resolve r -> List.iter go r.parts
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
  | Combine { summands; _ } ->
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
  | Clause { lits = ls; _ } ->
      "clause(" ^ String.concat " " (List.map Lit.to_string ls) ^ ")"
  | Linear { terms; rhs; _ } ->
      Printf.sprintf "linear(%s >= %d)"
        (String.concat " "
           (List.map (fun (a, l) -> Printf.sprintf "%+d %s" a (Lit.to_string l)) terms))
        rhs
  | Cut { e1 = a; e2 = b; c1; c2; _ } ->
      Printf.sprintf "cut(%d*%s + %d*%s)" c1 (to_string a) c2 (to_string b)
  | Model_row id -> Printf.sprintf "model_row(%d)" id
  | Combine { summands; divisor; _ } ->
      Printf.sprintf "combine(%s)%s"
        (String.concat " + " (List.map summand_to_string summands))
        (if divisor = 1 then "" else Printf.sprintf " / %d" divisor)
  | Resolve { parts; _ } ->
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
  let vacant : expl = Clause { lits = []; line = No_line; hid = 0 }

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
