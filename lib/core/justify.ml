(* Justify: turn an [Explanation.t] into VeriPB proof rules and hand back the id of the
   resulting constraint.

   This lives in [core], not [proof] (docs/ARCHITECTURE.md section 1): the dependency
   direction is [core -> proof], so [proof] cannot see [Explanation] and the bridge has
   to sit on the [core] side of the line, calling down into [Baguette_proof.Writer].

   -------------------------------------------------------------------------------
   Which rule a derivation is written as (D-0009, D-0013, D-0043, and since
   M8-bits-encoding-T5 D-0131)
   -------------------------------------------------------------------------------

   docs/PROOF-FORMAT.md section 2a's rule used to read "prefer [pol] over [rup]
   everywhere [pol] states the reasoning; [rup] makes the checker search". D-0127
   measured that sentence on the checker alone and found it true for a derivation of
   O(1) citations and false for one of Theta(w): a `pol` that adds Theta(w) terms into
   a wide accumulator is quadratic for VeriPB 3.0.2 (383 s at w = 10^6), the same
   conclusion as a `rup` is 197 bytes and the linear unit-propagation walk the checker
   does anyway (2.6 s, dominated by reading the .opb), and the elaborator writes a
   `rup` as its hint list while it copies a `pol` as it is. So the rule this module
   follows is D-0127's closing sentence: **a justification is written as `rup`
   wherever the checker's unit propagation closes it, and as `pol` only where it
   cannot.**

   Per constructor, that is:

     - [Clause] and [Linear] are `rup`, and always were: a clause carries no record of
       HOW its literals imply the pruning, and a bare literal in a `pol` asserts
       nothing (D-0009, and [emit_linear]'s comment keeps the measurement).
     - [Combine] and [Cut] WITH A CONCLUSION -- [emit_concluding], the D-0043 path,
       whose claim is one order literal -- are `rup` of that literal. The ladder walk
       D-0013's "weaken, divide, add" spells out as Theta(w) axioms is exactly what the
       checker's unit propagation performs on its own along the ladder rows the .opb
       holds (D-0031), once the bounds the derivation cites are on the page as lines it
       can propagate along. Where that is true a `rup` is one line and O(1) tokens where
       the `pol` + `ia` + `del` of D-0043 were three lines and Theta(w) tokens; where it
       is not, the checker says so at the line ("not implied by reverse unit
       propagation"), and nothing is silently weaker. The conclusion goes through the
       claim index like every other clause, so a line the trace already wrote is reused
       rather than restated (M1-T59).
     - [Combine] and [Cut] WITHOUT a conclusion -- plain [emit] -- stay the D-0013
       `pol`. A bare derivation is demanded exactly where its RESULT is consumed as a
       ROW by arithmetic rather than as a bound: a [Term] operand of a parent `pol`, a
       counting family's derivation written ahead of its trace line because unit
       propagation cannot close that line without it (I-X10's [Needs_derivation]:
       alldiff, gcc, element, cumulative), and [Pb_analysis.introduce]'s learned PB row,
       whose claim is an inequality the checker cannot reach by propagation (measured,
       D-0131: the lifted row of lib/core/ladder.ml's worked example is refused as
       `rup`). For those the `pol` IS the statement, and its token count is what
       `--stats` reports so that a Theta(w) one is seen rather than suffered.
     - [Model_row] writes nothing: its id is the row's.
     - [Decision] is not a derivation at all, and [emit] refuses it rather than
       rendering it as something.

   The root conflict, which until D-0131 was the one place [Linear]'s Combine reached
   the page as a `pol` at all, no longer asks this module for the derivation:
   [Search.close_root_conflict] writes the root's trace and closes with `rup >= 1`, the
   nogood over an empty decision stack (D-0018 with [decisions = []]), which is the same
   shape every branch already closed with.

   -------------------------------------------------------------------------------
   The BITS arm (M8-bits-encoding-T2, D-0130 section 7 as D-0132 section 2 rebuilt it)
   -------------------------------------------------------------------------------

   A pruning or conflict of a [Linear] row with at least one term on the bits encoding
   is not RUP: a bound does not cross a bits row by unit propagation (D-0127, measured
   at every width). Its trace line is therefore written by [emit_bits_pruning] as ONE
   `pol` that derives EXACTLY the trace clause `claim \/ ~facts`, pinned by `ia`
   through [Writer.pol_concluding]: the row; for every other term, its bound line
   ([Encoding.bound_lines], `@lb`/`@ub`) scaled by |a| when the bound it read is the
   declared one, else its bridge ([Encoding.ensure_atom]: B1 for `x >= v`, B2 for
   `x <= v`) scaled by |a|, which cancels the term and leaves `|a| k ~fact` in the row;
   then `|a_j| d`; then the pruned variable's own atom (B1 for an upper push, B2 for a
   lower one); then `s`. Every atom's coefficient after the division is >= 1 and the
   degree is exactly 1, so saturation yields the clause with coefficient 1 on each
   literal -- the trace clause itself, which is what [Trace] and [Learn] read. NO unit is
   cited and NO cited explanation is recursed into: that is what makes the derived
   clause the trace clause under a decision as at the root (D-0132 section 2.1 says why
   D-0130's "cite the unit" is wrong under a decision). An ORDER variable in such a row
   is rendered through the same shape by the `rup` bridge pair and degree-0 bound lines
   [Encoding] mints once per (x, v) (D-0132 section 2.2). The order arm's text at
   `--bits-above none` is untouched: [emit_summand] renders a [Linear_term] exactly as it
   rendered the [Weaken]/[Term] it replaced.

   M8-bits-encoding-T3 (D-0134): the second bits-arm shape is [Explanation.Resolve],
   a CHOICE derivation -- maxmin's selector rows over bits, each summed with the bounds
   it reads and saturated to a clause on its selector, the clauses summed with the
   selector clause and saturated ([emit_bits_resolve]). The same fragment per term, the
   same `ia` pin, and no atom added for the claim: the claim variable's term assumes
   the claim's negation inside every part, so the derived clause is the trace clause
   with the claim among its literals (D-0134 section 2.3), which is checked.

   Atoms are minted where a name first reaches the writer (D-0130 section 3.3):
   [validate_lits] below, which every clause, `rup`, [Defining] and nogood already pass
   through, mints the atom of every bits-owned order literal it checks; [Trace] and
   [Search] call [ensure_lit] for a claim, a fact and a decision. A propagator never
   mints; it could not know whether it needs to.

   -------------------------------------------------------------------------------
   Context -- and the ambient row that used to live in it (M1-T31)
   -------------------------------------------------------------------------------

   [ctx] carries two things, and it used to carry a third:

     - [writer]   the proof writer every rule is emitted through.
     - [encoding] lets Justify sanity-check that the literals an explanation mentions
       belong to variables the encoding actually declared, which turns "propagator
       passed garbage" into an immediate, legible error instead of a confusing veripb
       rejection several lines later.

   The third was [model_id], a thunk answering "what is the id of the model constraint
   this batch of explanations is about, right now", with a [for_constraint] view to
   rebind it per site. It existed for one reason: [Explanation.Trivial] carried no
   data, so [emit] could not answer "which constraint is this about" from the
   explanation value alone and had to be told.

   Both are gone. D-0015 gave the ADT [Model_row id], so an explanation names its own
   row; D-0011 says each propagator instance justifies against exactly one row and
   [Linear.make] now *requires* it; and M1-T31 deleted [Trivial], which was the only
   constructor that ever consulted the ambient pointer. What is left is the property
   the row was written for: a [ctx] has no field in which an ambient row could be
   stored, so no explanation can render as "whatever row happens to be current" -- not
   by discipline, but because there is nowhere to put one. A caller that used to reach
   for [for_constraint] wants [Explanation.model_row] in the explanation instead.

   -------------------------------------------------------------------------------
   Memoisation
   -------------------------------------------------------------------------------

   The same [Explanation.t] value can be demanded more than once while conflict
   analysis walks the reason graph (that is exactly why [Explanation.force] itself
   memoises). Emitting it twice would write duplicate proof rules, waste ids, and make
   the proof unreadable, so [emit] keeps its own memo from explanation identity to the
   [Writer.cid] already produced for it.

   Identity, not structural equality, is the only honest key: [Explanation.t] embeds
   closures ([Deferred]'s thunk), which have no useful notion of structural equality
   (and [Hashtbl.hash] on a value that stores a *mutable* memoised result is actively
   dangerous as a hash key -- forcing the thunk changes its representation, so a hash
   computed before forcing would stop matching the bucket after). So the memo is a plain
   association list compared with [==]. That is intentionally simple: the number of
   distinct explanation nodes alive during one conflict's analysis is small, so a linear
   scan costs nothing that matters, and it sidesteps the mutable-hash-key trap entirely.

   [Model_row] is never memoised: it writes nothing and returns the id it already
   carries, so there is nothing to remember.

   M11-complexity-T13 (D-0168): neither is a [Deferred] any more. A thunk's line is kept
   ON THE THUNK ([Explanation.line]: its id, its level, this [ctx]'s epoch and serial),
   and [emit_thunk] RELEASES the thunk once the line is written: the tree is dropped. The
   line answers a later [emit] for as long as no wipe has reached its level ([live]),
   which is when the memo entry it replaces would have answered; after such a wipe the
   thunk is forced again and written again. explanation.ml's header ("releasing a written
   thunk") gives the argument that every byte is the same.

   M11-complexity-T15: and since T15 no node is a key either. Every node a line is written
   for carries that line the way a thunk does ([Explanation.node_line]), so "have I
   emitted this value" is a field read on the value, the identity question it always
   was, with the same liveness test as a thunk's line. The paragraphs above describe the
   table this replaced; what they say about identity being the only honest key is
   unchanged, and is why the field is on the node.

   M11-complexity-T10 (D-0158) added a SHARE MODE (BAGUETTE_MEMO_SHARE=1): a propagator that
   rebuilds the same derivation at every level (D-0149's 388 copies on cable_tree_wiring)
   hands this module a new value each time, so the identity memo misses and each copy
   writes its own line, identical to the first copy's but for its id; share mode rendered
   every miss and looked the LINE up. M11-complexity-T15 (D-0172) replaced it, and it is
   gone: the smart constructors HASH-CONS the nodes (explanation.ml, "hash-consing"), so a
   build whose content equals a node whose line is on the page is that node, and its line
   answers. The condition share mode put on a shared line stays, on the node's line
   ([node_answer]): it answers only at or below the writer's current level, the claim
   index's condition 2 below, for the same reason (`w l` retires levels [>= l], so a line
   at a level at or below the citing line's is never retired before it). The proof is
   share mode's proof (byte for byte on three of D-0172's four instances), the search does
   not change, and BAGUETTE_HASHCONS=0 writes the proof of the identity memo alone.

   Every memo entry is tagged with the writer's level at the moment it was created
   (docs/PROOF-FORMAT.md section 5: [w] wipes every constraint at or above a level).
   [wipe_level] drops the matching memo entries in the same call that wipes the writer,
   so the two stay in lockstep -- a stale memo entry pointing at an id the proof no
   longer contains would otherwise let a later [Cut] silently cite a deleted id.

   -------------------------------------------------------------------------------
   The claim index (M2-T9): which line already states this?
   -------------------------------------------------------------------------------

   The memo above answers "have I emitted *this explanation value* before", keyed on
   physical identity. It cannot answer the different and older question D-0009 leaves
   open: **which constraint id establishes this bound fact?** That question has no
   answer inside an [Explanation.t] -- the record says so in as many words ("an
   explanation that appeals to a bound fact must name the constraint id that
   established it ... until [Explanation.t] can carry ids, [Linear] renders as [rup]")
   -- and the missing field is not on the ADT, it is here: a *lookup* from what a line
   claims to the id of the line claiming it.

   [stated] is that lookup. Its key is a clause, as a set of literals; its value is the
   id of the line that put that clause on the page, with the writer's level at the
   moment it did.

   Three things about the key, each load-bearing:

     - **A clause, not a literal.** D-0019's whole content is that the jump from
       "literal" to "clause" is where a milestone went wrong: a [rup] target is a
       clause, so a *line* claims a clause, and an index over literals could not
       describe most of the lines this proof contains. The literal case is the
       interesting one -- a **unit** line is the only thing that establishes a literal,
       which is exactly what D-0009 needs and what [defining_lit] exposes -- but it is
       the special case of the clause key, not a different table.
     - **Structural, over [Lit.t] rather than over rendered names.** [Lit.var_name]
       sanitises, so two distinct FlatZinc identifiers can render to one OPB name; a
       key built from [Lit.to_string] would silently conflate them and hand back an id
       that states something else. The key is the literal list itself, sorted by
       [Lit.compare] so that clause order does not matter (a clause is a set) and
       [Hashtbl]'s structural equality is the right equality ([Lit.t] holds no closure
       and nothing mutable, unlike [Explanation.t] -- which is why the memo above
       cannot be a [Hashtbl] and this can). Since M11-complexity-T12 (D-0166) the
       sorted list is stored PACKED, two integers a literal over interned names
       ([pack_key]); the packing is injective, so the equality is the same one.
     - **The empty clause and a clause with a repeated literal are not indexed.**
       [Opb.clause] gives every literal coefficient 1 without merging duplicates, so a
       repeated literal is a coefficient-2 row rather than the set its key would claim.
       The empty clause is excluded for a different and sharper reason, below.

   *Nothing iterates this table*, only [Hashtbl.find_opt] on it, so no emitted byte
   depends on hash order (the gate's determinism lane is what would catch that).

   Reuse is allowed under exactly two conditions, and the second is invariant I-S4
   turned into a precondition:

     1. the clause is indexed, and
     2. the indexed line's level is **at or below the writer's current level**.

   (2) is what makes reuse safe rather than merely economical, and it is the same
   sentence I-S4 makes about a settle line citing a hole line: `w l` retires levels
   `>= l`, so a line at a level at or below the citing line's is never retired before
   it. Without (2) a deeper line could be reused by a shallower one and die first. It
   also disposes of the one genuinely dangerous case: [Search]'s nogood goes through
   [emit_clause] like every other clause, and the nogood's id is cited by
   [conclusion UNSAT] at the root and asserted live by [wipe_after_nogood] under a
   decision. A nogood is emitted at the *parent* level, so a trace line written inside
   the branch it closes cannot be handed back for it; and the root nogood is
   [Explanation.clause []], which is not indexed at all.

   [wipe_level] drops the index's entries in the same call as the memo's, for the same
   reason and in lockstep. *)

module Lit = Baguette_proof.Lit
module Opb = Baguette_proof.Opb
module Writer = Baguette_proof.Writer
module Pol = Baguette_proof.Writer.Pol
module Encoding = Baguette_proof.Encoding

(* M11-complexity-T15: the memo is no longer a table. Its history, kept because each
   step was measured: M6-T9 (D-0080) bucketed a physical-identity memo by a shallow hash;
   M11-complexity-T5 (D-0145, D-0140 J1) made that hash allocation-free and computed once;
   M6-T23 (D-0149) hashed an operand by its content; M11-complexity-T12 (D-0166) made a
   cell 48 bytes; M11-complexity-T13 (D-0168) took a released thunk's cells out. Each
   node now carries its own line ([Explanation.node_line]), so a lookup is a field read,
   nothing is hashed, and nothing outside the node holds it: what D-0168's window, frame
   and second forcing existed to let go of is never held. *)

(* M11-complexity-T10 (D-0158), M11-complexity-T15. Off unless asked for:
   BAGUETTE_MEMO_STATS=1 counts the memo's lookups, its hits, the lines too deep to answer
   ([node_answer]) and the thunks' lines, and prints them to stderr at exit, as
   BAGUETTE_WAKE_STATS does for the engine; explanation.ml adds the builds per producer. *)
let memo_stats_on =
  match Sys.getenv_opt "BAGUETTE_MEMO_STATS" with
  | Some ("1" | "true" | "yes" | "on") -> true
  | _ -> false

let ms_lookups = ref 0
let ms_hits = ref 0
let ms_line_hits = ref 0
let ms_level_misses = ref 0

let () =
  if memo_stats_on then
    at_exit (fun () ->
        Printf.eprintf "baguette: memo lookups=%d hits=%d level_misses=%d\n" !ms_lookups
          !ms_hits !ms_level_misses;
        Printf.eprintf
          "baguette: thunks released=%d line_hits=%d reforced=%d (to write again %d)\n"
          !Explanation.released !ms_line_hits !Explanation.reforced
          !Explanation.reforced_emit)

(* An integer mix, for the claim index's keys (M11-complexity-T5,
   D-0145). A name is hashed with [Hashtbl.hash], the C string hash, which allocates
   nothing. *)
let mix h x = (h * 31) + x

let finish h =
  let h = h * 0x2545F4914F6CDD1D in
  h lxor (h lsr 29) land max_int

let lit_hash (l : Lit.t) =
  let k, x, v =
    match l.Lit.v with
    | Lit.Ge (x, v) -> (0, x, v)
    | Lit.Eq (x, v) -> (1, x, v)
    | Lit.Bit (x, i) -> (2, x, i)
  in
  mix (mix (mix (Hashtbl.hash x) v) k) (Bool.to_int l.Lit.positive)

(* A claim that is already on the page: the id of the line stating it and the level that
   line was written at. See the module header's "claim index". *)
type stated = { s_cid : Writer.cid; s_level : int }

(* M11-complexity-T5 (D-0145, D-0140 J2), M11-complexity-T12 (D-0166). The claim
   index's table. Its key is the clause as a PACKED array, two [int]s per literal of the
   sorted set: the variable's name interned in [ctx.names] with the kind and the sign,
   then the value ([pack_key]). It was the sorted [Lit.t list] itself, and that list was
   the only thing holding its literals: 4.87 M literals in 25 888 keys on
   2011_black-hole_9 at node 40 (a trace line's claim and negated facts), 333 MB at about
   68 bytes a literal (a cons, a [Lit.t], a [Ge] block), where the packed key costs 16.
   The packing is injective (one interned id per name STRING, so two names are one id
   exactly when [String.equal] holds, which is what [Lit.equal] compares), so two keys
   are equal exactly when the sorted literal lists were [List.equal Lit.equal], the
   equality the table had. The hash mixes the first [claim_hash_width] literals and the
   length, now from the packed integers rather than a string hash of each name.
   Nothing iterates this table, so only the cost of a lookup and the bytes a key holds
   change. *)
module Claims = Hashtbl.Make (struct
  type t = int array

  let equal (a : int array) (b : int array) =
    let n = Array.length a in
    n = Array.length b
    &&
    let rec go i = i >= n || (Int.equal a.(i) b.(i) && go (i + 1)) in
    go 0

  (* The first [claim_hash_width] literals (two slots each) and the length. A key is
     sorted, so two clauses that agree on that prefix and length share a bucket and
     [equal] tells them apart. *)
  let claim_hash_width = 8

  let hash (a : int array) =
    let n = Array.length a in
    let m = Stdlib.min n (2 * claim_hash_width) in
    let rec go h i = if i >= m then h else go (mix h a.(i)) (i + 1) in
    finish (mix (go 8 0) (n / 2))
end)

(* M16-file-review-T4 (D-0192): the table of [combine_origin]'s shapes, keyed by the two
   integers packed as one, the count in the high bits. It was a [Writer.Itbl], whose hash
   is the key itself because the writer's keys are consecutive ids, and a bucket is the
   key's LOW bits: every shape of one divisor fell in one bucket, and the lookup walked
   them all (10.6 % of 2013_rcpsp_11's samples with the proof, a chain of every shape of
   divisor 1). [finish] spreads the high bits into the low ones. The table is never
   iterated, and a shape still finds the one closure it shared, so no byte moves. *)
module Shapes = Hashtbl.Make (struct
  type t = int

  let equal = Int.equal
  let hash k = finish k
end)

type ctx = {
  writer : Writer.t;
  encoding : Encoding.t;
  stated : stated Claims.t;
  mutable stated_by_level : int array list array;
      (* M6-T17: the keys each level stated, indexed by level. Level 0 is not recorded
         (M11-complexity-T5): no wipe reaches it. *)
  mutable stated_hi : int;
      (* M2-T9. Clause (as a sorted literal set) -> the line that states it. Read by
         [defining_line] and [defining_lit], written by every clause this module puts on
         the page, wiped by [wipe_level]. Lookup only -- never iterated for emission. *)
  names : (string, int) Hashtbl.t;
  mutable name_of : string array;
      (* M11-complexity-T12 (D-0166): the claim index's interned variable names, both
         ways ([name_of] only to spell a key back in [defining_key]'s message). One
         entry per name a stated clause has named, never wiped: the ids must stay
         stable for as long as a key that uses them can be in [stated]. *)
  combine_origins : (unit -> string) Shapes.t;
      (* M11-complexity-T12 (D-0166): one origin closure per (summands, divisor) shape,
         shared by every [Combine] line of that shape; see [combine_origin]. *)
  serial : int;
  mutable epoch : int;
  mutable wiped_at : int array;
  mutable line_hi : int;
      (* M11-complexity-T13 (D-0168), and since M11-complexity-T15 for every node's line
         too: what tells whether a line a thunk or a node remembers is still on the page. [epoch] counts this [ctx]'s wipes; [wiped_at.(l)] is the epoch of
         the last wipe that reached level [l] (0 if none), stamped by [wipe_level] for
         every level up to [line_hi], the highest level a line was recorded at since. A
         line recorded at level [l] in epoch [e] by the [ctx] whose [serial] it carries
         is live exactly when [wiped_at.(l) <= e]: the condition under which the memo
         entry it replaces would still be in the memo. *)
}

let serials = ref 0

let create ~writer ~encoding =
  incr serials;
  {
    writer;
    encoding;
    stated = Claims.create 64;
    stated_by_level = Array.make 16 [];
    stated_hi = -1;
    names = Hashtbl.create 64;
    name_of = Array.make 64 "";
    combine_origins = Shapes.create 64;
    serial = !serials;
    epoch = 0;
    wiped_at = Array.make 16 0;
    line_hi = -1;
  }

(* The writer a [ctx] emits through. [Learned] needs it to put a constraint on the page
   with a rule this module has no [Explanation.t] for -- a learned constraint is not a
   pruning's justification, it is a new constraint -- and asking for the field is more
   honest than adding an [Explanation] constructor that means "and also remember this". *)
let writer ctx = ctx.writer

(* Backtracking: wipe the writer's level and drop the memo entries it invalidated, in
   one call, so the two structures cannot drift apart. Always call this instead of
   [Writer.wipe_level] directly when a [ctx] is in play. *)
let wipe_level ctx level =
  Writer.wipe_level ctx.writer level;
  if !Explanation.hashcons || Explanation.stats_on then Explanation.hc_wipe level;
  (* M11-complexity-T13 (D-0168), M11-complexity-T15: every line a thunk or a node
     remembers at [level] or above is gone from the page. One stamp per level: the
     nodes are not visited. *)
  if ctx.line_hi >= level then (
    ctx.epoch <- ctx.epoch + 1;
    for l = level to ctx.line_hi do
      ctx.wiped_at.(l) <- ctx.epoch
    done;
    ctx.line_hi <- level - 1);
  for l = level to ctx.stated_hi do
    let keys = ctx.stated_by_level.(l) in
    ctx.stated_by_level.(l) <- [];
    List.iter
      (fun k ->
        match Claims.find_opt ctx.stated k with
        | Some (s : stated) when s.s_level >= level -> Claims.remove ctx.stated k
        | _ -> ())
      keys
  done;
  if ctx.stated_hi >= level then ctx.stated_hi <- level - 1

(* Emit at a chosen level -- [Writer.with_level] with the [ctx]'s two side tables kept
   honest, and the call every learned constraint goes through (M2-L1, D-0045).

   Nothing extra has to be done to them, and that is worth one sentence rather than
   leaving a reader to check: [remember] and [state_clause] both stamp their entry with
   [Writer.current_level] at the moment they are called, and [with_level] moves that
   level for real, so a line emitted inside the bracket is remembered at the bracketed
   level and [wipe_level] leaves it alone for exactly as long as the writer does. The two
   structures cannot drift here for the same reason [wipe_level] above cannot let them
   drift: there is one source of truth for the level and both read it.

   Use it for a constraint that must OUTLIVE the level it was derived at -- which today
   means a learned constraint and nothing else. Every other line in this project belongs
   to the branch that derived it and is retired with it. *)
let with_level ctx level f = Writer.with_level ctx.writer level f

(* ------------------------------------------------------- the claim index (M2-T9) *)

(* The key, or [None] for a clause this index does not describe: the empty clause, and
   any clause whose [Opb] rendering is not the literal *set* its key would claim. See
   the module header. Packed as [Claims] says (M11-complexity-T12, D-0166), in the
   order [Lit.compare] sorts the set. *)
let intern ctx (x : string) =
  match Hashtbl.find_opt ctx.names x with
  | Some i -> i
  | None ->
      let i = Hashtbl.length ctx.names in
      Hashtbl.add ctx.names x i;
      if i >= Array.length ctx.name_of then (
        let a = Array.make (2 * Array.length ctx.name_of) "" in
        Array.blit ctx.name_of 0 a 0 (Array.length ctx.name_of);
        ctx.name_of <- a);
      ctx.name_of.(i) <- x;
      i

let pack_key ctx (sorted : Lit.t list) : int array =
  let a = Array.make (2 * List.length sorted) 0 in
  List.iteri
    (fun i (l : Lit.t) ->
      let kind, x, v =
        match l.Lit.v with
        | Lit.Ge (x, v) -> (0, x, v)
        | Lit.Eq (x, v) -> (1, x, v)
        | Lit.Bit (x, v) -> (2, x, v)
      in
      a.(2 * i) <- (intern ctx x lsl 3) lor (kind lsl 1) lor Bool.to_int l.Lit.positive;
      a.((2 * i) + 1) <- v)
    sorted;
  a

(* [pack_key] read back, for a message only. *)
let unpack_key ctx (a : int array) : Lit.t list =
  List.init
    (Array.length a / 2)
    (fun i ->
      let w = a.(2 * i) and v = a.((2 * i) + 1) in
      let x = ctx.name_of.(w lsr 3) in
      let pv =
        match (w lsr 1) land 3 with
        | 0 -> Lit.Ge (x, v)
        | 1 -> Lit.Eq (x, v)
        | _ -> Lit.Bit (x, v)
      in
      { Lit.v = pv; positive = w land 1 = 1 })

let clause_key ctx (lits : Lit.t list) : int array option =
  match lits with
  | [] -> None
  | _ ->
      let sorted = List.sort_uniq Lit.compare lits in
      if List.compare_lengths sorted lits = 0 then Some (pack_key ctx sorted) else None

(* Record that [cid] states [lits]. The *outermost* line wins when a clause is stated
   more than once: it is the one that survives the most backtracking, so it is the one
   whose level satisfies [defining_line]'s condition for the widest set of callers.
   (Within one [Trace.emit] the trail is walked oldest first, so levels arrive
   non-decreasing and this is almost always the first writer anyway; the comparison is
   here so that "almost always" is not what the index rests on.) *)
let state_key ctx key (cid : Writer.cid) =
  let level = Writer.current_level ctx.writer in
  match Claims.find_opt ctx.stated key with
  | Some s when s.s_level <= level -> ()
  | _ ->
      Claims.replace ctx.stated key { s_cid = cid; s_level = level };
      if level > 0 then (
        if level >= Array.length ctx.stated_by_level then (
          let n = Array.length ctx.stated_by_level in
          let a = Array.make (Stdlib.max (level + 1) (2 * n)) [] in
          Array.blit ctx.stated_by_level 0 a 0 n;
          ctx.stated_by_level <- a);
        ctx.stated_by_level.(level) <- key :: ctx.stated_by_level.(level);
        if level > ctx.stated_hi then ctx.stated_hi <- level)

let state_clause ctx (lits : Lit.t list) (cid : Writer.cid) =
  match clause_key ctx lits with None -> () | Some key -> state_key ctx key cid

(* [defining_line ctx lits] is the id of a line already on the page that states exactly
   the clause [lits], and that a line written *now* may cite: it is at or below the
   current level, so no [w] retires it first (I-S4).

   Under the audit the recorded id is also checked to be live. That is not a fallback --
   it raises rather than quietly minting a fresh line -- because a dead id here means
   this table and [Writer]'s live set have drifted, and the only thing that wipes either
   is [wipe_level], which does both. Making it a fallback would also make *emission*
   depend on whether the audit is on, and the .pbp must not. *)
let defining_key ctx key : Writer.cid option =
  match Claims.find_opt ctx.stated key with
  | Some s when s.s_level <= Writer.current_level ctx.writer ->
      if Writer.auditing ctx.writer && not (Writer.is_live ctx.writer s.s_cid) then
        invalid_arg
          (Printf.sprintf
             "Justify.defining_line: the claim index names @c%d for `%s`, which the \
              proof no longer contains -- the index and the writer's live set have \
              drifted. Only [Justify.wipe_level] may retire either, and it retires both. \
              See justify.ml's claim-index header and I-S4."
             s.s_cid
             (String.concat " " (List.map Lit.to_string (unpack_key ctx key))))
      else Some s.s_cid
  | _ -> None

let defining_line ctx (lits : Lit.t list) : Writer.cid option =
  match clause_key ctx lits with None -> None | Some key -> defining_key ctx key

(* D-0009's missing field, and the whole reason the index exists.

   "A bound fact in a `pol` needs a constraint id, not a literal": a bare literal in a
   [pol] expression is the trivial axiom [l >= 0] and asserts nothing, so a derivation
   that appeals to [l] *holding* must name a constraint that establishes it. Only a
   **unit** line does that -- a multi-literal clause containing [l] establishes nothing
   about [l] on its own -- so this is [defining_line] on the one-literal clause, and the
   answer is [None] exactly when no line has stated [l] outright.

   M4-T7 gave it its caller. [Explanation.Defining (c, l)] is the slot this comment said
   [Combine]/[Cut] did not carry -- a summand that sits where a [Weaken] axiom would and
   cites this lookup's answer instead -- so the ADT gap D-0009 and D-0038 were circling
   is closed on the [pol] side. [emit_summand] below is the call. *)
let defining_lit ctx (l : Lit.t) : Writer.cid option = defining_line ctx [ l ]

(* The atom a literal names is on the page before the line that names it (D-0130
   section 3.3): for an order literal of a BITS variable, [Encoding.ensure_atom] mints
   the `red` pair (once; memoised there). An order variable's literal is a PB variable
   of the .opb and needs nothing; a [Bit] never reaches a clause this module writes. *)
let ensure_lit ctx (l : Lit.t) =
  match l.Lit.v with
  | Lit.Ge (x, v)
    when Encoding.n_bits_vars ctx.encoding > 0 && Encoding.is_bits ctx.encoding x ->
      ignore (Encoding.ensure_atom ctx.encoding ctx.writer x v : Writer.cid * Writer.cid)
  | Lit.Ge _ | Lit.Eq _ | Lit.Bit _ -> ()

let validate_lits ctx lits =
  List.iter
    (fun (l : Lit.t) ->
      let owner = Lit.owner l.Lit.v in
      if not (Encoding.is_declared ctx.encoding owner) then
        invalid_arg
          (Printf.sprintf
             "Justify: literal %s refers to variable %s not declared in this encoding"
             (Lit.to_string l) owner);
      ensure_lit ctx l)
    lits

(* M11-complexity-T13 (D-0168), M11-complexity-T15: the id of a line a thunk or a node
   remembers, if this [ctx] wrote it and it is still on the page (see [ctx]'s
   [wiped_at]): exactly when the memo cell it replaces would still answer. *)
let live ctx (l : Explanation.line) =
  match l with
  | Explanation.Line { cid; level; epoch; owner } ->
      if
        owner = ctx.serial
        && (level >= Array.length ctx.wiped_at || ctx.wiped_at.(level) <= epoch)
      then Some cid
      else None
  | Explanation.No_line -> None

(* A line at [cid], written now: the writer's current level, this [ctx]'s epoch. *)
let new_line ctx cid =
  let level = Writer.current_level ctx.writer in
  if level >= Array.length ctx.wiped_at then (
    let a = Array.make (Stdlib.max (level + 1) (2 * Array.length ctx.wiped_at)) 0 in
    Array.blit ctx.wiped_at 0 a 0 (Array.length ctx.wiped_at);
    ctx.wiped_at <- a);
  if level > ctx.line_hi then ctx.line_hi <- level;
  Explanation.Line { cid; level; epoch = ctx.epoch; owner = ctx.serial }

(* What a node's line answers. Without hash-consing it is what the identity memo
   answered. With it (BAGUETTE_HASHCONS=1) a node is every build of the same content, so
   its line is cited by builds that would each have written their own, and it answers
   only when it is at or below the writer's current level: the claim index's condition 2
   (M2-T9), for the same reason -- an id handed back is kept by the caller for as long as
   the CURRENT level lives (a nogood, a thunk's line), and `w l` retires levels [>= l], so
   only a line at or below that level is sure to outlive it. A deeper line is answered by
   a new one, which the node then remembers. *)
let node_answer ctx (e : Explanation.t) =
  match Explanation.node_line e with
  | Explanation.No_line -> None
  | Explanation.Line { level; _ } as l -> (
      match live ctx l with
      | Some _ as hit when !Explanation.hashcons ->
          if level <= Writer.current_level ctx.writer then hit
          else (
            if memo_stats_on then incr ms_level_misses;
            None)
      | hit -> hit)

(* [e]'s line is [cid], written now. With hash-consing the node enters the table of written nodes at the writer's
   level, which [wipe_level] empties with the level. *)
let remember ctx (e : Explanation.t) cid =
  Explanation.set_node_line e (new_line ctx cid);
  if !Explanation.hashcons || Explanation.stats_on then
    Explanation.hc_written e (Writer.current_level ctx.writer)

(* What [e]'s line answers now, for tests: the id [emit] would hand back without writing. *)
let remembered ctx (e : Explanation.t) = node_answer ctx e

(* Run [write] and remember its line on [e], unless [e]'s line answers. [e] is never a
   [Deferred]: a thunk's line is kept on the thunk ([emit]'s [Deferred] arm). *)
let memoized ctx (e : Explanation.t) (write : unit -> Writer.cid) : Writer.cid =
  if memo_stats_on then incr ms_lookups;
  match node_answer ctx e with
  | Some cid ->
      if memo_stats_on then incr ms_hits;
      cid
  | None ->
      let cid = write () in
      remember ctx e cid;
      cid

(* [Clause lits] -- rup, not pol.

   A [pol] step is a cutting-planes derivation: its content is *computed* from the ids
   and axioms named in its reverse-Polish expression, so emitting one requires knowing
   which existing constraints combine, by which coefficients, into the target. A
   [Clause] carries none of that: it is a bare list of literals that some propagator
   has already determined imply the pruning (a Hall-set argument, a direct-encoding
   disequality, ...), with no record of *how*. There is nothing for a cutting-planes
   expression to name. [rup] is the only rule in the vocabulary that accepts a bare
   target and searches for its own justification, so it is the only one that fits;
   docs/PROOF-FORMAT.md section 4 makes the same call for [int_ne] and [bool_clause].

   M1-T59: and before writing one, ask the claim index whether the page already says
   this. It did, twice out of 34 models, and the roadmap row is right that the fix is a
   question of *who owns the claim* rather than a rendering bug. Both duplicates had the
   same shape: [Trace] had already written the pruning's own line -- claim clause plus
   negated facts -- and then a conflict path asked [Justify] for the id of the very same
   [Clause], which had no way to know and wrote it again.

     root_hole_unsat    @c9 and @c14 are `rup +1 ~v0_ge_0 +1 v0_ge_1 +1 v1_ge_1 >= 1 ;`
     bool_channel_unsat @c6 and @c8  are `rup +1 ~x_ge_2 >= 1 ;`

   Handing back an id this module did not mint is not new -- [Model_row] always has, and
   the memo has since M1-T31 -- so I-X2's "an id you receive is an id you must delete"
   already cannot mean exclusive ownership of an [emit] result, and [Search.solve]
   already retires by [live_ids] rather than by counting what it was handed. *)
let emit_clause ctx lits =
  validate_lits ctx lits;
  (* The key once (M11-complexity-T5, D-0140 J2): it was sorted by [defining_line] and
     again by [state_clause]. *)
  let key = clause_key ctx lits in
  match match key with None -> None | Some k -> defining_key ctx k with
  | Some cid -> cid
  | None ->
      (* The origin is rendered only if something reads it (D-0145, D-0140 J6): the
         writer's audit naming a leaked id, or the mutation knob. *)
      let cid =
        Writer.rup_clause_lazy ctx.writer
          ~origin:(fun () ->
            Printf.sprintf "clause(%s)" (String.concat " " (List.map Lit.to_string lits)))
          lits
      in
      (match key with None -> () | Some k -> state_key ctx k cid);
      cid

(* A clause emitted outside the [Explanation.t] world entirely: docs/DECISIONS.md
   D-0018's trace lines, which state "these bound facts imply that bound" and are
   globally valid with no decision in them. They are deliberately *not* memoised --
   each one is about one trail entry at one moment, two prunings of the same variable
   in the same branch are two different lines, and physical identity of a freshly
   built literal list would never hit the memo anyway. [validate_lits] still applies:
   a propagator handing [Trace] a literal about an undeclared variable should say so
   here, not several lines later inside veripb.

   It *populates* the claim index (M2-T9) and deliberately does not *consult* it. That
   asymmetry is the ownership answer M1-T59 asks for: the trace is the primary record of
   what a branch learned, so it always writes its own line, and everything else asks it
   what is already there. Consulting here would also break two properties [Trace] owns
   -- [emitted_ids] would list one id twice, and [permanent_ids] would hand
   [Search.solve] an id to delete twice, which is an I-X2 violation rather than a saving. *)
(* [~origin] is a thunk (D-0145, D-0140 J6): [Trace] builds it from the line's literals,
   and only the writer's audit and the mutation knob ever render it. [emit_rup_clause]
   below is the same over a string, for [Search]'s bridges. *)
let emit_rup_clause_lazy ctx ~origin lits =
  (* M9-no-proof-T2: no line, no claim-index entry, no literal validated. *)
  if Writer.is_null ctx.writer then Writer.fresh_lazy ctx.writer ~origin
  else (
    validate_lits ctx lits;
    let cid = Writer.rup_clause_lazy ctx.writer ~origin lits in
    state_clause ctx lits cid;
    cid)

let emit_rup_clause ctx ~origin lits =
  emit_rup_clause_lazy ctx ~origin:(fun () -> origin) lits

(* [Linear (terms, rhs)] -- rup of exactly the constraint it states. Not [pol]; see
   D-0009 (docs/DECISIONS.md) for the full story, summarised here because
   docs/PROOF-FORMAT.md section 2 requires a propagator (and by extension, its bridge)
   that can only manage [rup] to say why in its own header.

   The earlier version of this function ignored [terms] and [rhs] entirely and emitted
   [pol <model_id>], restating the model constraint. That was wrong: [Explanation.Linear]
   is used by propagators (see [lib/core/prop/linear.ml]'s [int_lin_le]) to carry a
   restatement of *bound facts*, e.g. "the order-encoding unit literals witnessing the
   current bounds of the other variables" -- a completely different constraint from the
   model row, and the old code silently discarded it.

   The tempting fix -- render [terms >= rhs] as [pol], citing whatever established each
   literal -- does not work, because a [pol] expression cannot state that a literal
   *holds*: a bare literal in one is the trivial axiom [lit >= 0] (true for 0 or 1
   alike), not an assertion that it is 1. Checked directly against a checker -- the
   transcript below is the original 2.0-era one (D-0046 retired that format and its
   checker; the measurement is kept because it is what settled the question):

     f 1                  * model: 1 x1 >= 1
     pol x2
     rup 1 x2 >= 1 ;      * Failed to show '1 x2 >= 1' by reverse unit propagation

   So a bound fact can only be cited by the id of a constraint that already establishes
   it (a decision or an earlier pruning search has logged, per D-0008's levels) -- never
   by naming its literal inside a [pol] expression. [Explanation.t] cannot carry that id
   (D-0003 is still open on whether it ever will), so the only honest rendering today is
   [rup]: state [terms >= rhs] outright and let the checker's own unit-propagation search
   find the already-logged facts that make it true. This is faithful to what the
   explanation claims, unlike the old [pol <model_id>], at the cost of being exactly the
   "checker searches" case docs/PROOF-FORMAT.md section 2 says to avoid when a [pol] is
   available -- it is not available here. *)
let linear_line ctx terms rhs =
  validate_lits ctx (List.map snd terms);
  Opb.ge terms rhs

let write_linear ctx c =
  Writer.rup_lazy ctx.writer
    ~origin:(fun () -> Printf.sprintf "linear: %s" (Opb.constr_to_string c))
    c

let emit_linear ctx terms rhs = write_linear ctx (linear_line ctx terms rhs)

(* [Cut (e1, e2, c1, c2)] -- recurse on both reasons, then combine: c1 * e1 + c2 * e2.

   [Pol.mul] rejects a multiplier below 1, so [c1] and [c2] must be positive; this is
   the same restriction cutting planes always has (a "combination" with a non-positive
   multiplier is not a sound PB addition step). There is no negative-coefficient escape
   hatch here on purpose -- a caller wanting to subtract a reason should be weakening or
   negating literals inside the reason itself, not asking [Cut] to do it, since [Cut]'s
   coefficients are exactly what get handed to [Pol.mul]. *)
(* One [pol], or one [pol] that states what it concludes -- docs/DECISIONS.md D-0043.

   [claim = None] is what every caller got before M2-L0 and is still what [emit] passes:
   a bare [pol], whose content the checker recomputes and never compares against
   anything. [Some c] routes the same expression through [Writer.pol_concluding], which
   writes the derivation, an `ia` stating [c] against it, and a `del` of the derivation,
   and hands back the id of the CLAIM. M1-T51 measured what that buys: a [pol] truncated
   so it derives something strictly weaker than the bound the propagator actually set is
   ACCEPTED bare and REJECTED once the claim is on the page.

   Since D-0131 the only [Some] caller is [emit_stating], whose claim is a PB ROW: a
   learned inequality the checker cannot reach by unit propagation, so the `pol` is the
   statement and the `ia` is what checks our arithmetic against the checker's. A claim
   that is one LITERAL no longer comes here at all -- [emit_concluding] writes it as the
   `rup` the module header describes. *)
let pol_stating ctx ~origin ~claim expr =
  match claim with
  | None -> Writer.pol_lazy ctx.writer ~origin expr
  | Some c -> Writer.pol_concluding_lazy ctx.writer ~origin ~claim:c expr

(* The expression and the origin, with the operands emitted; [emit_cut] writes it (split
   for D-0158's share mode, which D-0172 removed). *)
let cut_line ~emit ctx e1 e2 c1 c2 =
  if c1 < 1 || c2 < 1 then
    invalid_arg
      (Printf.sprintf "Justify.emit: Cut coefficients must be >= 1, got (%d, %d)" c1 c2);
  let id1 = emit ctx e1 in
  let id2 = emit ctx e2 in
  ( Pol.(add (mul (id id1) c1) (mul (id id2) c2)),
    fun () -> Printf.sprintf "cut(%d*%d + %d*%d)" c1 id1 c2 id2 )

let emit_cut ~emit ~claim ctx e1 e2 c1 c2 =
  let expr, origin = cut_line ~emit ctx e1 e2 c1 c2 in
  pol_stating ctx ~claim ~origin expr

(* [Combine (summands, divisor)] -- docs/DECISIONS.md D-0013: the "weaken, divide, add"
   derivation. One [pol] step: every summand's [Pol.t] fragment added left to right,
   then (unless [divisor = 1]) divided.

   A [Term (c, e)] summand recurses through [emit] exactly as [Cut]'s operands do --
   the recursion can legitimately land on an explanation another propagator instance
   built (its own base a [Model_row] naming *that* instance's row, not this one),
   which is exactly why [Model_row] exists (see explanation.ml's header): the id it
   cites is unambiguous regardless of which [ctx] is doing the recursing.

   A [Weaken lits] summand emits no rule and consumes no id: each [(c, l)] becomes
   [Pol.mul (Pol.axiom l) c], folded together with [Pol.add]. This is the one place a
   bare literal is deliberately allowed into a [pol] expression as the *trivial*
   axiom [l >= 0] (D-0009) -- never to assert [l] holds, only to cancel a term whose
   variable is still sitting at its declared bound. [emit_summand] therefore has two
   return shapes (mint an id vs. build a fragment directly); folding both into one
   [Pol.t] before the single [Writer.pol] call is what keeps the whole [Combine] to
   exactly one proof line, matching every step of D-0013's worked example. *)
(* The axiom fold of a [Weaken] (and of an uncited [Linear_term]): one fragment, the
   literals added left to right. Empty for a fixed variable, which [emit_combine] drops. *)
let emit_weaken ctx lits =
  match lits with
  | [] -> []
  | (c0, l0) :: rest ->
      validate_lits ctx (List.map snd lits);
      [
        List.fold_left
          (fun acc (c, l) ->
            if c < 1 then
              invalid_arg
                (Printf.sprintf
                   "Justify.emit: Weaken axiom coefficient must be >= 1, got %d" c);
            Pol.add acc (Pol.mul (Pol.axiom l) c))
          (Pol.mul (Pol.axiom l0) c0)
          rest;
      ]

(* Every summand yields a LIST of fragments that [emit_combine] adds one at a time, in
   order -- the left fold is what the emitted text is, and a [Linear_term] with several
   cited explanations must land as the several [Term]s it replaced, not as one nested
   sum (M8-bits-encoding-T2; the determinism gate holds the text). *)
let emit_summand ~emit ctx = function
  | Explanation.Term (c, e) ->
      if c < 1 then
        invalid_arg
          (Printf.sprintf "Justify.emit: Combine term coefficient must be >= 1, got %d" c);
      let id = emit ctx e in
      [ Pol.mul (Pol.id id) c ]
  (* [Linear_term] in the ORDER arm (D-0132 section 2.4): the declared-range axiom chain
     when nothing is cited (declared bound, or a bound resting on a decision -- I-X9's
     exception), one [Term] at |coeff| per cited explanation otherwise. Byte for byte
     what [Linear] built before T2. A bits term cannot be rendered here at all: its
     order literals are atoms, not .opb variables, and the derivation that names them is
     [emit_bits_pruning]'s. *)
  | Explanation.Linear_term r -> (
      if
        Encoding.n_bits_vars ctx.encoding > 0
        && Encoding.is_bits ctx.encoding r.Explanation.lt_name
      then
        invalid_arg
          (Printf.sprintf
             "Justify.emit: `%s` is on the bits encoding; its row's derivation is \
              written by emit_bits_pruning, never as a bare pol (D-0132 section 2)"
             r.Explanation.lt_name);
      match r.Explanation.lt_cited with
      | [] ->
          let lits, _ =
            Order_reason.weaken_declared ~coeff:r.Explanation.lt_coeff
              ~name:r.Explanation.lt_name ~decl_lo:r.Explanation.lt_decl_lo
              ~decl_hi:r.Explanation.lt_decl_hi
          in
          emit_weaken ctx lits
      | es ->
          let c = Stdlib.abs r.Explanation.lt_coeff in
          List.map (fun e -> Pol.mul (Pol.id (emit ctx e)) c) es)
  (* [Defining (c, l)] -- D-0009's other half (M4-T7, explanation.ml's header).

     A [Weaken] puts [l] in as the trivial axiom, which cancels the term and costs one
     unit of degree per copy; this cites the id of the line that ESTABLISHES [l], which
     cancels the same term and keeps the degree. [defining_lit] is the lookup, and where
     no line has stated [l] outright this states it -- [emit_clause] consults the index
     once more and mints a one-literal [rup] only if it really is not there.

     EITHER WAY THE CITED LINE IS A UNIT, and that is the property the rest of the system
     reads off this constructor: a unit's cancellation is exact, so a derivation holding
     one still derives what its arithmetic says, which is why [Search.rests_on_a_clause]
     does not have to route a conflict carrying one away from its own [pol]. A [Clause]
     summand cannot promise that, which is exactly what D-0061 recorded going wrong.

     The soundness precondition -- that [l] is a consequence of the model rather than of
     a decision -- belongs to the caller and cannot be checked here: the writer's current
     level says where we are, not where the bound came from. [Alldiff] tests the level the
     bound was ESTABLISHED at; a caller that does not is writing a false unit and the
     checker will say so. *)
  | Explanation.Defining (c, l) ->
      if c < 1 then
        invalid_arg
          (Printf.sprintf
             "Justify.emit: Combine defining coefficient must be >= 1, got %d" c);
      validate_lits ctx [ l ];
      let id =
        match defining_lit ctx l with Some id -> id | None -> emit_clause ctx [ l ]
      in
      [ Pol.mul (Pol.id id) c ]
  | Explanation.Weaken lits -> emit_weaken ctx lits

(* The expression and the origin, with the operands emitted; [emit_combine] writes it
   (split for D-0158's share mode, which D-0172 removed). *)
(* The origin of a [Combine] line, which the writer's audit keeps for as long as the line
   is live. It renders two integers, so every line of one shape can share one closure
   (M11-complexity-T12, D-0166): a closure per line was 40 bytes for each of the 3.1 M
   live `pol` lines of 2011_black-hole_9 at node 40, and the shapes are a few hundred. The
   string it renders is the same. The table is [Shapes], whose hash mixes the key: see
   there why the writer's identity-hashed table was quadratic in the shapes here. *)
let combine_origin ctx n_summands divisor =
  let o () = Printf.sprintf "combine(%d summand(s), / %d)" n_summands divisor in
  (* The key packs both integers, so it is shared only where both fit in 31 bits (both
     are positive: a count, and a divisor [>= 1]); a shape outside that keeps its own. *)
  if n_summands >= 1 lsl 31 || divisor < 0 || divisor >= 1 lsl 31 then o
  else
    let k = (n_summands lsl 31) lor divisor in
    match Shapes.find_opt ctx.combine_origins k with
    | Some shared -> shared
    | None ->
        Shapes.add ctx.combine_origins k o;
        o

let combine_line ~emit ctx summands divisor =
  (* A [Weaken []] summand is a variable with NOTHING to weaken: declared on a single
     value (`var 7..7`), it has no order literal at all -- its whole contribution to the
     row is the constant the encoding already folded into the degree -- so
     [Order_reason.weaken_declared] builds an empty chain for it. D-0013's arithmetic is
     unchanged by a summand of zero axioms, and the division step still lands on the unit
     coefficient. It is dropped here rather than refused: refusing it was the
     `Invalid_argument` M7-T19 reproduced with `var 1..3: x; var 7..7: s;
     constraint int_le(s, x);` at the ROOT (exit 2 on a legal model, found 2026-10-01).
     [emit_summand]'s own check below stays, for a [Weaken []] that reaches it any other
     way. *)
  let summands =
    List.filter
      (function
        | Explanation.Weaken [] -> false
        | Explanation.Linear_term r ->
            (* A fixed variable, uncited: the same empty chain as [Weaken []]. *)
            not (r.Explanation.lt_cited = [] && Explanation.lt_width r <= 0)
        | _ -> true)
      summands
  in
  (match summands with
  | [] -> invalid_arg "Justify.emit: Combine must have at least one summand"
  | _ -> ());
  let frags = List.concat_map (emit_summand ~emit ctx) summands in
  let expr =
    match frags with
    | [] -> invalid_arg "Justify.emit: Combine must have at least one summand"
    | f :: rest -> List.fold_left Pol.add f rest
  in
  let expr = if divisor <= 1 then expr else Pol.div expr divisor in
  (* The count now, so that the origin, which the audit keeps for as long as the line
     is live, holds two integers and not the summands. *)
  (expr, combine_origin ctx (List.length summands) divisor)

let emit_combine ~emit ~claim ctx summands divisor =
  let expr, origin = combine_line ~emit ctx summands divisor in
  pol_stating ctx ~claim ~origin expr

(* The fragment one [Linear_term] contributes to a bits-arm `pol`, shared by the
   [Combine] rendering (D-0132) and the [Resolve] one (D-0134): the bound line scaled by
   |a| when the bound it read is the declared one, the bridge scaled by |a| otherwise --
   and in that case the term's negated literal is pushed on [neg_facts_rev], oldest
   first after reversal, which is the order the derived clause lists them in. [None]
   for a fixed variable, which has nothing to weaken. *)
let bits_term_fragment ctx neg_facts_rev (r : Explanation.linear_term) =
  let w = ctx.writer and enc = ctx.encoding in
  let c = Stdlib.abs r.Explanation.lt_coeff and x = r.Explanation.lt_name in
  match Explanation.lt_lit r with
  | None ->
      if Explanation.lt_width r <= 0 then None (* a fixed variable: nothing to weaken *)
      else
        let lb, ub = Encoding.bound_lines enc w x in
        Some (Pol.mul (Pol.id (if r.Explanation.lt_coeff > 0 then lb else ub)) c)
  | Some l ->
      validate_lits ctx [ l ];
      (* [x >= v] cites B1 at v; [x <= v] is [~x_ge_(v+1)] and cites B2 at v+1:
         [Lit.value] is the atom's value either way. *)
      let b1, b2 = Encoding.ensure_atom enc w x (Lit.value l.Lit.v) in
      neg_facts_rev := Lit.negate l :: !neg_facts_rev;
      Some (Pol.mul (Pol.id (if l.Lit.positive then b1 else b2)) c)

(* The summands of one bits-arm [Combine], as `pol` fragments: the row(s) and the terms.
   Anything else in a bits derivation is a propagator's mistake and is named. *)
let bits_summand_fragment ctx neg_facts_rev = function
  | Explanation.Term (c, Explanation.Model_row id) -> Some (Pol.mul (Pol.id id) c)
  | Explanation.Linear_term r -> bits_term_fragment ctx neg_facts_rev r
  | s ->
      invalid_arg
        (Printf.sprintf
           "Justify.emit_bits_pruning: a summand that is not a Linear term: %s"
           (Explanation.summand_to_string s))

let bits_sum frags =
  match frags with
  | [] -> invalid_arg "Justify.emit_bits_pruning: empty derivation"
  | f :: rest -> List.fold_left Pol.add f rest

(* D-0134 section 2.2: each part saturated to its clause (a [Combine]: its fragments
   summed, divided, saturated; a [Model_row]: cited as it is), the parts summed and
   saturated once more. The clause derived is every part's negated literal, without
   duplicates, in part order -- the claim is one of them, carried by the part that
   assumed its negation, and is checked to be. No atom is added for it. *)
let emit_bits_resolve ctx ~origin ~(concludes : Reason.fact option) parts =
  let w = ctx.writer and enc = ctx.encoding in
  let neg_facts_rev = ref [] in
  let part (e : Explanation.t) =
    match Explanation.force e with
    | Explanation.Model_row id -> Pol.id id
    | Explanation.Combine { summands; divisor; _ } ->
        let frags = List.filter_map (bits_summand_fragment ctx neg_facts_rev) summands in
        let expr = bits_sum frags in
        Pol.saturate (if divisor <= 1 then expr else Pol.div expr divisor)
    | other ->
        invalid_arg
          (Printf.sprintf
             "Justify.emit_bits_pruning: a Resolve part that is neither a Combine nor a \
              model row: %s"
             (Explanation.to_string other))
  in
  let expr = Pol.saturate (bits_sum (List.map part parts)) in
  let clause =
    List.fold_left
      (fun acc l -> if List.exists (Lit.equal l) acc then acc else acc @ [ l ])
      [] (List.rev !neg_facts_rev)
  in
  (* The claim is normally one of those literals (D-0134 section 2.3), and then [Trace]
     takes the `ia` as the line. Not always: a claim that SETTLED past a hole -- an
     operand of maxmin, or a disequality's own variable, with an interior hole beside
     the value -- is a stronger bound than the clause's literal, and [Trace] then writes
     its ordinary `rup` after this line, RUP in sequence through the hole's own line
     (D-0132 section 2.5's rule, which a [Resolve] obeys as a [Combine] does). So the
     claim is validated, and nothing is refused for it. *)
  Option.iter
    (fun l -> validate_lits ctx [ l ])
    (Option.bind concludes Reason.lit_of_fact);
  (* The origin names the shape, so a mutation lane can aim at a choice derivation and
     not at the first [Linear] bits line that happens to precede it. *)
  let cid =
    Writer.pol_concluding w ~origin:(origin ^ " [resolve]") ~claim:(Opb.clause clause)
      expr
  in
  Encoding.note_bits_pruning enc;
  state_clause ctx clause cid;
  (cid, clause)

(* The clause a [Resolve] derives, computed without writing anything: every part's
   [Linear_term] literal negated, deduplicated, in part order -- what [emit_bits_resolve]
   pins. Used by [emit]'s citation arm to find the line already stating it. *)
let resolve_clause parts =
  let acc = ref [] in
  let add l = if not (List.exists (Lit.equal l) !acc) then acc := l :: !acc in
  List.iter
    (fun e ->
      match Explanation.force e with
      | Explanation.Combine { summands; divisor = _; _ } ->
          List.iter
            (function
              | Explanation.Linear_term r -> (
                  match Explanation.lt_lit r with
                  | Some l -> add (Lit.negate l)
                  | None -> ())
              | _ -> ())
            summands
      | _ -> ())
    parts;
  List.rev !acc

(* The line a released thunk's derivation was written as, if it is still on the page. *)
let live_line ctx (th : Explanation.thunk) = live ctx (Explanation.line_of th)

(* [emit ctx e] renders [e] into proof rules through [Writer] and returns the id of the
   resulting constraint.

   - [Model_row id] costs nothing: [id] is already the constraint's id, no lookup and
     no rule.
   - [Decision] is the one constructor with no rendering at all, and the refusal is
     the point rather than an omission. Nothing in the proof establishes a decision
     (D-0009: a [pol] cannot assert a literal, a [rup] cannot derive a non-consequence),
     so there is no id to return and no rule to write; the decisions reach the proof
     negated, in the branch's nogood, and nowhere else (D-0018). Reaching here means a
     caller asked for the id of an assumption -- which is what M1-T50 was, silently
     answered with the ambient model row. [Explanation.term] and [Explanation.cut]
     refuse to build a citation out of a decision, so the only way in is a direct
     [emit] on one.
   - Every other constructor is memoised on [e]'s physical identity (see the module
     header) before doing any work, so asking for the same explanation twice is free
     the second time.
   - [Deferred] is forced -- never call its thunk directly, [Explanation.force] is what
     memoises it -- and the result is recursed on. Forcing happens *inside* the memo
     lookup for the [Deferred] node itself, so a [Deferred] demanded twice neither
     forces its thunk twice (that guarantee is [Explanation.force]'s) nor re-emits the
     inner explanation's rule twice (that guarantee is this memo). *)
let rec emit ctx (e : Explanation.t) : Writer.cid =
  match e with
  | Explanation.Decision l ->
      invalid_arg
        (Printf.sprintf
           "Justify.emit: a decision (%s) has no constraint id -- nothing in the proof \
            establishes it. A decision reaches the proof only negated, in its branch's \
            nogood (D-0018). See justify.ml's [emit] header and M1-T50."
           (Lit.to_string l))
  | Explanation.Model_row id -> id
  (* M9-no-proof-T2 (D-0126): under `--no-proof` the writer is null, and the guard sits
     HERE, before the memo and before anything is forced -- a [Deferred] thunk is never
     run for the proof's sake, and no literal is validated or rendered. The id handed
     back is distinct and stands for nothing; [Model_row] above and [Decision] before it
     keep their arms, because the first is an id the model already has and the second
     is a caller's mistake in both modes. *)
  | _ when Writer.is_null ctx.writer -> Writer.fresh ctx.writer ~origin:"no-proof"
  | Explanation.Clause { lits; _ } -> memoized ctx e (fun () -> emit_clause ctx lits)
  | Explanation.Linear { terms; rhs; _ } ->
      memoized ctx e (fun () -> emit_linear ctx terms rhs)
  | Explanation.Cut { e1; e2; c1; c2; _ } ->
      memoized ctx e (fun () -> emit_cut ~emit ~claim:None ctx e1 e2 c1 c2)
  | Explanation.Combine { summands; divisor; _ } ->
      memoized ctx e (fun () -> emit_combine ~emit ~claim:None ctx summands divisor)
  | Explanation.Deferred th -> (
      match live_line ctx th with
      | Some cid ->
          if memo_stats_on then incr ms_line_hits;
          cid
      | None -> emit_thunk ctx e th)
  (* M8-bits-encoding-T3 (D-0134 section 2.6, and its deviation in section 5): a
     [Resolve] is written by [emit_bits_pruning] as the trace line of the entry it
     justifies. It reaches here only as a CITATION -- an order-arm derivation whose
     [Linear_term] cites the entry that moved an order variable of a maxmin scope with a
     bits operand (D-0132 section 2.4's [Term] per cited explanation). The clause it
     derives is C_v, exactly what the per-value shape's [Clause] cited, so the answer is
     the line stating it: the trace line when it is on the page, else the same `pol` +
     `ia` written now. *)
  | Explanation.Resolve { parts; _ } ->
      memoized ctx e (fun () ->
          match defining_line ctx (resolve_clause parts) with
          | Some cid -> cid
          | None ->
              fst
                (emit_bits_resolve ctx ~origin:"bits resolve (cited)" ~concludes:None
                   parts))

(* M11-complexity-T13 (D-0168): write a thunk's derivation and RELEASE it -- record the
   line on the thunk and drop its tree, so that nothing holds the tree once it is
   written. A thunk released before whose line has since been wiped comes here again, is
   forced again through its closure, and its derivation is written again.

   M11-complexity-T15: nothing else is let go of. Until T15 the memo's cells held the
   tree's nodes, and the release took out the cells of the nodes the closure BUILT, which
   took a frame recording every build and, where the tree might hold a node it had not
   built, a second forcing to tell the two apart. Each node now carries its own line and
   no table holds it, so the tree is collectable the moment [forced] lets it go, and a
   node another derivation holds keeps its line because it is that derivation's node.

   The thunk takes the line of the node its tree is when that node answered (the tree
   was already written): the same id, with the level and epoch that line really has.
   It used to take the writer's current level whatever the answer was, which states a
   shorter life than the line has when the line is shallower (the thunk was then written
   again, to the same id, once its own level was wiped) and a longer one when it is
   deeper (possible only inside [with_level], where the thunk could then be cited after
   its line was gone). A line written now is at the current level either way. *)
and emit_thunk ctx e (th : Explanation.thunk) =
  let again = Explanation.line_of th <> Explanation.No_line in
  let tree = Explanation.force e in
  if again then incr Explanation.reforced_emit;
  let cid = emit ctx tree in
  if Debug.enabled && not (Explanation.same_derivation tree (Explanation.reforce th)) then
    failwith
      (Printf.sprintf
         "invariant violated: I-X6 (M11-complexity-T13): forcing the thunk of line %d \
          again does not give the derivation it was written from"
         cid);
  let line =
    match Explanation.node_line tree with
    | Explanation.Line { cid = c; _ } as l when c = cid && live ctx l = Some cid -> l
    | _ -> new_line ctx cid
  in
  Explanation.release th line;
  cid

(* M2-L6: emit [e] as a [pol] that STATES the constraint [claim], where [e] renders to a
   [pol] at all.

   [emit_concluding] below does the same thing for a pruning, whose claim is always a
   one-literal constraint read off a [Reason.fact]. A learned PB inequality is not a
   literal and not a bound, so it cannot go through that door; what it has is an [Opb.t]
   it believes the derivation evaluates to. The value of saying so is described at
   [Pb_analysis.introduce]: it makes the checker compare our arithmetic against its own,
   at the line where they would first differ.

   The three constructors that are not a [pol] fall through to [emit] unchanged, exactly
   as they do in [emit_concluding], and for the same reason: there is no expression for an
   `ia` to conclude from. A [Model_row] in particular returns an id that is already on the
   page and states nothing, so a caller that needs the claim checked must hand this
   function a derivation with at least one real step in it -- [Pb_analysis] guarantees
   that by refusing to learn at zero eliminations. *)
let emit_stating ctx ~(claim : Opb.constr) (e : Explanation.t) : Writer.cid =
  let rec go (e : Explanation.t) =
    match e with
    | Explanation.Cut { e1; e2; c1; c2; _ } ->
        emit_cut ~emit ~claim:(Some claim) ctx e1 e2 c1 c2
    | Explanation.Combine { summands; divisor; _ } ->
        emit_combine ~emit ~claim:(Some claim) ctx summands divisor
    | Explanation.Deferred _ -> go (Explanation.force e)
    | Explanation.Clause { lits = _; _ }
    | Explanation.Linear _ | Explanation.Model_row _ | Explanation.Decision _
    | Explanation.Resolve { parts = _; _ } ->
        emit ctx e
  in
  (* M9-no-proof-T2: nothing stated and nothing forced; see [emit]. *)
  if Writer.is_null ctx.writer then Writer.fresh ctx.writer ~origin:"no-proof: stated"
  else go e

(* D-0132 section 2.1: [Linear]'s row, every term weakened by its bridge or bound line,
   divided by the pruned term's coefficient, closed by the pruned variable's own atom. *)
let emit_bits_combine ctx ~origin ~(concludes : Reason.fact option) summands divisor =
  let w = ctx.writer and enc = ctx.encoding in
  let neg_facts_rev = ref [] in
  let frags = List.filter_map (bits_summand_fragment ctx neg_facts_rev) summands in
  let expr = bits_sum frags in
  let expr = if divisor <= 1 then expr else Pol.div expr divisor in
  let claim =
    match Option.bind concludes Reason.lit_of_fact with
    | None ->
        if concludes <> None then
          invalid_arg
            "Justify.emit_bits_pruning: a bits conclusion at its declared bound (nothing \
             to claim)";
        []
    | Some l ->
        validate_lits ctx [ l ];
        let b1, b2 = Encoding.ensure_atom enc w (Lit.owner l.Lit.v) (Lit.value l.Lit.v) in
        (* The pruned variable's own atom: an upper push [x <= u] is [~x_ge_(u+1)] and
           cites B1 at u+1; a lower push [x >= l] cites B2 at l. *)
        [ (l, if l.Lit.positive then b2 else b1) ]
  in
  let expr = List.fold_left (fun acc (_, b) -> Pol.add acc (Pol.id b)) expr claim in
  let clause = List.map fst claim @ List.rev !neg_facts_rev in
  let expr = if clause = [] then expr else Pol.saturate expr in
  let cid = Writer.pol_concluding w ~origin ~claim:(Opb.clause clause) expr in
  Encoding.note_bits_pruning enc;
  state_clause ctx clause cid;
  (cid, clause)

(* Whether [emit_bits_pruning] can render [e] (forced): a [Combine] of [Linear]'s shape --
   every summand the row cited as [Term (_, Model_row _)] or a [Linear_term] -- or a
   [Resolve] of such parts and model rows. Anything else is not a bits derivation even
   when its scope holds a bits variable, and keeps the order arm's line: a LEARNED
   constraint's conflict or pruning is the case that exists (a row citing the entries
   that falsified its literals; its literals are atoms, so its `rup` is unit propagation
   over the learned line itself). Found by the suite at `W = 0` once T3 released `int_ne`
   (D-0134 section 5): element_learn_hole_{sat,unsat} learned a clause over `y`'s atoms
   and its conflict reached the bits arm, which refused the [Term] it could not render. *)
let rec is_bits_derivation (e : Explanation.t) =
  let summand = function
    | Explanation.Term (_, t) -> (
        match Explanation.force t with Explanation.Model_row _ -> true | _ -> false)
    | Explanation.Linear_term _ -> true
    | Explanation.Weaken _ | Explanation.Defining _ -> false
  in
  match Explanation.force e with
  | Explanation.Combine { summands; divisor = _; _ } -> List.for_all summand summands
  | Explanation.Resolve { parts; _ } ->
      List.for_all
        (fun p ->
          match Explanation.force p with
          | Explanation.Model_row _ -> true
          | Explanation.Combine _ -> is_bits_derivation p
          | _ -> false)
        parts
  | _ -> false

(* M8-bits-encoding-T2: the BITS arm's trace line -- the module header's "The BITS arm"
   says what the `pol` is and why it derives exactly the trace clause. [concludes] is
   the pruning's own claim ([Reason.justified]'s third half, D-0043), [None] for a
   conflict. Returns the id of the `ia` line, which IS the clause, and the clause it
   states (claim first, then the facts negated in snapshot order), so [Trace] can tell
   whether its own line is that clause (always, unless the claim settled past a hole,
   which only an order variable in an [Ne] scope can do) or must follow it as a `rup`.
   Precondition: [e] forces to [Linear]'s [Combine] shape -- the row as [Term (1,
   Model_row)] and every other summand a [Linear_term] -- or (M8-bits-encoding-T3,
   D-0134) to a choice derivation's [Resolve]; anything else is a caller's mistake and
   says so here. *)
let emit_bits_pruning ctx ~origin ~(concludes : Reason.fact option) (e : Explanation.t) :
    Writer.cid * Lit.t list =
  match Explanation.force e with
  | Explanation.Combine { summands; divisor; _ } ->
      emit_bits_combine ctx ~origin ~concludes summands divisor
  | Explanation.Resolve { parts; _ } -> emit_bits_resolve ctx ~origin ~concludes parts
  | other ->
      invalid_arg
        (Printf.sprintf "Justify.emit_bits_pruning: not a bits derivation: %s"
           (Explanation.to_string other))

(* M8-bits-encoding-T5 (D-0131): a [Combine] or [Cut] that concludes a LITERAL is
   written as `rup <literal> >= 1 ;` -- the module header says why, and this comment
   says what the line rests on, because a `rup` is only as good as the database it is
   checked against.

   What the checker needs on the page is every bound the derivation CITES, as a line it
   can unit-propagate to: a [Term] summand's conclusion as a unit (or as a trace clause
   whose other literals are already forced), and a [Defining]'s literal likewise. The
   derivation's own summands are therefore NOT emitted here -- a [Term]'s explanation is
   not recursed into, and a [Weaken] has nothing to put on the page in any rule -- and
   the obligation moves to the caller, which is the same obligation every D-0018 trace
   line already carries: [Trace.emit] writes the trail oldest first, so each line's facts
   precede it. A caller that asks for a concluding derivation whose premises are not on
   the page gets the checker's "not implied by reverse unit propagation", at this line,
   and never a weaker constraint quietly accepted; that is the trade D-0043 asked for
   from the `ia`, made by the rule itself.

   The literal goes through [emit_clause], i.e. through the claim index: if the trace
   has already stated it, that id is handed back (M1-T59's ownership answer, and I-S4
   holds because [defining_line] only answers with a line at or below the current
   level); otherwise one `rup` is minted and indexed, so a later [Defining] or [Clause]
   asking for the same literal finds it. It deliberately still does not touch the memo:
   the memo maps an explanation to the id of the constraint EMITTED FOR IT as a row, and
   a unit stating its bound is a strictly weaker object than the row a parent [Cut]
   would ask [emit] for -- the silent-weakening failure D-0043 exists to close.

   Four cases fall through to [emit], each for its own reason:

     - [None], or a conclusion at its declared bound: there is no literal to claim
       (PROOF-FORMAT section 3 states that bound as the constant true).
     - [Clause] and [Linear] are `rup` already and name their own target.
     - [Model_row] mints no line; its id is the row's, and a bound stated against it
       would claim the ROW implies the bound, the D-0020 restatement defect.
     - [Decision] raises, in [emit], as it must. *)
let emit_concluding ctx ~(concludes : Reason.fact option) (e : Explanation.t) : Writer.cid
    =
  match Option.bind concludes Reason.lit_of_fact with
  | None -> emit ctx e
  (* M9-no-proof-T2: nothing concluded and nothing forced; see [emit]. *)
  | Some _ when Writer.is_null ctx.writer ->
      Writer.fresh ctx.writer ~origin:"no-proof: concluding"
  | Some l -> (
      (* The same hygiene [emit_clause] applies to a reason's literals: a conclusion
         about a variable this encoding never declared is a caller's mistake and says
         so here, not several lines later inside veripb. *)
      validate_lits ctx [ l ];
      match Explanation.force e with
      | Explanation.Cut _ | Explanation.Combine _ -> emit_clause ctx [ l ]
      | Explanation.Clause { lits = _; _ }
      | Explanation.Linear _ | Explanation.Model_row _ | Explanation.Decision _
      | Explanation.Deferred _
      | Explanation.Resolve { parts = _; _ } ->
          emit ctx e)
