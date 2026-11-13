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
       cannot be a [Hashtbl] and this can).
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

type memo_entry = { cid : Writer.cid; level : int }

(* M6-T9 (a cross-session PROPOSAL, D-0080). The memo keyed by physical identity, as
   before, but bucketed by a SHALLOW structural hash so a lookup is O(bucket) and not
   O(every explanation emitted since the last wipe). The hash never descends into a
   [Deferred] (its [thunk] is mutable, which is the trap the header names), nor into a
   [Cut]/[Term] operand beyond its constructor, so forcing a thunk cannot move a key.
   Equality inside a bucket is still [==], so the memo's meaning is unchanged. [by_level]
   records which keys each level inserted, so [wipe_level] removes exactly those. *)
and memo_table = {
  tbl : (int, (Explanation.t * memo_entry) list) Hashtbl.t;
  by_level : (int, Explanation.t list) Hashtbl.t;
  mutable memo_hi : int; (* M6-T17: no [by_level] key above this *)
}

let shallow_tag (e : Explanation.t) =
  match e with
  | Explanation.Decision _ -> 0
  | Explanation.Clause _ -> 1
  | Explanation.Linear _ -> 2
  | Explanation.Cut _ -> 3
  | Explanation.Model_row i -> 4 + (16 * i)
  | Explanation.Combine _ -> 5
  | Explanation.Deferred _ -> 6

let shallow_hash (e : Explanation.t) =
  match e with
  | Explanation.Decision l -> Hashtbl.hash (0, l)
  | Explanation.Clause ls -> Hashtbl.hash (1, ls)
  | Explanation.Linear (ts, r) -> Hashtbl.hash (2, ts, r)
  | Explanation.Cut (a, b, c1, c2) ->
      Hashtbl.hash (3, shallow_tag a, shallow_tag b, c1, c2)
  | Explanation.Model_row i -> Hashtbl.hash (4, i)
  | Explanation.Combine (ss, d) ->
      Hashtbl.hash
        ( 5,
          d,
          List.map
            (function
              | Explanation.Term (c, t) -> Hashtbl.hash (c, shallow_tag t)
              | Explanation.Weaken ls -> Hashtbl.hash (1, ls)
              | Explanation.Defining (c, l) -> Hashtbl.hash (2, c, l))
            ss )
  | Explanation.Deferred _ -> 6

(* A claim that is already on the page: the id of the line stating it and the level that
   line was written at. See the module header's "claim index". *)
type stated = { s_cid : Writer.cid; s_level : int }

type ctx = {
  writer : Writer.t;
  encoding : Encoding.t;
  memo : memo_table;
      (* Boxed behind a ref for the same reason it always was -- it is proof state,
         shared by every view of the same writer -- although since M1-T31 removed
         [for_constraint] there is only ever one view. *)
  stated : (Lit.t list, stated) Hashtbl.t;
  stated_by_level : (int, Lit.t list list) Hashtbl.t; (* M6-T17: keys each level stated *)
  mutable stated_hi : int;
      (* M2-T9. Clause (as a sorted literal set) -> the line that states it. Read by
         [defining_line] and [defining_lit], written by every clause this module puts on
         the page, wiped by [wipe_level]. Lookup only -- never iterated for emission. *)
}

let create ~writer ~encoding =
  {
    writer;
    encoding;
    memo = { tbl = Hashtbl.create 1024; by_level = Hashtbl.create 16; memo_hi = -1 };
    stated = Hashtbl.create 64;
    stated_by_level = Hashtbl.create 16;
    stated_hi = -1;
  }

(* The writer a [ctx] emits through. [Learned] needs it to put a constraint on the page
   with a rule this module has no [Explanation.t] for -- a learned constraint is not a
   pruning's justification, it is a new constraint -- and asking for the field is more
   honest than adding an [Explanation] constructor that means "and also remember this". *)
let writer ctx = ctx.writer

let find_memo ctx (e : Explanation.t) =
  let rec go = function
    | [] -> None
    | (k, m) :: rest -> if k == e then Some m else go rest
  in
  match Hashtbl.find_opt ctx.memo.tbl (shallow_hash e) with
  | None -> None
  | Some bucket -> go bucket

let remember ctx (e : Explanation.t) (cid : Writer.cid) : Writer.cid =
  let level = Writer.current_level ctx.writer in
  let h = shallow_hash e in
  let bucket = Option.value (Hashtbl.find_opt ctx.memo.tbl h) ~default:[] in
  Hashtbl.replace ctx.memo.tbl h ((e, { cid; level }) :: bucket);
  Hashtbl.replace ctx.memo.by_level level
    (e :: Option.value (Hashtbl.find_opt ctx.memo.by_level level) ~default:[]);
  if level > ctx.memo.memo_hi then ctx.memo.memo_hi <- level;
  cid

(* Backtracking: wipe the writer's level and drop the memo entries it invalidated, in
   one call, so the two structures cannot drift apart. Always call this instead of
   [Writer.wipe_level] directly when a [ctx] is in play. *)
let wipe_level ctx level =
  Writer.wipe_level ctx.writer level;
  (* M6-T17: walk levels [level, memo_hi] only, and the [stated] keys the same way,
     rather than folding every table. *)
  let doomed = ref [] in
  for l = level to ctx.memo.memo_hi do
    match Hashtbl.find_opt ctx.memo.by_level l with
    | Some es -> doomed := (l, es) :: !doomed
    | None -> ()
  done;
  if ctx.memo.memo_hi >= level then ctx.memo.memo_hi <- level - 1;
  List.iter
    (fun (l, es) ->
      Hashtbl.remove ctx.memo.by_level l;
      List.iter
        (fun e ->
          let h = shallow_hash e in
          match Hashtbl.find_opt ctx.memo.tbl h with
          | None -> ()
          | Some bucket -> (
              match List.filter (fun (_, (m : memo_entry)) -> m.level < level) bucket with
              | [] -> Hashtbl.remove ctx.memo.tbl h
              | b -> Hashtbl.replace ctx.memo.tbl h b))
        es)
    !doomed;
  for l = level to ctx.stated_hi do
    match Hashtbl.find_opt ctx.stated_by_level l with
    | None -> ()
    | Some keys ->
        Hashtbl.remove ctx.stated_by_level l;
        List.iter
          (fun k ->
            match Hashtbl.find_opt ctx.stated k with
            | Some (s : stated) when s.s_level >= level -> Hashtbl.remove ctx.stated k
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
   the module header. *)
let clause_key (lits : Lit.t list) : Lit.t list option =
  match lits with
  | [] -> None
  | _ ->
      let sorted = List.sort_uniq Lit.compare lits in
      if List.compare_lengths sorted lits = 0 then Some sorted else None

(* Record that [cid] states [lits]. The *outermost* line wins when a clause is stated
   more than once: it is the one that survives the most backtracking, so it is the one
   whose level satisfies [defining_line]'s condition for the widest set of callers.
   (Within one [Trace.emit] the trail is walked oldest first, so levels arrive
   non-decreasing and this is almost always the first writer anyway; the comparison is
   here so that "almost always" is not what the index rests on.) *)
let state_clause ctx (lits : Lit.t list) (cid : Writer.cid) =
  match clause_key lits with
  | None -> ()
  | Some key -> (
      let level = Writer.current_level ctx.writer in
      match Hashtbl.find_opt ctx.stated key with
      | Some s when s.s_level <= level -> ()
      | _ ->
          Hashtbl.replace ctx.stated key { s_cid = cid; s_level = level };
          Hashtbl.replace ctx.stated_by_level level
            (key :: Option.value (Hashtbl.find_opt ctx.stated_by_level level) ~default:[]);
          if level > ctx.stated_hi then ctx.stated_hi <- level)

(* [defining_line ctx lits] is the id of a line already on the page that states exactly
   the clause [lits], and that a line written *now* may cite: it is at or below the
   current level, so no [w] retires it first (I-S4).

   Under the audit the recorded id is also checked to be live. That is not a fallback --
   it raises rather than quietly minting a fresh line -- because a dead id here means
   this table and [Writer]'s live set have drifted, and the only thing that wipes either
   is [wipe_level], which does both. Making it a fallback would also make *emission*
   depend on whether the audit is on, and the .pbp must not. *)
let defining_line ctx (lits : Lit.t list) : Writer.cid option =
  match clause_key lits with
  | None -> None
  | Some key -> (
      match Hashtbl.find_opt ctx.stated key with
      | Some s when s.s_level <= Writer.current_level ctx.writer ->
          if Writer.auditing ctx.writer && not (Writer.is_live ctx.writer s.s_cid) then
            invalid_arg
              (Printf.sprintf
                 "Justify.defining_line: the claim index names @c%d for `%s`, which the \
                  proof no longer contains -- the index and the writer's live set have \
                  drifted. Only [Justify.wipe_level] may retire either, and it retires \
                  both. See justify.ml's claim-index header and I-S4."
                 s.s_cid
                 (String.concat " " (List.map Lit.to_string key)))
          else Some s.s_cid
      | _ -> None)

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

let validate_lits ctx lits =
  List.iter
    (fun (l : Lit.t) ->
      let owner = Lit.owner l.Lit.v in
      if not (Encoding.is_declared ctx.encoding owner) then
        invalid_arg
          (Printf.sprintf
             "Justify: literal %s refers to variable %s not declared in this encoding"
             (Lit.to_string l) owner))
    lits

(* Run [thunk] and memoise its result under [e]'s identity, unless it is already
   memoised. *)
let memoized ctx (e : Explanation.t) (thunk : unit -> Writer.cid) : Writer.cid =
  match find_memo ctx e with Some m -> m.cid | None -> remember ctx e (thunk ())

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
  match defining_line ctx lits with
  | Some cid -> cid
  | None ->
      let cid =
        Writer.rup_clause ctx.writer
          ~origin:
            (Printf.sprintf "clause(%s)"
               (String.concat " " (List.map Lit.to_string lits)))
          lits
      in
      state_clause ctx lits cid;
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
let emit_rup_clause ctx ~origin lits =
  validate_lits ctx lits;
  let cid = Writer.rup_clause ctx.writer ~origin lits in
  state_clause ctx lits cid;
  cid

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
let emit_linear ctx terms rhs =
  validate_lits ctx (List.map snd terms);
  Writer.rup ctx.writer
    ~origin:(Printf.sprintf "linear: %s" (Opb.constr_to_string (Opb.ge terms rhs)))
    (Opb.ge terms rhs)

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
  | None -> Writer.pol ctx.writer ~origin expr
  | Some c -> Writer.pol_concluding ctx.writer ~origin ~claim:c expr

let emit_cut ~emit ~claim ctx e1 e2 c1 c2 =
  if c1 < 1 || c2 < 1 then
    invalid_arg
      (Printf.sprintf "Justify.emit: Cut coefficients must be >= 1, got (%d, %d)" c1 c2);
  let id1 = emit ctx e1 in
  let id2 = emit ctx e2 in
  pol_stating ctx ~claim
    ~origin:(Printf.sprintf "cut(%d*%d + %d*%d)" c1 id1 c2 id2)
    Pol.(add (mul (id id1) c1) (mul (id id2) c2))

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
let emit_summand ~emit ctx = function
  | Explanation.Term (c, e) ->
      if c < 1 then
        invalid_arg
          (Printf.sprintf "Justify.emit: Combine term coefficient must be >= 1, got %d" c);
      let id = emit ctx e in
      Pol.mul (Pol.id id) c
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
      Pol.mul (Pol.id id) c
  | Explanation.Weaken lits ->
      (match lits with
      | [] -> invalid_arg "Justify.emit: Combine's Weaken summand must be non-empty"
      | _ -> ());
      validate_lits ctx (List.map snd lits);
      List.fold_left
        (fun acc (c, l) ->
          if c < 1 then
            invalid_arg
              (Printf.sprintf
                 "Justify.emit: Weaken axiom coefficient must be >= 1, got %d" c);
          Pol.add acc (Pol.mul (Pol.axiom l) c))
        (let c0, l0 = List.hd lits in
         Pol.mul (Pol.axiom l0) c0)
        (List.tl lits)

let emit_combine ~emit ~claim ctx summands divisor =
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
    List.filter (function Explanation.Weaken [] -> false | _ -> true) summands
  in
  (match summands with
  | [] -> invalid_arg "Justify.emit: Combine must have at least one summand"
  | _ -> ());
  let expr =
    List.fold_left
      (fun acc s -> Pol.add acc (emit_summand ~emit ctx s))
      (emit_summand ~emit ctx (List.hd summands))
      (List.tl summands)
  in
  let expr = if divisor <= 1 then expr else Pol.div expr divisor in
  pol_stating ctx ~claim
    ~origin:(Printf.sprintf "combine(%d summand(s), / %d)" (List.length summands) divisor)
    expr

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
  | Explanation.Clause lits -> memoized ctx e (fun () -> emit_clause ctx lits)
  | Explanation.Linear (terms, rhs) ->
      memoized ctx e (fun () -> emit_linear ctx terms rhs)
  | Explanation.Cut (e1, e2, c1, c2) ->
      memoized ctx e (fun () -> emit_cut ~emit ~claim:None ctx e1 e2 c1 c2)
  | Explanation.Combine (summands, divisor) ->
      memoized ctx e (fun () -> emit_combine ~emit ~claim:None ctx summands divisor)
  | Explanation.Deferred _ -> memoized ctx e (fun () -> emit ctx (Explanation.force e))

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
    | Explanation.Cut (e1, e2, c1, c2) ->
        emit_cut ~emit ~claim:(Some claim) ctx e1 e2 c1 c2
    | Explanation.Combine (summands, divisor) ->
        emit_combine ~emit ~claim:(Some claim) ctx summands divisor
    | Explanation.Deferred _ -> go (Explanation.force e)
    | Explanation.Clause _ | Explanation.Linear _ | Explanation.Model_row _
    | Explanation.Decision _ ->
        emit ctx e
  in
  go e

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
  | Some l -> (
      (* The same hygiene [emit_clause] applies to a reason's literals: a conclusion
         about a variable this encoding never declared is a caller's mistake and says
         so here, not several lines later inside veripb. *)
      validate_lits ctx [ l ];
      match Explanation.force e with
      | Explanation.Cut _ | Explanation.Combine _ -> emit_clause ctx [ l ]
      | Explanation.Clause _ | Explanation.Linear _ | Explanation.Model_row _
      | Explanation.Decision _ | Explanation.Deferred _ ->
          emit ctx e)
