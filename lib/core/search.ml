(* search.ml: depth-first search with every decision and backtrack reflected in the
   proof (M1-T10, Part 2). Read the module header below in full before calling
   [solve] -- the proof-logging strategy it implements is a specific, deliberate
   answer to "how a decision made mid-search can ever be cited by a checker that never
   sees it as an axiom", not an incidental detail.

   ---------------------------------------------------------------------------
   The hard question, and why the answer here is neither of the two the task poses
   ---------------------------------------------------------------------------

   docs/SPEC.md 3.4: first-fail variable selection, min-value branching, depth-first,
   restarts disabled. That part is unsurprising. The proof-logging strategy is not.

   A decision is not implied by the model, so it cannot enter the proof as a bare fact:
   neither [rup] nor [pol] can derive an unentailed literal (docs/DECISIONS.md D-0009
   demonstrates this directly against veripb -- a bare literal in a [pol] is the
   trivial axiom [lit >= 0], and [rup] requires a genuine logical consequence), and
   [a] (assumed-checked) is forbidden outside debugging (docs/PROOF-FORMAT.md section
   2). [red] (redundance) does not apply either: it justifies adding a constraint that
   preserves *satisfiability* under a witness substitution, which is not available for
   an arbitrary domain split (a solution with x=3 cannot be "witnessed" into one with
   x>=5; it may simply not exist).

   The task offers two standard resolutions:
     (a) every derived constraint carries the negated decision literals, so it is
         globally valid rather than valid-under-assumption;
     (b) nothing is logged inside a branch; the branch's refutation is derived only
         when it closes.

   This module used to implement (b) for the branching case, and that was the defect
   docs/DECISIONS.md D-0018 is about. The nogood over the active decisions was emitted
   as a [rup] and veripb rejected it; D-0012, D-0014 and D-0017 concluded from that that
   the nogood was *unreachable* and needed new machinery. It is not, and it does not.
   A [rup] check negates its target -- asserting each decision as a unit -- and then unit
   propagates over the database one single constraint at a time. With nothing logged
   inside the branch, the database held only the model rows, so the checker was being
   asked to re-derive a multi-row bounds fixpoint in one step. That is the one thing PB
   unit propagation cannot do, and it never had to: the solver already performed that
   fixpoint and can simply write down each step.

   So what is implemented now is (a) applied *per pruning* rather than per conflict, in
   the form D-0018 takes from the Glasgow Constraint Solver. Every pruning gets one line
   (lib/core/trace.ml):

       rup 1 <the order literal the pruning established>
             1 ~<a bound fact the propagator read> ... >= 1 ;

   which is globally valid and mentions **no decision at all** -- it says "these bounds
   imply that bound", a consequence of one model row. The decisions appear in exactly one
   line, the nogood, unchanged in form from what this module always emitted; it is RUP
   now because the checker has a trace to propagate along. We keep the lazy variant: the
   trace is written when a branch actually fails, by walking the trail, not at every
   pruning on every successful path. [Trace]'s header says why that is sound here and
   what would break it.

   **A conflict with no decision active** is unchanged: it renders the propagator's own
   [Explanation.t] -- D-0013's weaken-out-the-other-variables, divide, add -- as a [pol]
   chain. That is the derivation M1-T12 made [Explanation.t] able to express, and D-0018
   keeps it: where a pruning is not plain RUP over its row, the [pol] is what the trace
   line falls back on (D-0018 point 2). No such fallback was needed for any [int_lin_le]
   pruning in this checkout; see the M1-T13 hand-back report for what was run.

   ---------------------------------------------------------------------------
   How a decision and a backtrack become proof steps
   ---------------------------------------------------------------------------

   Branching splits on a single order-encoding literal [l = x_ge_(k+1)] for the chosen
   variable [x] at the chosen value [k] (docs/SPEC.md 3.4's default, [spec_order] below,
   is first-fail with [k = lo]: try [x = lo] -- i.e. [~l] -- before [x > lo] -- i.e.
   [l]). Which variable, which [k] and which side first are the *only* things the order
   decides, and none of them reaches anything below this paragraph: one literal, one
   level, one trace, one nogood, whatever the order says. Both branches run inside their own
   [Store] decision level (docs/DECISIONS.md D-0008), tagged in the proof with
   [Writer.set_level] to match: *every* decision opens a level and *every* backtrack
   wipes one, which is the sense in which "every branching decision and every
   backtrack MUST be reflected in the proof" (docs/SPEC.md 3.4) holds here. Since
   D-0018 each individual pruning inside a branch is rendered too, tagged with the
   level of the trail entry that produced it, so one [w] retires exactly the lines
   whose prunings the matching [Store.backtrack] undid.

   Ordering is load-bearing and has its own [Debug.check] below: the nogood is emitted
   **before** the level it mentions is wiped. D-0018 point 4 exists because reversing
   these two is the bug someone rediscovers; gcs/solve.cc:296-297 has the same two lines
   in the same order.

   When both branches of a decision fail, their two nogoods --
     "~l" branch:  (negated ancestor decisions) \/ l
     "l"  branch:  (negated ancestor decisions) \/ ~l
   -- resolve on [l] (itself a [rup], found trivially by unit propagation against the
   two clauses, both still live in the database at that point) into the ancestor-only
   nogood, i.e. the failure is propagated exactly one level up, mirroring chronological
   backtracking. The two child nogoods are then retired with a single [w] at the level
   they were tagged with (D-0008: one wipe per backtrack, not one deletion per
   reason), and the combined nogood survives, tagged one level up. Recursing this to
   the root produces, when the whole search space is exhausted, the empty clause --
   an unconditional contradiction -- which is exactly the id [conclusion UNSAT] cites
   (invariant I-S2: the proof independently establishes it, not merely the solver's
   own "I looked everywhere" bookkeeping). *)

module Lit = Baguette_proof.Lit
module Writer = Baguette_proof.Writer
module Encoding = Baguette_proof.Encoding

type assignment = (Var.t * int) list
type outcome = Sat of assignment | Unsat

(* Raised if the independently-checked solution (invariant I-S1) fails the caller's
   own [check] -- a propagator soundness bug (I-P1), never a normal outcome. [solve]
   must not paper over this by pretending UNSAT or silently retrying. *)
exception Unsound_solution of assignment

(* One node's outcome, before it has been reported to its own caller: a solution, or a
   nogood -- the clause already asserted into the proof (its [Writer.cid] is still
   live) together with the literals it states, so the caller can drop its own most
   recent decision literal and re-derive the next nogood up. *)
type node = NSat of assignment | NFail of Lit.t list * Writer.cid

(* ------------------------------------------------------- the branching order (M2-T11)

   Which variable is branched on, at which value, and which side first. docs/SPEC.md 3.4
   fixes that -- first-fail, indomain_min -- and [spec_order] is it; it is the default of
   [solve] and the only order anything outside the tests uses. [random_order] exists
   because M1's whole nogood story (D-0018, D-0021) is a claim about *whatever* tree the
   search happens to build: the branch's own trace is what its refutation rests on, so a
   different tree is a different proof, and a fuzzer that only ever drives one tree shape
   tests one shape of that claim. It is a test facility and nothing more.

   What an order may vary is the *choice*. It may not vary the logging discipline around
   it, and it cannot: everything below this point -- one level per decision, the trace
   before the nogood, the nogood before the wipe (D-0018 point 4) -- is written once and
   is the same code for every order. If making some order verify seems to need a change
   to the emission, that is the emission relying on the fixed order, which is a finding
   and not a patch. *)

(* Every unfixed variable, in declaration order; empty exactly when everything is fixed.

   An order chooses from this array and can choose nothing else, which is what keeps
   completeness (I-S2) a property of this module rather than of the strategy it is handed:
   [dfs] reports a solution exactly when the array is empty, so a strategy decides the
   *shape* of the tree and never which leaves it has. *)
let unfixed store =
  let n = Store.n_vars store in
  let acc = ref [] in
  for i = n - 1 downto 0 do
    let v = Var.of_int i in
    if Domain.size (Store.get store v) > 1 then acc := v :: !acc
  done;
  Array.of_list !acc

(* One decision. [d_split] is read as: the low branch is [x <= d_split], the high branch
   is [x >= d_split + 1], and the single order literal [x_ge_(d_split+1)] is the one thing
   the two branches disagree about -- so the two child nogoods still resolve on exactly
   one literal, as they always did. [d_split] must lie in [lo, hi), which makes both
   pushes strictly narrowing, which is what [check_decision_landed] asserts.

   docs/SPEC.md 3.4's indomain_min is [d_split = lo] with the low side first (that branch
   then fixes [x = lo], which is what [Search] has always emitted); indomain_max would be
   [d_split = hi - 1] with the high side first. *)
type decision = { d_var : Var.t; d_split : int; d_high_first : bool }

(* An order is asked for a decision given the store and the non-empty array of unfixed
   variables. *)
type order = Store.t -> Var.t array -> decision

(* First-fail (docs/SPEC.md 3.4): the unfixed variable (domain size > 1) with the
   smallest domain, ties broken by declaration order (the store's variable index). *)
let first_fail store cands =
  let best = ref cands.(0) in
  let bsize = ref (Domain.size (Store.get store cands.(0))) in
  for i = 1 to Array.length cands - 1 do
    let size = Domain.size (Store.get store cands.(i)) in
    if size < !bsize then (
      best := cands.(i);
      bsize := size)
  done;
  !best

(* docs/SPEC.md 3.4, and the default of [solve]: first-fail, min-value branching. This is
   the normative strategy and the only one the CLI can reach; `lib/flatzinc/compile.ml`
   rejects an annotation asking for anything else rather than silently ignoring it. *)
let spec_order store cands =
  let v = first_fail store cands in
  { d_var = v; d_split = Domain.lo (Store.get store v); d_high_first = false }

(* A branching order driven by [r], for the fuzzer (test/unit/test_random.ml). Every
   draw comes from [r], so one seed reproduces one whole tree.

   The split is taken at a [k] with both [k] and [k+1] in the domain, so that
   [set_hi _ k] lands on exactly [k] and [set_lo _ (k+1)] on exactly [k+1]. That is a
   constraint on the proof rather than on the search: [Domain.settle] walks a bound over
   a hole, so a decision at a hole would put a bound on the trail strictly stronger than
   the [x_ge_(k+1)] its nogood negates, and the checker could not replay the difference
   -- an interior hole gets no trace line at all ([Trace]'s [claims] writes one only when
   a bound moves). [lo] is the fallback after a few misses because [lo] is what
   docs/SPEC.md 3.4 already branches at: [lo] is in the domain by I-D2, so the low side
   lands exactly, and the high side is then the same [set_lo _ (lo+1)] the default has
   always made. So a random order reaches new tree shapes without inventing a class of
   decision the default does not also make -- which is what makes a rejection under it a
   finding about the solver rather than about this function.

   The guard shipped disabled. It read [if true || (Domain.mem d k && Domain.mem d
   (k + 1))], which short-circuits, so the membership test, [pick]'s recursion and
   [tries] were all dead and every draw was taken whatever the domain looked like --
   an unfinished-debugging edit from the interrupted session that wrote this, and one
   no compiler warning catches. Restored here, and what the disabled version bought is
   recorded rather than guessed at, because "the guard is load-bearing" would be a
   claim nobody has tested: with it disabled, and with [random_order] further biased to
   prefer a holey variable AND a hole split within it, 2051 splits out of 495723 over
   108000 solver runs landed where the guard now refuses, and **not one of them was
   rejected by veripb**. So the guard is conservative, not measured-necessary. It is
   restored because the code must say what its header says and because attribution is
   worth more here than 0.4% more tree shapes -- not because a hole split has been seen
   to break a proof. Whoever wants that 0.4% back should take it deliberately, with an
   instance that shows what it catches. *)
let random_order r store cands =
  let v = cands.(Random.State.full_int r (Array.length cands)) in
  let d = Store.get store v in
  let lo = Domain.lo d and hi = Domain.hi d in
  let rec pick tries =
    if tries = 0 then lo
    else
      let k = lo + Random.State.full_int r (hi - lo) in
      if Domain.mem d k && Domain.mem d (k + 1) then k else pick (tries - 1)
  in
  { d_var = v; d_split = pick 8; d_high_first = Random.State.bool r }

let extract_assignment store : assignment =
  List.init (Store.n_vars store) (fun i ->
      let v = Var.of_int i in
      (v, Domain.lo (Store.get store v)))

(* ------------------------------------------------------------------------------ dfs *)

(* [decisions] is the stack of literals actually forced true so far by branching,
   most-recent decision first -- so [List.map Lit.negate decisions] is, at every
   point, exactly the nogood clause that would state "not all of these hold". *)
(* D-0018 point 4, made loud. The nogood cites decisions that live at [lvl]; the [w]
   that retires them must come *after* it, and the writer must already have stepped down
   to the parent level, or the nogood is filed at a level its own [w] is about to wipe.
   Under the audit the id is checked to be live as well, which catches the same mistake
   made one call earlier. *)
let wipe_after_nogood ctx ~lvl ~nogood =
  Debug.check
    "D-0018.4: the nogood is emitted, at the parent level, before the branch's level is \
     wiped" (fun () ->
      Writer.current_level ctx.Justify.writer < lvl
      &&
      let w = ctx.Justify.writer in
      (not (Writer.auditing w)) || Writer.is_live w nogood);
  Justify.wipe_level ctx lvl

(* Does this derivation rest on a clausal reason?

   docs/DECISIONS.md D-0013 closed the no-decision case with "the propagator's own
   derivation *is* the contradiction", and for [int_lin_le] it is: a row whose slack has
   gone negative weakens every other variable out, divides, and adds down to a numeric
   [0 >= k], which veripb reads as a contradiction directly. That sentence was written
   when [int_lin_le] was the only propagator there was, and it is false for a clausal
   reason. A [Clause] says "not all of these variables take these values at once"
   (D-0019): a perfectly good constraint, and not a contradiction -- veripb says so in
   as many words, at the [conclusion] line rather than at the rule, which is what makes
   the mistake hard to read off the output.

   M1-T46: the two checkers word that rejection differently and **share no substring**,
   so match on neither alone. 2.2.2 says "Constraint is not a contradiction"; 3.0.2 --
   the checker of record, and the format emitted by default since D-0025 -- says "The
   constraint with ID <n> is not contradicting, as specified by the hint". Measured
   against both binaries, not guessed. lib/core/prop/ne.ml's header and
   test/unit/test_random.ml carry the same pair, and that test matches both deliberately:
   matching only the 2.0 wording is not a vacuous pass but it is a vacuous *diagnosis*,
   reporting a known bug as a brand-new one.

   It reaches the root arm two ways, and this predicate is deliberately structural so
   that it catches both: the propagator's conflict explanation can BE a [Clause]
   ([int_ne] conflicting with every variable fixed), or a [Combine] can have folded one
   into its arithmetic as a cited summand ([int_lin_le] citing the trail entry that last
   moved a bound, where the entry is a disequality's -- D-0019's last consequence). The
   second is sound as a [pol] step, which is why nothing louder happens at the rule
   itself: a [pol] derives whatever it derives, here something valid that simply is not
   what the row's own slack argument claimed, because a clause over several variables
   does not cancel this row's coefficient for the one variable the way a chain-sum over
   that variable's declared range does (lib/core/prop/linear.ml's header states that
   contract).

   Either way the honest close is the one D-0018 already uses everywhere else: write the
   trace, then state the contradiction as a [rup] the checker verifies for itself. *)
let rec rests_on_a_clause (e : Explanation.t) =
  match Explanation.force e with
  | Explanation.Clause _ -> true
  | Explanation.Decision _ | Explanation.Model_row _ | Explanation.Linear _ -> false
  | Explanation.Cut (a, b, _, _) -> rests_on_a_clause a || rests_on_a_clause b
  | Explanation.Combine (summands, _) ->
      List.exists
        (function
          | Explanation.Term (_, e) -> rests_on_a_clause e | Explanation.Weaken _ -> false)
        summands
  | Explanation.Deferred _ -> false (* [force] returns a non-deferred head *)

(* A root conflict whose derivation rests on a clause, closed the D-0018 way.

   Three lines, in this order, and the order is the same one the under-a-decision arm
   uses for the same reason (D-0018 point 4 and [Trace]'s header):

   1. the branch's trace -- here the *root's* trace, every level-0 pruning. D-0021: a
      [rup] check starts from nothing and does not inherit the solver's root fixpoint,
      so the bounds this conflict rests on have to be on the page before anything can
      unit propagate to them. This is exactly the measurement D-0021 records for
      `offset`, arrived at from the other end.
   2. the conflict's own reason line, when the propagator recorded facts for it
      (D-0018 point 3).
   3. the propagator's own derivation, which is emitted even though it is not the
      contradiction: it is still a valid consequence, and it leaves the empty clause one
      unit propagation away rather than a search away.

   Then the contradiction itself, as the empty clause. That is not a new rule or a new
   shape -- it is [rup >= 1 ;], the nogood over an empty decision stack, i.e. what the
   decision arm below emits with [decisions = []] substituted in. Citing *it* rather
   than the derivation is the whole fix: what [conclusion UNSAT] names is now a line
   veripb has checked to be a contradiction, not one this module asserted was. *)
let close_root_conflict ctx trace store e =
  Trace.emit ctx trace store;
  let _ : Writer.cid option = Trace.conflict_line ctx trace store in
  match Explanation.force e with
  | Explanation.Clause [] ->
      (* Already the empty clause -- a disequality every one of whose variables the
         model declares fixed (D-0019). Emitting it twice would be silly. *)
      Justify.emit ctx e
  | _ ->
      let _ : Writer.cid = Justify.emit ctx e in
      Justify.emit ctx (Explanation.clause [])

(* ------------------------------------------------- a decision that settled at a hole

   M1-T55, and the other half of the sentence in [random_order]'s header above.

   [spec_order] splits at [d_split = lo] and [explore_ge] pushes [set_lo v (lo + 1)].
   [Domain.settle] re-establishes I-D2 by walking a bound over a hole, so when [lo + 1]
   is a hole the trail entry records [x >= m] for the next value [m] actually in the
   domain, while the literal that branch assumed -- and the one its nogood negates -- is
   [x_ge_(lo+1)]. The nogood therefore claims to have refuted [x >= lo + 1] on the
   strength of having explored only [x >= m].

   That claim is *true*. The values [lo + 1 .. m - 1] are excluded by constraints (I-P1),
   and where a propagator needed an ancestor decision to exclude them the nogood is
   conditioned on exactly those decisions. What is not automatic is that veripb can
   *find* it. A [rup] check asserts the decisions and unit propagates one constraint at a
   time; a pure hole removal moves no bound, so lib/core/trace.ml's [claims] writes no
   line for it (that function says so itself, and M1-T56 is the same sentence from the
   other end). The exclusion is on the page only as whatever the punching constraint's
   own rows happen to unit propagate.

   For every propagator M1 has, that is enough -- which is why M2-T11 measured 2051 hole
   splits out of 495723 over 108000 runs with **not one veripb rejection**. A hole is
   punched only by a disequality (lib/core/prop/ne.ml, [int_lin_ne]); its .opb encoding
   is a bounded number of rows over that constraint's own literals; and PB unit
   propagation over one such row reproduces exactly the bounds reasoning the propagator
   did, given the other terms' bounds -- which are on the page either as a trace line or
   as a decision the nogood itself asserts. So the proof has been resting on a property
   of *the encoding of the current propagator set*, stated nowhere and checked by
   nothing. M4's [all_different] prunes from a Hall set, whose reason is not one row, and
   that property ends there.

   Two routes were open (docs/ROADMAP.md M1-T55). Guarding [spec_order] the way
   [random_order] is guarded was rejected: the split would no longer be at [lo], which is
   docs/SPEC.md 3.4's indomain_min, so it is a normative change that moves every model's
   proof to pay for a defect that has never been observed -- and [random_order]'s own
   guard is not total anyway ([pick]'s fallback after 8 misses is [lo], which is where it
   refuses to land). Making the decision's trail entry land exactly on the literal its
   nogood negates was rejected because **it cannot be done**: the low side lands exactly
   iff [k] is in the domain and the high side iff [k + 1] is, so demanding both is
   demanding [random_order]'s guard condition, and a complementary literal pair at a hole
   boundary always leaves one side settling. Choosing the literal from the settled bound
   instead only moves the gap to the other side, where it is worse: the two children's
   nogoods then no longer resolve on one literal.

   So the missing step is written down instead. [bridges] emits, for each decision on the
   path whose push settled past a hole, one line

       rup 1 <the bound the trail recorded> 1 ~<the bound the decision assumed>
              1 ~<each ancestor decision> >= 1 ;

   read as a clause: "under these decisions, [x >= lo + 1] implies [x >= m]". It is
   globally valid -- every ancestor it rests on is negated into it, which is form (a) of
   this module's header -- and it is exactly the one fact the nogood's own check has been
   deriving implicitly all along. It is emitted lazily, after [Trace.emit] and before the
   nogood, because D-0021: a [rup] does not inherit the solver's root fixpoint, so the
   trace the exclusion propagates along has to be on the page first.

   What that buys is the point. The implicit dependency becomes a line veripb checks at
   the decision that made it, naming the variable and both bounds, so when it stops
   holding the proof is rejected *there* rather than at a nogood several inferences away
   -- or, worse, accepted because some other route through the branch happened to close.
   It also retires M1-T45: with the bridge on the page a hole split is harmless, so
   [random_order]'s guard is no longer the thing standing between this module and a
   rejection and the 0.4% of tree shapes it refuses can be reclaimed deliberately.

   It changes no tree. No order, no split, no domain and no decision literal is touched;
   a run that never splits at a hole emits byte-for-byte the proof it emitted before, and
   [solve]'s "the default is byte-for-byte the tree this module has always built" still
   holds -- for the tree *and*, on every model in test/models/ but the one added for this
   task, for the bytes. *)

(* The decision pushes of the open levels, oldest first: each is the first trail entry of
   its own level, which is what [check_decision_landed] and [Store.is_level_start] assert
   from their two sides. A level that has been opened but whose push has not landed (the
   [Store.Conflict] arms of [explore_le]/[explore_ge]) contributes no entry, which is
   what makes the walk below line up on the ancestors and drop the literal that never
   made it onto the trail. *)
let decision_entries store =
  let n = Store.trail_length store in
  let acc = ref [] in
  for i = n - 1 downto 0 do
    if Store.is_level_start store i then acc := Store.trail_entry store i :: !acc
  done;
  !acc

(* Did this push land somewhere strictly stronger than its literal names, and if so on
   what? [Some cond] is the bound the trail actually recorded; [None] means the push
   landed exactly and there is nothing to bridge, which is the overwhelmingly common
   case and the only one [random_order]'s guard permits.

   The literal's polarity says which side the branch took: [x_ge_b] is the high side, so
   the low bound moved and lands exactly on [b]; [~x_ge_b] is [x <= b - 1], so the high
   bound moved and lands exactly on [b - 1]. *)
let settled_bound encoding (e : Store.entry) name (l : Lit.t) =
  let b = Lit.value l.Lit.v in
  if l.Lit.positive then
    let m = Domain.lo e.Store.now in
    if m <= b then None else Some (Encoding.ge encoding name m)
  else
    let h = Domain.hi e.Store.now in
    if h >= b - 1 then None else Some (Encoding.le encoding name h)

(* Does this entry plausibly belong to this decision literal? The walk pairs two lists
   that are built independently -- the open levels' pushes from [Store], the assumed
   literals from [dfs]'s own recursion -- and a pairing that has slipped would write a
   line about the wrong variable, which is the kind of mistake that verifies anyway
   (a true clause about some other variable is still a true clause). So it is checked
   rather than assumed, and a mismatch stops the walk instead of guessing. *)
let aligned store (e : Store.entry) (l : Lit.t) =
  Lit.is_order l.Lit.v
  && String.equal (Store.name store e.Store.var) (Lit.owner l.Lit.v)
  &&
  if l.Lit.positive then Domain.lo e.Store.now > Domain.lo e.Store.old
  else Domain.hi e.Store.now < Domain.hi e.Store.old

let bridges (ctx : Justify.ctx) store (decisions : Lit.t list) =
  let rec go entries rev_decisions ancestors =
    match (entries, rev_decisions) with
    | [], _ | _, [] -> ()
    | (e : Store.entry) :: es, (l : Lit.t) :: ls ->
        if not (aligned store e l) then
          Debug.check
            "M1-T55: the open levels' pushes and the assumed decision literals line up"
            (fun () -> false)
        else
          let name = Store.name store e.Store.var in
          (match settled_bound ctx.Justify.encoding e name l with
          | None -> ()
          | Some cond -> (
              match
                Trace.claim_of_cond ~what:"the bound a decision settled onto" ~name cond
              with
              | None ->
                  (* The settled bound is the declared one, so the claim is vacuous and
                     no literal exists to state it -- nothing to bridge. *)
                  ()
              | Some claim ->
                  let lits = claim :: Lit.negate l :: List.map Lit.negate ancestors in
                  let origin =
                    Printf.sprintf "M1-T55: %s settled onto %s" (Lit.to_string l)
                      (Lit.to_string claim)
                  in
                  let _ : Writer.cid = Justify.emit_rup_clause ctx ~origin lits in
                  ()));
          go es ls (l :: ancestors)
  in
  go (decision_entries store) (List.rev decisions) []

let rec dfs engine store ctx trace (order : order) (decisions : Lit.t list) : node =
  match Engine.propagate engine store with
  | Engine.Conflict e -> (
      match decisions with
      | [] ->
          (* D-0013: with no decision active there is nothing to negate. Where the
             propagator's own derivation really *is* the contradiction -- the [pol]
             chain M1-T12 exists to build -- emitting it and citing it is still the
             answer, and a bare clause there would be the "trust me" that D-0012
             recorded veripb rejecting. Where it is not, [close_root_conflict] takes
             over; [rests_on_a_clause] above is the difference and says why.
             Nothing has been branched on yet, so the trace this writes is the root's
             own: [dfs] reaches this arm with [decisions = []] only on the very first
             call. *)
          let cid =
            if rests_on_a_clause e then close_root_conflict ctx trace store e
            else Justify.emit ctx e
          in
          NFail ([], cid)
      | _ ->
          (* D-0018, in the order the record gives: the branch's own propagation trace
             first, then the conflict's reason line, then the nogood. Each of the first
             two is globally valid and decision-free; only the last one mentions the
             decisions, and it is RUP precisely because the other two are there to unit
             propagate along. *)
          Trace.emit ctx trace store;
          let _ : Writer.cid option = Trace.conflict_line ctx trace store in
          (* M1-T55: and then the bridge for any decision on this path that settled past
             a hole, which is the step the nogood's own [rup] needs and has until now
             been left to find for itself. It goes after the trace (D-0021) and before
             the nogood, at the nogood's own level, so the same [w] retires both. *)
          bridges ctx store decisions;
          let lits = List.map Lit.negate decisions in
          let cid = Justify.emit ctx (Explanation.clause lits) in
          NFail (lits, cid))
  | Engine.Fixpoint ->
      let cands = unfixed store in
      if Array.length cands = 0 then NSat (extract_assignment store)
      else branch engine store ctx trace order decisions (order store cands)

and branch engine store ctx trace order decisions (dec : decision) : node =
  let v = dec.d_var in
  let d = Store.get store v in
  let k = dec.d_split in
  if k < Domain.lo d || k >= Domain.hi d then
    invalid_arg
      (Printf.sprintf
         "Search.branch: the order split %s at %d, outside [%d, %d) -- a decision must \
          strictly narrow both branches"
         (Store.name store v) k (Domain.lo d) (Domain.hi d));
  let name = Store.name store v in
  let lit = Lit.ge name (k + 1) in
  (* The two sides, in the order this decision asks for. They are the same two functions
     whichever way round they go: which side is explored first changes the tree, and
     changes nothing about what is emitted for either side. *)
  let first, second =
    if dec.d_high_first then (explore_ge, explore_le) else (explore_le, explore_ge)
  in
  Store.new_level store;
  let lvl = Store.level store in
  Writer.set_level ctx.Justify.writer lvl;
  let r1 = first store engine ctx trace order decisions v k lit in
  Store.backtrack store;
  match r1 with
  | NSat asn ->
      Justify.wipe_level ctx lvl;
      NSat asn
  | NFail (lits1, _) -> (
      Store.new_level store;
      let lvl2 = Store.level store in
      Debug.check "search: reopened level matches the one just closed" (fun () ->
          lvl2 = lvl);
      Writer.set_level ctx.Justify.writer lvl;
      let r2 = second store engine ctx trace order decisions v k lit in
      Store.backtrack store;
      match r2 with
      | NSat asn ->
          Justify.wipe_level ctx lvl;
          NSat asn
      | NFail (lits2, _) ->
          let combined =
            match lits1 with
            | _ :: tl -> tl
            | [] ->
                invalid_arg
                  "Search.branch: a branch's own nogood must mention its own decision"
          in
          Debug.check "search: both children's nogoods agree past their own decision"
            (fun () ->
              match lits2 with
              | _ :: tl2 -> List.length tl2 = List.length combined
              | [] -> false);
          Writer.set_level ctx.Justify.writer (lvl - 1);
          let cid = Justify.emit ctx (Explanation.clause combined) in
          wipe_after_nogood ctx ~lvl ~nogood:cid;
          NFail (combined, cid))

(* The decision push itself. It is the first entry of the level just opened, which is
   what [Trace] relies on to tell a decision (no line -- nothing implies it) from a
   pruning (a line). [Store] asserts the same thing from its side via
   [is_level_start]; this check is the search's half, because the only way the two can
   disagree is a push here that did not actually change the domain. *)
and check_decision_landed store lvl outcome =
  Debug.check "D-0018: a decision is the first trail entry of its own level" (fun () ->
      (match (outcome : Store.outcome) with
      | Store.Changed -> true
      | Store.Unchanged | Store.Conflict _ -> false)
      && Store.level store = lvl
      && Store.is_level_start store (Store.trail_length store - 1))

(* The low side, [x <= k] -- the decision literal is [~lit]. With [k = lo] (docs/SPEC.md
   3.4's indomain_min) this fixes [x = lo], which is what it has always done.

   M1-T31/M1-T50: the reason pushed with it is [Explanation.decision ~lit] and not the
   old [Explanation.trivial]. A decision is an assumption, not an instance of the model
   constraint, and calling it [Trivial] was what let a propagator citing this entry
   render it as the ambient model row (see explanation.ml's header). The literal is
   exactly the one this branch assumes, so a propagator that reads a bound this entry
   established can see *that* it is an assumption and weaken it out of its [pol]
   (lib/core/prop/linear.ml's [Snap_assume]) rather than citing an id that does not
   exist. It is the same literal the nogood negates on the way back out. *)
and explore_le store engine ctx trace order decisions v k lit =
  let lvl = Store.level store in
  let outcome = Store.set_hi store v k (Explanation.decision (Lit.negate lit)) in
  match outcome with
  | Store.Conflict _ ->
      (* [k >= lo] and [lo] is in [v]'s domain (I-D2), so [set_hi _ k] cannot empty it;
         kept only so this function is total against [Store.outcome] without assuming
         it. *)
      Trace.emit ctx trace store;
      (* M1-T55: the ancestors only -- this push did not land, so it has no trail entry
         and nothing to bridge, and [bridges] drops it for exactly that reason. *)
      bridges ctx store decisions;
      let lits = List.map Lit.negate (Lit.negate lit :: decisions) in
      let cid = Justify.emit ctx (Explanation.clause lits) in
      NFail (lits, cid)
  | Store.Changed | Store.Unchanged ->
      check_decision_landed store lvl outcome;
      dfs engine store ctx trace order (Lit.negate lit :: decisions)

(* The high side, [x >= k + 1] -- the decision literal is [lit]. Symmetrically,
   [k + 1 <= hi] and [hi] is in the domain, so this push cannot empty it either. *)
and explore_ge store engine ctx trace order decisions v k lit =
  let lvl = Store.level store in
  let outcome = Store.set_lo store v (k + 1) (Explanation.decision lit) in
  match outcome with
  | Store.Conflict _ ->
      Trace.emit ctx trace store;
      (* M1-T55: as in [explore_le] -- the ancestors only. *)
      bridges ctx store decisions;
      let lits = List.map Lit.negate (lit :: decisions) in
      let cid = Justify.emit ctx (Explanation.clause lits) in
      NFail (lits, cid)
  | Store.Changed | Store.Unchanged ->
      check_decision_landed store lvl outcome;
      dfs engine store ctx trace order (lit :: decisions)

(* ------------------------------------------------------------------------------ API *)

(* Depth-first search from the store's current decision level (I-S3: the level on
   return equals the level on entry -- true here by construction, since every
   [Store.new_level] this module calls is paired with exactly one [Store.backtrack]
   before returning).

   [?order] is the branching order and defaults to [spec_order], docs/SPEC.md 3.4's
   normative first-fail/indomain_min: nothing outside the tests passes it, and the
   default is byte-for-byte the tree this module has always built. [random_order] is
   the fuzzer's (M2-T11); see the branching-order section above for what an order is
   allowed to vary.

   [engine] is shared, reusable state (its watcher table does not depend on the
   store's contents); [store] and [ctx] carry the search's actual state. [check] is
   the independent re-verification invariant I-S1 requires -- "every solution printed
   satisfies every constraint, re-checked independently ... not by trusting the
   propagators". There is deliberately no way to skip it: a caller without a real
   model-level checker at hand (M1-T10 lands before the FlatZinc [Model.t] is wired to
   the solver) still has to pass one, even if it is a small hand-written one, as the
   tests below do.

   On [Sat], the proof's [conclusion] cites the found assignment directly (never a
   bare [sol], which the doc notes only works when deletion-checking was never turned
   off -- the assignment form always works). On [Unsat], it cites the id of the
   final, decision-free nogood. Both leave [Writer]'s audit-mode live set exactly as
   it was before the call plus that one id, which [Writer.conclusion] itself retires
   (invariant I-X2 -- see docs/PROOF-FORMAT.md section 5, "discharged by the
   conclusion"). *)
let solve ~(engine : Engine.t) ~(store : Store.t) ~(ctx : Justify.ctx)
    ~(check : assignment -> bool) ?trace ?(order = spec_order) () : outcome =
  let entry_level = Store.level store in
  (* [?trace] exists so a caller can read back *which* rules in the emitted proof were
     D-0018 trace lines (test/unit/test_trace.ml checks each of them standalone against
     the .opb -- the one check that distinguishes a real trace from a decorative one).
     It is state this function would otherwise own privately; passing one in changes
     nothing about what is emitted. *)
  let trace = match trace with Some t -> t | None -> Trace.create () in
  let result = dfs engine store ctx trace order [] in
  Debug.check "I-S3: decision level on return equals level on entry" (fun () ->
      Store.level store = entry_level);
  (* I-X2: the trace lines for prunings made at level 0 are the one class of rule this
     search emits that no [w] retires -- they are deliberately outside every branch's
     level, because a level-0 pruning outlives every branch and the checker needs it on
     both sides of a backtrack (see [Trace]'s header). Retire them here, once, on every
     path, before the conclusion. Doing it here rather than inside [Trace] keeps the
     rule "an id you receive is an id you delete" with the caller that owns the proof's
     shape. *)
  let retire_trace () =
    match Trace.permanent_ids trace with
    | [] -> ()
    | ids -> Writer.delete_many ctx.Justify.writer ids
  in
  match result with
  | NSat assignment ->
      if not (check assignment) then raise (Unsound_solution assignment);
      retire_trace ();
      let bindings = List.map (fun (v, x) -> (Store.name store v, x)) assignment in
      let lits = Encoding.assignment_lits ctx.Justify.encoding bindings in
      Writer.conclusion ctx.Justify.writer (Writer.Sat lits);
      Sat assignment
  | NFail (lits, cid) ->
      (match lits with
      | [] -> ()
      | _ ->
          invalid_arg
            "Search.solve: the root nogood must be decision-free -- solve must be called \
             with no ambient decisions active");
      (* I-X2: the live set must be empty at [conclusion], and the contradiction cited
         by the conclusion is the one id that counts as discharged by it
         (docs/PROOF-FORMAT.md section 5). A root refutation's derivation leaves its
         intermediate steps behind -- they are at level 0, so no [w] retires them --
         so retire them explicitly here. Nothing references them again: the proof ends
         on the next line. *)
      retire_trace ();
      let leftovers =
        List.filter (fun id -> id <> cid) (Writer.live_ids ctx.Justify.writer)
      in
      if leftovers <> [] then Writer.delete_many ctx.Justify.writer leftovers;
      Writer.conclusion ctx.Justify.writer (Writer.Unsat (Some cid));
      Unsat
