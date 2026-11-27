(* all_different_int: the variables take pairwise distinct values.

   Consistency level: DOMAIN (docs/SPEC.md 3.2, docs/GLOSSARY.md). ONE propagator, ONE
   consistency tag, TWO STAGES, as docs/ROADMAP.md M4-T1 (stage 1) and M4-T2 (stage 2)
   and docs/GCS-COMPARISON.md section 3 specify:

     stage 1  [stage_bounds]  Hall intervals over lo/hi. Reads and writes bounds only.
     stage 2  [stage_regin]   a maximum matching over the value graph, which prunes
                              VALUES and therefore punches holes.

   [propagate] sequences them and is where the staging rule lives. The tag is what tells
   [Engine] to wake this instance on an interior hole and not only on a bound move, and
   the brute-force consistency oracle (BAGUETTE_CONSISTENCY=1, M2-T10) holds the
   declaration to its word at every search node.

   Proof shape (docs/SPEC.md 3.3): every pruning and every conflict is one [Combine], a
   `pol` that adds the at-least-one and at-most-one lines of the direct encoding over
   the Hall set (a counting argument, "Justification" below), cites the model's
   pairwise rows by id, and concludes in the ORDER encoding. Because a counting argument
   is not reverse unit propagation, the derivation is written AHEAD of the trace line
   that uses it.

   Regin's pruning has a justification (the question D-0004 left open): it is the same
   counting argument as stage 1 over a value SET rather than an interval, and the
   existing [Explanation] ADT expresses it with NO NEW CONSTRUCTOR. See [regin_pass] for
   the matching fact that bridges the two, and [gone] for the one thing an interval
   never forced.

   ONE CURRENCY FOR A HOLE (D-0086, built by M7-T22). Whatever this module derives
   internally, the explanation it attaches to a trail entry that punches an INTERIOR hole
   concludes the ORDER clause `~y_ge_v \/ y_ge_(v+1)` -- the clause the entry's trace line
   claims, and the one every other propagator's hole concludes -- not the direct literal
   [~y_eq_v] its counting naturally ends on. [in_order_currency] is the conversion and its
   comment is the argument; docs/PROOF-FORMAT.md section 4's all_different row is the
   contract.

   STAGE 2 IS GATED (D-0215). A Regin pass that cannot prune is skipped,
   and the test is exact: [cannot_prune] repairs a matching KEPT across passes (Régin's
   incremental matching, as Gecode and Chuffed keep theirs) and runs one Tarjan pass for
   an edge that lies in no maximum matching. When there is one, or no matching saturates
   the scope, the from-scratch pass [regin_scratch] runs exactly as before, so every
   pruning, its order and its justification are the ones it always made; the kept matching
   is a hint re-read against the live domains, never a fact, and needs no trail.

   THE COST PER CALL (D-0235; this and the gate are the per-node cost work of
   M20-pernode-T4). Four rules keep a call from paying for what cannot have changed, each
   stated and argued where it lives, none changing a pruning, its order, its reason or its
   derivation (the artefacts are byte-identical):

     - [pass] skips a stage 1 pass whose BOUND vector is one a scan once found quiet: the
       scan's outcome is a function of the bounds alone (BAGUETTE_DEBUG re-runs it);
     - [pass_scan] snapshots a term when it first reads it, and forces the snapshot of a
       term before pushing it, so it reads what the eager pass-start snapshot read;
     - [regin_scratch] keeps a term's snapshot until a removal lands on it, builds a
       tight set's facts once for all its removals, and hands the store only values
       still in the live domain ([Store.remove] answers [Unchanged] for the others);
     - Hall-set membership is a binary search ([mem_of]), never polymorphic [List.mem].

   None of these caches outlives the call except [quiet], which is a hint about a bound
   vector and not about the store, so nothing here needs the trail.

   THE COST PER CALL, SECOND PASS (D-0242). Four more, under the same
   contract (every pruning, its order, its reason and its derivation unchanged; the
   artefacts are byte-identical):

     - [hall_free] decides by counting, over two term permutations kept sorted across
       calls ([sort_by]), whether a stage 1 scan would move nothing, and [pass] skips the
       scan when it would not: a scan acts exactly on an over-full interval or a tight one
       holding an outside bound, and both are counts (BAGUETTE_DEBUG runs the scan behind
       every skip; test_prop's lane (h) checks both directions). [pass_scan] enumerates
       its intervals over the same permutations;
     - [regin_scratch] skips a tight set that no outside term meets, by a count, and
       marks the scope's values rather than sorting their lists;
     - the derivations a tight set or interval justifies share its at-least-one lines
       ([alo_lines]), under D-0216's rule that a derivation node is handed back from a
       memo only when building it again would return that very node.

   [by_lo]/[by_hi] outlive the call, and they are permutations re-sorted from the live
   bounds at every pass, so they need no trail either. The memos live in a derivation's
   thunk, and a thunk reads no store (I-X6: a deferred explanation closes over a
   snapshot and never reads live state).

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
   (I-P2: run again at its fixpoint it changes nothing) rather than by a one-pass
   argument like [Linear]'s.

   The enumeration is O(n * d^2) per pass and is the naive complete one, not Puget's
   O(n log n). That is a deliberate M4-T1 choice: this row is an experiment about the
   JUSTIFICATION, the models it may ship are bounded to single/low-double-digit domains
   by the memory rule, and an algorithm whose completeness is evident is worth more here
   than one whose completeness is a citation. The consistency oracle
   (BAGUETTE_CONSISTENCY=1; D-0059 made the tag checked) is what checks the claim either
   way.

   ---------------------------------------------------------------------------
   Justification: the multi-row Hall derivation
   ---------------------------------------------------------------------------

   A derivation may cite any number of model rows. D-0027 restated D-0011's "one
   instance justifies against exactly one model row" as a rule about NAMING rows, not
   counting them, and this module (built by roadmap M4-T1) was the first to spend that
   permission, and spends it hard: a single pruning's [Combine] names, transitively, one
   at-least-one line per Hall variable, one at-most-one line per Hall value, and a
   channelling id per value of every variable in sight. Every one of them is named with
   [Explanation.Model_row], the constructor D-0015 added for naming a row in the value.

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

   1. NO [Explanation.Clause] IN THE COUNTING. The at-most-one line is recovered by
      [pol] ([pair_amo]), and lib/proof/encoding.ml's [add_all_different] posts the
      pairwise CLAUSE rows rather than big-M rows precisely to make that recovery five
      ids and one division. The cheap alternative, a [rup] over the direct encoding,
      would work. It was rejected (D-0061) because, when this was written, a root
      conflict whose derivation rested on a clause was routed by search.ml to the empty
      clause instead of to the derivation (D-0022), so nothing the checker did would
      have depended on the Hall arithmetic being right: every [pol] here would have been
      decorative, as D-0057 and D-0060 had found twice by accident. That routing is gone
      since D-0131 (every root conflict now closes on its trace), but the rule stands:
      the only clauses in a derivation here are deep holes' [Gone_hole] cancellations.

   2. A CURRENT BOUND APPEARS AS A LITERAL IN THE DERIVED ROW, and is cancelled by the
      id of the line that establishes it where there is one. [excl] derives
      ~x_ge_lo(x) \/ ~x_eq_v rather than ~x_eq_v, so before cancellation the row is the
      globally valid `~<bound facts> \/ <the pruning>` shape lib/core/prop/ne.ml's clause
      already has, sound at any level. Citing the trail entry the way [Linear] does still
      does not fit -- a cited [Linear] derives a statement in the order encoding's ladder
      currency (D-0010, lib/core/ladder.ml's header), not the unit x_ge_c >= 1 the
      counting needs -- which is why M4-T7 gave [Explanation] the one thing that does:
      [Defining], a summand carrying the id of the UNIT line that states the fact
      (D-0064). See [hall_cancels] and [target_cancel] below.

   3. [WEAKEN] IS USED FOR ITS D-0009 MEANING, AND TWICE OVER: a literal axiom can
      weaken a term away but cannot assert a bound. Once to drop the
      excluded values the pruning does not need ([Lit.eq y v] as the trivial axiom
      y_eq_v >= 0), and once as the degenerate at-most-one: where only ONE variable in
      scope can take a value, the "at most one of them does" line is literally the
      literal axiom ~x_eq_v >= 0, and writing it as a [Weaken] summand rather than
      special-casing it keeps the counting uniform.

   3'. ONE NEW [Explanation] SUMMAND, the only thing in this file that is not
      [Combine]/[Weaken]/[Model_row]. M4-T1 built the whole derivation without one
      (D-0061) and got everything except the cancellation in item 2, where it had to fall
      back on [Explanation.clause [lit]]. M4-T7 replaced that stand-in with
      [Explanation.defining], whose record is D-0009's own: see explanation.ml's header
      for why it is a summand rather than a [t].

   ---------------------------------------------------------------------------
   The pairwise rows may be ROOT LEMMAS
   ---------------------------------------------------------------------------

   (The design is D-0151 section 2, built by M7-T28 with the native `inverse`.)

   The derivation above names each pairwise row `x <> v \/ z <> v` by id. For an
   all_different the MODEL posts, that id is a model row ([Encoding.add_all_different]).
   For one an `inverse` IMPLIES (lib/core/prop/inverse.ml's stage 2), the .opb states the
   channel rows and not the pairs, and the pairs are `rup` lemmas written at the start of
   the proof ([Encoding.add_cited_lemma]): [make]'s [?lemma_rows] carries their handles
   and [row] resolves one to its id when a derivation is rendered. That lookup is the
   whole of the change; the counting, the cancellations and every `pol` are the ones a
   model row gets, since a `pol` cites a derived line exactly as it cites a model row.

   ---------------------------------------------------------------------------
   A conflict carries its facts under a decision
   ---------------------------------------------------------------------------

   Both pigeonholes -- a Hall interval holding one variable too many, and a matching
   that saturates no more than all but one variable -- are reported at the ROOT as a
   factless emptying push whose derivation closes to [0 >= 1]. Under a DECISION they are
   reported with their facts, under [Store.deriving_ahead], so that 1UIP learning has a
   reason to resolve from and the derivation is on the page ahead of
   `rup ~facts >= 1` (D-0156, built by M7-T33). It is the arrangement cumulative's
   conflicts use (D-0096) and the root/decision split element's make (D-0101).
   [push_conflict] says which facts and why each literal the derivation leaves is one of
   them.

   ---------------------------------------------------------------------------
   Snapshotting: a derivation reads a snapshot, never the live store (I-X6)
   ---------------------------------------------------------------------------

   Every number a derivation depends on -- the interval, each variable's current and
   declared bounds, whether each current bound is root-established, and each interior
   hole with its cite -- is snapshotted into [snap] records at the moment of the pruning
   and the thunk reads nothing else from the store.

   WHAT IS BUILT EAGERLY AND WHAT LAZILY (D-0161 request 1, from the audit of what a
   run under [--no-proof] still paid for). The snapshot holds only what
   needs the store as it stood: the four bounds, the two root flags (they read the bound
   supports) and the interior holes (their cite reads the trail). The list of declared
   values the variable has lost BELOW and ABOVE its window is not stored: [gone] rebuilds
   it inside the [Deferred] from the four frozen bounds, so a snapshot whose derivation is
   never forced -- every snapshot under [--no-proof], most of them with a proof -- no
   longer pays two width-long lists per variable. The rule that makes this sound: a
   thunk may COMPUTE from snapshotted numbers whatever it likes; it may not READ the
   store. The rebuilt list is the eager one value for value, in the same order, so no
   proof byte moves. What the thunk DOES read live is
   [Encoding]'s constraint ids, and that is not an I-X6 violation for the reason I-X6
   is about: those ids are written once, by [Encoding.start_proof], before the first
   decision, and never move. Reading them later gives the same answer as reading them
   now. (They do not exist at all when no proof is being written, which is why
   [cid_of] says so rather than raising [Not_found] several layers down.)

   COST (the file-by-file review of the propagators, M16-file-review-T2, D-0190). Stage
   1 is O(P n) per pass for P candidate intervals, as above. A tight interval (as many
   confined variables as values) tests every other variable's LIVE bounds first and
   snapshots, and looks up in the Hall set, only one that can be pushed; the Hall set's
   own members pass that test and are found by name, O(k^2) for an interval of width k,
   which the scope bounds. With the proof, a pruning's derivation is O(|halls| w^2) to
   BUILD, because each excluded value's [excl] telescopes its own rungs, and every
   build is hash-consed whether or not its line is already on the page (D-0190 section 5
   measures it at half of a proof-mode run on 2011 cyclic-rcpsp). *)

module Lit = Baguette_proof.Lit
module Encoding = Baguette_proof.Encoding

(* Why a DECLARED value is no longer available to a variable, and therefore how the
   derivation is allowed to cancel its [x_eq_v] term out of that variable's
   at-least-one line. (Holes entered with Regin, M4-T2.)

   The Hall counting needs, per Hall variable, [sum_{v in S and decl(x)} x_eq_v >= 1]
   for the Hall value set [S], and it gets there from the declared-range at-least-one
   line by cancelling one term per declared value outside [S]. Each cancellation has to
   name a line that ESTABLISHES that the value is gone, at DEGREE-preserving strength --
   a [Weaken] axiom cancels the term but costs the degree (an axiom weakens, it asserts
   nothing, D-0009), so there is no
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
       -- exactly D-0064's per-bound rule (a bound established at the root is cited by
       its defining unit line), applied per hole. The cancellation is exact,
       nothing is left in the row, and a root conflict built on it still closes.
     - [Gone_hole facts]: the hole rests on a decision, so the unit would be FALSE. What
       is globally valid is the implication, and [Explanation.clause] states it:
       `~x_eq_v \/ ~facts`, RUP against the hole's own trace line plus two channelling
       halves. The facts stay in the derived row and are carried into the pruning's
       [Reason] alongside, which is what keeps the trace line true (I-P5, now part of
       I-P4: every bound move carries the facts its trace line negates). Such a hole
       rests on a decision, so a derivation holding this [Clause] never closes a ROOT
       conflict. *)
type gone = Gone_below | Gone_above | Gone_hole_root | Gone_hole of Reason.t

(* A variable, and the numbers any part of the derivation may ask about it. The declared
   pair is frozen at [make] time, because a bound fact is a chain of order literals
   counted from the declared bound (D-0010, [Order_reason]'s header); the current pair,
   the root flags and the holes are frozen per pruning. *)
type snap = {
  s_var : Var.t;
  s_name : string;
  s_dlo : int;
  s_dhi : int;
  s_lo : int;
  s_hi : int;
  (* Whether each current bound was established AT THE ROOT -- i.e. the trail entry
     supporting it belongs to level 0, or it has never moved off the declared bound.
     This is what decides whether [hall_cancels] and [target_cancel] may cite a line
     for it, and it
     is a fact about where the bound CAME FROM, not about the level the solver is at
     now: a root-established bound is a consequence of the model and stays citable
     however deep the search has gone. *)
  s_lo_root : bool;
  s_hi_root : bool;
  (* The INTERIOR holes of the window [s_lo, s_hi], ascending, each with the reason the
     derivation may cite for it ([Gone_hole_root] or [Gone_hole]). Snapshotted with
     everything else (I-X6): a hole's cite reads the trail as it stood at the pruning,
     and the thunk never looks again. Empty for a hole-free domain. The values below and
     above the window are NOT stored: [gone] rebuilds them from the four bounds above
     when a derivation is forced (D-0161 request 1, see [gone]). *)
  s_holes : (int * gone) list;
  (* The term's [rungs], carried so that a derivation reaches the ladder without the
     name (M7-T33, D-0156). Not a number the derivation depends on: the ladder ids are
     written once and never move (the header's I-X6 paragraph). *)
  s_rungs : (int -> int option) Lazy.t;
}

(* [rungs] is [Encoding.consistency_id] for this variable with the lookup done once, the
   first time a derivation cites one of its ladder rungs, and kept for the instance's
   lifetime (M7-T33, D-0156). Until then [excl] looked the variable up by NAME for every
   rung it cited -- a string hash per rung, O(width) rungs per excluded value -- which was
   12.4 % of 2011_cyclic-rcpsp_easy_6's proof mode (D-0145 section 5). Lazy because an
   instance whose explanations are never forced (no proof, or a test without an encoding
   for its variables) must not look anything up. The ids are the same, so every proof is
   byte-identical. *)
type term = {
  x : Var.t;
  name : string;
  decl_lo : int;
  decl_hi : int;
  rungs : (int -> int option) Lazy.t;
}

(* The state [cannot_prune] keeps across passes (D-0215): a matching, and the scratch its
   two searches reuse. NOTHING HERE IS A FACT ABOUT THE STORE. [g_val]/[g_owner] are a
   HINT, re-validated against the live domains at the start of every pass, so no trail
   entry and no stamp restores it on backtrack -- see [cannot_prune] for why none is
   needed. Values are slots [v - g_base] of the declared span. *)
type gate = {
  g_base : int;
  (* [g_val.(i)]: the value matched to term [i], or [g_base - 1] for none. *)
  g_val : int array;
  (* [g_owner.(v - g_base)]: the term matched to [v], or [-1]. [g_owner.(k) = i] iff
     [g_val.(i) = g_base + k], kept in step by [assign] and the repair. *)
  g_owner : int array;
  (* The augmenting search's visited marks, per value slot, against [g_stamp]. *)
  g_seen : int array;
  mutable g_stamp : int;
  (* The live domains of the pass, read once. *)
  g_doms : Domain.t array;
  (* Tarjan's per-term index, low-link, on-stack flag and stack; [g_reach.(i)]: [i]'s
     component reaches a free value, final once that component is closed. *)
  g_index : int array;
  g_low : int array;
  g_onstack : bool array;
  g_reach : bool array;
  g_stack : int array;
  mutable g_sp : int;
}

type t = {
  terms : term array;
  enc : Encoding.t;
  (* The Regin gate (D-0215), [None] when the scope's declared span exceeds
     [max_gate_span] or the caller turned it off; the stage then runs from scratch on
     every pass, as it did before. *)
  gate : gate option;
  (* The var-value-pair count above which [propagate] returns after stage 1 -- see the
     staging comment at the bottom of this file. *)
  cutoff : int;
  (* (x, z, v) -> the id of the .opb row "x <> v \/ z <> v", both orders of the pair
     present so a lookup never has to know which way [add_all_different] listed it. *)
  rows : (string * string * int, int) Hashtbl.t;
  (* M7-T28 (D-0151 section 2), the LEMMA-ROW HOOK: the same pairwise rows when they are
     root lemmas rather than model rows -- an all_different IMPLIED by an `inverse`, whose
     .opb states the channel rows and not the pairs ([Encoding.add_cited_lemma]). Keyed
     like [rows]; resolved to an id only when a derivation is rendered, because the id
     does not exist until [Encoding.start_proof] has written the lemma. Empty for every
     all_different the model posts. *)
  lemmas : (string * string * int, Encoding.lemma) Hashtbl.t;
  (* D-0216: the at-most-one nodes [amo] built, kept to be handed back when building them
     again would return them ([reuse]). Buckets of entries, allocated at the first use
     with a proof; [amo_count] entries. *)
  mutable amo_memo : amo_entry list array;
  mutable amo_count : int;
  (* D-0235: a bound vector on which stage 1 once moved nothing ([pass]). A hint, never
     a fact about the store, so no trail restores it. *)
  quiet : quiet;
  (* Whether [pass] may skip on [quiet] ([make]'s [?quiet], for test_prop's differential
     lane; every solver instance has it on). *)
  quiet_on : bool;
  (* D-0235: [canon.(i)] is the first term index with term [i]'s name, so that "is [i]
     in this set of terms" is the NAME comparison [pass] always made, as an array read.
     [canon.(i) = i] unless a variable occurs twice in the scope. *)
  canon : int array;
  (* Whether some variable occurs twice in the scope ([canon.(i) <> i] for some [i]). *)
  repeats : bool;
  (* D-0242: [pass]'s scratch, kept across calls. [lo0]/[hi0] are the pass-start bounds,
     overwritten at every pass; [by_lo]/[by_hi] are the term indices sorted by them,
     re-sorted by insertion at every pass ([sort_by]). A permutation and two arrays of
     numbers read off the store, never a fact about it: every pass rewrites [lo0]/[hi0]
     from the live domains before anything reads them, and an insertion sort of ANY
     permutation is sorted, so nothing needs the trail. Keeping the permutation is what
     makes the sort cheap, because one search step moves few bounds. *)
  lo0 : int array;
  hi0 : int array;
  by_lo : int array;
  by_hi : int array;
}

and quiet = { q_lo : int array; q_hi : int array; mutable q_valid : bool }

(* One entry of [amo_memo]: the key of a build (the at-most-one it extends, or [no_prev]
   for a pair; the pair's first variable, or -1; the variable added; the value), the node
   that build returned, and the table epoch at which [Explanation.rebuilds_to] last held
   for it (-1: not checked since the build). *)
and amo_entry = {
  k_prev : Explanation.t;
  k_a : int;
  k_u : int;
  k_v : int;
  mutable k_node : Explanation.t;
  mutable k_seen : int;
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

(* The widest declared span the gate indexes by value (D-0215): two int arrays of this
   length per instance. A wider scope runs the stage from scratch, which costs a list of
   every value per pass anyway. *)
let max_gate_span = 1 lsl 16

let make_gate terms =
  let n = Array.length terms in
  if n = 0 then None
  else
    let base = Array.fold_left (fun a tm -> Int.min a tm.decl_lo) max_int terms in
    let top = Array.fold_left (fun a tm -> Int.max a tm.decl_hi) min_int terms in
    let span = top - base + 1 in
    if span > max_gate_span then None
    else
      Some
        {
          g_base = base;
          g_val = Array.make n (base - 1);
          g_owner = Array.make span (-1);
          g_seen = Array.make span 0;
          g_stamp = 0;
          g_doms = Array.make n (Domain.singleton base);
          g_index = Array.make n (-1);
          g_low = Array.make n 0;
          g_onstack = Array.make n false;
          g_reach = Array.make n false;
          g_stack = Array.make n 0;
          g_sp = 0;
        }

(* [rows] is what [Encoding.add_all_different] returned, and the encoding is the live
   one: see the module header on I-X6. Reads each variable's domain, so it must be
   called before anything has narrowed it -- the same requirement, for the same D-0010
   reason, that [Linear.make] and [Ne.make] state. *)
let make ?(cutoff = default_cutoff) ?(lemma_rows = []) ?(gate = true) ?(quiet = true)
    store enc ~rows vars =
  let tbl = Hashtbl.create (2 * List.length rows) in
  List.iter
    (fun ((x, z, v), cid) ->
      Hashtbl.replace tbl (x, z, v) cid;
      Hashtbl.replace tbl (z, x, v) cid)
    rows;
  let lemmas = Hashtbl.create (2 * List.length lemma_rows) in
  List.iter
    (fun ((x, z, v), h) ->
      Hashtbl.replace lemmas (x, z, v) h;
      Hashtbl.replace lemmas (z, x, v) h)
    lemma_rows;
  let terms =
    Array.of_list
      (List.map
         (fun x ->
           let d = Store.get store x in
           let name = Store.name store x in
           {
             x;
             name;
             decl_lo = Domain.lo d;
             decl_hi = Domain.hi d;
             rungs = lazy (Encoding.consistency_ids enc name);
           })
         vars)
  in
  let canon =
    Array.map
      (fun tm ->
        let rec first j = if terms.(j).name = tm.name then j else first (j + 1) in
        first 0)
      terms
  in
  {
    terms;
    enc;
    gate = (if gate then make_gate terms else None);
    cutoff;
    rows = tbl;
    lemmas;
    amo_memo = [||];
    amo_count = 0;
    canon;
    repeats = Array.exists Fun.id (Array.mapi (fun i c -> c <> i) canon);
    quiet_on = quiet;
    quiet =
      {
        q_lo = Array.make (Array.length terms) 0;
        q_hi = Array.make (Array.length terms) 0;
        q_valid = false;
      };
    lo0 = Array.make (Array.length terms) 0;
    hi0 = Array.make (Array.length terms) 0;
    by_lo = Array.init (Array.length terms) Fun.id;
    by_hi = Array.init (Array.length terms) Fun.id;
  }

let vars t = Array.to_list (Array.map (fun tm -> tm.x) t.terms)

(* [f j] for every term [j] naming term [i]'s variable, [i] included: a change to [i]'s
   domain is a change to theirs, so whatever is cached per term is invalidated for all of
   them (D-0235). One term per variable unless the scope repeats one. *)
let twins t i f =
  if not t.repeats then f i
  else
    let c = t.canon.(i) in
    for j = 0 to Array.length t.terms - 1 do
      if t.canon.(j) = c then f j
    done

(* Whether the trail entry supporting this bound was pushed at level 0, or the bound has
   never moved: the level the bound BELONGS to, not the one in force now. Stays EAGER,
   because it reads the supports as they stand at the snapshot.

   D-0161 request 1: [Store.at_root] answers [level_of_index sup = 0] in one comparison
   instead of a binary search over the open levels -- the same answer by I-T2 (the marks
   are monotone, so an entry is at level 0 iff it precedes the first mark). Asked twice
   per variable per snapshot, the search was 2.2 % of 2011_cyclic-rcpsp_easy_6's
   [--no-proof] instructions. *)
let established_at_root store v ~lower =
  let sup = if lower then Store.lo_support store v else Store.hi_support store v in
  sup = Store.no_support || Store.at_root store sup

let range a b = List.init (Int.max 0 (b - a + 1)) (fun i -> a + i)

(* Membership of a Hall VALUE SET, by binary search over its values sorted once
   (M20-pernode-T4, D-0235). Every [keep] of a Regin set used to be [List.mem v vals]:
   OCaml's [List.mem] is POLYMORPHIC equality, a [caml_compare] call per element, and
   [hall_facts] asks it once per hole of every Hall member for every removal, which made
   [compare_val] the single largest symbol of elitserien handball12's profile (10 %). The
   answer is the same predicate, so every reason and every derivation is unchanged. *)
let mem_of vals =
  let a = Array.of_list vals in
  Array.sort Int.compare a;
  fun v ->
    let rec go lo hi =
      lo < hi
      &&
      let mid = (lo + hi) lsr 1 in
      let w = a.(mid) in
      if w = v then true else if w < v then go (mid + 1) hi else go lo mid
    in
    go 0 (Array.length a)

(* The entry that took [value] out of [var], or [None].

   What decides whether a hole may be cited as a unit is the LEVEL it was established at,
   and [Store.at_root] reads that off the entry's trail position, [pos] (M6-T15; the
   level-0 case of [Store.level_of_index], one comparison, D-0161 request 1).
   Until M7-T33 this walked the WHOLE trail backwards once per hole asked about, because
   when it was written the entry did not carry its position; on the Challenge's black-hole
   instances, once element's own walk was gone (D-0155), that walk was 70 to 89 % of the
   run. [Store.remover] answers from [var]'s entry history by binary search (D-0088), and
   it is the SAME entry: its predicate (on [var], [value] in [old], not in [now]) is the
   walk's, [Store.remover_scan] is the walk started at the same position, and
   [Store.remover] agrees with that scan under [BAGUETTE_DEBUG] by physical equality.
   Element made the same move in D-0155. Read eagerly, at snapshot time (I-X6).

   [None] is a hole with no trail entry behind it: a gap in a DECLARED set domain
   (`var {1,3,5}: x`). The .opb states such a gap as a clause of its own
   ([Encoding.declare_int_with_holes]; M7-T11 removed the [reject_set_domain] check
   that used to refuse these domains), so it is cited as a [Gone_hole] with no facts. *)
let hole_cite store var value =
  match Store.remover store ~before:(Store.trail_length store) ~var value with
  | Some e when Store.at_root store e.Store.pos -> Gone_hole_root
  | Some e -> Gone_hole e.Store.reason
  | None -> Gone_hole (Reason.of_facts Reason.none)

(* [s_holes]: the interior holes of [d], ascending, each cited from the trail NOW (at
   snapshot time, I-X6). *)
let holes_of store tm d =
  if not (Domain.has_holes d) then []
  else
    List.filter_map
      (fun v -> if Domain.mem d v then None else Some (v, hole_cite store tm.x v))
      (range (Domain.lo d) (Domain.hi d))

(* Every DECLARED value [s] can no longer take, ascending, with the reason the derivation
   may cite for it: below the window, then the holes inside it, then above. The order is
   what makes an [alo_over] over an INTERVAL value set emit exactly the summands the
   interval-only version of M4-T1 emitted, in the same order, so stage 1's proofs did not
   change when M4-T2 generalised it to value sets.

   BUILT WHEN A DERIVATION IS FORCED, NOT AT THE SNAPSHOT (D-0161 request 1). Until then
   [snap_of] built this list for every variable at every snapshot -- two [range] lists of
   up to the declared width per variable per pass -- and only a derivation ever read the
   below/above part: the REASON reads the holes alone ([hall_facts]). That was 37.3 % of
   2011_cyclic-rcpsp_easy_6's [--no-proof] instructions at 10 000 nodes, built and never
   read. Rebuilding it here is sound under I-X6 because the two outer runs are functions
   of [s_dlo], [s_lo], [s_hi] and [s_dhi] alone -- numbers frozen in the snapshot -- with
   the constant tags [Gone_below]/[Gone_above]; the store is not read. Only the holes need
   the trail as it stood, and they stay eager in [s_holes]. Same values, same order, same
   tags as the eager list, so every proof line is the same byte for byte. *)
let gone s =
  List.map (fun v -> (v, Gone_below)) (range s.s_dlo (s.s_lo - 1))
  @ s.s_holes
  @ List.map (fun v -> (v, Gone_above)) (range (s.s_hi + 1) s.s_dhi)

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
    s_holes = holes_of store tm d;
    s_rungs = tm.rungs;
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

(* One lookup per table (D-0216): an all_different an `inverse` implies has no model rows,
   and its every pair went through three hashes of the (string, string, int) key here. *)
let row t s1 s2 v =
  let key = (s1.s_name, s2.s_name, v) in
  match if Hashtbl.length t.rows = 0 then None else Hashtbl.find_opt t.rows key with
  | Some id -> id
  | None -> (
      match Hashtbl.find_opt t.lemmas key with
      | Some h -> cid_of "the pairwise root lemma" (Encoding.root_lemma_id t.enc h)
      | None ->
          invalid_arg
            (Printf.sprintf
               "Alldiff: no model row for %s <> %d \\/ %s <> %d. \
                Encoding.add_all_different posts one per pair per SHARED declared value, \
                so this means the pair's declared domains do not both contain %d."
               s1.s_name v s2.s_name v v))

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
(* D-0216, for test_endtoend's regression lane: how many pairwise at-most-one nodes were
   built, and a switch that turns [reuse] off so the lane can compare the proof both ways.
   Neither is read by the solver. *)
let pair_builds = ref 0
let amo_reuse = ref true

let pair_amo t sx sz v =
  incr pair_builds;
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
(* D-0216: the node [build] returns, or the one the same key's last build returned when
   building again would return that very node ([Explanation.rebuilds_to]). [amo]'s builds
   are deterministic in the key: a pair's node in (x, z, v) through [pair_amo]'s ids, a
   step's in the at-most-one it extends (by identity, which fixes the variables it covers
   and their order) and in (u, v). A step's operands are that at-most-one, obtained
   through this function, and pairs, which [rebuilds_to] checks, so its induction holds.
   A removal under a Hall set of m variables over m values rebuilt, per value, the m+1
   variables' (m+1)m/2 pairs, all but y's m of them hits of the table (2011_black-hole_10:
   156 removals with m = 47, 8.3 M pairs); it now builds y's m pairs and finds the rest
   here, unless a node left the table since. A key not found, or a node that no longer
   rebuilds to itself, costs a build, never a wrong node. *)
let no_prev = Explanation.model_row (-1)

let reuse t ~prev ~a ~u v build =
  let epoch = if !amo_reuse then Explanation.reuse_epoch () else -1 in
  if epoch < 0 then build ()
  else (
    (* As many buckets as the instance has (variable, value) pairs, times four, within
       [1 024, 65 536]; emptied when it holds as many entries as buckets, which bounds the
       nodes it keeps alive past their lines. *)
    if Array.length t.amo_memo = 0 then (
      let span =
        Array.fold_left (fun w tm -> max w (tm.decl_hi - tm.decl_lo + 1)) 1 t.terms
      in
      let want = min 65536 (max 1024 (4 * Array.length t.terms * span)) in
      let size = ref 1024 in
      while !size < want do
        size := 2 * !size
      done;
      t.amo_memo <- Array.make !size []);
    (* The key's fields are small consecutive ints (variable ids, values); a
       multiplicative mix and a fold of the high bits spread them over the low bits the
       bucket is taken from. *)
    let h =
      Explanation.operand_id prev lxor (a * 0x2545F491) lxor (u * 0x9E3779B1)
      lxor (v * 0x632BE5AB)
    in
    let h = h lxor (h lsr 29) lxor (h lsr 13) in
    let b = h land (Array.length t.amo_memo - 1) in
    let rec find = function
      | [] -> None
      | e :: rest ->
          if e.k_prev == prev && e.k_a = a && e.k_u = u && e.k_v = v then Some e
          else find rest
    in
    match find t.amo_memo.(b) with
    | Some e
      when e.k_seen = epoch
           || Explanation.rebuilds_to e.k_node
              &&
              (e.k_seen <- epoch;
               true) ->
        e.k_node
    | Some e ->
        let node = build () in
        e.k_node <- node;
        e.k_seen <- -1;
        node
    | None ->
        let node = build () in
        if t.amo_count >= Array.length t.amo_memo then (
          Array.fill t.amo_memo 0 (Array.length t.amo_memo) [];
          t.amo_count <- 0);
        t.amo_memo.(b) <-
          { k_prev = prev; k_a = a; k_u = u; k_v = v; k_node = node; k_seen = -1 }
          :: t.amo_memo.(b);
        t.amo_count <- t.amo_count + 1;
        node)

let amo t ss v =
  match ss with
  | [] | [ _ ] -> invalid_arg "Alldiff.amo: at least two variables"
  | first :: second :: rest ->
      let id s = Var.to_int s.s_var in
      (* [rhave] is the variables covered so far, last first; [m] their number. *)
      let rec grow acc rhave m = function
        | [] -> acc
        | u :: more ->
            let step =
              reuse t ~prev:acc ~a:(-1) ~u:(id u) v (fun () ->
                  Explanation.combine
                    (Explanation.term (m - 1) acc
                    :: List.rev_map (fun s -> Explanation.term 1 (pair_amo t u s v)) rhave
                    )
                    m)
            in
            grow step (u :: rhave) (m + 1) more
      in
      let base =
        reuse t ~prev:no_prev ~a:(id first) ~u:(id second) v (fun () ->
            pair_amo t first second v)
      in
      grow base [ second; first ] 2 rest

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
(* The ladder rung of [s]'s variable at [u], through the term's once-looked-up [rungs]
   (M7-T33, D-0156): the id [Encoding.consistency_id] gives, without the name lookup. *)
let rung s u = cite (cid_of "ladder rung" (Lazy.force s.s_rungs u))

let excl t s v =
  if v < s.s_lo then
    Explanation.combine
      (cite (cid_of "d_hi" (Encoding.direct_hi_id t.enc s.s_name v))
      :: List.map (rung s) (range (v + 1) (s.s_lo - 1)))
      1
  else if v > s.s_hi then
    Explanation.combine
      (cite (cid_of "d_lo" (Encoding.direct_lo_id t.enc s.s_name v))
      :: List.map (rung s) (range (s.s_hi + 1) (v - 1)))
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

   The excluded values are read off [gone s] rather than recomputed, because the
   *reason* each one is gone is what decides which line cancels it. For an interval
   [keep] this is value-for-value and order-for-order what M4-T1 computed: a Hall
   variable's window is inside the interval, so every declared value outside the
   interval is outside the window too, and no hole of its is ever excluded. *)
let alo_over t s ~keep =
  Explanation.combine
    (cite (cid_of "at-least-one" (Encoding.at_least_one_id t.enc s.s_name))
    :: List.filter_map
         (fun (v, g) -> if keep v then None else Some (exclude_summand t s v g))
         (gone s))
    1

(* The counting argument itself: one at-least-one per Hall variable, one at-most-one per
   Hall value over whichever variables could take it. [extra] is the variable being
   pruned, which joins the at-most-one lines but contributes no at-least-one -- that
   asymmetry is exactly why the sum leaves ITS terms behind and cancels everything else.

   A value only one variable in scope can take gets a literal axiom instead of an
   at-most-one line: "at most one of {x} takes v" IS ~x_eq_v >= 0, and a value no
   variable can take gets nothing, because there is no term to cancel. *)
(* WHAT THE DERIVATIONS OF ONE TIGHT SET SHARE, BUILT ONCE (M20-pernode-T4, D-0242). Every
   derivation a tight set (a Regin set, or a stage 1 interval) justifies sums the same
   at-least-one line per member, from the same snapshots and the same [keep]: only the
   at-most-one lines (which [y] joins) and [y]'s leftovers differ. [alo_lines] hands back
   the lines the first forced derivation built, when building them again would return
   those very nodes, by D-0216's rule ([Explanation.rebuilds_to], checked again only after
   a node left the table, [Explanation.reuse_epoch]): an at-least-one line's operands are
   model rows, the [excl] chains (whose own operands are model rows) and hole clauses, so
   the shallow check is the whole induction. Otherwise, and always when hash-consing or
   [amo_reuse] is off (test_endtoend compares the bytes both ways), they are built, which
   is what every derivation did. The same nodes either way, so the same bytes.
   [memo_hits] counts what the memo handed back.

   WITHDRAWN (D-0242 section 3): the same memo for the at-most-one lines of the removals
   from one [y], kept while no node left the table. Same bytes in every normal run, but
   under BAGUETTE_DEBUG (which forces and re-forces derivations) it changed the proof of
   2018 soccer-computational, so "no node left" does not establish what a rebuild
   returns, and only the [rebuilds_to] rule is used. *)
type 'a memo = { mutable m_val : 'a option; mutable m_seen : int }

let memo () = { m_val = None; m_seen = -1 }
let memo_hits = ref 0
let memo_epoch () = if !amo_reuse then Explanation.reuse_epoch () else -1

let alo_lines t ~vals ~halls memo =
  let epoch = memo_epoch () in
  match memo.m_val with
  | Some nodes
    when epoch >= 0
         && (memo.m_seen = epoch
            || List.for_all Explanation.rebuilds_to nodes
               &&
               (memo.m_seen <- epoch;
                true)) ->
      incr memo_hits;
      nodes
  | _ ->
      let keep = mem_of vals in
      let nodes = List.map (fun s -> alo_over t s ~keep) halls in
      memo.m_val <- Some nodes;
      memo.m_seen <- -1;
      nodes

let core_summands ?alo t ~vals ~halls ~extra =
  let all = halls @ Option.to_list extra in
  let amos () =
    List.concat_map
      (fun v ->
        match List.filter (fun s -> s.s_dlo <= v && v <= s.s_dhi) all with
        | [] -> []
        | [ s ] -> [ Explanation.weaken [ (1, Lit.negate (Lit.eq s.s_name v)) ] ]
        | ss -> [ Explanation.term 1 (amo t ss v) ])
      vals
  in
  (match alo with
  | Some memo -> List.map (Explanation.term 1) (alo_lines t ~vals ~halls memo)
  | None ->
      let keep = mem_of vals in
      List.map (fun s -> Explanation.term 1 (alo_over t s ~keep)) halls)
  @ amos ()

(* CANCELLING THE BOUND LITERALS. [alo_over] narrows a Hall variable's at-least-one line
   with one [excl] per declared value outside the value set, and each [excl] carries the
   bound it rests on into the sum as a literal: [a - decl_lo] copies of ~x_ge_lo(x), and
   [decl_hi - b] of x_ge_(hi(x)+1). The pruned variable [y] leaves one more, from its
   telescope. This section cancels them with the lines that already state those bounds:
   [hall_cancels] for the Hall variables, [target_cancel] for [y], [overshoot_cancel] for
   an emptying push. Read it together with explanation.ml's [Defining] section before
   changing it.

   THE RULE. A bound literal is cancelled exactly when its bound was ESTABLISHED AT THE
   ROOT, by an [Explanation.defining] summand, which [Justify.defining_lit] resolves to
   the UNIT line already stating the bound (the trace line, in practice), minting one
   only if there is none. The cancellation is exact: the term goes and the degree stays.
   A bound a decision set is left in the row as its literal.

   WHY IT IS SOUND. Left uncancelled, the literals make the derived row the globally
   valid "the pruning, disjoined with the bounds it read", the shape [Ne]'s clause
   already has, so a pruning is right either way. The test is the level the bound was
   ESTABLISHED at, not the level the solver is at: a bound the root fixpoint set is a
   consequence of the model, so its unit line is true and citable at any depth, while a
   unit line for a bound a decision set would be false. [snap.s_lo_root]/[s_hi_root]
   carry the test, snapshotted with everything else the derivation reads (I-X6). So a
   Hall inference made three decisions deep still cancels whatever the root established.

   WHY IT IS NEEDED. A root CONFLICT must derive [0 >= 1], and a row with literals left
   in it is not contradicting: veripb 3.0.2 says "The constraint with ID n is not
   contradicting, as specified by the hint" (M1-T17 met the same message from [Ne]'s
   side). With every root bound cancelled, the root derivation closes on its own.

   History, in short. Cancelling needs "the id of the line that establishes this bound
   fact", the gap D-0009 left open in the ADT, which M4-T7 closed with
   [Explanation.defining] (D-0064). M4-T1's stand-in was [Explanation.clause [lit]], the
   same arithmetic wearing a label search.ml then read as "not numeric" (D-0061's
   recorded cost), and it could only say "level 0 or nothing", switching the whole
   cancellation off under a decision. *)
(* The Hall variables' share: one copy of ~x_ge_lo(x) per declared value below the
   value set and one of x_ge_(hi(x)+1) per declared value above it, which is exactly how
   many [excl] summands [alo_over] added in each direction. A Hall variable's window is
   inside the value set's hull, so [below > 0] implies its lo really has moved and
   [Lit.ge] below names a literal the encoding has (likewise [above] and [Lit.le]). *)
let hall_cancels ~keep ~halls =
  List.concat_map
    (fun s ->
      (* The [Gone_below]/[Gone_above] entries of [gone s] that [keep] excludes, counted
         over the two runs directly rather than over the rebuilt list: the same numbers. *)
      let count a b = List.length (List.filter (fun v -> not (keep v)) (range a b)) in
      let below = count s.s_dlo (s.s_lo - 1) and above = count (s.s_hi + 1) s.s_dhi in
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
   and nothing else of y's survives. [y] has no at-least-one line ([alo_over]), and that
   asymmetry is the whole reason its terms are what the derivation is left holding, so
   it must not be handed to [hall_cancels], which counts a Hall variable's [excl]
   summands.

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
(* CAPPED AT y's DECLARED TOP (D-0086 (c): a telescope stops at the declared top).
   [pass]'s pigeonhole arm pushes a CONTAINED y to [b + 1], and [b] is the interval's end
   -- some variable's upper bound, not necessarily one y's declared domain reaches. The
   values of [y.s_lo .. b] above [decl_hi(y)] have no forward channelling clause (y takes
   none of them by declaration), and the core sum leaves no [~y_eq_v] for them to cancel
   either ([core_summands] filters the at-most-one lines by declared domain), so the
   telescope stops at [decl_hi(y)] and its residue [y_ge_(decl_hi+1)] is the constant
   false. Uncapped it asked for a [direct_fwd_id] that does not exist: exit 2 on `var
   1..3: a, b, c; var 1..2: d; all_different_int([a, b, c, d])`, the four-variable
   pigeonhole. *)
let prune_summands ?alo t ~a ~b ~halls ~y ~lower =
  let keep, drop =
    if lower then
      (range y.s_lo (Int.min b y.s_dhi), range (Int.max a y.s_dlo) (y.s_lo - 1))
    else (range a y.s_hi, range (y.s_hi + 1) (Int.min b y.s_dhi))
  in
  core_summands ?alo t ~vals:(range a b) ~halls ~extra:(Some y)
  @ List.map (fun v -> Explanation.weaken [ (1, Lit.eq y.s_name v) ]) drop
  @ List.map
      (fun v -> cite (cid_of "d_fwd" (Encoding.direct_fwd_id t.enc y.s_name v)))
      keep

(* THE OTHER END OF AN EMPTYING PUSH. [overshoot_cancel] cancels the residue a
   pigeonhole push leaves, for a root-established upper bound. (Found by M4-T2: a defect
   M4-T1 shipped latent.)

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
   exactly: a [Defining] summand (D-0064) and its per-bound root test, once more.

   The test [b + 1 > y.s_hi] is what tells the two arms apart and is not a heuristic: in
   the [n = k] arm the pushed variable is NOT contained, so its upper bound is strictly
   above [b] and the residue IS the pruning and must stay; in the [n > k] arm it is
   contained, so the push always oversteps. Only the lower direction needs this, because
   [pass] only ever empties a domain downward-out-of ([push ~lower:true]); the mirror
   case is written out in this comment rather than in code because nothing reaches it.

   [b < y.s_dhi] (M7-T22, D-0086 (c)) is the first paragraph's own condition, which the
   guard did not state: the residue [y_ge_(b+1)] is a literal the encoding has only when
   [b + 1 <= decl_hi(y)]. Past it the residue is the constant false, there is nothing to
   cancel, and the ladder has no rung [y_ge_(decl_hi+1) -> y_ge_decl_hi] to cite. Without
   it the bench/fuzz sweep found the `Alldiff: ladder rung has no constraint id` crash
   (exit 2) on models where an element constraint had shaved y's upper bound below a Hall
   interval reaching y's declared top. *)
let overshoot_cancel ~b ~y ~lower =
  if lower && b + 1 > y.s_hi && b < y.s_dhi && y.s_hi < y.s_dhi && y.s_hi_root then
    List.map (rung y) (range (y.s_hi + 1) b)
    @ [ Explanation.defining 1 (Lit.le y.s_name y.s_hi) ]
  else []

let prune_expl ?alo t ~a ~b ~halls ~y ~lower =
  Explanation.deferred (fun () ->
      Explanation.combine
        (prune_summands ?alo t ~a ~b ~halls ~y ~lower
        @ hall_cancels ~keep:(fun v -> a <= v && v <= b) ~halls
        @ target_cancel ~y ~lower @ overshoot_cancel ~b ~y ~lower)
        1)

(* ------------------------------------------------------ a VALUE is removed (M4-T2)

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
let remove_summands ?alo t ~vals ~halls ~y ~value =
  let mine = List.filter (fun w -> y.s_dlo <= w && w <= y.s_dhi) vals in
  core_summands ?alo t ~vals ~halls ~extra:(Some y)
  @ List.filter_map
      (fun w ->
        if w = value then None else Some (Explanation.weaken [ (1, Lit.eq y.s_name w) ]))
      mine

let remove_expl ?alo t ~keep ~vals ~halls ~y ~value =
  Explanation.deferred (fun () ->
      Explanation.combine
        (remove_summands ?alo t ~vals ~halls ~y ~value @ hall_cancels ~keep ~halls)
        1)

(* THE PIGEONHOLE over a value SET, which is the M4-T2 shape of the sentence this
   module's header already makes about an interval: with no [extra] at all and one more
   variable than there are values, every term of the core sum cancels and the degree does
   not, so the row is [0 >= 1].

   [halls] here is the WHOLE violating set -- |halls| = |vals| + 1 -- and that one
   difference is the whole difference between a pruning and a refutation. It is reported
   the way [pass] reports its own: handed to a mutator that must fail, so
   [Store.apply]'s [Failed] arm pairs it with [Reason.none] and no `rup` conflict line
   claims a counting argument as reverse unit propagation (I-X10). That is the
   ROOT's arrangement since M7-T33; under a decision the same derivation is the
   conflict's, with its facts, written ahead of its line ([push_conflict], D-0156). *)
let conflict_expl t ~vals ~halls =
  let keep = mem_of vals in
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
         line's tail owes them (I-P5: every bound move carries the facts its trace line
         negates). Only the EXCLUDED holes: a hole inside the value
         set is never cancelled, contributes nothing, and naming it would put a fact in
         the tail that the derivation does not read. For an interval value set there are
         no excluded holes at all, which is why stage 1's reasons are unchanged. *)
      @ List.concat_map
          (fun (v, g) ->
            match g with Gone_hole r when not (keep v) -> Reason.facts r | _ -> [])
          s.s_holes)
    halls

let prune_reason ~keep halls y ~lower =
  (if lower then Reason.at_least ~name:y.s_name ~decl:y.s_dlo y.s_lo
   else Reason.at_most ~name:y.s_name ~decl:y.s_dhi y.s_hi)
  :: hall_facts ~keep halls

(* A value removal reads no bound of [y] -- the counting is over DECLARED domains and
   [y]'s window never enters the row. Both of [y]'s bounds are named anyway, and that is
   deliberate rather than sloppy: the derivation's top level weakens [y]'s own [y_eq_w]
   terms away, so [Explanation.top_weaken_owners] names [y] and D-0026's agreement check
   requires the reason to name it too (D-0026: reason and justification are separate
   values, checked to name the same variables). A tail with a fact the derivation did
   not need is a WEAKER trace line, which is sound; a tail missing one breaks I-P5. *)
let remove_reason_of y hall_facts =
  Reason.at_least ~name:y.s_name ~decl:y.s_dlo y.s_lo
  :: Reason.at_most ~name:y.s_name ~decl:y.s_dhi y.s_hi
  :: hall_facts

let remove_reason ~keep halls y = remove_reason_of y (hall_facts ~keep halls)

(* ------------------------------------- a conflict carries its facts (M7-T33, D-0156)

   THE RULE: at the root a pigeonhole conflict is factless; under a decision it carries
   the facts listed below and its derivation is written ahead of its line.

   WHY. Until M7-T33 both pigeonholes -- [pass]'s push that empties a contained variable
   and [regin_pass]'s failed matching -- reached the store as a pruning that must fail,
   and [Store.apply]'s [Failed] arm paired the derivation with [Reason.none] at every
   depth. That is sound (search.ml writes a factless conflict's derivation on the page,
   the arm D-0040 introduced, and the decision nogood closes the branch), but it hands
   [Learn.at_conflict] an EMPTY cut: on 2015_p1f_13 under the native [inverse] the run
   learned 0 clauses (D-0151 section 2), where std's decomposition learned 523.

   AT THE ROOT nothing changes, deliberately: there is no branch to learn from, every
   bound the derivation reads is root-established and cancelled ([hall_cancels],
   [target_cancel], [overshoot_cancel]), so the derivation closes to [0 >= 1] itself and
   search.ml's root arm writes it. Every root refutation is byte-identical -- element.ml's
   [no_position_conflict] makes the same split (D-0101).

   UNDER A DECISION the conflict is reported with the facts below and under
   [Store.deriving_ahead], so [Trace.conflict_line] writes the derivation FIRST and then
   `rup ~facts >= 1` (cumulative's arrangement, D-0096; store.ml's [c_ahead]). That line
   is the counting argument, so it is NOT reverse unit propagation over the pairwise
   rows on its own (I-X10 asks every trace line to be RUP against what is on the page
   before it, which is why D-0040 writes the derivation first); after the derivation it is
   unit propagation against one line, because every literal the derivation leaves in its
   row is the negation of a fact listed here:

     - a Hall variable's bound literal that [hall_cancels] could not cancel (moved under
       a decision) -- its bound fact, from [hall_facts];
     - a deep hole's [Gone_hole] clause -- the remover's facts, from [hall_facts], which
       names exactly the EXCLUDED holes, the only ones the derivation cancels;
     - the pushed variable's [~y_ge_lo(y)] -- its lower bound; and its residue
       [y_ge_(b+1)], which [overshoot_cancel] closes only for a root-established upper
       bound. Under a decision it stays, and the fact [y <= hi(y)] with [hi(y) <= b]
       falsifies it through the ladder rungs [hi(y)+1 .. b], which unit propagation
       walks. That fact is the CROSSED OPPOSING BOUND [Store.apply]'s [Failed] arm says
       a conflict line needs and a pruning's reason does not carry, which is why the
       pigeonhole's facts are [remove_reason]'s (both of [y]'s bounds) and not
       [prune_reason]'s.

   A root-established fact is listed too, where the derivation cancelled its literal: it
   is harmless on a tail (Analysis drops root nodes from every cut), and listing it keeps
   this free of a second copy of the cancellation rule -- element.ml's [conflict_facts]
   reasons the same way. *)
(* Each fact once, first occurrence kept. Two members of a Regin set holed by the same
   remover list its facts twice (k-scene: int_ne(x_i, k) with k = 2 gives every x_i the
   tail [k <= 2]), and a conflict line is a clause: a repeat is a longer line saying the
   same thing. Once per conflict, linear in the facts. *)
let distinct_facts facts =
  let seen = Hashtbl.create 16 in
  List.filter
    (fun f ->
      if Hashtbl.mem seen f then false
      else (
        Hashtbl.replace seen f ();
        true))
    facts

let push_conflict store ~facts why =
  Store.deriving_ahead store (fun () ->
      Store.conflict store (Reason.because ~concludes:None (distinct_facts facts) why))

(* ------------------------------------------------------------------- propagation *)

exception Found of Store.conflict

(* [perm] sorted by [key], ascending, in place, by insertion. Ties keep no particular
   order, and none is needed: [hall_free] reads only counts and the values at run ends,
   and [pass_scan] only counts along [by_hi] and marks what it walked. O(n + the number
   of pairs out of order), which across one search step is the few bounds that moved. *)
let sort_by (key : int array) perm =
  for j = 1 to Array.length perm - 1 do
    let i = perm.(j) in
    let k = key.(i) in
    let p = ref (j - 1) in
    while !p >= 0 && key.(perm.(!p)) > k do
      perm.(!p + 1) <- perm.(!p);
      decr p
    done;
    perm.(!p + 1) <- i
  done

(* One pass: every candidate interval, in a fixed order, pushing what it can. Returns
   [true] if anything moved, so [propagate] can re-run; raises [Found] on a conflict,
   which is the one non-local exit -- a conflict abandons the pass, and unwinding
   through the interval loops with a flag would be the same control flow spelled longer.

   Candidate endpoints are the current lo and hi values, which is the standard
   restriction: a Hall interval can always be shrunk to one whose ends are a variable's
   bounds without losing any variable from its set.

   ONE SNAPSHOT, EVERY DEDUCTION (I-P6, from M6-T19: a pass photographs the store once
   and applies every deduction the photograph justifies). The pass takes [snaps] once
   and applies
   every push the snapshot justifies before [propagate] takes the next one. Until M6-T19
   it returned at the first push that landed, so a Hall set confining k variables cost
   k + 1 snapshots and k + 1 interval enumerations; the restart bought the one-line
   argument "everything examined is current", which I-P6 replaces with this one: a Hall
   set's facts are frozen at snapshot values that still hold at every later push of the
   pass, because bounds only tighten within a level (I-D3), and the pruned variable [y]
   is re-read live at the push. Containment computed from the older, wider bounds is a
   SUBSET of the true containment, so a set the stale snapshot calls Hall is Hall; what
   staleness can do is miss a set that only the newer bounds reveal, or push a [y] the
   live store already has there ([Unchanged]), or push a [y] the newer bounds have since
   confined inside the interval -- which empties it, and that is the pigeonhole the
   store reports as a conflict. The next pass, which [stage_bounds] runs until a pass
   changes nothing, recovers whatever this one missed. *)
let pass_scan t store ~lo0 ~hi0 =
  let nt = Array.length t.terms in
  let moved = ref false in
  (* THE PASS-START SNAPSHOTS, TAKEN WHEN FIRST READ (M20-pernode-T4, D-0235). [snap i]
     is the snapshot [snap_of] took of every term at the start of the pass until D-0235;
     it is now taken the first time the pass reads it, which is the same value as long
     as nothing has changed term [i] in between -- a snapshot reads [i]'s domain, its two
     supports and the remover of each of its holes, and within a pass only a push ON
     [i] moves any of them. So the one rule is: a push forces the pushed term's snapshot
     BEFORE it lands ([dirty] marks it after). A pass that reaches no Hall interval
     snapshots nothing, where it used to snapshot every term with a [Store.remover]
     search per hole: 19 to 23 % of elitserien, tppv and costas instructions. [live i]
     is the snapshot of the store as it stands now, which the [n = k] arm reads. *)
  let cache = Array.make nt None and dirty = Array.make nt false in
  let snap i =
    match cache.(i) with
    | Some s -> s
    | None ->
        let s = snap_of store t.terms.(i) in
        cache.(i) <- Some s;
        s
  in
  let live i = if dirty.(i) then snap_of store t.terms.(i) else snap i in
  (* [inset.(canon.(i))]: term [i]'s NAME is a member of the Hall set being scanned. *)
  let inset = Array.make nt false and inmask = Array.make nt false in
  (* [lo_l]/[hi_l]: the LIVE bounds. Only this pass's own pushes change the store while
     it runs, so the pass-start bounds updated at each push that lands are what
     [Store.get] would read, without reading it per term per tight interval. *)
  let lo_l = Array.copy lo0 and hi_l = Array.copy hi0 in
  (* The terms by ascending lower and upper bound, the instance's kept permutations
     ([sort_by] is a walk over them when [pass] has just sorted them). The intervals are
     enumerated over them: [a] at the first term of each run of equal lower bounds, [b]
     at the last of each run of equal upper bounds, so the same distinct values in the
     same ascending order as the sorted lists of bounds this used to build (D-0242). The
     number of terms inside [a, b] is a pointer walked along [by_hi] for each [a] rather
     than a filter of the scope per interval. *)
  sort_by lo0 t.by_lo;
  sort_by hi0 t.by_hi;
  let by_lo = t.by_lo and by_hi = t.by_hi in
  (* One push, with both halves of D-0026 (the reason and the justification) built from
     the same snapshot. It raises [Found] on a conflict and sets [moved] on a change; a
     push that changes nothing (the bound is already there) falls through, which is how
     [Unchanged] can happen at all here. *)
  let push ?alo ~halls ~a ~b ~y ~yi ~lower bound =
    (* M7-T33 (D-0156): the push that would EMPTY [y] -- [pass]'s pigeonhole arm, or an
       [n = k] push whose live [y] is now confined -- is the conflict, reported with its
       facts under a decision (see [push_conflict]). [y]'s bounds here are the ones the
       store will read: live for the [n = k] arm, and for the pigeonhole arm a snapshot
       whose [s_hi <= b] the live bound can only undercut, so this test and the store's
       [Failed] agree. At the root the push runs and fails as before. *)
    let empties = if lower then bound > y.s_hi else bound < y.s_lo in
    if empties && Store.level store > 0 then
      raise
        (Found
           (push_conflict store
              ~facts:(remove_reason ~keep:(fun v -> a <= v && v <= b) halls y)
              (prune_expl t ~a ~b ~halls ~y ~lower)));
    let j =
      Reason.because
        ~concludes:
          (Some
             (if lower then Reason.at_least ~name:y.s_name ~decl:y.s_dlo bound
              else Reason.at_most ~name:y.s_name ~decl:y.s_dhi bound))
        (prune_reason ~keep:(fun v -> a <= v && v <= b) halls y ~lower)
        (prune_expl ?alo t ~a ~b ~halls ~y ~lower)
    in
    (* The rule above: the pass-start snapshot of [yi], and of any term naming the same
       variable, is taken before the push can land. *)
    twins t yi (fun j -> ignore (snap j));
    (* [deriving_ahead]: a Hall pruning counts several disequality rows, so its trace
       line is RUP only after its derivation (I-X10, D-0040). "Derive ahead" is a
       property of the propagator that made the entry, stamped on [Store.entry]'s [ahead]
       (D-0082, M7-T17); it used to be [Encoding.has_direct] of [x]. *)
    match
      Store.deriving_ahead store (fun () ->
          if lower then Store.set_lo store y.s_var bound j
          else Store.set_hi store y.s_var bound j)
    with
    | Store.Conflict c -> raise (Found c)
    | Store.Changed ->
        Propagator.count_deduction ();
        let d = Store.get store y.s_var in
        twins t yi (fun j ->
            dirty.(j) <- true;
            lo_l.(j) <- Domain.lo d;
            hi_l.(j) <- Domain.hi d);
        moved := true
    | Store.Unchanged -> ()
  in
  for ia = 0 to nt - 1 do
    let a = lo0.(by_lo.(ia)) in
    if ia = 0 || lo0.(by_lo.(ia - 1)) <> a then
      let inside = ref 0 and p = ref 0 in
      for ib = 0 to nt - 1 do
        let b = hi0.(by_hi.(ib)) in
        if ib = nt - 1 || hi0.(by_hi.(ib + 1)) <> b then (
          (* [inside]: the terms whose pass-start window lies in [a, b]. *)
          while !p < nt && hi0.(by_hi.(!p)) <= b do
            if lo0.(by_hi.(!p)) >= a then incr inside;
            incr p
          done;
          let k = b - a + 1 in
          let n = !inside in
          if b >= a && n >= k then (
            (* The contained terms, marked in [inmask]; [idx ()] lists them in
               [t.terms] order, as [contained] listed them, for a push that needs them. *)
            for q = 0 to !p - 1 do
              let i = by_hi.(q) in
              if lo0.(i) >= a then inmask.(i) <- true
            done;
            let idx () = List.filter (fun i -> inmask.(i)) (range 0 (nt - 1)) in
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

               M7-T33 (D-0156) keeps that at the ROOT only. Under a decision [push]
               reports the conflict itself, WITH its facts, under [deriving_ahead]: the
               derivation then goes on the page before `rup ~fact ... >= 1`, which makes
               that line unit propagation against one line rather than the Hall
               argument, and 1UIP learning gets a reason to resolve from. See
               [push_conflict].

               [all_in] is split rather than used whole: the Hall set must be EXACTLY as
               big as the interval for the counting to cancel, so the first [k] are the
               set and the (k+1)th is the variable pushed out of it. Which [k] is
               immaterial to soundness and fixed by [t.terms] order for determinism. *)
            if n > k then
              let idx = idx () in
              let halls = List.map snap (List.filteri (fun i _ -> i < k) idx) in
              let yi = List.nth idx k in
              push ~halls ~a ~b ~y:(snap yi) ~yi ~lower:true (b + 1)
            else (
              (* M16-file-review-T2 (D-0190): a variable is snapshotted, and looked for in
                 the Hall set, only once its LIVE bounds show it can be pushed: [y.s_lo]
                 and [y.s_hi] are those bounds, read again by [snap_of] from the same
                 store, so the same variables are pushed with the same snapshots. Every
                 variable of the scope used to be snapshotted (its holes, two root tests)
                 and compared by name with the Hall set, for every tight interval. *)
              (* D-0235: the Hall set is snapshotted only when a push needs it, and a
                 term is looked for in it before it is snapshotted, through [inset] over
                 [canon] -- the same test as the name comparison it replaces, which was
                 O(n) string comparisons per term of every tight interval. *)
              for i = 0 to nt - 1 do
                if inmask.(i) then inset.(t.canon.(i)) <- true
              done;
              (* Every push from this interval sums the same Hall set's at-least-one
                 lines, from the same pass-start snapshots ([alo_lines], D-0242). *)
              let alo = memo () in
              for yi = 0 to nt - 1 do
                let lo = lo_l.(yi) and hi = hi_l.(yi) in
                if (a <= lo && lo <= b) || (a <= hi && hi <= b) then
                  if not inset.(t.canon.(yi)) then
                    let y = live yi in
                    let halls = List.map snap (idx ()) in
                    if a <= y.s_lo && y.s_lo <= b then
                      push ~alo ~halls ~a ~b ~y ~yi ~lower:true (b + 1)
                    else if a <= y.s_hi && y.s_hi <= b then
                      push ~alo ~halls ~a ~b ~y ~yi ~lower:false (a - 1)
              done;
              for i = 0 to nt - 1 do
                if inmask.(i) then inset.(t.canon.(i)) <- false
              done);
            Array.fill inmask 0 nt false))
      done
  done;
  !moved

(* THE QUIET-BOUNDS SKIP (M20-pernode-T4, D-0235). Whether [pass_scan] moves anything or
   raises is a function of the scope's BOUNDS alone: every interval, every containment,
   every push and every emptying test reads [lo]/[hi] and nothing else (holes enter only
   the reasons and derivations of a push that lands). So a bound vector on which a scan
   once moved nothing is QUIET for good, and a pass that starts on it is skipped. The
   vector is not a fact about the store and needs no trail: after a backtrack, a restart
   or a descent the test compares the live bounds with it and runs the scan whenever
   they differ. Most wake-ups of a domain-consistent alldiff are interior holes, which
   leave the bounds where the last call's final pass found them quiet. [count_pass] is
   counted as before, so the [snaps] counter the lanes compare is unchanged.
   BAGUETTE_DEBUG runs the scan behind every skip and requires it to move nothing. *)
(* How many passes [pass] skipped, for test_prop's lane; not read by the solver. *)
let quiet_skips = ref 0

(* THE HALL-FREE TEST (M20-pernode-T4, D-0242). Whether [pass_scan] on the bound vector
   [lo]/[hi] would move nothing and raise nothing, decided by counting alone, with no
   snapshot, no allocation and no push. [by_lo]/[by_hi] must be sorted by [lo]/[hi].

   THE RULE. A scan acts on a candidate interval [a, b] (a a lower bound, b an upper bound,
   a <= b) holding n terms of k = b - a + 1 values exactly when
     - n > k: it pushes a contained term out, which empties it (a conflict), or
     - n = k and some term NOT contained has a bound in [a, b]: it pushes that bound past
       the interval, which always changes it (a lower bound in [a, b] goes to b + 1 > lo).
   Nothing else in a scan pushes, and with no push the live bounds are the pass-start
   ones, so the scan moves nothing iff no candidate interval is one of the two. The
   second case is counted rather than searched: a contained term has both bounds in
   [a, b], so "some term outside has its lower bound in [a, b]" is "more than n = k lower
   bounds lie in [a, b]", and the same for the upper bounds. A variable repeated in the
   scope ([twins]) has one bound pair for all its terms, so its terms are contained
   together and the scan's name test ([inset]) skips exactly the contained terms: the
   count is the scan's test there too.

   THE WALK is the scan's own: each distinct lower bound [a] ascending, the terms in
   [by_hi] order counting those with [lo >= a], an interval closing at each distinct
   upper bound. It stops for [a] as soon as k exceeds the number of terms with
   [lo >= a], which no later [b] can fill. BAGUETTE_DEBUG runs the scan behind every
   [true] and requires it to move nothing; test_prop's lane (h) checks the converse
   (every [false] is a scan that moves or raises) on random vectors. *)
let hall_free ~by_lo ~by_hi lo hi =
  let n = Array.length by_lo in
  let free = ref true and ia = ref 0 and hlo = ref 0 in
  while !free && !ia < n do
    let a = lo.(by_lo.(!ia)) in
    if !ia > 0 && lo.(by_lo.(!ia - 1)) = a then incr ia
    else (
      (* [hlo]: the terms whose upper bound is below [a]; none is contained in an interval
         from [a], and none has a bound in it. Monotone in [a]. *)
      while !hlo < n && hi.(by_hi.(!hlo)) < a do
        incr hlo
      done;
      let rem = n - !ia in
      let inside = ref 0 and pl = ref !ia and p = ref !hlo in
      while !p < n do
        let i = by_hi.(!p) in
        if lo.(i) >= a then incr inside;
        let b = hi.(i) in
        if !p + 1 < n && hi.(by_hi.(!p + 1)) = b then incr p
        else
          let k = b - a + 1 in
          if k > rem then p := n
          else (
            if !inside > k then (
              free := false;
              p := n)
            else if !inside = k then (
              while !pl < n && lo.(by_lo.(!pl)) <= b do
                incr pl
              done;
              if !pl - !ia > k || !p + 1 - !hlo > k then (
                free := false;
                p := n));
            incr p)
      done;
      incr ia)
  done;
  !free

(* How many passes [hall_free] answered without a scan, for test_prop's lanes. *)
let hall_free_skips = ref 0

let pass t store =
  Propagator.count_pass ();
  let nt = Array.length t.terms in
  let lo0 = t.lo0 and hi0 = t.hi0 in
  for i = 0 to nt - 1 do
    let d = Store.get store t.terms.(i).x in
    lo0.(i) <- Domain.lo d;
    hi0.(i) <- Domain.hi d
  done;
  let q = t.quiet in
  let quiet = ref (t.quiet_on && q.q_valid) in
  let i = ref 0 in
  while !quiet && !i < nt do
    if lo0.(!i) <> q.q_lo.(!i) || hi0.(!i) <> q.q_hi.(!i) then quiet := false;
    incr i
  done;
  if !quiet then (
    incr quiet_skips;
    Debug.check "I-P2 (D-0235): stage 1 skipped a pass on quiet bounds" (fun () ->
        match pass_scan t store ~lo0 ~hi0 with
        | moved -> not moved
        | exception Found _ -> false);
    false)
  else (
    sort_by lo0 t.by_lo;
    sort_by hi0 t.by_hi;
    let moved =
      if t.quiet_on && hall_free ~by_lo:t.by_lo ~by_hi:t.by_hi lo0 hi0 then (
        incr hall_free_skips;
        Debug.check "I-P2 (D-0242): stage 1 found the bounds Hall-free" (fun () ->
            match pass_scan t store ~lo0 ~hi0 with
            | moved -> not moved
            | exception Found _ -> false);
        false)
      else pass_scan t store ~lo0 ~hi0
    in
    if not moved then (
      Array.blit lo0 0 q.q_lo 0 nt;
      Array.blit hi0 0 q.q_hi 0 nt;
      q.q_valid <- true);
    moved)

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
   `rup` conflict line claims the counting argument as reverse unit propagation. That is
   the root's arrangement; under a decision the conflict is reported with A's facts and
   its derivation written ahead of its line (M7-T33, D-0156, [push_conflict]).

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

(* M7-T22 / D-0086 (b). An INTERIOR Regin removal states `y <> v` the way every other
   hole in the store is stated -- over the ORDER encoding, `~y_ge_v \/ y_ge_(v+1)`, the
   clause its own trace line claims -- and not in this module's working currency
   [~y_eq_v]. The forward channelling line [y_eq_v \/ ~y_ge_v \/ y_ge_(v+1)] converts one
   into the other exactly: added to [~y_eq_v >= 1 (+ leftovers)], the [y_eq_v] terms pair
   off and the degree drops by the one unit they carried, divisor 1.

   The trail entry's explanation is a CONTRACT with whoever embeds it, and the embedder
   that reads it is element.ml's [excl_hole]: when an element RESULT sits in this scope,
   that instance excludes a position by citing the result hole's remover and pairing it
   off against its own two ORDER-literal rows. Handed [~y_eq_v], nothing cancelled and a
   root conflict did not close (bench/fuzz ad 24319, ad 25012;
   test/models/alldiff_regin_hole_element_unsat.fzn). The convention lives HERE, not as a
   bridge in [excl_hole], for the reason element.ml's own [in_order_currency] gives: one
   currency for every hole means an embedder never has to know which propagator punched
   it. This module's own derivations never read this entry's explanation -- [holes_of]
   cites a hole by its level ([Gone_hole_root]) or its facts ([Gone_hole]) -- so they are
   untouched. A removal AT a bound is a bound move, which no one embeds, and keeps its
   form, exactly as in element.ml. *)
let in_order_currency t y value expl =
  match Encoding.direct_fwd_id t.enc y.s_name value with
  | None -> expl
  | Some fwd -> Explanation.combine [ Explanation.term 1 expl; cite fwd ] 1

(* One removal, with both halves of D-0026 built from the same snapshot, returning
   through [Found] exactly as [pass]'s [push] does and recording a landed removal in
   [moved], and answering whether it landed. [y] and [d] are LIVE here, not the pass's
   snapshot: I-P6 allows stale premises, but the SHAPE of the entry -- a hole clause for
   an interior value, the bound landed on for a value at the bound ([removal_conclusion])
   -- must be decided against the domain the store is about to change. [y] comes from
   [regin_scratch]'s cache, which is the live snapshot by its invalidation rule, and
   [facts] is the tight set's [hall_facts], shared by every removal under that set
   (D-0235); the caller hands over only a value still in [y]'s live domain, so every
   call reaches the store. *)
let remove_one t store ~moved ~halls ~vals ~keep ~facts ~alo ~y ~y_tm value =
  let d = Store.get store y_tm.x in
  let concludes = removal_conclusion y d value in
  let expl = remove_expl ~alo t ~keep ~vals ~halls ~y ~value in
  let j =
    Reason.because ~concludes
      (remove_reason_of y (Lazy.force facts))
      (if Option.is_none concludes then in_order_currency t y value expl else expl)
  in
  (* A Regin hole counts too: [deriving_ahead], as for a Hall bound move. *)
  match Store.deriving_ahead store (fun () -> Store.remove store y_tm.x value j) with
  | Store.Conflict c -> raise (Found c)
  | Store.Changed ->
      Propagator.count_deduction ();
      moved := true;
      true
  | Store.Unchanged -> false

(* One Regin pass FROM SCRATCH: the matching rebuilt, every tight set enumerated. Its
   output -- which removals land, in which order, with which [halls] and [vals] -- is the
   contract D-0215 keeps byte for byte, and [regin_pass] runs it whenever [cannot_prune]
   does not rule it out. Returns whether a removal landed. ONE SNAPSHOT, EVERY DEDUCTION (I-P6,
   M6-T19): [doms], the matching and the components are computed once and every removal
   they justify is applied. The argument is [pass]'s, in this module's second currency:
   a removal only ever takes a value OUTSIDE its tight set, so no matching edge and no
   set membership is ever removed by this pass, and a set that is tight over the stale
   domains is tight over the live ones, which are subsets of them. *)
let regin_scratch t store =
  let n = Array.length t.terms in
  let moved = ref false in
  if n > 0 then (
    let doms = Array.map (fun tm -> Store.get store tm.x) t.terms in
    (* Every value some domain holds, ascending: a mark per value of the scope's live
       span, then the marked values in order (D-0242; the same array the sorted union of
       the domains' lists gives, without the lists). The lists stay for a span too wide
       to mark, the gate's bound. *)
    let vlo = Array.fold_left (fun a d -> Int.min a (Domain.lo d)) max_int doms in
    let vhi = Array.fold_left (fun a d -> Int.max a (Domain.hi d)) min_int doms in
    let values =
      if vhi - vlo + 1 > max_gate_span then
        Array.of_list
          (List.sort_uniq Int.compare
             (List.concat_map Domain.to_list (Array.to_list doms)))
      else
        let mark = Array.make (vhi - vlo + 1) false in
        Array.iter (fun d -> Domain.iter (fun v -> mark.(v - vlo) <- true) d) doms;
        let count = Array.fold_left (fun c b -> if b then c + 1 else c) 0 mark in
        let values = Array.make count 0 and k = ref 0 in
        Array.iteri
          (fun i b ->
            if b then (
              values.(!k) <- vlo + i;
              incr k))
          mark;
        values
    in
    let nv = Array.length values in
    let holds i vi = Domain.mem doms.(i) values.(vi) in
    (* [mval.(i)] is the index of the value matched to variable [i], [mvar.(vi)] the
       variable matched to value [vi]; [-1] is unmatched on both sides. *)
    let mval = Array.make n (-1) and mvar = Array.make (Int.max 1 nv) (-1) in
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
        let seen = Array.make (Int.max 1 nv) false in
        if not (augment i seen) then failed := Some (i, seen)
    done;
    (* THE SNAPSHOT CACHE (M20-pernode-T4, D-0235). [snap i] is [snap_of store
       t.terms.(i)] as the store stands NOW, and it is kept until a removal lands on
       [i]: a snapshot reads [i]'s domain, its two supports and the remover of each of
       its holes, and within this pass only a removal ON [i] changes any of them (the
       remover of a hole that exists is the entry that made it, however long the trail
       has grown since). Until D-0235 every tight set snapshotted every member again, and
       every removal snapshotted its [y], with a [Store.remover] search per hole each
       time: 16 % of elitserien handball12's instructions. *)
    let cache = Array.make n None in
    let snap i =
      match cache.(i) with
      | Some s -> s
      | None ->
          let s = snap_of store t.terms.(i) in
          cache.(i) <- Some s;
          s
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
          snap x0
          :: List.filter_map
               (fun vi -> if seen.(vi) then Some (snap mvar.(vi)) else None)
               (range 0 (nv - 1))
        in
        let x0_tm = t.terms.(x0) in
        (* M7-T33 (D-0156): under a decision, the conflict with A's facts -- both bounds
           of every member and the remover's facts of every hole the derivation cancels
           ([hall_facts] over B) -- derived ahead ([push_conflict]). At the root, the
           factless emptying push below, unchanged. *)
        if Store.level store > 0 then
          raise
            (Found
               (push_conflict store
                  ~facts:(hall_facts ~keep:(mem_of vals) halls)
                  (conflict_expl t ~vals ~halls)));
        let j =
          Reason.because ~concludes:None Reason.none (conflict_expl t ~vals ~halls)
        in
        (* Must fail: the bound is one past the variable's own upper bound. *)
        match Store.set_lo store x0_tm.x (Domain.hi doms.(x0) + 1) j with
        | Store.Conflict c -> raise (Found c)
        | Store.Changed | Store.Unchanged ->
            invalid_arg
              "Alldiff.regin_scratch: the emptying push did not fail, so the pigeonhole \
               derivation would be attached to a change that landed")
    | None ->
        (* [has_free.(i)]: [i]'s domain holds a value the matching leaves free. A function
           of the matching and [doms] alone, so computed once per pass rather than once
           per member of every set [ink] (D-0235: it allocated a list of every value per
           member per set). *)
        let has_free =
          Array.init n (fun i ->
              let rec any vi =
                vi < nv && ((mvar.(vi) = -1 && holds i vi) || any (vi + 1))
              in
              any 0)
        in
        (* [holders.(vi)]: how many terms hold [values.(vi)]; [held.(i)]: how many
           values term [i] holds. Read once per pass, for the outsider count below. *)
        let holders = Array.make nv 0 and held = Array.make n 0 in
        for i = 0 to n - 1 do
          for vi = 0 to nv - 1 do
            if holds i vi then (
              holders.(vi) <- holders.(vi) + 1;
              held.(i) <- held.(i) + 1)
          done
        done;
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
              let rec any i = i < n && ((ink.(i) && has_free.(i)) || any (i + 1)) in
              any 0
            in
            (* WHETHER ANY TERM OUTSIDE THE SET HOLDS ONE OF ITS VALUES (D-0242). A tight
               set's members hold only its values (every value they hold is matched, to
               a member, by the closure above), so the terms outside hold
               [sum holders over its values - sum held over its members] of them, counted
               over [doms]. When that is 0 the removal loop below tests [doms.(y)] first
               for every pair and calls nothing: skipping it, and the value list, the
               membership table and the lazy facts it would have built, changes nothing
               but the instructions. *)
            let outsiders =
              let c = ref 0 in
              for i = 0 to n - 1 do
                if ink.(i) then c := !c + holders.(mval.(i)) - held.(i)
              done;
              !c
            in
            if (not free_reachable) && outsiders > 0 then
              let vals =
                List.sort_uniq Int.compare
                  (List.filter_map
                     (fun i -> if ink.(i) then Some values.(mval.(i)) else None)
                     (range 0 (n - 1)))
              in
              (* Built at the first removal that lands, from the cache: see the
                 comment above [snap]. *)
              let halls =
                lazy
                  (List.filter_map
                     (fun i -> if ink.(i) then Some (snap i) else None)
                     (range 0 (n - 1)))
              in
              let keep = mem_of vals in
              let facts = lazy (hall_facts ~keep (Lazy.force halls)) in
              let alo = memo () in
              List.iter
                (fun y ->
                  if not ink.(y) then
                    List.iter
                      (fun v ->
                        if
                          Domain.mem doms.(y) v
                          && Domain.mem (Store.get store t.terms.(y).x) v
                        then
                          if
                            remove_one t store ~moved ~halls:(Lazy.force halls) ~vals
                              ~keep ~facts ~alo ~y:(snap y) ~y_tm:t.terms.(y) v
                          then twins t y (fun j -> cache.(j) <- None))
                      vals)
                (range 0 (n - 1))
            else if not free_reachable then
              Debug.check "I-P2 (D-0242): a tight Regin set no outside term meets"
                (fun () ->
                  List.for_all
                    (fun y ->
                      ink.(y)
                      || List.for_all
                           (fun i -> not (ink.(i) && holds y mval.(i)))
                           (range 0 (n - 1)))
                    (range 0 (n - 1))))
          (range 0 (n - 1)));
  !moved

(* ------------------------------------------------------ THE REGIN GATE (D-0215) *)

(* [regin_scratch] removes a value [v] from [y] exactly when the edge (y, v) lies in NO
   maximum matching (completeness: its [ink] enumeration finds the least tight set
   holding [v]'s partner, which excludes [y]), and a pass that removes nothing has no
   effect at all: it pushes nothing, and what it reads ([snap_of]) is read only. So when
   every edge lies in SOME maximum matching the pass is a no-op, and [cannot_prune] says
   so in O(n + sum of domain sizes), against the O(n^2 d) of the scratch pass:

   1. REPAIR the matching kept from the last call. An edge whose value has left its
      variable's domain is dropped; every variable left unmatched is re-augmented (Kuhn,
      a free value first). If one cannot be, NO matching saturates the scope -- a
      partial matching with no augmenting path from [i] is the Berge argument -- and the
      answer is "may prune": the scratch pass rebuilds its own matching and reports the
      pigeonhole with the very [seen] set it always did.
   2. TARJAN over the variables, [i -> j] when [i] holds [j]'s matched value, plus a
      sink for "holds a free value". Régin's characterisation: an edge (y, v) outside
      the matching is in some maximum matching iff v is free, or v's partner [j] and [y]
      share a strongly connected component (an even alternating cycle), or [j] reaches a
      free value (an even alternating path). So the one unusable edge is an edge INTO an
      already closed component that reaches no free value, and the search stops at the
      first one ([Prunable]).

   The answer is EXACT both ways: "cannot prune" holds iff the scratch pass would land
   nothing. Only "cannot prune" skips anything, and the scratch pass is what runs
   otherwise, so the gate can change the speed and nothing else: the matching it keeps
   is never handed to the scratch pass, whose output is a function of the domains alone.

   WHY NO TRAIL (the question every cross-pass state must answer). The kept matching is
   not a fact about the store. Step 1 re-reads every matched edge against the live
   domain, so a matching that a backtrack, a restart, or a different store has made
   stale costs a repair and never an answer: after a backtrack the domains are WIDER
   (I-T1: a backtrack restores every domain exactly), every kept edge still exists and the
   matching is still valid, and after a descent the edges that left are the ones step 1
   drops. The invariant that covers the answer is I-P2 through the BAGUETTE_DEBUG check in
   [regin_pass]: whenever the gate says "cannot prune", the scratch pass runs as well and
   must land nothing. *)

exception Prunable

let assign g i v =
  g.g_val.(i) <- v;
  g.g_owner.(v - g.g_base) <- i

(* Kuhn's augmenting search from term [i], visited marks against [g_stamp]: a free value
   of [i]'s domain if there is one, else a value whose partner can move. *)
let rec augment g i =
  let d = g.g_doms.(i) in
  let hi = Domain.hi d in
  let rec free v =
    v <= hi
    && (Domain.mem d v
        && g.g_owner.(v - g.g_base) < 0
        &&
        (assign g i v;
         true)
       || free (v + 1))
  in
  let rec deep v =
    v <= hi
    &&
    let k = v - g.g_base in
    Domain.mem d v
    && g.g_seen.(k) <> g.g_stamp
    && (g.g_seen.(k) <- g.g_stamp;
        augment g g.g_owner.(k))
    &&
    (assign g i v;
     true)
    || deep (v + 1)
  in
  free (Domain.lo d) || deep (Domain.lo d)

(* Tarjan from term [i]; raises [Prunable] at the first edge into a closed component
   that reaches no free value. A closed [j] is never in [i]'s component: had [j] reached
   [i], Tarjan would not have closed [j] before [i]. *)
let rec visit g counter i =
  g.g_index.(i) <- !counter;
  g.g_low.(i) <- !counter;
  incr counter;
  g.g_stack.(g.g_sp) <- i;
  g.g_sp <- g.g_sp + 1;
  g.g_onstack.(i) <- true;
  g.g_reach.(i) <- false;
  let d = g.g_doms.(i) and mine = g.g_val.(i) in
  for v = Domain.lo d to Domain.hi d do
    if v <> mine && Domain.mem d v then
      let j = g.g_owner.(v - g.g_base) in
      if j < 0 then g.g_reach.(i) <- true
      else (
        if g.g_index.(j) < 0 then (
          visit g counter j;
          g.g_low.(i) <- Int.min g.g_low.(i) g.g_low.(j))
        else if g.g_onstack.(j) then g.g_low.(i) <- Int.min g.g_low.(i) g.g_index.(j);
        if not g.g_onstack.(j) then
          if g.g_reach.(j) then g.g_reach.(i) <- true else raise Prunable)
  done;
  if g.g_low.(i) = g.g_index.(i) then (
    (* Close [i]'s component: everything above [i] on the stack. It reaches a free value
       if any member does, directly or through a closed component. *)
    let first = ref (g.g_sp - 1) in
    while g.g_stack.(!first) <> i do
      decr first
    done;
    let reach = ref false in
    for p = !first to g.g_sp - 1 do
      if g.g_reach.(g.g_stack.(p)) then reach := true
    done;
    for p = !first to g.g_sp - 1 do
      let m = g.g_stack.(p) in
      g.g_onstack.(m) <- false;
      g.g_reach.(m) <- !reach
    done;
    g.g_sp <- !first)

let cannot_prune g t store =
  let n = Array.length t.terms in
  for i = 0 to n - 1 do
    let d = Store.get store t.terms.(i).x in
    g.g_doms.(i) <- d;
    let v = g.g_val.(i) in
    if v >= g.g_base && not (Domain.mem d v) then (
      g.g_owner.(v - g.g_base) <- -1;
      g.g_val.(i) <- g.g_base - 1)
  done;
  let saturated = ref true in
  for i = 0 to n - 1 do
    if !saturated && g.g_val.(i) < g.g_base then (
      g.g_stamp <- g.g_stamp + 1;
      if not (augment g i) then saturated := false)
  done;
  !saturated
  &&
  (Array.fill g.g_index 0 n (-1);
   Array.fill g.g_onstack 0 n false;
   g.g_sp <- 0;
   let counter = ref 0 in
   match
     for i = 0 to n - 1 do
       if g.g_index.(i) < 0 then visit g counter i
     done
   with
   | () -> true
   | exception Prunable -> false)

(* One Regin pass: the gate, and the scratch pass behind it. [count_pass] is counted here
   once per pass as before, so every counter the lanes compare is unchanged. *)
let regin_pass t store =
  if Array.length t.terms = 0 then false
  else (
    Propagator.count_pass ();
    match t.gate with
    | Some g when cannot_prune g t store ->
        Debug.check "I-P2 (D-0215): the Regin gate said a pass cannot prune" (fun () ->
            match regin_scratch t store with
            | moved -> not moved
            | exception Found _ -> false);
        false
    | Some _ | None -> regin_scratch t store)

(* Stage 1, unchanged: Hall intervals over bounds. Returns whether it moved anything, so
   [propagate] can decide whether to go on to stage 2. *)
let rec stage_bounds t store ~moved =
  if pass t store then stage_bounds t store ~moved:true else moved

let rec stage_regin t store = if regin_pass t store then stage_regin t store

(* THE STAGING, and it is a measurement of GCS's rather than a choice of ours
   (docs/GCS-COMPARISON.md section 3, docs/ROADMAP.md M4-T2): above 256 var-value pairs
   the cheap pass returns WITHOUT an idempotence claim, so the propagators that are
   cheaper than a matching get to react to what it inferred before the matching work is
   paid for; at or below the cutoff both stages run in one call, because the staging
   itself costs a wake-up that a small instance does not earn back.

   "Without an idempotence claim" is about this CALL and not about I-P2, idempotence at
   the interface. The instance
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
