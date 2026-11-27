(* The backtrackable domain store: the current domain of every variable, the TRAIL of
   every change made to them, and the decision-level marks into that trail.

   The mutators. A propagator changes a domain only through [set_lo], [set_hi], [remove]
   and [fix], and each takes ONE [Reason.justified]: the facts the pruning read (its
   reason), the derivation that convinces the checker (its justification) and the bound
   it concludes. All four go through [apply], which pushes a trail [entry] recording the
   old and new domain, those three halves, and the propagator instance that made the
   change (stamped from the slot the engine sets around each run, so no mutator takes an
   id; see [with_running]). Every change therefore carries its explanation (I-P4).

   Backtracking. A level mark records where the trail and the explanation arena stood
   when the level opened; [backtrack] pops entries back to it, writing each entry's [old]
   domain back. Three trail invariants (docs/INVARIANTS.md) hold:
     I-T1  [backtrack_to l] restores every domain to exactly its state when level [l]
           was opened;
     I-T2  trail entries are ordered by level, so the level marks are monotone;
     I-T3  every live entry's explanation index resolves in the arena (no orphan
           reasons), because the mark rewinds the arena with the trail.

   Restoring is an array write plus [Domain.undo]. A [Domain.t]'s holes are a version of
   a per-variable log its successors share (the hole log of lib/core/domain.ml, D-0222),
   so the trail holds a removed value (16 bytes in the log) where it used to hold a copy
   of the bitset per pruning (98 % of wordpress's heap at its refusal, D-0218's memory
   census). [Domain.undo] truncates the log back to the version the popped entry
   restores. Every domain an entry, a history or a frame holds stays readable while that
   entry is on the trail; a domain from an undone branch raises [Domain.Stale_version].

   Who established a bound. [lo_sup]/[hi_sup] name, per variable, the trail position of
   the entry behind its current lower/upper bound, in O(1) (see [lo_support]), and the
   bound HISTORIES ([lo_hist], [hi_hist], [all_hist]) keep the whole chain of such
   entries, so "which entry established [x >= v]?" and "which entry removed value [v]?"
   are binary searches rather than trail scans ([bound_support], [remover]). A
   [history] is the trail cut at a position, which a reason built after the push reads
   as if it had been read at the push.

   Costs kept off the per-entry path (the core file review, M16-file-review-T1, D-0186):
   a [Debug.check] on a path taken per trail entry ([apply], [push_entry],
   [check_agreement], [remover]) sits under [if Debug.enabled], because its predicate is
   a closure over the entry's values, and a closure with free variables is allocated at
   every call whether or not anything checks it: three per entry, about as many words as
   the entry itself. The bound walks of [hi_below] and [lo_at_least] are walks of the
   newest moves then binary searches over the bound histories, and [created_domain]
   reads an array of the created domains (see each). A walk over a [Combine]'s summands
   ([drop_page_only_lemmas]) runs in constant stack, since a summand list is as long as
   the ladders it crosses (D-0197, the stack overflow a 32-million-term row caused).

   Name lookup. [var_named] answers through a DIRECT-MAPPED memo of the name index's
   answers, a hit being a cell whose variable's name is PHYSICALLY the name asked
   (M20-pernode-T4, D-0245). Sound because the cell's answer came from the index for an
   equal name; the cell a name lands in decides only where an answer is kept (see
   [var_index_named]). *)

module Lit = Baguette_proof.Lit
module Name_tbl = Baguette_proof.Name_tbl

(* The propagator instance that made a change, as the [id] of [Propagator.instance]
   (lib/core/propagator.ml) -- the id that already existed and that [Engine] already
   indexes its watcher lists and trigger masks by. [no_prop] is "no propagator":
   [Search]'s decision pushes, and a direct mutation from a test, are attributed to
   nobody, and that is the right answer for both. See [with_running]. *)
let no_prop = -1

(* "No trail entry supports this bound": it is still the bound the variable was created
   with. Not a valid trail position, so [lo_support]'s caller cannot accidentally index
   with it. *)
let no_support = -1

(* A level mark records where in the trail the level began, and where in the explanation
   arena it began: backtracking rewinds both together, which is what keeps I-T3 true
   (no trail entry survives whose reason has been dropped) and stops the arena growing
   without bound over a long search. *)
type mark = { trail_mark : int; reason_mark : int }

(* One recorded domain change. [apply] is its only constructor and builds a fresh record
   for every push. Twelve fields: [var], [old] and [why] serve undo and conflict
   analysis; the other nine exist for the proof and for conflict analysis, and [cites],
   a memo, is the only mutable one. docs/ARCHITECTURE.md section 3 lists them too.

   [old] is what the domain was, so backtracking is a single array write (I-T1).

   [now] is what the change PRODUCED. The trace line a pruning contributes to the proof
   claims the order literal the pruning established, and that literal is a function of
   the new bound, which nothing else on the trail records (D-0018: a branch's nogood is
   RUP over the branch's own logged trace, so every pruning writes such a line;
   lib/core/trace.ml writes them). It costs one word and no work: [Domain.t] reads as it
   was while the entry is on the trail (D-0222), and [apply] already holds the value it
   is about to store.

   [why] is the explanation's index in the arena (I-T3 is a bounds test on it). It is
   the JUSTIFICATION, the derivation the checker is shown.

   [reason] is the other half of the trace line: the bound facts the propagator actually
   read, negated into the line's tail. It is deliberately NOT [Explanation.lits] of
   [why], which returns the declared-width [Weaken] chain that the [pol] of a bounds
   justification needs (D-0013: weaken, divide, add); the two are different projections
   of the same pruning (lib/core/reason.ml's header says which, and
   lib/core/explanation.ml's [owners] says what they share). A [Reason.t] is declarative
   data, not a closure (D-0026: reasons are data, justifications are cutting planes),
   and three things follow:

     - A pruning allocates no closure and captures no environment. What a closure used
       to capture (a snapshot list, a propagator's term record) is what D-0026 quotes
       GCS measuring at ~20% of runtime.
     - The literals are built late, once, and only for the prunings a failing branch
       actually writes down ([Reason.lits]; ARCHITECTURE, "Deferred explanations"),
       where the old thunks were cheap only because their [Lit.t]s had been allocated
       eagerly at every call site ([Linear.snapshot_source] built [Lit.ge name cur] per
       term per pruning whether or not anyone ever asked).
     - It cannot read live store state, because it is not code, so the I-X6 obligation
       (an explanation reads a snapshot, never live domains) is discharged by the type on
       this half. A propagator that supplies no facts writes [Reason.none] and cannot do
       so by omission.
   History: the field was a [unit -> Lit.t list] thunk until M2-T8.

   [concludes] is the third half (D-0043): WHAT the pruning derived, where [reason] is
   what it read and [why] how the checker is convinced. It is kept on the trail for the
   reason [now] is: a caller walking the trail later has no other way to recover it (the
   proof-line index of M2-T9 keys a line by its claim, and a [pol] line's content is
   otherwise unknown to us), and recomputing it would mean re-running the propagator.
   [apply] checks it against the change before pushing, so an entry's conclusion and its
   [old]/[now] cannot disagree.

   [prop] is the id of the propagator instance that made this change ([no_prop] for a
   decision). Conflict analysis (1UIP learning, M2-T3) walks the trail and asks, of an
   entry it did not watch happen, which constraint implied it; this field answers that
   without [Explanation] having to carry the row. It is stamped by [apply] from
   [t.current_prop], which the ENGINE sets around each [run], and never passed in by the
   propagator, so a propagator has nothing to get wrong. [Engine.check_attribution] reads
   the stamp back, on by default, and rejects an entry that does not name the instance
   that just ran or that credits an instance which does not watch the variable it
   changed; an id threaded and never read would change no behaviour and pass every test.
   History: added by M2-T7. Until then the trail held only [{ var; old; why }], and
   D-0011 (one propagator instance per model row) recorded that a caller walking it could
   not tell which half of an [int_lin_eq] instance, its [le] row or its [ge] row,
   produced a pruning.

   [sup_lo]/[sup_hi] are the trail positions that supported [var]'s lower and upper bound
   BEFORE this entry, or [no_support]. They make "which earlier derivation established
   this bound?" an O(1) question (see [lo_support] below), and they live here rather than
   in a side structure because backtracking has to restore them and [undo_to] already
   visits exactly this record. Two immediate ints, no allocation. *)
type entry = {
  var : Var.t;
  old : Domain.t;
  now : Domain.t;
  why : Explanation.Arena.id;
  reason : Reason.t;
  concludes : Reason.fact option;
  prop : int;
  ahead : bool;
      (* "This pruning's derivation must be written on the page AHEAD of its trace
         line." It is a property of the PROPAGATOR that made the pruning, not of the
         encoding of the variable it moved (D-0082, M7-T17). lib/core/trace.ml's
         [derive_ahead] reads it and nothing else does. Stamped by [apply] from
         [current_ahead], which only [deriving_ahead] sets, and only a
         [Needs_derivation] propagator calls that, around its own pruning call: one whose
         pruning follows from several model constraints at once, so that its trace line
         is RUP only once the derivation is on the page (I-X10: every trace line is RUP
         against the .opb plus the lines already written; test/unit/test_trace.ml's table
         classifies every family). *)
  sup_lo : int;
  sup_hi : int;
  pos : int;
      (* The trail position this entry was pushed at, [-1] for [dummy_entry]. [apply] is
         the only constructor and pushes the record it builds at exactly this position,
         and no entry is ever re-pushed, so an entry occupies one trail position for its
         whole life. lib/core/trace.ml's [position_of] reads it to answer in O(1) what it
         used to answer by walking its list of written entries (M6-T15, D-0090). *)
  mutable cites : int array option;
      (* lib/core/analysis.ml's memo of what this entry's reason CITES, as the trail
         positions that established the facts it read (packed with their level and
         direction by [Analysis]; [Store] never reads the contents). [None] until the
         decision closure (the walk of [Analysis.decision_closure] down to the decisions a
         fact rests on) first reaches the entry; filled once and read at every later
         conflict instead of materialising the reason again. It lives on the entry and not
         in a side table because its validity is exactly the entry's life: the trail below
         a live entry is frozen (I-T1, and the argument for [history] below), so what the
         entry cites, at which level and whether it is a decision cannot change while the
         entry is on the trail, and [apply] builds a fresh record for every push, so
         nothing has to invalidate it when the entry is popped. The memo is O(cited facts
         above level 0) per entry, filled only for entries a conflict analysis reaches.
         History: M7-T27 (a3), the second addendum of D-0124, which builds a Linear
         pruning's reason later from the trail's history instead of snapshotting it at the
         push. *)
}

(* [lo_sup]/[hi_sup] are indexed by variable and hold the trail position of the entry
   that established that variable's current lower/upper bound, or [no_support] while it
   is still the declared one. Maintained by [apply] in O(1) and restored by [undo_to]
   from the entry's own [sup_lo]/[sup_hi].

   They delete a scan; they are not a cache. The answer to "what established this
   bound?" is a single trail position that [apply] already knows when it pushes the
   entry, so it is recorded instead of recomputed. The equivalence argument, which is the
   part worth checking, is at "what holds a bound up" below: the scan and the array agree
   only because bounds are monotone within a level (I-D3) and the array is restored on
   backtrack. History: M2-T8 (D-0026) added them. [Linear] used to answer the question
   once per term per pruning by walking the trail down from the newest entry, O(|trail|)
   per term and O(n * |trail|) per pruning, the most expensive thing left in [lib/] once
   M1-T24 had replaced the same kind of walk in [Engine.propagate] by a trail cursor. *)
type t = {
  domains : Domain.t array;
  initial : Domain.t array;
      (* The domains the store was created with, read by [created_domain]
         (M16-file-review-T1, D-0186). A copy of the array, sharing the records; a
         created domain is the oldest version of its hole log, which no undo truncates
         (D-0222). *)
  names : string array;
  (* The name -> variable index behind [var_named] and [name_rep], built on first use
     rather than in [create], because [Engine.oracle_accepts] builds a scratch store per
     tuple and never asks for a name. Names are fixed at creation ([names] is a private
     copy nothing writes), so the index never goes stale. Added by M6-T11 (D-0085, a pass
     of constant-factor savings on conflict analysis, every artefact byte-identical). *)
  by_name : (int Name_tbl.t * int array) Lazy.t;
  (* A DIRECT-MAPPED memo in front of [by_name]: [memo_size] cells, cell [memo_slot name]
     holding a variable the index answered for a name of that slot, or [-1]; tested by
     PHYSICAL equality against [names] (see [var_index_named]). Ints, so that writing one
     is a plain store and not a [caml_modify], the write barrier a pointer field pays (a
     string field cost more on a miss than the hits saved, D-0236). Allocated on the
     first lookup, [[||]] until then, for the reason [by_name] is lazy. M20-pernode-T4:
     D-0245, generalising D-0236's one-entry memo. *)
  mutable named_memo : int array;
  reasons : Explanation.Arena.t;
  lo_sup : int array;
  hi_sup : int array;
  (* The bound HISTORIES. [lo_hist.(i)] holds, in increasing order, the trail positions
     of the live entries that RAISED variable [i]'s lower bound, the first [lo_hn.(i)]
     cells of it; [hi_hist]/[hi_hn] likewise for the entries that LOWERED its upper bound.
     Pushed by [apply] exactly when [lo_sup]/[hi_sup] is written, popped by [undo_to]
     exactly when it is restored, so the top of a history IS the array's answer and the
     history is the rest of the chain. One int per bound move, in total; a variable's
     array is allocated on its first move. See [bound_support]. They replaced the trail
     scans behind the support and remover queries (M6-T14, D-0088). *)
  lo_hist : int array array;
  lo_hn : int array;
  hi_hist : int array array;
  hi_hn : int array;
  (* The same for EVERY live entry on the variable, bound move or hole, behind
     [remover]. One more int per trail entry. *)
  all_hist : int array array;
  all_hn : int array;
  (* The [name_rep] classes with more than one member, or [None] when names are unique
     (every store [Compile] builds). Lazy for the same reason [by_name] is. *)
  classes : int list array option Lazy.t;
  mutable trail : entry array;
  mutable trail_len : int;
  mutable marks : mark array;
  mutable n_levels : int;
  mutable starts : int array;
  (* Trail position -> how many OPEN level marks sit there (an empty level can share its
     position with the next). Kept by [push_mark] and [backtrack], the only two places
     [n_levels] moves, so [is_level_start] is one load instead of a binary search over
     the marks. From the complexity pass M11-complexity-T3 (D-0142), the store half of
     item S3 of D-0140's inventory of costs that grow with the run. *)
  (* The propagator instance currently running, or [no_prop]. Written only by [run_as]
     (behind [with_running]), and read by [apply] and the two conflict builders to stamp
     what they build. It is written and restored by the same wrapper in the same call.
     History: before M2-T7 a one-shot slot here carried a conflict's facts from the
     propagator to the trace, to be consumed exactly once and cleared in three places
     (a [take_conflict_facts] function since deleted, [new_level], [backtrack]); the
     facts now travel in the [conflict] value itself ([c_reason]). *)
  mutable current_prop : int;
  (* True only inside [deriving_ahead]; [apply] copies it into [entry.ahead] and the
     conflict builders into [c_ahead]. Written and restored by the same wrapper in the
     same call, like [current_prop]. *)
  mutable current_ahead : bool;
  (* The trail's LOW-WATER MARKS, one per registered reader: reader [r]'s slot is the
     smallest [trail_len] reached since [r] last called [take_low_water]. Maintained by
     [undo_to], the only place the trail shrinks, and reset to the current length on read.
     [Engine.propagate] reads it to find how far a backtrack reached since it last looked:
     the trail being short tells it a pop happened, but not how far, and a pop followed by
     pushes back to the same length leaves no trace in [trail_len] at all.
     One slot PER READER rather than one per store because a read resets the mark, so
     two engines on one store (a unit test's shape, never a solve's) sharing a slot
     would each steal the other's pops. See [register_low_water]. They let the engine
     seed its queue from what CHANGED rather than from every propagator (M6-T18). *)
  mutable low_water : int array;
}

(* A conflict: the explanation of the contradiction ([c_why]), the bound facts it read
   ([c_reason]), and the propagator instance that reported it ([c_prop]). It is built
   from the same [Reason.justified] value a pruning is, by [conflict] below, so the two
   halves arrive together here too.

   [c_prop] is the reporting instance's id. The engine knows it in a local variable when
   [propagate] returns, but [Search] and [Trace] are handed the conflict after that local
   is gone, and 1UIP learning (M2-T3) needs the conflicting constraint to start its
   resolution from. Added by M2-T7.

   [c_reason] is the facts a conflict under decisions writes as its own reason line
   before the branch's nogood (D-0018 point 3). A conflict establishes no bound, so it
   has no trail entry to hang them on, and they are a field of the returned value. It is
   a [Reason.t] with no default: a conflict with nothing behind it says [Reason.none]
   and is seen saying it, and [Trace.conflict_line] then writes no line, because a line
   over an empty tail claims an unconditional contradiction, which is false. History:
   before M2-T7 the facts went through a one-shot mutable slot on [t] (see
   [current_prop]); before M2-T8 they were a thunk. *)
type conflict = {
  c_prop : int;
  c_why : Explanation.t;
  c_reason : Reason.t;
  c_ahead : bool;
      (* "This conflict's derivation must be on the page AHEAD of its reason line", the
         conflict's twin of [entry.ahead]: stamped by [conflict] from [current_ahead],
         which only [deriving_ahead] sets. [Trace.conflict_line] reads it. A
         [Needs_derivation] family that reports a conflict WITH its facts, so that 1UIP
         learning has a reason to resolve from, must put the counting argument ahead of
         `rup ~facts >= 1`, which is not reverse unit propagation on its own. Added for
         cumulative (M4-T10, D-0096), the first such family whose conflicts carry
         facts. *)
}

type outcome = Unchanged | Changed | Conflict of conflict

let dummy_entry =
  {
    var = Var.of_int 0;
    old = Domain.singleton 0;
    now = Domain.singleton 0;
    why = Explanation.Arena.null;
    reason = Reason.of_facts Reason.none;
    concludes = None;
    prop = no_prop;
    ahead = false;
    sup_lo = no_support;
    sup_hi = no_support;
    pos = -1;
    cites = None;
  }

let dummy_mark = { trail_mark = 0; reason_mark = 0 }

(* The first index bearing each name, and per index the first index bearing ITS name.
   "First" is what the linear scan [var_named] used to return, so a model with two
   variables of one name (nothing in [Compile] produces one; a hand-built test store
   could) still gets the same answer. *)
let build_name_index names =
  let tbl = Name_tbl.create ((2 * Array.length names) + 1) in
  let rep =
    Array.mapi
      (fun i nm ->
        match Name_tbl.find_opt tbl nm with
        | Some j -> j
        | None ->
            Name_tbl.add tbl nm i;
            i)
      names
  in
  (tbl, rep)

(* Per representative, every variable of its name, ascending -- built only when some name
   is shared, which only a hand-built test store does. *)
let build_classes (_, rep) =
  let n = Array.length rep in
  let shared = ref false in
  Array.iteri (fun i r -> if r <> i then shared := true) rep;
  if not !shared then None
  else
    let cls = Array.make n [] in
    for i = n - 1 downto 0 do
      cls.(rep.(i)) <- i :: cls.(rep.(i))
    done;
    Some cls

let create ~names ~domains =
  if Array.length names <> Array.length domains then
    invalid_arg "Store.create: names and domains differ in length";
  let names = Array.copy names in
  let by_name = lazy (build_name_index names) in
  let nv = Stdlib.max 1 (Array.length domains) in
  {
    domains = Array.copy domains;
    initial = Array.copy domains;
    names;
    by_name;
    named_memo = [||];
    reasons = Explanation.Arena.create ();
    lo_sup = Array.make nv no_support;
    hi_sup = Array.make nv no_support;
    lo_hist = Array.make nv [||];
    lo_hn = Array.make nv 0;
    hi_hist = Array.make nv [||];
    hi_hn = Array.make nv 0;
    all_hist = Array.make nv [||];
    all_hn = Array.make nv 0;
    classes = lazy (build_classes (Lazy.force by_name));
    trail = Array.make 64 dummy_entry;
    trail_len = 0;
    marks = Array.make 16 dummy_mark;
    n_levels = 0;
    starts = Array.make 64 0;
    current_prop = no_prop;
    current_ahead = false;
    low_water = [||];
  }

let n_vars t = Array.length t.domains
let get t v = t.domains.(Var.to_int v)
let name t v = t.names.(Var.to_int v)
let level t = t.n_levels

(* The trail position of the entry that established [v]'s current lower (upper) bound, or
   [no_support] while it is still the bound [v] was created with. O(1). Defined here, so
   far above the section that explains it, only because the D-0026 agreement check below
   reads it; the argument for why it is equivalent to the scan it replaced lives at
   "what holds a bound up". *)
let lo_support t v = t.lo_sup.(Var.to_int v)
let hi_support t v = t.hi_sup.(Var.to_int v)

(* The trail position of the entry that FIRST brought [v]'s upper bound below [k]
   ([hi_below]), or its lower bound to [k] or above ([lo_at_least]), or [no_support] when
   the declared bound already did. These are the positions at which the order literals
   `v >= k` and `v < k` became false, and so the positions a backtrack must undo to make
   them non-false again, which is what the watch rule of [Clause.Learned_clause] ranks
   literals by (learned clauses answer their wakes through an advisor with two watched
   literals, M6-T20, D-0104).

   [hi_support] is NOT that position: it is the entry behind the CURRENT bound, and a
   bound that has moved twice since it crossed [k] has a support later than its crossing.
   The first M6-T20 draft ranked by the support, so it watched a literal falsified early
   as if it had been falsified late, and the BAGUETTE_DEBUG check of I-P7 (an advisor
   answers for every wake it drops) caught the clause going unit unwatched after a
   backjump.

   How it is found. Each entry records the support of the bound BEFORE it
   ([sup_lo]/[sup_hi]), so the crossing could be found by walking one bound's own chain
   of moves back from its support while the entry's [old] bound was already past [k].
   That chain IS the bound's HISTORY ([hi_hist]/[lo_hist]) read backwards: [apply] pushes
   a position there exactly when it writes [hi_sup] (the next entry's [sup_hi]), and
   [undo_to] pops it exactly when it restores it. Along the history the [old] upper
   bounds do not increase (the first is the declared bound, each later one the [now] of
   the entry before, and no entry outside the history moves the bound), so "[old] is
   already below [k]" is false, then true. So the search tests the newest [walk_first]
   entries one by one, then binary-searches the rest for the first entry where it is
   true, and answers its predecessor, or [no_support] when there is none: O(min(steps,
   log moves)). It gives the walk's answer even for a literal that is not false now (the
   walk then stops at once on the current support, the history's top). Symmetric on the
   lower bound.

   Measured: on 2021 perfect_square the plain walk was 7 % of the instructions, because
   its learned clauses watch literals falsified many moves ago (the history search is
   M16-file-review-T1's, D-0186). The walks stay, as [hi_below_walk] and
   [lo_at_least_walk], for the BAGUETTE_DEBUG cross-check and test_core.ml's oracle. *)
let hi_below_walk t v k =
  let rec back p =
    if p = no_support then p
    else
      let e = t.trail.(p) in
      if Domain.hi e.old < k then back e.sup_hi else p
  in
  back (hi_support t v)

let lo_at_least_walk t v k =
  let rec back p =
    if p = no_support then p
    else
      let e = t.trail.(p) in
      if Domain.lo e.old >= k then back e.sup_lo else p
  in
  back (lo_support t v)

(* The newest [walk_first] moves are tested one by one, newest first, before the binary
   search takes the rest: a literal falsified a move or two ago is then found in a step or
   two, as the walk found it, and only an old crossing pays the logarithm. The binary
   search alone cost 2013 rcpsp_11 0.56 % more instructions per node than the walk, whose
   crossings are recent, and grew with its histories; the walk alone is perfect_square's 7
   %. *)
let walk_first = 4

(* [h.(j)] for the largest [j <= top] whose [old] upper bound is at least [k], or
   [no_support]. *)
let rec hi_crossing t h k top steps =
  if top < 0 then no_support
  else if Domain.hi t.trail.(h.(top)).old >= k then h.(top)
  else if steps > 1 then hi_crossing t h k (top - 1) (steps - 1)
  else
    (* every position from [top] up is below [k]: the first j in [0, top) that is *)
    let lo = ref 0 and hi = ref top in
    while !lo < !hi do
      let mid = (!lo + !hi) lsr 1 in
      if Domain.hi t.trail.(h.(mid)).old < k then hi := mid else lo := mid + 1
    done;
    if !lo = 0 then no_support else h.(!lo - 1)

let rec lo_crossing t h k top steps =
  if top < 0 then no_support
  else if Domain.lo t.trail.(h.(top)).old < k then h.(top)
  else if steps > 1 then lo_crossing t h k (top - 1) (steps - 1)
  else
    let lo = ref 0 and hi = ref top in
    while !lo < !hi do
      let mid = (!lo + !hi) lsr 1 in
      if Domain.lo t.trail.(h.(mid)).old >= k then hi := mid else lo := mid + 1
    done;
    if !lo = 0 then no_support else h.(!lo - 1)

let hi_below t v k =
  let i = Var.to_int v in
  let r = hi_crossing t t.hi_hist.(i) k (t.hi_hn.(i) - 1) walk_first in
  if Debug.enabled && r <> hi_below_walk t v k then
    failwith "invariant violated: D-0186: hi_below's history search agrees with the walk";
  r

let lo_at_least t v k =
  let i = Var.to_int v in
  let r = lo_crossing t t.lo_hist.(i) k (t.lo_hn.(i) - 1) walk_first in
  if Debug.enabled && r <> lo_at_least_walk t v k then
    failwith
      "invariant violated: D-0186: lo_at_least's history search agrees with the walk";
  r

let trail_length t = t.trail_len
let reasons t = t.reasons

(* ------------------------------------------------ who is running (M2-T7) *)

(* [Store] does not know what a propagator is -- [Propagator] depends on this module and
   not the other way round -- so it holds the id as a plain int and trusts its caller for
   nothing except that the id is the one the engine is about to run. That is a weaker
   obligation than it looks: exactly one caller sets it ([Engine.propagate], through
   [with_running]), and the check that the stamp is right lives there too, next to the
   instance whose [inst_vars] it can compare against.

   The alternative considered and rejected was for each propagator to pass its own id to
   every mutator it calls. That is invasive -- every [set_lo]/[set_hi]/[remove] call site
   in prop/ grows an argument -- and, worse, unenforceable: nothing stops a propagator
   passing an id that is not its own, and there is no second source of truth to check it
   against, because the caller IS the authority in that design. Stamping from the engine
   leaves the mutators with no id to get wrong and gives the check something to compare
   against; the one remaining route to a wrong stamp is re-entering [with_running] from
   inside a propagator, which [Engine.check_attribution] refuses. *)
let running t = t.current_prop

(* Run [f] with [id] recorded as the running instance, restoring whatever was recorded
   before. Restoring rather than clearing to [no_prop] so that nesting is not a trap: an
   engine that ever runs a propagator from inside another one gets the right answer, and
   a caller that never nests pays nothing for it.

   The restore runs on BOTH exits, the return and the exception, because a propagator
   can raise -- [Checked]'s overflow guard does, by design, so that no row whose
   arithmetic wrapped is ever committed (I-X8, D-0029) -- and a store
   left claiming a propagator is running when none is would stamp the next change with a
   stale id. The exception is re-raised with its own backtrace.

   It is written out as a [match ... with exception] rather than through [Fun.protect].
   The behaviour is the same on both exits ([Fun.protect]'s one extra case, a [finally]
   that raises, cannot arise: the restore is one field write), but this is one call per
   propagator RUN, 400 to 600 runs per node on codes-cp's QR48, and [Fun.protect]
   allocates its [finally] closure and goes through two more calls and a second handler
   on every one of them. [run_as] is the same bracket for the engine's own call, [f x]
   instead of [f ()], so that call allocates no closure either. (M11-complexity-T14, the
   per-node cost measured against Gecode on the same tree.) *)
let run_as t id f x =
  let saved = t.current_prop in
  t.current_prop <- id;
  if Explanation.stats_on then (
    (* Who builds which explanation, counted for BAGUETTE_MEMO_STATS only (the
       explanation-memo statistics of M11-complexity-T15) *)
    let p = !Explanation.producer in
    Explanation.producer := id;
    match f x with
    | r ->
        t.current_prop <- saved;
        Explanation.producer := p;
        r
    | exception e ->
        let bt = Printexc.get_raw_backtrace () in
        t.current_prop <- saved;
        Explanation.producer := p;
        Printexc.raise_with_backtrace e bt)
  else
    match f x with
    | r ->
        t.current_prop <- saved;
        r
    | exception e ->
        let bt = Printexc.get_raw_backtrace () in
        t.current_prop <- saved;
        Printexc.raise_with_backtrace e bt

let with_running t id f = run_as t id f ()

(* ------------------------------------------------ the derivation written ahead *)

(* Run [f] with every change it makes stamped [ahead = true]: lib/core/trace.ml will
   write the change's derivation (its forced [Explanation.t], through [Justify.emit])
   immediately before the change's trace line. A line that is NOT RUP against the .opb
   alone (a counting argument over several model constraints) is then RUP against the
   .opb plus the derivation just written, which is what I-X10 asks of every trace line.
   That is how a counting global is proved: an explicit derivation on the page, not a
   direct encoding (D-0040).

   The CALLER is the propagator, at its own pruning call, and that is the point of the
   design (D-0082, M7-T17): whether a pruning needs its derivation ahead is decided by
   HOW it was inferred, which only the propagator knows, and only at the moment it
   prunes. The engine does not set it (lib/core/engine.ml sets [current_prop], not
   this), because it runs every family the same way and has no way to know. History:
   the trigger was [Encoding.has_direct] of the pruned variable, a proxy for "this
   variable is in a counting global's scope" that over-triggered (an [int_lin_le]
   pruning of an all_different variable got a [pol] it did not need) and, once gcc's
   order-encoded rows arrived, under-triggered (D-0078).

   Restored rather than cleared, on both exits, for [with_running]'s reasons; here
   through [Fun.protect], which [run_as] avoids only because it runs once per
   propagator run. *)
let deriving_ahead t f =
  let saved = t.current_ahead in
  t.current_ahead <- true;
  Fun.protect ~finally:(fun () -> t.current_ahead <- saved) f

(* ------------------------------------------------------------- trail growth *)

let push_entry t e =
  if Debug.enabled then
    Debug.check "M6-T15: an entry is pushed at its own [pos]" (fun () ->
        e.pos = t.trail_len);
  if t.trail_len = Array.length t.trail then (
    let bigger = Array.make (2 * Array.length t.trail) dummy_entry in
    Array.blit t.trail 0 bigger 0 t.trail_len;
    t.trail <- bigger);
  t.trail.(t.trail_len) <- e;
  t.trail_len <- t.trail_len + 1

(* Push trail position [at] onto variable [i]'s history [h]/[hn]. Positions only grow
   along the trail, so the history stays sorted. *)
let push_hist (h : int array array) (hn : int array) i at =
  let n = hn.(i) in
  if n = Array.length h.(i) then (
    let bigger = Array.make (Stdlib.max 4 (2 * n)) no_support in
    Array.blit h.(i) 0 bigger 0 n;
    h.(i) <- bigger);
  h.(i).(n) <- at;
  hn.(i) <- n + 1

let push_mark t m =
  if t.n_levels = Array.length t.marks then (
    let bigger = Array.make (2 * Array.length t.marks) dummy_mark in
    Array.blit t.marks 0 bigger 0 t.n_levels;
    t.marks <- bigger);
  t.marks.(t.n_levels) <- m;
  t.n_levels <- t.n_levels + 1;
  let p = m.trail_mark in
  if p >= Array.length t.starts then (
    let bigger = Array.make (Stdlib.max (p + 1) (2 * Array.length t.starts)) 0 in
    Array.blit t.starts 0 bigger 0 (Array.length t.starts);
    t.starts <- bigger);
  t.starts.(p) <- t.starts.(p) + 1

(* ----------------------------------------------------------------- mutation *)

(* The variable of that name (the lowest-numbered, should two share it), or [None].

   One hash lookup into an index built on first use ([by_name]), behind a direct-mapped
   memo. [Pb_analysis], [Analysis.support_of], [Learn], [Pb] and [Search] all call it on
   the conflict path, and [Analysis.locate] asks it once per fact it locates.
   [var_named_scan] is the linear definition, kept as the specification the index is
   tested against (test_core.ml).

   The index is a [Name_tbl], keyed by [String.equal] and hashed by [String.hash] (the
   value [Hashtbl.hash] gave, without the generic hash's dispatch or the polymorphic
   compare).

   The memo has [memo_size] cells. The cell of a name is chosen by [memo_slot] (its
   length and its last eight bytes, multiplied and shifted, so a slot costs a few
   instructions where [String.hash] mixes the whole string behind a C call). A hit is a
   cell holding a variable [i] with [names.(i) == name], PHYSICAL equality. It is sound
   because [i] came out of the index for a name equal to [names.(i)], and any string
   equal to [names.(i)] gets the same answer from the index; a name that is equal
   without being that very string just misses. The slot only decides WHERE an answer is
   remembered, never what it is, so two names sharing a slot just evict each other, and
   [memo_slot] could be any function of the string. The answer is an int ([-1]: no such
   name), so a hit allocates nothing; [var_named] wraps it.

   Why it pays: producers name a variable by [name t v], i.e. by the string in [names],
   so a repeated question is a physical repeat, and conflict analysis asks about the
   variables near the conflict, conflict after conflict. Over 3 000 nodes of elitserien
   handball12 (no proof), 98.0 % of 8.87 M lookups hit, and 99.6 to 99.99 % on tppv
   circ14, costas13 and qr2 (D-0245).

   History. The lookup was a linear scan, documented as "only called from the
   debug-gated agreement check"; once the conflict path called it, D-0080 measured it at
   11 % of a 60 s profile on 2018 rotating-workforce, and M6-T11 (D-0085) built the
   index. M20-pernode-T4 then keyed the index by [Name_tbl] (it was 7.3 % of elitserien
   handball12's instructions without the proof) and put a ONE-ENTRY memo in front of it
   (a reason names one variable twice in a row more often than not: [Reason.fixed_at]'s
   two halves, alldiff's [at_least]/[at_most] of one snapshot; D-0236 counted 47 % of
   that instance's lookups as physical repeats of the one before, and none equal without
   being physical), which D-0245 generalised to the
   direct-mapped memo; the one-entry memo is its case [memo_size = 1]. *)
let memo_bits = 12
let memo_size = 1 lsl memo_bits

external string_get64u : string -> int -> int64 = "%caml_string_get64u"

let memo_slot name =
  let n = String.length name in
  let h =
    if n >= 8 then Int64.to_int (string_get64u name (n - 8))
    else
      let h = ref 0 in
      for i = 0 to n - 1 do
        h := (!h lsl 8) lor Char.code (String.unsafe_get name i)
      done;
      !h
  in
  (h lxor n * 0x2545F4914F6CDD1D) lsr (Sys.int_size - memo_bits)

let rec var_index_named t name =
  let m = t.named_memo in
  if Array.length m = 0 then (
    t.named_memo <- Array.make memo_size (-1);
    var_index_named t name)
  else
    let slot = memo_slot name in
    let i = m.(slot) in
    if i >= 0 && t.names.(i) == name then i
    else
      match Name_tbl.find_opt (fst (Lazy.force t.by_name)) name with
      | Some i ->
          m.(slot) <- i;
          i
      | None -> -1

let var_named t name =
  let i = var_index_named t name in
  if i < 0 then None else Some (Var.of_int i)

let var_named_scan t name =
  let n = Array.length t.names in
  let rec go i =
    if i >= n then None
    else if String.equal t.names.(i) name then Some (Var.of_int i)
    else go (i + 1)
  in
  go 0

(* [var_named t (name t v)], in O(1): the variable whose NAME a trail scan is really
   comparing against. [Var.equal (name_rep t a) (name_rep t b)] iff
   [String.equal (name t a) (name t b)], which is what lets [Analysis.scan_support]
   compare integers along the trail instead of strings (M6-T11). With unique names --
   every store [Compile] builds -- it is the identity. *)
let name_rep t v = Var.of_int (snd (Lazy.force t.by_name)).(Var.to_int v)

(* Whether trail position [i] was pushed at level 0. [level_of_index] answers the general
   question further down; this is its level-0 case, by I-T2 (the marks are monotone, so
   [i] precedes every mark iff it precedes the first). *)
let at_root t i = t.n_levels = 0 || i < t.marks.(0).trail_mark

(* Whether the store holds the ORDER literal [l] at the ROOT: the current bound implies it
   and the entry supporting that bound, if any, was pushed at level 0. A bound still at
   its declaration counts -- nothing moved it, so nothing a decision did holds it up.
   Mirrors [established_at_root] in lib/core/prop/element.ml and alldiff.ml, which decide
   whether a [Defining] may be BUILT; this decides whether one may go unnamed. A direct
   literal answers [false]; see [agreement_holds]. *)
let root_holds t (l : Lit.t) =
  match l.Lit.v with
  | Lit.Eq _ | Lit.Bit _ -> false (* a bit is never a bound fact (D-0130 section 3.2) *)
  | Lit.Ge (x, k) -> (
      match var_named t x with
      | None -> false
      | Some v ->
          let root sup = sup = no_support || at_root t sup in
          if l.Lit.positive then Domain.lo (get t v) >= k && root (lo_support t v)
          else Domain.hi (get t v) <= k - 1 && root (hi_support t v))

(* A PAGE-ONLY LEMMA: a [Term (c, Clause l)] followed at once by a [Weaken] of exactly
   [(c, ~l_j)] for each literal of [l], in order. Each [c l_j + c ~l_j] is the constant
   [c], so the pair adds a constant to the row and NO VARIABLE: the clause is in the
   derivation only so that its own line is on the page ahead of the line that needs it
   (member.ml's threshold lemmas, D-0170), and the derivation's result does not read it.
   The [Weaken] there is not "a variable read and weakened away", which is
   the only thing the reverse arm asks the reason to account for. Matched on the raw
   [Clause], never a [Deferred] one, so the check forces nothing it did not force before,
   and on the exact shape: one coefficient or literal off and the [Weaken] counts.
   History: M7-T35 (D-0189), after the reverse arm over-read member's threshold lemmas
   and six member models stopped under BAGUETTE_DEBUG with correct reasons. *)
let page_only_lemma c lits ws =
  List.compare_lengths lits ws = 0
  && List.for_all2 (fun l (c', w) -> c' = c && Lit.equal w (Lit.negate l)) lits ws

(* Accumulated and reversed (D-0197): a [Combine]'s summand list is as long as the
   ladders it crosses, so no walk over one recurses once per summand. *)
let drop_page_only_lemmas summands =
  let rec go acc = function
    | Explanation.Term (c, Explanation.Clause { lits; _ })
      :: Explanation.Weaken ws
      :: rest
      when page_only_lemma c lits ws ->
        go acc rest
    | s :: rest -> go (s :: acc) rest
    | [] -> List.rev acc
  in
  go [] summands

(* [Explanation.top_weaken_owners] less every top-level [Defining] the root holds and
   every page-only lemma's [Weaken]: the variables the reverse arm of [agreement_holds]
   requires the reason to name. *)
let reverse_owners t e =
  match Explanation.force e with
  | Explanation.Combine { summands; divisor = _; _ } ->
      List.sort_uniq String.compare
        (List.concat_map
           (function
             | Explanation.Weaken lits -> List.map (fun (_, l) -> Lit.owner l.Lit.v) lits
             | Explanation.Defining (_, l) ->
                 if root_holds t l then [] else [ Lit.owner l.Lit.v ]
             | Explanation.Term _ -> []
             | Explanation.Linear_term r -> if r.lt_cited = [] then [ r.lt_name ] else [])
           (drop_page_only_lemmas summands))
  | _ -> []

(* The predicate, public and unconditional, so that a test can assert it directly rather
   than only through an environment variable read at module initialisation. A check that
   only runs under [BAGUETTE_DEBUG] is a check the suite cannot see fail; test_core.ml
   tests this function on both answers and then re-runs itself with the flag on to prove
   the wiring fires.

   Two directions, and neither is the naive one.

   **Forward.** Every fact the reason actually STATES is about a bound the justification
   could have used: either the derivation MENTIONS that variable's literals, or that bound
   is held up by a trail entry -- in which case the derivation is entitled to cite it by
   id and says nothing about the variable at all. That second arm is not slack, it is
   D-0038: [Explanation.Combine] records how a bound was derived and not what was derived,
   so a [Term (c, e)] citing "the entry that established y >= 2" contains no literal about
   y anywhere. The naive predicate ([Reason.owners] included in [Explanation.owners])
   therefore FIRES ON EVERY CORRECT CITING PRUNING -- found by running it, in
   test_prop.ml's D-0026 scene, not by reading it.

   "Actually states" is the second correction the same way. A fact at its declared bound
   materialises to no literal at all, so it appears in neither half and can contradict
   nothing: [Bool2int] pushing `x <= 1` out of `b <= 1` with `b` still at its declared
   upper bound is a correct pruning whose reason materialises to nothing and whose clause
   mentions only `x`. Requiring a support there fired on three test binaries. Both
   corrections were found by turning BAGUETTE_DEBUG on and watching the check reject
   working code; neither was visible by reading it.

   The forward arm compares variable SCOPES, so it catches a reason naming the wrong
   variable and not the right variable at the wrong value. The value is checked exactly
   by [conclusion_holds] below, against the conclusion each pruning now carries (D-0043,
   which answered D-0038's question).

   **Reverse.** Every variable the derivation weakens out of its own row at the top level
   must be named by the reason ([Explanation.top_weaken_owners] says why top level). This
   is the I-P5 direction (a pruning's reason carries every fact its trace line negates;
   I-P5 is now part of I-P4): a derivation that read a variable and weakened it away has
   a pruning that depends on it, and a reason that omits it writes a trace line over too
   short a tail.

   **The reverse arm and a ROOT [Defining].** A top-level [Explanation.Defining (c, l)]
   on an order literal the ROOT established is exempt; one a branch rests on counts as a
   [Weaken] does. The difference is D-0064's own construction rule: a [Defining] may cite
   only a
   consequence of the MODEL (element.ml's and alldiff.ml's [established_at_root], gcc.ml's
   [root]). A reason is the list of facts a BRANCH rests on -- what a trace line assumes
   on its tail and what a learned clause negates -- and a root-established fact is in no
   branch's dependency: its unit line is on the page at level 0 and is never wiped, so a
   trace line that omits it is no shorter in the sense I-P5 means, and [Analysis] drops a
   root node from every cut anyway. History: until M6-T8 (D-0091) a root [Defining]
   counted as a [Weaken] too, and demanding it of the reason fired on every element
   no-position conflict whose residue cancellation cites a root bound (four suite models,
   found by turning BAGUETTE_DEBUG on) while the proofs verified.

   So a top-level [Defining] on an ORDER literal is exempt exactly when the STORE says the
   bound is root-held -- checked here, not taken on the propagator's word. A [Defining] of
   a bound a decision set (the D-0064 violation) is still required, and so is every
   [Weaken]. A [Defining] on a DIRECT literal (alldiff's hole units) is not exempted: no
   caller in [lib/] needs it to be, and deciding whether a hole is root-held needs
   [remover], which is not this check's business to call. *)
let agreement_holds t (j : Reason.justified) =
  let mentioned = Explanation.owners j.justification in
  let supported fact =
    match var_named t (Reason.fact_owner fact) with
    | None -> false
    | Some v ->
        if Reason.fact_is_lower fact then lo_support t v <> no_support
        else hi_support t v <> no_support
  in
  let named = Reason.owners j.reason in
  List.for_all
    (fun fact ->
      Option.is_none (Reason.lit_of_fact fact)
      || List.mem (Reason.fact_owner fact) mentioned
      || supported fact)
    (Reason.facts j.reason)
  && List.for_all (fun o -> List.mem o named) (reverse_owners t j.justification)

(* The conclusion a pruning carries ([concludes], D-0043) is the bound this change
   produced, up to the holes the store settled over.

   [agreement_holds] above compares the two halves' variable SCOPES, so it catches a
   reason naming the wrong variable and not the right variable at the wrong value. A
   conclusion is a value, so this check is exact where that one is structural. The defect
   it closes is the one I-X9 forbids (an explanation justifies the bound as recorded on
   the trail): a claim one unit off the bound the trail actually holds, which M1-T44 met
   as a correct UNSAT answer whose proof the checker rejected, and which nothing on our
   side had seen first.

   Three conjuncts, and each rejects a different wrong answer:

     - the conclusion is about the variable this change is about (not some other
       variable that happens to sit at that value);
     - its direction is one this change actually MOVED. A [Some] in the direction the
       change left alone would be a claim about a bound this pruning did not establish,
       which is the "right variable, wrong bound" case;
     - its value is the new bound, UP TO THE HOLES THE STORE SETTLED OVER, and that
       window is checked value by value rather than allowed as slack. With no hole in
       the way it reduces to "exactly the new bound", which is what every propagator in
       [lib/] hits almost all of the time. Not "at least as strong" and not "at least as
       weak": a conclusion stronger than the change is a claim the store cannot back,
       and a weaker one is precisely what M1-T51 measured the checker accepting in
       silence (a [pol] that derives something weaker than the claimed bound).

   THE SETTLE WINDOW was measured, not designed. Running the suite under BAGUETTE_DEBUG
   with the naive "exactly the new bound" test reddened three scenes and every one was
   the same shape: [Domain.set_lo] does not stop at the bound it is given, it SETTLES
   over the holes immediately above it (I-D2). `x` over `1..3 \ {2}`, told `x >= 2`,
   lands at 3. Both numbers are honest claims about that one change -- 2 is what the
   propagator's row derives and what its [pol] can be checked against, 3 is what the
   trail holds and what lib/core/trace.ml's line claims, citing the hole's own line as
   [settled_over] -- and the distance between them is exactly the settled holes. So that
   is what this admits, and nothing else: every value strictly between the claim and the
   new bound must be a hole of [old]. A claim one unit off across a value that is not a
   hole is still rejected, which is the whole of test (b).

   [None] passes, and reason.ml's header enumerates when [None] is the honest answer --
   a decision, a conflict, an interior hole. *)
let conclusion_holds t v ~old ~now (j : Reason.justified) =
  match j.concludes with
  | None -> true
  | Some f ->
      let b = Reason.fact_value f in
      (* Every value from [b] towards the new bound, exclusive, was a hole. *)
      let settled_up limit =
        let rec go u = u >= limit || (Domain.is_hole old u && go (u + 1)) in
        go b
      in
      let settled_down limit =
        let rec go u = u <= limit || (Domain.is_hole old u && go (u - 1)) in
        go b
      in
      String.equal (Reason.fact_owner f) (name t v)
      &&
      if Reason.fact_is_lower f then
        Domain.lo now > Domain.lo old
        && b > Domain.lo old
        && b <= Domain.lo now
        && settled_up (Domain.lo now)
      else
        Domain.hi now < Domain.hi old
        && b < Domain.hi old
        && b >= Domain.hi now
        && settled_down (Domain.hi now)

(* A DECISION concludes nothing (D-0037: a decision is an assumption, not a consequence
   of the model row), and this enforces it.

   A decision moves a bound like any pruning, so [conclusion_holds] above would happily
   accept one that claimed it: the numbers agree, because the store really did set that
   bound. What is wrong is the claim. Nothing in the proof establishes a decision
   ([Justify.emit] refuses a [Decision] outright, D-0009), so stating that the pruning
   derived it repeats the M1-T50 defect (linear.ml citing its own row twice when a fact
   came from a decision) in a new field. The match is on the raw justification and not on
   [Explanation.force]: a decision is never [Deferred], and forcing here would run a
   propagator's thunk inside an invariant check. *)
let decision_concludes_nothing (j : Reason.justified) =
  match j.justification with
  | Explanation.Decision _ -> Option.is_none j.concludes
  | _ -> true

(* The agreement check of D-0026: the reason and the justification are about the same
   pruning.

   They are two projections of one pruning, and cannot be compared literal for literal:
   a [Weaken] summand states a variable's whole declared range while the reason states
   where its bound currently sits, so for a weakened term the two share no literal at all
   (lib/core/explanation.ml's [owners] says this at length). What they must share is the
   VARIABLE SCOPE: a reason naming a variable the derivation never mentions is a reason
   for a different pruning, which is how a hand-edited propagator drifts. Before M2-T8
   the two were kept in agreement by a comment.

   Under [BAGUETTE_DEBUG] only, and it FORCES the justification to do it. That is a
   deliberate cost with one sharp edge: forcing at push time masks an I-X6 violation (a
   deferred explanation that reads live state reads it before anything has moved). That
   is how [explain_cross_conflict]'s violation stayed hidden until M1-T13, because search
   happened to force conflict explanations immediately. A debug run therefore cannot be
   the run that catches a NEW I-X6 violation, and nothing here claims otherwise: the type
   discharges I-X6 on the reason half (lib/core/reason.ml), and on the justification half
   it stays an argument that test_prop.ml's snapshot tests check by backtracking before
   forcing.

   The failing message carries the offending pair, because "these two disagree" without
   saying which fact and which derivation is a message that sends the reader back to a
   breakpoint. Built only on the failing path, so the enabled-and-passing cost is the
   predicate alone. *)
let check_agreement t (j : Reason.justified) =
  if Debug.enabled then
    Debug.check "D-0124: a deferred reason's [empty] agrees with its materialisation"
      (fun () -> Reason.is_empty j.reason = (Reason.facts j.reason = []));
  if Debug.enabled && not (agreement_holds t j) then
    failwith
      (Printf.sprintf
         "invariant violated: D-0026: the reason and the justification are about the \
          same pruning -- reason [%s] vs justification %s"
         (Reason.to_string j.reason)
         (Explanation.to_string (Explanation.force j.justification)))

(* The two conclusion checks above, under one [Debug.enabled] test and with the message
   built only on the failing path -- [Debug.check]'s [name] is an ordinary argument, so a
   [Printf.sprintf] handed to it is paid on every pruning of every run, debugging or not.
   [check_agreement] is shaped this way for the same reason. *)
let check_conclusion t v ~old ~now (j : Reason.justified) =
  if Debug.enabled then (
    if not (decision_concludes_nothing j) then
      failwith
        (Printf.sprintf
           "invariant violated: D-0043/D-0037: a decision concludes nothing -- it is an \
            assumption, not a derived bound, but this one claims %s"
           (match j.concludes with None -> "-" | Some f -> Reason.fact_to_string f));
    if not (conclusion_holds t v ~old ~now j) then
      failwith
        (Printf.sprintf
           "invariant violated: D-0043: the conclusion must be the bound this change \
            produced -- %s claims %s, but the change recorded is %s -> %s"
           (name t v)
           (match j.concludes with None -> "-" | Some f -> Reason.fact_to_string f)
           (Domain.to_string old) (Domain.to_string now)))

(* A conflict, attributed to whoever is running. The propagator never names itself; see
   [with_running]. It takes the same [Reason.justified] a pruning does, so "a conflict
   with no facts" is [Reason.because ~concludes:None Reason.none expl], written out and
   never defaulted; see [Reason.none]. *)
let conflict t (j : Reason.justified) =
  check_agreement t j;
  {
    c_prop = t.current_prop;
    c_why = j.justification;
    c_reason = j.reason;
    c_ahead = t.current_ahead;
  }

(* The one documented exception to the agreement check, for [apply]'s [Failed] arm alone.

   That arm deliberately pairs the justification of the change that did NOT land with
   [Reason.none], because the facts a *conflict* line needs are strictly more than the
   pruning's (see the comment there). The pair is therefore a real disagreement by the
   check's standard -- the derivation weakens variables the empty reason does not name --
   and it is sound only because nothing writes a trace line for it: [Trace.conflict_line]
   writes nothing over an empty tail, and the propagators that care build their own
   [conflict] with the fuller set.

   It is a separate function rather than a flag on [conflict] so that the exception is one
   named call site that a reader trips over, and so that adding a second one is an edit to
   this file. Found by turning the check on: this arm was the only false positive left in
   the suite once non-materialising facts were skipped.

   [c_ahead] carries [current_ahead] exactly as [conflict] does. [Search]'s root arm
   writes a factless conflict's derivation ONLY when the family flagged the conflict, and
   the pigeonhole (alldiff's and gcc's push that empties a domain, made inside
   [deriving_ahead]) is a conflict of exactly that kind: its derivation is the counting
   argument the empty clause rests on. Measured: with [false] here, five root
   refutations (alldiff_hall_unsat, alldiff_pigeonhole_narrow_unsat, gcc_capacity_unsat,
   ...) closed on `rup >= 1` with no derivation on the page and 3.0.2 refused each at
   that line. History: it was hard-coded [false] while both of [Search]'s conflict arms
   wrote a factless derivation unconditionally, until M8-bits-encoding-T5 (D-0131, which
   writes the order arm's ladder walks as [rup]) made the root arm read the flag. *)
let unattributed_conflict t why =
  {
    c_prop = t.current_prop;
    c_why = why;
    c_reason = Reason.of_facts Reason.none;
    c_ahead = t.current_ahead;
  }

(* Apply a [Domain.result], recording the old value so it can be undone.

   Every path through here takes ONE [Reason.justified], which carries both halves of
   D-0026 (the reason and the justification) and so discharges I-P4: every change
   carries its explanation, and its reason carries the facts its trace line negates.
   There is no second entry point that takes fewer: do not add an optional argument and
   do not add a sibling function that omits the reason. History: a [set_lo_with_facts]
   sibling existed until M2-T8, and the plain [set_lo] beside it silently meaning "no
   facts" is how [int_ne] (M1-T9) pruned without facts until M1-T17. *)
let apply t v (r : Domain.result) (j : Reason.justified) =
  let why = j.justification in
  match r with
  | Domain.Unchanged -> Unchanged
  | Domain.Failed ->
      (* Deliberately WITHOUT the pruning's reason. That reason belongs to the change
         that did not land, and the facts a *conflict* line needs are strictly more: the
         crossed opposing bound as well (see lib/core/prop/linear.ml's [cross_conflict]
         and bool2int.ml's push arms, which both build the fuller set and return their
         own [conflict]). Attaching the partial set here would give those unreachable-at-
         the-interface forwarding arms in ne.ml and bool_clause.ml a conflict line over
         too few facts -- a claim that those facts alone are contradictory, which is
         false and which veripb would reject. They get no line. *)
      Conflict (unattributed_conflict t why)
  | Domain.Changed d ->
      let i = Var.to_int v in
      let old = t.domains.(i) in
      if Debug.enabled then (
        Debug.check "I-D3: domains only shrink" (fun () ->
            Domain.lo d >= Domain.lo old
            && Domain.hi d <= Domain.hi old
            && Domain.size d < Domain.size old);
        Debug.check "I-D1: a stored domain is non-empty" (fun () ->
            Domain.lo d <= Domain.hi d));
      check_agreement t j;
      check_conclusion t v ~old ~now:d j;
      let why = Explanation.Arena.add t.reasons why in
      let at = t.trail_len in
      push_hist t.all_hist t.all_hn i at;
      push_entry t
        {
          var = v;
          old;
          now = d;
          why;
          reason = j.reason;
          concludes = j.concludes;
          prop = t.current_prop;
          ahead = t.current_ahead;
          sup_lo = t.lo_sup.(i);
          sup_hi = t.hi_sup.(i);
          pos = at;
          cites = None;
        };
      (* The support of a bound this entry moved is this entry. A bound it left alone
         keeps whatever supported it, which is what the saved fields above restore. Both
         are tested: [Domain.fix] moves both, [Domain.remove] of an interior value moves
         neither. *)
      if Domain.lo d > Domain.lo old then (
        t.lo_sup.(i) <- at;
        push_hist t.lo_hist t.lo_hn i at);
      if Domain.hi d < Domain.hi old then (
        t.hi_sup.(i) <- at;
        push_hist t.hi_hist t.hi_hn i at);
      t.domains.(i) <- d;
      Changed

(* One mutator per kind of change, each taking one [Reason.justified]. There is no
   factless sibling and no optional argument: see [apply]. *)
let set_lo t v bound j = apply t v (Domain.set_lo (get t v) bound) j
let set_hi t v bound j = apply t v (Domain.set_hi (get t v) bound) j
let remove t v value j = apply t v (Domain.remove (get t v) value) j
let fix t v value j = apply t v (Domain.fix (get t v) value) j

(* ------------------------------------------------------------- backtracking *)

let new_level t =
  push_mark t
    { trail_mark = t.trail_len; reason_mark = Explanation.Arena.length t.reasons }

(* Undoing an entry restores the bound supports it saved as well as the domain. Both
   have to move together or [lo_support] starts naming a trail position that has been
   popped -- I-T3's failure mode one level up, and the reason [lo_support]'s equivalence
   with the scan it replaced holds at all. *)
let undo_to t target =
  while t.trail_len > target do
    let e = t.trail.(t.trail_len - 1) in
    let i = Var.to_int e.var in
    Domain.undo ~old:e.old ~now:e.now;
    t.domains.(i) <- e.old;
    t.lo_sup.(i) <- e.sup_lo;
    t.hi_sup.(i) <- e.sup_hi;
    (* The entry being popped is the newest on the trail, so if it moved a bound it is
       the top of that bound's history. *)
    t.all_hn.(i) <- t.all_hn.(i) - 1;
    if Domain.lo e.now > Domain.lo e.old then t.lo_hn.(i) <- t.lo_hn.(i) - 1;
    if Domain.hi e.now < Domain.hi e.old then t.hi_hn.(i) <- t.hi_hn.(i) - 1;
    t.trail.(t.trail_len - 1) <- dummy_entry;
    t.trail_len <- t.trail_len - 1
  done;
  let lw = t.low_water in
  for r = 0 to Array.length lw - 1 do
    if t.trail_len < lw.(r) then lw.(r) <- t.trail_len
  done

(* A new low-water reader, whose mark starts at the CURRENT trail length -- the
   reader has seen nothing yet, so nothing has been popped from under it. Returns the
   handle [take_low_water] takes. *)
let register_low_water t =
  let r = Array.length t.low_water in
  t.low_water <- Array.append t.low_water [| t.trail_len |];
  r

(* Reader [r]'s minimum trail length since its previous call (or since it
   registered), and reset its mark to the current length. Every trail position below the
   returned value has been on the trail, UNCHANGED, throughout; every position at or
   above it may have been popped and pushed again. The trail shrinks only in [undo_to],
   which lowers every reader's mark, so the mark is exact, not an estimate. *)
let take_low_water t r =
  let m = t.low_water.(r) in
  t.low_water.(r) <- t.trail_len;
  m

let backtrack t =
  if t.n_levels = 0 then invalid_arg "Store.backtrack: already at level 0";
  let m = t.marks.(t.n_levels - 1) in
  undo_to t m.trail_mark;
  Explanation.Arena.truncate t.reasons m.reason_mark;
  t.starts.(m.trail_mark) <- t.starts.(m.trail_mark) - 1;
  t.n_levels <- t.n_levels - 1

let backtrack_to t target_level =
  if target_level < 0 then invalid_arg "Store.backtrack_to: negative level";
  if target_level > t.n_levels then
    invalid_arg "Store.backtrack_to: cannot backtrack forwards";
  while t.n_levels > target_level do
    backtrack t
  done

(* ------------------------------------------------------------------ reading *)

let all_fixed t = Array.for_all Domain.is_fixed t.domains
let snapshot t = Array.copy t.domains

let same_domains t snap =
  Array.length snap = Array.length t.domains
  &&
  let ok = ref true in
  Array.iteri (fun i d -> if not (Domain.equal d snap.(i)) then ok := false) t.domains;
  !ok

(* The trail, most recent first. Conflict analysis walks this. *)
let trail_entries t =
  let acc = ref [] in
  for i = 0 to t.trail_len - 1 do
    acc := t.trail.(i) :: !acc
  done;
  !acc

(* The trail position at which each open level began, oldest level first. I-T2 says these
   are monotone; [check_invariants] asserts it. *)
let level_marks t = List.init t.n_levels (fun i -> t.marks.(i).trail_mark)
let explanation t e = Explanation.Arena.get t.reasons e.why

(* One trail entry by position, oldest first -- the order [Trace] walks, and the order
   the proof's trace lines have to be written in. [trail_entries] above is the other
   direction (newest first) and allocates the whole list; this does neither. *)
let trail_entry t i =
  if i < 0 || i >= t.trail_len then
    invalid_arg
      (Printf.sprintf "Store.trail_entry: %d out of range (len %d)" i t.trail_len);
  t.trail.(i)

(* ------------------------------------------------------ what holds a bound up *)

(* [lo_support] (defined near the top, because the agreement check reads it) is the
   trail position of the entry that established [v]'s current lower bound, or
   [no_support] while it is still the bound [v] was created with. O(1).

   It answers what lib/core/prop/linear.ml's [find_lo_reason] (deleted by M2-T8) answered
   by scanning the trail downwards from the newest entry, once per term per pruning. Why
   the two agree, because it is not obvious and because the DIRECTION of that scan was
   load-bearing (M1-T28 recorded that scanning upwards returns the OLDEST entry that
   moved the bound, i.e. a superseded reason, and that no model in the suite can tell the
   two apart):

     - The scan looked for the newest entry [e] for [v] with [Domain.lo e.old < cur].
       Lower bounds only increase within a level (I-D3), so that entry is exactly the
       last one that increased lo, and every later entry for [v] left lo alone.
     - [apply] writes this array precisely when the change it is applying increases lo,
       so the array holds the last such entry -- the same one.
     - [undo_to] restores the value the entry saved, so a popped entry is never named.

   The remaining difference is the guard. The scan took the *propagator's frozen declared
   bound* and returned nothing when [cur] had not passed it; this array knows only what
   the store was created with. The two differ for a propagator built after something had
   already narrowed the variable (which unit tests do deliberately), so the guard stays
   at the call site where the declared bound lives: [Linear.snapshot_at], behind
   [snapshot_source], makes exactly that test before asking. *)
(* ---------------------------------------------- which entry established a value *)

(* Did [e] establish [value] in this direction? True for at most one live entry per
   (variable, direction, value), by I-D3's monotonicity. Moved here from
   lib/core/analysis.ml, which re-exports it, so that the history search below and the
   scan it replaced share ONE predicate -- the direction asymmetry ([>=] on a lower
   bound, [<=] on an upper) included. *)
let establishes (e : entry) ~is_lower ~value =
  if is_lower then Domain.lo e.old < value && Domain.lo e.now >= value
  else Domain.hi e.old > value && Domain.hi e.now <= value

(* The live entry on variable index [i] that established [value], or [no_support]. Along
   [i]'s lower-bound history the [now] lower bounds strictly increase and each entry's
   [old] lower bound is its predecessor's [now] (no other entry moved it in between), so
   the entries partition the values above the declared bound into consecutive intervals
   (old, now]: the one containing [value] is the FIRST whose [now] reaches it, found by
   binary search, and it establishes [value] iff its [old] does not already reach it --
   which can fail only for the first entry, when the declared bound already does.
   Symmetric on the upper bound. O(log moves of [i]). *)
let member_support t i ~is_lower ~value =
  let h, n =
    if is_lower then (t.lo_hist.(i), t.lo_hn.(i)) else (t.hi_hist.(i), t.hi_hn.(i))
  in
  let reaches (d : Domain.t) =
    if is_lower then Domain.lo d >= value else Domain.hi d <= value
  in
  (* first j in [0, n) with reaches now(h.(j)), or n *)
  let lo = ref 0 and hi = ref n in
  while !lo < !hi do
    let mid = (!lo + !hi) lsr 1 in
    if reaches t.trail.(h.(mid)).now then hi := mid else lo := mid + 1
  done;
  if !lo = n then no_support
  else
    let at = h.(!lo) in
    if establishes t.trail.(at) ~is_lower ~value then at else no_support

(* [member_support] on one exact variable, for [Pb_analysis.falsified_at], which compares
   [Var.equal] rather than [name_rep]. *)
let var_support t v ~is_lower ~value = member_support t (Var.to_int v) ~is_lower ~value

(* The trail position, strictly below [before], of the newest entry ON ANY VARIABLE OF
   [v]'s NAME that established [value] in this direction, or [no_support] -- exactly what
   the downward scan [Analysis.scan_support] returns (it compares [name_rep]), in
   O(log moves) instead of O(|trail|) per call. Each member has at most one live
   establishing entry, so "strictly below [before]" is a test on that one entry, not a
   search. With unique names the class is [v] alone. *)
let bound_support t ~before v ~is_lower ~value =
  let below at = if at <> no_support && at < before then at else no_support in
  let r = Var.to_int (name_rep t v) in
  match Lazy.force t.classes with
  | None -> below (member_support t r ~is_lower ~value)
  | Some cls ->
      List.fold_left
        (fun acc i -> Stdlib.max acc (below (member_support t i ~is_lower ~value)))
        no_support cls.(r)

(* The entry that took [value] out of [var]'s domain, looking back from trail position
   [before] (exclusive). A value leaves a domain once and stays gone until the backtrack
   that pops the entry that removed it, so there is at most one and this finds it at the
   first hit.

   [None] means a hole with no trail entry behind it, i.e. a DECLARED domain with a gap
   (`var {1,3,5}: x`). Nothing in `lib/` produces one: lib/flatzinc/compile.ml gives the
   store the HULL of a set domain and posts one [Ne] instance per hole, so every hole has
   a trail entry behind it (D-0072, M7-T11, which replaced the refusal of set domains).
   The only builder of a gapped declared domain is the test helper
   [Domain_helper.of_list] (test/unit/domain_helper.ml, moved out of [lib/] by
   M22-review-T5). Callers cite nothing rather than raising; the comment on
   [Store.remover] in lib/core/trace.ml argues why.

   [before] is EXCLUSIVE. [Trace] and [Linear] once had a copy each, with the two
   off-by-one conventions that invites; this is the one they share. *)
let remover_scan t ~before ~var value =
  let rec go i =
    if i < 0 then None
    else
      let e = t.trail.(i) in
      if Var.equal e.var var && Domain.mem e.old value && not (Domain.mem e.now value)
      then Some e
      else go (i - 1)
  in
  go (Stdlib.min (before - 1) (t.trail_len - 1))

(* [remover_scan]'s answer from [var]'s entry history in O(log entries on [var]) rather
   than O(|trail|) per call. The scan was at the top of 2014_mario's profile once
   [bound_support] had removed the bound one (M6-T14, D-0088). Along that history
   each entry's [old] is its predecessor's [now] and domains only shrink (I-D3), so
   "[value] is gone from [now]" is false then true: the first entry where it turns true
   is the only one that can have removed it, found by binary search; it did iff its [old]
   still held [value] (false only for the first entry, when the declared domain never
   did), and the scan finds it iff it lies strictly below [before]. The scan stays as the
   [BAGUETTE_DEBUG] cross-check and test_core's oracle. *)
let remover t ~before ~var value =
  let i = Var.to_int var in
  let h = t.all_hist.(i) and n = t.all_hn.(i) in
  let lo = ref 0 and hi = ref n in
  while !lo < !hi do
    let mid = (!lo + !hi) lsr 1 in
    if Domain.mem t.trail.(h.(mid)).now value then lo := mid + 1 else hi := mid
  done;
  let r =
    if !lo = n then None
    else
      let at = h.(!lo) in
      let e = t.trail.(at) in
      if at < before && Domain.mem e.old value then Some e else None
  in
  if Debug.enabled then
    Debug.check "M6-T14: remover's history agrees with the trail scan" (fun () ->
        Option.equal ( == ) r (remover_scan t ~before ~var value));
  r

(* The values [Domain.settle] walked a bound over on its way to [cur]: the maximal run of
   holes immediately below (above) it in [old]. It stops at the first value [old] still
   held, which is at or beyond whatever bound was actually pushed, so it never claims more
   than the settle did. Empty when the entry's bound is exactly the bound its explanation
   derives, which is every entry in a model with no disequality. *)
let settled_over_lo old ~cur =
  let rec go v acc =
    if v < Domain.lo old || Domain.mem old v then acc else go (v - 1) (v :: acc)
  in
  go (cur - 1) []

let settled_over_hi old ~cur =
  let rec go v acc =
    if v > Domain.hi old || Domain.mem old v then acc else go (v + 1) (v :: acc)
  in
  go (cur + 1) []

(* Every reason [v]'s current lower bound rests on: the entry that moved it, then one per
   hole that entry's settle walked over, since the bound the trail records rests on those
   holes too (I-X9; M1-T44 was the rejected proof that omitted them). [[]] exactly when
   no entry has moved it.

   O(1) plus one scan per hole settled over, which is zero holes for every bound in a
   model with no disequality. The hole scan is what is left of the old O(n * |trail|):
   it is per *hole*, not per term, and reaching it at all requires a disequality to have
   punched a hole immediately under a bound another propagator then pushed onto. *)
let reasons_under t v ~support ~settled =
  if support = no_support then []
  else
    let e = t.trail.(support) in
    Explanation.Arena.get t.reasons e.why
    :: List.filter_map
         (fun h ->
           Option.map
             (fun (r : entry) -> Explanation.Arena.get t.reasons r.why)
             (remover t ~before:support ~var:v h))
         (settled e)

let lo_reasons t v =
  reasons_under t v ~support:(lo_support t v) ~settled:(fun (e : entry) ->
      settled_over_lo e.old ~cur:(Domain.lo e.now))

let hi_reasons t v =
  reasons_under t v ~support:(hi_support t v) ~settled:(fun (e : entry) ->
      settled_over_hi e.old ~cur:(Domain.hi e.now))

(* ----------------------------------------------- the trail as of a fixed position *)

(* A [history] is the store's trail cut at [upto]: positions [0 .. upto - 1] and nothing
   after. The four lookups below answer, for that cut, exactly what [lo_support],
   [Domain.lo (get t v)], [lo_reasons] and their [hi] twins answer for the live store --
   and when [upto] is the current trail length the answers are the same values, which is
   how a [Linear] pruning's reason can be materialised later from a history taken at the
   push and render what a snapshot taken at the push would have (D-0124, M7-T27 (a)).

   WHY THIS IS A SNAPSHOT AND NOT A LIVE READ, as I-X6 requires of an explanation. The
   trail is a stack: an entry at
   position [p] is popped only by [undo_to], which pops every entry above it first, and a
   popped slot is overwritten with [dummy_entry]. So while the entry pushed at [upto] is
   on the trail, every position below [upto] holds the same physical record it held at
   the push, with the same [old], [now], [sup_lo]/[sup_hi] and the same live arena id.
   Reading those positions later is reading frozen data. What a history must NOT read is
   anything at or above [upto] (the pruning's own entry, and whatever came after), and
   [support_before] walks every support chain back past it before answering.

   WHEN THE HISTORY IS GONE. A reason is asked for by the trace at the branch's failure
   and by conflict analysis at the conflict, both before the backtrack that pops its
   entry; a conflict's reason is read where the conflict is raised. Nothing legitimately
   asks later, and a reader that did would be reading a trail that has been unwound and
   re-pushed with other entries -- the I-X6 failure, as a wrong answer. [check_history]
   turns that into a raise: [h_witness] is the physical entry at [upto - 1] when the
   history was taken, and a trail that has been unwound below [upto] cannot hold it at
   that position again, because every [apply] allocates a fresh record. [upto = 0] is
   the empty history, valid forever. *)
type history = { h_store : t; h_upto : int; h_witness : entry }

let history t =
  {
    h_store = t;
    h_upto = t.trail_len;
    h_witness = (if t.trail_len = 0 then dummy_entry else t.trail.(t.trail_len - 1));
  }

let history_upto h = h.h_upto

(* Names never change, so the history answers them as the store does. *)
let history_name h v = name h.h_store v

let history_live h =
  let t = h.h_store in
  t.trail_len >= h.h_upto && (h.h_upto = 0 || t.trail.(h.h_upto - 1) == h.h_witness)

let check_history h =
  if not (history_live h) then
    invalid_arg
      (Printf.sprintf
         "I-X6 (D-0124): a reason was materialised after the trail it reads was unwound \
          below its pruning (history at %d, trail now %d)"
         h.h_upto h.h_store.trail_len)

(* The newest entry below [upto] on one bound's own chain of moves, starting from its
   current support: [sup_lo]/[sup_hi] on a bound-moving entry is the previous support of
   that bound, so the walk visits only that bound's movers, newest first, and stops at
   the first one the history contains. O(moves of that bound since [upto]). *)
let rec support_before t ~upto ~sup p =
  if p = no_support || p < upto then p else support_before t ~upto ~sup (sup t.trail.(p))

let lo_support_at h v =
  support_before h.h_store ~upto:h.h_upto
    ~sup:(fun e -> e.sup_lo)
    (lo_support h.h_store v)

let hi_support_at h v =
  support_before h.h_store ~upto:h.h_upto
    ~sup:(fun e -> e.sup_hi)
    (hi_support h.h_store v)

(* The domain [v] was created with: the [old] of its oldest entry, or its current domain
   while it has none. Only needed when a bound has no support within the history, i.e.
   it still stood where the store created it.

   Read from [initial], one load where the history took four dependent ones (2 % of 2011
   roster's instructions, whose reasons cite many declared bounds; M16-file-review-T1,
   D-0186). The two agree: only [apply] and [undo_to] write [domains], so before the
   oldest live entry on [v] was pushed nothing live had moved [v], every popped entry
   had restored what it found, and that entry's [old] is the created domain; with no
   live entry the current domain is. [created_domain_by_history] is the old reading,
   kept for the BAGUETTE_DEBUG cross-check and test_core.ml. *)
let created_domain_by_history t v =
  let i = Var.to_int v in
  if t.all_hn.(i) > 0 then t.trail.(t.all_hist.(i).(0)).old else t.domains.(i)

let created_domain t v =
  let d = t.initial.(Var.to_int v) in
  if Debug.enabled && not (Domain.equal d (created_domain_by_history t v)) then
    failwith "invariant violated: D-0186: the created domain is the history's oldest";
  d

let lo_at h v =
  let q = lo_support_at h v in
  if q = no_support then Domain.lo (created_domain h.h_store v)
  else Domain.lo h.h_store.trail.(q).now

let hi_at h v =
  let q = hi_support_at h v in
  if q = no_support then Domain.hi (created_domain h.h_store v)
  else Domain.hi h.h_store.trail.(q).now

let lo_reasons_at h v =
  reasons_under h.h_store v ~support:(lo_support_at h v) ~settled:(fun (e : entry) ->
      settled_over_lo e.old ~cur:(Domain.lo e.now))

let hi_reasons_at h v =
  reasons_under h.h_store v ~support:(hi_support_at h v) ~settled:(fun (e : entry) ->
      settled_over_hi e.old ~cur:(Domain.hi e.now))

(* The three readers an Element FRAME needs beyond the bound ones above, each one call on
   a position below the cut, so none can read past it. A frame is what an Element pruning
   records instead of its reason: the domains it read and the trail cut, from which the
   reason and derivation are built only when asked (D-0214, M20-pernode-T2; the readers
   moved here with M21-memory-T3). [remover_at] is [remover] with
   [~before] at the cut: the first entry on [var] whose [now] lost [v], kept iff it lies
   below the cut, which is the entry the live store named at the push. [explanation_at]
   is the arena explanation of an entry the history holds (its arena slot is live while
   the entry is). [at_root_at] is [at_root] for a position below the cut: the first level
   mark does not move while the cut is live, since a level opened later has its mark at or
   above it. *)
let remover_at h ~var v = remover h.h_store ~before:h.h_upto ~var v
let explanation_at h e = explanation h.h_store e
let at_root_at h pos = at_root h.h_store pos

(* The decision level the entry at trail position [i] belongs to: the number of open
   level marks at or below it. Position [marks.(k)] is exactly the FIRST entry of level
   [k+1], which for a level opened by [Search.branch] is the decision push itself. The
   count is a binary search for the first [k] whose mark is past [i], because the marks
   are monotone (I-T2). It was a walk over every open level, once per trail entry
   conflict analysis reads, until the per-node cost pass on the XOR-heavy codes models
   (M6-T22, D-0138). *)
let first_mark_above t i =
  let rec go lo hi =
    if lo >= hi then lo
    else
      let mid = (lo + hi) lsr 1 in
      if t.marks.(mid).trail_mark <= i then go (mid + 1) hi else go lo mid
  in
  go 0 t.n_levels

let level_of_index t i = first_mark_above t i

(* True when [i] is the first entry of some open level, i.e. the push that opened it.
   [Trace] skips these: a decision is not implied by the model and has no trace line.
   The marks at or below [i] are exactly the first [level_of_index t i], so [i] is a
   level start iff the last of them equals it, which (the marks being monotone, I-T2) is
   iff SOME open mark sits at [i]. That last form is what [t.starts] counts, so the
   answer is one load. [Search.decision_entries] asks it for every trail entry at every
   conflict, where the binary search was 8 % of mspsp's instructions at 10 000 nodes
   (item S3 of D-0140, fixed by M11-complexity-T3, D-0142). [is_level_start_by_marks] is
   the binary-search definition, kept as the specification test_core.ml checks the count
   against. *)
let is_level_start_by_marks t i =
  let k = first_mark_above t i in
  k > 0 && t.marks.(k - 1).trail_mark = i

let is_level_start t i = i >= 0 && i < Array.length t.starts && t.starts.(i) > 0

(* Debug-mode check of the trail invariants. Cheap enough to call after a backtrack in
   tests; linear in the trail, so not something the engine should call per propagation. *)
let check_invariants t =
  (* I-T2: level marks are monotone and within the trail. *)
  let rec monotone prev = function
    | [] -> true
    | m :: rest -> m >= prev && m <= t.trail_len && monotone m rest
  in
  let ok_marks = monotone 0 (level_marks t) in
  (* I-T3: every live trail entry's explanation index resolves. *)
  let ok_reasons = ref true in
  for i = 0 to t.trail_len - 1 do
    if not (Explanation.Arena.mem t.reasons t.trail.(i).why) then ok_reasons := false
  done;
  (* I-D1: no stored domain is empty. *)
  let ok_domains = Array.for_all (fun d -> Domain.lo d <= Domain.hi d) t.domains in
  (* Every bound support names a live entry for that variable which moved that bound to
     where it now sits. This is the property [lo_support]'s equivalence with the
     scan it replaced rests on, so it is asserted rather than argued: an array that drifts
     from the trail makes every citation name the wrong derivation, and a wrong citation
     is a proof step about a bound nobody derived. *)
  let ok_support = ref true in
  Array.iteri
    (fun i sup ->
      if sup <> no_support then
        if sup < 0 || sup >= t.trail_len then ok_support := false
        else
          let e = t.trail.(sup) in
          if
            Var.to_int e.var <> i
            || Domain.lo e.old >= Domain.lo e.now
            || Domain.lo e.now <> Domain.lo t.domains.(i)
          then ok_support := false)
    t.lo_sup;
  Array.iteri
    (fun i sup ->
      if sup <> no_support then
        if sup < 0 || sup >= t.trail_len then ok_support := false
        else
          let e = t.trail.(sup) in
          if
            Var.to_int e.var <> i
            || Domain.hi e.old <= Domain.hi e.now
            || Domain.hi e.now <> Domain.hi t.domains.(i)
          then ok_support := false)
    t.hi_sup;
  (* Each history is sorted, names live entries on its variable that moved its bound, and
     its top is the O(1) array's answer -- the property that makes [bound_support] and
     [lo_support] two readings of one chain. *)
  let ok_hist = ref true in
  let hist_ok h hn sup moved =
    Array.iteri
      (fun i n ->
        let top = if n = 0 then no_support else h.(i).(n - 1) in
        if top <> sup.(i) then ok_hist := false;
        for j = 0 to n - 1 do
          let at = h.(i).(j) in
          if at < 0 || at >= t.trail_len || (j > 0 && at <= h.(i).(j - 1)) then
            ok_hist := false
          else
            let e = t.trail.(at) in
            if Var.to_int e.var <> i || not (moved e) then ok_hist := false
        done)
      hn
  in
  hist_ok t.lo_hist t.lo_hn t.lo_sup (fun e -> Domain.lo e.now > Domain.lo e.old);
  hist_ok t.hi_hist t.hi_hn t.hi_sup (fun e -> Domain.hi e.now < Domain.hi e.old);
  (* and the entry history holds exactly the live entries, each under its own variable *)
  let total = ref 0 in
  Array.iteri
    (fun i n ->
      total := !total + n;
      for j = 0 to n - 1 do
        let at = t.all_hist.(i).(j) in
        if
          at < 0 || at >= t.trail_len
          || (j > 0 && at <= t.all_hist.(i).(j - 1))
          || Var.to_int t.trail.(at).var <> i
        then ok_hist := false
      done)
    t.all_hn;
  if !total <> t.trail_len then ok_hist := false;
  ok_marks && !ok_reasons && ok_domains && !ok_support && !ok_hist

let to_string t =
  String.concat " "
    (Array.to_list
       (Array.mapi
          (fun i d -> Printf.sprintf "%s=%s" t.names.(i) (Domain.to_string d))
          t.domains))
