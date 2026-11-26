(* clause: a disjunction over ORDER LITERALS,

     [x_1 >= k_1] \/ ... \/ [x_p >= k_p] \/ [y_1 <= m_1] \/ ... \/ [y_q <= m_q]

   and therefore, at threshold 1 over `var bool`s, the Boolean clause family this file
   used to be called `bool_clause` for: the `bool_clause` builtin itself and, through
   lib/flatzinc/compile.ml's decomposition, `array_bool_or`, `array_bool_and`, `bool_eq`
   and `bool_not`. The submodules at the bottom are that same propagator under the name
   of the builtin an instance came from, exactly as [Ne.Int_ne] is [Ne] under another
   name -- an instance reports the builtin the model actually wrote, which is what a
   trace or a failure message has to say to be worth reading.

   ---------------------------------------------------------------------------
   M2-L12 / D-0052: this is a WIDENING, and the widening is why the file moved
   ---------------------------------------------------------------------------

   D-0052 decided that a clause over order literals is a widening of `bool_clause` and
   not a new propagator family, and the decision rests on three checkable facts:
   [Explanation.Clause] is already [Lit.t list] rather than a list of Booleans,
   [Justify.validate_lits] checks only that a literal's owner is a declared variable, and
   every Boolean-specific site in this file was a CONSTANT SUBSTITUTION -- the threshold
   1 -- rather than a structural assumption. [Lit.bool_true] / [Lit.bool_false] are
   literally [Lit.ge x 1] / [Lit.le x 0].

   So the threshold [k] is now a field of [lit] instead of the constant 1, [status],
   [assign] and [falsity_fact] read it, and everything else is unchanged. M2-L12 needs
   this because a 1UIP learned clause over integer variables is exactly such a clause and
   nothing propagated it (lib/core/learn.ml's header: the backjump "would re-reach the
   same fixpoint, re-take the same decision and re-derive the same conflict").

   WHAT D-0052 EXPLICITLY REFUSED, and this module honours both:

     - **no watched literals.** [survey] below is still a full walk with early exit. No
       propagator in lib/core/prop/ has a single [mutable] field, and watch pointers
       would be the first search-dependent mutable propagator state outside [Store]'s
       undo trail. Max observed learned-clause width on this suite is 4 (M2-L12 step 0,
       measured: 72 clauses of width 1, 5 of width 2, 8 of width 3, 3 of width 4).
     - **no second implementation.** The submodules below share [t], [make], [vars] and
       [propagate] outright, which is what the pre-M2-L12 version of this comment
       already refused to give up for [Array_bool_or].

   ---------------------------------------------------------------------------
   Consistency level: BOUNDS here, DOMAIN in the [Bool_clause] submodule
   ---------------------------------------------------------------------------

   This is the real cost of the widening and D-0052 names it as the honest
   counter-argument to its own verdict. The pre-M2-L12 header declared DOMAIN and spent
   nine lines making the argument: for a clause, unit propagation *is* domain
   consistency, because **Booleans have no interior**, so every value of every variable
   has a support while two literals are open.

   **Order literals over integers do have an interior.** `x <= 1 \/ x >= 3` over
   `x in 0..5` is a HOLE at 2, not a tautology. Unit propagation moves bounds; it does
   not punch the hole. So the declared level here is BOUNDS (docs/SPEC.md 3.2), and
   SPEC 3.2 makes the declared level the bound on what an explanation may claim.

   Chasing the hole would need [Store.remove_with_facts], of which I-X10 records [Ne] is
   the sole caller in lib/, and would trip D-0019 point 3. D-0052 says do not, and this
   module does not.

   **[Bool_clause] below still declares DOMAIN, and that declaration is still true**:
   its [make] rejects any variable not declared over [0, 1] (D-0007), a [0, 1] variable
   has no interior, and the nine-line argument survives verbatim on that restriction.
   That is the [Ne] / [Ne.Int_ne] pattern this file already used -- one implementation,
   two honest declarations, the narrower one earned by a checked precondition.

   ---------------------------------------------------------------------------
   The opposite-direction pair: a HOLE, not a tautology
   ---------------------------------------------------------------------------

   [make] drops exact duplicate literals but leaves a variable occurring at both
   polarities alone. That is unchanged, and the CODE was already right; the RATIONALE
   was wrong for order literals and is rewritten here rather than left to mislead.

   The old text said such a clause "is a tautology, the propagator correctly never
   fires". For `b \/ ~b` that is true. For `x >= 3 \/ x <= 1` it is false twice over, and
   the ordinary path gets both cases right without a special case:

     - `x` narrowed to [2, 2]: both literals are [Unsat_lit], the survey returns
       [Units []], and the propagator CONFLICTS. A tautology assumption would have
       missed a real violation.
     - `x` narrowed to [2, 5]: `x <= 1` is [Unsat_lit] and `x >= 3` is [Open], so the
       survey returns that one literal and the propagator moves `lo` to 3 -- a pruning no
       tautology ever licenses.

   D-0052 measured that at least 9 learned clauses of width >= 3 carry such a pair, so it
   is real traffic rather than an edge case. [Learn.minimise]'s [slot] keys on
   (variable, polarity), so opposite-direction pairs survive minimisation by design.

   ---------------------------------------------------------------------------
   Shape and the two structural differences from [Linear]
   ---------------------------------------------------------------------------

   This follows lib/core/prop/linear.ml, the reference propagator -- one pass,
   [consistency] declared, the explanation built from data frozen at [make] time. The two
   structural differences are deliberate and are the same two lib/core/prop/ne.ml makes,
   for the same reason:

     - it cites no row id, because its justification is a [rup] whose target states its
       own content in full. D-0011's hazard was [Explanation.Trivial] ("whatever
       ctx.model_id points at", unresolvable once it is on the trail with no propagator
       identity attached). **It no longer exists** (M1-T31/M1-T50, D-0037): the ambient
       row is unrepresentable now, not merely unused. Nothing here ever built [Trivial]
       or [Model_row], so there is nothing to route and [make] takes no [?row_id]. An
       unused id parameter would be an invitation to believe it was load-bearing.

     - nothing is [Deferred]. [Linear] and [Ne] defer because their reasons are a
       function of the *store* at the moment of the pruning, so they must snapshot, and
       snapshotting is what costs. A clause's reason is the clause: a function of the
       constraint alone, identical for every pruning and every conflict this instance
       will ever report, and therefore computed once in [make] and shared.
       docs/ARCHITECTURE.md's "lazy where it is expensive" cuts the other way here --
       there is nothing to be lazy about, and I-X6's snapshot discipline is satisfied
       vacuously by a value that does not depend on the store at all.

   Sharing the one [Explanation.t] has a second, useful consequence: lib/core/justify.ml
   memoises on *physical* identity, so every pruning of one clause inside one decision
   level emits the clause once and cites that id again afterwards.

   ---------------------------------------------------------------------------
   Justification -- one [rup], which is the clause restated
   ---------------------------------------------------------------------------

   docs/PROOF-FORMAT.md section 4 nominates [rup] for `bool_clause`, and D-0019 is why
   that is not a weakness: a `rup` target is a *clause*, and this constraint IS a clause
   over order-encoding literals. D-0007 fixes the Boolean spelling -- a `var bool` is the
   order encoding on [0, 1], so "b is true" is [b_ge_1] ([Lit.bool_true]) and "b is
   false" is [~b_ge_1] ([Lit.bool_false]). There is no second naming scheme and no direct
   encoding anywhere in this module; by D-0019 point 3's test, none is forced, because no
   reason here ever has to mention a hole. [of_lits] REFUSES a [Lit.Eq] literal outright
   for that reason -- see its comment.

   Every explanation this module builds -- pruning and conflict alike -- is the same
   clause, namely the constraint itself. For a *conflict* every literal is false and the
   clause says so. For a *pruning* of the last open literal it is D-0018's trace-line
   shape read the other way round: the claim (the literal being made true) disjoined with
   the negation of the facts the propagator read (the other literals, each false). Those
   are literally the same list, which is not a coincidence -- the reason a literal is
   forced is that the assignment which falsifies it is the assignment that conflicts.
   [Ne]'s header records the identical observation about a disequality.

   Three properties of that clause, each of which a later change could quietly break:

   1. It is *globally valid*: it is the constraint, not a consequence of the current
      decisions. So it is sound at any proof level and never needs guarding or wiping.

      **M2-L12 qualifies this for a LEARNED instance and the qualification is the whole
      of step 3.** A clause from a model row is on the page for the whole run. A LEARNED
      clause is on the page only while lib/core/retention.ml holds it, so a [rup] citing
      it is RUP only while that constraint is live. Whoever registers a learned instance
      must [Retention.cite] its id; [Search.register_learned] does, and D-0051's
      "what would reverse this" section is the other half of the link.

   2. It is *reverse unit propagation in one step* against the row that states it -- the
      model row lib/flatzinc/compile.ml posts, or the learned constraint
      [Learned.introduce] put on the page. Negating the target falsifies that row
      outright, so the checker does no searching at all. This is the one case where
      PROOF-FORMAT section 2's "prefer pol over rup" costs nothing: the [pol] would be
      `pol <row>`, a restatement, and D-0009 records what restating a row as a
      justification did to this project once already.

   3. It contains no direct-encoding literal, so it depends on nothing introduced by
      [red] and leaves nothing for the I-X2 audit to retire.

   The empty clause is a real value here and is handled by no special case. It arises
   when every literal folded away against a constant (`bool_clause([], [])`, or a clause
   all of whose operands are parameters with the wrong truth value), and the propagator
   conflicts immediately with [Explanation.clause []], which renders as `rup >= 1 ;` and
   is closed the D-0022/I-X7 way because it rests on a clause. That is the same route
   `int_ne(x, x)` takes in test/models/ne_self_unsat.fzn.

   COST (M16-file-review-T2, D-0190). A run is [Pb.quiet]'s walk to the second non-false
   literal, O(position of that literal), and a pass over the row when it is not quiet. A
   learned clause's advisor ([Learned_clause.ask]) is asked once per wake of every clause
   watching the moved variable, so it reads only its own record and the domain: each
   watch's variable, threshold and polarity are kept there flat by [set_watches], the one
   writer of [w1] and [w2]. *)

module Lit = Baguette_proof.Lit

(* ---------------------------------------------------------------------------
   M2-L13 / D-0054: there is now ONE implementation, and it is [Pb]
   ---------------------------------------------------------------------------

   D-0044 fixed the learned object as a PB inequality with the CLAUSE as its degree-1,
   unit-coefficient case. Until M2-L13 that was a claim about types made in prose; this
   module now *is* that case. [t] is [Pb.t], [make] and [of_lits] build one with every
   coefficient 1 and degree 1, and [propagate] is [Pb.propagate] with no wrapper.

   lib/core/prop/pb.ml's header works the four arms of the old [survey] -- [Satisfied],
   [Two_open], [Units [l]], [Units []] -- out of the slack rule and shows each falls out
   rather than being special-cased, and its [reason_clause] is where the explanations
   are shown to coincide: for a degree-1 row the literals a step names are always the
   WHOLE constraint, in term order, so the [Explanation.t] is the same value -- the
   shared one, which keeps lib/core/justify.ml's memoisation on physical identity firing
   exactly as this module's header claims below.

   Everything the pre-M2-L13 version of this file said about the SHAPE of a clause is
   still true and still above; what is gone is the second copy of the propagation loop.
   The old header already refused "a second implementation to keep in step" for
   [Array_bool_or]; keeping one for the degree-1 PB row would have been the same refusal
   ignored. *)

type t = Pb.t

let name = "clause"

(* BOUNDS, not DOMAIN. The header's "Consistency level" section is the argument, and
   [Bool_clause.consistency] below is the restriction on which DOMAIN is still true.
   [Pb.consistency] is the same value and for the same reason. *)
let consistency = Pb.consistency

(* Drop exact duplicates -- the same variable at the same polarity and the same threshold
   twice -- because two occurrences of one literal would read below as two unassigned
   literals and the propagator would then decline to infer anything. That is sound but
   strictly weaker, and there is no reason to accept it when the merge is this cheap.

   Note this is NOT [Learned.make]'s merge, which would sum the coefficients to 2 and
   leave the degree at 1. `2l >= 1` and `l >= 1` force the same thing over 0-1, so
   either would be correct; deduping keeps the clause a clause, which is what
   [literals] and [width] are asked about.

   A variable occurring at both polarities, or at one polarity with two different
   thresholds, is LEFT ALONE. See the header's "opposite-direction pair" section: the
   ordinary path is right for both, and for order literals the old tautology rationale
   is simply false. (Same-direction pairs subsume one another along the ladder;
   [Learn.minimise] already performs that reduction on a learned clause before it gets
   here, and doing it a second time here would duplicate its policy argument.) *)
let dedup (ls : Pb.atom list) : Pb.atom list =
  let seen = Hashtbl.create 16 in
  List.filter
    (fun (a : Pb.atom) ->
      let key = (Var.to_int a.Pb.x, a.Pb.positive, a.Pb.k) in
      if Hashtbl.mem seen key then false
      else (
        Hashtbl.add seen key ();
        true))
    ls

let finish atoms = Pb.of_atoms (dedup atoms)

(* --------------------------------------------------------------- the Boolean entry

   [raw] is (variable, polarity) pairs, i.e. the shape lib/flatzinc/compile.ml has.

   Reads each variable's domain out of the store, so it must be called before anything
   has narrowed it -- the same requirement, for the same D-0010 reason, that
   [Linear.make] and [Ne.make] state. Here it is a check rather than a freeze: a
   `bool_clause` literal must be a `var bool`, i.e. the order encoding on [0, 1]
   (D-0007), and [Bool_clause.consistency]'s DOMAIN declaration rests on exactly that.
   lib/flatzinc/compile.ml rejects a non-Boolean argument with a positioned diagnostic
   before ever reaching here; this is the backstop for a caller built by hand, which is
   what every unit test is. *)
let make store raw =
  finish
    (List.map
       (fun (x, positive) ->
         let d = Store.get store x in
         if Domain.lo d <> 0 || Domain.hi d <> 1 then
           invalid_arg
             (Printf.sprintf
                "Clause.make: `%s` is declared over %s, but a `bool_clause` literal must \
                 be a `var bool`, i.e. the order encoding on [0, 1] (docs/DECISIONS.md \
                 D-0007). For a clause over general order literals use [Clause.of_lits], \
                 which declares BOUNDS (D-0052)."
                (Store.name store x) (Domain.to_string d));
         {
           Pb.x;
           Pb.name = Store.name store x;
           Pb.positive;
           Pb.k = 1;
           Pb.decl_lo = 0;
           Pb.decl_hi = 1;
         })
       raw)

(* --------------------------------------------------------------- the general entry

   Build a clause from proof literals -- the shape a LEARNED clause has
   ([Explanation.Clause] and [Learn.lits] are both [Lit.t list]).

   [decl] is the variable's DECLARED bounds, read from the encoding rather than from the
   store: see [Pb.atom]'s comment. [None] from it, or a name the store does not know,
   means this engine cannot instantiate the clause, and the honest answer is to decline
   rather than to guess a box. [None] is also the answer for a [Lit.Eq] literal, and
   [Pb.atom_of] is where both refusals live now, with the reason. A 1UIP cut can contain
   such a literal (lib/core/learn.ml's [slot] returns [None] for one), so declining is a
   case that really arises and is counted, not a defensive arm. *)
let of_lits store ~(decl : string -> (int * int) option) (ls : Lit.t list) : t option =
  let rec go acc = function
    | [] -> Some (finish (List.rev acc))
    | l :: rest -> (
        match Pb.atom_of store ~decl l with None -> None | Some a -> go (a :: acc) rest)
  in
  go [] ls

let vars = Pb.vars

(* The clause, for callers that want to see what was built. *)
let literals = Pb.literals
let width = Pb.width

(* ------------------------------------------------------------------- propagation

   [Pb.propagate], unwrapped. The header says why there is no second copy, and
   lib/core/prop/pb.ml's own header derives the four arms this used to spell out. Its
   degree-1 shortcut (M6-T22, [Pb.quiet]) is therefore this module's too. *)
let propagate = Pb.propagate
(* ---------------------------------------------------------------------------
   The Boolean face, and the same propagator under the name of the builtin that
   produced the clause.

   lib/flatzinc/compile.ml decomposes `array_bool_or`, `array_bool_and`, `bool_eq` and
   `bool_not` into clauses -- one row and one instance per clause, which is D-0027 point
   3's default ("where a constraint's rows propagate independently and the engine's
   fixpoint reproduces the fused loop, post one instance per row") and loses nothing:
   unit propagation over the clauses of a reified or/and is domain consistent for the
   whole constraint, which is the same thing a hand-written [Array_bool_or] would achieve
   with more code and a second reason shape to get right.

   These exist so the packed instance reports the builtin the model wrote, the way
   [Ne.Int_ne] does, and -- since M2-L12 -- so that a clause built by [make] keeps the
   DOMAIN declaration its [0, 1] restriction earns. They share [t], [make], [vars] and
   [propagate] outright; there is deliberately nothing else in them, because anything
   else would be a second implementation to keep in step. *)

(* DOMAIN, and it is still true: [make] rejects any variable not declared over [0, 1], a
   [0, 1] variable has no interior, and for a clause over such variables unit propagation
   *is* domain consistency rather than an approximation of it -- while two literals are
   unassigned every value of every variable has a support (set some other open literal
   true), and when exactly one is unassigned its falsifying value has none. So there is
   no stronger propagator for a Boolean clause and nothing is left on the table.

   This is the [Ne] / [Ne.Int_ne] pattern: one implementation, and the narrower face
   declares the stronger level because a checked precondition earns it. An instance built
   by [of_lits] does NOT go through here and gets the module's own BOUNDS. *)
let bool_consistency = Propagator.Domain

module Bool_clause = struct
  type nonrec t = t

  let name = "bool_clause"
  let consistency = bool_consistency
  let vars = vars
  let propagate = propagate
end

module Array_bool_or = struct
  type nonrec t = t

  let name = "array_bool_or"
  let consistency = bool_consistency
  let vars = vars
  let propagate = propagate
end

module Array_bool_and = struct
  type nonrec t = t

  let name = "array_bool_and"
  let consistency = bool_consistency
  let vars = vars
  let propagate = propagate
end

module Bool_eq = struct
  type nonrec t = t

  let name = "bool_eq"
  let consistency = bool_consistency
  let vars = vars
  let propagate = propagate
end

module Bool_not = struct
  type nonrec t = t

  let name = "bool_not"
  let consistency = bool_consistency
  let vars = vars
  let propagate = propagate
end

(* The learned face: a clause over general order literals, registered mid-search by
   lib/core/search.ml. Named apart from [name] above so that a trace, a fallback reason
   or an attribution failure says WHICH clause -- a model row's or one this search
   derived -- which is exactly the distinction [Retention]'s citation guard is about. *)
module Learned_clause = struct
  (* M6-T20 / D-0104: the clause plus TWO WATCHED LITERALS, the first mutable propagator
     state in lib/core/prop/ and the one kind I-P7 admits. [w1] and [w2] index [atoms];
     after a run both are non-false unless the clause was unit or failed, and a widening
     domain cannot falsify a literal, so backtracking never has to restore them.

     M11-complexity-T17 (D-0173): RESTING, with [rest_satisfied]. [rest] is the index of a
     watched literal found TRUE by a run, or [-1]. THE RULE: a run that finds one of its two
     watched literals true does nothing, MOVES NEITHER WATCH, and reports that it rests on
     that literal ([watched] answers [(w, Propagator.rests)]); while it rests its advisor
     declines every change; the engine indexes it under that literal alone and seeds it
     again after a backtrack that pops the bound holding the literal up ([Engine.rest_on]);
     that run finds the literal still true and rests again, or goes back to the two watches
     it left. WHY IT LOSES NO PRUNING: a clause with a true literal cannot prune or fail
     whatever else changes, so declining is I-P7 read literally; and the two watches it
     left are good again once released, because the other watch was non-false or falsified
     at a level at or above the true one's (the classic argument for MiniSat's satisfied
     clauses, spelled out at [Engine.rest_on]). WHY: on codes-cp's QR48 every one of the 177
     learned-clause runs per node was a run of a satisfied clause moving its false watch,
     and the asks that woke it cost more than the runs (D-0173 section 2). WHAT IT CHANGES:
     not the fixpoint of any node, but the watch a satisfied clause holds after a backtrack,
     so a later pruning by it can be woken at another trail entry and land at another place
     in the propagation order (D-0173 section 3). OFF by default in [make]; [Search] passes
     its [config.rest_satisfied]. *)
  (* M16-file-review-T2 (D-0190): each watch's literal is ALSO kept flat in the record, its
     variable as an int ([x1]/[x2], [-1] for no literal), its threshold and its polarity,
     because [ask] reads nothing else and is asked once per wake of every clause watching
     the moved variable (27 % of 2013 rcpsp_11's samples were [ask] itself, a chain of
     four dependent loads: the record, [atoms], the atom, the domain). They are a COPY of
     term [w1]'s and term [w2]'s fields of [pb], written only by [set_watches], which is
     the one place [w1] and [w2] are written; a test that places the watches by hand
     calls it too. Since D-0226 there is no atom array: [pb]'s own flat arrays are read
     by index. *)
  type nonrec t = {
    pb : Pb.t;
    mutable w1 : int;
    mutable w2 : int;
    mutable x1 : int;
    mutable k1 : int;
    mutable p1 : bool;
    mutable x2 : int;
    mutable k2 : int;
    mutable p2 : bool;
    rest_satisfied : bool;
    mutable rest : int;
  }

  (* Place the two watches at [w1] and [w2], with their flat copies (the record's header);
     a watch that does not move keeps the copy it has. An index outside [atoms] (the [-1]
     [rewatch]'s [best] answers for a one-literal clause with its literal false) gets
     [x = -1], which no variable is. *)
  let set_watches t w1 w2 =
    let n = Pb.width t.pb in
    if w1 <> t.w1 then (
      t.w1 <- w1;
      if w1 >= 0 && w1 < n then (
        t.x1 <- Var.to_int (Pb.var_at t.pb w1);
        t.k1 <- Pb.k_at t.pb w1;
        t.p1 <- Pb.positive_at t.pb w1)
      else t.x1 <- -1);
    if w2 <> t.w2 then (
      t.w2 <- w2;
      if w2 >= 0 && w2 < n then (
        t.x2 <- Var.to_int (Pb.var_at t.pb w2);
        t.k2 <- Pb.k_at t.pb w2;
        t.p2 <- Pb.positive_at t.pb w2)
      else t.x2 <- -1)

  let name = "learned_clause"
  let consistency = consistency
  let vars t = vars t.pb
  let false_at store t i = Pb.falsified_at store t.pb i

  (* The trail position of the entry that FALSIFIED literal [i], which must be false:
     a positive atom `x >= k` became false when [hi x] first moved below [k], a
     negative one when [lo x] first reached [k]. [Store.no_support] (-1) for a literal
     false by declaration, which no backtrack ever un-falsifies. NOT [Store.hi_support]:
     see [Store.hi_below] for why the support of the current bound is a later position
     than the crossing, and how that difference broke the first draft. *)
  let falsified_at store t i =
    let x = Pb.var_at t.pb i and k = Pb.k_at t.pb i in
    if Pb.positive_at t.pb i then Store.hi_below store x k
    else Store.lo_at_least store x k

  (* Two watches, chosen so that I-P7 holds through every backtrack:

       - with two or more non-false literals, two of them (a current watch that still
         qualifies is kept);
       - with exactly one, it and the LATEST-falsified other literal;
       - with none (the run failed), the two latest-falsified literals.

     The second and third cases are the classic argument. Backtracking un-falsifies
     literals in reverse trail order, so the latest-falsified watch is non-false again
     no later than any other false literal: whenever the clause has two non-false
     literals both watches are among them, and whenever it has one that one is a watch.
     A change that falsifies an unwatched literal therefore never makes the clause unit
     or failed, which is exactly what [advise] answers [false] to. Two drafts got this
     wrong and the BAGUETTE_DEBUG check of I-P7 caught both, on `colour_unsat` and five
     more models and on test_random's random branching orders: the first kept whatever
     stale false index it had, the second ranked by [Store.hi_support], the current
     bound's support rather than the crossing ([falsified_at]). Either way a watch that
     was falsified EARLIER than an unwatched literal is un-falsified after it, and the
     clause goes unit unwatched. *)
  let rewatch store t =
    let n = Pb.width t.pb in
    let best ~not_ =
      (* Any non-false literal other than [not_]; failing that, the latest-falsified.
         Ranks are computed only when every candidate is false. *)
      let r = ref (-1) in
      for j = 0 to n - 1 do
        if j <> not_ && !r < 0 && not (false_at store t j) then r := j
      done;
      (if !r < 0 then
         let rk = ref min_int in
         for j = 0 to n - 1 do
           if j <> not_ then
             let k = falsified_at store t j in
             if k > !rk then (
               r := j;
               rk := k)
         done);
      !r
    in
    let keep i = i >= 0 && i < n && not (false_at store t i) in
    let w1 = if keep t.w1 then t.w1 else best ~not_:t.w2 in
    let w2 = if keep t.w2 && t.w2 <> w1 then t.w2 else best ~not_:w1 in
    set_watches t w1 (if w2 >= 0 then w2 else w1)

  (* THE PRECONDITION of the two watches (D-0142 section 5): at most one literal per
     (variable, polarity). Two rungs of one variable in one direction, `x >= 3 \/ x >= 5`,
     can propagate with both of them non-false -- [Pb.pass]'s ladder-effective rule forces
     `x >= 3` once every other literal is false -- so watching those two would let a
     change of an unwatched variable make the clause unit unasked. Opposite polarities on
     one variable are fine: BOUNDS cannot punch the hole between them, so a run with both
     open does nothing. [Learn.minimise] merges every same-slot pair of the 1UIP clause, and
     that clause is the only one [Search] registers here; checked under BAGUETTE_DEBUG. *)
  let one_per_slot (pb : Pb.t) =
    let n = Pb.width pb in
    let ok = ref true in
    for i = 0 to n - 1 do
      for j = i + 1 to n - 1 do
        if
          Var.to_int (Pb.var_at pb i) = Var.to_int (Pb.var_at pb j)
          && Pb.positive_at pb i = Pb.positive_at pb j
        then ok := false
      done
    done;
    !ok

  let make ?(rest_satisfied = false) (pb : Pb.t) =
    let n = Pb.width pb in
    Debug.check "Learned_clause: one literal per (variable, polarity) (D-0142 section 5)"
      (fun () -> one_per_slot pb);
    let t =
      {
        pb;
        w1 = -1;
        w2 = -1;
        x1 = -1;
        k1 = 0;
        p1 = false;
        x2 = -1;
        k2 = 0;
        p2 = false;
        rest_satisfied;
        rest = -1;
      }
    in
    set_watches t 0 (if n > 1 then 1 else 0);
    t

  let true_at store t i = Pb.holds_at store t.pb i

  (* I-P7: queue only when a WATCHED literal on [v] has just become false. Written
     without a local closure (M6-T22): this is asked once per wake, and the closure the
     first version built per call was an allocation on the engine's hottest loop. A
     RESTING clause declines (M11-complexity-T17): it is satisfied, or a backtrack has
     released it and the engine seeds it anyway.
     M16-file-review-T2 (D-0190): from the watches' flat copies ([set_watches]), which is
     [false_at store t t.w1] on the same domain: [x1] is [atoms.(w1)]'s variable, which is
     [v], and the test is [Pb.falsified]'s on [k1] and [p1]. *)
  let watch_false store v positive k =
    let d = Store.get store v in
    if positive then d.Domain.hi < k else d.Domain.lo >= k

  let ask t store v =
    let x = Var.to_int v in
    t.rest < 0
    && ((t.x1 = x && watch_false store v t.p1 t.k1)
       || (t.x2 = x && watch_false store v t.p2 t.k2))

  (* M6-T22 / D-0138: the variables of the two watches. [ask] answers [false] for every
     other variable whatever the store holds, which is [Propagator.inst_watched]'s
     contract, so the engine may wake this clause from these two variables only.

     M11-complexity-T3 (D-0142, E1): with the move that can falsify each. `x >= k` is
     false once [hi x < k], so only an UPPER-bound move falsifies it; `x <= k - 1` only a
     LOWER-bound move. That is [Propagator.watch_hi]/[watch_lo]'s whole claim, and it is
     true of every order literal. *)
  let watch_of t i =
    if Pb.positive_at t.pb i then Propagator.watch_hi (Pb.var_at t.pb i)
    else Propagator.watch_lo (Pb.var_at t.pb i)

  let watched t () =
    if t.rest >= 0 then (watch_of t t.rest, Propagator.rests)
    else (watch_of t t.w1, watch_of t t.w2)

  (* The advisor [Propagator.pack] takes: both halves of one object. Each a closure of
     its own arity over [t] (M16-file-review-T2, D-0190): [ask t], a partial application,
     made every ask go through OCaml's currying stub before reaching [ask]. *)
  let advise t =
    {
      Propagator.ask = (fun store v -> ask t store v);
      watched = Some (fun () -> watched t ());
    }

  (* [rewatch] after a run [Pb.quiet] answered (M11-complexity-T3, D-0142, E2 (a)), from
     what its walk found instead of a walk of its own. The store has not moved since
     [quiet] (a quiet run prunes nothing), and [quiet] answered [true], so [scan.f1] and
     [scan.f2] are the first two non-false literals. [best ~not_] is then "the first
     non-false literal other than [not_]", which is [f1] unless [not_] is [f1] and then
     [f2], and its latest-falsified arm is never reached. [keep] is [rewatch]'s own test.
     So the two watches are the ones [rewatch] would choose, by its own definition. *)
  let rewatch_quiet store t (s : Pb.scan) =
    let n = Pb.width t.pb in
    let best ~not_ = if s.Pb.f1 <> not_ then s.Pb.f1 else s.Pb.f2 in
    let keep i = i >= 0 && i < n && not (false_at store t i) in
    let w1 = if keep t.w1 then t.w1 else best ~not_:t.w2 in
    let w2 = if keep t.w2 && t.w2 <> w1 then t.w2 else best ~not_:w1 in
    set_watches t w1 w2

  (* M6-T22 / D-0138: nearly every run of a learned clause is a watched literal falsified
     with another literal still free -- the run a two-watched-literal solver answers by
     moving the watch. [Pb.quiet] answers it with one walk, and the watch then moves on
     the same store, so the watches -- and every later wake -- are what they were.

     M11-complexity-T3 (D-0142, E2 (a)): that walk is now the only one. [Pb.quiet] leaves
     the first two non-false literals in [t.pb]'s scan and [rewatch_quiet] reads them,
     where the run used to walk the clause again in [rewatch]'s [best], once per watch to
     replace. A run [quiet] does not answer is [Pb.pass] -- exactly what [Pb.propagate]
     does then -- followed by the full [rewatch], because that run may have moved the
     store. *)
  (* RESTING first ([t]'s header): a resting clause whose literal still holds stays as it
     is; one whose literal no longer does (a backtrack released it) goes back to its two
     watches and is run as any other. *)
  let rec propagate t store =
    if t.rest >= 0 then
      if true_at store t t.rest then Propagator.Fixpoint
      else (
        t.rest <- -1;
        propagate t store)
    else if t.rest_satisfied && (true_at store t t.w1 || true_at store t t.w2) then (
      t.rest <- (if true_at store t t.w1 then t.w1 else t.w2);
      Propagator.Fixpoint)
    else if Pb.quiet store t.pb then (
      rewatch_quiet store t t.pb.Pb.scan;
      Propagator.Fixpoint)
    else
      let r = Pb.pass t.pb store in
      rewatch store t;
      r
end
