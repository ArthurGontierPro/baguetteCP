(* clause: a disjunction over ORDER LITERALS,

     [x_1 >= k_1] \/ ... \/ [x_p >= k_p] \/ [y_1 <= m_1] \/ ... \/ [y_q <= m_q]

   and therefore, at threshold 1 over `var bool`s, the Boolean clause family this file
   used to be called `bool_clause` for: the `bool_clause` builtin itself and, through
   lib/flatzinc/compile.ml's decomposition, `array_bool_or`, `array_bool_and`, `bool_eq`
   and `bool_not`. The submodules at the bottom are that same propagator under the name
   of the builtin an instance came from, exactly as [Ne.Int_ne] is [Ne] under another
   name, so that an instance reports the builtin the model actually wrote, which is what
   a trace or a failure message has to say to be worth reading. [Learned_clause] is the
   face a learned clause is registered under.

   Consistency level: BOUNDS ([consistency] below) for a clause over general order
   literals, DOMAIN ([bool_consistency]) for the Boolean faces, whose [make] admits only
   [0, 1] variables (section "Consistency level" below). Governed by docs/SPEC.md 3.2
   (consistency levels) and 3.3 (explanations). Proof shape: every pruning and every
   conflict is one `rup` whose clause is the constraint itself, RUP in one step against
   the row that states it. The family is [Single_row] in the I-X10 classification table
   of test/unit/test_trace.ml (a pruning that follows from one model constraint, whose
   trace line is RUP with nothing derived ahead of it).

   The propagation itself is lib/core/prop/pb.ml's: a clause is a PB row with every
   coefficient 1 and degree 1, and [t] is [Pb.t] (see "There is ONE implementation"
   below the header).

   ---------------------------------------------------------------------------
   A WIDENING of bool_clause (D-0052)
   ---------------------------------------------------------------------------

   D-0052 decided that a clause over order literals is a widening of `bool_clause` and
   not a new propagator family, and the decision rests on three checkable facts:
   [Explanation.Clause] is already [Lit.t list] rather than a list of Booleans,
   [Justify.validate_lits] checks only that a literal's owner is a declared variable, and
   every Boolean-specific site in this file was a CONSTANT SUBSTITUTION (the threshold 1)
   rather than a structural assumption. [Lit.bool_true] / [Lit.bool_false] are literally
   [Lit.ge x 1] / [Lit.le x 0].

   So the threshold [k] is a field of each literal ([Pb.atom]) instead of the constant 1.
   The widening exists because a 1UIP learned clause over integer variables is exactly
   such a clause, and before it nothing propagated one (lib/core/learn.ml's header: the
   backjump "would re-reach the same fixpoint, re-take the same decision and re-derive
   the same conflict"). It was built by M2-L12.

   ONE IMPLEMENTATION. The faces below share [t], [make], [vars] and [propagate] outright,
   so there is no second propagation loop to keep in step. D-0052 refused one, and this
   holds.

   WATCHED LITERALS, on the learned face only. A model clause keeps no state between
   runs: a run is [Pb.propagate], whose degree-1 shortcut [Pb.quiet] walks to the second
   non-false literal. A LEARNED clause carries two watched literals in [Learned_clause]
   and answers the engine's advisor question from them (lib/core/propagator.ml's
   [inst_advise] and [inst_watched]); I-P7 admits that state, because an advisor may
   drop a wake only when a run then would change nothing. D-0052 had refused watched
   literals, because no propagator then had a [mutable] field and learned clauses were
   narrow (M2-L12 step 0 measured 72 clauses of width 1, 5 of width 2, 8 of width 3 and 3
   of width 4 on the suite). M6-T20 (D-0104) added them once learned clauses were
   measured to be where the propagator runs went, and M6-T22 (D-0138) made the engine
   ask only the clauses watching the moved variable.

   ---------------------------------------------------------------------------
   Consistency level: BOUNDS here, DOMAIN in the [Bool_clause] submodule
   ---------------------------------------------------------------------------

   Order literals over integers have an INTERIOR. `x <= 1 \/ x >= 3` over `x in 0..5` is
   a HOLE at 2, not a tautology. Unit propagation moves bounds; it does not punch the
   hole. So the declared level here is BOUNDS (docs/SPEC.md 3.2), and SPEC 3.2 makes the
   declared level the bound on what an explanation may claim. This is the real cost of
   the widening, and D-0052 names it as the honest counter-argument to its own verdict.

   Chasing the hole would need [Store.remove], and a reason that mentions a hole is the
   case that forces the direct encoding (a hole cannot be negated into a clause without a
   literal for `x = v`; D-0019 point 3, which otherwise keeps disequalities on the order
   encoding). D-0052 decided that the clause row does not chase it, and this module does
   not.

   [Bool_clause] below still declares DOMAIN, and that declaration is true. Its [make]
   rejects any variable not declared over [0, 1] (a `var bool` is the order encoding on
   [0, 1], D-0007), a [0, 1] variable has no interior, and for a clause over such
   variables unit propagation IS domain consistency: while two literals are open every
   value of every variable has a support. That is the [Ne] / [Ne.Int_ne] pattern, one
   implementation and two honest declarations, the narrower one earned by a checked
   precondition.

   ---------------------------------------------------------------------------
   The opposite-direction pair: a HOLE, not a tautology
   ---------------------------------------------------------------------------

   [make] drops exact duplicate literals but leaves a variable occurring at both
   polarities alone, and the ordinary path is right for it without a special case. For
   `b \/ ~b` the clause is a tautology and never fires. For `x >= 3 \/ x <= 1` it is not
   one, in two ways:

     - `x` narrowed to [2, 2]: both literals are false ([Pb.Unsat_lit]), the slack is
       negative, and the propagator CONFLICTS. A tautology assumption would have missed a
       real violation.
     - `x` narrowed to [2, 5]: `x <= 1` is false and `x >= 3` is [Pb.Open], so that one
       literal is forced and the propagator moves `lo` to 3, a pruning no tautology ever
       licenses.

   D-0052 measured that at least 9 learned clauses of width >= 3 carry such a pair, so it
   is real traffic rather than an edge case. [Learn.minimise]'s [slot] keys on
   (variable, polarity), so opposite-direction pairs survive minimisation by design.
   (An older version of this header called such a clause a tautology; the code was
   already right.)

   ---------------------------------------------------------------------------
   Shape, and the two structural differences from [Linear]
   ---------------------------------------------------------------------------

   This follows lib/core/prop/linear.ml, the reference propagator: one pass, [consistency]
   declared, the explanation built from data frozen at [make] time. The two structural
   differences are deliberate and are the same two lib/core/prop/ne.ml makes, for the
   same reason:

     - It cites no row id, because its justification is a `rup` whose target states its
       own content in full. Nothing here builds a [Model_row], so [make] takes no
       [?row_id]; an unused id parameter would be an invitation to believe it was
       load-bearing. (The hazard D-0011 guarded against, a [Trivial] explanation meaning
       "whatever row is current", is gone: D-0037 deleted the constructor and made the
       ambient row unrepresentable.)

     - Nothing is [Deferred]. [Linear] and [Ne] defer because their reasons are a
       function of the STORE at the moment of the pruning, so they must snapshot, and
       snapshotting is what costs. A clause's reason is the clause: a function of the
       constraint alone, identical for every pruning and every conflict this instance
       will ever report, and therefore computed once in [make] and shared.
       docs/ARCHITECTURE.md's "lazy where it is expensive" cuts the other way here, since
       there is nothing to be lazy about, and I-X6 (an explanation reads a snapshot,
       never live domains) is satisfied vacuously by a value that does not depend on the
       store at all.

   Sharing the one [Explanation.t] has a second, useful consequence: lib/core/justify.ml
   memoises on PHYSICAL identity, so every pruning of one clause inside one decision
   level emits the clause once and cites that id again afterwards.

   ---------------------------------------------------------------------------
   Justification: one `rup`, which is the clause restated
   ---------------------------------------------------------------------------

   docs/PROOF-FORMAT.md section 4 nominates `rup` for `bool_clause`, and that is not a
   weakness: a `rup` target is a CLAUSE, and this constraint IS a clause over
   order-encoding literals (D-0019: the order encoding suffices while no reason has to
   mention a hole). D-0007 fixes the Boolean spelling: a `var bool` is the order
   encoding on [0, 1], so "b is true" is [b_ge_1] ([Lit.bool_true]) and "b is false" is
   [~b_ge_1] ([Lit.bool_false]). There is no second naming scheme and no direct encoding
   anywhere in this module, and none is forced, because no reason here ever has to
   mention a hole. [of_lits] REFUSES a [Lit.Eq] literal outright for that reason (see its
   comment).

   Every explanation this module builds, pruning and conflict alike, is the same clause,
   namely the constraint itself. For a CONFLICT every literal is false and the clause
   says so. For a PRUNING of the last open literal it is the trace-line shape of D-0018
   (the claim disjoined with the negation of the facts the propagator read) read the
   other way round: the claim is the literal being made true, and the facts are the other
   literals, each false. Those are literally the same list, and that is no coincidence:
   the reason a literal is forced is that the assignment which falsifies it is the
   assignment that conflicts. [Ne]'s header records the identical observation about a
   disequality.

   Three properties of that clause, each of which a later change could quietly break:

   1. It is GLOBALLY VALID: it is the constraint, not a consequence of the current
      decisions. So it is sound at any proof level and never needs guarding or wiping.

      For a LEARNED instance this holds only while the constraint is on the page. A
      clause from a model row is there for the whole run; a LEARNED clause is there only
      while lib/core/retention.ml holds it (the default policy, [tiered], evicts, D-0226),
      so a `rup` citing it is RUP only while that constraint is live. Whoever registers a
      learned instance must cite its id with [Retention]; [Search.register_learned] does
      ([Retention.cite_lazy]).

   2. It is REVERSE UNIT PROPAGATION IN ONE STEP against the row that states it: the
      model row lib/flatzinc/compile.ml posts, or the learned constraint
      [Learned.introduce] put on the page. Negating the target falsifies that row
      outright, so the checker does no searching at all. docs/PROOF-FORMAT.md section 2a
      asks for `rup` wherever unit propagation closes a step, and here the alternative
      `pol` would be `pol <row>`, a restatement of the row, which D-0009 records as a
      trap this project once fell into.

   3. It contains no direct-encoding literal, so it depends on nothing introduced by
      `red` and leaves nothing for the I-X2 audit (every constraint id deleted exactly
      once) to retire.

   The empty clause is a real value here and is handled by no special case. It arises
   when every literal folded away against a constant (`bool_clause([], [])`, or a clause
   all of whose operands are parameters with the wrong truth value), and the propagator
   conflicts immediately with [Explanation.clause []], which renders as `rup >= 1 ;`. A
   conflict that rests on a clause is closed with the empty clause rather than by a
   numeric contradiction (D-0022; I-X7, what `conclusion UNSAT` cites must be a line the
   checker established). That is the same route `int_ne(x, x)` takes in
   test/models/ne_self_unsat.fzn.

   COST. A run is [Pb.quiet]'s walk to the second non-false literal, O(position of that
   literal), and a pass over the row when it is not quiet. A learned clause's advisor
   ([Learned_clause.ask]) is asked once per wake of every clause watching the moved
   variable, so it reads only its own record and the domain: each watch's variable,
   threshold and polarity are kept there flat by [set_watches], the one writer of [w1]
   and [w2] (the file-by-file review of M16-file-review-T2, D-0190). *)

module Lit = Baguette_proof.Lit

(* ---------------------------------------------------------------------------
   There is ONE implementation, and it is [Pb] (D-0054)
   ---------------------------------------------------------------------------

   This module IS the degree-1 case of a learned PB row: [t] is [Pb.t], [make] and
   [of_lits] build one with every coefficient 1 and degree 1, and [propagate] is
   [Pb.propagate] with no wrapper. D-0044 fixed the learned object as a PB inequality with
   the CLAUSE as its degree-1, unit-coefficient case, and D-0054 built the PB row as a
   propagator, so a clause needs no loop of its own (M2-L13).

   lib/core/prop/pb.ml's header derives the four cases a clause has (satisfied, two
   open, one open and forced, none open and conflicting) from its slack rule, each
   falling out rather than being special-cased. Its [reason_clause] is where the
   explanations are shown to coincide: for a degree-1 row the literals a step names are
   always the WHOLE constraint, in term order, so the [Explanation.t] is the same value,
   the shared one, which keeps lib/core/justify.ml's memoisation on physical identity
   firing exactly as the header above says.

   What the header says about the SHAPE of a clause is unchanged by this; what went is a
   second copy of the propagation loop, which would have been "a second implementation
   to keep in step", the thing this file already refused for [Array_bool_or]. *)

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
   has narrowed it: the same requirement, for the same reason, that [Linear.make] and
   [Ne.make] state (a bound fact is a chain of order literals from the DECLARED bound,
   D-0010). Here it is a check rather than a freeze: a
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
  (* The clause plus TWO WATCHED LITERALS, the one kind of mutable propagator state I-P7
     admits (an advisor may drop a wake only when a run then would change nothing).
     [w1] and [w2] are term indices of [pb]. After a run both are non-false unless the
     clause was unit or failed, and a widening domain cannot falsify a literal, so
     backtracking never has to restore them. Added by M6-T20 (D-0104).

     RESTING, under [rest_satisfied]. [rest] is the index of a watched literal found TRUE
     by a run, or [-1]. The rule: a run that finds one of its two watched literals true
     does nothing, MOVES NEITHER WATCH, and reports that it rests on that literal
     ([watched] answers [(w, Propagator.rests)]). While it rests its advisor declines
     every change, and the engine indexes it under that literal alone and seeds it again
     after a backtrack that pops the bound holding the literal up ([Engine.rest_on]). That
     run finds the literal still true and rests again, or goes back to the two watches it
     left.

     Why it loses no pruning: a clause with a true literal cannot prune or fail whatever
     else changes, so declining is I-P7 read literally; and the two watches it left are
     good again once released, because the other watch was non-false or falsified at a
     level at or above the true one's (the classic argument for MiniSat's satisfied
     clauses, spelled out at [Engine.rest_on]). What it changes: not the fixpoint of any
     node, but the watch a satisfied clause holds after a backtrack, so a later pruning by
     it can be woken at another trail entry and land at another place in the propagation
     order (D-0173 section 3). It is OFF by default ([Search.default_config], and [make]'s
     own default); [Search] passes its [config.rest_satisfied]
     (BAGUETTE_REST_SATISFIED=on). Measured motive: on codes-cp's QR48 every one of the
     177 learned-clause runs per node was a run of a satisfied clause moving its false
     watch, and the asks that woke it cost more than the runs (M11-complexity-T17, D-0173
     section 2). *)
  (* Each watch's literal is ALSO kept flat in the record: its variable as an int
     ([x1]/[x2], [-1] for no literal), its threshold and its polarity, because [ask] reads
     nothing else and is asked once per wake of every clause watching the moved variable.
     They are a COPY of term [w1]'s and term [w2]'s fields of [pb], written only by
     [set_watches], which is the one place [w1] and [w2] are written; a test that places
     the watches by hand calls it too. Measured motive: 27 % of 2013 rcpsp_11's samples
     were [ask] itself, a chain of four dependent loads (the record, the atom array, the
     atom, the domain), found by the file-by-file review M16-file-review-T2 (D-0190).
     Since D-0226 (the learned-row layout) there is no atom array: [pb]'s own flat arrays
     are read by index. *)
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
     a watch that does not move keeps the copy it has. An index outside the row (the [-1]
     [rewatch]'s [best] answers for a one-literal clause with its literal false) gets
     [x = -1], which no variable is. *)
  (* Term [i]'s polarity, read off [pb]'s polarity bytes here rather than through
     [Pb.positive_at]: dune's dev profile compiles with [-opaque], so a cross-module
     accessor is a call, and these run on every watch move (D-0226 measured the calls). *)
  let positive (pb : Pb.t) i = Bytes.unsafe_get pb.Pb.pv i <> '\000'

  let set_watches t w1 w2 =
    let n = Pb.width t.pb in
    if w1 <> t.w1 then (
      t.w1 <- w1;
      if w1 >= 0 && w1 < n then (
        t.x1 <- Var.to_int t.pb.Pb.xv.(w1);
        t.k1 <- t.pb.Pb.kv.(w1);
        t.p1 <- positive t.pb w1)
      else t.x1 <- -1);
    if w2 <> t.w2 then (
      t.w2 <- w2;
      if w2 >= 0 && w2 < n then (
        t.x2 <- Var.to_int t.pb.Pb.xv.(w2);
        t.k2 <- t.pb.Pb.kv.(w2);
        t.p2 <- positive t.pb w2)
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
    let x = t.pb.Pb.xv.(i) and k = t.pb.Pb.kv.(i) in
    if positive t.pb i then Store.hi_below store x k else Store.lo_at_least store x k

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

  (* THE PRECONDITION of the two watches: at most one literal per (variable, polarity)
     (D-0142 section 5; D-0142 is the first batch of the complexity pass over the engine,
     the store and the propagators). Two rungs of one variable in one direction,
     `x >= 3 \/ x >= 5`, can propagate with both of them non-false, because [Pb.pass]'s
     ladder-effective rule forces `x >= 3` once every other literal is false. So watching
     those two would let a change of an unwatched variable make the clause unit unasked.
     Opposite polarities on one variable are fine: BOUNDS cannot punch the hole between
     them, so a run with both open does nothing. [Learn.minimise] merges every same-slot
     pair of the 1UIP clause, and that clause is the only one [Search] registers here;
     checked under BAGUETTE_DEBUG. *)
  let one_per_slot (pb : Pb.t) =
    let n = Pb.width pb in
    let ok = ref true in
    for i = 0 to n - 1 do
      for j = i + 1 to n - 1 do
        if
          Var.to_int pb.Pb.xv.(i) = Var.to_int pb.Pb.xv.(j)
          && positive pb i = positive pb j
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

  (* The variables of the two watches, each with the move that can falsify it. [ask]
     answers [false] for every other variable whatever the store holds, which is
     [Propagator.inst_watched]'s contract, so the engine may wake this clause from these
     two variables only (M6-T22, D-0138, after the engine was measured asking every
     learned clause about every variable it names). The direction is the directional
     watch of M11-complexity-T3 (D-0142, item E1). `x >= k` is
     false once [hi x < k], so only an UPPER-bound move falsifies it; `x <= k - 1` only a
     LOWER-bound move. That is [Propagator.watch_hi]/[watch_lo]'s whole claim, and it is
     true of every order literal. *)
  let watch_of t i =
    if positive t.pb i then Propagator.watch_hi t.pb.Pb.xv.(i)
    else Propagator.watch_lo t.pb.Pb.xv.(i)

  let watched t () =
    if t.rest >= 0 then (watch_of t t.rest, Propagator.rests)
    else (watch_of t t.w1, watch_of t t.w2)

  (* The advisor [Propagator.pack] takes: both halves of one object. Each is a closure of
     its own arity over [t], because [ask t], a partial application, made every ask go
     through OCaml's currying stub before reaching [ask] (M16-file-review-T2, D-0190). *)
  let advise t =
    {
      Propagator.ask = (fun store v -> ask t store v);
      watched = Some (fun () -> watched t ());
    }

  (* [rewatch] after a run [Pb.quiet] answered, from what its walk found instead of a
     walk of its own (item E2 (a) of the complexity pass, D-0142). The store has not moved
     since [quiet] (a quiet run prunes nothing), and [quiet] answered [true], so [scan.f1]
     and [scan.f2] are the first two non-false literals. [best ~not_] is then "the first
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

  (* Nearly every run of a learned clause is a watched literal falsified with another
     literal still free, the run a two-watched-literal solver answers by moving the
     watch. [Pb.quiet] answers it with one walk, and the watch then moves on the same
     store, so the watches, and every later wake, are what they would have been (M6-T22,
     D-0138).

     That walk is the only one: [Pb.quiet] leaves the first two non-false literals in
     [t.pb]'s scan and [rewatch_quiet] reads them, rather than walking the clause again
     in [rewatch]'s [best] once per watch to replace (D-0142, item E2 (a)). A run [quiet]
     does not answer is [Pb.pass], exactly what [Pb.propagate] does then, followed by the
     full [rewatch], because that run may have moved the store. *)
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
