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
   `int_ne(x, x)` takes in test/models/ne_self_unsat.fzn. *)

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
   lib/core/prop/pb.ml's own header derives the four arms this used to spell out. *)
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
  type nonrec t = t

  let name = "learned_clause"
  let consistency = consistency
  let vars = vars
  let propagate = propagate
end
