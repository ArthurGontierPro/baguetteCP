(* bool_clause: a disjunction over Boolean variables,

     x_1 \/ ... \/ x_p  \/  ~y_1 \/ ... \/ ~y_q

   and, through the decomposition lib/flatzinc/compile.ml performs, the clause family
   of `array_bool_or`, `array_bool_and`, `bool_eq` and `bool_not` as well. The
   submodules at the bottom of this file are that same propagator under the name of
   the builtin an instance came from, exactly as [Ne.Int_ne] is [Ne] under another
   name -- an instance reports the builtin the model actually wrote, which is what a
   trace or a failure message has to say to be worth reading.

   Consistency level: DOMAIN (docs/SPEC.md 3.2). A clause has exactly one inference --
   unit propagation -- and for a clause unit propagation *is* domain consistency, not
   an approximation of it: while two literals are unassigned every value of every
   variable has a support (set some other open literal true), and when exactly one is
   unassigned its falsifying value has none. So there is no stronger propagator for
   this constraint and nothing is left on the table. Booleans have no interior, so
   "bounds" and "domain" coincide here anyway; DOMAIN is declared because it is the
   true level, and SPEC 3.2 makes the declared level the bound on what an explanation
   may claim.

   Shape: this follows lib/core/prop/linear.ml, the reference propagator -- one pass,
   [consistency] declared, the explanation built from data frozen at [make] time. The
   two structural differences from [Linear] are deliberate and are the same two
   lib/core/prop/ne.ml makes, for the same reason:

     - it cites no row id, because its justification is a [rup] whose target states
       its own content in full. D-0011's hazard is [Explanation.Trivial] ("whatever
       ctx.model_id points at", unresolvable once it is on the trail with no
       propagator identity attached); nothing here ever builds [Trivial] or
       [Model_row], so there is nothing to route and [make] takes no [?row_id]. An
       unused id parameter would be an invitation to believe it was load-bearing.

     - nothing is [Deferred]. [Linear] and [Ne] defer because their reasons are a
       function of the *store* at the moment of the pruning, so they must snapshot,
       and snapshotting is what costs. A clause's reason is the clause: a function of
       the constraint alone, identical for every pruning and every conflict this
       instance will ever report, and therefore computed once in [make] and shared.
       docs/ARCHITECTURE.md's "lazy where it is expensive" cuts the other way here --
       there is nothing to be lazy about, and I-X6's snapshot discipline is satisfied
       vacuously by a value that does not depend on the store at all.

   Sharing the one [Explanation.t] has a second, useful consequence: lib/core/justify.ml
   memoises on *physical* identity, so every pruning of one clause inside one decision
   level emits the clause once and cites that id again afterwards.

   ---------------------------------------------------------------------------
   Justification -- one [rup], which is the model row restated
   ---------------------------------------------------------------------------

   docs/PROOF-FORMAT.md section 4 nominates [rup] for `bool_clause`, and D-0019 is why
   that is not a weakness: a `rup` target is a *clause*, and a Boolean clause is
   already a clause over order-encoding literals. D-0007 fixes the spelling --
   a `var bool` is the order encoding on [0, 1], so "b is true" is [b_ge_1]
   ([Lit.bool_true]) and "b is false" is [~b_ge_1] ([Lit.bool_false]). There is no
   second naming scheme and no direct encoding anywhere in this module; by D-0019
   point 3's test, none is forced, because no reason here ever has to mention a hole.

   Every explanation this module builds -- pruning and conflict alike -- is the same
   clause, namely the constraint itself:

       x_1 \/ ... \/ x_p \/ ~y_1 \/ ... \/ ~y_q

   For a *conflict* every literal is false and the clause says so. For a *pruning* of
   the last open literal it is D-0018's trace-line shape read the other way round:
   the claim (the literal being made true) disjoined with the negation of the facts
   the propagator read (the other literals, each false). Those are literally the same
   list, which is not a coincidence -- the reason a literal is forced is that the
   assignment which falsifies it is the assignment that conflicts. [Ne]'s header
   records the identical observation about a disequality.

   Three properties of that clause, each of which a later change could quietly break:

   1. It is *globally valid*: it is the model constraint, not a consequence of the
      current decisions. So it is sound at any proof level and never needs guarding
      or wiping.

   2. It is *reverse unit propagation in one step* against the row
      lib/flatzinc/compile.ml posts for this constraint. That row is the clause: the
      linear form  -sum_i x_i + sum_j y_j <= q - 1  expands over the order encoding
      and normalises to  +1 x_1_ge_1 ... +1 ~y_1_ge_1 ... >= 1.  Negating the target
      falsifies it outright, so the checker does no searching at all. This is the one
      case where PROOF-FORMAT section 2's "prefer pol over rup" costs nothing: the
      [pol] would be `pol <row>`, a restatement, and D-0009 records what restating a
      row as a justification did to this project once already.

   3. It contains no direct-encoding literal, so it depends on nothing introduced by
      [red] and leaves nothing for the I-X2 audit to retire.

   The empty clause is a real value here and is handled by no special case. It arises
   when every literal folded away against a constant (`bool_clause([], [])`, or a
   clause all of whose operands are parameters with the wrong truth value), and the
   propagator conflicts immediately with [Explanation.clause []], which renders as
   `rup >= 1 ;` and is closed the D-0022/I-X7 way because it rests on a clause. That
   is the same route `int_ne(x, x)` takes in test/models/ne_self_unsat.fzn. *)

module Lit = Baguette_proof.Lit

(* One literal. [name] is frozen at [make] time -- nothing renames a variable, and the
   explanation should not have to hold the store to spell itself out. [positive] is
   "this literal is x", false is "this literal is ~x". *)
type lit = { x : Var.t; name : string; positive : bool }

(* [pb] is the whole clause as proof literals and [expl] the whole clause as an
   explanation, both built once in [make]: see the module header on why neither is
   deferred and why sharing [expl] is worth doing. *)
type t = { lits : lit list; pb : Lit.t list; expl : Explanation.t }

let name = "bool_clause"
let consistency = Propagator.Domain

(* D-0007 / docs/PROOF-FORMAT.md section 3, "Booleans": there is exactly one Boolean
   per `var bool` and it is the order literal [b_ge_1]. Reached through
   [Lit.bool_true] / [Lit.bool_false] rather than spelled out, so that this module
   cannot become the place a second naming scheme appears. *)
let pb_lit l = if l.positive then Lit.bool_true l.name else Lit.bool_false l.name

(* [raw] is (variable, polarity) pairs. Duplicates -- the same variable at the same
   polarity twice -- are dropped, because two occurrences of one literal would read
   below as two unassigned literals and the propagator would then decline to infer
   anything. That is sound but strictly weaker, and there is no reason to accept it
   when the merge is this cheap. A variable occurring at *both* polarities is left
   alone: the clause is then a tautology, the propagator correctly never fires (one
   of the two is satisfied the moment the variable is fixed, and while it is unfixed
   both are open, which is two), and encoding that as a special case would be more
   code than letting the ordinary path be right.

   Reads each variable's domain out of the store, so it must be called before anything
   has narrowed it -- the same requirement, for the same D-0010 reason, that
   [Linear.make] and [Ne.make] state. Here it is a check rather than a freeze: a clause
   literal must be a `var bool`, i.e. the order encoding on [0, 1] (D-0007), and every
   literal spelling below assumes it. lib/flatzinc/compile.ml rejects a non-Boolean
   argument with a positioned diagnostic before ever reaching here; this is the
   backstop for a caller built by hand, which is what every unit test is. *)
let make store raw =
  let seen = Hashtbl.create 16 in
  let lits =
    List.filter_map
      (fun (x, positive) ->
        let key = (Var.to_int x, positive) in
        if Hashtbl.mem seen key then None
        else (
          Hashtbl.add seen key ();
          let d = Store.get store x in
          if Domain.lo d <> 0 || Domain.hi d <> 1 then
            invalid_arg
              (Printf.sprintf
                 "Bool_clause.make: `%s` is declared over %s, but a clause literal must \
                  be a `var bool`, i.e. the order encoding on [0, 1] (docs/DECISIONS.md \
                  D-0007)"
                 (Store.name store x) (Domain.to_string d));
          Some { x; name = Store.name store x; positive }))
      raw
  in
  let pb = List.map pb_lit lits in
  { lits; pb; expl = Explanation.clause pb }

let vars t = List.map (fun l -> l.x) t.lits

(* The clause, for callers that want to see what was built. *)
let literals t = t.pb

(* ------------------------------------------------------------------- bound facts *)

(* docs/DECISIONS.md D-0018's other projection: the facts lib/core/trace.ml negates
   into the tail of a trace line. A literal that is *false* is a bound fact -- the
   positive statement is "b <= 0" for a positive occurrence and "b >= 1" for a
   negative one -- which is exactly [Lit.negate] of the literal, so the line [Trace]
   builds, [claim :: List.map Lit.negate facts], comes out as the clause itself.

   Every fact here is a genuine, non-declared bound: a `var bool` is declared over the
   whole of [0, 1] (lib/flatzinc/compile.ml's [bounds_of_domain]), so a literal can
   only be false because something moved a bound, never because the declaration
   already said so. That is why nothing is dropped here, unlike [Linear.facts_of_snaps]
   and [Ne.fixed_facts], which must drop a fact that is still the encoding's constant
   true (docs/PROOF-FORMAT.md section 3). *)
let falsity_fact l = Lit.negate (pb_lit l)

let other_facts t (unit_lit : lit) =
  List.filter_map (fun l -> if l == unit_lit then None else Some (falsity_fact l)) t.lits

let all_facts t = List.map falsity_fact t.lits

(* ------------------------------------------------------------------- propagation *)

type status = Sat_lit | Unsat_lit | Open

let status store l =
  let d = Store.get store l.x in
  if l.positive then
    if Domain.lo d >= 1 then Sat_lit else if Domain.hi d <= 0 then Unsat_lit else Open
  else if Domain.hi d <= 0 then Sat_lit
  else if Domain.lo d >= 1 then Unsat_lit
  else Open

(* One walk over the clause. It stops at the first satisfied literal (nothing can be
   inferred from a satisfied clause) and at the second open one (nor from a clause
   with two ways left to be true). Otherwise it hands back the open literals, of which
   there are none (every literal is false: conflict) or one (the unit). *)
type survey = Satisfied | Two_open | Units of lit list

let rec survey_from store acc = function
  | [] -> Units (List.rev acc)
  | l :: rest -> (
      match status store l with
      | Sat_lit -> Satisfied
      | Unsat_lit -> survey_from store acc rest
      | Open -> if acc = [] then survey_from store [ l ] rest else Two_open)

(* Force the last open literal true. A positive one moves lo to 1, a negative one
   moves hi to 0; either way exactly one bound moves, so lib/core/trace.ml writes
   exactly one line for it (its [claims] checks both bounds and would happily write
   two). [Store.set_lo_with_facts]/[set_hi_with_facts] rather than the factless
   mutators: I-P5, and without the facts the line would claim the new bound
   unconditionally, which is false. *)
let assign t store (l : lit) =
  let facts () = other_facts t l in
  let outcome =
    if l.positive then Store.set_lo_with_facts store l.x 1 ~facts t.expl
    else Store.set_hi_with_facts store l.x 0 ~facts t.expl
  in
  match outcome with
  | Store.Changed | Store.Unchanged -> Propagator.Fixpoint
  | Store.Conflict e ->
      (* Unreachable at the interface: [l] is [Open], so its domain holds both 0 and
         1 and moving one bound to the other cannot empty it. Handled rather than
         asserted so a future [Domain] change cannot turn a silent wrong answer into
         the failure mode, and the explanation handed back is the one that caused it,
         exactly as [Store.apply] returns it. *)
      Propagator.Conflict e

let propagate t store =
  match survey_from store [] t.lits with
  | Satisfied -> Propagator.Fixpoint
  | Two_open -> Propagator.Fixpoint
  | Units [ l ] -> assign t store l
  | Units [] ->
      (* I-P3, checking: every literal is false, so the clause is violated. This is
         also the all-fixed case -- a fixed variable is never [Open] -- so declaring
         a conflict here is exactly "fail iff the assignment violates the
         constraint", and it is reached before every variable is fixed as well, which
         is the propagation half. *)
      Store.record_conflict_facts store (fun () -> all_facts t);
      Propagator.Conflict t.expl
  | Units (_ :: _ :: _) ->
      (* [survey_from] returns at most one; it stops at the second. *)
      assert false

(* ---------------------------------------------------------------------------
   The same propagator under the name of the builtin that produced the clause.

   lib/flatzinc/compile.ml decomposes `array_bool_or`, `array_bool_and`, `bool_eq`
   and `bool_not` into clauses -- one row and one instance per clause, which is
   D-0027 point 3's default ("where a constraint's rows propagate independently and
   the engine's fixpoint reproduces the fused loop, post one instance per row") and
   loses nothing: unit propagation over the clauses of a reified or/and is domain
   consistent for the whole constraint, which is the same thing a hand-written
   [Array_bool_or] would achieve with more code and a second reason shape to get
   right.

   These exist only so the packed instance reports the builtin the model wrote, the
   way [Ne.Int_ne] does. They share [t], [make], [vars] and [propagate] outright;
   there is deliberately nothing else in them, because anything else would be a
   second implementation to keep in step. *)

module Array_bool_or = struct
  type nonrec t = t

  let name = "array_bool_or"
  let consistency = consistency
  let vars = vars
  let propagate = propagate
end

module Array_bool_and = struct
  type nonrec t = t

  let name = "array_bool_and"
  let consistency = consistency
  let vars = vars
  let propagate = propagate
end

module Bool_eq = struct
  type nonrec t = t

  let name = "bool_eq"
  let consistency = consistency
  let vars = vars
  let propagate = propagate
end

module Bool_not = struct
  type nonrec t = t

  let name = "bool_not"
  let consistency = consistency
  let vars = vars
  let propagate = propagate
end
