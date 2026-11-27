(* bool2int(b, x): the FlatZinc channelling constraint between a `var bool` and a
   `var int`, i.e.  x = b  with b ranging over {0, 1}.

   Consistency level BOUNDS, proof shape a `rup` clause per pruning; both are argued
   below. This module serves an x on the ORDER encoding. Over a bits-encoded x,
   lib/flatzinc/compile.ml posts the same two rows as a pair of [Linear] instances
   instead ([Bool2int_row] there).

   This is the seam between the Boolean and the integer half of the model, and a
   channelling constraint that prunes in one direction and not the other is the
   classic way to lose propagation without losing any test. So, explicitly:

   ---------------------------------------------------------------------------
   Which directions propagate: BOTH, on BOTH bounds. Four pushes, every time.
   ---------------------------------------------------------------------------

     b -> x    lo(x) := max(lo(x), lo(b))        hi(x) := min(hi(x), hi(b))
     x -> b    lo(b) := max(lo(b), lo(x))        hi(b) := min(hi(b), hi(x))

   The b -> x direction is the one that is easy to write and easy to believe is all
   there is; it is what confines x to {0, 1} (b is declared over [0, 1], so the very
   first run gives x <= 1 and x >= 0 whatever x was declared over). The x -> b
   direction is the one that does the work during search: it is how a bound moved on
   the integer side by a linear constraint becomes a Boolean fact that a clause can
   then unit-propagate on. Dropping either half would leave every model in
   test/models/bool_channel_*.fzn still solvable and still correct, just explored by
   branching instead of by inference, which is exactly the shape of bug this comment
   exists to make impossible to introduce silently.

   One pass reaches the fixpoint, and the order below is why: x is narrowed to b's
   bounds first, then b to x's *new* bounds. After the first step lo(x) >= lo(b) and
   hi(x) <= hi(b), so the second step can only tighten b to what x has actually got --
   there is nothing left for a third step to do. (Re-running is still cheap and the
   engine does it anyway. The point is I-P2, idempotence at the interface: run again at
   the fixpoint, the propagator changes nothing.)

   Consistency level: BOUNDS (docs/SPEC.md 3.2). Only lo/hi are read and written; no
   hole is ever punched. At the fixpoint that happens to be domain consistency as
   well, because the constraint confines both variables to {0, 1}, where an interval
   and a domain are the same object -- but BOUNDS is what is declared, because the
   declared level is the bound on what an explanation may claim (SPEC 3.2) and the
   claim "x's remaining values each have a support" is not one this code establishes
   on the first pass over a wide x. Declaring the weaker level is conservative in the
   only direction that matters. A hole inside x is handled correctly without being
   reasoned about: x = {0, 2} meets hi(x) := 1 and [Domain.set_hi] tightens past the
   hole, because a bound is always a value of the domain (I-D2), leaving {0}.

   Shape: this follows lib/core/prop/linear.ml, the reference propagator. The
   arithmetic is the one place it does not need to: every quantity here is a bound
   already in a domain, and nothing is multiplied, added or divided, so there is no
   [Checked] call and no overflow exposure in this module (the overflow audit that
   introduced checked arithmetic was M1-T23). (lib/flatzinc/compile.ml
   still runs the cap over the two rows it posts for this constraint, because
   [Encoding.linear_terms_int_lin_le] does multiply.)

   ---------------------------------------------------------------------------
   Justification -- a clause, not a pol, and why that is the better answer here
   ---------------------------------------------------------------------------

   Proof shape (docs/SPEC.md 3.3): every pruning and every conflict is a [Clause],
   which the checker verifies as one `rup` step. The model rows are the two halves of
   the equality, posted by lib/flatzinc/compile.ml through [Encoding.add_int_lin_le]:

       row LE:  x - b <= 0            row GE:  b - x <= 0

   so the obvious move is to justify a pruning the way [Linear] does, as D-0013's
   "weaken, divide, add" [pol] over the row it came from. This module deliberately does
   not, and the reason is measured rather than aesthetic: D-0028 records that a
   [Weaken] summand is one literal per value across the *declared* width of the other
   term, per pruning -- a model with a `var 0..1000000` and no prunings at all emits a
   29.8 MB [pol] line. `bool2int` is precisely where a wide integer variable meets a
   Boolean one, so taking the [pol] route here would make the size of a channelling
   justification proportional to a width the constraint immediately destroys.

   The clausal reason is O(1) instead. Every pruning this module makes has the shape
   of the trace line D-0018 writes for it anyway (a branch's nogood is RUP over the
   trace lines the branch logged, one per pruning),

       <the order literal the pruning established>  \/  ~<the one bound fact read>

   and that clause is reverse unit propagation against one of the two rows above, in
   a step or two of the checker's own propagation along the order encoding's
   consistency clauses. Worked, for x declared 0..5 and the pruning hi(x) := 1 taken
   from hi(b) = 1 (b still at its declared bound, so the clause is the unit
   `~x_ge_2`): negating it asserts x_ge_2, the consistency clause x_ge_2 -> x_ge_1
   gives x_ge_1, and row LE -- which over the order encoding reads
   `~x_ge_1 + ... + ~x_ge_5 + b_ge_1 >= 5` -- can then reach at most 4. Falsified, so
   the [rup] closes with no search. The same check goes through for each of the four
   pushes; test/unit/test_prop.ml runs every one of them past the real checker rather
   than taking this paragraph's word for it.

   No [Explanation] constructor was needed for any of this: [Clause] was enough, the
   same place D-0019 arrived at from the disequality side (a disequality is justified
   over the order encoding by clauses, with no direct encoding). And no row id is
   cited, so the question D-0011 settles (which model row does an instance's
   explanation mean) cannot arise here any more than it can in lib/core/prop/ne.ml;
   [make] takes no row id for that reason. (M1-T31 removed the ambient row that
   question used to resolve to; this module never depended on it.)

   A bound fact still sitting at the variable's *declared* value contributes nothing
   to a clause: it is the encoding's constant true (docs/PROOF-FORMAT.md section 3,
   [Encoding.ge]'s [Holds]), it has no literal, and its negation is false, so
   including it would weaken the clause for nothing and name a variable the .opb does
   not contain. That is what [ge_fact] and [le_fact] below are for, and it is the
   common case here rather than an edge: b is declared over the whole of [0, 1], so
   *both* of b's bounds are declared until something moves one, and the b -> x
   prunings on the first pass therefore have empty reasons and emit unit clauses.

   A conflict is the same clause with the claim replaced by the opposing bound that
   the new one ran into -- "not all of these facts hold" over the facts read plus
   that one. When the opposing bound is itself still declared, that list can be
   empty, and [Explanation.clause []] is then the correct and honest answer: the
   model is unsatisfiable from its declared domains alone (`var 2..5: x` channelled
   to a `var bool`), the empty clause renders as `rup >= 1 ;`, and lib/core/search.ml
   closes it as it closes every root conflict, with the empty clause over the root's
   trace (D-0131). A clause is never cited to `conclusion UNSAT` as a contradiction in
   its own right (I-X7: the line UNSAT cites is one the checker has itself established
   as a contradiction; D-0022 first drew that line for a derivation resting on a
   clause). No special case is needed and none should be added: this is the same route
   `int_ne(x, x)` takes.

   ---------------------------------------------------------------------------
   Snapshotting
   ---------------------------------------------------------------------------

   Every explanation and every [~facts] list below is built BEFORE the push, from
   bounds read before the push. A reason rendered later (when the branch fails, which
   is when lib/core/trace.ml writes it down) must state the derivation as of the moment
   it was made, never as of now (I-X6, stated there for a deferred explanation's
   snapshot). Here that is easy to hold because the facts and the clause are built
   eagerly as plain values: this file makes no [Explanation.deferred], so nothing reads
   the store when the reason is rendered. *)

module Lit = Baguette_proof.Lit

(* Declared bounds are frozen at [make] time for the reason [Linear.make] and [Ne.make]
   both state (D-0010: a bound fact is a chain of order literals counted from the
   declared bound). A clause drops the halves that sit at the DECLARED bound,
   and the store stops reporting that bound the moment anything narrows the variable.
   [b_decl_lo]/[b_decl_hi] are 0 and 1 for every `var bool` (Booleans are the order
   encoding on [0, 1], D-0007), and are carried
   rather than assumed so the two sides read alike and neither has a constant baked
   into it. *)
type t = {
  b : Var.t;
  b_name : string;
  b_decl_lo : int;
  b_decl_hi : int;
  x : Var.t;
  x_name : string;
  x_decl_lo : int;
  x_decl_hi : int;
}

let name = "bool2int"
let consistency = Propagator.Bounds

(* Reads both declared domains out of the store, so it must be called before anything
   has narrowed them. [b] must be a `var bool`: the order encoding on [0, 1] (D-0007)
   is what every literal below is spelled in. lib/flatzinc/compile.ml rejects a
   non-Boolean first argument with a positioned diagnostic long before this runs; the
   check here is the backstop for a caller built by hand, which every unit test is. *)
let make store ~b ~x =
  let db = Store.get store b in
  if Domain.lo db <> 0 || Domain.hi db <> 1 then
    invalid_arg
      (Printf.sprintf
         "Bool2int.make: `%s` is declared over %s, but bool2int's first argument must be \
          a `var bool`, i.e. the order encoding on [0, 1] (docs/DECISIONS.md D-0007)"
         (Store.name store b) (Domain.to_string db));
  let dx = Store.get store x in
  {
    b;
    b_name = Store.name store b;
    b_decl_lo = Domain.lo db;
    b_decl_hi = Domain.hi db;
    x;
    x_name = Store.name store x;
    x_decl_lo = Domain.lo dx;
    x_decl_hi = Domain.hi dx;
  }

(* Both variables, so the engine wakes this propagator from either side -- which is
   what makes the x -> b direction of the header actually run. A duplicate is
   harmless: [Engine.create] dedupes its watcher lists, and `bool2int(b, b)` is a
   legal, vacuous constraint. *)
let vars t = [ t.b; t.x ]

(* ------------------------------------------------------------------- bound facts *)

(* "v >= value" / "v <= value" as a [Reason.fact], a list of one so the call sites
   below can concatenate. A fact at the declared bound renders to no literal, because a
   declared bound is the encoding's constant true (see the module header); that test
   lives once, in [Reason.lit_of_fact], shared with [Ne] and [Linear]. Facts are data
   rather than [Lit.t]s since reasons became declarative values separate from their
   justification (D-0026, built by M2-T8). *)
let ge_fact ~name ~decl_lo value = [ Reason.at_least ~name ~decl:decl_lo value ]
let le_fact ~name ~decl_hi value = [ Reason.at_most ~name ~decl:decl_hi value ]

(* "not all of these facts hold", the clause a conflict reports. *)
let nogood reason = Explanation.clause (List.map Lit.negate (Reason.lits_of_facts reason))

(* "these facts imply this claim", the clause a pruning reports -- and, literally, the
   line lib/core/trace.ml will write for it from the claim and the reason separately. The
   two being the same clause is what keeps the explanation and the trace line from
   drifting. A derivation and a trace that agreed on a type and not on a meaning was
   exactly the failure D-0009 recorded (a bound fact in a [pol] needs a constraint id,
   not a literal).

   Here the justification is a FUNCTION OF THE REASON. For this propagator the agreement
   D-0026 wants as a type is not merely a shared source, it is a derivation -- there is no
   reason/justification pair to get wrong, because one is computed from the other.
   [Linear] cannot do this (its justification is a cutting-planes [Combine] over
   declared-width chains, which states nothing about where a bound sits) and that is
   exactly why the two halves are separate types rather than one. *)
let implication ~claim reason =
  Explanation.clause (claim :: List.map Lit.negate (Reason.lits_of_facts reason))

(* ------------------------------------------------------------------- propagation *)

let propagate t store =
  let conflict = ref None in
  (* Raise [var]'s lower bound to [bound], justified by [facts]. Does nothing if the
     bound does not move, or if a push earlier in this same call already conflicted --
     the store is consistent at that point and pushing further would record a second
     reason for a failure that already has one. *)
  let push_lo var ~name ~decl_lo ~decl_hi bound ~facts =
    if Option.is_none !conflict then
      let d = Store.get store var in
      if bound > Domain.lo d then
        let claim = Lit.ge name bound in
        (* What this pruning concludes, as a [Reason.fact] carried on the [justified]
           value (D-0043). It is the same bound
           in the same direction as [claim] -- [Reason.lit_of_fact] of it IS [claim]
           whenever the bound has moved off the declared one -- built from the fact
           constructor rather than from the literal so that the store can compare it
           against the trail as data (numbers and a direction), which a [Lit.t] cannot
           be asked. *)
        let concludes = Some (Reason.at_least ~name ~decl:decl_lo bound) in
        match
          Store.set_lo store var bound
            (Reason.because ~concludes facts (implication ~claim facts))
        with
        | Store.Changed | Store.Unchanged -> ()
        | Store.Conflict _ ->
            (* The new bound crossed the variable's current upper bound. The reason is
               the facts that produced it, plus that upper bound -- dropped when it is
               still the declared one, which leaves the empty clause; see the header. *)
            let all = facts @ le_fact ~name ~decl_hi (Domain.hi d) in
            conflict :=
              Some
                (Store.conflict store (Reason.because ~concludes:None all (nogood all)))
  in
  let push_hi var ~name ~decl_lo ~decl_hi bound ~facts =
    if Option.is_none !conflict then
      let d = Store.get store var in
      if bound < Domain.hi d then
        let claim = Lit.le name bound in
        let concludes = Some (Reason.at_most ~name ~decl:decl_hi bound) in
        match
          Store.set_hi store var bound
            (Reason.because ~concludes facts (implication ~claim facts))
        with
        | Store.Changed | Store.Unchanged -> ()
        | Store.Conflict _ ->
            let all = facts @ ge_fact ~name ~decl_lo (Domain.lo d) in
            conflict :=
              Some
                (Store.conflict store (Reason.because ~concludes:None all (nogood all)))
  in
  (* b -> x. [db] is read once: nothing below writes to b before the x pushes are
     done, so it cannot go stale in between. *)
  let db = Store.get store t.b in
  push_lo t.x ~name:t.x_name ~decl_lo:t.x_decl_lo ~decl_hi:t.x_decl_hi (Domain.lo db)
    ~facts:(ge_fact ~name:t.b_name ~decl_lo:t.b_decl_lo (Domain.lo db));
  push_hi t.x ~name:t.x_name ~decl_lo:t.x_decl_lo ~decl_hi:t.x_decl_hi (Domain.hi db)
    ~facts:(le_fact ~name:t.b_name ~decl_hi:t.b_decl_hi (Domain.hi db));
  (* x -> b, against x as it now stands: the two pushes above may have tightened it,
     and reading the pre-push bounds here would state a fact that is no longer the
     one the propagator acted on. *)
  let dx = Store.get store t.x in
  push_lo t.b ~name:t.b_name ~decl_lo:t.b_decl_lo ~decl_hi:t.b_decl_hi (Domain.lo dx)
    ~facts:(ge_fact ~name:t.x_name ~decl_lo:t.x_decl_lo (Domain.lo dx));
  push_hi t.b ~name:t.b_name ~decl_lo:t.b_decl_lo ~decl_hi:t.b_decl_hi (Domain.hi dx)
    ~facts:(le_fact ~name:t.x_name ~decl_hi:t.x_decl_hi (Domain.hi dx));
  match !conflict with Some c -> Propagator.Conflict c | None -> Propagator.Fixpoint
