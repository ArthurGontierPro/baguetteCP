(* The propagator interface: the module type [S] every constraint family implements, and
   [instance], the record the engine actually runs once a propagator has been packed.
   lib/core/prop/linear.ml is the reference implementation; read it next.

   Every propagator MUST document its consistency level in [consistency] and the shape of
   the proof step it emits in its module header, because the consistency level bounds what
   its explanations are allowed to claim (docs/SPEC.md section 3.2, and the table of
   docs/PROOF-FORMAT.md section 4).

   [propagate] runs until it has nothing more to say about its own constraint, then
   returns [Fixpoint]. Three properties are required of it (docs/INVARIANTS.md): it is
   SOUND, removing only values that extend to no solution of its constraint (I-P1);
   CHECKING, so that with every variable fixed it fails if and only if the assignment
   violates the constraint (I-P3); and IDEMPOTENT AT THE INTERFACE, so that run again at
   the engine's fixpoint it changes nothing (I-P2). Every domain change it makes carries
   its explanation, because the mutators of lib/core/store.ml take one (I-P4). *)

(* A conflict is a [Store.conflict]: the explanation ([c_why]), the bound facts the
   conflict read, which the branch writes as its own reason line before its nogood (D-0018
   point 3), and the id of the instance that reported it (M2-T7).

   A propagator never writes its own id. Either it forwards, unchanged, the
   [Store.conflict] a failing mutator handed it, or it builds one with [Store.conflict
   store], which stamps whichever instance [Engine] said was running. No function a
   propagator calls to change a domain or to report a conflict takes an id, so naming the
   wrong one would mean going out of its way through [Store.with_running], which the
   engine needs public. That route is not sealed, because [Store] cannot tell an engine
   from a propagator (it sees neither type); it is CHECKED instead, by
   [Engine.check_attribution], and test_engine.ml's [Steals_credit] takes it on purpose
   to prove the check fires. *)
type result = Fixpoint | Conflict of Store.conflict

(* One of these, not a free-form string, so that a typo cannot silently claim a stronger
   consistency than the code delivers. docs/GLOSSARY.md defines each. *)
type consistency = Bounds | Domain | Value | Checking

let consistency_to_string = function
  | Bounds -> "bounds"
  | Domain -> "domain"
  | Value -> "value"
  | Checking -> "checking"

module type S = sig
  type t

  val name : string
  val consistency : consistency
  val vars : t -> Var.t list
  val propagate : t -> Store.t -> result
end

(* ------------------------------------------------------------------ the PB row

   The pseudo-Boolean inequality an instance IS, as the .opb already contains it:
   [sum r_terms >= r_degree] over order literals, with [r_cid] the id of that very
   constraint on the page. It exists for PB conflict analysis (M2-L6).

   PB conflict analysis (lib/core/pb_analysis.ml) resolves ROWS, not clauses, and that is
   the whole of why it can learn something the clause path cannot. It therefore needs,
   for a propagation, the constraint that DID the propagating -- which for a PB solver is
   not "the facts the propagator read" but the row itself. lib/core/analysis.ml's graph
   answers the first question; this field answers the second, and nothing else in the
   codebase did.

   Three things about the shape, each deliberate:

     - it is a plain [(coeff, lit) list] and not a [Learned.t], because [Learned] depends
       on [Linear] which depends on this module. The dependency runs one way and this
       field must not turn it into a cycle. [Learned.of_pb_row] is the conversion and it
       lives where the cycle allows it.
     - it is a FUNCTION of the store, not a value, because an instance is packed before
       any store exists ([Compile] builds pending instances first) and because the
       expansion needs each variable's NAME. It is emphatically not a function of the
       store because it reads live domains: [Linear.pb_row] reads [Store.name] and the
       DECLARED bounds the instance froze at [make] time, and nothing else. A row that
       moved with the search would break I-X6 (an explanation reads a snapshot, never live
       domains), and every [pol] built on it would derive something other than what the
       .opb actually says.
     - [r_cid] is required, not optional. A row nobody can cite is a row no [pol] can be
       built from; an instance offering terms without an id would be offering arithmetic
       with no proof behind it.

   [None] -- the default -- means "this instance does not expose a PB row", which is the
   honest answer for [Ne] (a disequality is a pair of big-M rows, not one), for
   [Bool_clause] and for [Bool2int]. That is not a defect. It is exactly the condition
   under which PB analysis falls back to 1UIP clause learning (lib/core/learn.ml, M2-L3),
   and how often it is the answer is the fallback rate [Search] reports. D-0044 decided
   that the learned object is a PB inequality with the clause as its degree-1 case, so
   the clause path is permanent, and this field is the mechanism that makes it so. *)
type pb_row = { r_terms : (int * Baguette_proof.Lit.t) list; r_degree : int; r_cid : int }

(* A WATCH, as the engine's wake index keys it: the variable of one watched literal and
   the bound move that can FALSIFY it.

     [watch_any v]  any change of [v] may falsify it (the general case);
     [watch_lo v]   only a move of [v]'s LOWER bound can falsify it (an order literal
                    `v <= k`);
     [watch_hi v]   only a move of [v]'s UPPER bound can falsify it (`v >= k`).

   A watch is an int, three per variable, so the index is an array. What the engine does
   with it, and why it wakes exactly what a per-variable index woke, is
   lib/core/engine.ml's "The wake index by direction". The directional watches were item
   E1 of the complexity inventory (D-0140), built by M11-complexity-T3 (D-0142). *)
type watch = int

let watch_any v = 3 * Var.to_int v
let watch_lo v = (3 * Var.to_int v) + 1
let watch_hi v = (3 * Var.to_int v) + 2
let watch_var (w : watch) = Var.of_int (w / 3)

(* [rests], in the SECOND place of an [inst_watched] pair [(w, rests)], says the instance
   RESTS on the literal behind [w]: that literal is TRUE, so the instance (a satisfied
   learned clause, typically) has nothing to do and its advisor answers [false] for every
   change while the store keeps it true, and only a backtrack can undo it. The engine then
   indexes the instance under [w] alone, and wakes it again at the first propagation after
   a backtrack that popped the bound holding the literal up (see [Engine.rest_on]). Never
   a real slot: those are [>= 0]. D-0173 (M11-complexity-T17) measured that the learned
   clauses which "could not prune" were satisfied ones, and introduced this. *)
let rests : watch = -1

(* The engine holds a heterogeneous collection of propagators, so it needs them erased to
   a common type. Packing at registration time keeps [propagate] a plain closure call on
   the hot path instead of a first-class-module application. *)
type instance = {
  id : int;
  inst_name : string;
  inst_consistency : consistency;
  inst_vars : Var.t list;
  run : Store.t -> result;
  inst_row : Store.t -> pb_row option;
      (* See [pb_row] above. [pack] defaults it to "no row", so a propagator family that
         has not been taught its own row is not silently credited with one. *)
  inst_advise : Store.t -> Var.t -> bool;
      (* The ADVISOR (Gecode's term). Asked by [Engine] before a wake on [v] is queued:
         [false] drops the wake. It may answer [false] only if, every change since this
         instance's last run on a variable it names having been answered [false], a run
         now would change nothing and not fail (invariant I-P7). The default always
         answers [true]. Under BAGUETTE_DEBUG the engine runs every dropped wake anyway
         and raises if it did anything ([Engine.check_advise]). Introduced for learned
         clauses, which were where the propagator runs went (D-0104, M6-T20). *)
  inst_watched : (unit -> watch * watch) option;
      (* [Some w] when [inst_advise] answers [false] for EVERY variable except the two
         [w ()] returns (the same variable twice is allowed), whatever the store says:
         the two variables a watched-literal propagator currently watches, or
         [(w, rests)] for an instance resting on [w] (see [rests]). Each comes as a
         [watch], which also says which bound move can falsify the literal, so the engine
         asks only on that move when the watch is directional.
         The engine then wakes the instance only from changes of those two variables,
         asking [w] again after each run, instead of from its whole scope. The answers
         are the advisor's own, so the runs are the same; what goes is the asking, which
         was the per-node cost on the XOR codes (D-0138, M6-T22).
         [None], the default, is "my advisor may want any variable of my scope". Under
         BAGUETTE_DEBUG the claim is checked after every run ([Engine.check_watched]). *)
  inst_idempotent : bool;
      (* The CLAIM that one call of [run] reaches this instance's own fixpoint: run it
         again straight after, with nothing else having moved, and it prunes nothing and
         does not fail. [Engine] uses it to skip re-waking an instance off its own
         prunings (GCS's self-wake veto, M2-T6), and only HONOURS it when the scope has
         no aliased variable -- see [Engine.honours_claim]. A wrong claim is invisible in
         the answer and in the proof and visible only in pruning lost (GCS issue #889:
         767 -> 1 089 375 nodes), so under BAGUETTE_DEBUG every honoured claim is re-run
         and checked at the moment it is relied on ([Engine.check_claim]). The default is
         [false]: an instance that has not stated the claim is re-woken, which is never
         unsound, only slower. *)
  inst_attach : (unit -> unit) -> unit;
      (* [Engine.add] calls it ONCE, with the function that takes this instance out of
         that engine: its slot, its subscriptions and the closures it holds, so that the
         GC can reclaim them. An instance that may be removed keeps the function and calls
         it when its owner says so. The only such owner is the learned-constraint
         database, through [Retention.gate]'s wrapper: an evicted learned constraint
         leaves the engine as well as the proof (D-0226). The default, [attach_never],
         drops the function: a model propagator lives as long as its engine. *)
}

let no_row : Store.t -> pb_row option = fun _ -> None
let attach_never : (unit -> unit) -> unit = fun _ -> ()
let advise_always : Store.t -> Var.t -> bool = fun _ _ -> true

(* What [pack]'s [?advise] takes: the advisor ([inst_advise]) and, for a watched-literal
   advisor, the two variables it watches ([inst_watched]). A record, so that the packing
   site hands over both halves of one object ([Clause.Learned_clause.advise]) and cannot
   pass one without the other. *)
type advisor = {
  ask : Store.t -> Var.t -> bool;
  watched : (unit -> watch * watch) option;
}

let no_advisor = { ask = advise_always; watched = None }

(* The single-call idempotence claim is made AT THE PACKING SITE, by passing
   [~idempotent:true], and nowhere else: [Compile.pack_linear] and
   [Compile.pack_arith_row] claim it, every other site does not. The packing site is the
   one place that knows which face of a builtin it packs. A table by packed name, which is
   what preceded it (D-0098, M6-T18), could not tell the arithmetic ROW faces
   ([Arith.Times_row] and friends, which are [Linear.t] and qualify) from the arithmetic
   GUARD faces (reifications, which do not), because they share their builtin names.

   The argument for [Linear] is in its header ("Idempotence"): the slack is computed once
   from every term's MINIMUM contribution, the push on term i reads only the other terms'
   minima, and tightening x_i's upper bound (a_i > 0) or lower bound (a_i < 0) never moves
   x_i's own minimum -- so after one pass no term's bound can move again. That argument is
   about DISTINCT variables, and [Engine.honours_claim] refuses the claim for an aliased
   scope rather than trusting the packing site. [Pb] (aliased by construction: several
   literals can be rungs of one ladder), [Ne], the clause family, [Reif], [Alldiff] (two
   stages, the second deliberately not claiming), [Gcc], [Element], [Maxmin] and
   [Bool2int] make no claim. The default is [false]: an instance whose packing site says
   nothing is re-woken off its own prunings, which is never unsound, only slower. *)
let pack (type a) ?(row = no_row) ?(advise = no_advisor) ?(idempotent = false) ~id
    (module P : S with type t = a) (p : a) : instance =
  {
    id;
    inst_name = P.name;
    inst_consistency = P.consistency;
    inst_vars = P.vars p;
    run = (fun store -> P.propagate p store);
    inst_row = row;
    inst_advise = advise.ask;
    inst_watched = advise.watched;
    inst_idempotent = idempotent;
    inst_attach = attach_never;
  }

(* ------------------------------------------------------------ pass counters

   MEASUREMENT ONLY, and global on purpose: a propagator holds no handle on the engine or
   the search, and threading one through every [propagate] to carry two integers would be
   the wrong trade. [passes] counts snapshots taken by the propagators that apply every
   deduction of a snapshot in one pass (invariant I-P6, "one snapshot, every deduction":
   alldiff, cumulative, gcc, element); [deductions] counts the domain changes those passes
   made. Before M6-T19 every deduction cost its own pass, so [passes] was [deductions]
   plus one per call; the ratio now is what that task bought. Printed on stderr under
   --stats by bin/main.ml, never on stdout, so the determinism gate does not see them. *)
type pass_counters = { mutable passes : int; mutable deductions : int }

(* ------------------------------------------------------ cost classes

   Under BAGUETTE_PRIORITY=classes the engine keeps one FIFO per COST CLASS and always
   runs from the cheapest non-empty one (Gecode's PropCost, Chuffed's two priorities);
   under [off], the default, the classes are computed and never read (D-0246, which
   measured [classes] and kept [off]). The class is a statement about what ONE RUN costs,
   nothing else: it is never read by a propagator, a reason or the proof, so a wrong class
   costs time and never soundness.

   One rule, in two parts, for every instance:
     (1) a scope of at most two distinct variables is [Cheap], whatever the family: a run
         over two variables is constant work (Gecode's PropCost::binary);
     (2) otherwise the FAMILY's class, from the table below, which is the only place a
         family states its class. A family the table does not name (a test's propagator,
         a family added later) falls back on its declared consistency: [Bounds] and
         [Value] read bounds or test one value, so [Row]; [Domain] and [Checking] are
         the shape of the globals, so [Global]. A new family lands somewhere sound and
         its author moves it by adding its name here.

   The classes, cheapest first:
     [Cheap]   clauses over order literals, the Boolean clause family, learned clauses
               (watched literals, Chuffed's SAT engine runs these before any
               propagator), bool2int, the binary comparisons and their reifications;
     [Row]     rows whose pass is linear in the scope: int_lin_le/ne and the reified
               row, the arithmetic rows and guards, model PB rows, max/min, element and
               member (one pass over the index domain or the selectors);
     [Learned_row] learned PB rows: linear, but there may be tens of thousands of them, and
               a model row is more likely to prune than one of them;
     [Global]  the globals whose pass is superlinear: all_different's matching, gcc,
               cumulative, regular, circuit, table, inverse.

   Why a table by NAME is acceptable here when the idempotence claim was moved off one
   (see [pack]): a name could not tell an arithmetic row from an arithmetic guard, which
   differ in whether the claim is TRUE; they do not differ in cost class, and a wrong
   class is never unsound. The table lives here and not as a [val cost] in [S] because [S]
   is implemented outside lib/core (compile.ml, the test suites), and a field every
   implementer must state would change all of them for a scheduling hint. *)
type cost = Cheap | Row | Learned_row | Global

let n_cost_classes = 4
let cost_rank = function Cheap -> 0 | Row -> 1 | Learned_row -> 2 | Global -> 3

let cost_of_family ~name consistency =
  match name with
  | "clause" | "learned_clause" | "bool_clause" | "array_bool_or" | "array_bool_and"
  | "bool_eq" | "bool_not" | "bool2int" | "int_le" | "int_lt" | "int_ne" | "int_le_reif"
  | "int_eq_reif" | "int_ne_reif" ->
      Cheap
  | "int_lin_le" | "int_lin_ne" | "int_lin_le_reif" | "int_times" | "int_div" | "int_abs"
  | "pb" | "array_int_maximum" | "array_int_minimum" | "array_int_element" | "member" ->
      Row
  | "learned_pb" -> Learned_row
  | "all_different_int" | "global_cardinality" | "cumulative" | "regular" | "circuit"
  | "table" | "inverse" ->
      Global
  | _ -> ( match consistency with Bounds | Value -> Row | Domain | Checking -> Global)

(* The rule above, for an instance whose scope has [arity] distinct variables. *)
let cost_class (inst : instance) ~arity =
  if arity <= 2 then Cheap else cost_of_family ~name:inst.inst_name inst.inst_consistency

let pass_counters = { passes = 0; deductions = 0 }
let count_pass () = pass_counters.passes <- pass_counters.passes + 1
let count_deduction () = pass_counters.deductions <- pass_counters.deductions + 1
