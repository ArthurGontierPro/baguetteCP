# Architecture

How the pieces fit. `docs/SPEC.md` says *what*; this says *how*, and may change more
freely — but changes to §4 (explanations) need a decision record.

---

## 1. Module map

*Verified against the tree on 2026-09-18, and re-verified the same day after M2-L11.* **That first verification missed six modules** -- the whole M2L learning vertical (`learned`, `learn`, `analysis`, `reduce`, `pb_analysis`) plus `ladder` -- which is worth knowing about a map that says it was checked: it was checked against the propagators and not against `lib/core`'s root. They are listed below now. This section was stale for long enough that
`CLAUDE.md` carried its own replacement map and told readers to trust that one over this —
it listed three propagators that have never existed (`alldiff`, `element`, `clause`) and
omitted eleven modules that do, including `reason.ml`, which half of `lib/core` now depends
on. If you change the tree, change this. A map nobody trusts costs more than no map.

```
bin/main.ml                 CLI: parse args, wire everything, print results

lib/flatzinc/   Baguette_flatzinc
  pos.ml error.ml           source positions; the single front-end error type
  ast.ml                    FlatZinc syntax tree, restricted to SPEC 2.1
  lexer.ml parser.ml        hand-written scanner + recursive descent (D-0006)
  model.ml                  the front end's output: vars, domains, constraints
  builder.ml                ast -> Model.t, and the normative rules of SPEC 2.1
  compile.ml                Model.t -> store + PB encoding + propagator instances;
                            this is the flatzinc -> core edge
  output.ml                 solution printing in FlatZinc output format (SPEC 2.2)

lib/core/       Baguette_core
  var.ml                    variable identity (abstract int)
  domain.ml                 bounds pair + lazily allocated hole set (section 2)
  store.ml                  backtrackable store: domains + undo trail (section 3)
  reason.ml                 WHICH FACTS justify a pruning, as declarative data, and
                            [justified] -- the one value a mutator takes. D-0026's
                            first half; [Explanation] is the second
  explanation.ml    *****   THE Explanation ADT: HOW the checker is convinced, as a
                            cutting-planes expression. Read SPEC 3.3 + section 4
                            first. No new constructor without a decision record
  justify.ml                Explanation.t -> VeriPB rules -> constraint id. Lives in
                            core, not proof, because proof cannot see Explanation
  trace.ml                  records what a branch learned so its nogood is plain RUP
                            (D-0018)
  learned.ml                the LEARNED-CONSTRAINT type: a PB inequality of which a
                            clause is the degree-1 case, plus its runtime instance and
                            its proof-side introduction/deletion (M2-L1, D-0044)
  learn.ml                  1UIP clause learning over order literals, its semantic
                            minimisation, its `rup` derivation and the backjump it
                            licenses (M2-L3)
  analysis.ml               the implication graph and the cut, AS DATA. The criterion
                            is a swappable record carrying its own postcondition
                            (M2-L2)
  reduce.ml                 REDUCTION as a named, swappable component: `division` and
                            `roundToOne`, the pluggable field being outcome.derive
                            (M2-L5)
  pb_analysis.ml            PB conflict analysis: eliminate the pivot by linear
                            combination + reduction, clause path as fallback. Stops on
                            SLACK, never on counting conflict-level literals -- see the
                            header, and do not "optimise" that back (M2-L6)
  ladder.ml                 the order-encoding ladder chain AS A ROW, so a PB reason
                            can propagate: lifts a Linear reason onto the ladder rungs
                            that actually carry its strength (M2-L11, D-0028/D-0010)
  retention.ml              the learned-constraint DATABASE, and the SINGLE owner of a
                            learned constraint's lifetime. Policies are swappable
                            (`keep_all`, `fifo`, `lbd`) and the default is `keep_all`
                            BY MEASUREMENT, not by omission -- see D-0051 (M2-L4)
  view.ml                   VIEWS (+-x + k) and constants-as-variables, as a RENDERING
                            onto the base's order literals -- no PB variables of its
                            own, no name, so no sanitize table (M4-T0, D-0058)
  propagator.ml             the PROPAGATOR module type (65 lines -- read it whole)
  engine.ml                 propagate-to-fixpoint loop and the queue (section 5)
  search.ml                 DFS, branching, backtracking, every step proof-logged.
                            NOT restarts: SPEC 3.4 disables them, and whether that
                            survives clause learning is the open question D-0045
  checked.ml                checked integer arithmetic + the overflow cap
  interval.ml               interval arithmetic: mul, square, div of bounds
  debug.ml                  BAGUETTE_DEBUG-gated invariant checks
  prop/                     one module per constraint family:
    pb.ml                   the LEARNED PB ROW AS A PROPAGATOR: counter/slack over
                            Lit.t, reading LIVE domains and the order ladder. The
                            solving-side object of D-0054; D-0055 spends D-0044's
                            "no new propagator family" bet knowingly (M2-L13)
    arith.ml                int_times / int_div / int_abs. The CASE SPLIT LIVES IN THE
                            MODEL: guarded linear rows over M3-reified Booleans, so every
                            pruning is Linear's and no Explanation constructor was needed
                            (M4-T4b, D-0060)
    alldiff.ml              all_different_int, BOUNDS consistent, with the multi-row Hall
                            justification. Stage 1 of two; M4-T2 sequences beside it.
                            The row that proved Combine/Weaken/Model_row carry a real
                            global (M4-T1, D-0061)
    linear.ml               int_lin_le. THE REFERENCE PROPAGATOR -- copy this shape
    lin_eq.ml               int_lin_eq (two model rows, see D-0011)
    ne.ml                   int_lin_ne and int_ne (VALUE consistency)
    int_le.ml int_lt.ml     degenerate linear constraints, delegate to Linear
    int_eq.ml               delegates to Lin_eq
    bool2int.ml             bool <-> int channelling
    clause.ml               clauses over ORDER literals (Bounds); the degree-1 face of
                            pb.ml, plus the bool_clause/array_bool_or/and/eq/not family
                            as Domain submodules (M2-L12)
    reif.ml                 the REIFICATION DISPATCHER (M3-T4, D-0057)
    reif_lin_le.ml          b <-> (sum a x <= c) as two big-M int_lin_le rows
    reif_lin_eq.ml          int_eq_reif / int_ne_reif, one arg apart
    order_reason.ml         bound-fact chains in the order encoding (D-0010)

lib/proof/      Baguette_proof
  lit.ml                    encoding literals; naming is NORMATIVE (PROOF-FORMAT 3)
  encoding.ml               which variable has which encoding; channelling
  opb.ml                    writes the .opb model file
  writer.ml                 writes the .pbp proof; owns the constraint-id counter
                            (I-X2: an id you receive is an id you must delete)
  checker.ml                resolves which veripb to use; mirrors scripts/checker.sh
```

Dependency direction is strictly `flatzinc -> core -> proof`. `core` must not depend on
`flatzinc`. `proof` must not reach back into `core`'s mutable state — it receives values.

That direction has a consequence worth stating once, because it has surprised two tasks:
`lib/proof/` **cannot call `Baguette_core.Checked`**. A proof-side module needing checked
arithmetic must get the value already checked from its caller, or do its own.

---

## 2. Domains

`Domain.t` is a bounds pair plus an optional hole set:

- `lo`, `hi` as ints — the common case, and the only thing most propagators read
- a bitset of removed values, allocated lazily, only when a hole is actually punched

Rationale: the overwhelming majority of propagation in a linear-heavy FlatZinc workload
is bounds reasoning. Paying for a full bitset per variable up front is wasted memory and
worse cache behaviour. Variables that reach `all_different` or `element` get the bitset.

Operations return a `change` describing what moved (`NoChange | Bound of ... | Holes of ...`)
so the engine knows which propagators to re-queue and the proof layer knows which
literals became true.

## 3. Store (the trail)

`Store.t` owns the domain array and the undo trail. Every mutation pushes a record of
the variable and its previous `Domain.t`, and `backtrack_to level` replays them in
reverse. Decision levels are marks into that array.

Domains are immutable values, so a saved entry shares no mutable state with the domain
that replaced it. That is what makes I-T1 hold without deep copying.

Each entry records the **explanation id** of the change, so conflict analysis can walk
back through the reasons. Explanations live in a side arena (`Explanation.Arena`), not
inline, to keep trail records small and uniform. A level mark covers both the trail and
the arena, so backtracking rewinds them together and reasons neither orphan nor
accumulate (I-T3).

Since M1-T13 an entry carries two further fields that exist **only for the proof**
(D-0018): `now`, the domain the pruning produced — the claim literal of a trace line is a
function of it, and `old` alone cannot give it — and `facts`, a thunk for the bound facts
the propagator read. **M2-T7 then added a sixth, `prop`**: the id of the propagator
instance that made the entry, stamped by `Store.apply` from a slot the engine sets around
each `run`, so no mutator takes an id and no propagator can pass the wrong one. It is not
proof-side — M2-T3 resolves an entry's reason constraint through it, which is why
`Engine.check_attribution` reads it back on every propagation and not only under
`BAGUETTE_DEBUG`.

**M2-T8 then reshaped the record again.** `facts`, a thunk, became `reason : Reason.t`,
a list of frozen facts that materialises on demand and closes over nothing — so the
laziness moved from a closure per pruning to a materialisation point, and I-X6 on that
half became a type property. And `sup_lo` / `sup_hi` were added: the trail position of
the entry that established each bound, maintained by `apply` and restored by `undo_to`,
which is what let `linear.ml`'s per-pruning backward trail scan be deleted.

So "keep trail records small" above is now a goal the entry only partly meets: **eight
fields** — `var`, `old`, `now`, `why`, `reason`, `prop`, `sup_lo`, `sup_hi` — two of them
proof-side, one for conflict analysis and two for support. The arena indirection for
explanations matters more, not less. If the trail ever moves to `Bigarray`/`Bytes`
(M6-T2, D-0001), `now` and `reason` are the awkward part of the move and should be planned
for rather than discovered; `prop`, `sup_lo` and `sup_hi` are plain ints and are the easy
part.

## 4. Explanations

This is the design centre of the project.

An explanation answers: *why was this value removed?* in a form the proof layer can turn
into a VeriPB rule. Three concerns pull on the type:

1. **Cost.** Most prunings are never asked for a reason — they are never involved in a
   conflict, and never need a proof step beyond the propagator's own logged constraint.
   Computing a full reason eagerly for every pruning is the classic way to make a
   proof-logging solver ten times slower than its unlogged sibling.
2. **Composition.** The reason for a pruning is often "because of *this* other pruning,
   plus a cut" — reasons refer to reasons.
3. **Checkability.** Whatever the shape, it must come out as `pol`/`rup`/`red` steps.

### Deferred explanations

The type therefore has a deferred constructor: an explanation may be a *thunk* that,
when forced, produces the concrete reason. OCaml makes this cheap and readable, which is
a large part of why the language was chosen (see D-0001).

```ocaml
type t =
  | Trivial                              (* from the model constraint itself *)
  | Clause of Lit.t list                 (* a set of literals that imply the pruning *)
  | Linear of (int * Lit.t) list * int   (* a PB constraint: sum a_i l_i >= b *)
  | Cut of t * t * int * int             (* linear combination of two reasons *)
  | Deferred of (unit -> t)              (* computed only if actually needed *)
```

`Deferred` MUST be memoised on force — a reason can be demanded more than once during
conflict analysis, and recomputing a propagator's reason is not cheap.

**Open**: whether `Cut` and `Deferred` are enough, or whether explanations should be
parameterised over the reasons they consume (a genuinely higher-order form). That is
decision **D-0003**; do not build past M3 without settling it.

## 5. Propagation loop

A priority queue of propagator ids, ordered by cost class (cheap bounds propagators
before `all_different`). `engine.ml` pops, runs, applies the resulting changes to the
trail, and re-queues the propagators watching the changed variables.

Failure aborts the loop and hands the failing explanation to `search.ml`.

## 6. Proof writing

`writer.ml` owns the proof file and the **constraint id counter**. Every rule emission
returns a `Cid.t` — an abstract id. The rule is: *an id you received is an id you are
responsible for deleting.* Since OCaml will not enforce that statically, it is enforced
dynamically in debug builds: the writer tracks live ids and asserts the set is empty at
`conclusion` time. Turn that on with `BAGUETTE_PROOF_AUDIT=1`.

This is the one place where OCaml costs us relative to Rust (D-0001 records that
trade-off explicitly), so it gets a runtime check instead.
