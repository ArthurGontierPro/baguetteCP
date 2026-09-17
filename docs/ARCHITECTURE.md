# Architecture

How the pieces fit. `docs/SPEC.md` says *what*; this says *how*, and may change more
freely — but changes to §4 (explanations) need a decision record.

---

## 1. Module map

```
bin/main.ml                    CLI: parse args, wire everything, print results

lib/flatzinc/   Baguette_flatzinc      (standalone: does not depend on core yet)
  pos.ml  error.ml             source positions; one error type carrying a Pos.t
  ast.ml                       FlatZinc syntax tree
  lexer.ml  parser.ml          hand-written scanner + recursive descent (D-0006)
  model.ml                     the front end's output: vars, domains, constraints
  builder.ml                   ast -> Model, and the SPEC 2.1 normative rules

lib/core/       Baguette_core
  var.ml                       variable identity (abstract int)
  domain.ml                    finite integer domain
  store.ml                     backtrackable store: domains + undo trail
  explanation.ml       *****   the Explanation type. Read docs/SPEC.md 3.3 first.
  propagator.ml                the propagator interface (module type PROPAGATOR)
  prop/                        one module per constraint family
    linear.ml  alldiff.ml  element.ml  clause.ml ...
  justify.ml                   Explanation -> proof rule(s). Lives here, not in
                               lib/proof/, because the dependency runs core -> proof:
                               proof cannot see Explanation.
  engine.ml                    propagate-to-fixpoint loop, the queue
  search.ml                    branching, backtracking, restarts
  debug.ml                     BAGUETTE_DEBUG-gated invariant checks

lib/proof/      Baguette_proof
  lit.ml                       order/direct encoding literals; naming is normative
  opb.ml                       write the .opb model file
  encoding.ml                  which variable has which encoding; channelling
  writer.ml                    write the .pbp proof: emit rules, hand back constraint ids
```

Dependency direction is strictly `flatzinc -> core -> proof`. `core` must not depend on
`flatzinc`. `proof` must not reach back into `core`'s mutable state — it receives values.

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
