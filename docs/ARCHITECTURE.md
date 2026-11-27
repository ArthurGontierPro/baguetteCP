# Architecture

How the pieces fit. `docs/SPEC.md` says *what*; this says *how*, and may change more
freely — but changes to §4 (explanations) need a decision record.

---

## 1. Module map

This block is the same text as the map in `CLAUDE.md`, "Where things are". If you add,
move or remove a module, change both, and check them against `ls lib/*/ lib/core/prop/`
rather than against the propagators alone. *Verified against the tree on 2026-11-27
(M22-review-T4, D-0253).* History in one line: the map drifted for months before
2026-09-18, listing three propagators that did not exist yet and missing eleven modules,
and the first re-verification missed the six learning modules of `lib/core`'s root.

```
bin/main.ml                 CLI: parse args, wire everything, print results

lib/flatzinc/   Baguette_flatzinc
  pos.ml error.ml           source positions; the single front-end error type
  ast.ml                    FlatZinc syntax tree, restricted to SPEC 2.1
  lexer.ml parser.ml        hand-written scanner + recursive descent (D-0006)
  model.ml                  the front end's output: vars, domains, constraints
  builder.ml                ast -> Model.t, and the normative rules of SPEC 2.1
  arith_aux.ml              the arithmetic family's sign and ladder Booleans, shared by
                            builder.ml and lib/scp/reader.ml (M23-inputs-T4, D-0230)
  compile.ml                Model.t -> store + PB encoding + propagator instances;
                            this is the flatzinc -> core edge
  output.ml                 solution printing in FlatZinc output format

lib/scp/        Baguette_scp (M23-inputs, D-0228 section 14, D-0230)
  sexp.ml                   .scp text -> s-expressions with positions: iterative, linear,
                            through a 64 KiB buffer, one item's tree alive at a time
  reader.ml                 .scp (cake_pb_cp's grammar, version 1) -> the same Model.t
                            builder.ml produces; refuses with a position what baguette
                            does not propagate. Depends on lib/flatzinc for Model

lib/core/       Baguette_core
  var.ml                    variable identity (abstract int)
  domain.ml                 bounds pair + lazily allocated hole set, a VERSION of a
                            per-variable hole log since D-0222 (ARCH §2)
  store.ml                  backtrackable store: domains + undo trail (ARCH §3)
  reason.ml                 WHICH FACTS justify a pruning, as declarative data, and
                            [justified], the one value a mutator takes (D-0026)
  explanation.ml    *****   THE Explanation ADT: HOW the checker is convinced, as a
                            cutting-planes expression over model rows and facts
                            (D-0026, M2-T8). Read SPEC §3.3 + ARCH §4 first. Check
                            `## Active claims` before touching this file. No new
                            constructor without a decision record.
  justify.ml                Explanation.t -> VeriPB rules -> constraint id. Lives in
                            core, not proof, because proof cannot see Explanation.
  trace.ml                  records what a branch learned so its nogood is plain RUP
                            (D-0018, M1-T13)
  learned.ml                the LEARNED-CONSTRAINT type: a PB inequality of which a
                            clause is the degree-1 case, plus its runtime instance and
                            its proof-side introduction/deletion (M2-L1, D-0044)
  learn.ml                  1UIP clause learning over order literals, its semantic
                            minimisation, its `rup` derivation and the backjump it
                            licenses (M2-L3). Removing root-level and re-derivable
                            literals from the learned clause is BAGUETTE_MINIMISE
                            (off, root, local, rec), `off` by default (D-0241)
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
                            learned constraint's lifetime, its proof id AND its engine
                            instance (an eviction removes both, D-0226). Policies are
                            swappable (`keep_all`, `fifo`, `lbd`, `tiered`) and the default
                            is `tiered` BY MEASUREMENT since D-0226 (`keep_all` before:
                            D-0051, D-0221) (M2-L4)
  view.ml                   VIEWS (+-x + k) and constants-as-variables, as a RENDERING
                            onto the base's order literals -- no PB variables of its
                            own, no name, so no sanitize table (M4-T0, D-0058)
  propagator.ml             the PROPAGATOR module type (288 lines — read it whole)
  engine.ml                 propagate-to-fixpoint loop and the queue (ARCH §5). The
                            queue is FIFO; BAGUETTE_PRIORITY=classes runs cheap
                            propagators first (four cost classes), off by default
                            (D-0246)
  search.ml                 DFS, branching, backtracking, every step proof-logged.
                            Restarts are opt-in (SPEC 3.4, D-0137): NRestart t unwinds
                            to level t and re-enters that node, no new proof rule.
                            CDCL loop `Search.cdcl` beside `dfs`: `--cdcl` or
                            BAGUETTE_CDCL=1, OFF by default (D-0219). With it, `--chrono
                            T` (BAGUETTE_CHRONO=T) backjumps one level instead of more
                            than T (chronological backtracking, D-0224)
  restart.ml                WHEN to restart: Luby, geometric, Glucose's LBD average
                            (with a Luby floor), the stable alternation (M10-T2)
  phase.ml                  phase saving: the value a variable was last fixed at,
                            read when its level is undone (M10-T2, D-0137)
  activity.ml               the activity heuristic: VSIDS score per variable,
                            learned-clause bumps, EVSIDS decay (M10-T3, D-0137)
  checked.ml                checked integer arithmetic + the overflow cap (M1-T23)
  interval.ml               interval arithmetic: mul, square, div of bounds (M4-T4a)
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
    alldiff.ml              all_different_int, DOMAIN consistent, two stages: Hall
                            intervals on the bounds with the multi-row Hall justification
                            (M4-T1, D-0061), then a maximum matching that prunes values
                            (M4-T2), skipped when it cannot prune (D-0215)
    gcc.ml                  global_cardinality by interval CAPACITY -- alldiff generalised;
                            counting rows over the ORDER encoding (M7-T16, D-0078)
    element.ml              array_int_element over a constant array, DOMAIN consistent.
                            The index is a VIEW, not an auxiliary (D-0058), and the
                            pruning is an interior hole in its own domain (M4-T3)
    maxmin.ml               array_int_maximum / array_int_minimum (and int_max/int_min as
                            the two-element case), BOUNDS consistent over one clause row per
                            value; minimum is maximum over negated views (M4-T9, D-0095).
                            Over bits: one SELECTOR row per operand + a clause, each
                            pruning one Resolve `pol` (M8-bits-encoding-T3, D-0134)
    cumulative.ml           cumulative (and disjunctive as cap 1, r 1): time-table filtering
                            over gcc's window indicators, one capacity row per time point,
                            CHECKING; the first Needs_derivation family whose CONFLICTS carry
                            facts, so they can be learned from (M4-T10, D-0096). Also diffn's
                            two RELAXATIONS: mznlib/fzn_diffn.mzn keeps std's pairs and adds
                            cumulative over order copies of x and of y (no module of its
                            own; the capacity rows are model rows, M18-coverage-T2, D-0213)
    regular.ml              regular (DFA) through mznlib's baguette_regular, DOMAIN
                            consistent over the letters and (n+1)*Q STATE FLAGS (store
                            variables, so a dead state is a trail entry); every pruning one
                            rup against its rows plus the backward-chain lemmas
                            Encoding.start_proof derives (M7-T28, D-0146). The reasons name
                            the LETTERS only, recursing into the dead flags' own tails (D-0151)
    inverse.ml              inverse(f, g) through mznlib's baguette_inverse: CHANNEL filtering
                            (j in f_i <=> i in g_j), CHECKING, every pruning one rup; compile.ml
                            adds all_different over each array whose pairwise rows are cited
                            ROOT LEMMAS (Encoding.add_cited_lemma) (M7-T28, D-0151)
    member.ml               member(x, y) through mznlib's baguette_member: DOMAIN consistent
                            over x, y and one SELECTOR per position (store variables, as
                            regular's flags), b_k -> x_k = y as six rows at most; a line that
                            walks a hole rests on threshold lemmas written AHEAD, and a value
                            of y two holes exclude on a derivation ahead (M7-T28, D-0159,
                            D-0170)
    table.ml                table(x, T) through mznlib's baguette_table: DOMAIN consistent over
                            x and one SELECTOR per tuple (store variables, as member's), one
                            DEF row s_t -> x = t per tuple; every pruning one rup with its
                            reasons on the letters (M18-coverage-T1, D-0206)
    circuit.ml              circuit through mznlib's baguette_circuit, beside all_different:
                            CHECKING plus Chuffed's PREVENT over MTZ POSITION store variables
                            (succ_u = v -> pos_v = pos_u + 1 in the .opb, the definition); a
                            subtour cut is ONE pol, the rows around the cycle divided by n,
                            written ahead (M18-coverage-T3, D-0217)
    linear.ml               int_lin_le. THE REFERENCE PROPAGATOR — copy this shape.
    lin_eq.ml               int_lin_eq (two model rows, see D-0011)
    ne.ml                   int_lin_ne and int_ne (VALUE consistency)
    int_le.ml int_lt.ml     degenerate linear constraints, delegate to Linear
    int_eq.ml               delegates to Lin_eq
    bool2int.ml             bool <-> int channelling
    clause.ml               clauses over ORDER literals (Bounds); the degree-1 face of
                            pb.ml, plus the bool_clause/array_bool_or/and/eq/not
                            family as Domain submodules (M2-L12)
    reif.ml                 the REIFICATION DISPATCHER: author supplies enforce-hold /
                            enforce-not-hold / entailment; framework does the collapse,
                            the contrapositive and the polarity (M3-T4, D-0057)
    reif_lin_le.ml          b <-> (sum a x <= c) as two big-M int_lin_le rows
    reif_lin_eq.ml          int_eq_reif / int_ne_reif, one arg apart (D-0057)
    order_reason.ml         bound-fact chains in the order encoding (D-0010)

lib/proof/      Baguette_proof
  lit.ml                    encoding literals; naming is NORMATIVE (PROOF-FORMAT §3)
  encoding.ml               which variable has which encoding; channelling
  opb.ml                    writes the .opb model file
  writer.ml                 writes the .pbp proof; owns the constraint-id counter
                            (I-X2: an id you receive is an id you must delete)
  text.ml                   one line's bytes, for writer.ml and opb.ml: integers and
                            literal names written in place, each variable's name prefix
                            rendered once (M20-pernode-T5, D-0209)
  e2e.ml                    the END-TO-END PREFIX under --e2e: derives each of baguette's
                            rows from cake_pb_cp's verified .opb; nothing in it is
                            trusted, every line is checked (M14-T3, D-0187)
  name_tbl.ml               the table keyed by a FlatZinc identifier: String.equal and
                            String.hash (Hashtbl.hash's value without its dispatch), for
                            Encoding, Justify and Store's name index (M20-pernode-T4, D-0236)
  checker.ml                resolves which veripb to use; mirrors scripts/checker.sh

test/unit/                  25 binaries: test_core test_domain test_engine test_prop
                            test_proof test_justify test_trace test_flatzinc
                            test_compile test_endtoend test_matrix test_mutation
                            test_output test_random test_interval test_learned
                            test_learn test_analysis test_ladder test_retention test_clause test_pb test_consistency
                            test_search_strategy (M10: restarts, phases, activity)
                            test_scp (M23-inputs: the .scp reader)
  mem_guard.ml              NOT a test binary: the shared Gc-alarm heap guard every
                            suite installs (M1-T53). All 25 announce arming under
                            BAGUETTE_TEST_HEAP_CAP_ANNOUNCE=1
  domain_helper.ml          NOT a test binary: Domain.of_list and change_of, test-only
                            constructors moved out of lib/ (M22-review-T5, D-0248)
test/models/                264 .fzn models  test/expected/  their expected outputs
test/scp/                   26 .scp models   test/scp/expected/  theirs (M23-inputs, D-0230)
mznlib/                     baguette's MiniZinc library: the fzn_*.mzn redefinitions that
                            route a global to a native propagator or to its decomposition
scripts/                    checker.sh verify_proof.sh run_model_tests.sh shrink.sh
                            mutate_proof.sh check_test_widths.py check_fmt.sh
                            check_determinism.sh check_unlimited.sh bootstrap.sh; the lanes
                            (diff, scaling, e2e, sym, fuzz)_lane.sh; compare_run.sh and
                            corpus_run.sh (Challenge and corpus runs) with their
                            *_selftest.sh; run_scp_tests.sh (the .scp models, `make scp`).
                            scripts/README.md is the operating manual for the node
tools/                      baguette.msc (the MiniZinc solver configuration); compare/
                            (Challenge scoring, the README's performance table); e2e/
                            (the cake_pb_cp end-to-end chain); symmetry/ (dejavu,
                            `make sym`); fuzz/; lp/ (opb2lp.py)
tools/scp/                  the .scp lanes: validate.py (an answer against the .scp alone),
                            fzn_lane.sh, random_lane.py, mutate.sh (D-0230)
bench/                      measurement harnesses and their results; bench/challenge/ and
                            bench/series/ hold the Challenge runs (README.md in each)
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
- a bitset of removed values, allocated lazily, only when a hole is actually punched.
  Since D-0222 the bitset belongs to a per-variable LOG that also records the removals in
  order, and a domain holds a VERSION of it (the first `k` removals): a removal appends
  16 bytes instead of copying the bitset, and a past version reads through the log (O(1)
  once a position table is built on the first deep read)

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

Domains were immutable values until D-0222, so a saved entry shared no mutable state with
the domain that replaced it, and I-T1 held by copying the hole bitset per removal. Since
D-0222 a saved entry shares its variable's hole LOG with the domain that replaced it, and
`undo_to` calls `Domain.undo`, which truncates the log back to the version the entry
restores; a domain from an undone branch raises `Domain.Stale_version` when read (I-T1's
second half).

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

So "keep trail records small" above is a goal the entry only partly meets. It has
**twelve fields** today (`lib/core/store.ml`, `type entry`): `var`, `old`, `now` and `why`
for undo and conflict analysis; `reason` and `concludes`, the facts a trace line negates
and the fact it states (proof-side); `prop`, the instance that made the entry; `ahead`, set
when the pruning's derivation must be written ahead of its trace line (I-X10, D-0082);
`sup_lo` and `sup_hi`, the supports that replaced the backward scan; `pos`, the entry's
own trail position (D-0090); and `cites`, conflict analysis's memo of what the reason cites
(D-0124). The arena indirection for explanations matters more, not less. If the trail ever
moves to `Bigarray`/`Bytes` (M6-T2, D-0001), `now`, `reason`, `concludes` and `cites` are
the awkward part of the move and should be planned for rather than discovered; the others
are plain ints or Booleans.

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

The constructors today (`lib/core/explanation.ml` is the reference; the record fields
`line` and `hid` that the written ones carry are left out here):

```ocaml
type t =
  | Decision of Lit.t                    (* an assumption of the search; no id, never a pol operand *)
  | Clause of Lit.t list                 (* these literals imply the pruning; renders to rup *)
  | Linear of (int * Lit.t) list * int   (* a PB constraint sum a_i l_i >= b *)
  | Cut of t * t * int * int             (* c1 * e1 + c2 * e2, the single-row combination *)
  | Model_row of int                     (* a model constraint of the .opb, cited by id *)
  | Combine of summand list * int        (* sum of summands, then divide: one pol step (D-0013) *)
  | Resolve of t list                    (* saturated derivations summed: resolution in one pol (D-0134) *)
  | Deferred of thunk                    (* computed only if actually needed *)
```

A `summand` is `Term (c, e)` (c times the line of another explanation, which is what
makes an explanation higher-order), `Weaken` (literal axioms that weaken a variable out of
a row), `Defining (c, l)` (the line that establishes a literal) or `Linear_term` (one term
of a linear row as the snapshot it read, rendered for the order or the bits encoding by
`Justify`, D-0132). The first sketch of September 2026 had a `Trivial` constructor and no
`Model_row`, `Combine` or `Resolve`.

`Deferred` MUST be memoised on force — a reason can be demanded more than once during
conflict analysis, and recomputing a propagator's reason is not cheap.

**Until its line is written** (M11-complexity-T13, D-0168). Once `Justify.emit` has
written a thunk's derivation, the thunk is *released*: it records the line (id, level)
and drops the tree. A later `emit` is answered by the line for as long as no wipe has
reached its level; after such a wipe, and for every reader that walks the tree
(`Explanation.lits`, `Pb_analysis.cited_ids`, a match on the forced head), the closure is
forced again, not memoised. That writes the same proof because a thunk closes over a
snapshot (I-X6), so a second forcing is the same derivation. `BAGUETTE_DEBUG` re-forces
every release and every later read against the original.

**Every node a line is written for carries it** (M11-complexity-T15, spike, branch
`wave55-dag`). `Clause`, `Linear`, `Cut`, `Combine` and `Resolve` are inline records with
a mutable `line` (the record a thunk keeps) and an identity `hid`, so `Justify`'s memo is
a field read on the node and no table holds a node: what T13 needed to take out of the
table (a frame of what a forcing built, a second forcing where it might have captured)
is gone. Build nodes through the smart constructors; a pattern names the fields it reads
and ends in `_`. The constructors also return a written node of the same content
(hash-consing, D-0172), so an identical derivation is one line. It is on by default;
`BAGUETTE_HASHCONS=0` turns it off and gives back the proof written before D-0172, byte for
byte. `lib/core/explanation.ml`'s header gives the argument reader by reader. The type's
listing above is the 2026-09 sketch; the module is the reference.

**Settled**: the question this section used to leave open, whether `Cut` and `Deferred` are
enough or explanations should take other explanations as arguments (D-0003), was resolved by
D-0026 on 2026-09-16. Which facts justify a pruning is declarative data (`Reason.t`), and
how the checker is convinced is this type, whose `Term` summand recurses into another
explanation. A new constructor still needs a decision record.

## 5. Propagation loop

As of M2-T6 (D-0094) `engine.ml` uses a **FIFO** queue of propagator ids. Since M19-config-T9
(D-0246) a cost-class ordering exists as an option, `BAGUETTE_PRIORITY=classes` (default `off`,
the FIFO): `Propagator.cost_class` files every instance in one of four classes (Cheap, Row,
Learned_row, Global), the queue is one FIFO per class, the loop runs the cheapest non-empty one,
and the dirty seed slots below enter their class queues in id order before anything runs. Each `propagate` call, made once per search node, walks one **seed
slot** per instance in id order, ahead of the FIFO. As of M6-T18 (D-0098) it runs only the
**dirty** slots:

- the instance watches a variable that a trail entry above the last joint fixpoint moved,
  after the trigger mask has been applied;
- the instance is not yet **born** at that fixpoint. This covers an instance added with
  `Engine.add`, and an instance born after a fixpoint that a backjump has since returned to;
- a run earlier in the same call woke the instance before its slot came up.

The engine records each `Fixpoint` return as a (trail length, epoch) pair. The trail's
**low-water mark** comes from `Store.take_low_water`, which is per reader and maintained in
`undo_to`. It tells the engine which of those records are still prefixes of the store's
trail.

Skipping a clean slot is **exact**. The instance's watched domains are the ones it last
reached a fixpoint on, and its output depends on nothing else (D-0034, and the audit in
D-0098). So the run that the old full seed made at that slot pruned nothing. Every run that
is made happens in the same order, on the same domains, as under the full seed. Trail,
proof and search are therefore byte-identical, and the no-op runs are gone.

The loop pops an id and runs that instance, bracketed by `Store.with_running` so that each
trail entry is stamped with its author (M2-T7). It checks that attribution and then
re-queues the watchers of each variable the run changed. The trail is diffed from the run's
starting position, and the walk preserves wake order. Two filters drop wakes:

- the **trigger mask** (M2-T5, D-0034) drops a wake by the KIND of change. A `Bounds`
  instance is not woken by an interior hole.
- the **self-wake veto** (M2-T6) drops a wake by WHO made the change. An instance whose
  idempotence claim (`Propagator.inst_idempotent`) is honoured is not re-woken by its own
  prunings. A claim is honoured only when the instance's scope names no variable twice (the
  aliased-scope rule). A claim is made at the packing site, `Compile.pack_linear` and
  `pack_arith_row` (D-0098). It is no longer looked up in a table by name.

Failure aborts the loop and hands the failing `Store.conflict` to `search.ml`.
`BAGUETTE_DEBUG` adds three checks:

- every skipped seed slot is re-run, and it must prune nothing (`check_skip`);
- every honoured claim is re-run at the moment the veto relies on it (`check_claim`);
- on a fixpoint, `check_fixpoint` re-runs every instance and requires that nothing moves
  (I-P2).

Under `BAGUETTE_CONSISTENCY` the M2-T10 oracle checks each declared level.

`Engine.counters` keeps the following per engine, and `--stats` prints them: runs,
effectful runs, contradicting runs, wakes, masked wakes, vetoed wakes, seeded runs (seed
slots actually run) and skipped slots (`c_skipped`, not printed). D-0094 measured seeding
at 75–85 % of runs. The before and after for the incremental seed are in D-0098.

## 6. Proof writing

`writer.ml` owns the proof file and the **constraint id counter**. Every rule emission
returns a `Cid.t` — an abstract id. The rule is: *an id you received is an id you are
responsible for deleting.* Since OCaml will not enforce that statically, it is enforced
dynamically in debug builds: the writer tracks live ids and asserts the set is empty at
`conclusion` time. Turn that on with `BAGUETTE_PROOF_AUDIT=1`.

This is the one place where OCaml costs us relative to Rust (D-0001 records that
trade-off explicitly), so it gets a runtime check instead.
