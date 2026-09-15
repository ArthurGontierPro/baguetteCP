# Worklog

Coordination between concurrent Claude sessions. **Append only.** Add rows at the bottom
of a section; never reflow, reorder or rewrite rows you did not write. That is what makes
git merge two sessions' edits instead of conflicting.

Read this file at the start of every session. Claim before you edit. See `CLAUDE.md`.

---

## Active claims

| Task | Files being touched | Session | Since |
|---|---|---|---|
_No session is holding anything right now._ The three rows that stood here
(`integration`, M1-T12, M1-T13) were stale: all three had shipped, and M1-T13 was already
listed under Completed. Cleared 2026-09-15 by the orchestrator — see the handoff note
"the claims table had rotted".

## Cross-session requests

Need a change in a file someone else has claimed? Write it here and move on to other
work. The owning session picks it up.

| Request | For file | From | Status |
|---|---|---|---|
| `lib/proof/lit.ml` is a shared dependency: agent-proof may **add** to it but must not change the existing signatures of `pbvar`, `t`, `ge`, `le`, `eq`, `ne`, `negate`, `to_string`, `var_name`, since agent-core compiles against them | `lib/proof/lit.ml` | orchestrator | standing |
| `WORKLOG.md`, `docs/**`, `dune-project`, `Makefile`, `scripts/**` and all committing are held by the orchestrator this round — agents touch none of them | — | orchestrator | standing |
| **All `dune` files are orchestrator-owned.** `lib/core/dune` already has `(include_subdirs unqualified)` so a new `lib/core/prop/*.ml` needs no dune edit, and `test/unit/dune` already names `test_prop` and `test_justify`. Need another module named? Ask here | `**/dune` | orchestrator | standing |
| `lib/proof/encoding.ml` is now claimed by agent-encoding, and `lib/core/justify.ml` compiles against `Encoding.is_declared`: agent-encoding may **add** to encoding.ml but must not change the signature of anything already there | `lib/proof/encoding.ml` | orchestrator | standing |
| `lib/core/justify.ml`, `lib/core/explanation.ml`, `lib/core/prop/order_reason.ml` and `lib/proof/**` are **read-only** for both sessions this round: read them freely, edit none of them. Need a change? Write it here | — | orchestrator | standing |
| M1-T14 is split in two along a contract stated in full in the dispatch, not merely a type (the D-0009 lesson): agent-compile owns `lib/flatzinc/compile.ml` only; agent-output owns `lib/flatzinc/output.ml` and the `check_assignment` addition to `lib/flatzinc/model.ml` only. Neither touches `bin/main.ml`, any `dune` file, or the other's files; the orchestrator owns the wiring and the integration | `lib/flatzinc/**` | orchestrator | standing |
| M1-T7 is split across two sessions. The contract between them is the **existing** `Explanation.t` ADT in `lib/core/explanation.ml`, which neither may change: agent-core builds `Linear`/`Cut` values, agent-justify renders any of them. A change there is a cross-session request, not an edit | `lib/core/explanation.ml` | orchestrator | standing |
| **This round's split (D-0018).** agent-trace owns the trace vertical in `lib/core/`; agent-ne owns the direct encoding and `int_ne`; agent-mutate owns the mutation harness. The contract between agent-trace and agent-ne is that `Encoding` and `Lit` may only be **added** to — `Encoding.is_declared`, `Lit.ge/le/eq/ne/negate/to_string/owner` keep their current signatures, since `justify.ml` compiles against them | `lib/proof/encoding.ml`, `lib/proof/lit.ml` | orchestrator | standing, this round |
| `lib/core/explanation.ml` is **frozen again** this round. D-0018's derivation needs no new constructor: `Combine`/`Weaken`/`Model_row` already express it, and the new work is *where and when* they are emitted, not what they say. If the trace genuinely cannot be said with the current ADT, that is a cross-session request and a decision record, not an edit | `lib/core/explanation.ml` | orchestrator | standing, this round |
| Each session builds into its own `--build-dir` (`dune build --build-dir=/tmp/baguette-build-<tag> <target>`). Three sessions share `_build/`'s global lock this round, so a bare `dune build` will fail for reasons that are not yours | — | orchestrator | standing, this round |
| Clarifying this round's split: `lib/core/prop/linear.ml` belongs to **agent-trace**, not agent-ne. A D-0018 trace line states `claim ∨ ¬(reason)` where the reason is the *other terms' current bound literals* — knowledge only the propagator has, and which `Explanation.t` deliberately does not carry in that shape (`Weaken` holds the declared-width chain the `pol` needs, which is a different projection). agent-ne owns `lib/core/prop/ne.ml` and no other file in `prop/` | `lib/core/prop/linear.ml` | orchestrator | standing, this round |
| M1-T16 runs alone: no other session is active, so agent-tests may add new files under `test/models/` and `test/expected/` (new files only — it must not edit an existing model, an existing expected output, or `PENDING`). Everything under `lib/` stays read-only: this task finds bugs and pins them, it does not fix them | `test/**` | orchestrator | standing, this round |
| `test/unit/test_matrix.ml`'s empty-cell note (line ~1192) is stale: it says four `int_ne` cells (|a| > 1, common factor, offset domains, negative domains) are left unfilled because "every disequality pruning that moves a bound **currently** emits a factless trace line". M1-T17 fixed that and inverted `known_bug_ne_trace_facts` itself, so the stated reason no longer holds and those cells are fillable. Not touched here — M1-T11 claimed neither the matrix nor `lib/` | `test/unit/test_matrix.ml` | agent-ne-wiring | open |

## Completed

| Task | Session | Date | Summary |
|---|---|---|---|
| M0-T1 | setup | 2026-09-14 | Project skeleton, docs, dune files, test harness, `.claude/` setup |
| M0-T2 | orchestrator | 2026-09-14 | opam 2.5.2 + OCaml 5.1.1 switch `baguette`; bootstrap.sh rewritten to fetch the opam binary |
| M0-T3 | all | 2026-09-14 | Everything compiles; 253 unit checks pass |
| M0-T4 | orchestrator | 2026-09-14 | `make check` green, with `test/models/PENDING` for not-yet-working models |
| M1-T1, M1-T2, M1-T3 | agent-core | 2026-09-14 | Domain (bitset holes), Store (trail + explanation arena), Explanation (memoised Deferred) |
| M1-T4, M1-T5 | agent-proof | 2026-09-14 | Encoding, OPB writer, proof writer; proofs accepted by veripb 2.2.2 |
| M1-T6 | agent-flatzinc | 2026-09-14 | Hand-written lexer/parser/builder; parses all five test models |
| M1-T7a | agent-core | 2026-09-14 | `int_lin_le` bounds propagator, deferred explanations, 33 checks incl. brute-force soundness |
| M1-T7b | agent-justify | 2026-09-14 | `Justify`: memo, level-wipe lockstep, `Linear` as faithful `rup` (D-0009) |
| M1-T7c | agent-encoding | 2026-09-14 | `Encoding.expand_int_lin_le`: integer term to PB row over the order encoding |
| M1-T7 | orchestrator | 2026-09-14 | Chain fix (D-0010) + cross-session repairs; a real pruning's reason is accepted by veripb |
| M1-T14 | orchestrator + agent-compile + agent-output | 2026-09-15 | The CLI is wired: `.fzn` in, solution + verified proof out. 5 models pass, 564 checks |
| M1-T13 | agent-trace + orchestrator | 2026-09-15 | D-0018/D-0021: one `rup` line per pruning, root prunings included. `chain_sat` and the three D-0012 parity models verify; no veripb xfail left anywhere |
| M1-T9 | agent-ne | 2026-09-15 | D-0019: `int_ne`/`int_lin_ne` over the **order** encoding — the direct encoding is not what a disequality needs. 182 checks. CLI wiring still open |
| M1-T15 | agent-mutate | 2026-09-15 | D-0020: mutation harness + control lane, 18 checks. Found `lin_unsat`'s refutation has a unit of slack |
| M1-T16 | agent-tests | 2026-09-15 | Case matrix + randomised differential tester, 152 checks, 17 verified break-it mutations. Found 3 real bugs (2 new), all pinned; gate is red until M1-T17 |
| M1-T17 | agent-fix + orchestrator | 2026-09-15 | D-0022/I-X7/I-P5: `remove_with_facts`, and a clausal root conflict closed by the empty clause. Gate green |
| M1-T11 | agent-ne-wiring | 2026-09-15 | `int_ne`/`int_lin_ne` posted by `compile.ml` instead of rejected, + five disequality models. 14/14 models verify, `PENDING` empty, 864 unit checks. On branch `worktree-m1-t11-ne-wiring` |
| M1-T12 | agent-explain + orchestrator | 2026-09-15 | D-0015: `Combine`/`Weaken`/`Model_row` made real and the root conflict wired to its derivation; two UNSAT proofs verify. Row added 2026-09-15 — the task shipped but was never released from Active claims |
| integration | orchestrator | 2026-09-15 | `test/unit/test_endtoend.ml` is green as part of the 864-check suite. Row added 2026-09-15 — released late, same reason |

## Handoff notes

Newest at the bottom. Two or three lines: what changed, what surprised you, what the next
session should know before touching the same area.

**2026-09-14 — setup**
Scaffolded the project. Two things the next session must know:
(1) There is **no OCaml toolchain on this machine** — `ocaml`, `opam` and `dune` are all
absent. Run `scripts/bootstrap.sh` first. M0-T2.
(2) The OCaml under `lib/` was written **without a compiler available to check it**.
Treat it as a typed sketch of the intended shape, not as working code; M0-T3 is making it
actually compile, and correcting it is expected rather than a sign something went wrong.
`veripb` is already installed (`~/.local/bin/veripb`, format 2.0) and works.

**2026-09-14 — orchestrator**
Toolchain installed: opam 2.5.2 binary in `~/.local/bin`, switch `baguette` on OCaml
5.1.1 being built by `scripts/bootstrap.sh`. `bootstrap.sh` now downloads the opam
release binary rather than piping the installer script, which is what actually worked
here; `bubblewrap` is absent so sandboxing stays disabled.
Three agents dispatched in parallel on disjoint file sets (see Active claims). They do
not commit — the orchestrator commits each area as it lands, to avoid racing on the git
index.

**2026-09-14 — orchestrator, after the first parallel round**

Three agents ran concurrently on disjoint file sets and none collided, but file-level
claims turned out not to be enough: **dune holds a global lock on `_build/`**, so
concurrent builds corrupt `_build/.lock` and both fail. Build into your own
`--build-dir` while others are working. This is now in CLAUDE.md.

Seven errors in `docs/PROOF-FORMAT.md` were found by building against the real checker
and are fixed. Two of them silently corrupt a proof rather than failing it — the worst
being that an `.opb` line with `=` counts as **two** constraints for the `f` rule, which
shifts every later id so `pol` steps quietly reference the wrong constraints. If you are
touching the proof layer, read section 2's "Traps" before anything else.

`make check` is green but five model tests are `xfail` via `test/models/PENDING` — the
solver does not solve yet. Delete lines from that file as propagators land; the runner
fails if a listed model starts passing, so the list cannot rot.

**Next is M1-T7** (`int_lin_le` + its `pol` justification). It is the reference
propagator — every later one copies its shape — so it is worth doing carefully and alone
rather than in parallel with M1-T8/T9.

**2026-09-14 — orchestrator, after the M1-T7 round**

Two agents ran on disjoint files, both reported success, both were individually good, and
**their halves did not compose**. `Explanation.Linear` was read as "the bound facts" by
the propagator and as "the model row restated" by the bridge. veripb accepted the bridge's
output because restating a constraint is trivially valid, so nothing went red; the id it
handed back simply did not assert what the explanation claimed. Composed, the two would
have emitted twice the model row and justified nothing.

The lesson for the next round is not "claim files more carefully" — the file claims worked
perfectly. It is that a shared *type* is not a shared *contract*. When a task is split, the
split must state what each constructor means operationally, with an example of the emitted
text, or two sessions will agree on the type and disagree on the semantics.

D-0009 records the underlying finding, which was checked against the checker rather than
argued: **a bare literal in a `pol` is the trivial axiom `lit >= 0`**, so bound facts can
only enter a `pol` as constraint ids. That is why `Linear` cannot render as a `pol` today,
and why `Cut`'s missing division matters. Both belong to D-0003, still open — this is the
first time leaving it open has cost real work.

Also found: nothing expands `sum a_i x_i` into PB literals over the order encoding, so the
model row an `int_lin_le` proof must cite cannot be written at all yet. That is now M1-T7c
and it blocks the end-to-end check. `make check` is green, and `test/models/PENDING` is
unchanged at five — the solver still does not solve.

**2026-09-14 — orchestrator, M1-T7 closed**

It works: `Linear.propagate` prunes, its explanation renders, and veripb accepts the
result. The two-step case that broke is now a counted I-X1 check emitting
`rup +1 x2_ge_1 +1 x2_ge_2 >= 2 ;` followed by `pol 10 11 +`.

Three bugs in three rounds, none of which a green test suite caught:

1. Two sessions read `Explanation.Linear` differently and veripb accepted the mismatch,
   because re-stating a constraint is trivially valid (D-0009).
2. A bound fact stated as one literal instead of a chain. It verified at a one-step bound
   and is unsatisfiable at every larger one, so the first test written happened to land
   on the only value where the bug is invisible (D-0010).
3. `make`'s new signature broke the other session's test file, seen by neither, because
   each builds scoped to its own target — which is exactly what the shared `_build/` lock
   forces them to do.

The pattern in all three: **each session verified its own half and every half was green.**
What found the bugs was running the halves together against the real checker. Whoever
orchestrates the next round should treat "both agents report success" as the beginning of
review, not the end of it, and should own one integration test that no single agent can
make pass alone.

For M1-T8: copy `prop/linear.ml`'s shape *and* `prop/order_reason.ml`'s chains. Do not
re-derive bound-fact literals by hand — that is the D-0010 bug, and it will look like it
works.

**2026-09-14 — orchestrator, after D-0013**

The whole M1-T7/T8 vertical (propagator, explanation, bridge) is being handed to **one**
session this round rather than split. Splitting it along `Explanation.t` is exactly what
produced D-0009: two sessions agreed on the type and disagreed on its meaning, and the
checker accepted the mismatch. A shared type is not a shared contract, so this time the
type and both of its users move together.

`lib/core/explanation.ml` is unfrozen for agent-explain, and only for it. D-0013 says what
the ADT is missing and why; the change is no longer speculative.

**2026-09-15 — orchestrator, M1-T14: the CLI is wired**

`bin/main.ml` no longer prints "not implemented yet". Five of the seven models solve
and veripb accepts every proof; `make check` is green at 564 checks, up from 462.
`test/models/PENDING` is down to two: `ne_sat` (M1-T9, `int_ne` is now *rejected* with
a position and a name rather than absent) and `chain_sat`.

Two things the next session should know.

**The split worked this time, and the reason is worth keeping.** Two sessions ran on
disjoint files again, but unlike the M1-T7 round the contract between them was written
out operationally — what each function must *mean*, which index space it lives in, an
example of the bytes it emits — rather than being left implicit in a shared type. The
one cross-piece invariant (`Var.of_int i` denotes `Model.var m i`) was stated in both
briefs, implemented in `Compile`, and re-checked at run time in `main.ml`, because a
permutation there is invisible to I-S1: the check would be handed the same permuted
array and confirm it. Nothing had to be repaired at integration.

**`chain_sat` was added to catch an index permutation and caught something else.**
It is satisfiable, the answer is right, and veripb rejects the proof — see D-0017.
D-0012 said a SAT run's nogoods carry no weight because `conclusion SAT` checks the
assignment. True of the conclusion, false of the steps: veripb checks every rule as it
is emitted, so a nogood logged while the search is still hunting sinks the proof. That
makes **M1-T13 gate satisfiable models too**, which is a much larger claim than the
roadmap's framing — any model whose search takes one wrong turn before succeeding emits
an unverifiable proof. It stayed hidden because a SAT run only logs a nogood if a branch
fails first, and every satisfiable instance in the suite happens to be solved by a search
that guesses right at every level.

For whoever takes M1-T13: it is now the single thing standing between this solver and
being usable on anything non-trivial, and D-0016 point 1 is the most promising lead —
`pol` can recover a leaf's nogood by going through a root contradiction. D-0016 also
warns that guarding the wrong literal produces a valid but useless generalisation, so a
derivation recipe has to identify which decision the branch's refutation actually turns
on.

Smaller notes: `Encoding.add_equality` looks like the way to post an `int_lin_eq` and is
not — it takes PB literal terms and skips the order-encoding expansion; use two
`add_int_lin_le` calls. An empty term list is a real, representable PB row (`>= 1 ;`) that
veripb accepts, which is what makes a false ground constraint like `int_le(2, 1)` provable
rather than a special case. And `make check` reformats a tree someone else has already
called clean, so the reformat lands on whoever runs the gate next.

**2026-09-15 — orchestrator, the D-0018 round**

Three sessions on disjoint files, all three landed, nothing had to be repaired at
integration. `make check` is green with **no veripb xfail anywhere for the first time**;
`test/models/PENDING` is down to one line, and that line is CLI wiring, not proof work.

**The headline is not the code, it is that we had the wrong diagnosis for three decision
records.** D-0012, D-0014 and D-0017 all elaborated on "the branch nogood is unreachable".
It was reachable the whole time. What was missing was that we never wrote down the
propagation the checker was supposed to replay. Reading a solver that had already solved
it (GCS) took about three minutes to overturn what we had been theorising about for three
rounds — and GCS's own docs record the identical misdiagnosis as a known trap, in wording
that matches D-0012 almost line for line. When something in this area resists, read
someone else's implementation before writing another decision record.

Two corrections to my own D-0018, both found by building it:
- point 1 was wrong. "Every pruning **under a decision**" should be "every pruning". A
  `rup` check starts from nothing and does not inherit the root fixpoint. D-0021.
- point 3 (the conflict's own reason line) is redundant for `int_lin_le` and is kept
  deliberately. D-0021 says why, so nobody removes it as dead weight.

`chain_sat` turned out not to discriminate between those two readings: blank either half
of its trace and it still verifies; blank both and it fails. That is the fifth time in
this project that the instance chosen to test a thing could not see the thing break. The
mutation harness (M1-T15) now exists precisely for this, and its first run found that
`lin_unsat`'s refutation carries a unit of slack — veripb accepts that proof with a
corrupted coefficient. Reproduced by hand before believing it.

For the next session: **`int_ne` is written, proved, tested, and not reachable from the
CLI.** `compile.ml:365` still rejects it. agent-ne's handoff has the three lines, and the
one wrinkle is that `instances` is typed to `Linear.t` and needs to become
`Propagator.instance list`; `test_prop.ml` has a worked `pack_ne`/`pack_linear` example.
That clears the last `PENDING` line and closes M1-T11. After that, M2-T3 (clause learning)
is the next real one, and note I-X6 before starting it: conflict analysis is exactly the
caller that will break a `Deferred` thunk that reads live store state, which is a bug
`linear.ml` actually had until this round.

**2026-09-15 — orchestrator, the M1-T16/T17 round**

Populating the tests paid for itself in one round. The matrix and the fuzzer found
**three real bugs, two of them new**, all in the seam between `int_ne` (M1-T9) and the
trace machinery (M1-T13) — two pieces built the same morning and never run against each
other until something deliberately composed them. The root cause of the worst one was a
comment that went stale within hours: `store.ml` justified having no `remove_with_facts`
with "M1 is bounds-only … nothing punches a hole", which M1-T9 made untrue in the same
round. The emitted line was not merely unprovable, it was **false** on a satisfiable model.
That is now invariant I-P5.

Two process notes worth keeping.

**A pin that asserts a bug's symptom expires the moment the bug is fixed.** M1-T16 pinned
bug B as `contains "rup +1 y_ge_2 >= 1 ;"` — the presence of the bad line. Correct while
the bug stood, red the instant it was fixed, and indistinguishable at a glance from "a
test we broke". The replacement asserts the line the same pruning must now write, which
pins the situation and the content together. When pinning a bug, prefer an assertion that
stays true after the fix.

**Two of the three "bugs" had a fix that looked obvious and was wrong.** Weakening the
`Clause` out of the `pol` (the obvious fix for bug A) makes the derivation `0 >= 0`, which
still does not close, *and* erases the signal the real fix reads. Both were settled by
running the checker rather than by argument.

Also: `veripb` here is the **Python 2.2.2** implementation and the 2.0 proof format. The
current VeriPB is a **Rust** rewrite at 3.0.2 and it reads our 2.0 proofs unchanged
(advisory only), agrees with the old checker on all 9 of our proofs including which
mutations it rejects, and is ~30× faster per invocation — 223 ms to 7 ms, almost all of it
Python startup, which matters because the suite shells out to the checker hundreds of
times. Two-phase upgrade proposed and not yet taken: adopt the Rust checker while still
emitting 2.0 (no proof changes), then migrate emission to 3.0 before M2. Phase 2
supersedes D-0002 and needs its own decision record; its prize is **labels**, which delete
the `=`-counts-as-two-constraints trap in PROOF-FORMAT section 2 outright.

**2026-09-15 — agent-ne-wiring, M1-T11: the last PENDING line is gone**

`compile.ml` now posts both disequalities, so `test/models/PENDING` is empty and all 14
models solve with a proof veripb accepts (864 unit checks, 0 failures). M1-T11 and the
CLI half of M1-T9 are closed.

**The wiring itself was three lines, as the last handoff said. The hour went on finding
an instance that could watch it fail.** `ne_sat.fzn` — the model this task was measured
by, and the one line in `PENDING` — carries `int_lt(x, y)` beside its `int_ne`, and
`int_lt` alone fixes `x = 1, y = 2`. It passes whether or not the disequality does
anything, and its SAT proof contains no `rup` at all, because a search that never
conflicts never cites a reason and `conclusion SAT` is self-checking. Wiring `int_ne`
and calling that green would have been the sixth instance in this project that could not
see the thing it tested break. Five models now cover what it cannot: a bound moved by
`int_ne` alone, `int_lin_ne`'s division under a non-unit coefficient (nothing exercised
`int_lin_ne` from the CLI before — every `int_ne` is `1*x + (-1)*y <> 0`), a satisfiable
run refuted once *by* a clause, both branches closed by clauses and resolved to the
empty clause, and `int_ne(x, x)`.

Two things worth knowing before touching this area.

**`Engine.create` indexes its array by `Propagator.id`**, so an instance's id must equal
its position in the list it is handed — and an arm of `compile`'s match may yield one
instance or two, so it cannot know its own position. The arms now yield `pending`
instances (`int -> Propagator.instance`) and `compile` assigns ids once with a single
`List.mapi`. A new arm that packs its own instance with an id it invents will look
correct and will run the wrong propagator.

**`int_ne(x, x)` is a real case and it works.** `normalise_terms` merges the two
occurrences into a zero coefficient and drops it, leaving the false empty sum, and both
halves agree about it with no variable left to disagree over: the A/B rows degenerate to
two contradictory units on the auxiliary Boolean, the propagator conflicts with an empty
`Clause`, and the refutation is `rup >= 1 ;` closed the D-0022/I-X7 way. That is
`ne_self_unsat.fzn`. No special case was added and none should be — it is the
ground-constraint argument in `compile.ml`'s header, a second time.

One finding handed back rather than fixed, in `Cross-session requests`:
`test_matrix.ml`'s empty-cell note still says disequality prunings emit a factless trace
line, which M1-T17 fixed. Four `int_ne` shape cells are now fillable and the note says
they are not. M1-T11 claimed neither the matrix nor `lib/`, so it is a request.

Note for whoever merges: this work is on branch `worktree-m1-t11-ne-wiring`, not on
master. `test_output` and `test_mutation` locate the checkout from the cwd or the
executable path, so building into a `--build-dir` outside the tree makes both FAIL
loudly (not skip) — pass `BAGUETTE_ROOT`, or just use `dune --root .` inside the
worktree, which gives each worktree its own `_build` and no shared lock at all. That is
a cheaper answer to the `_build` contention in CLAUDE.md than a private `--build-dir`.

**2026-09-15 — orchestrator: the claims table had rotted, and M1 is merged to master**

Three rows sat under `## Active claims` describing work that had already shipped:
`integration`, M1-T12 and M1-T13. M1-T13 was *simultaneously* listed under Completed, so
the two tables contradicted each other. M1-T12 and `integration` were in neither. A
session reading the protocol in good faith would have believed `explanation.ml`,
`justify.ml` and `prop/**` were held by a live agent and routed around files nobody was
holding — which is exactly the cost the protocol exists to avoid, paid for nothing.

Both tables are now correct and Active claims is empty. **The lesson is not "remember to
release"** — every one of those three sessions *did* write a handoff note; what they
skipped was the one-line table edit, because the note felt like the deliverable. If a
session writes a handoff note without also moving its row, the row is what a later
session reads. `/handoff` does both; the rows that rotted were released by hand.

`worktree-m1-t11-ne-wiring` is merged to master as a fast-forward (4 commits, 0 behind).
M1 is closed: M1-T1..T17 all DONE, 14/14 models solve, `PENDING` empty, 864 unit checks.

**On the checker.** `veripb` resolves to the **Python 2.2.2** build at `~/.local/bin`,
but a **Rust 3.0.2** build is already installed at `~/.cargo/bin/veripb` — `~/.local/bin`
simply comes first on PATH. The previous handoff's two-phase proposal is therefore
cheaper than it reads: phase 1 needs no new install, only a decision about which binary
the harness invokes. Dispatched this round as M1-T18 / M1-T19.
