# Worklog

Coordination between concurrent Claude sessions. **Append only.** Add rows at the bottom
of a section; never reflow, reorder or rewrite rows you did not write. That is what makes
git merge two sessions' edits instead of conflicting.

Read this file at the start of every session. Claim before you edit. See `CLAUDE.md`.

---

## Active claims

| Task | Files being touched | Session | Since |
|---|---|---|---|
| integration | `test/unit/test_endtoend.ml` | orchestrator | 2026-09-14 — no single session can make it pass alone |
| M1-T12 — make the D-0013 derivation real: `Explanation` + `Justify` + `int_lin_le` | `lib/core/explanation.ml`, `lib/core/justify.ml`, `lib/core/prop/**`, `test/unit/test_prop.ml`, `test/unit/test_justify.ml` | agent-explain | 2026-09-14 — **authorised to change the Explanation ADT**, see D-0013 |
| M1-T13 — the branching half of D-0013, research only | none — scratchpad only | agent-branch | 2026-09-14 |
| M1-T14 — wire the CLI: `.fzn` in, solution + proof out | `lib/flatzinc/compile.ml` (new), `lib/flatzinc/output.ml` (new), `lib/flatzinc/model.ml`, `lib/flatzinc/dune`, `bin/main.ml`, `test/unit/test_compile.ml` (new), `test/models/**`, `test/expected/**` | orchestrator | 2026-09-14 |

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
