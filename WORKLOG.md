# Worklog

Coordination between concurrent Claude sessions. **Append only.** Add rows at the bottom
of a section; never reflow, reorder or rewrite rows you did not write. That is what makes
git merge two sessions' edits instead of conflicting.

Read this file at the start of every session. Claim before you edit. See `CLAUDE.md`.

---

## Active claims

| Task | Files being touched | Session | Since |
|---|---|---|---|
| M1-T1, M1-T2, M1-T3 | `lib/core/{var,domain,store,explanation,propagator}.ml`, `lib/core/dune`, `test/unit/test_core.ml` | agent-core | 2026-09-14 |
| M1-T4, M1-T5 | `lib/proof/{lit,opb,writer}.ml`, `lib/proof/dune`, `test/unit/test_proof.ml` | agent-proof | 2026-09-14 |
| M1-T6 | `lib/flatzinc/**`, `test/unit/test_flatzinc.ml` | agent-flatzinc | 2026-09-14 |

## Cross-session requests

Need a change in a file someone else has claimed? Write it here and move on to other
work. The owning session picks it up.

| Request | For file | From | Status |
|---|---|---|---|
| `lib/proof/lit.ml` is a shared dependency: agent-proof may **add** to it but must not change the existing signatures of `pbvar`, `t`, `ge`, `le`, `eq`, `ne`, `negate`, `to_string`, `var_name`, since agent-core compiles against them | `lib/proof/lit.ml` | orchestrator | standing |
| `WORKLOG.md`, `docs/**`, `dune-project`, `Makefile`, `scripts/**` and all committing are held by the orchestrator this round — agents touch none of them | — | orchestrator | standing |

## Completed

| Task | Session | Date | Summary |
|---|---|---|---|
| M0-T1 | setup | 2026-09-14 | Project skeleton, docs, dune files, test harness, `.claude/` setup |

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
