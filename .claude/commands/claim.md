---
description: Claim a roadmap task in WORKLOG.md before starting work on it
argument-hint: <TASK-ID> [short note]
---

Claim task `$1` so no other session works on it at the same time.

`WORKLOG.md` is 68 KB and `docs/ROADMAP.md` is 46 KB — read the section you need, never
the whole file. The commands below are the scoped reads.

Do this now, in order:

1. Check the `## Active claims` table. The `SessionStart` hook already printed it; if you
   need it fresh:

   ```sh
   sed -n '/^## Active claims/,/^## Cross-session requests/p' WORKLOG.md
   ```

   If `$1` already appears there, **stop** and tell me who holds it — do not start the
   work. Offer the nearest unclaimed task from `docs/ROADMAP.md` instead; list candidates
   without pulling their notes:

   ```sh
   grep -n '^| M' docs/ROADMAP.md | grep -v 'DONE' | cut -c1-140
   ```

2. Read the row for `$1` — **that row only**. Each roadmap row is one very long line with
   its full history in it, so never use `grep -A`; the neighbours cost more than the task:

   ```sh
   grep -n '^| $1 |' docs/ROADMAP.md
   ```

   If it is `BLOCKED`, or its notes name a dependency that is not `DONE`, say so and stop.
3. Work out which files the task will touch. Check them against the other rows in
   `## Active claims`. If any file is already claimed, say so and stop.
4. Append a row to the bottom of the `## Active claims` table — do not reflow or reorder
   the existing rows:

   | $1 | <files you will touch> | <a short session tag> | <today's date> |

5. Set the task's status to `WIP` in `docs/ROADMAP.md`.
6. Commit just those two files, with the message `claim: $1`. Stage them by explicit
   path — never `git add -A` or `git add .`.
7. Then, before writing any code, read — in this order, and scoped:
   - `docs/INVARIANTS.md` — whole, it is 6 KB and short on purpose
   - the sections of `docs/SPEC.md` your task touches (§2.1 the FlatZinc subset,
     §3.2 consistency levels, §3.3 explanations)
   - the relevant section of `docs/PROOF-FORMAT.md` — **not the whole file**. Section
     boundaries: `grep -n '^## ' docs/PROOF-FORMAT.md`. For a propagator, §4 is the
     justification table: `sed -n '352,402p' docs/PROOF-FORMAT.md`.
   - the module header of the file you are about to change (`head -40 <file>`), and of
     `lib/core/prop/linear.ml` if this is propagator work — it is the reference shape.

   Look up a decision record only when something points you at one, and look it up by id
   rather than reading the 126 KB log: `grep -n 'D-0028' docs/DECISIONS.md`, then `sed`
   the range it reports.

Then start the work.

Extra context from me, if any: $2
