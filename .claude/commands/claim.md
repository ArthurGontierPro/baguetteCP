---
description: Claim a roadmap task in WORKLOG.md before starting work on it
argument-hint: <TASK-ID> [short note]
---

Claim task `$1` so no other session works on it at the same time.

Do this now, in order:

1. Read `WORKLOG.md`. If `$1` already appears under `## Active claims`, **stop** and tell
   me who holds it — do not start the work. Offer the nearest unclaimed task from
   `docs/ROADMAP.md` instead.
2. Read the row for `$1` in `docs/ROADMAP.md`. If it is `BLOCKED`, or its notes name a
   dependency that is not `DONE`, say so and stop.
3. Work out which files the task will touch. Check them against the other rows in
   `## Active claims`. If any file is already claimed, say so and stop.
4. Append a row to the bottom of the `## Active claims` table — do not reflow or reorder
   the existing rows:

   | $1 | <files you will touch> | <a short session tag> | <today's date> |

5. Set the task's status to `WIP` in `docs/ROADMAP.md`.
6. Commit just those two files, with the message `claim: $1`. Stage them by explicit
   path — never `git add -A` or `git add .`.
7. Then read `docs/SPEC.md`, `docs/INVARIANTS.md` and the relevant part of
   `docs/PROOF-FORMAT.md` before writing any code, and start the work.

Extra context from me, if any: $2
