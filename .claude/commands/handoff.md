---
description: Finish a task cleanly — release the claim and write handoff notes
argument-hint: <TASK-ID>
---

Close out task `$1`.

1. Run `make check`. If it fails, **stop** — report what failed and do not release the
   claim. A half-finished task still claimed is better than a released broken one.
2. Confirm the work actually meets the task's roadmap notes and the relevant parts of
   `docs/SPEC.md`. Say plainly if anything in scope was left undone.
3. In `WORKLOG.md`:
   - remove your row from `## Active claims` (only your own row)
   - append a row to `## Completed` with a one-line summary
   - append a dated entry at the bottom of `## Handoff notes`: what changed, anything
     surprising, and what the next session needs to know before touching the same area.
     Two or three lines. Write what you would have wanted to know an hour ago.
4. Set the task to `DONE` in `docs/ROADMAP.md`.
5. If the work settled a design question, append an entry to `docs/DECISIONS.md` —
   including the reasoning, not just the verdict. If it raised one, append it as `OPEN`.
6. If you left a request for a file someone else has claimed, put it under
   `## Cross-session requests`.
7. Commit, staging explicit paths only. Message: `$1: <what you did>`.
