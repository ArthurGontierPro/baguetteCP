---
description: Catch up on what other sessions have done since you last looked
---

Orient before doing anything else.

This is a cheap orientation pass, not a research task. Every step below is a scoped read:
`WORKLOG.md` is 68 KB and `docs/DECISIONS.md` is 126 KB, and reading either one whole
costs more context than the work you are about to start. Use the commands as written.

1. What has landed, and is the tree clean?

   ```sh
   git log --oneline -20
   git status --short
   ```

2. What is being worked on right now, and therefore which files are off limits to you.
   The `SessionStart` hook already printed this; re-read only if you need it fresh:

   ```sh
   sed -n '/^## Active claims/,/^## Cross-session requests/p' WORKLOG.md
   ```

3. The last few handoff notes:

   ```sh
   sed -n '/^## Handoff notes/,$p' WORKLOG.md | tail -60
   ```

4. Anything addressed to a file you own:

   ```sh
   sed -n '/^## Cross-session requests/,/^## Completed/p' WORKLOG.md
   ```

5. New decisions — **headings only**, then fetch just the ones that are new to you:

   ```sh
   grep -n '^## D-' docs/DECISIONS.md | tail -20
   ```

   For one that matters, `sed -n '<start>,<end>p' docs/DECISIONS.md` using the line
   numbers that grep reported. Pay particular attention to any that moved from `OPEN` to
   `DECIDED`. Do not read the file whole.

6. Report back in a few lines: what changed, what is claimed, what is free to pick up
   from `docs/ROADMAP.md`, and whether anything conflicts with what I asked you to do.
   A few lines means a few lines — do not paste the output of the commands above.
