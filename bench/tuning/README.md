# The tuning set (M19-config-T0, D-0205)

`set.lst`: 200 Challenge instances, `id<TAB>family<TAB>edition<TAB>tier`. Ids are those of
`bench/challenge/<edition>.lst`. Family is the problem name. Drawn by `draw_set.py` from D-0185's three
arms (`/cluster/arthur/baguette-results/m10t5/results_{A,B,C}.tsv`, 1 200 s, binary 7c880bce):

    python3 -I bench/tuning/draw_set.py . /cluster/arthur/baguette-results/m10t5 --out bench/tuning/set.lst

## Selection rule

1. Candidate: a row in all three arms, no FLATTEN-FAIL, not REFUSED/ERROR in all three, and not
   "complete in at most 10 s in every arm" (complete = OPT/UNSAT/SAT-on-satisfaction, verified in A
   and B, trusted in C).
2. Tier: 1 contested (some arm complete and another not, or one arm REFUSED/CAPPED/ERROR and another
   not, or incumbents differ), 2 attempted and hard (no complete answer, an incumbent exists),
   3 solved by all but over 10 s, 4 nothing to compare (all time out, no incumbent).
3. Round r gives every family its r-th best instance (tier, then md5 of the id), better tiers first,
   until 200 or 6 rounds. With 183 families that is one per family, then 17 second instances.
Result: 1 222 candidates, 183 families, 200 instances (tiers 164 / 15 / 6 / 15), 9 to 16 per edition.
Only 17 families get a second instance, so a per-family win or loss on the set is one or two
instances; read families in aggregate (by edition or by kind) and do not argue from one family.

## Protocol for an idea (M19-config rows)

- Arms: the idea's flag against the default of the day, same binary build otherwise (hash it).
  Each with proof (veripb on every finished run) and without (`--no-proof`).
- 300 s solve, the other D-0133 settings (16 GiB, `--max-heap-mb 8192`, own cgroup), no proof cap.
  A 1 200 s answer is out of reach of this set by design, so it ranks configurations at 300 s only.
- Report, per arm: complete (verified), incumbents, and the score of `agreement.py` (Challenge order,
  Borda over the arms; use arms_compare.py for the pairwise tables), per family wins and losses
  aggregated by edition, and the instances that changed status.
- Decision on the subset: an idea is kept for the full series if it gains on the subset's score and
  loses no verified complete answer without a stated reason. A winner is NOT adopted from the subset.
  The full M17 series confirms it, and the subset's verdict must agree in sign with the full series'
  (score and complete count). If it disagrees, record that in the D-record and widen the set.
- Run through M17's driver once it accepts a list and a solve timeout. Today it takes neither
  (WORKLOG cross-session request). Until then use `scripts/compare_run.sh` with
  `INSTANCES=` set to a per-edition filtered list.

## Validation against D-0185 (`agreement.py`, 1 200 s rows)

    python3 -I bench/tuning/agreement.py . bench/tuning/set.lst A=.../results_A.tsv B=... C=... --trust C [--cut 300]

Full set (1 574 instances) and subset (200) rank C > B > A, with score shares 0.403 / 0.337 / 0.260
and 0.391 / 0.367 / 0.242. B over A: 489+ 336- full, 94+ 56- subset. The subset narrows C against B
(full 0.066 apart, subset 0.024).
With a 300 s cut applied to the same rows (a complete answer later than 300 s no longer counts, its
incumbent kept, so optimistic), the full set stays C > B > A (0.395 / 0.339 / 0.267) and the subset
gives B > C > A (0.372 / 0.369 / 0.259): B and C are a tie there. A against B, both with proof,
agree in order on both (0.451 / 0.549 full, 0.405 / 0.595 subset). So the set separates A from the
rest reliably and cannot separate B from C at 300 s: a difference of under about 0.03 of the share
between two arms on this set is noise.
