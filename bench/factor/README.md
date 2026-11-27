# bench/factor: the per-node factor lane's instances

M17-bench-series-T6, D-0256. `scripts/factor_lane.sh` (`make factor`) reads `plan.tsv` and the
files of `fzn/`, and prints how many times a reference solver's instructions baguette spends per
search node (or per failure, where the trees differ), in four configurations. Its header is the
manual: what is run, the measure, the outputs, the exit statuses. `reference.tsv` is the recorded
run the next ones are compared with, as information.

## The instances

| id | family | what it is | where it comes from |
|---|---|---|---|
| `qr3` | clauses | codes-cp QR48 with 3 fixed, UNSAT, 1 134 `bool_clause` | D-0169's `f3.fzn` |
| `costas14` | alldiff | 2011 costas-array, n = 14, to the first solution | MiniZinc Challenge 2011 |
| `mknap2-1` | linear | 2014 multi-knapsack `mknap2-1`, cut at 20 000 nodes | MiniZinc Challenge 2014 |
| `jr63` | element | 2013 javarouting `trip_6_3`, objective <= 66 (optimum 67), cut at 20 000 nodes | MiniZinc Challenge 2013, bounded |
| `rcpsp11_60`, `rcpsp11_66` | cumulative | 2013 rcpsp `11`, makespan <= 60 and <= 66 (optimum 77), UNSAT | MiniZinc Challenge 2013, bounded |
| `sat3_200_1` to `_3` | sat3 | planted random 3-SAT, 200 variables, 852 clauses (ratio 4.26), SAT | `gen_3sat.py 200 4.26 SEED` |

The first six are D-0207's instances, the very files it flattened on 2026-11-23 (copied from
`/cluster/arthur/baguette-results/pernode2/fzn/`, gzipped, not re-flattened), so that its table and
this lane's are on the same bytes. `.b` is baguette's flattening (its `mznlib` of that day), `.g`
Gecode's and `.c` Chuffed's (the MiniZinc 2.10.1 bundle's libraries). Each file's own header gives
the flattening command (`% Command line invocation:`). The optimisation models were made
satisfaction models with the objective bounded below the optimum, so that the tree is a refutation:
the modified `jr63.mzn` and `rcpsp.mzn` are in `pernode2/models/`, and the flattening was

```sh
minizinc -c --solver <baguette.msc | gecode | chuffed> MODEL.mzn DATA.dzn [-D BOUND=60] -o NAME.{b,g,c}.fzn
```

(`pernode2/flat.sh`). Every model carries a complete search annotation, so baguette, Gecode and
Chuffed `--lazy off` walk the same tree when baguette does not prune more by learning.

The 3-SAT files are plain FlatZinc that every solver reads unchanged, written by `gen_3sat.py`
(docstring: the planted distribution, why it is SAT, the determinism). The three seeds are 1, 2 and
3, all kept, chosen before any run. To check that the committed files are the generator's:

```sh
for s in 1 2 3; do python3 -I bench/factor/gen_3sat.py 200 4.26 $s | cmp - <(gzip -dc bench/factor/fzn/sat3_200_$s.fzn.gz); done
```

## Adding an instance

Keep the lane under about ten minutes at `-j 8`: an instance whose proved run takes more than two
minutes needs a node budget. A new line in `plan.tsv` changes the reference: re-record it
(`scripts/factor_lane.sh --record`) in its own commit, and say so in the HISTORY row.
