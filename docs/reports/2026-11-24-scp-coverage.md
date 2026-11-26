# Constraint coverage: GCS, baguette, `cake_pb_cp`

2026-11-24, branch `wave74-inputs`, for M23-inputs (D-0228 section 8). Sources: cake from
`cp_parseScript.sml` at CakeML master (identical to `14856fcf` that day). GCS from `gcs/scp_reader.cc`
and `minizinc/fzn_glasgow.cc` at `d7468618`. baguette from `lib/flatzinc/builder.ml`, `mznlib/` and
`E2e.spec` at `dd499b2`. **N** = own propagator, **D** = decomposed by MiniZinc's library or ours,
**-** = absent. The last column counts MiniZinc Challenge models (2011 to 2026, the smallest
instance of each, 300 of 319 flattened) whose `.scp`, written by GCS, holds the keyword.

| family (`.scp` keywords) | cake | GCS | baguette | `--e2e` | models |
|---|---|---|---|---|---|
| linear `lin_*` | yes | N | N | yes | 269 |
| linear reified `lin_*_iff` | yes | N | N for `<=`, D for `=` and `!=` | `<=` only | 121 |
| comparisons `equals less_equal ...` | yes | N | N | yes, not over views | 251 |
| comparisons reified `_iff` | yes | N | N | `<=`, `=`, `!=`, condition `(b = 1)` | 183 |
| half reified `_if` | yes | N | D | no | 0 |
| `and`, `or` | yes | N | N | conditions `(b = 0)`, `(b = 1)` | 201 |
| `parity` | yes | N | D | no | 2 |
| `abs` | yes | N | N | yes | 17 |
| `multiply` | yes | N | N | no | 42 |
| `divide` | yes | N | N | no | 11 |
| `modulus` | yes | N | D | no | 6 |
| `power` | no | N | D | no | 0 |
| `array_max`, `array_min` (`max`, `min`) | yes | N | N | yes | 80 |
| `element`, constant array | yes | N | N | yes | 93 |
| `element`, variable array | yes | N | D | no | 82 |
| `element_2d` | yes | N | - | no | 0 |
| `all_different` | yes | N | N | yes | 50 |
| `all_different_except` | yes | N | D | no | 9 |
| `symmetric_all_different`, `all_equal` | yes | N | D | no | 0, 3 |
| `global_cardinality` (open, closed) | yes | N | N | open, keyword `gac*` | 29 |
| `count` | yes | N | D (27 of 32 models), N through gcc (5 of 32) | through gcc only | 32 |
| `among`, `at_most_one` | yes | N | D | no | 0 |
| `nvalue` | yes | N | D | no | 7 |
| `in` (member) | yes | N | N | constants only | 7 |
| `table` | yes | N | N | no | 26 |
| `negative_table`, `smart_table`, wildcards | yes | N | - | no | 0 |
| `regular` | yes | N | N | yes | 20 |
| `mdd` | no | N | D | no | 0 |
| `inverse` | yes | N | N | yes | 12 |
| `circuit` | yes | N | N | no | 16 |
| `subcircuit` | no | N | D | no | 6 |
| `cumulative`, constant durations and resources | yes | N | N | yes | 17 |
| `cumulative`, variable arguments | yes | N | D | no | 28 |
| `disjunctive`, `disjunctive_strict` | yes | N | N as cumulative when constant, else D | no | 7 |
| `disjunctive2d`, `_strict` (diffn) | yes | N | D (pairs plus two cumulative) | no | 23 |
| optional tasks | no | N | D | no | 2 |
| `binpacking` | no | N | D (linear rows) | no | 15 |
| `knapsack` | yes | N | D | no | 2 |
| `lex_*` | yes | N | D | no | 16 |
| `value_precede`, `seq_precede_chain` | yes | N | D | no | 14 |
| `increasing`, `decreasing`, strict | yes | N | D (linear rows) | no | 17 |
| `sort`, `arg_sort` | yes | N | D | no | 0 |
| `reachable`, `tree`, `path`, `dag`, `subgraph` | no | N | D | no | 2 |
| `difference`, `min_distance` | no | N | - | no | 0 |

A "D" for baguette means MiniZinc decomposes it. A `.scp` reader has no MiniZinc, so a "D" is work
for the reader: it must write the decomposition itself.

## The GCS `.scp` against cake

GCS reads back the 300 files it wrote. The public `cake_pb_cp` (CakePB `438b8f83`) encodes 88 of the
220 of at most 400 kB tried. 115 are refused on a view, `(X + 3)` or `(-X + 17)`, which GCS's grammar has
and cake's lacks. Rewriting the views of comparisons as linear rows (`bench/inputs_spike/deview.py`)
brings the total to 184 of 220. Of the 36 others, 9 have a view inside `circuit`, 21 use a keyword cake
lacks (`binpacking`, `subcircuit`, ...), one exhausted the heap and 5 produced no file in 120 s (not resolved here).

## What a reader gains, by argument shape (297 models, `bench/inputs_spike/stage.py`)

| reader accepts | models entirely readable |
|---|---|
| the shapes of `E2e.spec` today, views in comparisons as linear rows | 45 |
| plus conditions of every operator in `and`/`or`, the `_iff` of linear equality, the bounds gcc keyword, `increasing` | 93 |
| plus every family baguette propagates itself (`table`, `circuit`, `multiply`, `divide`, closed gcc, `count` of a constant value, `in`) | 137 |
| plus the decompositions (first: variable `element` 82 models, variable `cumulative` 28, `disjunctive2d` 23, `binpacking` 14, `lex` 13) | 287 |

These count forms of one small instance per model. Nothing was solved. 143 of the 297 have no domain
wider than 1 000 values.
