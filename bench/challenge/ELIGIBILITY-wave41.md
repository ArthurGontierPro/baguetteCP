# Bits-encoding eligibility on the D-0129 wall (M8-bits-encoding-T1, measurement)

**Question.** D-0130 §3.4 gives the bits encoding to a variable only when every `.opb` row
that mentions it is a linear row, and keeps the order encoding at every threshold for a
variable in the scope of `all_different_int`, `global_cardinality`, `array_int_element`,
`array_int_maximum/minimum`, `cumulative`, or declared with holes. On the 169 Challenge runs
whose `.opb` never finished writing (D-0129, the encoding wall), how much of the declared
width would bits remove under that rule, and how much stays on the ladder because of scope?

**Answer, in one paragraph.** Per instance, 94 of the 169 would have at least 90 % of their
declared width made eligible, 25 between 50 and 90 %, and 50 less than 50 %. By width, the
169 declare Σw = 3.27 × 10¹² ladder rows, 54.2 % of it eligible and 45.8 % held back, and the
held-back width is 99.98 % `maxmin` (`array_int_maximum`/`array_int_minimum`), because the
ten `road-cons` instances alone hold 1.47 × 10¹² behind `array_int_minimum` over variables of
width 2 000 000, and the 15 `tower`, 6 `largescheduling` and 6 `ATSP`/`atsp` instances hold
another 23 × 10⁹ behind the same family. `array_int_element` is the second holder and holds
237.6 × 10⁶ on its own (the width held by element and by no other family), which is 0.016 % of
the held width but the largest holder in 36 instances. `gcc`, `alldiff`, `cumulative` and
holes together hold 3.2 × 10⁶. The eligible 1.77 × 10¹² would need 7.3 × 10⁶ bits. Relaxing
element alone would move 237.6 × 10⁶ from held to eligible; relaxing maxmin would move
1.496 × 10¹². D-0130 §7.4's extra hold on `Ne`'s scope at T2 costs 4 115 of eligible width,
so it is free. Of the 8 OPTs whose proof the checker cannot finish, the six `ship-schedule`
are 98 to 99.8 % eligible, `smelt_2` 52 % (the rest is width-0/1 variables and 10 000 behind
`cumulative`) and `mapping_full2x2_mp3` 57 % (`maxmin` and holes).

Files: `bench/challenge/eligibility-wave41.tsv` (one row per instance, 177 rows, columns
below) and this note. The scripts and the re-flattened `.fzn` are on `fataepyc-06` under
`/scratch/arthur/wave42-elig/` (`elig.py` md5 `74fe02a1`, `aggregate.py`, `flatten_line.sh`,
`run_elig.sh`, `mkjobs.sh`, `launch.sh`; `fzn/` 2.7 GB, kept for T2).

## Method

**Population.** `/scratch/arthur/wave41run/<Y>/results.tsv` for Y in 2011..2026, the rows
with solver `baguette`, status in {CAPPED, TIMEOUT, ERROR} and the `opb` column (field 8 of
`scripts/compare_run.sh`'s `emit`) equal to `-`. That is D-0129's proxy for "the `.opb` was
never completed" and it gives 143 + 19 + 7 = 169, the same split. The 8 OPTs are D-0129's list.

**The `.fzn` files.** D-0129 says the population's `.fzn` were kept under
`/scratch/arthur/wave41run/*/work/`. They are not there any more for most of them (the
harness deletes the `.fzn` on most outcomes; `wave41run/2011/work/` holds 5 files and
`wave41run/2021/work/` 15, for example). 15 of the 177 were found and used as they are, 8 under `wave41run/<Y>/work/` and 7
under `m7t27run/<Y>/work/` (the list is at the end of this note, and the TSV's `fzn_source`
column says it per instance). The other **162 were re-flattened** with the run's exact
tool chain, read from `wave41run/<Y>/run.conf`: MiniZinc 2.10.1 at
`/scratch/arthur/mzn/MiniZincIDE-2.10.1-x86_64-linux-gnu/bin/minizinc`, the solver library
`/scratch/arthur/baguette-gate-20261106/mznlib` (md5-identical, file by file, to `mznlib/`
at this commit) through `tools/baguette.msc` on `MZN_SOLVER_PATH`, the model and data paths
from `wave41run/<Y>/pair.tsv`, and the harness's command line
`minizinc -c --no-output-ozn --solver org.baguette.baguette <model> <data> -o <out>.part`.
The command was validated on `2021_ATSP_instance5_0p15`, whose kept `.fzn` was still on
disk, and the re-flattened file is identical to the kept one line for line except the
`:: output_var` annotation the harness adds on the objective, which changes no domain and no
constraint. All 162 flattened with rc 0, within a few minutes at 24 lanes (the slowest
single flatten, `2023_table-layout_p2000_m16_r1000_c200`, took 70 s), 2.7 GB in all.

**The parser** (`elig.py`, Python, `python3 -I`, streaming line by line) reads every
`var <dom>: name` and `array [a..b] of var <dom>: name` declaration and every
`constraint pred(...)` line. Width is `hi - lo` for `var lo..hi` and for `var {…}` (with
`holes` set when the set is not contiguous); a `var int` with no domain would count as
unknown width (there are none in the 177 files); `var bool` is not an int variable; an
alias `var …: x = y;` declares no variable and is resolved to `y`; an `array … of var`
with an element list is a name for its elements, one without is `n` fresh variables.
Identifiers in a constraint line are resolved against the declarations, an array name
expanding to all its elements. Predicates are classified as **linear** (`int_lin_le/eq/ne`,
`int_le/lt/eq/ne`, their `_reif` forms, `bool2int`, `int_abs/times/div/mod`, `int_plus`,
and every `bool_*`/`array_bool_*` row) or **enumerating**, by family: `gcc` (`global_cardinality*`,
`fzn_global_cardinality*`, `baguette_global_cardinality`, `count_eq`, `exactly`, `at_most`,
`at_least`, `among`), `alldiff` (`all_different_int`, `fzn_all_different_int`), `element`
(`array_int_element`, `array_var_int_element`, `array_bool_element`,
`array_var_bool_element`), `maxmin` (`array_int_maximum/minimum`, `int_max/min`),
`cumulative` (`cumulative`, `fzn_cumulative`, `baguette_cumulative`, `disjunctive*`). Any
other predicate is **unclassified** and would hold its variables (none occurred). A
variable is **eligible** iff width ≥ 2, no holes, and never mentioned by an enumerating
or unclassified predicate. A held variable is attributed to the first holding family in
the fixed order gcc, alldiff, element, maxmin, cumulative, holes; `held_element_only_w`
is exact (held by element and by nothing else), so the "element versus the rest" split
does not depend on the order.

**Sanity checks, counted by hand.** `test/models/element_const_result.fzn` (one variable
`i` in 1..4, in `array_int_element`: Σw 3, eligible 0, held by element 3) and
`test/models/alldiff_const_sat.fzn` (`p`, `q` in 1..3, in `all_different_int`: Σw 4,
eligible 0, held by alldiff 4) are the two the brief asked for. Two more exercised the
parts those do not: `test/models/set_domain_sat.fzn` (`x` in {1,3,5}: width 4, held by
holes) and `test/models/array_sat.fzn` (`array [1..2] of var 0..4: q` with no element
list: 2 variables of width 4, both eligible, 3 bits each, Σw 8).

**Run.** 177 files at 24 lanes on `fataepyc-06` (idle, load 0), 25 s of wall, every rc 0;
the slowest file, `2025_ihtc-2024-marte_i14` (849 MB, 610 455 int variables next to
3.17 M `var bool`, 5.0 M constraints), took 31 s at a peak RSS of 878 MB. The tables below are `aggregate.py` over
the TSV.

## Columns of `eligibility-wave41.tsv`

`id`, `status` (CAPPED/TIMEOUT/ERROR from `results.tsv`, or `OPT8`), `fzn_source`
(`kept-wave41run`, `kept-m7t27run`, `reflattened`), `n_int` (int variables, aliases and
`var bool` excluded), `n_unknown_width` (`var int` with no domain, always 0 here),
`n_constraints`, `sum_w` (Σ(hi − lo)), `elig_w`, `elig_pct`, `n_elig`, `elig_bits`
(Σ⌈log₂(w+1)⌉ over eligible variables), `held_w`, `held_n`, `held_gcc` … `held_unclassified`
(Σw attributed to each family by the fixed order), `held_element_only_w`, `held_other_w`
(= `held_w` − `held_element_only_w`), `ne_elig_w` and `n_ne_elig` (eligible width and count
also in an `int_ne`/`int_lin_ne` scope, D-0130 §7.4's T2 hold), `narrow_w` (Σw of width-0/1
variables, ineligible by width), `max_w`, `top3` (`name:width:tag;…`, tag = holding family,
`eligible` or `narrow`), `unclassified` and `unknown_ids` (`-` when empty), `n_contig_set`,
`n_set_var`, `preds` (every predicate with its count).

## Caveats

- Σw is the number of **ladder rows** the order encoding declares per variable (D-0028), the
  quantity bits would replace. It is not the `.opb` size. The enumerating families add rows of
  their own (one per value for `maxmin`'s clauses and `gcc`'s counts, per position for
  `element`), the channelling adds more, and `int_lin_le_reif` adds two big-M rows per
  reification. So "x % eligible by Σw" bounds the ladder's share, not the file's.
- The width is the **declared** width in the `.fzn`, which is what `builder.ml` sees. No
  `var int` without a domain occurs, so D-0083's inference plays no part.
- The brief's rule is applied at **every width ≥ 2**, that is `--bits-above W` with `W = 1`.
  A larger `W` can only move eligible width back to the ladder, never the reverse, and it
  leaves the held width untouched.
- `int_ne`/`int_lin_ne` are **linear** here, as the brief says. D-0130 §7.4 holds `Ne`'s
  scope at T2, and the `ne_elig_w` column says what that would cost (4 115 in all).
- `count_eq`, `exactly`, `at_most`, `at_least`, `among` never reach the `.fzn`. The baguette
  mznlib has no `fzn_count_*` redefinition, so MiniZinc's standard library decomposes them
  into `int_eq_reif` + `bool2int` + `int_lin_eq` before the file is written. "Routed to gcc"
  in the brief does not happen in these 177 files. Likewise `int_max`/`int_min` are rewritten
  by `mznlib/redefinitions.mzn` into `array_int_maximum/minimum`, so only the array forms occur.
- A variable in several enumerating scopes is counted under the first family in the fixed
  order; the per-family Σw are attributions, and the order favours gcc and alldiff. Only
  `held_element_only_w` is order-independent. In practice the overlaps are small (the
  `tower` instances have a few thousand element-held variables next to 10⁹ maxmin-held ones).
- Identifiers inside a constraint's annotations (`:: defines_var(x)`) count as mentioned by
  that constraint. The variable is in the constraint's scope anyway. The only identifier the
  resolver could not place is `domain`, the annotation on 8 `int_lin_eq`/`int_lin_le` rows of
  four `yumi-dynamic` instances, now in the annotation list; nothing else was unresolved.
- The 7 ERROR runs all ended with rc 134 after the width warning on one variable (D-0129);
  their `.fzn` parsed like the others and they are in every table.
- The per-family width shares are dominated by `road-cons` (ten instances, Σw 1.47 × 10¹²,
  99.9 % held). The "mean per-instance share" column and the per-problem table exist so that
  the reader is not misled by the totals. Without `road-cons`, 23.7 × 10⁹ is held, of which
  `largescheduling` 16.3 × 10⁹, `tower` 5.4 × 10⁹ and `ATSP`/`atsp` 1.7 × 10⁹, all `maxmin`;
  the eligible total is likewise dominated by four `MZNC` (`connect`) instances at
  1.42 × 10¹² and five `arithmetic-target` at 0.29 × 10¹², all 100 % eligible.

## Tables

### The 169 runs whose `.opb` never finished (D-0129) (169 instances)

| eligible share of the instance's Σw | instances | CAPPED | TIMEOUT | ERROR |
|---|---|---|---|---|
| ≥ 90 % | **94** | 71 | 17 | 6 |
| 50–90 % | **25** | 24 | 0 | 1 |
| < 50 % | **50** | 48 | 2 | 0 |

| total over the 169 | value |
|---|---|
| int variables | 9 943 504 (of which 0 `var int` with no declared domain, width counted 0) |
| Σw, declared width (= order-encoding ladder rows per variable, D-0028) | 3 270 509 544 639 |
| Σw over eligible variables | 1 774 003 650 124 (54.2 %) |
| Σ⌈log2(w+1)⌉ over eligible variables (the bits those would need instead) | 7 324 656 |
| Σw held back by scope or holes | 1 496 498 293 403 (45.8 %) |
| of which held ONLY by `array_int_element` (no other family on the variable) | 237 575 891 (0.0 % of held) |
| of which held by some other family (alone or with element) | 1 496 260 717 512 (100.0 % of held) |
| Σw of width-0/1 variables (ineligible by width, not by scope) | 7 601 112 (0.0 %) |
| eligible Σw that D-0130 §7.4's Ne hold would ALSO keep on the ladder at T2 (`int_ne`/`int_lin_ne` scope) | 4 115 (0.0 % of eligible) |

Per-family share of the held-back width. The width share is dominated by a few giant instances, so the third column gives the mean over instances of the family's share of that instance's held width (each instance counting once):

| family | Σw held | share of held Σw | mean per-instance share | instances where it holds the most | instances where it holds anything |
|---|---|---|---|---|---|
| gcc | 79 684 | 0.0 % | 2.5 % | 1 | 19 |
| alldiff | 1 355 568 | 0.0 % | 3.7 % | 5 | 15 |
| element | 237 617 661 | 0.0 % | 25.9 % | 36 | 65 |
| maxmin | 1 496 257 468 663 | 100.0 % | 58.8 % | 78 | 85 |
| cumulative | 349 658 | 0.0 % | 4.0 % | 5 | 9 |
| holes | 1 422 169 | 0.0 % | 5.0 % | 6 | 37 |
| unclassified | 0 | 0.0 % | 0.0 % | 0 | 0 |
| (no family: nothing held) | | | | | 38 |

Per Challenge problem (the second `_` token of the instance id), sorted by Σw:

| problem | instances | Σw | eligible % | held Σw | held by | ≥90 / 50–90 / <50 |
|---|---|---|---|---|---|---|
| road-cons | 10 | 1 474 740 112 054 | 0.1 | 1 472 796 113 048 | maxmin 1 472 796 113 048 | 0 / 0 / 10 |
| MZNC | 4 | 1 419 580 331 345 | 100.0 | 8 610 073 | element 8 610 059, holes 14 | 4 / 0 / 0 |
| arithmetic-target | 5 | 294 295 928 474 | 100.0 | 4 618 | gcc 982, element 3 636 | 5 / 0 / 0 |
| largescheduling | 6 | 32 504 900 431 | 50.0 | 16 264 650 131 | maxmin 16 264 650 131 | 0 / 2 / 4 |
| routing-flexible | 5 | 16 406 473 180 | 100.0 | 79 611 | maxmin 79 590, holes 21 | 5 / 0 / 0 |
| gbac | 9 | 7 813 616 724 | 100.0 | 877 412 | gcc 21 089, maxmin 856 323 | 9 / 0 / 0 |
| unit-commitment | 4 | 6 636 885 361 | 100.0 | 0 | - | 4 / 0 / 0 |
| tower | 15 | 5 358 267 716 | 0.0 | 5 358 155 741 | element 62 415, maxmin 5 358 093 326 | 0 / 0 / 15 |
| code-generator | 2 | 4 163 171 215 | 100.0 | 795 000 | alldiff 232, element 587 860, maxmin 178 684, holes 28 224 | 2 / 0 / 0 |
| ATSP | 3 | 1 984 691 948 | 44.5 | 1 100 569 640 | element 1 000, maxmin 1 100 568 640 | 0 / 1 / 2 |
| atp-stage2 | 1 | 1 758 939 743 | 100.0 | 4 180 | alldiff 901, holes 3 279 | 1 / 0 / 0 |
| atsp | 3 | 917 630 526 | 37.0 | 577 661 265 | element 950, maxmin 577 660 315 | 0 / 0 / 3 |
| wmsmc-int | 2 | 809 305 500 | 100.0 | 0 | - | 2 / 0 / 0 |
| cable | 1 | 776 482 366 | 100.0 | 184 784 | alldiff 78 012, maxmin 106 772 | 1 / 0 / 0 |
| ihtc-2024-marte | 2 | 608 410 988 | 80.7 | 116 410 176 | element 41 598, maxmin 116 362 595, cumulative 2 496, holes 3 487 | 0 / 2 / 0 |
| celar | 1 | 475 338 206 | 99.9 | 302 064 | holes 302 064 | 1 / 0 / 0 |
| flowshop-workers | 5 | 252 626 681 | 100.0 | 0 | - | 5 / 0 / 0 |
| liner-sf-repositioning | 1 | 204 789 624 | 75.7 | 49 801 321 | gcc 252, alldiff 80, element 49 733 759, maxmin 67 230 | 0 / 1 / 0 |
| aircraft-disassembly | 1 | 195 086 620 | 99.9 | 105 600 | maxmin 105 600 | 1 / 0 / 0 |
| steiner-tree | 3 | 183 125 097 | 100.0 | 0 | - | 3 / 0 / 0 |
| carpet-cutting | 18 | 173 220 012 | 99.4 | 51 677 | element 51 677 | 18 / 0 / 0 |
| zephyrus | 3 | 153 601 721 | 100.0 | 0 | - | 3 / 0 / 0 |
| table-layout | 1 | 104 694 066 | 0.6 | 104 036 266 | element 104 036 266 | 0 / 0 / 1 |
| train | 16 | 87 734 991 | 100.0 | 0 | - | 16 / 0 / 0 |
| pentominoes-zayenz | 1 | 72 387 840 | 0.0 | 72 382 254 | element 72 382 254 | 0 / 0 / 1 |
| vrp-submission | 1 | 63 632 238 | 100.0 | 18 478 | alldiff 11 877, element 6 601 | 1 / 0 / 0 |
| cargo | 4 | 47 784 925 | 99.8 | 13 889 | cumulative 13 889 | 4 / 0 / 0 |
| mapping | 15 | 46 917 531 | 67.9 | 15 077 936 | maxmin 14 184 226, holes 893 710 | 0 / 15 / 0 |
| test-scheduling | 4 | 17 780 793 | 0.0 | 17 358 184 | element 435, maxmin 17 357 233, holes 516 | 0 / 0 / 4 |
| saeling | 2 | 16 913 840 | 59.5 | 6 840 732 | element 44 783, maxmin 6 795 949 | 0 / 1 / 1 |
| openshop | 2 | 16 084 465 | 100.0 | 0 | - | 2 / 0 / 0 |
| ship-schedule | 1 | 10 184 192 | 99.8 | 14 694 | element 14 694 | 1 / 0 / 0 |
| fjsp | 3 | 7 290 947 | 89.5 | 275 886 | cumulative 275 886 | 2 / 0 / 1 |
| cyclic-rcpsp | 1 | 6 368 428 | 49.7 | 3 203 207 | alldiff 1 842, maxmin 3 172 814, cumulative 28 551 | 0 / 0 / 1 |
| yumi-dynamic | 4 | 5 079 444 | 18.1 | 3 050 250 | alldiff 8 579, element 2 027 148, maxmin 1 014 523 | 0 / 0 / 4 |
| kitchen | 1 | 4 360 676 | 100.0 | 0 | - | 1 / 0 / 0 |
| rcpsp-wet-diverse | 1 | 2 498 461 | 48.2 | 118 260 | maxmin 89 424, cumulative 28 836 | 0 / 0 / 1 |
| multi-agent-graph-coverage | 1 | 2 260 266 | 98.2 | 40 474 | alldiff 28 234, maxmin 12 240 | 1 / 0 / 0 |
| cvrp | 1 | 1 632 031 | 92.0 | 130 587 | alldiff 118 061, element 12 526 | 1 / 0 / 0 |
| multiple-constant-multiplication | 3 | 984 673 | 75.5 | 240 666 | gcc 52 192, holes 188 474 | 0 / 3 / 0 |
| ma-path-finding | 1 | 821 490 | 0.1 | 401 310 | alldiff 401 310 | 0 / 0 / 1 |
| whirlpool | 1 | 711 956 | 0.0 | 708 820 | alldiff 706 440, holes 2 380 | 0 / 0 / 1 |
| hitori | 1 | 485 854 | 98.9 | 5 169 | gcc 5 169 | 1 / 0 / 0 |

Instances where the held-back width exceeds 10⁶ (59 of 169), largest first:

| instance | status | Σw | held Σw | held % | by | widest held variable (if among the top 3 widest) |
|---|---|---|---|---|---|---|
| `2017_road-cons_road_33` | CAPPED | 716 284 177 827 | 715 755 177 887 | 99.9 | maxmin 715 755 177 887 | `X_INTRODUCED_38624_` w=2 000 000 (maxmin) |
| `2017_road-cons_road_26` | CAPPED | 268 748 271 325 | 268 422 271 364 | 99.9 | maxmin 268 422 271 364 | `X_INTRODUCED_19319_` w=2 000 000 (maxmin) |
| `2017_road-cons_road_25` | CAPPED | 228 574 476 519 | 228 273 476 633 | 99.9 | maxmin 228 273 476 633 | `X_INTRODUCED_17246_` w=2 000 000 (maxmin) |
| `2014_road-cons_road_20` | CAPPED | 90 610 213 232 | 90 419 213 330 | 99.8 | maxmin 90 419 213 330 | `X_INTRODUCED_9076_` w=2 000 000 (maxmin) |
| `2017_road-cons_road_18` | CAPPED | 58 377 406 597 | 58 223 406 980 | 99.7 | maxmin 58 223 406 980 | `X_INTRODUCED_6723_` w=2 000 000 (maxmin) |
| `2017_road-cons_road_17` | CAPPED | 45 951 475 225 | 45 814 475 297 | 99.7 | maxmin 45 814 475 297 | `X_INTRODUCED_5716_` w=2 000 000 (maxmin) |
| `2014_road-cons_road_16` | CAPPED | 35 624 581 404 | 35 503 581 309 | 99.7 | maxmin 35 503 581 309 | `X_INTRODUCED_4808_` w=2 000 000 (maxmin) |
| `2014_road-cons_road_14` | CAPPED | 20 279 715 612 | 20 187 715 762 | 99.5 | maxmin 20 187 715 762 | `X_INTRODUCED_3292_` w=2 000 000 (maxmin) |
| `2014_road-cons_road_11` | CAPPED | 7 249 864 402 | 7 193 864 351 | 99.2 | maxmin 7 193 864 351 | `X_INTRODUCED_1672_` w=2 000 000 (maxmin) |
| `2018_largescheduling_instance-0800-4` | CAPPED | 12 944 716 073 | 6 476 080 873 | 50.0 | maxmin 6 476 080 873 | (none in the top 3) |
| `2015_largescheduling_instance-0800-1` | CAPPED | 12 801 277 687 | 6 404 316 887 | 50.0 | maxmin 6 404 316 887 | (none in the top 3) |
| `2014_road-cons_road_9` | CAPPED | 3 039 929 911 | 3 002 930 135 | 98.8 | maxmin 3 002 930 135 | `X_INTRODUCED_962_` w=2 000 000 (maxmin) |
| `2018_largescheduling_instance-0400-4` | CAPPED | 3 205 119 877 | 1 604 480 677 | 50.1 | maxmin 1 604 480 677 | (none in the top 3) |
| `2015_largescheduling_instance-0400-2` | CAPPED | 3 151 251 000 | 1 577 512 600 | 50.1 | maxmin 1 577 512 600 | (none in the top 3) |
| `2020_tower_challenge_tower_070_070_30_100-05` | CAPPED | 1 105 512 061 | 1 105 505 961 | 100.0 | element 5 130, maxmin 1 105 500 831 | `X_INTRODUCED_3826_` w=48 600 024 (maxmin) |
| `2022_tower_tower_070_070_15_085-09` | CAPPED | 1 018 531 531 | 1 018 526 346 | 100.0 | element 5 130, maxmin 1 018 521 216 | `X_INTRODUCED_5027_` w=48 600 025 (maxmin) |
| `2025_tower_tower_070_070_30_100-02` | CAPPED | 863 109 844 | 863 103 744 | 100.0 | element 5 130, maxmin 863 098 614 | `X_INTRODUCED_4532_` w=48 600 026 (maxmin) |
| `2021_ATSP_instance16_0p35` | CAPPED | 1 052 848 820 | 557 426 406 | 52.9 | element 400, maxmin 557 426 006 | `X_INTRODUCED_10602_` w=4 613 880 (maxmin) |
| `2021_ATSP_instance19_0p35` | CAPPED | 591 721 207 | 373 361 249 | 63.1 | element 400, maxmin 373 360 849 | `X_INTRODUCED_5602_` w=4 613 880 (maxmin) |
| `2020_tower_challenge_tower_070_070_15_100-04` | CAPPED | 333 528 611 | 333 525 511 | 100.0 | element 2 565, maxmin 333 522 946 | `X_INTRODUCED_602_` w=24 300 009 (maxmin) |
| `2025_atsp_instance20_0p35` | CAPPED | 435 190 891 | 309 130 360 | 71.0 | element 400, maxmin 309 129 960 | `X_INTRODUCED_1702_` w=4 613 880 (maxmin) |
| `2020_tower_challenge_tower_070_070_15_070-06` | CAPPED | 290 302 769 | 290 300 599 | 100.0 | element 2 565, maxmin 290 298 034 | `X_INTRODUCED_2476_` w=24 300 011 (maxmin) |
| `2022_tower_tower_070_070_15_070-09` | CAPPED | 264 255 637 | 264 253 467 | 100.0 | element 2 565, maxmin 264 250 902 | `X_INTRODUCED_2022_` w=24 300 014 (maxmin) |
| `2022_tower_tower_500_500_50_300-01` | CAPPED | 257 300 381 | 257 271 681 | 100.0 | element 8 550, maxmin 257 263 131 | `X_INTRODUCED_3154_` w=40 743 020 (maxmin) |
| `2022_tower_tower_300_300_40_200-00` | CAPPED | 216 180 060 | 216 163 940 | 100.0 | element 6 840, maxmin 216 157 100 | `X_INTRODUCED_1287_` w=32 594 431 (maxmin) |
| `2022_tower_100_100_20_100-04` | CAPPED | 194 680 733 | 194 676 633 | 100.0 | element 3 420, maxmin 194 673 213 | `X_INTRODUCED_3040_` w=32 400 006 (maxmin) |
| `2025_atsp_instance14_0p25` | CAPPED | 351 535 950 | 177 193 710 | 50.4 | element 275, maxmin 177 193 435 | `X_INTRODUCED_1852_` w=2 686 380 (maxmin) |
| `2021_ATSP_instance9_0p25` | CAPPED | 340 121 921 | 169 781 985 | 49.9 | element 200, maxmin 169 781 785 | `X_INTRODUCED_2302_` w=2 303 880 (maxmin) |
| `2020_tower_challenge_tower_070_070_15_100-05` | CAPPED | 168 621 627 | 168 618 527 | 100.0 | element 2 565, maxmin 168 615 962 | `X_INTRODUCED_2032_` w=6 075 009 (maxmin) |
| `2025_tower_tower_070_070_15_070-02` | CAPPED | 144 580 484 | 144 578 314 | 100.0 | element 2 565, maxmin 144 575 749 | `X_INTRODUCED_2182_` w=24 300 009 (maxmin) |
| `2025_tower_tower_070_070_15_070-08` | CAPPED | 137 518 848 | 137 516 678 | 100.0 | element 2 565, maxmin 137 514 113 | `X_INTRODUCED_2343_` w=12 222 908 (maxmin) |
| `2025_tower_tower_500_500_50_300-05` | CAPPED | 134 802 415 | 134 774 815 | 100.0 | element 8 550, maxmin 134 766 265 | `X_INTRODUCED_15069_` w=10 116 936 (maxmin) |
| `2020_tower_challenge_tower_070_070_15_070-04` | CAPPED | 128 491 489 | 128 489 349 | 100.0 | element 2 565, maxmin 128 486 784 | `X_INTRODUCED_416_` w=6 075 004 (maxmin) |
| `2018_largescheduling_instance-0100-4` | CAPPED | 209 554 891 | 105 293 691 | 50.2 | maxmin 105 293 691 | (none in the top 3) |
| `2023_table-layout_p2000_m16_r1000_c200` | TIMEOUT | 104 694 066 | 104 036 266 | 99.4 | element 104 036 266 | (none in the top 3) |
| `2025_tower_tower_050_050_10_050-03` | CAPPED | 100 851 226 | 100 850 176 | 100.0 | element 1 710, maxmin 100 848 466 | `X_INTRODUCED_936_` w=16 200 005 (maxmin) |
| `2015_largescheduling_instance-0100-1` | CAPPED | 192 980 903 | 96 965 403 | 50.2 | maxmin 96 965 403 | (none in the top 3) |
| `2025_atsp_instance11_0p25` | CAPPED | 130 903 685 | 91 337 195 | 69.8 | element 275, maxmin 91 336 920 | `X_INTRODUCED_852_` w=2 686 380 (maxmin) |
| `2025_ihtc-2024-marte_i14` | CAPPED | 357 921 888 | 79 789 784 | 22.3 | element 26 838, maxmin 79 759 409, cumulative 1 226, holes 2 311 | (none in the top 3) |
| `2021_pentominoes-zayenz_size_20_tiles_15_seed_4711_strategy_source` | CAPPED | 72 387 840 | 72 382 254 | 100.0 | element 72 382 254 | `X_INTRODUCED_17535_` w=22 846 (element) |
| `2014_liner-sf-repositioning_tp7_10` | ERROR | 204 789 624 | 49 801 321 | 24.3 | gcc 252, alldiff 80, element 49 733 759, maxmin 67 230 | (none in the top 3) |
| `2025_ihtc-2024-marte_i11` | CAPPED | 250 489 100 | 36 620 392 | 14.6 | element 14 760, maxmin 36 603 186, cumulative 1 270, holes 1 176 | (none in the top 3) |
| `2023_test-scheduling_t100m20r3-14` | CAPPED | 7 295 801 | 7 068 661 | 96.9 | maxmin 7 068 420, holes 241 | `X_INTRODUCED_154_` w=35 206 (maxmin) |
| `2018_test-scheduling_t100m10r3-2` | CAPPED | 6 988 010 | 6 871 242 | 98.3 | maxmin 6 871 134, holes 108 | `X_INTRODUCED_154_` w=34 216 (maxmin) |
| `2026_saeling_instance__j0050_m016_w04_g5x5_s027` | CAPPED | 14 136 275 | 5 415 633 | 38.3 | element 25 683, maxmin 5 389 950 | (none in the top 3) |
| `2021_MZNC_connect_connect__0083_02` | CAPPED | 392 486 677 853 | 3 359 292 | 0.0 | element 3 359 284, holes 8 | (none in the top 3) |
| `2014_cyclic-rcpsp_hard_2` | CAPPED | 6 368 428 | 3 203 207 | 50.3 | alldiff 1 842, maxmin 3 172 814, cumulative 28 551 | `X_INTRODUCED_207_` w=31 314 (maxmin) |
| `2021_MZNC_connect_connect__0061` | CAPPED | 367 423 863 355 | 2 761 980 | 0.0 | element 2 761 978, holes 2 | (none in the top 3) |
| `2018_mapping_mesh_star_2` | CAPPED | 8 725 761 | 2 746 396 | 31.5 | maxmin 2 626 300, holes 120 096 | `X_INTRODUCED_5589_` w=290 700 (maxmin) |
| `2018_mapping_mesh3x3_mpeg` | CAPPED | 8 647 551 | 2 737 090 | 31.7 | maxmin 2 627 092, holes 109 998 | `X_INTRODUCED_5297_` w=290 788 (maxmin) |
| `2021_mapping_mesh_star_mpeg` | CAPPED | 8 767 551 | 2 737 090 | 31.2 | maxmin 2 627 092, holes 109 998 | `X_INTRODUCED_5588_` w=290 788 (maxmin) |
| `2023_test-scheduling_t50m20r10-17` | CAPPED | 1 788 300 | 1 734 988 | 97.0 | maxmin 1 734 821, holes 167 | `X_INTRODUCED_104_` w=17 213 (maxmin) |
| `2021_MZNC_connect_connect__0041_02` | CAPPED | 342 368 166 298 | 1 732 995 | 0.0 | element 1 732 993, holes 2 | (none in the top 3) |
| `2018_test-scheduling_t50m10r5-6` | CAPPED | 1 708 682 | 1 683 293 | 98.5 | element 435, maxmin 1 682 858 | `X_INTRODUCED_104_` w=16 691 (maxmin) |
| `2026_saeling_instance__j0050_m003_w01_g5x5_s022` | CAPPED | 2 777 565 | 1 425 099 | 51.3 | element 19 100, maxmin 1 405 999 | (none in the top 3) |
| `2015_mapping_mesh3x3_mpeg_2` | CAPPED | 4 185 267 | 1 377 298 | 32.9 | maxmin 1 267 300, holes 109 998 | `X_INTRODUCED_5297_` w=139 700 (maxmin) |
| `2016_mapping_mesh4x4_1` | CAPPED | 3 489 803 | 1 166 160 | 33.4 | maxmin 1 088 400, holes 77 760 | `X_INTRODUCED_2461_` w=67 400 (maxmin) |
| `2021_mapping_mesh4x4_2` | CAPPED | 3 489 803 | 1 166 160 | 33.4 | maxmin 1 088 400, holes 77 760 | `X_INTRODUCED_2460_` w=67 400 (maxmin) |
| `2024_yumi-dynamic_p_5_GG_GGG_yumi_grid_setup_5_5_zones` | CAPPED | 1 552 267 | 1 100 789 | 70.9 | alldiff 1 598, element 893 274, maxmin 205 917 | (none in the top 3) |

### The 8 OPTs whose proof the checker cannot finish (D-0129)

| instance | int vars | Σw | eligible Σw | % | eligible bits | held Σw | by | max w | widest |
|---|---|---|---|---|---|---|---|---|---|
| `2011_ship-schedule_6ShipsMixedUnconst` | 1 429 | 3 733 722 | 3 727 996 | 99.8 | 3 889 | 5 498 | element 5 498 | 3 600 000 | `objective` (eligible) |
| `2012_ship-schedule_5Ships` | 1 578 | 513 499 | 503 959 | 98.1 | 2 670 | 9 165 | element 9 165 | 489 500 | `X_INTRODUCED_30_` (eligible) |
| `2012_ship-schedule_6ShipsMixed` | 1 429 | 345 052 | 339 076 | 98.3 | 3 862 | 5 748 | element 5 748 | 320 400 | `X_INTRODUCED_34_` (eligible) |
| `2012_ship-schedule_7ShipsMixedUnconst` | 1 730 | 436 924 | 429 380 | 98.3 | 4 542 | 7 241 | element 7 241 | 408 000 | `X_INTRODUCED_40_` (eligible) |
| `2012_ship-schedule_8ShipsUnconst` | 2 481 | 887 042 | 872 498 | 98.4 | 4 116 | 13 944 | element 13 944 | 850 000 | `X_INTRODUCED_48_` (eligible) |
| `2014_ship-schedule_3Ships` | 977 | 281 430 | 275 676 | 98.0 | 1 758 | 5 529 | element 5 529 | 267 000 | `X_INTRODUCED_18_` (eligible) |
| `2014_smelt_smelt_2` | 40 410 | 105 218 | 54 871 | 52.1 | 448 | 10 000 | cumulative 10 000 | 14 000 | `objective` (eligible) |
| `2018_mapping_full2x2_mp3` | 602 | 97 906 | 55 762 | 57.0 | 1 691 | 41 936 | maxmin 34 160, holes 7 776 | 10 000 | `objective` (maxmin) |

### Predicates the classifier could not place

None: every `constraint` predicate in the 177 files is in the linear or the enumerating list below.

### Identifiers in constraint lines the parser could not resolve

None: every identifier in a constraint line resolved to a declared variable, array, alias, parameter or known annotation.

### Every predicate seen in the 177 files, and how it was classified

| predicate | class | occurrences | instances |
|---|---|---|---|
| `int_lin_le_reif` | linear | 8 460 387 | 137 |
| `bool2int` | linear | 5 591 997 | 163 |
| `array_bool_and` | linear | 5 254 127 | 101 |
| `bool_clause` | linear | 4 691 704 | 127 |
| `int_eq_reif` | linear | 3 488 928 | 120 |
| `int_times` | linear | 2 400 885 | 105 |
| `int_le_reif` | linear | 1 081 442 | 112 |
| `int_lin_eq` | linear | 776 534 | 171 |
| `int_ne_reif` | linear | 759 810 | 96 |
| `int_lin_le` | linear | 584 367 | 131 |
| `array_int_element` | element | 434 118 | 71 |
| `bool_not` | linear | 145 424 | 49 |
| `array_int_minimum` | maxmin | 44 468 | 26 |
| `int_ne` | linear (Ne: flagged for T2's hold) | 16 591 | 13 |
| `array_int_maximum` | maxmin | 10 352 | 76 |
| `int_abs` | linear | 2 969 | 7 |
| `bool_eq` | linear | 1 423 | 3 |
| `int_div` | linear | 511 | 12 |
| `array_bool_or` | linear | 455 | 2 |
| `baguette_global_cardinality` | gcc | 283 | 19 |
| `all_different_int` | alldiff | 96 | 15 |
| `int_le` | linear | 85 | 6 |
| `baguette_cumulative` | cumulative | 43 | 11 |
| `int_lin_ne` | linear (Ne: flagged for T2's hold) | 18 | 2 |

Contiguous set domains (`var {1,2,3}`, read as a range, no hole): 0 declarations in 0 instances; `var set` declarations (skipped, not int): 0. `.fzn` sources: kept-wave41run 8, kept-m7t27run 7, reflattened 162.

### Five largest held-back widths in the 169

- `2017_road-cons_road_33` (CAPPED): held 715 755 177 887 of Σw 716 284 177 827 (99.9 %) by maxmin 715 755 177 887
- `2017_road-cons_road_26` (CAPPED): held 268 422 271 364 of Σw 268 748 271 325 (99.9 %) by maxmin 268 422 271 364
- `2017_road-cons_road_25` (CAPPED): held 228 273 476 633 of Σw 228 574 476 519 (99.9 %) by maxmin 228 273 476 633
- `2014_road-cons_road_20` (CAPPED): held 90 419 213 330 of Σw 90 610 213 232 (99.8 %) by maxmin 90 419 213 330
- `2017_road-cons_road_18` (CAPPED): held 58 223 406 980 of Σw 58 377 406 597 (99.7 %) by maxmin 58 223 406 980

### The kept `.fzn` (not re-flattened)

- `2011_ship-schedule_6ShipsMixedUnconst` (OPT8): kept-wave41run
- `2014_liner-sf-repositioning_tp7_10` (ERROR): kept-wave41run
- `2015_largescheduling_instance-0800-1` (CAPPED): kept-m7t27run
- `2018_largescheduling_instance-0800-4` (CAPPED): kept-m7t27run
- `2018_steiner-tree_es20fst08.stp` (ERROR): kept-wave41run
- `2018_steiner-tree_es20fst09.stp` (ERROR): kept-wave41run
- `2018_steiner-tree_es20fst14.stp` (ERROR): kept-wave41run
- `2019_rcpsp-wet-diverse_j90_48_4-wet-diverse-3` (TIMEOUT): kept-m7t27run
- `2020_gbac_UD10-gbac` (ERROR): kept-wave41run
- `2022_ma-path-finding_ins_g32_p20_a10` (CAPPED): kept-m7t27run
- `2023_unit-commitment_L7-T12G5L5` (ERROR): kept-wave41run
- `2024_aircraft-disassembly_B737NG-600-04-Anon.json` (ERROR): kept-wave41run
- `2025_carpet-cutting_cc_rnd_8_1` (CAPPED): kept-m7t27run
- `2025_ihtc-2024-marte_i11` (CAPPED): kept-m7t27run
- `2025_ihtc-2024-marte_i14` (CAPPED): kept-m7t27run

