# bits_spike — RUP, `pol` and elaboration on the checker alone (M8-bits-encoding-T0)

A checker-only measurement, recorded as **D-0127**. One Python generator writes the SAME
bound propagation four ways — in the order encoding and in a bits encoding, as one `rup`
line and as explicit `pol` lines — over a satisfiable model whose width runs from 10³ to
10⁶. VeriPB 3.0.2 checks each pair, `veripb -e` elaborates it, `cake_pb` checks the
elaboration. No solver code is involved; what is measured is how a justification should be
WRITTEN, which is the question `M8-bits-encoding-T1` has to settle before the solver grows a
second encoding.

Everything here ran on `fataepyc-06` (`~/.cargo/bin/veripb` 3.0.2 Rust build d5644ca4,
`/scratch/arthur/cake_pb` of 2026-08-25), on 2026-11-06, sequentially, one checker at a
time, under `ulimit -v 16777216`. `results.tsv` is the run's table verbatim.

## The derivation

`gen.py`'s docstring is the specification; in short:

```
a in [l, w]   b in [0, w]   z in {0, 1}       l = w//4,  c = l + w//2,  m = c - l + 1
R:  a + b <= c          T:  z  or  b >= m         min z
```

The propagation is the root pruning `Linear` makes from `R` with `a` at its declared
lower bound, `b <= c - l`, i.e. the literal `~b_ge_m`. The proof then derives `z >= 1`
from `T` and that literal (line `Z`, a `pol` that CITES the pruning) and concludes
`BOUNDS 1 : Z INF`. The model is satisfiable (a = l, b = 0, z = 1), so `red`, `pol` and
`rup` lines are judged rather than waved through (D-0053, D-0066).

| arm | the `.opb` | the pruning as `pol` | as `rup` |
|---|---|---|---|
| **order** | `x_ge_v` for `l < v <= w`, the ladder rungs, `R` as the encoding's expansion with its constant against the declared bound (PROOF-FORMAT §3, D-0028) | `@R`, weaken every `a` literal, fold `b`'s ladder up to rung m−1 with a growing multiplier (`@lb_v v * +`, lib/core/ladder.ml's step), weaken `b` above m, `s` — Θ(w) tokens | `rup +1 ~b_ge_m >= 1 ;` |
| **bits** | `bit_length(w)` bits per variable plus two bound rows; `[b >= m]` is NOT in the `.opb` and is minted by a `red` pair whose witness touches only the fresh atom (the M8 preamble's shape, not D-0031's rotation) | `pol @R @Alo + @B1 + s` — three citations | the same `rup` |

Both styles carry an `e` pin (`e +1 ~b_ge_m >= 1 : @G`) so a `pol` that derives
something else is refused where it happens (M1-T51's control). In the bits arm `Z` also
needs the atom's second direction (`@B2`) to turn `~b_ge_m` back into a bound on the bits.

### What makes the lines load-bearing

The first design concluded `BOUNDS -c INF` on `min -b`, and the elaborator cited **`R`
itself** as the lower bound's justification: a root bound from declared bounds is a
weakening of the row, so the Θ(w) literal derivation was decoration. Hence `z`, `T` and a
conclusion that cites a `pol` consuming the pruning. The control that proves it:
`control-noG` replaces the pruning line with a copy of `R` and drops the pin; it is refused
at the conclusion in all 16 pairs ("Expected constraint is not syntactically implied by
the constraint at the hint.").

## How to run

```sh
python3 -I bench/bits_spike/gen.py --out out/x --widths 12          # laptop: syntax only
bench/bits_spike/run.sh /scratch/arthur/wave41-spike/out/full       # node: the table
bench/bits_spike/diag.sh /scratch/arthur/wave41-spike/out/full      # node: per-operator pol
```

`run.sh` writes `results.tsv`; one row per (width, arm, style, variant). Verdicts are the
checker's own `s …` line or its "Checking error" sentence, never an exit status: `cake_pb`
**exits 0 on a refusal** and says `c Checking failed …` (measured on the raw, labelled
proof, which it cannot parse).

## Results

Times are CPU seconds from `/usr/bin/time -v` (user + sys; every tool is single-threaded
and wall agrees to 0.1 s); RSS is max resident set. "V" is `s VERIFIED BOUNDS 1 <= obj <= INF`.

### VeriPB 3.0.2 on the proof

| w | arm | style | `.opb` B | `.pbp` B | verdict | s | RSS MB |
|---|---|---|---|---|---|---|---|
| 10³ | order | rup | 90 592 | 188 | V | 0.00 | 19 |
| 10³ | order | pol | 90 592 | 21 696 | V | 0.00 | 19 |
| 10³ | bits | rup | 978 | 542 | **REJECTED**, not RUP | 0.00 | 11 |
| 10³ | bits | pol | 978 | 542 | V | 0.00 | 11 |
| 10⁴ | order | rup | 975 595 | 191 | V | 0.01 | 41 |
| 10⁴ | order | pol | 975 595 | 237 949 | V | 0.05 | 41 |
| 10⁴ | bits | rup | 1 404 | 680 | **REJECTED**, not RUP | 0.00 | 11 |
| 10⁴ | bits | pol | 1 404 | 679 | V | 0.00 | 11 |
| 10⁵ | order | rup | 10 455 598 | 194 | V | 0.20 | 201 |
| 10⁵ | order | pol | 10 455 598 | 2 602 952 | V | **4.09** | 175 |
| 10⁵ | bits | rup | 1 746 | 787 | **REJECTED**, not RUP | 0.00 | 11 |
| 10⁵ | bits | pol | 1 746 | 785 | V | 0.00 | 11 |
| 10⁶ | order | rup | 111 555 601 | 197 | V | 2.58 | 1 553 |
| 10⁶ | order | pol | 111 555 601 | 28 277 955 | V | **383.05** | 1 268 |
| 10⁶ | bits | rup | 2 109 | 903 | **REJECTED**, not RUP | 0.00 | 11 |
| 10⁶ | bits | pol | 2 109 | 900 | V | 0.00 | 11 |

The checker's own `--stats` time agrees (10⁶ order: 2.45 s rup, 383.1 s pol; bits pol
0.4 ms at every width). The `control-noG` rows give the parse-only baseline for the
order `.opb`: 0.15 s at 10⁵ and 1.8–1.9 s at 10⁶, so the `rup` CHECK proper is ~0.05 s
and ~0.7 s, the `pol` ~3.9 s and ~381 s.

### Elaboration (`veripb -e`) and `cake_pb` on it

| w | arm | style | elab B | elab s | elab RSS MB | cake_pb | s | RSS MB |
|---|---|---|---|---|---|---|---|---|
| 10³ | order | rup | 2 407 | 0.00 | 19 | V | 0.02 | 26 |
| 10³ | order | pol | 20 017 | 0.00 | 19 | V | 0.03 | 29 |
| 10³ | bits | pol | 491 | 0.00 | 11 | V | 0.00 | 1.6 |
| 10⁴ | order | rup | 27 661 | 0.02 | 43 | V | 0.36 | 260 |
| 10⁴ | order | pol | 221 520 | 0.05 | 43 | V | 0.39 | 293 |
| 10⁴ | bits | pol | 619 | 0.00 | 11 | V | 0.00 | 1.5 |
| 10⁵ | order | rup | 325 165 | 0.22 | 231 | V | 4.09 | 2 863 |
| 10⁵ | order | pol | 2 439 023 | 4.08 | 207 | V | 4.75 | 3 213 |
| 10⁵ | bits | pol | 718 | 0.00 | 11 | V | 0.00 | 3.0 |
| 10⁶ | order | rup | 3 750 169 | 2.67 | 1 936 | V | 34.33 | 4 310 |
| 10⁶ | order | pol | 26 639 026 | 380.86 | 1 634 | V | 49.27 | 4 370 |
| 10⁶ | bits | pol | 826 | 0.00 | 11 | V | 0.00 | 3.1 |

(The rejected bits/rup pairs have no elaboration: the elaborator stops at the refused
line and writes a truncated file, which `cake_pb` refuses with "Unexpected EOF".)

What the elaborator re-emits on this build (d5644ca4), measured on these files:

- labels are dropped and every citation is renumbered (D-0102's trap), the `e` pins are
  **dropped entirely**, `output`/`conclusion` are kept and the conclusion keeps its hint;
- a `rup C ;` becomes `rup C : <ids> ;` with the ids its unit propagation used, `~` for
  the negated claim — in the order arm that is the m−1 ladder rungs it walked plus `R`,
  about 7.5 bytes per rung (3.75 MB at 10⁶);
- a `pol` is copied as is (labels to numbers), so the elaborated `pol` is the `pol`;
- a `red` becomes `red C : witness : subproof` / `qed;` — an explicit, empty subproof.
- **Elaborating costs the same as checking** (2.67 s vs 2.58 s; 380.9 s vs 383.1 s): the
  elaborator is the checker with the hints written down, and a `rup` costs it nothing
  extra to "reconstruct".

`cake_pb` needs the elaboration: on the raw proof it fails to parse the first labelled
line. On the elaborated proof it verifies all 12 accepted pairs. Its RSS is the CakeML
heap, 4.3 GB at 10⁶ for a 111 MB `.opb` in both styles, 3 MB in the bits arm.

### Variants: every lane refused with the checker's wording, at all four widths

| variant | arm/style | refused at | wording |
|---|---|---|---|
| `broken` (claim literal flipped) | order/rup, bits/rup | the `rup` | "The constraint is not implied by reverse unit propagation (RUP) from core and derived database." |
| `broken` (fold one rung too high: b ≤ c−l+1, a weaker true bound) | order/pol | the `e` pin | "Expected constraint is not equal to the constraint at the hint." |
| `broken` (`@B2` cited where `@B1` belongs) | bits/pol | the `e` pin | same |
| `broken-red-B1` (witness `b_ge_m -> 1`) | bits/* | the `red` | "Proofgoal #1 could not be autoproven. Please add an explicit subproof for proofgoal #1." |
| `broken-red-B2` (witness `b_ge_m -> 0`) | bits/* | the `red` | same — **but see below** |
| `control-noG` (pruning line is a copy of `R`, no pin) | all | the conclusion | "Expected constraint is not syntactically implied by the constraint at the hint." |

**`B2` is vacuous in principle and judged only by accident.** For a ROOT pruning the atom
it mints is decided by the model (b ≥ m is impossible), so the negation of `B2` contradicts
the database and every redundance goal is implied — D-0053's vacuity, one step out. The
checker judges it anyway here only because its unit propagation does not SEE that
contradiction (three constraints, two variables, over bits): with `a`'s lower bound at 0
(a first design, w = 10) the same wrong witness was `s VERIFIED`. A test of `ensure_atom`'s
witness must therefore mint an atom the model does not decide, or it tests nothing.

### Which `pol` operator is quadratic (`diag.sh`, `diag-results.tsv`)

One operator kind per proof, over the order arm's `model.opb`, concluding NONE:

| w | variant | ops | `.pbp` B | checker s | RSS MB |
|---|---|---|---|---|---|
| 10⁵ | `weaken`, every literal of a and b | 175 000 | 2 264 011 | 0.21 | 171 |
| 10⁵ | `sum`, `@lb_v +` for v < m | 50 000 | 589 009 | 17.17 | 171 |
| 10⁵ | `fold`, `@lb_v v * +` for v < m | 50 000 | 977 899 | 12.69 | 169 |
| 10⁵ | `foldT`, the fold from the 2-term row `T` | 50 000 | 977 899 | 3.07 | 167 |
| 10⁶ | `weaken` | 1 750 000 | 24 389 013 | 2.49 | 1 152 |
| 10⁶ | `sum` | 500 000 | 6 389 011 | **1 754.35** | 1 166 |
| 10⁶ | `fold` | 500 000 | 10 777 902 | **1 291.64** | 1 199 |
| 10⁶ | `foldT` | 500 000 | 10 777 902 | 290.99 | 1 221 |

Weakening is linear (1.4 µs an op). Every addition of a rung into the accumulator costs time
proportional to the accumulator's width, with or without the multiplier: ×95 to ×102 for ×10 in
width, quadratic in w from `R` and in m from the two-term `T`. The `sum`, which cancels nothing,
is slower than the fold, which removes one term a step. The run's full `pol` (4.09 s, 383 s) is
cheaper than its fold alone because the `a` weakenings come first and shrink the accumulator.

## Reading

1. **In the order arm, `rup` beats `pol` on every axis the checker can measure.** The same
   Θ(w)-rung cancellation costs the checker 0.7 s as a RUP check and 381 s as an explicit
   `pol` at w = 10⁶ (×4 s / 0.05 s at 10⁵: the `pol` is quadratic in w, the RUP linear and
   parse-dominated). The `rup` line is 197 bytes against 28 MB. D-0028 measured 12 s for
   its 2w-weakening `pol`; a *fold* is a different operator and a different exponent.
2. **The prior "`pol` elaborates better than `rup`" is not what the checker does.** The
   elaborator re-emits a `pol` unchanged and a `rup` as a hint list: 26.6 MB against
   3.75 MB at 10⁶, produced in the same time as checking. `cake_pb` then checks the hinted
   RUP in 34 s and the `pol` in 49 s. A RUP "reconstructed by the elaborator" costs the
   solver nothing and the checker its ordinary propagation.
3. **In the bits arm there is no `rup`.** A bound does not cross a row by unit propagation
   on bits — refused at 10³ already, and at every width — so every such step is a `pol`,
   as GCS found. That `pol` is three citations, 0.4 ms and 11 MB, flat from 10³ to 10⁶;
   its elaboration is under 1 kB and `cake_pb` checks it in no measurable time.
4. **The bits arm's price is the atom pair, not the derivation**: two `red` lines of
   O(log w) bytes, plus `B2` to use the literal again in a row. One of the pair is unjudged
   for a root pruning (above).

The sentence for T1: **justifications are written as `rup` wherever the checker's unit
propagation can close them (the order encoding, and any derived clause over existing
atoms) and as `pol` only where it cannot (every bound that crosses a bits row), because a
Θ(w)-token `pol` is quadratic for VeriPB 3.0.2, its elaboration is the `pol` itself, and
a `rup` elaborates to a hint list the verified checker handles faster.**
