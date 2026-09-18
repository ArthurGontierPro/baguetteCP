M2-T17's control corpus. One scene, `ctl_size`, a pair of hand-authored .pbp FIXTURES
(not solved from a .fzn model): bench/control/size/base/ctl_size.pbp is measured as the
tight explanation and bench/control/size/variant/ctl_size.pbp as the same derivation
deliberately widened -- extra literals named in the `rup` line that the derivation does
not need, and extra bare-literal premises folded into the `pol` chain that combines it,
holding the chain's `@c`-labelled premises fixed so the widening is provably attributable
to the bare-literal part (see "This is deliberate, not incidental" below).

Why a fixture .pbp and not a base/.fzn + variant/.fzn pair, unlike bench/control/{base,
variant}/ (M2-L8's scene for run_bench.sh's proof-only-vs-CHANGED classifier): there is
no lever in the CLI or the FlatZinc front end that widens an explanation on purpose --
that choice is made inside a propagator, in lib/, which M2-T17 does not own and must not
edit (bench/**-only per the wave-sixteen dispatch). A hand-written proof fixture is the
only way to exhibit "sound but maximally weak" -- exactly the failure mode
docs/EXPLANATION-REVIEW.md section 5 warns about -- without touching the solver.

Both files are syntactically well-formed VeriPB 3.0 proof text but are NOT run through
the checker and are not meant to be: they exist only to be read by
bench/explanation_size.sh's own parser, the same way a unit test fixture exercises a
parser without needing to be a real program.

`.gitignore` excludes `*.pbp` project-wide, because every other `.pbp` in this tree is a
generated artefact of a solve. These two are the one deliberate exception -- committed
fixtures, not generated output -- and were added with `git add -f` for that reason; if
this scene is ever regenerated, force-add stays necessary.

What must move, and how bench/explanation_size.sh -c asserts it:

  metric      base (tight)                    variant (widened)
  rup_lits    1 literal on three filler        1 literal on the same three
              `rup` lines and 3 literals on    filler lines and 6 literals on
              the one that states the          the same explanation line
              explanation (`@c9`) -- mean      (`@c9`) -- three unrelated
              1.5000 over n=4 `rup` lines      facts named that the derivation
                                                does not need -- mean 1.7143
                                                over n=7 `rup` lines
  pol_prems   6 operands cited in the `pol`    9 operands cited in the same
              chain: `@c7 @c12 @c13 @c9`       chain: the SAME four `@c` ids,
              (4 constraint ids) plus          plus the SAME two bare literals
              `v4_ge_1 v5_ge_1` (2 bare-       `v4_ge_1 v5_ge_1`, plus three
              literal premises, pushed as      MORE bare-literal premises
              their own unit axioms rather     (`v6_ge_0 v7_ge_1 v8_ge_0`) --
              than cited by id)                widened in the bare-literal part
                                                specifically, `@c`-id count
                                                unchanged at 4

This is deliberate, not incidental: `@c`-labelled premises and bare-literal premises are
both real in this proof format (a `pol` chain cites an existing constraint by id OR pushes
a literal as its own unit axiom), and bare literals are not a corner case -- they are the
DOMINANT case in the largest real figure this benchmark reports. `width_root_unsat.fzn`'s
single `pol` line is ~2000 bare-literal premises and a handful of `@c` ids; an ordinary
model's `pol` line is often `@c6 v1_ge_1 v1_ge_2 + + ;`, i.e. mostly bare literals too. A
control that only ever widened the `@c`-id part would leave that dominant token class
completely unprotected, so the fixture's variant widens ONLY the bare-literal part,
holding the `@c`-id count fixed at 4 in both files -- that is what makes break (3) below
bite.

`-c` fails unless BOTH rup_lits and pol_prems come out strictly larger on the variant --
a metric that only ever reports one moving is half a metric, same reasoning as M2-L8's
"both directions are required" for the CHANGED/proof-only classifier. Verified 2026-09-18,
re-verified 2026-09-18 after widening for bare literals, by breaking
bench/explanation_size.sh's own measure_pbp on purpose:

  break                                          what it caught
  ---------------------------------------------  --------------------------------------
  rup_lits: count `is_operator` tokens instead    both fixtures report the same rup_lits
  of `is_lit_token` tokens (i.e. count the        (1.0000 -- the wrong half of the line
  wrong half of the line)                         never changes) -- -c fails on
                                                   "did not grow"
  pol_prems: count only tokens matching `@c[0-9]+`   both fixtures report the same
  (i.e. drop literal-pushed premises)             pol_prems (4.0000 -- the `@c`-id count
                                                   is fixed on purpose) -- -c fails on
                                                   "did not grow"
  pol_prems: hard-code the mean to a constant     -c fails on "did not grow" for pol_prems
  (e.g. always print 6.0000)

Before the widening above, this fixture's `pol` chain used only `@c`-labelled premises on
both sides, so restricting the count to `@c[0-9]+` tokens happened to grow anyway (every
premise was an `@c` id already) and break (3) passed by accident -- a hole the orchestrator
found and asked to be closed, since it meant a regression in bare-literal counting would
silently move the headline `pol_prems` figure (bare-literal-dominated, per the paragraph
above) with no lane going red. Closed by holding the `@c`-id count fixed across base and
variant and widening only the bare-literal part, so a count that drops bare literals now
provably cannot tell the two files apart.
