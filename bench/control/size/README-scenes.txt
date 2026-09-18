M2-T17's control corpus. One scene, `ctl_size`, a pair of hand-authored .pbp FIXTURES
(not solved from a .fzn model): bench/control/size/base/ctl_size.pbp is measured as the
tight explanation and bench/control/size/variant/ctl_size.pbp as the same derivation
deliberately widened -- extra literals named in the `rup` line that the derivation does
not need, and the matching extra premises cited in the `pol` chain that combines them.

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
  pol_prems   4 operands cited in the `pol`    7 operands cited in the same
              chain (`@c7 @c12 @c13 @c9`)      chain -- three more premises
                                                folded in for no reason
                                                (`@c1 @c2 @c3`)

`-c` fails unless BOTH rup_lits and pol_prems come out strictly larger on the variant --
a metric that only ever reports one moving is half a metric, same reasoning as M2-L8's
"both directions are required" for the CHANGED/proof-only classifier. Verified 2026-09-18
by breaking bench/explanation_size.sh's own measure_pbp on purpose:

  break                                          what it caught
  ---------------------------------------------  --------------------------------------
  rup_lits: count `is_operator` tokens instead    both fixtures report the same rup_lits
  of `is_lit_token` tokens (i.e. count the        (1.0000 -- the wrong half of the line
  wrong half of the line)                         never changes) -- -c fails on
                                                   "did not grow"
  pol_prems: count only tokens matching `@c[0-9]+`   -c still passes by accident on this
  (i.e. drop literal-pushed premises) -- not      particular fixture, because every
  broken enough to matter here, see below         premise in both files happens to be an
                                                   `@c` id already
  pol_prems: hard-code the mean to a constant     -c fails on "did not grow" for pol_prems
  (e.g. always print 4.0000)

The middle row is recorded rather than silently dropped: it shows the fixture does not
by itself distinguish "count operand tokens" from "count only @c-labelled tokens", because
neither file uses a bare-literal premise in its `pol` chain. That is a known gap in this
specific control, not in the metric definition -- width_root_unsat.fzn's real `pol` line
(see bench/explanation_size.sh's header comment) DOES push bare literals, so the
suite-wide run exercises the distinction even though this fixture does not. Widening the
fixture to also cover it is left as a small follow-up rather than done here, to keep the
control's job to what it was built to prove: literals-per-rup and premises-per-pol both
respond to a widened explanation, independently.
