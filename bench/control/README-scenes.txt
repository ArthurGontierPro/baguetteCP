M2-L8's control corpus. Two SCENES, each a pair of models that share a basename:
bench/control/base/NAME.fzn is measured as configuration A, bench/control/variant/NAME.fzn
as configuration B, and `bench/run_bench.sh -c` asserts the verdict the comparison table
prints for each.

The pairing is by basename because that is how run_bench.sh's comparison table joins its
two configurations, so the control exercises the real join and the real classifier rather
than a stub of them.

Why a pair of MODELS and not a pair of solver configurations: until D-0046 the
proof-only scene was produced by re-running one model under proof format 2.0, and that
knob no longer exists. `--proof-comments` cannot replace it -- it is a documented no-op
on every shipped model (bin/main.ml's own usage text says so) -- and every other knob
the CLI has either changes nothing or changes the tree. Two models, one tree, two
proofs is the shape that is still available without a lib/ change.

This rests on M1-T37's self-check, which is run before any measurement: .opb bytes are a
property of the model, not of the path it was given. The two scenes live in different
directories, so if that property ever broke, every control row would differ for a reason
that has nothing to do with what it is testing -- and the self-check would say so and
exit non-zero before the control ran.

Domains are 0..1 and 0..3 throughout (D-0028).
