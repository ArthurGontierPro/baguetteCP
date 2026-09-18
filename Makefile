# MACHINE LIMIT: this box has 15 GB of RAM, shared by every concurrent session.
# On 2026-09-16 a test binary reached 14.9 GB RSS and had to be killed by hand; later
# the same day two more had to be killed at the ceiling. Warning sessions about it
# twice did not work, so the cap is enforced here instead of documented elsewhere.
#
# Every target that RUNS something applies it. A run that dies against this cap is a
# finding to report -- a test that needs more than 4 GB is a test with a wide declared
# domain, and the order encoding is width-proportional (D-0028). Raise MEM_CAP_KB only
# with a reason you are willing to write into WORKLOG.md.
MEM_CAP_KB ?= 4000000

.PHONY: build test unit models check fmt fmt-check lint determinism clean proof bootstrap bench

build:
	dune build

unit:
	ulimit -v $(MEM_CAP_KB) && dune runtest --force

models: build
	ulimit -v $(MEM_CAP_KB) && ./scripts/run_model_tests.sh

# Unit tests and model tests. Model tests include proof checking with veripb.
test: unit models

# The explicit fixer. Rewrites files. NOT in the gate -- see fmt-check and M1-T64.
fmt:
	@command -v ocamlformat >/dev/null 2>&1 && dune build @fmt --auto-promote || \
	  echo "ocamlformat not installed; skipping (opam install ocamlformat)"

# The gate's formatting check (M1-T64). VERIFIES; it does not fix.
#
# `check` used to depend on `fmt`, which auto-promotes -- so an unformatted commit was
# never anybody's failure, it was silently repaired in the next person's working tree,
# and on 2026-09-17 that is exactly how one session's formatting debt ended up inside
# another's unrelated commit while two more sessions separately reported the same files.
# Its self-test runs FIRST, the same discipline `lint` follows: a guard nobody has seen
# fail is not yet a guard.
fmt-check:
	./scripts/check_fmt.sh --self-test
	./scripts/check_fmt.sh

# The declared-width lint (M1-T53's sibling). Its self-test runs FIRST and on every
# gate, so the guard re-proves it can fail before it is trusted to pass -- three test
# binaries died at the memory ceiling because a width went unnoticed, and the first
# draft of this lint waved the real line through.
lint:
	./scripts/check_test_widths.py --self-test
	./scripts/check_test_widths.py

# Artefact determinism (M2-T12): two runs of the same binary on the same model must
# agree byte for byte. Needs bin/main.exe, hence the `build` dependency -- `dune runtest`
# does not build it, which is the trap CLAUDE.md records. Self-test first, as `lint` and
# `fmt-check` do. It deliberately compares runs against EACH OTHER rather than against a
# stored digest: a committed hash would be wrong on the next legitimate proof change
# (M1-T29 moved 14 of 34 .pbp files, correctly) and would train people to re-bless it.
determinism: build
	ulimit -v $(MEM_CAP_KB) && ./scripts/check_determinism.sh --self-test
	ulimit -v $(MEM_CAP_KB) && ./scripts/check_determinism.sh

# The gate. Run this before every commit.
#
# The verdict line is CONDITIONAL, and that is the point. `check_fmt.sh` treats a missing
# ocamlformat as a loud skip rather than a failure -- a deliberate asymmetry with
# checker.sh, argued in that script's own header: veripb verifies a correctness property
# so a missing one makes the run worthless, ocamlformat verifies a cosmetic one so
# refusing to run the gate without it would block real work over whitespace. That
# reasoning is sound and this does not overturn it.
#
# What it fixes is narrower: the banner announcing the skip scrolls past, and `check: ok`
# was printed anyway -- so the ONE line a hurried human or a CI log reads said the gate
# passed when part of it had not run. On 2026-09-18 the orchestrator hit exactly this,
# having forgotten `eval "$$(opam env --switch=baguette)"`. A gate that reports a pass it
# did not earn is this project's signature failure mode (D-0020, D-0030: a lane rejected
# without the checker ever judging an inference is not a pass), and it does not stop being
# that because the unearned part is only whitespace.
#
# Still exit 0 when ocamlformat is absent. The skip is allowed; claiming it did not happen
# is not.
check: fmt-check build lint determinism test
	@if command -v ocamlformat >/dev/null 2>&1; then \
	  echo "check: ok"; \
	else \
	  echo "=========================================================================="; \
	  echo "check: ok EXCEPT formatting, which was NOT verified -- ocamlformat was not"; \
	  echo "       on PATH, so fmt-check skipped. This is not a full gate pass."; \
	  echo "       Fix: eval \"\$$(~/.local/bin/opam env --switch=baguette)\" and re-run."; \
	  echo "=========================================================================="; \
	fi

# Solve one model and verify its proof end to end.
#   make proof FZN=test/models/trivial_sat.fzn
proof: build
	@test -n "$(FZN)" || { echo "usage: make proof FZN=path/to/model.fzn"; exit 2; }
	ulimit -v $(MEM_CAP_KB) && ./scripts/verify_proof.sh "$(FZN)"

bootstrap:
	./scripts/bootstrap.sh

clean:
	dune clean
	rm -rf test/out

# Measurement, deliberately NOT a dependency of `check`: a benchmark that gates a
# commit becomes a flaky test. M3-T5. Pass arguments through, e.g.
#   make bench ARGS="-r 9"
# Read bench/README.md first -- in particular, on the current models 23 of the 38 rows
# are at the process floor, so their timing columns measure exec and not this solver.
bench: build
	ulimit -v $(MEM_CAP_KB) && ./bench/run_bench.sh $(ARGS)
