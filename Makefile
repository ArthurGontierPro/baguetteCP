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

.PHONY: build test unit models check fmt lint clean proof bootstrap bench

build:
	dune build

unit:
	ulimit -v $(MEM_CAP_KB) && dune runtest --force

models: build
	ulimit -v $(MEM_CAP_KB) && ./scripts/run_model_tests.sh

# Unit tests and model tests. Model tests include proof checking with veripb.
test: unit models

fmt:
	@command -v ocamlformat >/dev/null 2>&1 && dune build @fmt --auto-promote || \
	  echo "ocamlformat not installed; skipping (opam install ocamlformat)"

# The declared-width lint (M1-T53's sibling). Its self-test runs FIRST and on every
# gate, so the guard re-proves it can fail before it is trusted to pass -- three test
# binaries died at the memory ceiling because a width went unnoticed, and the first
# draft of this lint waved the real line through.
lint:
	./scripts/check_test_widths.py --self-test
	./scripts/check_test_widths.py

# The gate. Run this before every commit.
check: fmt build lint test
	@echo "check: ok"

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
#   make bench ARGS="-F 2.0"
# Read bench/README.md first -- in particular, on the current models fifteen of the
# eighteen rows are at the process floor, so their timing columns measure exec and
# not this solver.
bench: build
	ulimit -v $(MEM_CAP_KB) && ./bench/run_bench.sh $(ARGS)
