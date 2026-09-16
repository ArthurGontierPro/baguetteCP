.PHONY: build test unit models check fmt clean proof bootstrap bench

build:
	dune build

unit:
	dune runtest --force

models: build
	./scripts/run_model_tests.sh

# Unit tests and model tests. Model tests include proof checking with veripb.
test: unit models

fmt:
	@command -v ocamlformat >/dev/null 2>&1 && dune build @fmt --auto-promote || \
	  echo "ocamlformat not installed; skipping (opam install ocamlformat)"

# The gate. Run this before every commit.
check: fmt build test
	@echo "check: ok"

# Solve one model and verify its proof end to end.
#   make proof FZN=test/models/trivial_sat.fzn
proof: build
	@test -n "$(FZN)" || { echo "usage: make proof FZN=path/to/model.fzn"; exit 2; }
	./scripts/verify_proof.sh "$(FZN)"

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
	./bench/run_bench.sh $(ARGS)
