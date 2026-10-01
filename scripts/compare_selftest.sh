#!/usr/bin/env bash
# M6-T4. Proves every bucket of scripts/compare_run.sh is REACHABLE, including the one
# the harness exists for: DISAGREE.
#
# `scripts/compare_run.sh --self-test` runs this. A three-model synthetic corpus in a
# temp dir, run through the REAL harness with the REAL baguette and the REAL checker,
# and two shims standing in for Chuffed and GCS:
#
#   sat/sat.mzn      satisfiable          baguette SAT    chuffed-shim SAT     gcs-shim UNSAT
#   unsat/unsat.mzn  unsatisfiable        baguette UNSAT  chuffed-shim REFUSED gcs-shim UNSAT
#   opt/opt.mzn      minimise, optimum 1  baguette OPT    chuffed-shim OPT     gcs-shim UNSAT
#
# The gcs shim is deliberately WRONG -- it answers UNSAT to everything -- so `sat` and
# `opt` must come out DISAGREE and `unsat` AGREE. A harness that cannot be seen to
# report a disagreement has not been shown able to (the discipline of
# corpus_selftest.sh: a guard that has not been seen to fail is not yet a guard). The
# shim also logs no proof, so GCS's NO-PROOF verdict is reached too; baguette's three
# proofs must each be VERIFIED by veripb, and the optimisation model's objective is
# NOT an output variable in the source, so `min:1` in baguette's row proves the
# objective injection (compare.py prep) worked.
#
# minizinc: the real one if it is on PATH (shim .msc files with an empty mznlib), else
# a stub that copies the model to -o. The models are written in the intersection of
# MiniZinc and FlatZinc so the stub's copy IS a valid FlatZinc file.
#
# It cannot SKIP: no baguette binary or no veripb is a loud FAIL, exit 1.

set -u

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
D="$(mktemp -d)"
trap 'rm -rf "$D"' EXIT INT TERM
fails=0
fail() {
  echo "FAIL $*"
  fails=$((fails + 1))
}

BAGUETTE="${BAGUETTE:-$ROOT/_build/default/bin/main.exe}"
if [ ! -x "$BAGUETTE" ]; then
  echo "compare self-test: FAIL -- no baguette at $BAGUETTE. Build it first:"
  echo "    dune build --root . bin/"
  echo "  This is NOT a skip: an unrun self-test has proved nothing."
  exit 1
fi
# shellcheck source=/dev/null
. "$ROOT/scripts/checker.sh"
if ! baguette_resolve_veripb; then
  baguette_veripb_diagnostic
  echo "compare self-test: FAIL -- no checker, so baguette's proofs cannot be checked."
  exit 1
fi
command -v python3 > /dev/null 2>&1 || {
  echo "compare self-test: FAIL -- python3 is required."
  exit 1
}

C="$D/corpus/2099"
mkdir -p "$C/sat" "$C/unsat" "$C/opt" "$D/bin" "$D/msc/empty-lib" "$D/out"
cat > "$C/sat/sat.mzn" <<'M'
var 1..3: s_x :: output_var;
var 1..3: s_y :: output_var;
constraint int_lt(s_x, s_y);
solve satisfy;
M
cat > "$C/unsat/unsat.mzn" <<'M'
var 1..3: u_x :: output_var;
var 1..3: u_y :: output_var;
constraint int_lin_le([1, -1], [u_x, u_y], -1);
constraint int_lin_le([-1, 1], [u_x, u_y], -1);
solve satisfy;
M
cat > "$C/opt/opt.mzn" <<'M'
var 1..5: o_x :: output_var;
var 1..5: o_y;
constraint int_lin_le([-1, -1], [o_x, o_y], -6);
solve minimize o_y;
M

# The honest-ish Chuffed stand-in: right on sat and opt, REFUSES unsat.
cat > "$D/bin/chuffed-shim" <<'S'
#!/usr/bin/env bash
f="${*: -1}"
if grep -q u_x "$f"; then echo "Error: constraint int_lin_le is not supported" >&2; exit 1; fi
if grep -q o_y "$f"; then printf 'o_y = 2;\n----------\no_y = 1;\n----------\n==========\n'; exit 0; fi
printf 's_x = 1;\ns_y = 2;\n----------\n'
S
# The deliberately WRONG GCS stand-in: UNSAT to everything, and no proof.
cat > "$D/bin/gcs-shim" <<'S'
#!/usr/bin/env bash
echo '=====UNSATISFIABLE====='
S
chmod +x "$D/bin/chuffed-shim" "$D/bin/gcs-shim"
for n in chuffed gcs; do
  cat > "$D/msc/$n-shim.msc" <<J
{ "id": "org.selftest.$n-shim", "name": "$n-shim", "version": "0",
  "mznlib": "$D/msc/empty-lib", "executable": "$D/bin/$n-shim",
  "supportsFzn": true, "needsSolns2Out": true }
J
done

if command -v minizinc > /dev/null 2>&1; then
  MZN="$(command -v minizinc)"
  echo "compare self-test: using the real minizinc at $MZN"
else
  MZN="$D/bin/minizinc"
  cat > "$MZN" <<'S'
#!/usr/bin/env bash
# Stub: `--solvers` lists the ids the harness asks for; `-c ... MODEL -o OUT` copies
# the FIRST .mzn (a second one is the COMPAT shim file, which the stub ignores).
if [ "${1:-}" = --solvers ]; then
  echo "org.baguette.baguette org.selftest.chuffed-shim org.selftest.gcs-shim"
  exit 0
fi
out=""
model=""
while [ $# -gt 0 ]; do
  case "$1" in
    -o) out="$2"; shift ;;
    --solver) shift ;;
    *.mzn) [ -n "$model" ] || model="$1" ;;
  esac
  shift
done
[ -n "$out" ] && [ -n "$model" ] || exit 1
cp "$model" "$out"
S
  chmod +x "$MZN"
  echo "compare self-test: no minizinc on PATH; using a stub that copies the model"
fi

run() {
  env MZN="$MZN" BAGUETTE="$BAGUETTE" CHUFFED="$D/bin/chuffed-shim" GCS="$D/bin/gcs-shim" \
    GCS_MSC_DIR="$D/msc" EXTRA_MSC_DIR="$D/msc" \
    CHUFFED_MZN_ID=org.selftest.chuffed-shim GCS_MZN_ID=org.selftest.gcs-shim \
    SOLVE_TIMEOUT=60 CHECK_TIMEOUT=60 MEM_KB=4000000 PROOF_CAP_KB=100000 "$@" \
    "$ROOT/scripts/compare_run.sh" "$D/corpus" "$D/out"
}

PAR=40 run > "$D/run1.log" 2>&1
grep -q 'capping PAR at 16' "$D/run1.log" \
  && echo "ok   PAR=40 x 3 solvers is capped at 16 per solver (48 total)" \
  || fail "PAR=40 with 3 solvers was not capped to 16 -- the 48-job budget is unenforced"

R="$D/out/results.tsv"
# $1 id $2 solver $3 column number $4 expected
expect_col() {
  local got
  got="$(awk -F'\t' -v i="$1" -v s="$2" -v c="$3" '$1 == i && $2 == s {print $c}' "$R")"
  if [ "$got" = "$4" ]; then
    echo "ok   $1/$2 column $3 -> $got"
  else
    fail "$1/$2 column $3: expected '$4', got '$got'"
    awk -F'\t' -v i="$1" -v s="$2" '$1 == i && $2 == s' "$R" | sed 's/^/     row: /'
  fi
}
expect_col 2099_sat baguette 3 SAT
expect_col 2099_sat baguette 10 VERIFIED
expect_col 2099_unsat baguette 3 UNSAT
expect_col 2099_unsat baguette 10 VERIFIED
expect_col 2099_opt baguette 3 OPT
expect_col 2099_opt baguette 5 min:1
expect_col 2099_opt baguette 10 VERIFIED
expect_col 2099_sat chuffed 3 SAT
expect_col 2099_unsat chuffed 3 REFUSED
expect_col 2099_opt chuffed 3 OPT
expect_col 2099_opt chuffed 5 min:1
expect_col 2099_opt chuffed 10 -
expect_col 2099_sat gcs 3 UNSAT
expect_col 2099_sat gcs 10 NO-PROOF

grep -q '^DONE-' "$R" && echo "ok   the run wrote its DONE marker" \
  || fail "no DONE marker after a complete run"

python3 "$ROOT/tools/compare/compare.py" report "$D/out" > "$D/report.txt" 2>&1
grep -q 'DISAGREE: 2 instance' "$D/report.txt" \
  && echo "ok   report: 2 DISAGREE (sat, opt) -- the wrong shim was caught" \
  || fail "report did not find exactly 2 DISAGREE; the oracle is blind"
grep -q 'SOUNDNESS(baguette) 2099_sat' "$D/report.txt" \
  && echo "ok   report: the sat disagreement is tagged as involving baguette" \
  || fail "the sat disagreement was not tagged SOUNDNESS(baguette)"
grep -q 'AGREE 1 ' "$D/report.txt" \
  && echo "ok   report: unsat AGREEs (baguette UNSAT, gcs-shim UNSAT, chuffed REFUSED)" \
  || fail "unsat did not AGREE"
d="$(grep -n '== DISAGREE' "$D/report.txt" | cut -d: -f1)"
t="$(grep -n '== status by solver' "$D/report.txt" | cut -d: -f1)"
[ -n "$d" ] && [ -n "$t" ] && [ "$d" -lt "$t" ] \
  && echo "ok   report prints DISAGREE before the status table" \
  || fail "the DISAGREE list is not printed first"

rows1="$(grep -vc '^DONE-' "$R")"
run > "$D/run2.log" 2>&1
rows2="$(grep -vc '^DONE-' "$R")"
[ "$rows1" = "$rows2" ] && [ "$rows1" = 9 ] \
  && echo "ok   resumption: 9 rows, and a second run recomputed nothing" \
  || fail "rows: first run $rows1 (want 9), after resume $rows2"

# Pinned answers: the agreed answer of a run is pinned, and a run that contradicts a pin
# is reported. Pin from this run (sat/opt are DISPUTED and must be pinned as such).
python3 "$ROOT/tools/compare/compare.py" answers "$D/out" "$D/answers.tsv" > /dev/null
grep -qP '^2099_unsat\tUNSAT\t' "$D/answers.tsv" && grep -qP '^2099_sat\tDISPUTED\t' "$D/answers.tsv" \
  && echo "ok   answers: unsat pinned UNSAT, sat pinned DISPUTED (never silently dropped)" \
  || fail "answers.tsv does not pin unsat=UNSAT and sat=DISPUTED"
printf 'id\tanswer\tobjective\tby\tdata\n2099_opt\tOPT\tmin:2\ttest\t<none>\n' > "$D/pin.tsv"
python3 "$ROOT/tools/compare/compare.py" report "$D/out" --pinned "$D/pin.tsv" > "$D/r2.txt"
grep -q 'PIN-MISMATCH 2099_opt baguette' "$D/r2.txt" \
  && echo "ok   a run contradicting a pinned optimum is reported PIN-MISMATCH" \
  || fail "a contradicted pin was not reported"

# Every status the harness can assign that this corpus reaches, listed once.
echo "     statuses reached: $(grep -v '^DONE-' "$R" | cut -f3 | sort -u | tr '\n' ' ')"
echo "     verdicts reached: $(grep -v '^DONE-' "$R" | cut -f10 | sort -u | tr '\n' ' ')"

if [ "$fails" -eq 0 ]; then
  echo "compare self-test: PASS"
  exit 0
fi
echo "compare self-test: $fails FAIL"
echo "---- run log"; tail -30 "$D/run1.log"
exit 1
