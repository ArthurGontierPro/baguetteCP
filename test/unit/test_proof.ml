(* Unit tests for the proof layer: literal naming, OPB rendering, proof emission.

   Literal names are part of the contract (docs/PROOF-FORMAT.md section 3) — a test that
   pins them is a test that stops someone quietly introducing a second naming scheme. *)

module Lit = Baguette_proof.Lit
module Opb = Baguette_proof.Opb

let failures = ref 0

let check name cond =
  if cond then Printf.printf "ok   %s\n" name
  else begin
    incr failures;
    Printf.printf "FAIL %s\n" name
  end

let test_lits () =
  check "lit: order-encoding name" (Lit.to_string (Lit.ge "x" 3) = "x_ge_3");
  check "lit: upper bound is a negated order literal"
    (Lit.to_string (Lit.le "x" 4) = "~x_ge_5");
  check "lit: negative values avoid '-'" (Lit.to_string (Lit.ge "x" (-2)) = "x_ge_m2");
  check "lit: direct encoding" (Lit.to_string (Lit.eq "x" 2) = "x_eq_2");
  check "lit: double negation"
    (Lit.to_string (Lit.negate (Lit.negate (Lit.ge "x" 3))) = "x_ge_3");
  check "lit: identifiers are sanitised for OPB"
    (Lit.to_string (Lit.ge "X_INTRODUCED_1_" 1) = "X_INTRODUCED_1__ge_1")

let test_opb () =
  let c = Opb.ge [ (1, Lit.ge "x" 1); (-2, Lit.le "y" 3) ] 1 in
  check "opb: renders a constraint"
    (Opb.constr_to_string c = "+1 x_ge_1 -2 ~y_ge_4 >= 1 ;")

let () =
  test_lits ();
  test_opb ();
  if !failures > 0 then begin
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1
  end
  else print_endline "\nproof unit tests passed"
