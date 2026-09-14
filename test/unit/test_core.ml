(* Unit tests for the solver core.

   These check the invariants in docs/INVARIANTS.md directly. When a new propagator
   lands, add it to the soundness check (I-P1) — brute force over small domains catches
   the class of bug that is otherwise only visible as a rejected proof, hours later. *)

module Domain = Baguette_core.Domain
module Store = Baguette_core.Store
module Var = Baguette_core.Var
module Explanation = Baguette_core.Explanation
module Lit = Baguette_proof.Lit

let failures = ref 0

let check name cond =
  if cond then Printf.printf "ok   %s\n" name
  else begin
    incr failures;
    Printf.printf "FAIL %s\n" name
  end

let check_raises name f =
  match f () with
  | exception _ -> Printf.printf "ok   %s\n" name
  | _ ->
      incr failures;
      Printf.printf "FAIL %s (expected an exception)\n" name

(* ------------------------------------------------------------------ domains *)

let test_domains () =
  let d = Domain.make 1 5 in
  check "domain: size of 1..5" (Domain.size d = 5);
  check "domain: membership" (Domain.mem d 3 && not (Domain.mem d 6));
  check "domain: not fixed" (not (Domain.is_fixed d));

  check_raises "domain: empty initial range rejected" (fun () -> Domain.make 5 1);

  (* I-D2: a hole punched at a bound must move the bound past it. *)
  (match Domain.remove d 1 with
  | Domain.Changed d' ->
      check "I-D2: removing lo moves lo" (Domain.lo d' = 2);
      check "I-D2: size drops by one" (Domain.size d' = 4)
  | _ -> check "I-D2: removing lo moves lo" false);

  (match Domain.remove d 3 with
  | Domain.Changed d' ->
      check "domain: interior hole keeps bounds"
        (Domain.lo d' = 1 && Domain.hi d' = 5 && Domain.size d' = 4);
      check "domain: interior hole is absent" (not (Domain.mem d' 3))
  | _ -> check "domain: interior hole" false);

  check "domain: no-op prune reports Unchanged"
    (match Domain.set_lo d 1 with Domain.Unchanged -> true | _ -> false);

  check "domain: contradictory bound fails"
    (match Domain.set_lo d 9 with Domain.Failed -> true | _ -> false);

  check "domain: fix outside domain fails"
    (match Domain.fix d 9 with Domain.Failed -> true | _ -> false);

  (* Removing every value must fail rather than produce an empty domain (I-D1). *)
  let shrink d v = match Domain.remove d v with Domain.Changed d' -> d' | _ -> d in
  let d2 = List.fold_left shrink (Domain.make 1 3) [ 1; 3 ] in
  check "I-D1: shrunk to a single value" (Domain.is_fixed d2 && Domain.lo d2 = 2);
  check "I-D1: removing the last value fails"
    (match Domain.remove d2 2 with Domain.Failed -> true | _ -> false)

(* -------------------------------------------------------------------- store *)

let sample_store () =
  Store.create
    ~names:[| "x"; "y"; "z" |]
    ~domains:[| Domain.make 0 10; Domain.make 0 10; Domain.make 0 10 |]

let test_store () =
  let s = sample_store () in
  let x = Var.of_int 0 and y = Var.of_int 1 in
  check "store: starts at level 0" (Store.level s = 0);

  let why = Explanation.trivial in
  check "store: prune applies"
    (match Store.set_lo s x 3 why with Store.Changed -> true | _ -> false);
  check "store: prune took effect" (Domain.lo (Store.get s x) = 3);
  check "store: redundant prune is a no-op"
    (match Store.set_lo s x 2 why with Store.Unchanged -> true | _ -> false);
  check "store: contradiction surfaces the explanation"
    (match Store.set_hi s x 1 why with Store.Conflict _ -> true | _ -> false);

  (* I-T1: backtracking restores exactly the state at the level mark. *)
  let before_lo = Domain.lo (Store.get s x) and before_hi = Domain.hi (Store.get s y) in
  Store.new_level s;
  check "I-T2: level opened" (Store.level s = 1);
  ignore (Store.set_lo s x 7 why);
  ignore (Store.set_hi s y 2 why);
  Store.new_level s;
  ignore (Store.fix s y 1 why);
  check "store: nested changes applied"
    (Domain.lo (Store.get s x) = 7 && Domain.is_fixed (Store.get s y));
  Store.backtrack_to s 0;
  check "I-T1: x restored" (Domain.lo (Store.get s x) = before_lo);
  check "I-T1: y restored" (Domain.hi (Store.get s y) = before_hi);
  check "I-S3: level restored" (Store.level s = 0);

  check_raises "store: backtracking past level 0 is an error" (fun () ->
      Store.backtrack s)

(* ------------------------------------------------------------- explanations *)

let test_explanations () =
  let l = Lit.ge "x" 3 in
  check "lit: order-encoding name" (Lit.to_string l = "x_ge_3");
  check "lit: upper bound is a negated order literal"
    (Lit.to_string (Lit.le "x" 4) = "~x_ge_5");
  check "lit: negative values avoid '-'" (Lit.to_string (Lit.ge "x" (-2)) = "x_ge_m2");
  check "lit: double negation" (Lit.to_string (Lit.negate (Lit.negate l)) = "x_ge_3");

  (* Deferred explanations must be computed at most once: forcing twice must not
     re-run the thunk. See docs/ARCHITECTURE.md section 4. *)
  let calls = ref 0 in
  let e =
    Explanation.deferred (fun () ->
        incr calls;
        Explanation.clause [ l ])
  in
  let _ = Explanation.force e in
  let _ = Explanation.force e in
  check "explanation: Deferred is memoised" (!calls = 1);
  check "explanation: forced value is the computed one"
    (match Explanation.force e with
    | Explanation.Clause [ l' ] -> Lit.to_string l' = "x_ge_3"
    | _ -> false);

  check "explanation: lits of a cut unions both sides"
    (List.length (Explanation.lits (Explanation.cut (Explanation.clause [ l ])
                                     (Explanation.clause [ Lit.ge "y" 1 ]) 1 1))
     = 2)

let () =
  test_domains ();
  test_store ();
  test_explanations ();
  if !failures > 0 then begin
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1
  end
  else print_endline "\ncore unit tests passed"
