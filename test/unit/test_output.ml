(* Unit tests for the solution printer (SPEC 2.2) and for the independent solution
   checker that I-S1 names.

   Both halves are pure functions over a Model.t, so this file never builds a store, a
   propagator or a proof. That is the point of keeping them core-free: a printer bug and
   a checker bug are both findable without a working solver, and they stay findable while
   the solver is being rewritten underneath.

   The printer half is anchored twice. Hand-built models cover the shapes the shipped
   models happen not to contain (bools, negatives, array2d, empty arrays, an empty output
   list), and then four of the satisfiable models in test/models/ are parsed for real and
   printed, and the bytes compared with test/expected/*.out. Those files are I-M1 ground
   truth: if this test fails on them the printer is wrong, not the file.

   The checker half asserts one violation per constraint kind. Int_lin_ne and Int_ne have
   no propagator yet, and are tested here exactly because of that — the checker is the
   only thing in the tree that knows what they mean. *)

module F = Baguette_flatzinc
module M = F.Model
module O = F.Output

let failures = ref 0

let check name cond =
  if cond then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s\n" name)

(* String comparison reports both sides, with newlines made visible: almost every failure
   in this file is a difference of one character that is invisible when printed raw. *)
let show s = String.concat "\\n" (String.split_on_char '\n' s)

let check_str name ~expected ~actual =
  if String.equal expected actual then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s\n       expected: %S\n       actual:   %S\n" name
      (show expected) (show actual))

let check_raises_invalid name f =
  match f () with
  | exception Invalid_argument _ -> Printf.printf "ok   %s\n" name
  | exception e ->
      incr failures;
      Printf.printf "FAIL %s: raised %s, expected Invalid_argument\n" name
        (Printexc.to_string e)
  | _ ->
      incr failures;
      Printf.printf "FAIL %s: returned normally, expected Invalid_argument\n" name

(* ---------------------------------------------------------------- locating test data *)

(* Same search as test_flatzinc.ml: the test binary may be run from the source root, from
   a dune sandbox, or from a private --build-dir, so walk up from both the cwd and the
   executable looking for a file only the source tree has. *)
let rec find_up dir marker depth =
  if depth <= 0 then None
  else if Sys.file_exists (Filename.concat dir marker) then Some dir
  else
    let parent = Filename.dirname dir in
    if String.equal parent dir then None else find_up parent marker (depth - 1)

let root =
  let marker = Filename.concat "test" (Filename.concat "models" "trivial_sat.fzn") in
  match find_up (Sys.getcwd ()) marker 12 with
  | Some d -> Some d
  | None -> find_up (Filename.dirname Sys.executable_name) marker 12

let data_path sub name =
  match root with
  | Some d -> Filename.concat d (Filename.concat "test" (Filename.concat sub name))
  | None -> failwith "test data not found"

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

(* ---------------------------------------------------------------- model construction *)

let p = F.Pos.unknown
let v name dom = { M.v_name = name; M.v_dom = dom; M.v_pos = p }
let c k = { M.k; M.c_pos = p }

let model ?(vars = [||]) ?(constraints = []) ?(output = []) () =
  { M.vars; constraints; objective = M.Satisfy; search = []; output }

(* ====================================================================== the printer *)

let test_scalars () =
  let m =
    model
      ~vars:[| v "x" (M.Drange (0, 10)); v "b" M.Dbool; v "n" (M.Drange (-5, 5)) |]
      ~output:
        [
          M.Out_var ("x", M.Oint, M.Var 0);
          M.Out_var ("b", M.Obool, M.Var 1);
          M.Out_var ("n", M.Oint, M.Var 2);
        ]
      ()
  in
  check_str "scalars: int, bool true, negative"
    ~expected:"x = 7;\nb = true;\nn = -3;\n----------\n"
    ~actual:(O.solution m [| 7; 1; -3 |]);
  check_str "scalars: bool false" ~expected:"x = 0;\nb = false;\nn = 0;\n----------\n"
    ~actual:(O.solution m [| 0; 0; 0 |])

let test_const_item () =
  (* A `Const' output item is a parameter the builder folded to a literal. The value
     alone cannot say whether it was an int or a bool, which is exactly why the item
     carries its declared [out_ty]: under [Oint] the literal prints as a decimal, under
     [Obool] as false/true. M1-T21 — before it, every [Const] printed as a decimal and a
     bool parameter reached the user as `1'. *)
  let m =
    model
      ~output:
        [ M.Out_var ("k", M.Oint, M.Const 42); M.Out_var ("neg", M.Oint, M.Const (-1)) ]
      ()
  in
  check_str "const item, Oint: prints as an integer"
    ~expected:"k = 42;\nneg = -1;\n----------\n" ~actual:(O.solution m [||]);
  let b =
    model
      ~output:[ M.Out_var ("t", M.Obool, M.Const 1); M.Out_var ("f", M.Obool, M.Const 0) ]
      ()
  in
  check_str "const item, Obool: prints as false/true"
    ~expected:"t = true;\nf = false;\n----------\n" ~actual:(O.solution b [||]);
  (* A Boolean item holding something that is not 0 or 1 is a bug upstream (the builder
     rejects `var bool: b = 3;'), and I-S1 says it must not be laundered into a
     plausible-looking `true'. *)
  let bad = model ~output:[ M.Out_var ("bad", M.Obool, M.Const 3) ] () in
  check_raises_invalid "const item, Obool: a non-Boolean value raises" (fun () ->
      O.solution bad [||])

let test_arrays () =
  let m =
    model
      ~vars:
        [|
          v "a" (M.Drange (0, 9));
          v "b" (M.Drange (0, 9));
          v "c" (M.Drange (0, 9));
          v "d" (M.Drange (0, 9));
          v "f" M.Dbool;
        |]
      ~output:
        [
          M.Out_array ("x", [ (1, 3) ], M.Oint, [ M.Var 0; M.Var 1; M.Var 2 ]);
          M.Out_array
            ("y", [ (1, 2); (1, 2) ], M.Oint, [ M.Var 0; M.Var 1; M.Var 2; M.Var 3 ]);
          M.Out_array ("z", [ (1, 0) ], M.Oint, []);
          (* One array declaration has one base type, so an array's [out_ty] governs
             every element: a [Var] and a folded [Const] side by side print by the same
             rule. Both directions are covered — an int array mixing the two, and a bool
             array mixing them. Before M1-T21 the [Const 0] in `flags' printed as `0'. *)
          M.Out_array ("mixed", [ (0, 1) ], M.Oint, [ M.Var 3; M.Const 9 ]);
          M.Out_array ("flags", [ (0, 1) ], M.Obool, [ M.Var 4; M.Const 0 ]);
        ]
      ()
  in
  check_str "array1d / array2d / empty array / mixed operands / bool array"
    ~expected:
      "x = array1d(1..3, [1, 2, 3]);\n\
       y = array2d(1..2, 1..2, [1, 2, 3, 4]);\n\
       z = array1d(1..0, []);\n\
       mixed = array1d(0..1, [4, 9]);\n\
       flags = array1d(0..1, [true, false]);\n\
       ----------\n"
    ~actual:(O.solution m [| 1; 2; 3; 4; 1 |])

let test_empty_output () =
  let m = model ~vars:[| v "x" (M.Drange (0, 1)) |] () in
  check_str "empty output list is just the separator" ~expected:"----------\n"
    ~actual:(O.solution m [| 0 |])

let test_bad_index () =
  let m =
    model
      ~vars:[| v "x" (M.Drange (0, 1)) |]
      ~output:[ M.Out_var ("x", M.Oint, M.Var 3) ]
      ()
  in
  check_raises_invalid "out-of-range variable index raises Invalid_argument" (fun () ->
      O.solution m [| 0 |])

let test_markers () =
  check_str "unsatisfiable marker" ~expected:"=====UNSATISFIABLE=====\n"
    ~actual:O.unsatisfiable;
  check_str "exhausted marker" ~expected:"==========\n" ~actual:O.exhausted

(* -------------------------------------------- the shipped models, byte for byte (I-M1) *)

let test_expected_bytes () =
  let one name values =
    let m = F.Builder.of_file (data_path "models" (name ^ ".fzn")) in
    let expected = read_file (data_path "expected" (name ^ ".out")) in
    check_str
      (name ^ ".out reproduced byte for byte")
      ~expected ~actual:(O.solution m values);
    (* The values printed must actually be a solution, or the comparison above proves
       only that two wrong things agree. *)
    check (name ^ ": the printed assignment is a solution") (M.check_assignment m values)
  in
  one "trivial_sat" [| 1 |];
  one "lin_sat" [| 1; 0 |];
  one "ne_sat" [| 1; 2 |];
  (* M1-T21. `aliased' and the elements of `flags' are aliases, not variables, so this
     model declares exactly two: b and x. The interesting bytes are the ones no variable
     is behind. *)
  one "bool_out_sat" [| 0; 2 |]

(* ================================================================ check_assignment *)

(* A two-variable scaffold reused by the per-kind violation tests: both variables range
   over 0..10, so a violation can only come from the constraint under test. *)
let two_var k =
  model
    ~vars:[| v "x" (M.Drange (0, 10)); v "y" (M.Drange (0, 10)) |]
    ~constraints:[ c k ]
    ()

let test_satisfying () =
  let m =
    model
      ~vars:[| v "x" (M.Drange (0, 10)); v "y" (M.Drange (0, 10)); v "b" M.Dbool |]
      ~constraints:
        [
          c (M.Int_lin_le ([ (1, 0); (2, 1) ], 6));
          c (M.Int_lin_eq ([ (1, 0); (1, 1) ], 3));
          c (M.Int_lin_ne ([ (1, 0); (1, 1) ], 4));
          c (M.Int_le (M.Var 1, M.Var 0));
          c (M.Int_lt (M.Var 1, M.Var 0));
          c (M.Int_eq (M.Var 2, M.Const 1));
          c (M.Int_ne (M.Var 0, M.Var 1));
        ]
      ()
  in
  check "check_assignment: a satisfying assignment" (M.check_assignment m [| 2; 1; 1 |]);
  (* b = 0 breaks Int_eq (b, 1) and nothing else: every other constraint still holds at
     x = 2, y = 1, so a single false constraint is enough to reject the whole
     assignment. *)
  check "check_assignment: same model, one constraint broken"
    (not (M.check_assignment m [| 2; 1; 0 |]))

let test_each_kind () =
  (* One test per constraint kind: an assignment inside every declared domain that
     violates exactly that constraint, and one that satisfies it, so a checker that
     always returns false does not pass. *)
  let kind name k ~sat ~unsat =
    let m = two_var k in
    check (Printf.sprintf "check_assignment: %s holds" name) (M.check_assignment m sat);
    check
      (Printf.sprintf "check_assignment: %s violated" name)
      (not (M.check_assignment m unsat))
  in
  kind "int_lin_le"
    (M.Int_lin_le ([ (1, 0); (2, 1) ], 6))
    ~sat:[| 2; 2 |] ~unsat:[| 3; 2 |];
  kind "int_lin_eq"
    (M.Int_lin_eq ([ (1, 0); (1, 1) ], 5))
    ~sat:[| 2; 3 |] ~unsat:[| 2; 4 |];
  kind "int_lin_ne"
    (M.Int_lin_ne ([ (1, 0); (1, 1) ], 5))
    ~sat:[| 2; 4 |] ~unsat:[| 2; 3 |];
  kind "int_le" (M.Int_le (M.Var 0, M.Var 1)) ~sat:[| 3; 3 |] ~unsat:[| 4; 3 |];
  kind "int_lt" (M.Int_lt (M.Var 0, M.Var 1)) ~sat:[| 2; 3 |] ~unsat:[| 3; 3 |];
  kind "int_eq" (M.Int_eq (M.Var 0, M.Var 1)) ~sat:[| 3; 3 |] ~unsat:[| 3; 4 |];
  kind "int_ne" (M.Int_ne (M.Var 0, M.Var 1)) ~sat:[| 3; 4 |] ~unsat:[| 3; 3 |];
  (* Const operands are evaluated too, not skipped. *)
  let m =
    model
      ~vars:[| v "x" (M.Drange (0, 10)) |]
      ~constraints:[ c (M.Int_le (M.Var 0, M.Const 4)) ]
      ()
  in
  check "check_assignment: Const operand, holds" (M.check_assignment m [| 4 |]);
  check "check_assignment: Const operand, violated" (not (M.check_assignment m [| 5 |]))

let test_domains () =
  let range = model ~vars:[| v "x" (M.Drange (1, 3)) |] () in
  check "domain: inside a Drange" (M.check_assignment range [| 2 |]);
  check "domain: above a Drange" (not (M.check_assignment range [| 4 |]));
  check "domain: below a Drange" (not (M.check_assignment range [| 0 |]));
  let set = model ~vars:[| v "x" (M.Dset [ 1; 3; 7 ]) |] () in
  check "domain: inside a Dset" (M.check_assignment set [| 3 |]);
  check "domain: in the hole of a Dset" (not (M.check_assignment set [| 2 |]));
  let b = model ~vars:[| v "b" M.Dbool |] () in
  check "domain: Dbool 0" (M.check_assignment b [| 0 |]);
  check "domain: Dbool 1" (M.check_assignment b [| 1 |]);
  check "domain: Dbool 2 is not Boolean" (not (M.check_assignment b [| 2 |]));
  check "domain: Dbool -1 is not Boolean" (not (M.check_assignment b [| -1 |]));
  (* The domain check is not subsumed by the constraints: this model has none. *)
  check "domain violation alone is enough to reject"
    (not (M.check_assignment (model ~vars:[| v "x" (M.Drange (1, 1)) |] ()) [| 2 |]))

let test_wrong_length () =
  let m = model ~vars:[| v "x" (M.Drange (0, 1)); v "y" (M.Drange (0, 1)) |] () in
  check_raises_invalid "check_assignment: too few values" (fun () ->
      M.check_assignment m [| 0 |]);
  check_raises_invalid "check_assignment: too many values" (fun () ->
      M.check_assignment m [| 0; 0; 0 |]);
  check_raises_invalid "check_assignment: empty array for a two-variable model" (fun () ->
      M.check_assignment m [||])

(* ------------------------------------- 4b. I-S1's oracle is arithmetically independent

   M1-T33, from D-0029's consequence list. [Model.check_assignment] used to evaluate
   `sum a_i v_i` with the same wrapping `+`/`*` as the propagator and the .opb expansion
   it exists to check, so on the overflow class it agreed with the bug -- and agreed
   *because* it computed the same wrong product. It now evaluates exactly.

   Note what is NOT asserted here: that this changes any answer the solver gives.
   M1-T23's cap means no model the front end accepts can reach the wrapping case, so
   every model's output is byte-identical either way. These models are built by hand,
   bypassing [Compile] and therefore the cap, which is the only way to put the oracle in
   front of the arithmetic it used to get wrong. *)

let hand_model vars constraints =
  {
    M.vars =
      Array.of_list
        (List.map
           (fun (n, lo, hi) ->
             { M.v_name = n; M.v_dom = M.Drange (lo, hi); M.v_pos = F.Pos.unknown })
           vars);
    M.constraints = List.map (fun k -> { M.k; M.c_pos = F.Pos.unknown }) constraints;
    M.objective = M.Satisfy;
    M.search = [];
    M.output = [];
  }

let test_oracle_arithmetic () =
  (* D-0029's own reproduction, put to the oracle directly. -2^61 * 3 = -6.9e18, which
     is well below zero, so `int_lin_le([-2^61], [x], 0)` HOLDS at x = 3. Native 63-bit
     multiplication wraps that product to +2^61, a positive number, and answers
     "violated" -- the same wrong product the .opb row was folded from, which is why the
     old oracle could not see the bug D-0029 records. *)
  let big = -2305843009213693952 (* -2^61 *) in
  let m = hand_model [ ("x", 3, 4) ] [ M.Int_lin_le ([ (big, 0) ], 0) ] in
  check "I-S1 oracle: -2^61 * 3 <= 0 holds (native arithmetic says it does not)"
    (M.check_assignment m [| 3 |]);
  check "I-S1 oracle: the wrapped product would have answered the opposite" (big * 3 > 0);
  (* The converse direction, so the check above is not passing by answering "true" to
     everything: the same coefficient with the inequality the other way round. *)
  let m2 = hand_model [ ("x", 3, 4) ] [ M.Int_lin_le ([ (-big, 0) ], 0) ] in
  check "I-S1 oracle: 2^61 * 3 <= 0 does not hold" (not (M.check_assignment m2 [| 3 |]));
  (* Equality and disequality go through the same exact comparison. 2^61 * 3 is not
     representable, so no [rhs] a native evaluator could be handed makes this true;
     stated against the exact value's own sign instead. *)
  let m3 = hand_model [ ("x", 3, 4) ] [ M.Int_lin_eq ([ (big, 0) ], 0) ] in
  check "I-S1 oracle: -2^61 * 3 = 0 does not hold" (not (M.check_assignment m3 [| 3 |]));
  let m4 = hand_model [ ("x", 3, 4) ] [ M.Int_lin_ne ([ (big, 0) ], 0) ] in
  check "I-S1 oracle: -2^61 * 3 <> 0 holds" (M.check_assignment m4 [| 3 |]);
  (* A sum whose TERMS each fit and whose total does not: two copies of 2^62 - 1 sum to
     2^63 - 2, which wraps to -2. A native evaluator answers "<= 0"; the truth is not. *)
  let huge = 4611686018427387903 (* 2^62 - 1 *) in
  let m5 =
    hand_model [ ("x", 1, 1); ("y", 1, 1) ] [ M.Int_lin_le ([ (huge, 0); (huge, 1) ], 0) ]
  in
  check "I-S1 oracle: (2^62-1) + (2^62-1) <= 0 does not hold (the sum, not a product)"
    (not (M.check_assignment m5 [| 1; 1 |]));
  check "I-S1 oracle: that sum really does wrap negative natively" (huge + huge < 0);
  (* min_int as a coefficient: [of_int] must not negate it. A wrong [of_int] raises or
     silently returns zero here rather than answering. *)
  let m6 = hand_model [ ("x", 1, 1) ] [ M.Int_lin_le ([ (min_int, 0) ], -1) ] in
  check "I-S1 oracle: min_int as a coefficient is exact, not negated"
    (M.check_assignment m6 [| 1 |]);
  let m7 = hand_model [ ("x", 1, 1) ] [ M.Int_lin_eq ([ (min_int, 0) ], 0) ] in
  check "I-S1 oracle: min_int * 1 is not zero" (not (M.check_assignment m7 [| 1 |]));
  (* Multi-limb times multi-limb. Everything above has at least one single-limb
     operand, and that is not an accident of the values: a coefficient is what a model
     writes down, so reaching the case needs a *value* past 2^30 too. It was found by
     the break-it pass -- with [mul]'s inner carry deleted, every check above still
     passed, because the inner loop only ever ran once. 2^40 * 2^35 and 2^37 * 2^38 are
     both 2^75, which no native int holds; they must cancel exactly, leaving the third
     term, so the assertion pins the exact total rather than only its sign. *)
  let p1 = 1 lsl 40 and p2 = -(1 lsl 37) in
  let wide = [ ("x", 0, 1 lsl 40); ("y", 0, 1 lsl 40); ("z", 0, 9) ] in
  let terms = [ (p1, 0); (p2, 1); (1, 2) ] in
  let vals = [| 1 lsl 35; 1 lsl 38; 5 |] in
  check "I-S1 oracle: 2^40*2^35 - 2^37*2^38 + 5 = 5 exactly (multi-limb * multi-limb)"
    (M.check_assignment (hand_model wide [ M.Int_lin_eq (terms, 5) ]) vals);
  check "I-S1 oracle: ...and is not 4"
    (not (M.check_assignment (hand_model wide [ M.Int_lin_eq (terms, 4) ]) vals));
  check "I-S1 oracle: ...and orders correctly against both neighbours"
    (M.check_assignment (hand_model wide [ M.Int_lin_le (terms, 5) ]) vals
    && not (M.check_assignment (hand_model wide [ M.Int_lin_le (terms, 4) ]) vals));
  (* ...and still not enough, which the break-it pass said again, twice.

     First: 2^40 and 2^35 have *small* limbs (a single bit each), so no limb product
     comes near 2^30 and [mul]'s inner carry stays zero throughout.

     Second, and worth writing down because it is a trap: the obvious repair --
     multi-limb operands with full limbs, pinned by commutativity, A*B - B*A = 0 -- is
     provably blind to a lost inner carry. With the carry dropped, [mul] computes
     r[k] = (sum of x_i*y_j over i+j=k) mod 2^30, and that convolution is *symmetric* in
     x and y, so the broken A*B and the broken B*A are equal and cancel just as exactly
     as the right ones do. A test can be commutative and useless at the same time.

     What does see it is the same exact product reached by two different FACTORISATIONS,
     because the limbs of 3M are not three times the limbs of M -- [of_int] carries, and
     the broken multiply does not. 6*M and 2*(3M) are the same number; their broken
     limb convolutions are not. *)
  let m_big = 1234567890123456789 in
  let factor = [ ("p", 0, max_int); ("q", 0, max_int) ] in
  let two_ways = [ (6, 0); (-2, 1) ] in
  check "I-S1 oracle: 6*M - 2*(3M) = 0, the same product by two factorisations"
    (M.check_assignment
       (hand_model factor [ M.Int_lin_eq (two_ways, 0) ])
       [| m_big; 3 * m_big |]);
  check "I-S1 oracle: ...and 6*M - 2*(3M - 1) is not zero"
    (not
       (M.check_assignment
          (hand_model factor [ M.Int_lin_eq (two_ways, 0) ])
          [| m_big; (3 * m_big) - 1 |]));
  (* Carries and borrows in the ADDITION, across limbs and across sign: four terms of
     magnitude 2^62 - 1 that cancel in pairs. Each partial sum is past what a native
     int holds in both directions. *)
  let hugev = max_int in
  let four = [ ("a", 0, 1); ("b", 0, 1); ("c", 0, 1); ("d", 0, 1) ] in
  let cancel = [ (hugev, 0); (hugev, 1); (-hugev, 2); (-hugev, 3) ] in
  check "I-S1 oracle: max_int + max_int - max_int - max_int = 0, with carries"
    (M.check_assignment (hand_model four [ M.Int_lin_eq (cancel, 0) ]) [| 1; 1; 1; 1 |]);
  check "I-S1 oracle: the same four terms with one dropped are not zero"
    (not
       (M.check_assignment
          (hand_model four [ M.Int_lin_eq (List.tl cancel, 0) ])
          [| 1; 1; 1; 1 |]));
  (* Ordinary-sized arithmetic must be unchanged: this is an oracle, and a rewrite that
     moved a small answer would change what the solver prints. Cross-checked against the
     native evaluation on every small case, where the two must agree exactly. *)
  let agree = ref true in
  for a = -6 to 6 do
    for b = -6 to 6 do
      for v = -6 to 6 do
        for w = -6 to 6 do
          for rhs = -4 to 4 do
            let m =
              hand_model
                [ ("x", -6, 6); ("y", -6, 6) ]
                [ M.Int_lin_le ([ (a, 0); (b, 1) ], rhs) ]
            in
            if M.check_assignment m [| v; w |] <> ((a * v) + (b * w) <= rhs) then
              agree := false
          done
        done
      done
    done
  done;
  check "I-S1 oracle: agrees with native arithmetic on every small case (28561 of them)"
    !agree;
  (* The bound this module's header derives for [mul]'s inner product. If a later change
     raises [bits], this is what says so instead of a silent wrap in the oracle itself. *)
  (* Positive means it did not wrap computing itself; the headroom factor is what a
     later change to [bits] would eat. At bits = 30 the bound is ~2^60 and max_int is
     2^62 - 1, so there are two spare bits; at bits = 31 there would be none. *)
  check "I-S1 oracle: mul's widest intermediate does not wrap, with headroom to spare"
    (M.Exact.widest_mul_intermediate > 0 && max_int / M.Exact.widest_mul_intermediate >= 4)

(* ============================================================================== main *)

let () =
  test_scalars ();
  test_const_item ();
  test_arrays ();
  test_empty_output ();
  test_bad_index ();
  test_markers ();
  (match root with
  | None ->
      incr failures;
      print_endline
        "FAIL could not locate test/models/ and test/expected/ from the current \
         directory or the executable path; the byte-for-byte assertions did not run"
  | Some d ->
      Printf.printf "(test data from %s)\n" d;
      test_expected_bytes ());
  test_satisfying ();
  test_each_kind ();
  test_domains ();
  test_wrong_length ();
  test_oracle_arithmetic ();
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "\noutput unit tests passed"
