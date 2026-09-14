(* Unit tests for the solution printer (SPEC 2.2) and for the independent solution
   checker that I-S1 names.

   Both halves are pure functions over a Model.t, so this file never builds a store, a
   propagator or a proof. That is the point of keeping them core-free: a printer bug and
   a checker bug are both findable without a working solver, and they stay findable while
   the solver is being rewritten underneath.

   The printer half is anchored twice. Hand-built models cover the shapes the shipped
   models happen not to contain (bools, negatives, array2d, empty arrays, an empty output
   list), and then the three satisfiable models in test/models/ are parsed for real and
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
        [ M.Out_var ("x", M.Var 0); M.Out_var ("b", M.Var 1); M.Out_var ("n", M.Var 2) ]
      ()
  in
  check_str "scalars: int, bool true, negative"
    ~expected:"x = 7;\nb = true;\nn = -3;\n----------\n"
    ~actual:(O.solution m [| 7; 1; -3 |]);
  check_str "scalars: bool false" ~expected:"x = 0;\nb = false;\nn = 0;\n----------\n"
    ~actual:(O.solution m [| 0; 0; 0 |])

let test_const_item () =
  (* A `Const' output item is a parameter the builder folded to a literal. Its FlatZinc
     type is gone by then, so it prints as an integer even if it was a bool — see the
     comment in output.ml. *)
  let m =
    model ~output:[ M.Out_var ("k", M.Const 42); M.Out_var ("neg", M.Const (-1)) ] ()
  in
  check_str "const item prints as an integer" ~expected:"k = 42;\nneg = -1;\n----------\n"
    ~actual:(O.solution m [||])

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
          M.Out_array ("x", [ (1, 3) ], [ M.Var 0; M.Var 1; M.Var 2 ]);
          M.Out_array ("y", [ (1, 2); (1, 2) ], [ M.Var 0; M.Var 1; M.Var 2; M.Var 3 ]);
          M.Out_array ("z", [ (1, 0) ], []);
          M.Out_array ("mixed", [ (0, 1) ], [ M.Var 4; M.Const 9 ]);
        ]
      ()
  in
  check_str "array1d / array2d / empty array / mixed operands"
    ~expected:
      "x = array1d(1..3, [1, 2, 3]);\n\
       y = array2d(1..2, 1..2, [1, 2, 3, 4]);\n\
       z = array1d(1..0, []);\n\
       mixed = array1d(0..1, [true, 9]);\n\
       ----------\n"
    ~actual:(O.solution m [| 1; 2; 3; 4; 1 |])

let test_empty_output () =
  let m = model ~vars:[| v "x" (M.Drange (0, 1)) |] () in
  check_str "empty output list is just the separator" ~expected:"----------\n"
    ~actual:(O.solution m [| 0 |])

let test_bad_index () =
  let m =
    model ~vars:[| v "x" (M.Drange (0, 1)) |] ~output:[ M.Out_var ("x", M.Var 3) ] ()
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
  one "ne_sat" [| 1; 2 |]

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
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "\noutput unit tests passed"
