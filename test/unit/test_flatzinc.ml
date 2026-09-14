(* Unit tests for the FlatZinc front end: lexing, parsing, model building.

   Two halves:

   1. the five real models in test/models/ are parsed and the resulting Model.t is
      asserted on in full — variables, domains, constraints, objective, output;
   2. rejection cases, each asserting that the diagnostic says the right thing *and*
      carries a line/column. SPEC 2.1 makes two of these normative: a `var int` with no
      declared domain must be rejected, and an unsupported builtin must be named in the
      error rather than silently skipped. *)

module F = Baguette_flatzinc
module M = F.Model

let failures = ref 0

let check name cond =
  if cond then Printf.printf "ok   %s\n" name
  else begin
    incr failures;
    Printf.printf "FAIL %s\n" name
  end

let check_str name ~expected ~actual =
  if String.equal expected actual then Printf.printf "ok   %s\n" name
  else begin
    incr failures;
    Printf.printf "FAIL %s\n       expected: %s\n       actual:   %s\n" name expected actual
  end

let contains ~needle haystack =
  let n = String.length needle and h = String.length haystack in
  if n = 0 then true
  else begin
    let found = ref false in
    for i = 0 to h - n do
      if (not !found) && String.equal (String.sub haystack i n) needle then found := true
    done;
    !found
  end

(* ------------------------------------------------------------------ locating models *)

let rec find_up dir marker depth =
  if depth <= 0 then None
  else if Sys.file_exists (Filename.concat dir marker) then Some dir
  else
    let parent = Filename.dirname dir in
    if String.equal parent dir then None else find_up parent marker (depth - 1)

let models_dir =
  let marker = Filename.concat "test" (Filename.concat "models" "trivial_sat.fzn") in
  let from_cwd = find_up (Sys.getcwd ()) marker 12 in
  let root =
    match from_cwd with
    | Some d -> Some d
    | None -> find_up (Filename.dirname Sys.executable_name) marker 12
  in
  match root with
  | Some d -> Some (Filename.concat d (Filename.concat "test" "models"))
  | None -> None

let model_path name =
  match models_dir with
  | Some d -> Filename.concat d (name ^ ".fzn")
  | None -> failwith "test/models not found"

(* ------------------------------------------------------------------------- helpers *)

let kinds (m : M.t) = List.map (fun (c : M.constr) -> c.M.k) m.M.constraints
let doms (m : M.t) = Array.to_list (Array.map (fun (v : M.var) -> v.M.v_dom) m.M.vars)
let names (m : M.t) = Array.to_list (Array.map (fun (v : M.var) -> v.M.v_name) m.M.vars)

let load name =
  try Ok (F.Builder.of_file (model_path name)) with
  | F.Error.Error e -> Error (F.Error.to_string e)
  | Failure msg -> Error msg

let with_model name f =
  match load name with
  | Ok m -> f m
  | Error msg ->
      incr failures;
      Printf.printf "FAIL %s: front end rejected the model: %s\n" name msg

(* A rejection case: [src] must fail, the message must mention every string in [needles],
   and the reported position must be on [line]. *)
let reject name ~src ~line ~needles =
  match F.Error.catch (fun () -> F.Builder.of_string ~file:"<test>" src) with
  | Ok _ ->
      incr failures;
      Printf.printf "FAIL %s: expected a rejection, the model was accepted\n" name
  | Error (e : F.Error.t) ->
      let msg = F.Error.to_string e in
      let missing = List.filter (fun s -> not (contains ~needle:s msg)) needles in
      if missing <> [] then begin
        incr failures;
        Printf.printf "FAIL %s: message does not mention %s\n       message: %s\n" name
          (String.concat ", " (List.map (Printf.sprintf "%S") missing))
          msg
      end
      else if e.F.Error.pos.F.Pos.line <> line then begin
        incr failures;
        Printf.printf "FAIL %s: expected the error on line %d, got line %d\n       message: %s\n"
          name line e.F.Error.pos.F.Pos.line msg
      end
      else if e.F.Error.pos.F.Pos.col <= 0 then begin
        incr failures;
        Printf.printf "FAIL %s: error carries no column\n       message: %s\n" name msg
      end
      else Printf.printf "ok   %s (%s)\n" name (F.Pos.to_string e.F.Error.pos)

(* ============================================================ the five shipped models *)

let test_trivial_sat () =
  with_model "trivial_sat" (fun m ->
      check "trivial_sat: one variable" (M.nvars m = 1);
      check "trivial_sat: names" (names m = [ "x" ]);
      check "trivial_sat: domain 1..3" (doms m = [ M.Drange (1, 3) ]);
      check "trivial_sat: int_le(x, 2)" (kinds m = [ M.Int_le (M.Var 0, M.Const 2) ]);
      check "trivial_sat: satisfy" (m.M.objective = M.Satisfy);
      check "trivial_sat: output x" (m.M.output = [ M.Out_var ("x", M.Var 0) ]);
      check "trivial_sat: no search annotation" (m.M.search = []))

let test_trivial_unsat () =
  with_model "trivial_unsat" (fun m ->
      check "trivial_unsat: one variable" (M.nvars m = 1);
      check "trivial_unsat: domain 1..3" (doms m = [ M.Drange (1, 3) ]);
      check "trivial_unsat: int_le(x, 0)" (kinds m = [ M.Int_le (M.Var 0, M.Const 0) ]))

let test_lin_sat () =
  with_model "lin_sat" (fun m ->
      (* `coeffs` is a parameter array: it must not become a solver variable. *)
      check "lin_sat: two variables" (M.nvars m = 2);
      check "lin_sat: names" (names m = [ "x"; "y" ]);
      check "lin_sat: domains 0..5" (doms m = [ M.Drange (0, 5); M.Drange (0, 5) ]);
      check "lin_sat: constraints"
        (kinds m
        = [ M.Int_lin_le ([ (1, 0); (2, 1) ], 6); M.Int_lt (M.Var 1, M.Var 0) ]);
      check "lin_sat: output x and y"
        (m.M.output = [ M.Out_var ("x", M.Var 0); M.Out_var ("y", M.Var 1) ]))

let test_lin_unsat () =
  with_model "lin_unsat" (fun m ->
      check "lin_unsat: two variables" (M.nvars m = 2);
      check "lin_unsat: negative coefficients survive"
        (kinds m
        = [
            M.Int_lin_le ([ (1, 0); (1, 1) ], 3);
            M.Int_lin_le ([ (-1, 0); (-1, 1) ], -8);
          ]))

let test_ne_sat () =
  with_model "ne_sat" (fun m ->
      check "ne_sat: two variables" (M.nvars m = 2);
      check "ne_sat: domains 1..2" (doms m = [ M.Drange (1, 2); M.Drange (1, 2) ]);
      check "ne_sat: constraints"
        (kinds m = [ M.Int_ne (M.Var 0, M.Var 1); M.Int_lt (M.Var 0, M.Var 1) ]))

(* ==================================================== the rest of the SPEC 2.1 subset *)

let kitchen_sink =
  "% a line comment\n\
   /* a block\n\
   comment */\n\
   predicate my_pred(var int: a, array [int] of var int: b);\n\
   int: n = 3;\n\
   bool: flag = true;\n\
   array [1..3] of int: w = [1, -2, n];\n\
   var bool: b1;\n\
   var {1, 3, 5}: s :: output_var;\n\
   array [1..2] of var 0..4: xs :: output_array([1..2]);\n\
   var 0..9: obj :: output_var;\n\
   constraint int_lin_eq(w, [xs[1], xs[2], obj], 4);\n\
   constraint int_ne(s, 3);\n\
   solve :: int_search([obj], first_fail, indomain_min, complete) minimize obj;\n"

let test_kitchen_sink () =
  match F.Error.catch (fun () -> F.Builder.of_string ~file:"<sink>" kitchen_sink) with
  | Error e ->
      incr failures;
      Printf.printf "FAIL kitchen sink: %s\n" (F.Error.to_string e)
  | Ok m ->
      check "sink: five variables (parameters are not variables)" (M.nvars m = 5);
      check "sink: array elements get indexed names"
        (names m = [ "b1"; "s"; "xs[1]"; "xs[2]"; "obj" ]);
      check "sink: var bool domain" (List.hd (doms m) = M.Dbool);
      check "sink: set domain" (List.nth (doms m) 1 = M.Dset [ 1; 3; 5 ]);
      check "sink: array element domains"
        (List.nth (doms m) 2 = M.Drange (0, 4) && List.nth (doms m) 3 = M.Drange (0, 4));
      check "sink: parameter array is substituted into the coefficients"
        (kinds m
        = [
            M.Int_lin_eq ([ (1, 2); (-2, 3); (3, 4) ], 4);
            M.Int_ne (M.Var 1, M.Const 3);
          ]);
      check "sink: minimize objective" (m.M.objective = M.Minimize (M.Var 4));
      check "sink: search annotation honoured"
        (m.M.search = [ M.Int_search ([ 4 ], M.First_fail, M.Indomain_min) ]);
      check "sink: output items in declaration order"
        (m.M.output
        = [
            M.Out_var ("s", M.Var 1);
            M.Out_array ("xs", [ (1, 2) ], [ M.Var 2; M.Var 3 ]);
            M.Out_var ("obj", M.Var 4);
          ])

let test_misc_accepts () =
  let ok name src =
    match F.Error.catch (fun () -> F.Builder.of_string ~file:"<t>" src) with
    | Ok _ -> Printf.printf "ok   %s\n" name
    | Error e ->
        incr failures;
        Printf.printf "FAIL %s: %s\n" name (F.Error.to_string e)
  in
  ok "accept: maximize" "var 0..3: x;\nsolve maximize x;\n";
  ok "accept: seq_search"
    "var 0..3: x;\n\
     var 0..3: y;\n\
     solve :: seq_search([int_search([x], input_order, indomain_max, complete), \
     int_search([y], first_fail, indomain_min, complete)]) satisfy;\n";
  ok "accept: constant folded out of a linear constraint"
    "var 0..3: x;\nconstraint int_lin_le([1, 1], [x, 2], 5);\nsolve satisfy;\n";
  ok "accept: unknown non-search annotations are ignored"
    "var 0..3: x :: var_is_introduced :: is_defined_var;\nsolve satisfy;\n";
  ok "accept: aliased variable" "var 0..3: x;\nvar 0..3: y = x;\nsolve satisfy;\n";
  ok "accept: array[int] parameter with access"
    "array [int] of int: a = [4, 5, 6];\n\
     var 0..9: x;\n\
     constraint int_le(x, a[3]);\n\
     solve satisfy;\n"

let test_constant_folding () =
  match
    F.Error.catch (fun () ->
        F.Builder.of_string ~file:"<t>"
          "var 0..3: x;\nconstraint int_lin_le([1, 1], [x, 2], 5);\nsolve satisfy;\n")
  with
  | Error e ->
      incr failures;
      Printf.printf "FAIL fold: %s\n" (F.Error.to_string e)
  | Ok m ->
      check "fold: constant moved to the right-hand side"
        (kinds m = [ M.Int_lin_le ([ (1, 0) ], 3) ])

(* ========================================================================= rejections *)

let test_rejections () =
  (* SPEC 2.1, normative: no defaulting to a machine-word range. *)
  reject "reject: var int with no domain" ~line:1
    ~src:"var int: x;\nsolve satisfy;\n"
    ~needles:
      [ "error"; "`x`"; "no domain"; "finite declared domain"; "<test>:1:1" ];
  reject "reject: var int with no domain inside an array" ~line:1
    ~src:"array [1..2] of var int: xs;\nsolve satisfy;\n"
    ~needles:[ "no domain" ];
  (* SPEC 2.1, normative: name the builtin, never skip it. *)
  reject "reject: unknown builtin" ~line:2
    ~src:"var 1..3: x;\nconstraint frobnicate(x, 1);\nsolve satisfy;\n"
    ~needles:[ "unknown builtin"; "`frobnicate`"; "int_lin_le" ];
  reject "reject: builtin from a later milestone" ~line:3
    ~src:
      "var 1..3: x;\n\
       var 1..3: y;\n\
       constraint all_different_int([x, y]);\n\
       solve satisfy;\n"
    ~needles:[ "unsupported builtin"; "`all_different_int`"; "M4" ];
  reject "reject: reified builtin from M3" ~line:3
    ~src:
      "var 1..3: x;\n\
       var bool: b;\n\
       constraint int_eq_reif(x, 2, b);\n\
       solve satisfy;\n"
    ~needles:[ "`int_eq_reif`"; "M3" ];
  reject "reject: missing semicolon" ~line:2 ~src:"var 1..3: x\nsolve satisfy;\n"
    ~needles:[ "expected"; "`;`" ];
  reject "reject: unexpected character" ~line:1 ~src:"var 1..3: x @ y;\nsolve satisfy;\n"
    ~needles:[ "unexpected character" ];
  reject "reject: missing solve item" ~line:2 ~src:"var 1..3: x;\n"
    ~needles:[ "no `solve` item" ];
  reject "reject: undeclared identifier" ~line:2
    ~src:"var 1..3: x;\nconstraint int_le(z, 1);\nsolve satisfy;\n"
    ~needles:[ "undeclared identifier"; "`z`" ];
  reject "reject: wrong arity" ~line:2
    ~src:"var 1..3: x;\nconstraint int_le(x, 1, 2);\nsolve satisfy;\n"
    ~needles:[ "`int_le`"; "expects 2 argument" ];
  reject "reject: mismatched linear arrays" ~line:3
    ~src:
      "var 1..3: x;\n\
       var 1..3: y;\n\
       constraint int_lin_le([1, 2, 3], [x, y], 4);\n\
       solve satisfy;\n"
    ~needles:[ "coefficient array"; "3"; "2" ];
  reject "reject: variable coefficient" ~line:3
    ~src:
      "var 1..3: x;\n\
       var 1..3: y;\n\
       constraint int_lin_le([x, 1], [x, y], 4);\n\
       solve satisfy;\n"
    ~needles:[ "coefficient"; "must be a constant" ];
  reject "reject: float literal" ~line:2
    ~src:"var 1..3: x;\nconstraint int_le(x, 1.5);\nsolve satisfy;\n"
    ~needles:[ "floating-point" ];
  reject "reject: set of int" ~line:1 ~src:"set of int: s = {1};\nsolve satisfy;\n"
    ~needles:[ "`set of int` is not supported" ];
  reject "reject: duplicate declaration" ~line:2
    ~src:"var 1..3: x;\nvar 1..3: x;\nsolve satisfy;\n"
    ~needles:[ "declared more than once" ];
  reject "reject: empty domain" ~line:1 ~src:"var 3..1: x;\nsolve satisfy;\n"
    ~needles:[ "empty domain" ];
  reject "reject: unsupported search strategy" ~line:2
    ~src:
      "var 1..3: x;\n\
       solve :: int_search([x], smallest, indomain_random, complete) satisfy;\n"
    ~needles:[ "unsupported variable-selection strategy"; "input_order" ];
  reject "reject: array initialiser length mismatch" ~line:1
    ~src:"array [1..3] of int: w = [1, 2];\nsolve satisfy;\n"
    ~needles:[ "`w`"; "initialiser" ];
  reject "reject: array index out of bounds" ~line:3
    ~src:
      "array [1..2] of int: w = [1, 2];\n\
       var 0..9: x;\n\
       constraint int_le(x, w[5]);\n\
       solve satisfy;\n"
    ~needles:[ "out of bounds"; "`w`" ];
  reject "reject: two solve items" ~line:3
    ~src:"var 1..3: x;\nsolve satisfy;\nsolve satisfy;\n"
    ~needles:[ "only one `solve` item" ]

(* ============================================================================== main *)

let () =
  (match models_dir with
  | None ->
      incr failures;
      print_endline
        "FAIL could not locate test/models/ from the current directory or the executable \
         path; the shipped-model assertions did not run"
  | Some d -> Printf.printf "(models from %s)\n" d);
  if models_dir <> None then begin
    test_trivial_sat ();
    test_trivial_unsat ();
    test_lin_sat ();
    test_lin_unsat ();
    test_ne_sat ()
  end;
  test_kitchen_sink ();
  test_misc_accepts ();
  test_constant_folding ();
  test_rejections ();
  check_str "error rendering carries file:line:col" ~expected:"<t>:2:12: error: boom"
    ~actual:
      (F.Error.to_string { F.Error.pos = F.Pos.make "<t>" 2 12; msg = "boom" });
  if !failures > 0 then begin
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1
  end
  else print_endline "\nflatzinc unit tests passed"
