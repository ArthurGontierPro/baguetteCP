(* Unit tests for the FlatZinc front end: lexing, parsing, model building.

   Two halves:

   1. the five real models in test/models/ are parsed and the resulting Model.t is
      asserted on in full — variables, domains, constraints, objective, output;
   2. rejection cases, each asserting that the diagnostic says the right thing *and*
      carries a line/column. SPEC 2.1 makes two of these normative: a `var int` with no
      declared domain must be rejected, and an unsupported builtin must be named in the
      error rather than silently skipped. *)

module F = Baguette_flatzinc

(* M1-T53: the inner heap guard. test_prop.exe is the binary that reached 14.9 GB RSS on
   2026-09-16 and had to be killed by hand, so a guard that covered only test_output and
   test_compile would have missed the one incident it exists to prevent. `ulimit -v` stays
   the outer backstop -- see mem_guard.ml's header for what this cannot see. *)
let () = Mem_guard.install ()

module M = F.Model

let failures = ref 0

let check name cond =
  if cond then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s\n" name)

let check_str name ~expected ~actual =
  if String.equal expected actual then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s\n       expected: %s\n       actual:   %s\n" name expected
      actual)

let contains ~needle haystack =
  let n = String.length needle and h = String.length haystack in
  if n = 0 then true
  else
    let found = ref false in
    for i = 0 to h - n do
      if (not !found) && String.equal (String.sub haystack i n) needle then found := true
    done;
    !found

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
      if missing <> [] then (
        incr failures;
        Printf.printf "FAIL %s: message does not mention %s\n       message: %s\n" name
          (String.concat ", " (List.map (Printf.sprintf "%S") missing))
          msg)
      else if e.F.Error.pos.F.Pos.line <> line then (
        incr failures;
        Printf.printf
          "FAIL %s: expected the error on line %d, got line %d\n       message: %s\n" name
          line e.F.Error.pos.F.Pos.line msg)
      else if e.F.Error.pos.F.Pos.col <= 0 then (
        incr failures;
        Printf.printf "FAIL %s: error carries no column\n       message: %s\n" name msg)
      else Printf.printf "ok   %s (%s)\n" name (F.Pos.to_string e.F.Error.pos)

(* ============================================================ the five shipped models *)

let test_trivial_sat () =
  with_model "trivial_sat" (fun m ->
      check "trivial_sat: one variable" (M.nvars m = 1);
      check "trivial_sat: names" (names m = [ "x" ]);
      check "trivial_sat: domain 1..3" (doms m = [ M.Drange (1, 3) ]);
      check "trivial_sat: int_le(x, 2)" (kinds m = [ M.Int_le (M.Var 0, M.Const 2) ]);
      check "trivial_sat: satisfy" (m.M.objective = M.Satisfy);
      check "trivial_sat: output x" (m.M.output = [ M.Out_var ("x", M.Oint, M.Var 0) ]);
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
        (kinds m = [ M.Int_lin_le ([ (1, 0); (2, 1) ], 6); M.Int_lt (M.Var 1, M.Var 0) ]);
      check "lin_sat: output x and y"
        (m.M.output
        = [ M.Out_var ("x", M.Oint, M.Var 0); M.Out_var ("y", M.Oint, M.Var 1) ]))

let test_lin_unsat () =
  with_model "lin_unsat" (fun m ->
      check "lin_unsat: two variables" (M.nvars m = 2);
      check "lin_unsat: negative coefficients survive"
        (kinds m
        = [
            M.Int_lin_le ([ (1, 0); (1, 1) ], 3); M.Int_lin_le ([ (-1, 0); (-1, 1) ], -8);
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
        = [ M.Int_lin_eq ([ (1, 2); (-2, 3); (3, 4) ], 4); M.Int_ne (M.Var 1, M.Const 3) ]
        );
      check "sink: minimize objective" (m.M.objective = M.Minimize (M.Var 4));
      check "sink: search annotation honoured"
        (m.M.search = [ M.Int_search ([ 4 ], M.First_fail, M.Indomain_min) ]);
      check "sink: output items in declaration order"
        (m.M.output
        = [
            M.Out_var ("s", M.Oint, M.Var 1);
            M.Out_array ("xs", [ (1, 2) ], M.Oint, [ M.Var 2; M.Var 3 ]);
            M.Out_var ("obj", M.Oint, M.Var 4);
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
  reject "reject: var int with no domain" ~line:1 ~src:"var int: x;\nsolve satisfy;\n"
    ~needles:[ "error"; "`x`"; "no domain"; "finite declared domain"; "<test>:1:1" ];
  reject "reject: var int with no domain inside an array" ~line:1
    ~src:"array [1..2] of var int: xs;\nsolve satisfy;\n" ~needles:[ "no domain" ];
  (* SPEC 2.1, normative: name the builtin, never skip it. *)
  reject "reject: unknown builtin" ~line:2
    ~src:"var 1..3: x;\nconstraint frobnicate(x, 1);\nsolve satisfy;\n"
    ~needles:[ "unknown builtin"; "`frobnicate`"; "int_lin_le" ];
  (* M4-T1: `all_different_int` was this lane's example until its propagator landed,
     which is builder.ml's own rule working -- a builtin moves from [planned] to
     [implemented] in the same commit as its propagator, and its lane moves with it.
     What `all_different_int` owes the front end now is arity.

     M4-T3 took the LAST entry out of [planned], so there is no longer a builtin in
     SPEC 2.1 that the front end refuses as "not yet" and no lane can assert that
     wording. [unsupported_builtin]'s [Some] arm is therefore unreachable from any model
     -- deliberately kept, because the next row to widen the subset needs it -- and the
     "unknown builtin" lane above is what still exercises the function. *)
  reject "reject: all_different_int with the wrong arity" ~line:3
    ~src:
      "var 1..3: x;\n\
       var 1..3: y;\n\
       constraint all_different_int([x, y], 2);\n\
       solve satisfy;\n"
    ~needles:[ "`all_different_int`"; "expects 1 argument" ];
  (* `int_eq_reif` was this file's "builtin from a later milestone" lane until M3-T2
     implemented it. lib/flatzinc/builder.ml's header sets the rule -- a builtin moves
     from [planned] to [implemented] in the same commit as its propagator -- and this
     lane moves with it, from "not yet" to arity, which is what the front end still
     owes a reified builtin. The "later milestone" wording is now covered by the
     `array_int_element` lane below; [test_compile.ml]'s [test_reified] is where the
     four M3 builtins are checked to compile. *)
  reject "reject: a reified builtin with the wrong arity" ~line:3
    ~src:"var 1..3: x;\nvar bool: b;\nconstraint int_eq_reif(x, 2);\nsolve satisfy;\n"
    ~needles:[ "`int_eq_reif`"; "expects 3 argument" ];
  (* M4-T4b. `int_abs`, `int_times` and `int_div` moved from [planned] to
     [implemented], so what the front end still owes them is arity -- the same move
     the `int_eq_reif` lane above records for M3. `array_int_element` is still the
     "later milestone" case and its own lane below covers the wording. *)
  reject "reject: int_times with the wrong arity" ~line:2
    ~src:"var 1..3: x;\nconstraint int_times(x, 2);\nsolve satisfy;\n"
    ~needles:[ "`int_times`"; "expects 3 argument" ];
  reject "reject: int_abs with the wrong arity" ~line:2
    ~src:"var 1..3: x;\nconstraint int_abs(x);\nsolve satisfy;\n"
    ~needles:[ "`int_abs`"; "expects 2 argument" ];
  (* M4-T3. This lane was `array_int_element`'s "later milestone" case until its
     propagator landed; it moves to arity like every other one before it. The second
     lane is the one that is NOT just arity: SPEC 2.1 admits only a CONSTANT array, and
     lib/flatzinc/builder.ml refuses a variable element through [as_const] -- here,
     where the message can carry a source position and name the builtin, rather than
     several layers down in compile.ml. *)
  reject "reject: array_int_element with the wrong arity" ~line:2
    ~src:"var 1..3: x;\nconstraint array_int_element(x, [1, 2, 3]);\nsolve satisfy;\n"
    ~needles:[ "`array_int_element`"; "expects 3 argument" ];
  reject "reject: array_int_element over a VARIABLE array" ~line:3
    ~src:
      "var 1..3: x;\n\
       var 1..3: y;\n\
       constraint array_int_element(x, [1, y, 3], x);\n\
       solve satisfy;\n"
    ~needles:[ "`array_int_element`"; "every element of the array"; "constant" ];
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
  (* M7-T9 shipped `smallest`; the example moved to `anti_first_fail`, which is still
     unsupported. Same assertion, same strength -- see test_search_strategies below. *)
  reject "reject: unsupported search strategy" ~line:2
    ~src:
      "var 1..3: x;\n\
       solve :: int_search([x], anti_first_fail, indomain_random, complete) satisfy;\n"
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

(* ==================================================== the width cap (M1-T54, D-0028)

   Why these live in test_flatzinc.exe rather than test_compile.exe or test_proof.exe:
   the cap is two halves in two libraries -- the constant and the raise in
   [Baguette_proof.Encoding], the positioned diagnostic in [Baguette_flatzinc.Compile]
   -- and the thing worth testing is that they agree. This binary links both libraries,
   and the file-ownership protocol in CLAUDE.md put this file, not the other two, in the
   hands of the session that wrote the cap. If the cap ever moves, so should these.

   What is NOT here, deliberately. There is no model file in test/models/ for either
   side of the boundary. The reject side cannot be one: scripts/run_model_tests.sh
   requires exit 0, empty stderr and a matching .out, and a refused model is exit 3 with
   a diagnostic. The accept side must not be one: a model declared at the cap would
   emit a 1.3 MB .opb, which is the artefact the cap exists to prevent, and "no test may
   declare a wide domain" is a house rule with three memory-ceiling incidents behind it.
   The accept side of the pair below therefore stops at compilation: nothing solves, and
   nothing writes a proof. The "under the cap it still solves and the proof still
   verifies" half is carried by test/models/width_root_unsat.fzn at w = 999, which is
   deliberate and measured, runs in the model suite with veripb over its proof, and is
   a factor of ten below the cap. *)

module E = Baguette_proof.Encoding

let cap = E.max_order_width

(* A Compile-level rejection: [src] parses, and then [Compile.compile] must refuse it,
   naming every needle and reporting a position on [line]. Distinct from [reject]
   above, which only runs the builder. *)
let reject_compile name ~src ~line ~needles =
  let built = F.Error.catch (fun () -> F.Builder.of_string ~file:"<test>" src) in
  match built with
  | Error (e : F.Error.t) ->
      incr failures;
      Printf.printf "FAIL %s: the model did not even parse: %s\n" name
        (F.Error.to_string e)
  | Ok m -> (
      match F.Error.catch (fun () -> F.Compile.compile m) with
      | Ok _ ->
          incr failures;
          Printf.printf "FAIL %s: expected a rejection, compile accepted the model\n" name
      | Error (e : F.Error.t) ->
          let msg = F.Error.to_string e in
          let missing = List.filter (fun s -> not (contains ~needle:s msg)) needles in
          if missing <> [] then (
            incr failures;
            Printf.printf "FAIL %s: message does not mention %s\n       message: %s\n"
              name
              (String.concat ", " (List.map (Printf.sprintf "%S") missing))
              msg)
          else if e.F.Error.pos.F.Pos.line <> line then (
            incr failures;
            Printf.printf
              "FAIL %s: expected the error on line %d, got line %d\n       message: %s\n"
              name line e.F.Error.pos.F.Pos.line msg)
          else if e.F.Error.pos.F.Pos.col <= 0 then (
            incr failures;
            Printf.printf "FAIL %s: error carries no column\n       message: %s\n" name
              msg)
          else Printf.printf "ok   %s (%s)\n" name (F.Pos.to_string e.F.Error.pos))

let accepts_compile name ~src =
  let built = F.Error.catch (fun () -> F.Builder.of_string ~file:"<test>" src) in
  match built with
  | Error (e : F.Error.t) ->
      incr failures;
      Printf.printf "FAIL %s: the model did not parse: %s\n" name (F.Error.to_string e)
  | Ok m -> (
      match F.Error.catch (fun () -> F.Compile.compile m) with
      | Ok _ -> Printf.printf "ok   %s\n" name
      | Error (e : F.Error.t) ->
          incr failures;
          Printf.printf "FAIL %s: compile refused a model it should accept: %s\n" name
            (F.Error.to_string e))

let raises_width_too_large f =
  match f () with
  | _ -> `Accepted
  | exception E.Width_too_large (x, lo, hi) -> `Refused (x, lo, hi)
  | exception e -> `Other (Printexc.to_string e)

(* [order_width_exceeds] is a pure predicate over a pair of bounds: it declares no
   variable, builds no ladder and allocates nothing whatever the pair is. The
   declared-width lint (scripts/check_test_widths.py) matches on the ~lo:/~hi: labels
   wherever they appear and cannot tell a predicate from a declaration, so every call
   below goes through this positional wrapper. That keeps the lint aimed at the two
   real declarations in this file rather than at thirteen predicate calls -- the point
   of a lint nobody has learned to wave through. *)
let width_over lo hi = E.order_width_exceeds ~lo ~hi

(* ------------------------------------------------------------------ M7-T1
   The cap became an OPTION, so this block became a pair: an INVERSION and a CONTROL.

   Until M7-T1 the width cap was a refusal in the default build, and everything below
   asserted it. The refusal came from the 15 GB laptop baguette was written on, the
   corpus now runs on a 2 TB node, and D-0028's real cost -- proof size and checker
   time -- is not repealed by either machine. So [max_order_width] stops being a
   THRESHOLD and becomes a SUGGESTED LIMIT: the same 10 000, reachable on request.

   Both halves are kept, deliberately:

     INVERSION  with the default (no limit) the declaration that used to be refused is
                now ACCEPTED, and builds its whole ladder. This is the change.
     CONTROL    with [order_width_limit := Some cap] every assertion the old build made
                still holds, unchanged, word for word. This is what proves the option
                RESTORES the old behaviour rather than approximating it.

   Deleting either half would leave a reader unable to tell which one moved. *)

let with_width_limit lim f =
  let saved = !E.order_width_limit in
  E.order_width_limit := lim;
  Fun.protect ~finally:(fun () -> E.order_width_limit := saved) f

(* The only two [declare_int] calls in this file, and the only two lines in the tree
   that ask for a wide ladder on purpose. Both are marked for the width lint, because
   the width is not incidental here: it IS the subject. Measured cost of the pair, with
   /usr/bin/time -v over the whole binary: 13 MB peak RSS, 0.05 s wall. The accepted one
   builds [cap - 1] = 9 999 clause records in memory; nothing writes an .opb, nothing
   propagates and nothing emits a proof, which is the line this file does not cross --
   a model at the cap emits a 407 kB .opb, and that artefact is what the cap exists to
   keep out of the suite. *)
let ladder_at_cap () =
  let e = E.create () in
  E.declare_int e "x" ~lo:0 ~hi:cap (* width-ok: M1-T54, the cap is the subject *);
  (e, E.n_constraints e)

let declare_one_over e =
  E.declare_int e "wide" ~lo:0 ~hi:(cap + 1) (* width-ok: M1-T54 refusal *);
  (* Reached only if the cap wrongly accepted, which [raises_width_too_large] reports
     as `Accepted`. The clause count is returned so that failure says how far the
     ladder got before anyone noticed. *)
  E.n_constraints e

(* ------------------------------------------------------------ the INVERSION *)
(* The default build. No limit is set, and the declaration that M1-T54 refused is
   encoded. The clause count is the half that matters: it shows the ladder was really
   built, rather than the refusal having been replaced by some quieter decline. *)
let test_width_cap_default () =
  with_width_limit None (fun () ->
      check "M7-T1: the default build sets no width limit"
        (E.current_order_width_limit () = None);
      check_str "M7-T1: and says so" ~expected:"unlimited"
        ~actual:(E.order_width_limit_string ());
      (match raises_width_too_large (fun () -> declare_one_over (E.create ())) with
      | `Accepted ->
          Printf.printf
            "ok   M7-T1: width %d, one over the OLD cap, is now encoded not refused\n"
            (cap + 1)
      | `Refused (x, lo, hi) ->
          incr failures;
          Printf.printf
            "FAIL M7-T1: the default build still refuses %s over %d..%d on width\n" x lo
            hi
      | `Other s ->
          incr failures;
          Printf.printf "FAIL M7-T1: declaring one over the old cap raised %s\n" s);
      let over = declare_one_over (E.create ()) in
      check_str "M7-T1: and builds its whole ladder" ~expected:(string_of_int cap)
        ~actual:(string_of_int over);
      (* The predicate agrees with the door. *)
      check "M7-T1: order_width_exceeds is false one over the old cap"
        (not (width_over 0 (cap + 1)));
      check "M7-T1: and false for a width the old cap refused by three orders"
        (not (width_over 0 10_000_000));
      (* THE ONE REFUSAL THAT IS NOT AN OPTION. A width that is not representable as a
         native int has no ladder to build and no count to report; [declare_int] would
         sit in a 2^64 loop. That is an ARITHMETIC refusal, in the family of
         [Unrepresentable], and no flag turns it off. A future session reading "M7-T1
         removed the width limits" will try to remove this one too. *)
      check "M7-T1: min_int..max_int is STILL refused with no limit set -- the width is"
        (width_over min_int max_int);
      check "M7-T1: not representable, which is arithmetic, not a budget"
        (width_over min_int (min_int + cap + 1) = false);
      match
        raises_width_too_large (fun () ->
            let e = E.create () in
            (* An unrepresentable width IS the subject here, and it allocates
               nothing: declare_int refuses before the ladder. The marker below is
               for scripts/check_test_widths.py, which reads one line at a time. *)
            E.declare_int e "huge" ~lo:min_int ~hi:max_int (* width-ok: M7-T1 *);
            E.n_constraints e)
      with
      | `Refused ("huge", _, _) ->
          Printf.printf
            "ok   M7-T1: declare_int refuses an unrepresentable width with no limit set\n"
      | `Refused (x, _, _) ->
          incr failures;
          Printf.printf "FAIL M7-T1: refused, but named %s\n" x
      | `Accepted ->
          incr failures;
          Printf.printf "FAIL M7-T1: declare_int ACCEPTED min_int..max_int\n"
      | `Other s ->
          incr failures;
          Printf.printf "FAIL M7-T1: min_int..max_int raised %s, not Width_too_large\n" s)

(* M7-T1: the warning that replaced the refusal. The default build must not be silent
   about an expensive encoding -- a silent success is as wrong as a silent failure -- so
   this captures the sink and asserts the text a reader actually sees. *)
let test_width_warning () =
  with_width_limit None (fun () ->
      let buf = Buffer.create 512 in
      let saved_sink = !E.warn_sink in
      let saved_warn = !E.width_warn_threshold in
      E.set_warn_sink (Buffer.add_string buf);
      E.width_warn_threshold := Some cap;
      (let e = E.create () in
       E.declare_int e "wide" ~lo:0 ~hi:(cap + 1) (* width-ok: M7-T1, the subject *));
      let msg = Buffer.contents buf in
      E.set_warn_sink saved_sink;
      E.width_warn_threshold := saved_warn;
      check "M7-T1: an over-wide declaration warns" (msg <> "");
      List.iter
        (fun needle ->
          check
            (Printf.sprintf "M7-T1: the warning says %S" needle)
            (contains ~needle msg))
        [
          "warning";
          "`wide`";
          Printf.sprintf "a width of %d" (cap + 1);
          "one Boolean per value";
          "Baguette will encode it";
          "too large to store";
          "--max-order-width";
          "--width-warn=none";
        ];
      (* Silenceable, and silencing it is the only thing that changes. *)
      let buf2 = Buffer.create 16 in
      E.set_warn_sink (Buffer.add_string buf2);
      E.width_warn_threshold := None;
      (let e = E.create () in
       E.declare_int e "wide" ~lo:0 ~hi:(cap + 1) (* width-ok: M7-T1, the subject *));
      E.set_warn_sink saved_sink;
      E.width_warn_threshold := saved_warn;
      check "M7-T1: --width-warn=none silences it" (Buffer.contents buf2 = "");
      (* And under the threshold nothing is said at all. *)
      let buf3 = Buffer.create 16 in
      E.set_warn_sink (Buffer.add_string buf3);
      (let e = E.create () in
       E.declare_int e "narrow" ~lo:0 ~hi:9);
      E.set_warn_sink saved_sink;
      check "M7-T1: a narrow declaration says nothing" (Buffer.contents buf3 = ""))

(* -------------------------------------------------------------- the CONTROL *)
(* Every assertion the pre-M7 build made, unchanged, under an explicit limit. If this
   passes, --max-order-width=10000 is the old build and not an approximation of it. *)
let test_width_cap_boundary () =
  (* ------------------------------------------------------------------ the constant *)
  (* width_root_unsat.fzn is at w = 999 and is load-bearing: a cap that refuses it
     breaks the model suite. Assert the headroom rather than trusting it. *)
  check "width cap: leaves room for width_root_unsat's w = 999" (cap >= 999);
  check "width cap: at least a factor of 10 above w = 999" (cap >= 9990);
  check_str "width cap: the constant is 10 000" ~expected:"10000"
    ~actual:(string_of_int cap);

  (* ----------------------------------------- the boundary, at Encoding's own door *)
  (* Exactly at the cap: accepted, and the ladder is the full [cap - 1] clauses. The
     clause count is the half that matters -- it shows the declaration really built the
     encoding, rather than being declined by something upstream of the ladder. *)
  (match raises_width_too_large ladder_at_cap with
  | `Accepted -> ()
  | `Refused _ ->
      incr failures;
      Printf.printf "FAIL width cap: Encoding refused width %d, which is AT the cap\n" cap
  | `Other s ->
      incr failures;
      Printf.printf "FAIL width cap: declaring at the cap raised %s\n" s);
  let _, at_cap = ladder_at_cap () in
  check_str "width cap: a domain AT the cap builds its whole ladder"
    ~expected:(string_of_int (cap - 1))
    ~actual:(string_of_int at_cap);

  (* One unit over: refused, and refused by name. *)
  (match raises_width_too_large (fun () -> declare_one_over (E.create ())) with
  | `Refused ("wide", 0, hi) when hi = cap + 1 ->
      Printf.printf "ok   width cap: width %d is refused by Encoding.declare_int\n"
        (cap + 1)
  | `Refused (x, lo, hi) ->
      incr failures;
      Printf.printf "FAIL width cap: refused, but reported %s over %d..%d\n" x lo hi
  | `Accepted ->
      incr failures;
      Printf.printf "FAIL width cap: Encoding ACCEPTED width %d, one over the cap\n"
        (cap + 1)
  | `Other s ->
      incr failures;
      Printf.printf "FAIL width cap: width %d raised %s, not Width_too_large\n" (cap + 1)
        s);

  (* A refused declaration must leave no trace: the variable is not declared, and no
     constraint id was minted. Otherwise a caller that catches the exception carries on
     against a half-built encoding, and the ids in the .opb no longer match the proof
     (I-X5). *)
  let e_trace = E.create () in
  (try ignore (declare_one_over e_trace) with E.Width_too_large _ -> ());
  check "width cap: a refused declaration declares nothing"
    (not (E.is_declared e_trace "wide"));
  check_str "width cap: a refused declaration mints no constraint id" ~expected:"0"
    ~actual:(string_of_int (E.n_constraints e_trace));

  (* The mixed-sign branch of [order_width_exceeds], where hi - lo is the width but
     neither bound is. -5000..5000 is exactly the cap; one more either way is not. *)
  check "width cap: -5000..5000 (width 10 000) is inside the cap"
    (not (width_over (-5000) 5000));
  check "width cap: -5001..5000 (width 10 001) is outside it" (width_over (-5001) 5000);
  check "width cap: -5000..5001 (width 10 001) is outside it" (width_over (-5000) 5001);
  (* A width that is not itself representable. min_int..max_int has width 2^64 - 1, and
     a cap that computed [hi - lo] would get -1 here and accept it -- which is the
     failure mode this codebase keeps finding: a check that cannot see its own subject
     fail. Also the genuinely degenerate widths, which must stay accepted. *)
  check "width cap: min_int..max_int is refused, not wrapped to width -1"
    (width_over min_int max_int);
  check "width cap: min_int..(min_int + cap) is inside the cap"
    (not (width_over min_int (min_int + cap)));
  check "width cap: min_int..(min_int + cap + 1) is outside it"
    (width_over min_int (min_int + cap + 1));
  check "width cap: max_int..max_int (width 0) is inside the cap"
    (not (width_over max_int max_int));
  check "width cap: min_int..min_int (width 0) is inside the cap"
    (not (width_over min_int min_int));
  check "width cap: 0..0 is inside the cap" (not (width_over 0 0));
  check "width cap: a bool's 0..1 is inside the cap" (not (width_over 0 1));

  (* ------------------------------------- the boundary, on the path a user goes down *)
  (* The same pair through Compile, which is where the diagnostic comes from. AT the
     cap is accepted: it compiles, and nothing here solves it or writes its proof.
     ONE OVER is refused, with a position and with the numbers in the message.

     Both bounds are far below Checked.limit = max_int / 16, so the arithmetic cap
     (M1-T23) cannot be what fires -- and the needles below check the message is the
     width one, not the overflow one. A single over-the-cap rejection proves nothing on
     its own: the pair, and the wording, are what locate the boundary. *)
  (* M4-T4b: each of the three, in the shape whose auxiliaries differ -- a case
     variable, a constant case variable, and a sign that the declaration settles. *)
  accepts_compile "arith: int_times over two variables"
    ~src:
      "var -2..2: x;\n\
       var -2..2: y;\n\
       var -4..4: z;\n\
       constraint int_times(x, y, z);\n\
       solve satisfy;\n";
  accepts_compile "arith: int_times with a constant factor (the linear path)"
    ~src:"var -2..2: x;\nvar -6..6: z;\nconstraint int_times(x, 3, z);\nsolve satisfy;\n";
  accepts_compile "arith: int_div with a constant divisor"
    ~src:"var -5..5: x;\nvar -5..5: q;\nconstraint int_div(x, 2, q);\nsolve satisfy;\n";
  accepts_compile "arith: int_div with a divisor whose domain contains zero"
    ~src:
      "var -5..5: x;\n\
       var -2..2: y;\n\
       var -5..5: q;\n\
       constraint int_div(x, y, q);\n\
       solve satisfy;\n";
  accepts_compile "arith: int_abs with the sign settled by the declaration"
    ~src:"var 1..5: x;\nvar 0..5: z;\nconstraint int_abs(x, z);\nsolve satisfy;\n";
  accepts_compile "arith: int_abs over a constant"
    ~src:"var 0..9: z;\nconstraint int_abs(-4, z);\nsolve satisfy;\n";
  ()

(* M7-T1: the compile-level half of the CONTROL, lifted out of [test_rejections] so it
   can be run under an explicit limit. Every assertion is the pre-M7 one, unchanged. *)
let test_width_cap_compile () =
  accepts_compile "width cap: compile accepts a domain at the cap"
    ~src:(Printf.sprintf "var 0..%d: x :: output_var;\nsolve satisfy;\n" cap);
  reject_compile "width cap: compile refuses a domain one over the cap" ~line:1
    ~src:(Printf.sprintf "var 0..%d: x :: output_var;\nsolve satisfy;\n" (cap + 1))
    ~needles:
      [
        "error";
        "`x`";
        Printf.sprintf "0..%d" (cap + 1);
        Printf.sprintf "a width of %d" (cap + 1);
        Printf.sprintf "baguette's limit is %d" cap;
        (* M7-T1: the message now says the refusal is opt-in, and it is telling the
           truth -- this test had to ASK for the limit to see it at all. *)
        "M7-T1: this refusal is OFF by default";
        "order encoding";
        "legal FlatZinc";
        "Narrow the declared domain";
        "<test>:1:1";
      ];
  (* Negative and mixed-sign, through the front end too, so the branch that cannot
     subtract is exercised from the outside as well. *)
  accepts_compile "width cap: compile accepts -5000..5000"
    ~src:"var -5000..5000: x :: output_var;\nsolve satisfy;\n";
  reject_compile "width cap: compile refuses -5001..5000" ~line:1
    ~src:"var -5001..5000: x :: output_var;\nsolve satisfy;\n"
    ~needles:[ "`x`"; "-5001..5000"; "a width of 10001" ];
  (* The width is per variable, and the variable named must be the offending one --
     not the first in the model, and not the last. *)
  reject_compile "width cap: the diagnostic names the offending variable" ~line:3
    ~src:
      (Printf.sprintf
         "var 0..3: a :: output_var;\n\
          var 0..3: b :: output_var;\n\
          var 0..%d: wide :: output_var;\n\
          var 0..3: c :: output_var;\n\
          solve satisfy;\n"
         (cap + 1))
    ~needles:[ "`wide`"; "a width of " ^ string_of_int (cap + 1) ];
  (* A model over BOTH caps is told about the arithmetic one: narrowing to 10 000 would
     not have made it representable, so the width message would send the reader to fix
     the wrong thing. This pins the order of the two passes in Compile. *)
  reject_compile "width cap: over both caps reports the arithmetic cap first" ~line:1
    ~src:"var 0..1000000000000000000: x :: output_var;\nsolve satisfy;\n"
    ~needles:[ "`x`"; "arithmetic limit" ];
  (* And a model over the width cap only must NOT be told about arithmetic. The
     inverse of the case above, and the one that would silently hide a hole in the
     width pass if the arithmetic message ever widened to cover width. *)
  let width_only_msg =
    let m =
      F.Builder.of_string ~file:"<test>"
        (Printf.sprintf "var 0..%d: x;\nsolve satisfy;\n" (cap + 1))
    in
    match F.Error.catch (fun () -> F.Compile.compile m) with
    | Ok _ -> "ACCEPTED"
    | Error (e : F.Error.t) -> F.Error.to_string e
  in
  check "width cap: the width message does not mention the arithmetic limit"
    (not (contains ~needle:"arithmetic limit" width_only_msg))

(* M7-T1, the compile-level INVERSION: the .fzn that [reject_compile] refuses above,
   under the default build, compiles. Same source text, opposite verdict, and the only
   difference between them is the limit. *)
let test_width_cap_compile_default () =
  with_width_limit None (fun () ->
      accepts_compile "M7-T1: compile accepts the domain one over the old cap"
        ~src:(Printf.sprintf "var 0..%d: x :: output_var;\nsolve satisfy;\n" (cap + 1));
      accepts_compile "M7-T1: compile accepts -5001..5000"
        ~src:"var -5001..5000: x :: output_var;\nsolve satisfy;\n";
      (* The ARITHMETIC cap is untouched by M7-T1 and still refuses, first and with its
         own wording. A session removing "the width limits" must not take this with it. *)
      reject_compile "M7-T1: the arithmetic cap still refuses, default build" ~line:1
        ~src:"var 0..1000000000000000000: x :: output_var;\nsolve satisfy;\n"
        ~needles:[ "`x`"; "arithmetic limit" ])

(* =========================================== M7-T7: constants in a search array

   `int_search([x, 3, y], ...)` used to refuse the WHOLE MODEL. It does not any more: a
   constant in the array is a variable with nothing left to decide, so it is skipped and
   the annotation is honoured over the variables that remain (docs/SPEC.md 3.4).

   These assertions are on the DECISION, not on the answer, for the reason
   test_compile.ml states at length: a solver that dropped the annotation entirely and
   searched by [spec_order] would answer every one of these models correctly. The
   decision is the only thing that distinguishes honouring the annotation from ignoring
   it, so the decision is what is checked. *)

module Search = Baguette_core.Search
module Var = Baguette_core.Var

(* The order [Compile] built for [src], applied to [cands] (model variable indices).
   [None] means the model carries no usable annotation at all. *)
let decision_of ?cands src =
  let m = F.Builder.of_string ~file:"<t>" src in
  let c = F.Compile.compile m in
  match c.F.Compile.order with
  | None -> None
  | Some order ->
      let cands =
        match cands with
        | Some idxs -> Array.of_list (List.map Var.of_int idxs)
        | None -> Search.unfixed c.F.Compile.store
      in
      Some (order c.F.Compile.store cands)

let test_search_constants () =
  (* (a) MIXED array. Three variables, declared wide/narrow/mid, and the annotation
     writes `[3, narrow, 7, wide]` -- two constants among two variables, with a constant
     FIRST so that a naive "skip only trailing constants" would still fail.

       wide    0..7   declared first
       narrow  0..1   declared second
       mid     0..5   declared third, NOT named by the annotation

     `input_order` must pick the first still-unfixed element OF THE ANNOTATION'S ARRAY.
     With the constants removed that array is [narrow; wide], so the decision must be on
     [narrow] (index 1) -- which is neither declaration order (that would be [wide],
     index 0) nor first-fail-over-everything. And [indomain_max] must split it at
     hi - 1 = 0, high side first. *)
  let mixed vsel valsel =
    Printf.sprintf
      "var 0..7: wide;\n\
       var 0..1: narrow;\n\
       var 0..5: mid;\n\
       constraint int_le(wide, 7);\n\
       constraint int_le(narrow, 1);\n\
       constraint int_le(mid, 5);\n\
       solve :: int_search([3, narrow, 7, wide], %s, %s, complete) satisfy;\n"
      vsel valsel
  in
  (match F.Error.catch (fun () -> decision_of (mixed "input_order" "indomain_max")) with
  | Error e ->
      incr failures;
      Printf.printf "FAIL M7-T7 (a): a mixed search array was refused: %s\n"
        (F.Error.to_string e)
  | Ok None ->
      incr failures;
      print_endline
        "FAIL M7-T7 (a): the mixed array left no annotation at all; the variables in it \
         must still be searched"
  | Ok (Some d) ->
      check "M7-T7 (a): input_order over [3, narrow, 7, wide] decides `narrow`"
        (Var.to_int d.Search.d_var = 1);
      check "M7-T7 (a): ... and indomain_max splits it high-first at hi - 1"
        (d.Search.d_split = 0 && d.Search.d_high_first));
  (* The same array under [first_fail] must pick [narrow] too -- but that is not evidence
     on its own, so the discriminating case is [wide] made narrowest of the two NAMED
     variables while [mid] (unnamed, narrower still) is a candidate. first_fail over the
     ANNOTATION'S subset must pick from {wide, narrow}, never [mid]. *)
  (match
     F.Error.catch (fun () ->
         decision_of ~cands:[ 0; 1; 2 ]
           "var 0..7: wide;\n\
            var 0..1: narrow;\n\
            var 0..5: mid;\n\
            constraint int_le(wide, 7);\n\
            constraint int_le(narrow, 1);\n\
            constraint int_le(mid, 5);\n\
            solve :: int_search([3, wide, 7], input_order, indomain_min, complete) \
            satisfy;\n")
   with
  | Error e ->
      incr failures;
      Printf.printf "FAIL M7-T7 (a2): refused: %s\n" (F.Error.to_string e)
  | Ok None ->
      incr failures;
      print_endline "FAIL M7-T7 (a2): the annotation was dropped entirely"
  | Ok (Some d) ->
      check
        "M7-T7 (a2): a single variable among constants is still the annotation's subset"
        (Var.to_int d.Search.d_var = 0
        && d.Search.d_split = 0 && not d.Search.d_high_first));
  (* (b) ALL-CONSTANT array. The phase is empty, which is legal: it contributes no
     decision, and `seq_search` falls through to the NEXT phase. Here the second phase
     names [mid], so the decision must be on [mid] (index 2) -- not on [wide] (index 0),
     which is what a fallback to [spec_order]'s declaration-order-ish pick would look
     like if the empty phase had swallowed the sequence. *)
  (match
     F.Error.catch (fun () ->
         decision_of ~cands:[ 0; 1; 2 ]
           "var 0..7: wide;\n\
            var 0..1: narrow;\n\
            var 0..5: mid;\n\
            constraint int_le(wide, 7);\n\
            constraint int_le(narrow, 1);\n\
            constraint int_le(mid, 5);\n\
            solve :: seq_search([int_search([1, 2, 3], input_order, indomain_min, \
            complete), int_search([mid], input_order, indomain_max, complete)]) satisfy;\n")
   with
  | Error e ->
      incr failures;
      Printf.printf "FAIL M7-T7 (b): an all-constant search array was refused: %s\n"
        (F.Error.to_string e)
  | Ok None ->
      incr failures;
      print_endline "FAIL M7-T7 (b): the whole seq_search was dropped"
  | Ok (Some d) ->
      check "M7-T7 (b): an all-constant phase makes no decision; seq_search falls through"
        (Var.to_int d.Search.d_var = 2);
      check "M7-T7 (b): ... and the phase that DID fire is the one that chose the value"
        (d.Search.d_split = 4 && d.Search.d_high_first));
  (* (b2) An all-constant array as the ONLY annotation: no phase can fire, so every
     decision comes from docs/SPEC.md 3.4's default. It must not raise and must not
     deadlock -- [Search.sequence]'s fallback is what carries it. *)
  (match
     F.Error.catch (fun () ->
         decision_of ~cands:[ 0; 1 ]
           "var 0..7: wide;\n\
            var 0..1: narrow;\n\
            constraint int_le(wide, 7);\n\
            constraint int_le(narrow, 1);\n\
            solve :: int_search([1, 2, 3], input_order, indomain_max, complete) satisfy;\n")
   with
  | Error e ->
      incr failures;
      Printf.printf "FAIL M7-T7 (b2): refused: %s\n" (F.Error.to_string e)
  | Ok None ->
      (* Legal too: no phase can ever fire, so "no annotation" and "one empty phase" are
         the same search. Either shape passes; a raise or a wrong decision does not. *)
      check "M7-T7 (b2): an only-constants annotation searches by the 3.4 default" true
  | Ok (Some d) ->
      (* [spec_order] = first_fail + indomain_min: [narrow] (index 1), low side first. *)
      check "M7-T7 (b2): an only-constants annotation searches by the 3.4 default"
        (Var.to_int d.Search.d_var = 1
        && d.Search.d_split = 0 && not d.Search.d_high_first));
  (* The strategy checks are NOT relaxed by an empty array: 3.4 says an unsupported
     strategy MUST be refused, and an array that happens to hold only constants does not
     change what the annotation asked for. *)
  (* M7-T9 shipped `smallest`, which this assertion used to use as its example of an
     unsupported strategy. The assertion is unchanged in strength -- `anti_first_fail` is
     still unsupported and still must be refused; only the example moved. *)
  reject "M7-T7: an all-constant array does not excuse an unsupported strategy" ~line:2
    ~src:
      "var 1..3: x;\n\
       solve :: int_search([1, 2], anti_first_fail, indomain_min, complete) satisfy;\n"
    ~needles:[ "unsupported variable-selection strategy" ];
  reject "M7-T7: ... nor an unsupported value choice" ~line:2
    ~src:
      "var 1..3: x;\n\
       solve :: int_search([1, x], input_order, indomain_random, complete) satisfy;\n"
    ~needles:[ "unsupported value-choice strategy" ]

(* ====================================== M7-T9: smallest, largest, indomain_split

   Three of the four strategies docs/ROADMAP.md M7-T9 sized. The fourth,
   `indomain_median`, is REFUSED and its refusal is asserted below beside them --
   `lib/flatzinc/builder.ml` carries the argument, and the short version is that a
   baguette decision is one order literal, so assigning an interior value is not a
   value-choice change but a change to the decision shape.

   EVERY ASSERTION HERE IS ON THE DECISION, NOT ON THE ANSWER, and for these four that
   is not a stylistic preference: a value choice cannot change the answer at all (the
   search is complete either way), and a variable choice changes only the order the
   leaves are visited in. A test that checked the solution could not tell any of these
   apart from `input_order`, from each other, or from the annotation being dropped on
   the floor -- which is the failure docs/SPEC.md 3.4 exists to forbid. *)

(* The four-way model. FIVE variables, chosen so that the four variable-selection
   strategies pick FOUR DIFFERENT ONES, and so that the reading of `largest` this project
   did NOT take picks a fifth:

     index  name  domain  size  lo  hi
       0    w     4..8      5    4   8
       1    x     0..6      7    0   6
       2    y     2..3      2    2   3
       3    z     5..9      5    5   9
       4    u     7..8      2    7   8

   input_order -> w  (first in the annotation's array)
   first_fail  -> y  (smallest domain; ties with u at 2, broken by array order)
   smallest    -> x  (smallest domain MINIMUM, 0)
   largest     -> z  (largest domain MAXIMUM, 9)

   and the rejected reading of `largest` -- "the largest domain minimum" -- would pick
   u (lo = 7), which is why u is in the model. Without it `largest` and "largest lo"
   agree and the assertion would be evidence of nothing. *)
let quad vsel valsel =
  Printf.sprintf
    "var 4..8: w;\n\
     var 0..6: x;\n\
     var 2..3: y;\n\
     var 5..9: z;\n\
     var 7..8: u;\n\
     constraint int_le(w, 8);\n\
     constraint int_le(x, 6);\n\
     constraint int_le(y, 3);\n\
     constraint int_le(z, 9);\n\
     constraint int_le(u, 8);\n\
     solve :: int_search([w, x, y, z, u], %s, %s, complete) satisfy;\n"
    vsel valsel

let picks name src expect_idx =
  match F.Error.catch (fun () -> decision_of src) with
  | Error e ->
      incr failures;
      Printf.printf "FAIL %s: refused: %s\n" name (F.Error.to_string e)
  | Ok None ->
      incr failures;
      Printf.printf "FAIL %s: the annotation was dropped entirely\n" name
  | Ok (Some d) ->
      if Var.to_int d.Search.d_var = expect_idx then Printf.printf "ok   %s\n" name
      else (
        incr failures;
        Printf.printf "FAIL %s: decided variable index %d, expected %d\n" name
          (Var.to_int d.Search.d_var) expect_idx)

let test_search_strategies () =
  (* (a) The four variable selections, on ONE model, each naming a different variable.
     Run as a group so that a change which collapsed two of them would fail loudly
     rather than pass three assertions and one tautology. *)
  picks "M7-T9: input_order decides w (the array's first element)"
    (quad "input_order" "indomain_min")
    0;
  picks "M7-T9: first_fail decides y (the smallest domain)"
    (quad "first_fail" "indomain_min")
    2;
  picks "M7-T9: smallest decides x (the smallest domain MINIMUM)"
    (quad "smallest" "indomain_min")
    1;
  picks "M7-T9: largest decides z (the largest domain MAXIMUM, not the largest minimum)"
    (quad "largest" "indomain_min")
    3;
  (* (b) The three value choices, all on the SAME variable, so that the only thing that
     varies is the split. `smallest` pins the variable to x (0..6), and:

       indomain_min   splits at lo = 0,        low side first
       indomain_max   splits at hi - 1 = 5,    high side first
       indomain_split splits at the RANGE MIDPOINT 0 + (6 - 0) / 2 = 3, low side first

     3 is distinct from both, which is what makes this evidence rather than a
     coincidence: a build that quietly aliased indomain_split to either of the other two
     would fail here. *)
  let vals name valsel expect_split expect_high =
    match F.Error.catch (fun () -> decision_of (quad "smallest" valsel)) with
    | Error e ->
        incr failures;
        Printf.printf "FAIL %s: refused: %s\n" name (F.Error.to_string e)
    | Ok None ->
        incr failures;
        Printf.printf "FAIL %s: the annotation was dropped entirely\n" name
    | Ok (Some d) ->
        check name
          (Var.to_int d.Search.d_var = 1
          && d.Search.d_split = expect_split
          && d.Search.d_high_first = expect_high)
  in
  vals "M7-T9: indomain_min splits x at lo, low-first" "indomain_min" 0 false;
  vals "M7-T9: indomain_max splits x at hi - 1, high-first" "indomain_max" 5 true;
  vals "M7-T9: indomain_split bisects x at the range midpoint, low-first" "indomain_split"
    3 false;
  (* (c) INDOMAIN_SPLIT ON A DOMAIN WITH HOLES -- the one place a naive implementation is
     quietly wrong, and the reason this assertion runs the engine first.

     `var 0..6: x` with `int_ne(x, 3)` propagates to lo = 0, hi = 6 and an INTERIOR HOLE
     at 3. Two answers are then available and they differ:

       the RANGE midpoint          lo + (hi - lo) / 2                   = 3   <- correct
       the MEDIAN of the VALUES    {0,1,2,4,5,6}, lower middle element  = 2

     The second is `indomain_median`'s quantity, not `indomain_split`'s: MiniZinc says
     "bisect the domain", which is the interval bisection Gecode's INT_VAL_SPLIT_MIN
     performs. So 3 is the assertion, and it also happens to land ON the hole -- which is
     legal and is the M1-T55 case: [Domain.settle] walks the pushed bound past 3 to 2, so
     the decision lands strictly stronger than the order literal its nogood negates.
     test/models/search_split_hole_unsat.fzn is that case end to end with its proof
     checked, and test_hole_split_sweep in test/unit/test_engine.ml is the exhaustive
     sweep over every such shape. *)
  (match
     F.Error.catch (fun () ->
         let m =
           F.Builder.of_string ~file:"<t>"
             "var 0..6: x;\n\
              var 0..6: y;\n\
              constraint int_ne(x, 3);\n\
              constraint int_le(y, 6);\n\
              solve :: int_search([x, y], input_order, indomain_split, complete) satisfy;\n"
         in
         let c = F.Compile.compile m in
         let store = c.F.Compile.store in
         let outcome = Baguette_core.Engine.propagate c.F.Compile.engine store in
         let d0 = Baguette_core.Store.get store (Var.of_int 0) in
         let order =
           match c.F.Compile.order with Some o -> o | None -> Search.spec_order
         in
         (outcome, d0, order store [| Var.of_int 0; Var.of_int 1 |]))
   with
  | Error e ->
      incr failures;
      Printf.printf "FAIL M7-T9 (c): the holey model was refused: %s\n"
        (F.Error.to_string e)
  | Ok (_, d0, d) ->
      check "M7-T9 (c): int_ne left an interior hole to split across"
        (Baguette_core.Domain.lo d0 = 0
        && Baguette_core.Domain.hi d0 = 6
        && (not (Baguette_core.Domain.mem d0 3))
        && Baguette_core.Domain.size d0 = 6);
      check
        "M7-T9 (c): indomain_split takes the RANGE midpoint 3 across a hole, not the \
         value median 2"
        (Var.to_int d.Search.d_var = 0
        && d.Search.d_split = 3 && not d.Search.d_high_first));
  (* (d) `indomain_median` is refused, and the diagnostic must say WHY rather than just
     that it is unsupported -- the reason is the deliverable for this case, because a
     reader who hits it on a real model would otherwise re-derive the analysis. The
     needles pin the three load-bearing claims: that it is an interior value, that the
     sibling branch is a disjunction, and that the successor row is named. *)
  reject "M7-T9: indomain_median is refused, with its actual reason" ~line:2
    ~src:
      "var 1..9: x;\n\
       solve :: int_search([x], input_order, indomain_median, complete) satisfy;\n"
    ~needles:[ "indomain_median"; "INTERIOR"; "disjunction"; "M7-T12"; "indomain_split" ];
  (* And the two strategies that remain unsupported are still refused, at full strength.
     `anti_first_fail` and `indomain_random` are the rest of what MiniZinc defines; they
     must not have been swept into a catch-all while the four above were added. *)
  reject "M7-T9: anti_first_fail is still refused" ~line:2
    ~src:
      "var 1..9: x;\n\
       solve :: int_search([x], anti_first_fail, indomain_min, complete) satisfy;\n"
    ~needles:[ "unsupported variable-selection strategy"; "anti_first_fail" ];
  reject "M7-T9: indomain_random is still refused" ~line:2
    ~src:
      "var 1..9: x;\n\
       solve :: int_search([x], input_order, indomain_random, complete) satisfy;\n"
    ~needles:[ "unsupported value-choice strategy"; "indomain_random" ]

(* ============================== M7-T9: what indomain_split COSTS in the proof

   docs/ROADMAP.md's M7-T9 row predicted that `indomain_split` would be CHEAPER to
   justify than `indomain_min`, on the argument that it branches on an ORDER LITERAL and
   the order encoding is built out of exactly those (D-0028). The row asked for the claim
   to be measured rather than asserted. It is measured here, and IT DOES NOT HOLD -- on
   this model `indomain_split` is DEARER, and the reason the prediction failed is more
   useful than the prediction.

   THE PREDICTION IS ABOUT THE WRONG QUANTITY. Every decision this solver makes is
   already one order literal: `Search.branch` writes `x_ge_(k+1)` for `indomain_min`,
   `indomain_max` and `indomain_split` alike, and neither the bridge (M1-T55) nor the
   nogood is shaped by where k sits inside [lo, hi). So the PER-DECISION cost of the three
   is identical by construction, and there was never a saving available there. What a
   value choice changes is the TREE: how many decisions get made, and how deep.

   So the comparison is a tree comparison wearing proof-sized units, and which way it goes
   is a property of the model, not of the encoding. Two models, both measured while
   writing this:

     (i)  every sum of x + y forbidden (a flat refutation -- the first decision on x
          fixes it, which wipes y whatever the decision was). The two searches are
          isomorphic: 271 derivation lines and 45 opened levels EACH at width 16, and the
          proofs differ by 105 bytes of literal spelling and nothing else.
     (ii) the model below, whose only solution sits at the TOP of x's domain. Here
          `indomain_min` walks a spine and finds it last; `indomain_split` bisects, which
          costs internal nodes the spine does not have, and the low half it explores first
          is entirely fruitless. Split loses.

   The honest general statement is therefore: `indomain_split` costs the same per
   decision and a different number of decisions, and on a model whose answer the spine
   reaches early the bisection's extra internal nodes are a NET LOSS in proof size. The
   assertion below is on the DIRECTION, with both numbers printed, so that a future
   session that flips it learns something rather than merely going red. *)

let cmp_src valsel =
  let b = Buffer.create 1024 in
  Buffer.add_string b "var 0..15: x :: output_var;\nvar 0..15: y :: output_var;\n";
  (* Every sum from 0 to 29 forbidden, so x = y = 15 is the one solution -- and it is the
     LAST value `indomain_min` reaches. int_lin_ne is value-consistent, so none of these
     rows prunes anything until one of the two variables is fixed: the tree is real. *)
  for s = 0 to 29 do
    Buffer.add_string b (Printf.sprintf "constraint int_lin_ne([1, 1], [x, y], %d);\n" s)
  done;
  Buffer.add_string b
    (Printf.sprintf "solve :: int_search([x, y], input_order, %s, complete) satisfy;\n"
       valsel);
  Buffer.contents b

(* Solve one of them to a real .opb/.pbp pair, run veripb over it, and report the two
   sizes. [None] for the checker is a FAILURE at the call site, never a skip (M1-T18). *)
let cmp_run dir tag valsel =
  let m = F.Builder.of_string ~file:tag (cmp_src valsel) in
  let c = F.Compile.compile m in
  let opb = Filename.concat dir (tag ^ ".opb")
  and pbp = Filename.concat dir (tag ^ ".pbp") in
  let oc = open_out opb in
  Baguette_proof.Encoding.write_opb c.F.Compile.encoding oc;
  close_out oc;
  let oc = open_out pbp in
  let writer = Baguette_proof.Writer.create ~audit:true oc in
  Baguette_proof.Encoding.start_proof c.F.Compile.encoding writer;
  let ctx = Baguette_core.Justify.create ~writer ~encoding:c.F.Compile.encoding in
  let check_asn assignment =
    let values = Array.make (F.Model.nvars m) 0 in
    List.iter (fun (v, x) -> values.(Var.to_int v) <- x) assignment;
    F.Model.check_assignment m values
  in
  let order = match c.F.Compile.order with Some o -> o | None -> Search.spec_order in
  let outcome =
    Search.solve ~engine:c.F.Compile.engine ~store:c.F.Compile.store ~ctx ~check:check_asn
      ~order ()
  in
  close_out oc;
  let ic = open_in_bin pbp in
  let proof = really_input_string ic (in_channel_length ic) in
  close_in ic;
  let lines = String.split_on_char '\n' proof in
  (* A DERIVATION LINE is one that mints a constraint id, which in this writer's output
     is the labelled form `@cN <rule> ...`. Counting those rather than all lines keeps
     comments, deletions and the header out of the number. *)
  let derivations =
    List.length
      (List.filter (fun l -> String.length l > 2 && l.[0] = '@' && l.[1] = 'c') lines)
  in
  (outcome, opb, pbp, String.length proof, derivations)

let test_split_vs_min_proof_size () =
  let dir = Filename.temp_file "baguette_m7t9" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  let o_min, opb_min, pbp_min, bytes_min, der_min = cmp_run dir "min" "indomain_min" in
  let o_spl, opb_spl, pbp_spl, bytes_spl, der_spl =
    cmp_run dir "split" "indomain_split"
  in
  (* Same problem, same answer, whichever way the tree was walked. A value choice that
     changed the ANSWER would be a soundness bug, not a heuristic. *)
  let sat = function Search.Sat _ -> true | _ -> false in
  check "M7-T9: indomain_min and indomain_split agree on the answer"
    (sat o_min && sat o_spl);
  (* Both proofs are checked. A size comparison between two artefacts nobody verified
     would be a comparison of two guesses. *)
  (match Baguette_proof.Checker.find () with
  | None ->
      incr failures;
      print_endline
        "FAIL M7-T9: veripb not found -- NEITHER proof in the size comparison was \
         checked. Do not treat this as a pass."
  | Some veripb ->
      let run opb pbp =
        Sys.command
          (Printf.sprintf "%s %s %s > /dev/null 2>&1" (Filename.quote veripb)
             (Filename.quote opb) (Filename.quote pbp))
        = 0
      in
      check "M7-T9: veripb accepts the indomain_min proof" (run opb_min pbp_min);
      check "M7-T9: veripb accepts the indomain_split proof" (run opb_spl pbp_spl));
  Printf.printf
    "     M7-T9 proof cost, x,y in 0..15, only solution at the top of x:\n\
    \       indomain_min   %d bytes, %d derivation lines\n\
    \       indomain_split %d bytes, %d derivation lines\n"
    bytes_min der_min bytes_spl der_spl;
  (* THE FINDING, asserted. If this goes red, indomain_split has become the cheaper of
     the two on this model -- which would be a real change in the search or the learning
     and is worth understanding before the assertion is flipped. Do not flip it to match
     new numbers without saying what moved. *)
  check
    "M7-T9: indomain_split's proof is NOT cheaper than indomain_min's -- the roadmap's \
     prediction is refuted"
    (bytes_spl >= bytes_min && der_spl >= der_min);
  List.iter
    (fun f -> try Sys.remove f with _ -> ())
    [ opb_min; pbp_min; opb_spl; pbp_spl ];
  try Sys.rmdir dir with _ -> ()

(* ============================================================================== main *)

let () =
  (match models_dir with
  | None ->
      incr failures;
      print_endline
        "FAIL could not locate test/models/ from the current directory or the executable \
         path; the shipped-model assertions did not run"
  | Some d -> Printf.printf "(models from %s)\n" d);
  if models_dir <> None then (
    test_trivial_sat ();
    test_trivial_unsat ();
    test_lin_sat ();
    test_lin_unsat ();
    test_ne_sat ());
  test_kitchen_sink ();
  test_misc_accepts ();
  test_constant_folding ();
  test_rejections ();
  test_search_constants ();
  test_search_strategies ();
  test_split_vs_min_proof_size ();
  (* M7-T1. The inversion first -- it is the change -- then the control, which runs
     every pre-M7 assertion under an explicit --max-order-width=10000. *)
  test_width_cap_default ();
  test_width_warning ();
  test_width_cap_compile_default ();
  with_width_limit (Some cap) test_width_cap_boundary;
  with_width_limit (Some cap) test_width_cap_compile;
  check_str "error rendering carries file:line:col" ~expected:"<t>:2:12: error: boom"
    ~actual:(F.Error.to_string { F.Error.pos = F.Pos.make "<t>" 2 12; msg = "boom" });
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "\nflatzinc unit tests passed"
