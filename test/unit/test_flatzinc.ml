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
