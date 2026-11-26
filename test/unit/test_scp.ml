(* Unit tests for the `.scp` reader (M23-inputs, D-0230): lib/scp/sexp.ml (T1) and
   lib/scp/reader.ml (T2..T4).

   The s-expression half checks the tree and the POSITIONS, the four malformed shapes
   (unbalanced, stray text after the form, empty input, a byte the format refuses), a
   long atom, an atom that straddles the 64 KiB read buffer, and a nesting depth no
   recursive reader survives. The reader half checks that each refusal D-0230 lists is
   a refusal WITH A POSITION, and that the accepted forms build the Model.t constructors
   D-0230 section 4 says they do. The end-to-end behaviour (answers, proofs) is the
   lanes' job: scripts/run_scp_tests.sh and tools/scp/fzn_lane.sh. *)

module F = Baguette_flatzinc
module M = F.Model
module S = Baguette_scp.Sexp
module R = Baguette_scp.Reader

let () = Mem_guard.install ()
let failures = ref 0

let check name cond =
  if cond then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s\n" name)

let contains s sub =
  let n = String.length s and k = String.length sub in
  let rec go i = i + k <= n && (String.sub s i k = sub || go (i + 1)) in
  go 0

(* [f ()] must raise the front end's error, at [line:col], with [frag] in the message. *)
let check_error name ~at:(line, col) ~frag f =
  match f () with
  | exception F.Error.Error { F.Error.pos; msg } ->
      let ok = pos.F.Pos.line = line && pos.F.Pos.col = col && contains msg frag in
      if ok then Printf.printf "ok   %s\n" name
      else (
        incr failures;
        Printf.printf "FAIL %s\n       got %d:%d %s\n" name pos.F.Pos.line pos.F.Pos.col
          msg)
  | _ ->
      incr failures;
      Printf.printf "FAIL %s: no error\n" name

let sx s = S.parse_string ~file:"t" s

(* ------------------------------------------------------------------ T1: Sexp *)

let () =
  (match sx "(a (b  c)\n  d)" with
  | S.List
      ( [
          S.Atom ("a", { F.Pos.line = 1; col = 2; _ });
          S.List
            ([ S.Atom ("b", _); S.Atom ("c", { F.Pos.col = 8; _ }) ], { F.Pos.col = 4; _ });
          S.Atom ("d", { F.Pos.line = 2; col = 3; _ });
        ],
        { F.Pos.line = 1; col = 1; _ } ) ->
      check "sexp: tree and positions" true
  | _ -> check "sexp: tree and positions" false);
  (match sx "()" with
  | S.List ([], _) -> check "sexp: the empty list" true
  | _ -> check "sexp: the empty list" false);
  (match sx "  atom  " with
  | S.Atom ("atom", { F.Pos.col = 3; _ }) -> check "sexp: a lone atom is a form" true
  | _ -> check "sexp: a lone atom is a form" false);
  check_error "sexp: unbalanced (a list never closed)" ~at:(2, 1) ~frag:"never closed"
    (fun () -> sx "(a (b c)\n");
  check_error "sexp: a `)` with no `(`" ~at:(1, 1) ~frag:"no `(` open" (fun () -> sx ")");
  check_error "sexp: stray text after the form" ~at:(1, 5) ~frag:"after the end"
    (fun () -> sx "(a) b");
  check_error "sexp: a second `)` after the form" ~at:(1, 4) ~frag:"after the end"
    (fun () -> sx "(a))");
  check_error "sexp: empty input" ~at:(1, 1) ~frag:"ends where" (fun () -> sx "");
  check_error "sexp: white space only" ~at:(3, 1) ~frag:"ends where" (fun () ->
      sx " \n\n");
  check_error "sexp: a `;` comment is refused" ~at:(2, 3) ~frag:"comment" (fun () ->
      sx "(a\n  ; note\n)");
  check_error "sexp: a double quote is refused" ~at:(1, 4) ~frag:"quoted" (fun () ->
      sx "(a \"b\")");
  check_error "sexp: a control byte is refused" ~at:(1, 3) ~frag:"0x01" (fun () ->
      sx "(a\001)");
  (* a long atom, a million bytes *)
  let long = String.make 1_000_000 'x' in
  (match sx ("(" ^ long ^ ")") with
  | S.List ([ S.Atom (a, _) ], _) ->
      check "sexp: a 1 MB atom" (String.length a = 1_000_000)
  | _ -> check "sexp: a 1 MB atom" false);
  (* a nesting depth that would overflow a recursive reader's stack *)
  let depth = 1_000_000 in
  let s = String.make depth '(' ^ String.make depth ')' in
  (match sx s with
  | t ->
      let rec measure t d =
        match t with
        | S.List ([ t' ], _) -> measure t' (d + 1)
        | S.List ([], _) -> d + 1
        | _ -> -1
      in
      check "sexp: nesting depth 1e6, no stack" (measure t 0 = depth)
  | exception Stack_overflow -> check "sexp: nesting depth 1e6, no stack" false);
  (* through a channel: atoms straddling the 64 KiB buffer, positions kept across it *)
  let path = Filename.temp_file "test_scp" ".scp" in
  let oc = open_out_bin path in
  let n = 50_000 in
  output_string oc "(";
  for i = 1 to n do
    Printf.fprintf oc "atom%d%s" i (if i mod 10 = 0 then "\n" else " ")
  done;
  output_string oc ")\n";
  close_out oc;
  let ic = open_in_bin path in
  let t = S.read (S.of_channel ~file:path ic) in
  close_in ic;
  Sys.remove path;
  (match t with
  | S.List (es, _) ->
      let all_ok = ref (List.length es = n) in
      List.iteri
        (fun i e ->
          match e with
          | S.Atom (a, p) ->
              if a <> Printf.sprintf "atom%d" (i + 1) || p.F.Pos.line <> (i / 10) + 1 then
                all_ok := false
          | _ -> all_ok := false)
        es;
      check "sexp: 50 000 atoms through the channel, across buffer ends" !all_ok
  | _ -> check "sexp: 50 000 atoms through the channel, across buffer ends" false);
  (* integers, as cake's mlint$fromString *)
  let p = F.Pos.unknown in
  check "int: 42" (S.int_of_atom p "42" = Some 42);
  check "int: -7 and ~7"
    (S.int_of_atom p "-7" = Some (-7) && S.int_of_atom p "~7" = Some (-7));
  check "int: 007" (S.int_of_atom p "007" = Some 7);
  check "int: names are not integers"
    (List.for_all
       (fun a -> S.int_of_atom p a = None)
       [ "x"; "5x"; "-"; "~"; "+5"; "0x10"; "1_0" ]);
  check "int: min_int reads" (S.int_of_atom p "-4611686018427387904" = Some min_int);
  check_error "int: 2^62 does not fit" ~at:(0, 0) ~frag:"63 bits" (fun () ->
      S.int_of_atom p "4611686018427387904")

(* ------------------------------------------------------------------ T2..T4: Reader *)

let doc vars cons pt =
  Printf.sprintf "( (version 1)\n(variables %s)\n(constraints %s)\n(prob_type %s) )" vars
    cons pt

let rd s = R.of_string ~file:"t" s
let ks (m : M.t) = List.map (fun c -> c.M.k) m.M.constraints

let () =
  (* refusals, each with its position *)
  check_error "reader: version 2 is refused" ~at:(1, 12) ~frag:"version 1" (fun () ->
      rd "( (version 2) (variables) (constraints) (prob_type decide) )");
  check_error "reader: sections out of order" ~at:(1, 16) ~frag:"`variables`" (fun () ->
      rd "( (version 1) (constraints) (variables) (prob_type decide) )");
  check_error "reader: an undeclared name" ~at:(3, 31) ~frag:"not a declared variable"
    (fun () -> rd (doc "(x 0 3)" "(c1 less_equal x y)" "decide"));
  check_error "reader: a variable declared twice" ~at:(2, 21) ~frag:"declared twice"
    (fun () -> rd (doc "(x 0 3) (x 0 3)" "" "decide"));
  check_error "reader: a constraint name used twice" ~at:(3, 35) ~frag:"used twice"
    (fun () -> rd (doc "(x 0 3)" "(c1 less_equal x 2) (c1 less_equal x 1)" "decide"));
  check_error "reader: lb > ub" ~at:(2, 13) ~frag:"3 > 1" (fun () ->
      rd (doc "(x 3 1)" "" "decide"));
  check_error "reader: a view is refused" ~at:(3, 29) ~frag:"view" (fun () ->
      rd (doc "(x 0 3) (y 0 3)" "(c1 less_equal (x + 3) y)" "decide"));
  check_error "reader: a half reification is refused" ~at:(3, 14) ~frag:"half reification"
    (fun () -> rd (doc "(x 0 3) (b 0 1)" "(c1 equals_if (b = 1) x 2)" "decide"));
  check_error "reader: lin_equals_iff over a variable condition" ~at:(3, 14)
    ~frag:"out until the user" (fun () ->
      rd (doc "(x 0 3) (b 0 1)" "(c1 lin_equals_iff (b = 1) (1 x) 2)" "decide"));
  check_error "reader: an unknown keyword" ~at:(3, 14) ~frag:"does not take" (fun () ->
      rd (doc "(x 0 3)" "(c1 frobnicate x)" "decide"));
  check_error "reader: modulus is refused by name" ~at:(3, 18) ~frag:"decomposes"
    (fun () -> rd (doc "(x 0 3) (y 1 3) (z 0 3)" "(c1 modulus x y z)" "decide"));
  check_error "reader: lex_ is refused" ~at:(3, 18) ~frag:"lexicographic" (fun () ->
      rd (doc "(x 0 3) (y 0 3)" "(c1 lex_less_equal (x) (y))" "decide"));
  check_error "reader: an element over variables" ~at:(3, 14) ~frag:"must be constants"
    (fun () -> rd (doc "(x 0 3) (i 0 1) (z 0 3)" "(c1 element (x 2) (i 0) z)" "decide"));
  check_error "reader: a table wildcard" ~at:(3, 32) ~frag:"wildcard" (fun () ->
      rd (doc "(x 0 3) (y 0 3)" "(c1 table ((1 2) (* 3)) (x y))" "decide"));
  check_error "reader: a nondeterministic regular" ~at:(3, 14) ~frag:"nondeterministic"
    (fun () ->
      rd
        (doc "(x 0 3) (y 0 3)" "(c1 regular (x y) 2 (((1 0) (1 1)) ((2 1))) (1))" "decide"));
  check_error "reader: the objective must be declared" ~at:(4, 22) ~frag:"not a declared"
    (fun () -> rd (doc "(x 0 3)" "" "(minimize y)"));
  check_error "reader: text after the problem" ~at:(4, 22) ~frag:"after the end"
    (fun () -> rd (doc "(x 0 3)" "" "decide" ^ " x"));
  check_error "reader: a variable named like an integer" ~at:(2, 13)
    ~frag:"reads as an integer" (fun () -> rd (doc "(-3 0 3)" "" "decide"));
  check_error "reader: a `;` comment" ~at:(3, 14) ~frag:"comment" (fun () ->
      rd (doc "(x 0 3)" "; c\n" "decide"));
  (* the accepted forms *)
  let m =
    rd (doc "(x 0 3) (y -2 5) (b 0 1)" "(c1 lin_less_equal (2 x 3 y 4 5) 7)" "enumerate")
  in
  check "reader: a 0..1 variable is a Dbool, the others a range"
    (m.M.vars.(2).M.v_dom = M.Dbool && m.M.vars.(1).M.v_dom = M.Drange (-2, 5));
  check "reader: lin_less_equal folds its constant (7 - 4*5)"
    (ks m = [ M.Int_lin_le ([ (2, 0); (3, 1) ], -13) ]);
  check "reader: enumerate is decide" (m.M.objective = M.Satisfy);
  check "reader: every variable of the file is printed, in order"
    (m.M.output
    = [
        M.Out_var ("x", M.Oint, M.Var 0);
        M.Out_var ("y", M.Oint, M.Var 1);
        M.Out_var ("b", M.Oint, M.Var 2);
      ]);
  let m =
    rd (doc "(x 0 3) (y 0 3)" "(c1 lin_greater_than (1 x -1 y) y)" "(maximize x)")
  in
  check "reader: lin_greater_than is a negated <= row, Y moved left"
    (ks m = [ M.Int_lin_le ([ (-1, 0); (1, 1); (1, 1) ], -1) ]
    && m.M.objective = M.Maximize (M.Var 0));
  let m = rd (doc "(x 0 3) (y 0 3) (b 0 1)" "(c1 less_equal_iff (b = 0) x y)" "decide") in
  check "reader: (b = 0) <-> x <= y is b <-> x > y, no auxiliary"
    (Array.length m.M.vars = 3
    && ks m = [ M.Int_lin_le_reif ([ (1, 1); (-1, 0) ], -1, M.Var 2) ]);
  let m = rd (doc "(x 0 9) (b 0 1)" "(c1 or ((x >= 4) (b = 0)) (1 = 1))" "decide") in
  check "reader: a condition over an integer is one auxiliary, then a clause"
    (Array.length m.M.vars = 3
    && ks m
       = [
           M.Int_le_reif (M.Const 4, M.Var 0, M.Var 2);
           M.Bool_clause ([ M.Var 2 ], [ M.Var 1 ]);
         ]
    && m.M.vars.(2).M.v_name = "scp_cond_0");
  let m =
    rd
      (doc "(x 0 9) (y 0 9)" "(c1 in (1 3 5) x) (c2 in (2 3 9) y) (c3 in (0 4) y)"
         "decide")
  in
  check "reader: in over constants restricts the domain"
    (m.M.vars.(0).M.v_dom = M.Dset [ 1; 3; 5 ]
    && m.M.vars.(1).M.v_dom = M.Dset [ 2; 3; 9 ]
    && ks m = [ M.Bool_clause ([], []) ]);
  let m = rd (doc "(i -1 2) (z 0 9)" "(c1 element (7 8 9) (i -1) z)" "decide") in
  check "reader: element with offset -1 indexes through i' = i + 2"
    (m.M.vars.(2).M.v_dom = M.Drange (1, 4)
    && ks m
       = [
           M.Int_lin_eq ([ (1, 2); (-1, 0) ], 2);
           M.Array_int_element (M.Var 2, [| 7; 8; 9 |], M.Var 1);
         ]);
  let m = rd (doc "(a 0 2) (b 0 2) (c 0 2)" "(c1 circuit (a b c))" "decide") in
  check "reader: circuit is mznlib's shape, root 0, n - 1 positions on 1..n - 1"
    (Array.length m.M.vars = 5
    && m.M.vars.(3).M.v_dom = M.Drange (1, 2)
    && List.length (ks m) = 5);
  let m = rd (doc "(x 0 3) (y 0 3)" "(c1 table ((1 2) (2 7) (3 3)) (x y))" "decide") in
  check "reader: table keeps the rows in the domains, one selector each"
    (match ks m with
    | [ M.Table { M.tab_t = [| 1; 2; 3; 3 |]; tab_s = [ M.Var 2; M.Var 3 ]; _ } ] -> true
    | _ -> false);
  let m =
    rd (doc "(x 1 2) (y 1 2)" "(c1 regular (x y) 2 (((1 1)) ((2 0))) (1))" "decide")
  in
  check "reader: regular is a DFA, states shifted by one, (n + 1) * Q flags"
    (match ks m with
    | [
     M.Regular
       {
         M.r_nq = 2;
         r_smin = 1;
         r_delta = [| 2; 0; 0; 1 |];
         r_q0 = 1;
         r_final = [| 2 |];
         r_flags;
         _;
       };
    ] ->
        List.length r_flags = 6
    | _ -> false);
  let m =
    rd
      (doc "(x -3 3) (y 1 3) (z -9 9)"
         "(c1 multiply x y z) (c2 divide x y z) (c3 abs x z)" "decide")
  in
  check "reader: the arithmetic family carries Arith_aux's auxiliaries"
    (match ks m with
    | [ M.Int_times (_, _, _, a); M.Int_div (_, _, _, d); M.Int_abs (_, _, s) ] ->
        a.M.x_sign <> None
        && List.length a.M.y_ge = 2
        && List.length d.M.y_ge = 2
        && s.M.x_sign <> None
    | _ -> false)

let () =
  if !failures > 0 then (
    Printf.printf "%d FAILED\n" !failures;
    exit 1)
  else print_endline "test_scp: all passed"
