(* Unit tests for the proof layer: literal naming, OPB rendering, proof emission.

   Literal names are part of the contract (docs/PROOF-FORMAT.md section 3) — a test that
   pins them is a test that stops someone quietly introducing a second naming scheme.

   The last test in this file builds a real .opb/.pbp pair and runs veripb over it.
   "A test that does not check the proof is half a test" (CLAUDE.md), and invariant
   I-X1 — every emitted rule is accepted by VeriPB — is the product. If veripb is not
   installed the test says so loudly rather than passing quietly. *)

module Lit = Baguette_proof.Lit
module Opb = Baguette_proof.Opb
module Writer = Baguette_proof.Writer
module Pol = Baguette_proof.Writer.Pol
module Encoding = Baguette_proof.Encoding

let failures = ref 0

let check name cond =
  if cond then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s\n" name)

let check_eq name ~expected ~got =
  if String.equal expected got then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s\n       expected: %s\n            got: %s\n" name expected got)

let raises name f =
  match f () with
  | exception _ -> Printf.printf "ok   %s\n" name
  | _ ->
      incr failures;
      Printf.printf "FAIL %s (expected an exception)\n" name

(* ------------------------------------------------------------------ *)
(* Lit                                                                 *)
(* ------------------------------------------------------------------ *)

let test_lits () =
  check "lit: order-encoding name" (Lit.to_string (Lit.ge "x" 3) = "x_ge_3");
  check "lit: upper bound is a negated order literal"
    (Lit.to_string (Lit.le "x" 4) = "~x_ge_5");
  check "lit: negative values avoid '-'" (Lit.to_string (Lit.ge "x" (-2)) = "x_ge_m2");
  check "lit: direct encoding" (Lit.to_string (Lit.eq "x" 2) = "x_eq_2");
  check "lit: ne is a negated direct literal" (Lit.to_string (Lit.ne "x" 2) = "~x_eq_2");
  check "lit: double negation"
    (Lit.to_string (Lit.negate (Lit.negate (Lit.ge "x" 3))) = "x_ge_3");
  check "lit: identifiers are sanitised for OPB"
    (Lit.to_string (Lit.ge "X_INTRODUCED_1_" 1) = "X_INTRODUCED_1__ge_1");
  (* An array element's FlatZinc name is not an OPB name; the rewrite is recorded. *)
  check_eq "lit: array subscripts are sanitised" ~expected:"a_1__ge_0"
    ~got:(Lit.to_string (Lit.ge "a[1]" 0));
  check "lit: sanitise is detected" (Lit.is_renamed "a[1]");
  check "lit: plain identifiers are not renamed" (not (Lit.is_renamed "x"));
  (* A var bool is the order encoding on [0,1]; no third naming scheme. *)
  check_eq "lit: bool true" ~expected:"b_ge_1" ~got:(Lit.to_string (Lit.bool_true "b"));
  check_eq "lit: bool false" ~expected:"~b_ge_1" ~got:(Lit.to_string (Lit.bool_false "b"));
  check "lit: var_name of a pbvar" (Lit.var_name (Lit.Ge ("q", 7)) = "q_ge_7");
  check "lit: owner and value"
    (Lit.owner (Lit.Eq ("q", 7)) = "q" && Lit.value (Lit.Eq ("q", 7)) = 7);
  check "lit: order and direct are distinguishable"
    (Lit.is_order (Lit.Ge ("q", 1)) && Lit.is_direct (Lit.Eq ("q", 1)));
  check "lit: equality"
    (Lit.equal (Lit.ge "x" 1) (Lit.ge "x" 1)
    && not (Lit.equal (Lit.ge "x" 1) (Lit.le "x" 0)));
  check "lit: ge and eq families do not collide"
    (Lit.to_string (Lit.ge "x" 1) <> Lit.to_string (Lit.eq "x" 1))

(* ------------------------------------------------------------------ *)
(* Opb                                                                 *)
(* ------------------------------------------------------------------ *)

let test_opb () =
  let c = Opb.ge [ (1, Lit.ge "x" 1); (-2, Lit.le "y" 3) ] 1 in
  check_eq "opb: renders a constraint" ~expected:"+1 x_ge_1 -2 ~y_ge_4 >= 1 ;"
    ~got:(Opb.constr_to_string c);
  check_eq "opb: a clause is a >= 1 constraint" ~expected:"+1 x_ge_1 +1 ~y_ge_4 >= 1 ;"
    ~got:(Opb.constr_to_string (Opb.clause [ Lit.ge "x" 1; Lit.le "y" 3 ]));
  check_eq "opb: <= is stored negated" ~expected:"-1 x_ge_1 -1 x_ge_2 >= -1 ;"
    ~got:(Opb.constr_to_string (Opb.le [ (1, Lit.ge "x" 1); (1, Lit.ge "x" 2) ] 1));
  check_eq "opb: equality renders with =" ~expected:"+1 x_ge_1 = 1 ;"
    ~got:(Opb.constr_to_string (Opb.eq [ (1, Lit.ge "x" 1) ] 1));
  (* An equality is two constraints to the checker, and the header must say so or
     every id in the proof is off by one. *)
  check "opb: an equality counts twice in the header"
    (Opb.n_checker_constraints [ Opb.eq [ (1, Lit.ge "x" 1) ] 1 ] = 2);
  check "opb: an inequality counts once"
    (Opb.n_checker_constraints [ Opb.ge [ (1, Lit.ge "x" 1) ] 1 ] = 1);
  (* normalise: 1 x + 1 ~x >= 1 is the tautology 0 >= 0. *)
  check_eq "opb: normalise cancels a literal against its negation" ~expected:">= 0 ;"
    ~got:
      (Opb.constr_to_string
         (Opb.normalise (Opb.ge [ (1, Lit.ge "x" 1); (1, Lit.negate (Lit.ge "x" 1)) ] 1)));
  check_eq "opb: normalise merges repeated terms" ~expected:"+3 x_ge_1 >= 2 ;"
    ~got:
      (Opb.constr_to_string
         (Opb.normalise (Opb.ge [ (1, Lit.ge "x" 1); (2, Lit.ge "x" 1) ] 2)));
  check_eq "opb: normalise moves negative coefficients right"
    ~expected:"+2 ~x_ge_1 >= 1 ;"
    ~got:(Opb.constr_to_string (Opb.normalise (Opb.ge [ (-2, Lit.ge "x" 1) ] (-1))));
  check_eq "opb: objective line" ~expected:"min: +1 x_ge_1 +1 x_ge_2 ;"
    ~got:
      (Opb.objective_to_string (Opb.objective [ (1, Lit.ge "x" 1); (1, Lit.ge "x" 2) ]))

(* ------------------------------------------------------------------ *)
(* Writer                                                              *)
(* ------------------------------------------------------------------ *)

(* Run [f] against a fresh writer and hand back everything it wrote. *)
let emitted ?(comments = true) ?(audit = true) ?(format = Writer.V2_0) f =
  let path = Filename.temp_file "baguette_proof" ".pbp" in
  let oc = open_out path in
  let w = Writer.create ~comments ~audit ~format oc in
  let r = try Ok (f w) with e -> Error e in
  (try close_out oc with _ -> ());
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  Sys.remove path;
  (s, r)

let text ?format f = fst (emitted ?format f)

let test_pol () =
  check_eq "pol: a single id" ~expected:"3" ~got:(Pol.to_string (Pol.id 3));
  check_eq "pol: reverse Polish addition" ~expected:"3 4 +"
    ~got:(Pol.to_string Pol.(add (id 3) (id 4)));
  (* The example in docs/PROOF-FORMAT.md section 2. *)
  check_eq "pol: 'constraint 3 plus 4, divided by 2'" ~expected:"3 4 + 2 d"
    ~got:(Pol.to_string Pol.(div (add (id 3) (id 4)) 2));
  check_eq "pol: sum is left-associated" ~expected:"1 2 + 3 + 4 +"
    ~got:(Pol.to_string Pol.(sum [ id 1; id 2; id 3; id 4 ]));
  check_eq "pol: multiplying by one is a no-op" ~expected:"5"
    ~got:(Pol.to_string Pol.(mul (id 5) 1));
  check_eq "pol: literal axioms are written as literals" ~expected:"5 ~x_ge_2 +"
    ~got:(Pol.to_string Pol.(add (id 5) (axiom (Lit.le "x" 1))));
  check_eq "pol: saturation" ~expected:"5 s" ~got:(Pol.to_string Pol.(saturate (id 5)));
  (* VeriPB's weakening ignores the sign, so it takes the variable. *)
  check_eq "pol: weakening names a variable, not a literal" ~expected:"5 y_ge_1 w"
    ~got:(Pol.to_string Pol.(weaken (id 5) (Lit.Ge ("y", 1))));
  check_eq "pol: linear combination" ~expected:"1 2 * 2 3 * +"
    ~got:(Pol.to_string (Pol.lin_comb [ (2, 1); (3, 2) ]));
  raises "pol: division by zero is rejected" (fun () -> Pol.div (Pol.id 1) 0);
  raises "pol: an empty sum is rejected" (fun () -> Pol.sum [])

let test_writer_rules () =
  let s =
    text (fun w ->
        Writer.header w ~n_model_constraints:4;
        let a = Writer.pol w ~origin:"t" Pol.(sum [ id 1; id 2 ]) in
        let b = Writer.rup_clause w ~origin:"t" [ Lit.ge "x" 1; Lit.ne "y" 2 ] in
        let c =
          Writer.red w ~origin:"t"
            ~witness:[ (Lit.Eq ("y", 2), Writer.Zero) ]
            (Opb.clause [ Lit.ne "y" 2; Lit.ge "y" 2 ])
        in
        Writer.delete_many w [ a; b; c ];
        Writer.conclusion w (Writer.Unsat None))
  in
  let expected =
    String.concat "\n"
      [
        "pseudo-Boolean proof version 2.0";
        "f 4";
        "pol 1 2 +";
        "rup +1 x_ge_1 +1 ~y_eq_2 >= 1 ;";
        "red +1 ~y_eq_2 +1 y_ge_2 >= 1 ; y_eq_2 -> 0";
        "del id 5 6 7";
        "output NONE";
        "conclusion UNSAT";
        "end pseudo-Boolean proof";
        "";
      ]
  in
  check_eq "writer: rule vocabulary and id sequence" ~expected ~got:s

let test_writer_ids () =
  let ids = ref [] in
  let _ =
    text (fun w ->
        Writer.header w ~n_model_constraints:10;
        ids := [ Writer.pol w ~origin:"t" (Pol.id 1) ];
        ids := !ids @ [ Writer.rup_clause w ~origin:"t" [ Lit.ge "x" 1 ] ];
        ids := !ids @ [ Writer.solution_excluding w ~origin:"t" [ Lit.ge "x" 1 ] ];
        Writer.delete_many w !ids;
        Writer.conclusion w (Writer.Unsat None))
  in
  (* The f rule takes ids 1..10, so derived constraints start at 11. *)
  check "writer: derived ids follow the model constraints" (!ids = [ 11; 12; 13 ])

let test_writer_levels () =
  let s =
    text (fun w ->
        Writer.header w ~n_model_constraints:1;
        Writer.set_level w 2;
        let _ = Writer.pol w ~origin:"reason at level 2" (Pol.id 1) in
        let _ = Writer.pol w ~origin:"another" (Pol.id 1) in
        (* A backtrack is a wipe, not a truncation of the file (invariant I-X4). *)
        Writer.wipe_level w 2;
        Writer.conclusion w (Writer.Unsat None))
  in
  let lines = String.split_on_char '\n' s in
  let has l = List.exists (String.equal l) lines in
  check "writer: a decision level is set with the level rule" (has "# 2");
  check "writer: a backtrack is a level wipe" (has "w 2");
  check "writer: the proof is never truncated"
    (has "pseudo-Boolean proof version 2.0" && has "end pseudo-Boolean proof")

let test_audit () =
  (* An id that is handed out and never deleted is an I-X2 violation. *)
  let _, r =
    emitted ~audit:true (fun w ->
        Writer.header w ~n_model_constraints:1;
        let _leaked = Writer.pol w ~origin:"leaked reason" (Pol.id 1) in
        Writer.conclusion w (Writer.Unsat None))
  in
  check "audit: an undeleted id fails the audit"
    (match r with Error (Writer.Audit_failed _) -> true | _ -> false);
  (* The same proof with the deletion in place passes. *)
  let _, r =
    emitted ~audit:true (fun w ->
        Writer.header w ~n_model_constraints:1;
        let id = Writer.pol w ~origin:"reason" (Pol.id 1) in
        Writer.delete w id;
        Writer.conclusion w (Writer.Unsat None))
  in
  check "audit: a deleted id passes the audit" (match r with Ok () -> true | _ -> false);
  (* Model constraints are fixed by the .opb; nobody received them, so nobody owes
     their deletion. *)
  let _, r =
    emitted ~audit:true (fun w ->
        Writer.header w ~n_model_constraints:9;
        Writer.conclusion w (Writer.Unsat None))
  in
  check "audit: model constraints are not a deletion obligation"
    (match r with Ok () -> true | _ -> false);
  (* A contradiction consumed by the conclusion is discharged by it. *)
  let _, r =
    emitted ~audit:true (fun w ->
        Writer.header w ~n_model_constraints:1;
        let id = Writer.pol w ~origin:"contradiction" (Pol.id 1) in
        Writer.conclusion w (Writer.Unsat (Some id)))
  in
  check "audit: the concluding contradiction is discharged"
    (match r with Ok () -> true | _ -> false);
  (* Wiping a level retires every id created at or above it. *)
  let _, r =
    emitted ~audit:true (fun w ->
        Writer.header w ~n_model_constraints:1;
        Writer.set_level w 3;
        let _ = Writer.pol w ~origin:"a" (Pol.id 1) in
        let _ = Writer.pol w ~origin:"b" (Pol.id 1) in
        Writer.wipe_level w 3;
        Writer.conclusion w (Writer.Unsat None))
  in
  check "audit: a level wipe discharges its ids"
    (match r with Ok () -> true | _ -> false);
  (* And audit off never raises. *)
  let _, r =
    emitted ~audit:false (fun w ->
        Writer.header w ~n_model_constraints:1;
        let _leaked = Writer.pol w ~origin:"leaked" (Pol.id 1) in
        Writer.conclusion w (Writer.Unsat None))
  in
  check "audit: disabled audit does not raise" (match r with Ok () -> true | _ -> false)

(* ------------------------------------------------------------------ *)
(* Encoding                                                            *)
(* ------------------------------------------------------------------ *)

let opb_text e =
  let path = Filename.temp_file "baguette_model" ".opb" in
  let oc = open_out path in
  Encoding.write_opb e oc;
  close_out oc;
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  Sys.remove path;
  s

let test_order_encoding () =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:3;
  (* docs/PROOF-FORMAT.md section 3: one consistency clause per lo < v < hi. *)
  check "encoding: order encoding emits hi-lo-1 consistency clauses"
    (Encoding.n_constraints e = 2);
  check_eq "encoding: the order-consistency clauses"
    ~expected:
      "* #variable= 3 #constraint= 2\n\
       +1 ~x_ge_2 +1 x_ge_1 >= 1 ;\n\
       +1 ~x_ge_3 +1 x_ge_2 >= 1 ;\n"
    ~got:(opb_text e);
  (* x >= lo is the constant true and x >= hi+1 the constant false: no variables. *)
  check "encoding: x >= lo holds vacuously" (Encoding.ge e "x" 0 = Encoding.Holds);
  check "encoding: x >= hi+1 is impossible" (Encoding.ge e "x" 4 = Encoding.Fails);
  check "encoding: x >= 2 is a literal"
    (Encoding.ge e "x" 2 = Encoding.Cond (Lit.ge "x" 2));
  check "encoding: x <= hi holds vacuously" (Encoding.le e "x" 3 = Encoding.Holds);
  check "encoding: x <= lo-1 is impossible" (Encoding.le e "x" (-1) = Encoding.Fails);
  check "encoding: x <= 1 is a negated order literal"
    (Encoding.le e "x" 1 = Encoding.Cond (Lit.le "x" 1));
  check "encoding: consistency ids are recoverable"
    (Encoding.consistency_id e "x" 1 = Some 1 && Encoding.consistency_id e "x" 2 = Some 2);
  check "encoding: no consistency clause at the bounds"
    (Encoding.consistency_id e "x" 3 = None);
  (* A singleton domain needs no consistency clause at all. *)
  let e2 = Encoding.create () in
  Encoding.declare_int e2 "k" ~lo:5 ~hi:5;
  check "encoding: a singleton domain has no order variables"
    (Encoding.n_constraints e2 = 0);
  (* A var bool is [0,1]: one Boolean, no consistency clause. *)
  let e3 = Encoding.create () in
  Encoding.declare_bool e3 "b";
  check "encoding: a bool needs no consistency clause" (Encoding.n_constraints e3 = 0);
  check "encoding: a bool's true literal"
    (Encoding.ge e3 "b" 1 = Encoding.Cond (Lit.bool_true "b"));
  raises "encoding: an unknown variable is an error" (fun () -> Encoding.ge e "zz" 1);
  raises "encoding: an empty domain is rejected" (fun () ->
      Encoding.declare_int e "bad" ~lo:3 ~hi:2);
  raises "encoding: an equality may not go in the .opb" (fun () ->
      Encoding.add_constraint e (Opb.eq [ (1, Lit.ge "x" 1) ] 1))

let test_ids_and_equality () =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:2 (* 1 consistency clause: id 1 *);
  let c = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "x" 1) ] 1) in
  check "encoding: a model constraint follows the consistency clauses" (c = 2);
  let a, b = Encoding.add_equality e [ (1, Lit.ge "x" 1) ] 1 in
  check "encoding: an equality becomes two ids" (a = 3 && b = 4);
  check "encoding: and the .opb has four lines" (Encoding.n_constraints e = 4);
  check "encoding: the header agrees with the id count"
    (Opb.n_checker_constraints (Encoding.constraints e) = 4)

let test_direct_encoding () =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:2;
  check "encoding: the direct encoding is not there until asked"
    (not (Encoding.has_direct e "x"));
  raises "encoding: x = v without the direct encoding is an error" (fun () ->
      Encoding.eq e "x" 1);
  let s =
    text (fun w ->
        Writer.header w ~n_model_constraints:1;
        ignore (Encoding.ensure_direct e w "x");
        let alo = Encoding.derive_at_least_one e w "x" in
        let amo = Encoding.derive_at_most_one e w "x" 0 2 in
        Writer.delete_many w [ alo; amo ];
        Encoding.retire_direct e w "x";
        Writer.conclusion w (Writer.Unsat None))
  in
  check "encoding: the direct encoding is now present"
    (Encoding.has_direct e "x" = false (* retired again *));
  let lines = String.split_on_char '\n' s in
  let has l = List.exists (String.equal l) lines in
  (* The channelling of PROOF-FORMAT section 3, with the constant halves dropped:
     x_ge_0 is true and x_ge_3 is false, so they never appear. *)
  (* x >= lo is the constant true, so x_eq_lo's "lower" half is not emitted. *)
  check "encoding: x_eq_lo has no x_ge_lo half"
    (has "red +1 ~x_eq_0 +1 ~x_ge_1 >= 1 ; x_eq_0 -> 0"
    && has "red +1 x_eq_0 +1 x_ge_1 >= 1 ; x_eq_0 -> 1"
    && not (has "red +1 ~x_eq_0 +1 x_ge_0 >= 1 ; x_eq_0 -> 0"));
  check "encoding: the middle value gets both halves"
    (has "red +1 ~x_eq_1 +1 x_ge_1 >= 1 ; x_eq_1 -> 0"
    && has "red +1 ~x_eq_1 +1 ~x_ge_2 >= 1 ; x_eq_1 -> 0"
    && has "red +1 x_eq_1 +1 ~x_ge_1 +1 x_ge_2 >= 1 ; x_eq_1 -> 1");
  check "encoding: x_eq_hi has no x_ge_(hi+1) half"
    (has "red +1 ~x_eq_2 +1 x_ge_2 >= 1 ; x_eq_2 -> 0"
    && has "red +1 x_eq_2 +1 ~x_ge_2 >= 1 ; x_eq_2 -> 1");
  (* Exactly-one is derived from the channelling, never assumed. *)
  check "encoding: at-least-one is a pol over the channelling ids" (has "pol 3 6 + 8 +");
  check "encoding: at-most-one is a pol over channelling plus the order chain"
    (has "pol 2 7 + 1 +");
  check "encoding: the definitions are retired" (has "del id 2 3 4 5 6 7 8")

let test_assignment_lits () =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:3;
  let render l = String.concat " " (List.map Lit.to_string l) in
  check_eq "encoding: an assignment fixes the whole order family"
    ~expected:"x_ge_1 x_ge_2 ~x_ge_3"
    ~got:(render (Encoding.assignment_lits e [ ("x", 2) ]));
  check_eq "encoding: at the lower bound every order literal is false"
    ~expected:"~x_ge_1 ~x_ge_2 ~x_ge_3"
    ~got:(render (Encoding.assignment_lits e [ ("x", 0) ]));
  raises "encoding: a value outside the domain is rejected" (fun () ->
      Encoding.assignment_lits e [ ("x", 9) ])

let test_renaming_comments () =
  let e = Encoding.create () in
  Encoding.declare_int e "a[1]" ~lo:0 ~hi:2;
  let s = opb_text e in
  check "encoding: the sanitisation mapping is dumped as a comment"
    (List.exists (String.equal "* name a[1] -> a_1_") (String.split_on_char '\n' s))

(* Which checker to run: lib/proof/checker.ml, shared with scripts/checker.sh.
   Every test module open-coded this search, and every copy looked at
   ~/.local/bin/veripb first -- so a project-wide choice of checker lived in nine
   places and silently meant the Python 2.2.2 (M1-T18). [None] is a FAILURE at every
   call site below, never a skip. *)
let veripb_path () = Baguette_proof.Checker.find ()

(* ------------------------------------------------------------------ *)
(* M1-T7c: order-encoding expansion of sum a_i x_i <= rhs               *)
(* ------------------------------------------------------------------ *)

(* Evaluate a normalised Opb.constr under a concrete integer assignment
   (name -> value), by reading off each order literal's truth value directly
   from the assignment rather than from any Encoding state. This is the
   independent check: it knows nothing about how [expand_int_lin_le] built
   the row, only what an order literal *means* (x_ge_v holds iff value >= v),
   so it cannot be fooled by a sign error that cancels itself inside the same
   code path. *)
let lit_truth assign (l : Lit.t) =
  let v = l.Lit.v in
  let base =
    match v with
    | Lit.Ge (x, k) -> List.assoc x assign >= k
    | Lit.Eq (x, k) -> List.assoc x assign = k
  in
  if l.Lit.positive then base else not base

let eval_row assign (c : Opb.constr) =
  let lhs =
    List.fold_left
      (fun acc (a, l) -> acc + (a * if lit_truth assign l then 1 else 0))
      0 (Opb.terms c)
  in
  match Opb.relation c with Opb.Ge -> lhs >= Opb.rhs c | Opb.Eq -> lhs = Opb.rhs c

(* All assignments of a list of (name, lo, hi) domains, as (name, value) lists. *)
let rec all_assignments = function
  | [] -> [ [] ]
  | (x, lo, hi) :: rest ->
      let tails = all_assignments rest in
      List.concat_map
        (fun v -> List.map (fun tail -> (x, v) :: tail) tails)
        (List.init (hi - lo + 1) (fun i -> lo + i))

(* The arithmetic check: for every point of the (small) domain, the expanded
   PB row must agree with the integer constraint it was built from. This is
   what would catch a sign or constant error -- one that a single worked
   example could easily miss, but a mismatched point here cannot. *)
let check_soundness name ~domains ~terms ~rhs =
  let e = Encoding.create () in
  List.iter (fun (x, lo, hi) -> Encoding.declare_int e x ~lo ~hi) domains;
  let row = Encoding.expand_int_lin_le e terms rhs in
  let bad =
    List.find_opt
      (fun assign ->
        let int_side =
          List.fold_left (fun acc (a, x) -> acc + (a * List.assoc x assign)) 0 terms
          <= rhs
        in
        eval_row assign row <> int_side)
      (all_assignments domains)
  in
  check name (bad = None)

let test_int_lin_le_soundness () =
  check_soundness "int_lin_le soundness: 2x + 3y <= 10, x,y in [0,3]"
    ~domains:[ ("x", 0, 3); ("y", 0, 3) ]
    ~terms:[ (2, "x"); (3, "y") ]
    ~rhs:10;
  check_soundness "int_lin_le soundness: negative coefficient, x - y <= 1"
    ~domains:[ ("x", 0, 2); ("y", 0, 2) ]
    ~terms:[ (1, "x"); (-1, "y") ]
    ~rhs:1;
  check_soundness "int_lin_le soundness: both coefficients negative"
    ~domains:[ ("x", 0, 2); ("y", 0, 2) ]
    ~terms:[ (-2, "x"); (-1, "y") ]
    ~rhs:(-1);
  check_soundness "int_lin_le soundness: a zero coefficient contributes nothing"
    ~domains:[ ("x", 0, 5); ("y", 0, 3) ]
    ~terms:[ (0, "x"); (1, "y") ]
    ~rhs:2;
  check_soundness "int_lin_le soundness: a singleton-domain variable is a constant"
    ~domains:[ ("x", 0, 3); ("k", 4, 4) ]
    ~terms:[ (1, "x"); (1, "k") ]
    ~rhs:5;
  check_soundness "int_lin_le soundness: three variables, mixed signs"
    ~domains:[ ("x", -1, 2); ("y", 0, 2); ("z", 1, 3) ]
    ~terms:[ (2, "x"); (-3, "y"); (1, "z") ]
    ~rhs:2

(* Worked examples, checked by eye against the substitution in the module
   header of [Encoding], with the exact rendered .opb line pinned. *)
let test_int_lin_le_worked_examples () =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:3;
  Encoding.declare_int e "y" ~lo:0 ~hi:3;
  (* 2x + 3y <= 10 : the example from the task report. *)
  check_eq "int_lin_le: 2x + 3y <= 10 over [0,3]x[0,3]"
    ~expected:"+2 ~x_ge_1 +2 ~x_ge_2 +2 ~x_ge_3 +3 ~y_ge_1 +3 ~y_ge_2 +3 ~y_ge_3 >= 5 ;"
    ~got:(Opb.constr_to_string (Encoding.expand_int_lin_le e [ (2, "x"); (3, "y") ] 10));
  let e2 = Encoding.create () in
  Encoding.declare_int e2 "x" ~lo:0 ~hi:2;
  Encoding.declare_int e2 "y" ~lo:0 ~hi:2;
  (* x - y <= 1 : a negative coefficient. *)
  check_eq "int_lin_le: negative coefficient, x - y <= 1"
    ~expected:"+1 ~x_ge_1 +1 ~x_ge_2 +1 y_ge_1 +1 y_ge_2 >= 1 ;"
    ~got:(Opb.constr_to_string (Encoding.expand_int_lin_le e2 [ (1, "x"); (-1, "y") ] 1));
  let e3 = Encoding.create () in
  Encoding.declare_int e3 "x" ~lo:0 ~hi:3;
  Encoding.declare_int e3 "k" ~lo:4 ~hi:4;
  (* x + k <= 5, k fixed at 4: k contributes only to the constant, no k_ge_* literal. *)
  check_eq "int_lin_le: a singleton-domain variable is constant-only"
    ~expected:"+1 ~x_ge_1 +1 ~x_ge_2 +1 ~x_ge_3 >= 2 ;"
    ~got:(Opb.constr_to_string (Encoding.expand_int_lin_le e3 [ (1, "x"); (1, "k") ] 5));
  (* A zero coefficient never even looks up the variable's domain, so it works
     even for a variable this Encoding never declared. *)
  let e4 = Encoding.create () in
  Encoding.declare_int e4 "y" ~lo:0 ~hi:3;
  check_eq "int_lin_le: a zero coefficient contributes no term and needs no domain"
    ~expected:"+1 ~y_ge_1 +1 ~y_ge_2 +1 ~y_ge_3 >= 1 ;"
    ~got:
      (Opb.constr_to_string
         (Encoding.expand_int_lin_le e4 [ (0, "never_declared"); (1, "y") ] 2))

let test_int_lin_le_add () =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:2 (* 1 consistency clause: id 1 *);
  let cid = Encoding.add_int_lin_le e [ (1, "x") ] 1 in
  check "encoding: add_int_lin_le follows the consistency clauses" (cid = 2);
  check_eq "encoding: add_int_lin_le posts the expanded row"
    ~expected:"+1 ~x_ge_1 +1 ~x_ge_2 >= 1 ;"
    ~got:(Opb.constr_to_string (List.nth (Encoding.constraints e) 1));
  check "encoding: header count agrees with the ids assigned"
    (Opb.n_checker_constraints (Encoding.constraints e) = Encoding.n_constraints e)

(* End-to-end: post a real int_lin_le row through add_int_lin_le, derive a
   contradiction from it with a real veripb, and check I-X1 and I-X5 together.

   Model: x, y in [0,2],  x + y <= 1  (posted via add_int_lin_le),  x >= 2
   (posted directly). Unsatisfiable: x >= 2 forces y <= -1, which is outside
   y's domain.

   Soundness of the derivation below rests on the order-encoding consistency
   clauses that [declare_int] already emits (x_ge_2 -> x_ge_1): without them,
   x >= 2 would not license deriving x >= 1, which is the step the row needs
   to be summed against. That is the sense in which those clauses are what
   makes an int_lin_le row usable at all, not just the row's own arithmetic. *)
let build_int_lin_le_unsat dir =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:2 (* consistency id 1: x_ge_2 -> x_ge_1 *);
  Encoding.declare_int e "y" ~lo:0 ~hi:2 (* consistency id 2: y_ge_2 -> y_ge_1 *);
  let c_sum = Encoding.add_int_lin_le e [ (1, "x"); (1, "y") ] 1 (* id 3 *) in
  let c_x2 = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "x" 2) ] 1) (* id 4 *) in
  let opb = Filename.concat dir "int_lin_le.opb" in
  let pbp = Filename.concat dir "int_lin_le.pbp" in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "x + y <= 1 (int_lin_le); x >= 2" ] e oc;
  close_out oc;
  let f_count = Opb.n_checker_constraints (Encoding.constraints e) in
  let oc = open_out pbp in
  let w = Writer.create ~comments:true ~audit:true oc in
  Encoding.start_proof e w;
  let cons_x1 = Option.get (Encoding.consistency_id e "x" 1) in
  (* x >= 2 and x_ge_2 -> x_ge_1 give x >= 1. *)
  let x_ge_1 =
    Writer.pol w ~origin:"x >= 2 gives x >= 1" Pol.(sum [ id c_x2; id cons_x1 ])
  in
  (* The int_lin_le row, plus x >= 1 and x >= 2, forces
     ~y_ge_1 + ~y_ge_2 >= 3 -- impossible since that sum is at most 2. *)
  let contra =
    Writer.pol w ~origin:"the row, x >= 1 and x >= 2 overdetermine y"
      Pol.(sum [ id c_sum; id x_ge_1; id c_x2 ])
  in
  Writer.delete_many w [ x_ge_1 ];
  Writer.conclusion w (Writer.Unsat (Some contra));
  close_out oc;
  (opb, pbp, f_count)

let test_int_lin_le_veripb () =
  match veripb_path () with
  | None ->
      incr failures;
      print_endline
        "FAIL int_lin_le: veripb not found -- invariant I-X1 was NOT checked for the \
         int_lin_le row."
  | Some veripb -> (
      let dir = Filename.temp_file "baguette_veripb_lin" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      let opb, pbp, f_count = build_int_lin_le_unsat dir in
      (* I-X5: the .opb's constraint count and the f line must agree. *)
      let opb_text =
        let ic = open_in_bin opb in
        let s = really_input_string ic (in_channel_length ic) in
        close_in ic;
        s
      in
      check "int_lin_le: the .opb header count matches what we computed for f"
        (let prefix = Printf.sprintf "* #variable= " in
         String.length opb_text > String.length prefix
         &&
         let expected_suffix = Printf.sprintf "#constraint= %d\n" f_count in
         let has_substr hay needle =
           let hl = String.length hay and nl = String.length needle in
           let rec go i = i + nl <= hl && (String.sub hay i nl = needle || go (i + 1)) in
           go 0
         in
         has_substr opb_text expected_suffix);
      let pbp_text =
        let ic = open_in_bin pbp in
        let s = really_input_string ic (in_channel_length ic) in
        close_in ic;
        s
      in
      check "int_lin_le: the proof's f line matches the computed count"
        (List.exists
           (String.equal (Printf.sprintf "f %d" f_count))
           (String.split_on_char '\n' pbp_text));
      let log = Filename.concat dir "log" in
      let rc =
        Sys.command
          (Printf.sprintf "%s %s %s > %s 2>&1" (Filename.quote veripb)
             (Filename.quote opb) (Filename.quote pbp) (Filename.quote log))
      in
      let out =
        let ic = open_in_bin log in
        let s = really_input_string ic (in_channel_length ic) in
        close_in ic;
        s
      in
      if rc = 0 then
        Printf.printf
          "ok   int_lin_le: veripb accepts a proof over the expanded row (I-X1)\n"
      else (
        incr failures;
        Printf.printf "FAIL int_lin_le: veripb rejected the proof (I-X1)\n%s\n" out;
        Printf.printf "  model: %s\n  proof: %s\n" opb pbp);
      List.iter (fun f -> try Sys.remove f with _ -> ()) [ opb; pbp; log ];
      try Sys.rmdir dir with _ -> ())

(* ------------------------------------------------------------------ *)
(* The one that matters: I-X1                                          *)
(* ------------------------------------------------------------------ *)

(* The model:  x, y in [0,3],  x >= 2,  x + y <= 2,  y >= 1.  Unsatisfiable.
   The proof also introduces y's direct encoding, derives exactly-one over it, and
   retires it, so every piece of the encoding contract is exercised. *)
let build_unsat ?(format = Writer.V2_0) dir =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:3;
  Encoding.declare_int e "y" ~lo:0 ~hi:3;
  let order x = List.init 3 (fun i -> (1, Lit.ge x (i + 1))) in
  let c_x2 = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "x" 2) ] 1) in
  let c_sum = Encoding.add_constraint e (Opb.le (order "x" @ order "y") 2) in
  let c_y1 = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "y" 1) ] 1) in
  let opb = Filename.concat dir "unsat.opb" in
  let pbp = Filename.concat dir "unsat.pbp" in
  let oc = open_out opb in
  (* Labels in the .opb must match the writer's format or every citation in the proof
     is a parse error; [write_opb_for] is the form that cannot get that wrong, and it
     needs the writer, so build it first and write the proof into it below. *)
  let pbp_oc = open_out pbp in
  let w = Writer.create ~comments:true ~audit:true ~format pbp_oc in
  Encoding.write_opb_for ~comments:[ "x >= 2; x + y <= 2; y >= 1" ] e w oc;
  close_out oc;
  let oc = pbp_oc in
  Encoding.start_proof e w;
  ignore (Encoding.ensure_direct e w "y");
  let alo = Encoding.derive_at_least_one e w "y" in
  let amo = Encoding.derive_at_most_one e w "y" 0 3 in
  (* A reason logged at a decision level, then wiped by the backtrack. *)
  Writer.set_level w 1;
  let _ = Writer.rup_clause w ~origin:"a pruning at level 1" [ Lit.ge "x" 1 ] in
  Writer.wipe_level w 1;
  Writer.set_level w 0;
  Writer.delete_many w [ alo; amo ];
  Encoding.retire_direct e w "y";
  let cons_x1 = Option.get (Encoding.consistency_id e "x" 1) in
  let x_ge_1 =
    Writer.pol w ~origin:"x >= 2 gives x >= 1" Pol.(sum [ id c_x2; id cons_x1 ])
  in
  let y_le_0 =
    Writer.pol w ~origin:"x >= 2 and x + y <= 2 give y <= 0"
      Pol.(sum [ id c_sum; id x_ge_1; id c_x2 ])
  in
  let contra =
    Writer.pol w ~origin:"y <= 0 contradicts y >= 1" Pol.(sum [ id y_le_0; id c_y1 ])
  in
  Writer.delete_many w [ x_ge_1; y_le_0 ];
  Writer.conclusion w (Writer.Unsat (Some contra));
  close_out oc;
  (opb, pbp)

let test_veripb_accepts () =
  match veripb_path () with
  | None ->
      incr failures;
      print_endline
        "FAIL proof: veripb not found — invariant I-X1 was NOT checked. Install it (see \
         docs/PROOF-FORMAT.md) and re-run; do not treat this as a pass."
  | Some veripb -> (
      let dir = Filename.temp_file "baguette_veripb" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      let opb, pbp = build_unsat dir in
      let log = Filename.concat dir "log" in
      let rc =
        Sys.command
          (Printf.sprintf "%s %s %s > %s 2>&1" (Filename.quote veripb)
             (Filename.quote opb) (Filename.quote pbp) (Filename.quote log))
      in
      let out =
        let ic = open_in_bin log in
        let s = really_input_string ic (in_channel_length ic) in
        close_in ic;
        s
      in
      if rc = 0 then Printf.printf "ok   proof: veripb accepts the emitted proof (I-X1)\n"
      else (
        incr failures;
        Printf.printf "FAIL proof: veripb rejected the emitted proof (I-X1)\n%s\n" out;
        Printf.printf "  model: %s\n  proof: %s\n" opb pbp);
      List.iter (fun f -> try Sys.remove f with _ -> ()) [ opb; pbp; log ];
      try Sys.rmdir dir with _ -> ())

(* ------------------------------------------------------------------ *)
(* M1-T19: VeriPB 3.0 emission                                         *)
(*                                                                     *)
(* Every claim in D-0023 about 3.0 syntax is made here by running the   *)
(* checker, not by reading a grammar. Three things have to hold and     *)
(* the third is the one that makes the other two mean anything:        *)
(*   1. the 3.0 checker ACCEPTS a 3.0 proof of an unsatisfiable model;  *)
(* 2. the 3.0 checker REJECTS a corrupted one -- without this, "3.0.2 *)
   (*      accepted it" says nothing at all (scripts/mutate_proof.sh's *)
(*      argument, applied to the format switch itself);                 *)
(*   3. the 2.2.2 checker REJECTS a 3.0 proof outright. That is not a   *)
(*      nice-to-have: it is why the switch cannot be made one consumer  *)
(*      at a time.                                                      *)
(* ------------------------------------------------------------------ *)

let read_whole path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

(* [Some true] accepted, [Some false] rejected, [None] no such checker here. *)
let run_checker ~checker ~opb ~pbp ~log =
  if not (Sys.file_exists checker || checker = "veripb") then None
  else
    Some
      (Sys.command
         (Printf.sprintf "%s %s %s > %s 2>&1" (Filename.quote checker)
            (Filename.quote opb) (Filename.quote pbp) (Filename.quote log))
      = 0)

let test_v3_emitted_text () =
  let s =
    text ~format:Writer.V3_0 (fun w ->
        Writer.header w ~n_model_constraints:4;
        let a = Writer.pol w ~origin:"t" Pol.(sum [ id 1; id 2 ]) in
        let b = Writer.rup_clause w ~origin:"t" [ Lit.ge "x" 1; Lit.ne "y" 2 ] in
        let c =
          Writer.red w ~origin:"t"
            ~witness:[ (Lit.Eq ("y", 2), Writer.Zero) ]
            (Opb.clause [ Lit.ne "y" 2; Lit.ge "y" 2 ])
        in
        Writer.delete_many w [ a; b; c ];
        Writer.conclusion w (Writer.Unsat None))
  in
  (* The same proof as [test_writer_rules], every line different. Pinned in full
     rather than grepped for, because the interesting failures here are a missing
     terminator and a witness on the wrong side of a separator -- both of which a
     substring check would sail past. *)
  let expected =
    String.concat "\n"
      [
        "pseudo-Boolean proof version 3.0";
        "f 4 ;";
        "@c5 pol @c1 @c2 + ;";
        "@c6 rup +1 x_ge_1 +1 ~y_eq_2 >= 1 ;";
        "@c7 red +1 ~y_eq_2 +1 y_ge_2 >= 1 : y_eq_2 -> 0 ;";
        "del id @c5 @c6 @c7 ;";
        "output NONE ;";
        "conclusion UNSAT ;";
        "end pseudo-Boolean proof ;";
        "";
      ]
  in
  check_eq "3.0: rule vocabulary, terminators, labels and the red witness separator"
    ~expected ~got:s

(* The level stack is gone in 3.0 (D-0024), so [wipe_level] has to reproduce `w l`
   from the writer's own tags. The case that separates "delete what was derived since
   the level was set" from the real semantics is a level RE-ENTERED after a spell at a
   lower one -- which is exactly what search does: `# 1`, `# 0`, prune at the root,
   `# 1`, prune under the decision, backtrack. The root prunings must survive. *)
let test_v3_levels () =
  let ids = ref [] in
  let s =
    text ~format:Writer.V3_0 (fun w ->
        Writer.header w ~n_model_constraints:1;
        Writer.set_level w 1;
        Writer.set_level w 0;
        let r1 = Writer.pol w ~origin:"root" (Pol.id 1) in
        let r2 = Writer.pol w ~origin:"root" (Pol.id 1) in
        Writer.set_level w 1;
        let b1 = Writer.pol w ~origin:"branch" (Pol.id 1) in
        let b2 = Writer.pol w ~origin:"branch" (Pol.id 1) in
        Writer.wipe_level w 1;
        ids := [ r1; r2; b1; b2 ];
        (* The root pair is NOT covered by the wipe and has to go explicitly, which is
           PROOF-FORMAT's "level-0 lines are covered by no `w`" -- unchanged by 3.0. *)
        Writer.delete_many w [ r1; r2 ];
        Writer.conclusion w (Writer.Unsat None))
  in
  let lines = String.split_on_char '\n' s in
  let has l = List.exists (String.equal l) lines in
  check "3.0: there is no set-level rule"
    (not (List.exists (fun l -> String.length l > 0 && l.[0] = '#') lines));
  check "3.0: there is no wipe rule"
    (not (List.exists (fun l -> l = "w 1 ;" || l = "w 1") lines));
  check "3.0: a level is still marked, as a comment, or the proof is unreadable"
    (has "% level 1" && has "% level 0");
  (* b1 and b2 are consecutive, so the backtrack is one line, not two. *)
  check "3.0: a backtrack retires exactly the branch ids, as one range"
    (has
       (Printf.sprintf "del range @c%d @c%d" (List.nth !ids 2) (List.nth !ids 3) ^ " ;"));
  check "3.0: the root prunings survive the backtrack and are retired separately"
    (has (Printf.sprintf "del id @c%d @c%d ;" (List.nth !ids 0) (List.nth !ids 1)))

let test_v3_veripb () =
  match veripb_path () with
  | None ->
      incr failures;
      print_endline ("FAIL 3.0: " ^ Baguette_proof.Checker.not_found_message)
  | Some veripb -> (
      let dir = Filename.temp_file "baguette_v3" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      let opb, pbp = build_unsat ~format:Writer.V3_0 dir in
      let log = Filename.concat dir "log" in
      check "3.0: the emitted proof declares version 3.0"
        (String.length (read_whole pbp) > 0
        && List.hd (String.split_on_char '\n' (read_whole pbp))
           = "pseudo-Boolean proof version 3.0");
      (* 1. accepted *)
      (match run_checker ~checker:veripb ~opb ~pbp ~log with
      | None -> ()
      | Some true ->
          Printf.printf
            "ok   3.0: veripb accepts a 3.0 proof over the full vocabulary -- red, \
             levels, pol, del, conclusion UNSAT (I-X1)\n"
      | Some false ->
          incr failures;
          Printf.printf
            "FAIL 3.0: veripb rejected the emitted 3.0 proof (I-X1)\n\
             %s\n\
            \  model: %s\n\
            \ proof: %s\n"
            (read_whole log) opb pbp);
      (* 2. and it rejects a corrupted one. The conclusion is made to cite @c1 -- a
         perfectly good model row, and not a contradiction. Without this control,
         "3.0.2 accepted it" is not evidence of anything: it is the argument
         scripts/mutate_proof.sh's header makes, turned on the format switch. *)
      let corrupted = Filename.concat dir "corrupt.pbp" in
      let starts_with p l =
        String.length l >= String.length p && String.sub l 0 (String.length p) = p
      in
      let oc = open_out corrupted in
      output_string oc
        (String.concat "\n"
           (List.map
              (fun l ->
                if starts_with "conclusion " l then "conclusion UNSAT : @c1 ;" else l)
              (String.split_on_char '\n' (read_whole pbp))));
      close_out oc;
      (match run_checker ~checker:veripb ~opb ~pbp:corrupted ~log with
      | None -> ()
      | Some false ->
          Printf.printf
            "ok   3.0: veripb rejects a 3.0 proof whose conclusion cites a \
             non-contradiction\n"
      | Some true ->
          incr failures;
          Printf.printf
            "FAIL 3.0: veripb ACCEPTED a 3.0 proof concluding UNSAT from a model row \
             that is not a contradiction. The acceptance above therefore says nothing.\n");
      (* 3. the one-way door: 2.2.2 cannot read a 3.0 proof at all. Only checked when
         that build is actually installed; it is a fact about the OTHER checker, so
         its absence is not a failure here. *)
      let py =
        Filename.concat (try Sys.getenv "HOME" with Not_found -> "") ".local/bin/veripb"
      in
      (match run_checker ~checker:py ~opb ~pbp ~log with
      | None ->
          Printf.printf
            "note 3.0: no 2.2.2 build here, so the one-way-door check did not run\n"
      | Some false ->
          Printf.printf
            "ok   3.0: veripb 2.2.2 rejects a 3.0 proof outright -- the switch is not \
             per-consumer (D-0023)\n"
      | Some true ->
          incr failures;
          Printf.printf
            "FAIL 3.0: veripb 2.2.2 ACCEPTED a 3.0 proof. D-0023 says it cannot; one of \
             them is wrong.\n");
      List.iter (fun f -> try Sys.remove f with _ -> ()) [ opb; pbp; corrupted; log ];
      try Sys.rmdir dir with _ -> ())

(* Say which checker every I-X1 check in the suite is talking to, and its version.
   "veripb accepted it" is only meaningful if you know which veripb, and until M1-T18
   the answer was whichever build happened to come first on PATH -- on the
   development machine, the Python 2.2.2, even though a 3.0.2 was installed. *)
let report_checker () =
  match Baguette_proof.Checker.find () with
  | None ->
      incr failures;
      Printf.printf "FAIL %s\n" Baguette_proof.Checker.not_found_message
  | Some p ->
      Printf.printf "* checker: %s\n" p;
      ignore
        (Sys.command
           (Printf.sprintf
              "%s --version 2>&1 | grep -i version | head -1 | sed 's/^/*   /'"
              (Filename.quote p)))

let () =
  report_checker ();
  test_lits ();
  test_opb ();
  test_pol ();
  test_writer_rules ();
  test_writer_ids ();
  test_writer_levels ();
  test_audit ();
  test_order_encoding ();
  test_ids_and_equality ();
  test_direct_encoding ();
  test_assignment_lits ();
  test_renaming_comments ();
  test_int_lin_le_soundness ();
  test_int_lin_le_worked_examples ();
  test_int_lin_le_add ();
  test_int_lin_le_veripb ();
  test_veripb_accepts ();
  test_v3_emitted_text ();
  test_v3_levels ();
  test_v3_veripb ();
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "\nproof unit tests passed"
