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

(* M1-T53: the inner heap guard; see mem_guard.ml for what it cannot see. *)
let () = Mem_guard.install ()

(* M7-T1. Sampled HERE, before any test can touch the refs, because every other
   assertion about the limits sets them explicitly and would therefore pass against a
   build whose SHIPPED DEFAULT was still the refusal. Measured that gap by putting the
   cap back: scripts/check_unlimited.sh reddened and not one unit assertion did. *)
let m7_shipped_defaults =
  ( !Encoding.order_width_limit,
    !Encoding.direct_values_limit,
    !Encoding.width_warn_threshold )

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
let emitted ?(comments = true) ?(audit = true) f =
  let path = Filename.temp_file "baguette_proof" ".pbp" in
  let oc = open_out path in
  let w = Writer.create ~comments ~audit oc in
  let r = try Ok (f w) with e -> Error e in
  (try close_out oc with _ -> ());
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  Sys.remove path;
  (s, r)

let text f = fst (emitted f)

(* The cutting-planes expression algebra, rendered the one way it is ever emitted:
   every constraint reference is its label (D-0023, D-0046). [Writer.cite] is what the
   writer passes here, and [Opb.label_of] is what [Writer.cite] is. *)
let render p = Pol.to_string_cited ~cite:Opb.label_of p

let test_pol () =
  check_eq "pol: a single id" ~expected:"@c3" ~got:(render (Pol.id 3));
  check_eq "pol: reverse Polish addition" ~expected:"@c3 @c4 +"
    ~got:(render Pol.(add (id 3) (id 4)));
  (* The example in docs/PROOF-FORMAT.md section 2a. *)
  check_eq "pol: 'constraint 3 plus 4, divided by 2'" ~expected:"@c3 @c4 + 2 d"
    ~got:(render Pol.(div (add (id 3) (id 4)) 2));
  check_eq "pol: sum is left-associated" ~expected:"@c1 @c2 + @c3 + @c4 +"
    ~got:(render Pol.(sum [ id 1; id 2; id 3; id 4 ]));
  check_eq "pol: multiplying by one is a no-op" ~expected:"@c5"
    ~got:(render Pol.(mul (id 5) 1));
  check_eq "pol: literal axioms are written as literals" ~expected:"@c5 ~x_ge_2 +"
    ~got:(render Pol.(add (id 5) (axiom (Lit.le "x" 1))));
  check_eq "pol: saturation" ~expected:"@c5 s" ~got:(render Pol.(saturate (id 5)));
  (* VeriPB's weakening ignores the sign, so it takes the variable. *)
  check_eq "pol: weakening names a variable, not a literal" ~expected:"@c5 y_ge_1 w"
    ~got:(render Pol.(weaken (id 5) (Lit.Ge ("y", 1))));
  check_eq "pol: linear combination" ~expected:"@c1 2 * @c2 3 * +"
    ~got:(render (Pol.lin_comb [ (2, 1); (3, 2) ]));
  raises "pol: division by zero is rejected" (fun () -> Pol.div (Pol.id 1) 0);
  raises "pol: an empty sum is rejected" (fun () -> Pol.sum [])

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

(* A backtrack is a wipe, not a truncation of the file (invariant I-X4). What that wipe
   is SPELLED as is [test_v3_levels]'s subject -- there is no set-level rule and no `w`
   (D-0024), so the writer reproduces them from its own tags -- and this is the part of
   the claim that is about the file rather than about the deletion set. *)
let test_writer_not_truncated () =
  let s =
    text (fun w ->
        Writer.header w ~n_model_constraints:1;
        Writer.set_level w 2;
        let _ = Writer.pol w ~origin:"reason at level 2" (Pol.id 1) in
        let _ = Writer.pol w ~origin:"another" (Pol.id 1) in
        Writer.wipe_level w 2;
        Writer.conclusion w (Writer.Unsat None))
  in
  let lines = String.split_on_char '\n' s in
  let has l = List.exists (String.equal l) lines in
  check "writer: a decision level is marked" (has "% level 2");
  check "writer: the proof is never truncated"
    (has "pseudo-Boolean proof version 3.0" && has "end pseudo-Boolean proof ;")

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
  (* Every model row is named in the .opb so the proof can cite it by label rather than
     by position (D-0023); labelling is unconditional (D-0046). *)
  let lbl i = Printf.sprintf "@c%d " i in
  check_eq "encoding: the order-consistency clauses"
    ~expected:
      (Printf.sprintf
         "* #variable= 3 #constraint= 2\n\
          %s+1 ~x_ge_2 +1 x_ge_1 >= 1 ;\n\
          %s+1 ~x_ge_3 +1 x_ge_2 >= 1 ;\n"
         (lbl 1) (lbl 2))
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
  (* M1-T41, from D-0031. This used to read [consistency_id e "x" 1 = Some 1] -- the
     rung's EAGER value, i.e. its .opb row position. That is true today and is the first
     assertion any future lazy-ladder attempt would break, which would make a rejected
     design look like a broken test.

     So what is asserted here is the TRANSITION instead: no rung has an id before the
     ladder is materialised, every interior rung has one after, they are distinct, and
     the two bounds never get one. Under D-0031's eager policy the materialisation point
     IS [declare_int]; under a lazy scheme it would be a later demand. Either way the
     observable is the same, so this check keeps its meaning under both.

     What is NOT weakened by dropping the literal ids: that the rungs are .opb ROWS, in
     order, with the right text, is exactly what the [check_eq] on [opb_text] above
     pins, and SPEC 4.2 is where that is normative. Delete the ladder from the .opb and
     the suite still goes red -- through that check rather than this one.

     One thing this pair CANNOT see, said here rather than left to be discovered: under
     the eager policy there is no state "declared, ladder not yet materialised", so the
     "no id yet" half has to be exercised on a variable that has no rung for some other
     reason. A bool is one -- declared, on [0, 1], no interior value -- and it goes
     through exactly the declared-variable path a lazy scheme's pre-materialisation
     state would. Found by breaking [consistency_id] to answer [Some 1] unconditionally:
     with the "before" half written against an UNdeclared variable it stayed green,
     because the answer was coming from the Undeclared path instead. *)
  let e_rung = Encoding.create () in
  Encoding.declare_bool e_rung "b";
  check "encoding: a declared variable with no rung to materialise has no rung id"
    (Encoding.consistency_id e_rung "b" 0 = None
    && Encoding.consistency_id e_rung "b" 1 = None);
  check "encoding: nor has one that has not been declared at all"
    ((try Encoding.consistency_id e_rung "x" 1 with Encoding.Undeclared _ -> None)
    = None);
  Encoding.declare_int e_rung "x" ~lo:0 ~hi:3;
  check "encoding: every interior rung has an id once the ladder is materialised"
    (Encoding.consistency_id e_rung "x" 1 <> None
    && Encoding.consistency_id e_rung "x" 2 <> None);
  check "encoding: distinct rungs get distinct ids"
    (Encoding.consistency_id e_rung "x" 1 <> Encoding.consistency_id e_rung "x" 2);
  check "encoding: no consistency clause at the bounds"
    (Encoding.consistency_id e_rung "x" 0 = None
    && Encoding.consistency_id e_rung "x" 3 = None);
  raises "encoding: a rung of an undeclared variable is an error, not a missing rung"
    (fun () -> Encoding.consistency_id e "zz" 1);
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
  (* Matched on the rule's BODY -- label off the front, terminator off the back
     ([Writer.rule_body]) -- because what is asserted here is what each step SAYS, not
     what it is named. The name is the checker's business and it verifies it for us: a
     citation of a label that was never bound is a parse error (D-0023). *)
  let bodies = List.map Writer.rule_body (String.split_on_char '\n' s) in
  let has l = List.exists (String.equal l) bodies in
  (* The channelling of PROOF-FORMAT section 3, with the constant halves dropped:
     x_ge_0 is true and x_ge_3 is false, so they never appear. The witness follows the
     `:` separator, before the terminator. *)
  (* x >= lo is the constant true, so x_eq_lo's "lower" half is not emitted. *)
  check "encoding: x_eq_lo has no x_ge_lo half"
    (has "red +1 ~x_eq_0 +1 ~x_ge_1 >= 1 : x_eq_0 -> 0"
    && has "red +1 x_eq_0 +1 x_ge_1 >= 1 : x_eq_0 -> 1"
    && not (has "red +1 ~x_eq_0 +1 x_ge_0 >= 1 : x_eq_0 -> 0"));
  check "encoding: the middle value gets both halves"
    (has "red +1 ~x_eq_1 +1 x_ge_1 >= 1 : x_eq_1 -> 0"
    && has "red +1 ~x_eq_1 +1 ~x_ge_2 >= 1 : x_eq_1 -> 0"
    && has "red +1 x_eq_1 +1 ~x_ge_1 +1 x_ge_2 >= 1 : x_eq_1 -> 1");
  check "encoding: x_eq_hi has no x_ge_(hi+1) half"
    (has "red +1 ~x_eq_2 +1 x_ge_2 >= 1 : x_eq_2 -> 0"
    && has "red +1 x_eq_2 +1 ~x_ge_2 >= 1 : x_eq_2 -> 1");
  (* Exactly-one is derived from the channelling, never assumed. *)
  check "encoding: at-least-one is a pol over the channelling ids"
    (has "pol @c3 @c6 + @c8 +");
  check "encoding: at-most-one is a pol over channelling plus the order chain"
    (has "pol @c2 @c7 + @c1 +");
  check "encoding: the definitions are retired" (has "del id @c2 @c3 @c4 @c5 @c6 @c7 @c8")

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
   Every test module open-coded this search, and every copy resolved it differently --
   so a project-wide choice of checker lived in nine places and could silently mean a
   build nobody intended (M1-T18). [None] is a FAILURE at every call site below, never
   a skip: an unchecked proof is not a passing test.

   There is one checker (D-0046), so this is the only resolver the file needs. A lane
   that asserts a REJECTION additionally asserts its WORDING wherever it can, which is
   what separates "the checker judged the step" from "the artefact did not parse" --
   M2-T14 found four lanes passing on the latter. *)
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

(* ------------------------------------------------------------------ *)
(* M1-T32: "Compile is the only door", enforced                        *)
(* ------------------------------------------------------------------ *)

(* THE PIN THAT MAKES THE DUPLICATION SAFE.

   [Encoding.Arith] is a local copy of [Baguette_core.Checked]'s five primitives, and
   it has to be one: core depends on proof, so [Checked] is not nameable from
   lib/proof/ (docs/ARCHITECTURE.md section 1). What makes that copy checkable rather
   than a second source of truth is that the TEST layer depends on both libraries even
   though neither depends on the other -- so the equivalence can be asserted here even
   though it cannot be expressed in lib/.

   Both operations are run on every case and the two answers are compared, raise
   included. A case where one raises and the other does not is the divergence this
   exists to catch. *)
let test_arith_matches_checked () =
  let module Checked = Baguette_core.Checked in
  let answer f x = try `V (f x) with _ -> `Raised in
  (* One check per operation, not per case: a divergence names the inputs it was found
     on, so the report is as specific as a per-case check without a hundred identical
     `ok` lines hiding the rest of the suite. *)
  let same name f g show cases =
    let bad = List.filter (fun c -> answer f c <> answer g c) cases in
    check
      (Printf.sprintf "M1-T32: Encoding.Arith.%s agrees with Checked.%s on all %d cases"
         name name (List.length cases))
      (bad = []);
    List.iter
      (fun c -> Printf.printf "       diverges at %s\n" (show c))
      (List.filteri (fun i _ -> i < 5) bad)
  in
  let one x = string_of_int x in
  let two (a, b) = Printf.sprintf "(%d, %d)" a b in
  (* The values straddle [mul]'s fast-path boundary deliberately: both copies take a
     four-comparison shortcut below 2^30 and an exact division above it, so a copy that
     drifted on WHERE that boundary sits would agree everywhere else. *)
  let ones =
    [
      0;
      1;
      -1;
      7;
      -7;
      max_int;
      min_int;
      max_int - 1;
      min_int + 1;
      0x3FFFFFFF;
      -0x3FFFFFFF;
      0x40000000;
      -0x40000000;
      max_int / 2;
      min_int / 2;
    ]
  in
  let pairs = List.concat_map (fun a -> List.map (fun b -> (a, b)) ones) ones in
  same "neg" Encoding.Arith.neg Checked.neg one ones;
  same "abs" Encoding.Arith.abs Checked.abs one ones;
  same "add"
    (fun (a, b) -> Encoding.Arith.add a b)
    (fun (a, b) -> Checked.add a b)
    two pairs;
  same "sub"
    (fun (a, b) -> Encoding.Arith.sub a b)
    (fun (a, b) -> Checked.sub a b)
    two pairs;
  same "mul"
    (fun (a, b) -> Encoding.Arith.mul a b)
    (fun (a, b) -> Checked.mul a b)
    two pairs;
  (* And the fast path's own boundary, where a wrong constant would show up as a
     disagreement only on products the four comparisons let through. *)
  check "M1-T32: Arith.mul's fast path answers the same at 2^30 - 1 squared"
    (Encoding.Arith.mul 0x3FFFFFFF 0x3FFFFFFF = Checked.mul 0x3FFFFFFF 0x3FFFFFFF)

(* The guard itself: a row whose arithmetic cannot be carried out is REFUSED at the
   committing door rather than silently written wrapped.

   The instance is D-0029's, verbatim: c = -2^61 against x in 3..4. The true row is
   vacuous (-2^61 * x <= 0 for every x >= 0), the wrapped one FORCES x = 4, and veripb
   accepted the refutation of that different model. test/unit/test_prop.ml's
   [test_opb_row_wraps_identically] still demonstrates the wrap on the pure expansion,
   which is what this guard exists to stop reaching a file. *)
let test_committing_door_refuses_overflow () =
  let overflows f =
    match f () with exception Encoding.Unrepresentable _ -> true | _ -> false
  in
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:3 ~hi:4;
  let before = Encoding.n_constraints e in
  check "M1-T32: add_int_lin_le refuses a row whose folded constant would wrap"
    (overflows (fun () -> Encoding.add_int_lin_le e [ (-2305843009213693952, "x") ] 0));
  check "M1-T32: ... and the encoding is left untouched, so no corrupted row is posted"
    (Encoding.n_constraints e = before);
  (* Products that each fit and a sum that does not -- the second way a row's
     arithmetic goes wrong, and the one a per-product check alone would miss.

     NO TEST MAY DECLARE A WIDE DOMAIN. The order encoding is width-proportional
     (D-0028), so `~hi:(max_int / 3)` is not a slightly bigger case, it is
     [declare_int] trying to allocate 10^18 ladder clauses -- which is how this test
     drove the machine into its RAM ceiling on its first run. Large arithmetic is
     driven through large COEFFICIENTS against domains of width 0 or 1 throughout. *)
  let e2 = Encoding.create () in
  let big = (max_int / 2) + 1 in
  Encoding.declare_int e2 "a" ~lo:big ~hi:big (* fixed: width 0, no ladder *);
  Encoding.declare_int e2 "b" ~lo:big ~hi:big;
  check "M1-T32: a term mass that leaves the range is refused too"
    (overflows (fun () -> Encoding.add_int_lin_le e2 [ (1, "a"); (1, "b") ] 0));
  (* The A/B pair is the widest arithmetic the .opb performs (checked.ml, path 4), so
     it is refused on rows the plain `<=` door still accepts. p is on [0, 1]: one
     literal, one ladder rung fewer than that. *)
  let e3 = Encoding.create () in
  Encoding.declare_int e3 "p" ~lo:0 ~hi:1;
  let a = max_int / 3 in
  check "M1-T32: add_int_lin_le accepts a row inside the envelope"
    (not (overflows (fun () -> Encoding.add_int_lin_le e3 [ (a, "p") ] 0)));
  check "M1-T32: add_int_lin_ne refuses the same row, whose A/B pair is wider"
    (overflows (fun () -> Encoding.add_int_lin_ne e3 [ (a, "p") ] 0));
  (* And an ordinary row is unaffected -- the guard must not be a cap. *)
  let e4 = Encoding.create () in
  Encoding.declare_int e4 "y" ~lo:0 ~hi:10;
  let id = Encoding.add_int_lin_le e4 [ (3, "y") ] 7 in
  check "M1-T32: an ordinary row is posted exactly as before"
    (id = Encoding.n_constraints e4
    && Opb.constr_to_string (List.nth (Encoding.constraints e4) (id - 1))
       = "+3 ~y_ge_1 +3 ~y_ge_2 +3 ~y_ge_3 +3 ~y_ge_4 +3 ~y_ge_5 +3 ~y_ge_6 +3 ~y_ge_7 \
          +3 ~y_ge_8 +3 ~y_ge_9 +3 ~y_ge_10 >= 23 ;")

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
      (* 3.0 terminates every rule, the preamble's `f` included. Both spellings are
         named rather than one being matched loosely, so that a THIRD spelling would
         fail here instead of slipping through. *)
      check "int_lin_le: the proof's f line matches the computed count"
        (List.exists
           (fun l ->
             let l = String.trim l in
             l = Printf.sprintf "f %d" f_count || l = Printf.sprintf "f %d ;" f_count)
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
let build_unsat dir =
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
  let pbp_oc = open_out pbp in
  let w = Writer.create ~comments:true ~audit:true pbp_oc in
  Encoding.write_opb ~comments:[ "x >= 2; x + y <= 2; y >= 1" ] e oc;
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

(* ------------------------------------------------------------------ *)
(* M1-T19: VeriPB 3.0 emission                                         *)
(*                                                                     *)
(* Every claim in D-0023 about 3.0 syntax is made here by running the   *)
(* checker, not by reading a grammar. Two things have to hold, and the  *)
(* second is what makes the first mean anything:                       *)
(*   1. the checker ACCEPTS the proof of an unsatisfiable model over    *)
(*      the full vocabulary -- red, levels, pol, del, conclusion. This  *)
(*      is invariant I-X1, and it absorbed the separate acceptance lane *)
(*      that used to run the same artefacts under format 2.0 (D-0046).  *)
(*   2. it REJECTS a corrupted one, and says WHY in words that show it  *)
(*      judged the conclusion -- without this, "3.0.2 accepted it" says *)
(*      nothing at all (scripts/mutate_proof.sh's argument, applied to  *)
(*      this lane).                                                     *)
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
    text (fun w ->
        Writer.header w ~n_model_constraints:1;
        Writer.set_level w 1;
        Writer.set_level w 0;
        let r1 = Writer.pol w ~origin:"root" (Pol.id 1) in
        let r2 = Writer.pol w ~origin:"root" (Pol.id 1) in
        Writer.set_level w 1;
        let b1 = Writer.pol w ~origin:"branch" (Pol.id 1) in
        let b2 = Writer.pol w ~origin:"branch" (Pol.id 1) in
        Writer.wipe_level w 1;
        (* A second branch, with a level-0 line derived AFTER it. The doomed run then
           stops short of the newest id, which is the only situation in which the
           range form can name its own (exclusive) upper bound at all -- see
           [Writer.del_run] and [test_v3_del_range_semantics]. *)
        Writer.set_level w 1;
        let b3 = Writer.pol w ~origin:"branch" (Pol.id 1) in
        let b4 = Writer.pol w ~origin:"branch" (Pol.id 1) in
        Writer.set_level w 0;
        let r3 = Writer.pol w ~origin:"root" (Pol.id 1) in
        Writer.wipe_level w 1;
        ids := [ r1; r2; b1; b2; b3; b4; r3 ];
        (* The root lines are NOT covered by either wipe and have to go explicitly,
           which is PROOF-FORMAT's "level-0 lines are covered by no `w`" -- unchanged
           by 3.0. *)
        Writer.delete_many w [ r1; r2; r3 ];
        Writer.conclusion w (Writer.Unsat None))
  in
  let lines = String.split_on_char '\n' s in
  let has l = List.exists (String.equal l) lines in
  let nth k = List.nth !ids k in
  check "3.0: there is no set-level rule"
    (not (List.exists (fun l -> String.length l > 0 && l.[0] = '#') lines));
  check "3.0: there is no wipe rule"
    (not (List.exists (fun l -> l = "w 1 ;" || l = "w 1") lines));
  check "3.0: a level is still marked, as a comment, or the proof is unreadable"
    (has "% level 1" && has "% level 0");
  (* M1-T22 found it, M1-T29 changed the shape. b1 and b2 are consecutive, but b2 is
     the newest id the writer has handed out, so there is no `@c(b2+1)` label for a
     half-open range to name. Until M1-T29 the run went out as an explicit `del id`
     list -- one line, but one citation per retired reason. It is now the PAIR
     `del range @cb1 @cb2 ;` (the half-open span, so b1 only) and `del id @cb2 ;`,
     two rules of bounded length. Both halves are asserted, and the list shape is
     asserted ABSENT: a partial change that emitted the range and forgot the trailing
     `del id` would leave b2 live in the checker while [tags] dropped it, which is
     exactly M1-T22's I-X3 violation coming back. That half is measured, not pinned,
     by [test_v3_wipe_level_against_checker]. *)
  check "3.0: a backtrack whose run reaches the newest id opens with a half-open range"
    (has (Printf.sprintf "del range @c%d @c%d ;" (nth 2) (nth 3)));
  check "3.0: ... and then retires the run's own last id, which the range does not"
    (has (Printf.sprintf "del id @c%d ;" (nth 3)));
  check "3.0: the newest-id run is no longer a citation per retired reason"
    (not (has (Printf.sprintf "del id @c%d @c%d ;" (nth 2) (nth 3))));
  (* M1-T22, the regression. `del range LO HI` deletes the HALF-OPEN [LO, HI), so the
     inclusive run b3..b4 is written with r3 -- the first SURVIVOR -- as its upper
     bound. Emitting `del range @cb3 @cb4` (what we did until M1-T22) leaves b4 live
     in the checker while [tags] and [live] have dropped it: an I-X3 mirror violation.
     The checker's half of this claim is [test_v3_del_range_semantics] below; this
     half only pins what we write. *)
  check "3.0: an inclusive run is written as a half-open range, ending one past the run"
    (has (Printf.sprintf "del range @c%d @c%d ;" (nth 4) (nth 6)));
  check "3.0: the run's own last id is NOT the range's upper bound"
    (not (has (Printf.sprintf "del range @c%d @c%d ;" (nth 4) (nth 5))));
  check "3.0: the root prunings survive both backtracks and are retired separately"
    (has (Printf.sprintf "del id @c%d @c%d @c%d ;" (nth 0) (nth 1) (nth 6)))

(* ------------------------------------------------------------------ *)
(* M1-T22: what `del range` actually deletes                           *)
(*                                                                     *)
(* The bug this pins was a disagreement between our text and the        *)
(* checker's reading of it, so an assertion about the text we emit      *)
(* cannot catch it on its own -- [test_v3_levels] above is exactly that *)
(* half, and it was GREEN while the bug shipped in 5 of 14 models. Both *)
(* tests below run the checker instead:                                *)
(*                                                                     *)
(*   [test_v3_del_range_semantics]  what `del range LO HI` means, from  *)
(*      hand-written proof text, with controls in both directions. This *)
(*      is the measurement docs/PROOF-FORMAT.md section 2a cites, and   *)
(*      it is a claim about a NAMED checker version -- the version is   *)
(*      printed by [report_checker] at the top of this file. A fact     *)
(*      measured against one checker is not a fact about proofs (the    *)
(*      M1-T18 lesson), so if this goes red the doc is what changes.    *)
(*                                                                     *)
(*   [test_v3_wipe_level_against_checker]  that [Writer.wipe_level]'s   *)
(*      own output retires exactly the ids the writer believes it       *)
(*      retires -- invariant I-X3, checked against the thing being      *)
(*      mirrored rather than against our model of it.                   *)
(* ------------------------------------------------------------------ *)

(* A two-line unsatisfiable .opb: `u >= 2` and `u < 2`. Summing the two rows is a
   contradiction with no division or saturation in the way, which keeps every proof
   below about deletion and nothing else. *)
let del_range_opb dir name =
  let e = Encoding.create () in
  let c_pos = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "uu" 2) ] 1) in
  let c_neg = Encoding.add_constraint e (Opb.ge [ (1, Lit.negate (Lit.ge "uu" 2)) ] 1) in
  let opb = Filename.concat dir (name ^ ".opb") in
  let oc = open_out opb in
  Encoding.write_opb e oc;
  close_out oc;
  (opb, c_pos, c_neg)

let write_lines path lines =
  let oc = open_out path in
  List.iter (fun l -> output_string oc (l ^ "\n")) lines;
  close_out oc

let test_v3_del_range_semantics () =
  match veripb_path () with
  | None ->
      incr failures;
      print_endline
        ("FAIL 3.0 del range: " ^ Baguette_proof.Checker.not_found_message
       ^ " -- the semantics of `del range` is MEASURED, never assumed, so with no \
          checker this is not a pass.")
  | Some veripb -> (
      let dir = Filename.temp_file "baguette_delrange" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      let opb, c_pos, c_neg = del_range_opb dir "m" in
      let log = Filename.concat dir "log" in
      (* ids: 1 = c_pos, 2 = c_neg, then 3, 4, 5 are copies of c_pos, and 6 is the
         contradiction. A probe is `pol @cN` -- a one-operand derivation, valid for
         any LIVE id and a hard error for a deleted one, which is what makes the
         accept/reject answer mean "still in the database". *)
      let a, b, c = (c_neg + 1, c_neg + 2, c_neg + 3) in
      let proof ~del ~probe =
        List.concat
          [
            [ "pseudo-Boolean proof version 3.0"; Printf.sprintf "f %d ;" c_neg ];
            List.map (fun id -> Printf.sprintf "@c%d pol @c%d ;" id c_pos) [ a; b; c ];
            del;
            [ Printf.sprintf "@c%d pol @c%d ;" (c + 1) probe ];
            [
              Printf.sprintf "@c%d pol @c%d @c%d + ;" (c + 2) c_pos c_neg;
              "output NONE ;";
              Printf.sprintf "conclusion UNSAT : @c%d ;" (c + 2);
              "end pseudo-Boolean proof ;";
            ];
          ]
      in
      let accepted name ~del ~probe =
        let pbp = Filename.concat dir (name ^ ".pbp") in
        write_lines pbp (proof ~del ~probe);
        match run_checker ~checker:veripb ~opb ~pbp ~log with
        | Some v -> v
        | None -> failwith "checker vanished between find and run"
      in
      let range lo hi = [ Printf.sprintf "del range @c%d @c%d ;" lo hi ] in
      (* The controls that make the answer readable at all. *)
      check "3.0 del range: with no deletion, citing any derived id is accepted"
        (accepted "ctl_none" ~del:[] ~probe:c);
      check "3.0 del range: citing an id deleted by `del id` IS an error"
        (not (accepted "ctl_delid" ~del:[ Printf.sprintf "del id @c%d ;" c ] ~probe:c));
      (* The measurement itself, in both directions. *)
      check "3.0 del range: `del range LO HI` does NOT delete HI -- the span is half-open"
        (accepted "half_open_hi" ~del:(range a c) ~probe:c);
      check "3.0 del range: it DOES delete LO"
        (not (accepted "half_open_lo" ~del:(range a c) ~probe:a));
      check "3.0 del range: it DOES delete everything strictly between LO and HI"
        (not (accepted "half_open_mid" ~del:(range a c) ~probe:b));
      check "3.0 del range: widening HI by one is what deletes the old HI"
        (not (accepted "widened" ~del:(range a (c + 1)) ~probe:c));
      (* Why [Writer.del_run] cannot always use the range form: the exclusive upper
         bound must be a label that is already BOUND, or the proof does not parse. *)
      check "3.0 del range: an unbound label as the upper bound is a parse error"
        (not (accepted "unbound" ~del:(range a (c + 9)) ~probe:a));
      Sys.readdir dir
      |> Array.iter (fun f -> try Sys.remove (Filename.concat dir f) with _ -> ());
      try Sys.rmdir dir with _ -> ())

(* ------------------------------------------------------------------ *)
(* M1-T29: the pair spelling, measured, with the break performed      *)
(*                                                                     *)
(* [test_v3_del_range_semantics] above establishes what `del range`    *)
(* means. This establishes what the PAIR means, which is a different   *)
(* claim, and it does the thing this project keeps finding it has not  *)
(* done: it performs the off-by-one rather than reading the code for   *)
(* one. Over-deletion is the direction that matters. An upper bound    *)
(* one too HIGH retires a constraint a later line may cite -- and      *)
(* since D-0039/I-S4 "a later line" includes a trace line citing a     *)
(* hole line -- while our own I-X2 audit sees nothing, because an      *)
(* over-deleted id is not an un-retired id and the audit checks our    *)
(* bookkeeping against itself. Only the checker can answer, so only    *)
(* the checker is asked.                                               *)
(*                                                                     *)
(* Four derived ids, a..d, so that there is an id ABOVE the run: that  *)
(* is what makes over-deletion observable at all (with the run ending  *)
(* at the newest id there is nothing above it to lose), and it is what *)
(* lets the wrong bound be a BOUND label rather than an unassigned one *)
(* -- the two failures word themselves differently and both are        *)
(* asserted.                                                           *)
(* ------------------------------------------------------------------ *)
let test_v3_del_pair_spelling () =
  match veripb_path () with
  | None ->
      incr failures;
      print_endline
        ("FAIL 3.0 del pair: " ^ Baguette_proof.Checker.not_found_message
       ^ " -- M1-T29's spelling is a claim about what 3.0.2 deletes, and with no checker \
          this is not a pass.")
  | Some veripb -> (
      let dir = Filename.temp_file "baguette_delpair" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      let opb, c_pos, c_neg = del_range_opb dir "m" in
      let log = Filename.concat dir "log" in
      let a, b, c, d = (c_neg + 1, c_neg + 2, c_neg + 3, c_neg + 4) in
      (* [probe] is `pol @cN`: valid for any live id, a hard error for a deleted one,
         so the accept/reject verdict reads straight off the checker's database. *)
      let proof ~del ~probe =
        List.concat
          [
            [ "pseudo-Boolean proof version 3.0"; Printf.sprintf "f %d ;" c_neg ];
            List.map (fun id -> Printf.sprintf "@c%d pol @c%d ;" id c_pos) [ a; b; c; d ];
            del;
            [ Printf.sprintf "@c%d pol @c%d ;" (d + 1) probe ];
            [
              Printf.sprintf "@c%d pol @c%d @c%d + ;" (d + 2) c_pos c_neg;
              "output NONE ;";
              Printf.sprintf "conclusion UNSAT : @c%d ;" (d + 2);
              "end pseudo-Boolean proof ;";
            ];
          ]
      in
      let accepted name ~del ~probe =
        let pbp = Filename.concat dir (name ^ ".pbp") in
        write_lines pbp (proof ~del ~probe);
        match run_checker ~checker:veripb ~opb ~pbp ~log with
        | Some v -> v
        | None -> failwith "checker vanished between find and run"
      in
      (* [Writer.del_run]'s M1-T29 shape for the inclusive run [a, c]. *)
      let pair lo hi =
        [
          Printf.sprintf "del range @c%d @c%d ;" lo hi; Printf.sprintf "del id @c%d ;" hi;
        ]
      in
      (* The control, without which every rejection below says nothing. *)
      check "3.0 del pair: with no deletion the whole run is live"
        (accepted "pair_ctl" ~del:[] ~probe:c);
      (* The pair is a legal proof at all, and deletes the run: all three ids. *)
      check "3.0 del pair: the pair spelling is accepted by the checker"
        (accepted "pair_ok" ~del:(pair a c) ~probe:d);
      check "3.0 del pair: it deletes LO"
        (not (accepted "pair_lo" ~del:(pair a c) ~probe:a));
      check "3.0 del pair: it deletes the interior"
        (not (accepted "pair_mid" ~del:(pair a c) ~probe:b));
      check
        "3.0 del pair: it deletes the run's own last id, which the range alone does NOT \
         (M1-T22)"
        (not (accepted "pair_hi" ~del:(pair a c) ~probe:c));
      (* OVER-DELETION, the dangerous direction, performed. @cd is outside the run. *)
      check
        "3.0 del pair: the id one PAST the run survives -- the pair does not over-delete"
        (accepted "pair_past" ~del:(pair a c) ~probe:d);
      check
        "3.0 del pair: an upper bound one too HIGH is caught by the trailing `del id`, \
         not silent"
        (not
           (accepted "pair_over"
              ~del:
                [
                  Printf.sprintf "del range @c%d @c%d ;" a d;
                  Printf.sprintf "del id @c%d ;" c;
                ]
              ~probe:a));
      (* The same break where the wrong bound is an UNASSIGNED label -- the case the
         writer actually faces, since the run ends at the newest id. D-0023's trap
         stays closed: a drifted citation is a parse error naming the label. *)
      check
        "3.0 del pair: an upper bound past every assigned label is a parse error naming \
         it"
        (not
           (accepted "pair_unbound"
              ~del:
                [
                  Printf.sprintf "del range @c%d @c%d ;" a (d + 4);
                  Printf.sprintf "del id @c%d ;" c;
                ]
              ~probe:a));
      (* UNDER-DELETION, the other direction: a bound one too low leaves the run's
         second-to-last id live while our tags have dropped it -- the I-X3 mirror
         violation M1-T22 shipped, in miniature. Caught by asserting @cb is GONE. *)
      check
        "3.0 del pair: an upper bound one too LOW leaves an id of the run live (so the \
         `pair_mid` check above can fail)"
        (accepted "pair_under"
           ~del:
             [
               Printf.sprintf "del range @c%d @c%d ;" a b;
               Printf.sprintf "del id @c%d ;" c;
             ]
           ~probe:b);
      (* And the numeric route M1-T29 rejected, measured so the rejection is on
         record rather than argued: exactly one past the last id is tolerated, two
         past is a hard error. A spelling with no margin. *)
      (* Probing the untouched MODEL row separates "parsed, and deleted the span"
         from "was refused outright" -- both of which read as a rejection when the
         probe is inside the span, which is how a measurement of a tolerance turns
         into a measurement of nothing. *)
      let num bound = [ Printf.sprintf "del range @c%d %d ;" a bound ] in
      check
        "3.0 del pair: a NUMERIC bound one past the last id parses (the route not taken, \
         measured)"
        (accepted "num_one_past_ok" ~del:(num (d + 1)) ~probe:c_pos);
      check "3.0 del pair: ... and really does delete through the last id"
        (not (accepted "num_one_past_d" ~del:(num (d + 1)) ~probe:d));
      check
        "3.0 del pair: a NUMERIC bound TWO past the last id is a hard error, so the \
         numeric spelling has exactly one legal value"
        (not (accepted "num_two_past" ~del:(num (d + 2)) ~probe:c_pos));
      Sys.readdir dir
      |> Array.iter (fun f -> try Sys.remove (Filename.concat dir f) with _ -> ());
      try Sys.rmdir dir with _ -> ())

let test_v3_wipe_level_against_checker () =
  match veripb_path () with
  | None ->
      incr failures;
      print_endline
        ("FAIL 3.0 wipe_level: " ^ Baguette_proof.Checker.not_found_message
       ^ " -- I-X3 says our mirror agrees with the checker, which cannot be asserted \
          without one.")
  | Some veripb -> (
      let dir = Filename.temp_file "baguette_wipe" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      let log = Filename.concat dir "log" in
      (* [interior] decides which shape [Writer.del_run] reaches: false leaves the
         doomed run ending at the newest id (the `del id` list), true derives one
         more level-0 line after it (the half-open `del range`). [probe] picks an id
         to cite AFTER the wipe; the checker's accept/reject is then a direct read of
         whether that id is still in its database. *)
      let scenario name ~interior ~probe =
        let e = Encoding.create () in
        let c_pos = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "uu" 2) ] 1) in
        let c_neg =
          Encoding.add_constraint e (Opb.ge [ (1, Lit.negate (Lit.ge "uu" 2)) ] 1)
        in
        let opb = Filename.concat dir (name ^ ".opb") in
        let pbp = Filename.concat dir (name ^ ".pbp") in
        let pbp_oc = open_out pbp in
        let w = Writer.create ~audit:false pbp_oc in
        let oc = open_out opb in
        Encoding.write_opb e oc;
        close_out oc;
        Encoding.start_proof e w;
        Writer.set_level w 1;
        let p1 = Writer.pol w ~origin:"branch" (Pol.id c_pos) in
        let _p2 = Writer.pol w ~origin:"branch" (Pol.id c_pos) in
        let p3 = Writer.pol w ~origin:"branch" (Pol.id c_pos) in
        Writer.set_level w 0;
        let past =
          if interior then Some (Writer.pol w ~origin:"root" (Pol.id c_pos)) else None
        in
        Writer.wipe_level w 1;
        (match probe with
        | None -> ()
        | Some pick ->
            ignore
              (Writer.pol w ~origin:"probe"
                 (Pol.id (pick ~first:p1 ~last:p3 ~past ~model:c_pos))));
        let contra =
          Writer.pol w ~origin:"contradiction" Pol.(sum [ id c_pos; id c_neg ])
        in
        Writer.conclusion w (Writer.Unsat (Some contra));
        close_out pbp_oc;
        let verdict =
          match run_checker ~checker:veripb ~opb ~pbp ~log with
          | Some v -> v
          | None -> failwith "checker vanished between find and run"
        in
        (verdict, read_whole pbp)
      in
      let verdict name ~interior ~probe = fst (scenario name ~interior ~probe) in
      (* The baselines: the wipe on its own leaves a proof the checker accepts, in
         both emission shapes. Without these, a rejection below would say nothing. *)
      check "3.0 wipe_level: a backtrack ending at the newest id verifies"
        (verdict "base_list" ~interior:false ~probe:None);
      check "3.0 wipe_level: a backtrack with a later level-0 line verifies"
        (verdict "base_range" ~interior:true ~probe:None);
      (* I-X3, the direction M1-T22 got wrong. The writer drops the whole run from
         [t.tags]; the checker must have dropped it too. Before the fix the LAST id
         of the run was still live in the checker and this lane was ACCEPTED. *)
      List.iter
        (fun interior ->
          let tag = if interior then "range" else "list" in
          check
            (Printf.sprintf
               "3.0 wipe_level (%s form): the LAST id of the wiped run is gone from the \
                checker too (I-X3)"
               tag)
            (not
               (verdict ("last_" ^ tag) ~interior
                  ~probe:(Some (fun ~first:_ ~last ~past:_ ~model:_ -> last))));
          check
            (Printf.sprintf
               "3.0 wipe_level (%s form): the FIRST id of the wiped run is gone from the \
                checker"
               tag)
            (not
               (verdict ("first_" ^ tag) ~interior
                  ~probe:(Some (fun ~first ~last:_ ~past:_ ~model:_ -> first))));
          check
            (Printf.sprintf
               "3.0 wipe_level (%s form): a model row is untouched by the wipe, so a \
                rejection above is about deletion and not about position"
               tag)
            (verdict ("model_" ^ tag) ~interior
               ~probe:(Some (fun ~first:_ ~last:_ ~past:_ ~model -> model))))
        [ false; true ];
      (* The other side of half-open: the id the range NAMES as its upper bound is a
         survivor, not a casualty. Deleting it would be the mirror violation in the
         opposite direction -- silently losing a level-0 reason. *)
      check
        "3.0 wipe_level: the level-0 line one past the run survives the range that names \
         it"
        (verdict "past_range" ~interior:true
           ~probe:(Some (fun ~first:_ ~last:_ ~past ~model:_ -> Option.get past)));
      (* And that the range form really was the shape under test. *)
      let _, text_range = scenario "shape_range" ~interior:true ~probe:None in
      let _, text_list = scenario "shape_list" ~interior:false ~probe:None in
      let contains needle hay =
        let n = String.length needle and h = String.length hay in
        let rec go i = i + n <= h && (String.sub hay i n = needle || go (i + 1)) in
        n = 0 || go 0
      in
      check "3.0 wipe_level: the interior case really does emit `del range`"
        (contains "del range " text_range);
      (* M1-T29. The newest-id case emits the PAIR, so both halves must be there --
         and, unlike before, a `del range` in this text is now expected rather than
         forbidden. Asserting the pair rather than just "some deletion happened" is
         what keeps this check able to see its subject fail: the probes above are
         satisfied by a single over-wide range too, and it is the trailing `del id`
         that distinguishes a correct pair from one. *)
      check
        "3.0 wipe_level: the newest-id case emits a half-open range AND the run's last id"
        (contains "del range " text_list && contains "del id " text_list);
      (* Generically, not by naming ids: no `del id` rule this writer emits for a
         wiped run carries more than one citation any more. That is the whole of
         M1-T29's asymptotic claim, asserted on emitted text. *)
      let del_id_widths text =
        String.split_on_char '\n' text
        |> List.filter_map (fun l ->
               let l = String.trim l in
               if String.length l >= 7 && String.sub l 0 7 = "del id " then
                 Some (List.length (String.split_on_char ' ' l) - 3)
               else None)
      in
      check "3.0 wipe_level: no `del id` rule carries more than one citation"
        (List.for_all (fun n -> n <= 1) (del_id_widths text_list)
        && List.for_all (fun n -> n <= 1) (del_id_widths text_range));
      (* The over-deletion direction, end to end through [wipe_level] rather than
         through hand-written text: an upper bound one too high in the pair's range
         would retire [last] before the trailing `del id` reaches it, and 3.0.2 says
         so ("Trying to access constraint with ID N that has already been deleted").
         So the plain baseline verdict at the top of this test is itself the detector
         -- stated here because a baseline that is also a detector is easy to read as
         neither. [test_v3_del_pair_spelling] performs that break on purpose. *)
      Sys.readdir dir
      |> Array.iter (fun f -> try Sys.remove (Filename.concat dir f) with _ -> ());
      try Sys.rmdir dir with _ -> ())

let test_v3_veripb () =
  match veripb_path () with
  | None ->
      incr failures;
      print_endline ("FAIL 3.0: " ^ Baguette_proof.Checker.not_found_message)
  | Some veripb -> (
      let dir = Filename.temp_file "baguette_v3" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      let opb, pbp = build_unsat dir in
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
         perfectly good model row, and no contradiction at all. Without this control,
         "3.0.2 accepted it" is not evidence of anything: it is the argument
         scripts/mutate_proof.sh's header makes, turned on the format switch.

         The rejection's wording, measured and not guessed, is

           "The constraint with ID <n> is not contradicting, as specified by the hint."

         and it is asserted below, not just the exit status: an exit status cannot tell
         a JUDGEMENT from a parse error. lib/core/prop/ne.ml and
         test/unit/test_random.ml carry the same wording. *)
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
          (* M2-T14: "it rejected" is not the claim -- "it judged the conclusion" is.
             A checker that merely failed to PARSE the artefact prints nothing of the
             sort, which is how this lane used to pass when it was handed an .opb the
             checker could not read. *)
          let out = try read_whole log with _ -> "" in
          let says needle =
            let n = String.length needle in
            let rec go i =
              i + n <= String.length out && (String.sub out i n = needle || go (i + 1))
            in
            go 0
          in
          if says "is not contradicting" then
            Printf.printf
              "ok   3.0: veripb rejects a proof whose conclusion cites a \
               non-contradiction, and says so\n"
          else (
            incr failures;
            Printf.printf
              "FAIL 3.0: veripb refused the corrupted proof but never judged the \
               conclusion -- \"is not contradicting, as specified by the hint\" is not \
               in its output, so this is a malformed artefact and not a measurement.\n\
              \  checker said: %s\n"
              (String.trim out))
      | Some true ->
          incr failures;
          Printf.printf
            "FAIL 3.0: veripb ACCEPTED a proof concluding UNSAT from a model row that \
             establishes no contradiction. The acceptance above therefore says nothing.\n\
            \  A rejection here would have been worded \"The constraint with ID <n> is \
             not contradicting, as specified by the hint\".\n");
      List.iter (fun f -> try Sys.remove f with _ -> ()) [ opb; pbp; corrupted; log ];
      try Sys.rmdir dir with _ -> ())

(* ------------------------------------------------------------------------- *)
(* M1-T51: a `pol` that derives something WEAKER than the claimed bound.     *)
(* ------------------------------------------------------------------------- *)

(* The three-row .opb this test reasons over:

     @c1  +1 vv_ge_1 +1 uu_ge_2  >= 1
     @c2  +1 vv_ge_1 +1 ~uu_ge_2 >= 1
     @c3  +1 ~vv_ge_1            >= 1

   Summing @c1 and @c2 cancels uu_ge_2 against its negation and leaves
   `+2 vv_ge_1 >= 1`; dividing by 2 gives `+1 vv_ge_1 >= 1`, i.e. vv >= 1. So the
   honest derivation is `pol @c1 @c2 + 2 d` and the bound a propagator would prune to
   on the strength of it is exactly `vv >= 1`.

   Truncating that derivation to its leftmost operand leaves `@c1` itself, which is
   `vv >= 1 OR uu >= 2` -- strictly weaker than the claim, and not a bound at all. A
   propagator whose `pol` came out like that has pruned vv's domain on a derivation
   that does not support the prune. That is the subject of this test.

   @c3 is why the proof can close at all, and its role is load-bearing in a way worth
   spelling out. The derivation UNDER TEST must not be what closes the proof: if the
   conclusion cited it, a weakened `pol` would be caught downstream at the
   `conclusion` line and this test would be measuring that old indirect control
   instead of the new direct one -- the gap lane below would go red for the wrong
   reason. So the contradiction is derived SEPARATELY, from @c1 @c2 @c3 under its own
   origin, and the step under test is a side derivation that is created, claimed and
   deleted without anything ever depending on it. That is also the realistic shape:
   most prunings in a run are never cited by the conflict that ends the branch.

   That last point is also the resolution of an apparent contradiction with
   test_mutation, and it is worth writing down because it looks at first glance as
   though M1-T51 were already covered. The `triple_unsat/truncate-derivation` and
   `lin_unsat/truncate-derivation` lanes are green, and they say "veripb rejects the
   corrupted step, on the derivation". They are not lying. They are green because in
   those models the truncated `pol` IS load-bearing: the whole model suite emits ten
   `pol` lines between its thirty-one models, all of them on small unsat instances
   where the derivation feeds the contradiction that `conclusion UNSAT` cites. Break
   it and the conclusion stops checking.

   So the existing coverage is real but it is not general. It holds because the test
   models are small enough that every `pol` matters, and it says nothing about the
   case that dominates any real search -- a pruning the eventual conflict never cites.
   For that case, before this rule, the answer was that NOTHING caught it: not the
   shape pins, which never run against a corrupted writer at all, and not the checker,
   which the gap lane below shows accepting it. Hence M1-T42's ninth cell. *)
let pol_claim_opb dir name =
  let e = Encoding.create () in
  let v = Lit.ge "vv" 1 in
  let u = Lit.ge "uu" 2 in
  let c1 = Encoding.add_constraint e (Opb.ge [ (1, v); (1, u) ] 1) in
  let c2 = Encoding.add_constraint e (Opb.ge [ (1, v); (1, Lit.negate u) ] 1) in
  let c3 = Encoding.add_constraint e (Opb.ge [ (1, Lit.negate v) ] 1) in
  let opb = Filename.concat dir (name ^ ".opb") in
  let oc = open_out opb in
  Encoding.write_opb e oc;
  close_out oc;
  (opb, c1, c2, c3, v)

let test_pol_states_its_conclusion () =
  match veripb_path () with
  | None ->
      incr failures;
      print_endline
        ("FAIL M1-T51 pol conclusion: " ^ Baguette_proof.Checker.not_found_message
       ^ " -- the whole point of this test is that the CHECKER, not a regex over the \
          emitted text, is what rejects a weakened `pol`. With no checker there is \
          nothing here but shape pins, which is the state M1-T51 exists to leave. This \
          is not a pass.")
  | Some veripb -> (
      let dir = Filename.temp_file "baguette_polclaim" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      let log = Filename.concat dir "log" in
      let site = "vv >= 1 from the two rows" in
      (* [stated]: does the proof state its conclusion (`ia`) or only derive
         (`pol`)? [truncated]: is the derivation corrupted to its leftmost operand,
         so that it concludes something strictly weaker than the claim?

         Returns [Some true] if veripb ACCEPTED the proof. *)
      let run ~name ~stated ~truncated =
        let opb, c1, c2, c3, v = pol_claim_opb dir name in
        let pbp = Filename.concat dir (name ^ ".pbp") in
        let oc = open_out pbp in
        let mutation = Writer.Mutation.make ~site Writer.Mutation.Truncate_derivation in
        let w =
          if truncated then Writer.create_mutated ~mutation oc else Writer.create oc
        in
        Writer.header w ~n_model_constraints:c3;
        let expr = Pol.(div (add (id c1) (id c2)) 2) in
        let claim = Opb.ge [ (1, v) ] 1 in
        let id =
          if stated then Writer.pol_concluding w ~origin:site ~claim expr
          else Writer.pol w ~origin:site expr
        in
        (* The corruption must actually have happened, or every verdict below is about
           a proof nobody broke. [mutation_note] is the writer's own record of whether
           the knob found a site it could corrupt. *)
        if truncated && Writer.mutation_note w = None then (
          incr failures;
          Printf.printf
            "FAIL M1-T51 %s: the Truncate_derivation knob never fired at site %S, so \
             this lane corrupted nothing and its verdict means nothing.\n"
            name site);
        Writer.delete w id;
        (* The contradiction, under its own origin so the knob above cannot reach it:
           vv >= 1 from the first two rows, plus @c3's ~vv, is 1 >= 2. *)
        let bottom =
          Writer.pol w ~origin:"the contradiction"
            Pol.(add (div (add (id c1) (id c2)) 2) (id c3))
        in
        Writer.conclusion w (Writer.Unsat (Some bottom));
        close_out oc;
        run_checker ~checker:veripb ~opb ~pbp ~log
      in
      (* 1. The honest derivation, unstated and stated. Both must be accepted, or the
            control below is measuring a broken baseline rather than a corruption. *)
      check "M1-T51 baseline: an honest `pol` is accepted"
        (run ~name:"honest_bare" ~stated:false ~truncated:false = Some true);
      check "M1-T51 baseline: the same `pol` with its conclusion STATED is accepted"
        (run ~name:"honest_ia" ~stated:true ~truncated:false = Some true);
      (* 2. THE GAP. A `pol` truncated to derive something strictly weaker than the
            bound it was emitted to support is accepted by veripb, because nothing in
            the proof ever said what it was supposed to conclude. This lane asserts
            the ACCEPTANCE: it is the control that makes lane 3 mean something, and if
            it ever starts failing then `pol` alone has grown a conclusion check and
            this test's premise needs re-measuring, not deleting. *)
      check
        "M1-T51 the gap: a `pol` weakened to derive LESS than the claimed bound is still \
         accepted when the proof does not state what it concludes"
        (run ~name:"weak_bare" ~stated:false ~truncated:true = Some true);
      (* 3. THE CONTROL. Same corruption, same expression, same site -- the only
            difference from lane 2 is the `ia` line stating the claim. *)
      check
        "M1-T51 the control: stating the conclusion makes the checker REJECT that same \
         weakened `pol`"
        (run ~name:"weak_ia" ~stated:true ~truncated:true = Some false);
      (* 4. And the rejection is the one we think it is, not a parse error or a
            dangling label. Asserted at full strength: an exit status cannot tell a
            JUDGEMENT from a refusal to parse (M2-T14). *)
      let contains needle hay =
        let n = String.length needle and h = String.length hay in
        let rec go i = i + n <= h && (String.sub hay i n = needle || go (i + 1)) in
        n = 0 || go 0
      in
      let s = read_whole log in
      check "M1-T51: the rejection is the implication check, in the checker's words"
        (contains "not syntactically implied" s);
      Sys.readdir dir
      |> Array.iter (fun f -> try Sys.remove (Filename.concat dir f) with _ -> ());
      try Sys.rmdir dir with _ -> ())

(* -------------------------------------------------------------------------- *)
(*   M2-L1 / D-0045: a learned constraint and the backjump that follows it.    *)
(* -------------------------------------------------------------------------- *)

(* D-0045's addendum states a prediction and asks for it to be falsified before it is
   fixed: "emit a learned constraint at the conflict level, and the backjump that follows
   deletes it". This is that measurement, and then the fix, in one scenario driven twice.

   Why it is HERE and not in test_learned.ml: the thing under test is [Writer]'s id
   lifetime, not the learned type. A learned constraint is simply the first object this
   solver has whose lifetime is not a search level's, so it is the first caller that ever
   cares.

   The scenario:

     start_proof; set_level 1          -- we are inside a branch
     <mint a constraint>               -- at level 1 (broken) or inside
                                          [Writer.with_level w 0] (fixed)
     wipe_level 1                      -- the backjump
     pol <that constraint>             -- the learned constraint doing its job later

   BROKEN must be rejected and FIXED must be accepted. Requiring both directions is the
   point: a test that only ran the fixed case would pass just as well against a writer
   that had never had the bug.

   The machinery: VeriPB 3.0 has no level stack (D-0024), so [wipe_level] computes the
   doomed set from our own [t.tags] and emits the `del`s itself. [Writer.with_level]
   moves the level FOR REAL -- the `% level 0` marker goes on the page -- rather than
   only adjusting [t.tags], so [t.tags] and the proof cannot drift apart (I-X3).

   M2-T14. This used to assert on the checker's exit status alone. An exit status cannot
   tell a JUDGEMENT from a parse error, and that gap was live: the BROKEN lane passed on
   an .opb the checker could not read, never reaching a deletion at all. So the rejection
   is asserted by its words (measured 2026-09-18):

     "Trying to access constraint with ID 3 that has already been deleted."

   which no file that failed to parse can produce. *)
let test_learned_survives_the_backjump () =
  match veripb_path () with
  | None ->
      incr failures;
      print_endline
        ("FAIL M2-L1 learned lifetime: " ^ Baguette_proof.Checker.not_found_message
       ^ " -- D-0045's prediction is about what the CHECKER does with a wiped \
          level,           which cannot be measured without one.")
  | Some veripb ->
      let dir = Filename.temp_file "baguette_learned" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      let log = Filename.concat dir "log" in
      let has hay needle =
        let n = String.length needle in
        let rec go i =
          i + n <= String.length hay && (String.sub hay i n = needle || go (i + 1))
        in
        go 0
      in
      (* [at_level_0] is the fix. Returns the checker's verdict, the emitted text and the
         level our own table thinks the learned id landed at. *)
      let scenario name ~at_level_0 =
        let e = Encoding.create () in
        let c_pos = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "uu" 2) ] 1) in
        let c_neg =
          Encoding.add_constraint e (Opb.ge [ (1, Lit.negate (Lit.ge "uu" 2)) ] 1)
        in
        let opb = Filename.concat dir (name ^ ".opb") in
        let pbp = Filename.concat dir (name ^ ".pbp") in
        let pbp_oc = open_out pbp in
        let w = Writer.create ~audit:false pbp_oc in
        let oc = open_out opb in
        Encoding.write_opb e oc;
        close_out oc;
        Encoding.start_proof e w;
        Writer.set_level w 1;
        let learned =
          if at_level_0 then
            Writer.with_level w 0 (fun () ->
                Writer.pol w ~origin:"learned" (Pol.id c_pos))
          else Writer.pol w ~origin:"learned" (Pol.id c_pos)
        in
        let tag = Writer.tag_of w learned in
        Writer.wipe_level w 1;
        (* The learned constraint doing later what it was learned for. *)
        let used = Writer.pol w ~origin:"uses the learned constraint" (Pol.id learned) in
        Writer.delete w used;
        if at_level_0 then Writer.delete w learned;
        let contra =
          Writer.pol w ~origin:"contradiction" Pol.(sum [ id c_pos; id c_neg ])
        in
        Writer.conclusion w (Writer.Unsat (Some contra));
        close_out pbp_oc;
        let verdict =
          match run_checker ~checker:veripb ~opb ~pbp ~log with
          | Some v -> v
          | None -> failwith "checker vanished between find and run"
        in
        (verdict, read_whole pbp, tag, try read_whole log with _ -> "")
      in
      let broken, broken_text, broken_level, broken_log =
        scenario "broken" ~at_level_0:false
      in
      let fixed, fixed_text, fixed_level, _ = scenario "fixed" ~at_level_0:true in
      check
        "M2-L1: D-0045's prediction HOLDS -- a constraint minted at the conflict level \
         is deleted by the backjump and citing it is REJECTED"
        (not broken);
      (* ... and it is the DELETION that rejects it, not a file the checker could not
         parse. Without this the lane passes on any malformed artefact. *)
      let needle = "that has already been deleted" in
      let judged = has broken_log needle in
      check
        "M2-L1: and the rejection is the DELETION, in the checker's own words -- not a \
         parse error"
        judged;
      if not judged then
        Printf.printf "       checker said: %s\n" (String.trim broken_log);
      check
        "M2-L1: Writer.with_level 0 makes the learned constraint outlive the backjump -- \
         the same proof is ACCEPTED"
        fixed;
      check
        "M2-L1: without the fix our own tag table puts the learned id at the conflict \
         level"
        (broken_level = Some 1);
      check "M2-L1: with the fix it is tagged 0, so wipe_level cannot see it"
        (fixed_level = Some 0);
      (* The tag table alone is not the fix: the level has to be moved in the PROOF, or
         [t.tags] and the file disagree about where the id landed (I-X3). *)
      check "M2-L1: the fix is a real level marker in the proof, not a table update"
        (has fixed_text "% level 0" && not (has broken_text "% level 0"))

(* ------------------------------------------------------------------ *)
(* M3-T1: reified variables                                            *)
(*                                                                     *)
(* The design is in lib/proof/encoding.ml's "M3-T1" header. What is    *)
(* checked here, in the order the lanes run:                           *)
(*                                                                     *)
(*   1. the two rows MEAN  r <-> cond, checked point by point over     *)
(*      small domains against an evaluator that knows only what an     *)
(*      order literal means -- the same independent check              *)
(*      [check_soundness] makes for a plain int_lin_le row, and the    *)
(*      one that would catch a big-M off by one that cancels itself.   *)
(*   2. the emitted [red] line puts the witness BEFORE the terminator, *)
(*      pinned as text, with the trap itself performed: a proof whose  *)
(*      witness sits after the `;` is REJECTED, and on the wording     *)
(*      that says a witness was missing rather than on some parse      *)
(*      error further down.                                            *)
(*   3. veripb accepts a refutation that runs THROUGH the definition   *)
(*      -- both halves load-bearing, the contradiction being           *)
(*      `~r` and `r` -- so the definition is cited, not merely         *)
(*      emitted. A definition nothing cites is not yet evidence.       *)
(*   4. two deliberately wrong definitions are rejected, each on its   *)
(*      own wording: the witnesses swapped, and a reifier that is not  *)
(*      fresh. The second is the measurement behind the freshness      *)
(* precondition, i.e. behind "a model-declared reified bool       *)
   (*      cannot be defined by [red]". *)
(* ------------------------------------------------------------------ *)

(* r <-> (sum a_i x_i <= rhs), checked at every point of the (small) domains. The
   evaluator reads each order literal off the integer assignment and knows nothing
   about how [reif_rows] built either row, so a sign or big-M error that cancels
   itself inside the construction cannot hide from it. *)
let reif_semantics name ~domains ~terms ~rhs =
  let e = Encoding.create () in
  List.iter (fun (x, lo, hi) -> Encoding.declare_int e x ~lo ~hi) domains;
  Encoding.declare_bool e "r";
  let cond = Encoding.expand_int_lin_le e terms rhs in
  let fwd, bwd = Encoding.reif_rows ~reifier:"r" ~cond in
  let bad =
    List.find_opt
      (fun assign ->
        let cond_true =
          List.fold_left (fun acc (a, x) -> acc + (a * List.assoc x assign)) 0 terms
          <= rhs
        in
        let r_true = List.assoc "r" assign = 1 in
        let rows_hold = eval_row assign fwd && eval_row assign bwd in
        rows_hold <> (r_true = cond_true))
      (all_assignments (("r", 0, 1) :: domains))
  in
  check name (bad = None)

let test_reif_rows () =
  reif_semantics "reif: r <-> x <= 1, x in [0,3]"
    ~domains:[ ("x", 0, 3) ]
    ~terms:[ (1, "x") ]
    ~rhs:1;
  reif_semantics "reif: r <-> x + y <= 2"
    ~domains:[ ("x", 0, 2); ("y", 0, 2) ]
    ~terms:[ (1, "x"); (1, "y") ]
    ~rhs:2;
  reif_semantics "reif: r <-> 2x - y <= 1, mixed signs"
    ~domains:[ ("x", 0, 2); ("y", 0, 2) ]
    ~terms:[ (2, "x"); (-1, "y") ]
    ~rhs:1;
  reif_semantics "reif: r <-> x - y <= -1 over a domain that does not start at 0"
    ~domains:[ ("x", -1, 2); ("y", 1, 3) ]
    ~terms:[ (1, "x"); (-1, "y") ]
    ~rhs:(-1);
  (* The rendered pair, by eye against the header's formulas. x <= 1 over [0,3]
     normalises to  ~x_ge_1 + ~x_ge_2 + ~x_ge_3 >= 2,  so A = 3, k = 2, A-k+1 = 2. *)
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:3;
  let fwd, bwd =
    Encoding.reif_rows ~reifier:"r" ~cond:(Encoding.expand_int_lin_le e [ (1, "x") ] 1)
  in
  check_eq "reif: the forward row is the condition weakened by k ~r"
    ~expected:"+2 ~r_ge_1 +1 ~x_ge_1 +1 ~x_ge_2 +1 ~x_ge_3 >= 2 ;"
    ~got:(Opb.constr_to_string fwd);
  check_eq "reif: the backward row is the negated condition weakened by (A-k+1) r"
    ~expected:"+2 r_ge_1 +1 x_ge_1 +1 x_ge_2 +1 x_ge_3 >= 2 ;"
    ~got:(Opb.constr_to_string bwd)

(* ------------------------------------------------------------------ *)
(* M3-T2: the SAME two rows, posted as ordinary int_lin_le rows        *)
(*                                                                    *)
(* lib/proof/encoding.ml's [add_int_lin_le_reif_rows] exists because a *)
(* propagator cannot cite a row it cannot reproduce: [Linear] rebuilds *)
(* its row from integer terms and a right-hand side (M2-L6), not from  *)
(* literals. Its header claims the big-M form IS [reif_rows]'s pair.   *)
(* This performs that claim instead of leaving it to be believed -- if *)
(* the two ever drift, the .opb door would be saying two different     *)
(* things, which is exactly what [reif_rows] was made pure and shared  *)
(* to prevent.                                                        *)
(* ------------------------------------------------------------------ *)

(* A normalised row as a canonical string: the term ORDER differs between the two
   constructions ([reif_rows] puts the reifier first, [expand_int_lin_le] appends its
   rungs last) and a row is a sum, so order is not part of what is being compared. *)
let canonical c =
  let c = Opb.normalise c in
  let terms =
    List.sort compare
      (List.map (fun (a, l) -> Printf.sprintf "%+d %s" a (Lit.to_string l)) (Opb.terms c))
  in
  String.concat " " terms ^ Printf.sprintf " >= %d ;" (Opb.rhs c)

let same_rows name ~domains ~terms ~rhs =
  (* Door one: [reif_rows], over the condition as literals. *)
  let a = Encoding.create () in
  List.iter (fun (x, lo, hi) -> Encoding.declare_int a x ~lo ~hi) domains;
  Encoding.declare_bool a "r";
  let fwd, bwd =
    Encoding.reif_rows ~reifier:"r" ~cond:(Encoding.expand_int_lin_le a terms rhs)
  in
  (* Door two: the big-M rows M3-T2 posts, read back out of the encoding they were
     committed to. *)
  let b = Encoding.create () in
  List.iter (fun (x, lo, hi) -> Encoding.declare_int b x ~lo ~hi) domains;
  Encoding.declare_bool b "r";
  let k_fwd, k_bwd = Encoding.reif_big_m b terms rhs in
  let neg = List.map (fun (c, x) -> (-c, x)) terms in
  let big_fwd = Encoding.expand_int_lin_le b (terms @ [ (k_fwd, "r") ]) (rhs + k_fwd) in
  let big_bwd = Encoding.expand_int_lin_le b (neg @ [ (-k_bwd, "r") ]) (-rhs - 1) in
  check_eq (name ^ " (FWD)") ~expected:(canonical fwd) ~got:(canonical big_fwd);
  check_eq (name ^ " (BWD)") ~expected:(canonical bwd) ~got:(canonical big_bwd)

let test_reif_big_m_rows () =
  same_rows "reif big-M: r <-> x <= 1, x in [0,3]"
    ~domains:[ ("x", 0, 3) ]
    ~terms:[ (1, "x") ]
    ~rhs:1;
  same_rows "reif big-M: r <-> x + y <= 2"
    ~domains:[ ("x", 0, 2); ("y", 0, 2) ]
    ~terms:[ (1, "x"); (1, "y") ]
    ~rhs:2;
  same_rows "reif big-M: r <-> 2x - y <= 1, mixed signs"
    ~domains:[ ("x", 0, 2); ("y", 0, 2) ]
    ~terms:[ (2, "x"); (-1, "y") ]
    ~rhs:1;
  same_rows "reif big-M: r <-> x - y <= -1, domain not starting at 0"
    ~domains:[ ("x", -1, 2); ("y", 1, 3) ]
    ~terms:[ (1, "x"); (-1, "y") ]
    ~rhs:(-1);
  (* The big-Ms themselves, by eye against the header: x <= 1 over [0,3] has span
     (0, 3), so K = hi - rhs = 2 and K' = rhs + 1 - lo = 2 -- and those are the k and
     A-k+1 that [test_reif_rows] reads off the rendered pair above. *)
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:3;
  Encoding.declare_bool e "r";
  let k_fwd, k_bwd = Encoding.reif_big_m e [ (1, "x") ] 1 in
  check "reif big-M: the two constants are the smallest that work" (k_fwd = 2 && k_bwd = 2);
  (* A condition the declared domains already settle is not a reification, and the
     big-M door refuses it on the same terms [reif_rows] does. *)
  raises "reif big-M: an entailed condition is refused as constant" (fun () ->
      Encoding.add_int_lin_le_reif_rows e [ (1, "x") ] 3 ~reifier:"r");
  raises "reif big-M: a refuted condition is refused as constant" (fun () ->
      Encoding.add_int_lin_le_reif_rows e [ (1, "x") ] (-1) ~reifier:"r")

let test_reif_preconditions () =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:3;
  let cond rhs = Encoding.expand_int_lin_le e [ (1, "x") ] rhs in
  (* Constant on the coefficients alone: not a reification, a fixed Boolean. *)
  (match Encoding.reif_rows ~reifier:"r" ~cond:(cond 3) with
  | exception Encoding.Reif_constant ("r", true) ->
      print_endline "ok   reif: a condition the row cannot falsify is refused as constant"
  | (exception _) | _ ->
      incr failures;
      print_endline "FAIL reif: a vacuously true condition should raise Reif_constant");
  (match Encoding.reif_rows ~reifier:"r" ~cond:(cond (-1)) with
  | exception Encoding.Reif_constant ("r", false) ->
      print_endline "ok   reif: a condition the row cannot satisfy is refused as constant"
  | (exception _) | _ ->
      incr failures;
      print_endline "FAIL reif: an unsatisfiable condition should raise Reif_constant");
  (* b <-> C(b) is not a definition. *)
  Encoding.declare_bool e "r";
  raises "reif: a condition mentioning the reifier is refused" (fun () ->
      Encoding.reif_rows ~reifier:"r"
        ~cond:(Encoding.expand_int_lin_le e [ (1, "x"); (1, "r") ] 1));
  (* A reifier that is declared but is not a bool. *)
  raises "reif: a non-Boolean reifier is refused" (fun () ->
      Encoding.add_reif e ~reifier:"x" ~cond:(cond 1));
  (* An `=` condition is two constraints and cannot be one pair. *)
  raises "reif: an `=` condition is refused" (fun () ->
      Encoding.reif_rows ~reifier:"r" ~cond:(Opb.eq [ (1, Lit.ge "x" 1) ] 1));
  (* THE precondition: [define_reif] refuses a reifier the .opb already mentions, and
     refuses it BEFORE writing anything. The checker's own refusal of the same
     situation is [test_reif_veripb]'s "not fresh" lane -- this is the guard that means
     a caller never reaches it. *)
  let e2 = Encoding.create () in
  Encoding.declare_int e2 "x" ~lo:0 ~hi:3;
  Encoding.declare_bool e2 "b";
  ignore (Encoding.add_constraint e2 (Opb.ge [ (1, Lit.bool_true "b") ] 1));
  let w =
    Writer.create ~comments:false ~audit:false
      (let f = Filename.temp_file "baguette_reif" ".pbp" in
       let oc = open_out f in
       at_exit (fun () -> try Sys.remove f with _ -> ());
       oc)
  in
  Writer.header w ~n_model_constraints:(Encoding.n_constraints e2);
  (match
     Encoding.define_reif e2 w ~reifier:"b"
       ~cond:(Encoding.expand_int_lin_le e2 [ (1, "x") ] 1)
   with
  | exception Encoding.Reif_not_fresh "b" ->
      print_endline
        "ok   reif: define_reif refuses a reifier the .opb already constrains \
         (Reif_not_fresh)"
  | (exception _) | _ ->
      incr failures;
      print_endline "FAIL reif: define_reif accepted a non-fresh reifier");
  (* And a fresh one is accepted, so the guard above is not simply refusing
     everything -- the control that makes the refusal mean something. *)
  match
    Encoding.define_reif e2 w ~reifier:"$fresh"
      ~cond:(Encoding.expand_int_lin_le e2 [ (1, "x") ] 1)
  with
  | r ->
      check "reif: a fresh reifier is accepted and yields two ids"
        (List.length (Encoding.reif_ids r) = 2
        && Encoding.reif_fwd r <> Encoding.reif_bwd r
        && Lit.to_string (Encoding.reif_lit r) = "_fresh_ge_1")
  | exception _ ->
      incr failures;
      print_endline "FAIL reif: a fresh reifier was refused"

(* The witness-before-terminator trap, on the text [Writer.red] actually emits. The
   rule ends at the first `;`, so a witness written after one is SILENTLY not a
   witness -- the failure this pins is one that passes quietly. *)
let test_reif_emitted_text () =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:3;
  let s =
    text (fun w ->
        Writer.header w ~n_model_constraints:2;
        ignore (Encoding.define_reif_int_lin_le e w ~reifier:"$r" [ (1, "x") ] 1))
  in
  let lines =
    List.filter
      (fun l -> String.length l > 0 && String.contains l 'r' && String.length l > 4)
      (String.split_on_char '\n' s)
  in
  let red_lines =
    List.filter
      (fun l ->
        let l = String.trim l in
        let i = try Some (String.index l 'r') with Not_found -> None in
        match i with
        | Some i when i + 4 <= String.length l -> String.sub l i 4 = "red "
        | _ -> false)
      lines
  in
  check "reif: define_reif emits exactly two red lines" (List.length red_lines = 2);
  let well_formed l =
    (* exactly one `;`, at the end, and the witness separator before it *)
    let semis =
      List.length
        (List.filter (fun c -> c = ';') (List.init (String.length l) (String.get l)))
    in
    let colon = try String.index l ':' with Not_found -> -1 in
    let semi = try String.index l ';' with Not_found -> -1 in
    semis = 1 && semi = String.length (String.trim l) - 1 && colon >= 0 && colon < semi
  in
  check "reif: the witness comes BEFORE the terminator on every red line"
    (List.for_all (fun l -> well_formed (String.trim l)) red_lines);
  let has needle =
    List.exists
      (fun l ->
        String.length (String.trim l) >= String.length needle
        &&
        let t = String.trim l in
        let n = String.length needle in
        let rec go i =
          i + n <= String.length t && (String.sub t i n = needle || go (i + 1))
        in
        go 0)
      red_lines
  in
  check "reif: the forward half goes in first, under the witness that satisfies it"
    (has "+2 ~_r_ge_1 +1 ~x_ge_1 +1 ~x_ge_2 +1 ~x_ge_3 >= 2 : _r_ge_1 -> 0 ;");
  check "reif: the backward half goes in last, under the opposite witness"
    (has "+2 _r_ge_1 +1 x_ge_1 +1 x_ge_2 +1 x_ge_3 >= 2 : _r_ge_1 -> 1 ;")

(* THE LANE THAT VALIDATES THE DEFINITION, and the reason it looks the way it does.

   A [red] goal is discharged by showing F /\ ~C entails the substituted database. If F
   is itself contradictory, every goal discharges and EVERY witness is accepted --
   including a wrong one. That is measured below, not assumed, and it is why the
   definition is validated over a SATISFIABLE .opb: over a contradictory one, "veripb
   accepted the red line" says nothing whatever.

   The model here is therefore just x's ladder, x in [0, 3], which every value of x
   satisfies. The proof introduces the definition and then logs a solution -- so the
   two rows are checked twice over, once as redundance goals and once as constraints a
   concrete assignment has to satisfy. *)
let reif_sat_model dir name ~constrain_reifier =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:3;
  if constrain_reifier then (
    Encoding.declare_bool e "b";
    ignore (Encoding.add_constraint e (Opb.ge [ (1, Lit.bool_true "b") ] 1)));
  let opb = Filename.concat dir (name ^ ".opb") in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "x in [0,3]; satisfiable" ] e oc;
  close_out oc;
  (e, opb)

(* The model the two citation lanes refute:  x in [0,3],  x >= 3,  x <= 1.
   Contradictory, and deliberately contradictory in a way that has NOTHING to do with
   the reifier -- so a proof that routes the contradiction through the reifier is
   demonstrating the definition rather than being carried by it. *)
let reif_unsat_model dir name ~reifier_in_opb =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:3;
  let rows =
    if reifier_in_opb then (
      Encoding.declare_bool e "b";
      Some (Encoding.add_int_lin_le_reif e [ (1, "x") ] 1 ~reifier:"b"))
    else None
  in
  let c_hi = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "x" 3) ] 1) in
  let c_lo = Encoding.add_constraint e (Opb.ge [ (1, Lit.negate (Lit.ge "x" 2)) ] 1) in
  let opb = Filename.concat dir (name ^ ".opb") in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "x >= 3; x <= 1" ] e oc;
  close_out oc;
  (e, opb, rows, c_hi, c_lo)

(* The derivation, shared by both doors: it takes the two ids of the definition and
   knows nothing about where they came from. Both halves are load-bearing -- the
   contradiction IS `~r` against `r` -- and each direction's claim goes through
   [pol_concluding], so the checker judges the claim rather than accepting whatever the
   cutting-planes expression happened to evaluate to. A big-M off by one shows up
   exactly there. *)
let refute_through_reifier e w ~reifier ~fwd ~bwd ~c_hi ~c_lo =
  let r = Lit.bool_true reifier in
  let cons1 = Option.get (Encoding.consistency_id e "x" 1) in
  let cons2 = Option.get (Encoding.consistency_id e "x" 2) in
  let x_ge_2 =
    Writer.pol w ~origin:"x >= 3 gives x >= 2" Pol.(sum [ id c_hi; id cons2 ])
  in
  let x_ge_1 =
    Writer.pol w ~origin:"x >= 2 gives x >= 1" Pol.(sum [ id x_ge_2; id cons1 ])
  in
  (* Forward half: x >= 3 falsifies the condition, so the reifier is false. *)
  let not_r =
    Writer.pol_concluding w ~origin:"x >= 3 falsifies x <= 1, so ~r"
      ~claim:(Opb.ge [ (1, Lit.negate r) ] 1)
      Pol.(div (sum [ id fwd; id x_ge_1; id x_ge_2; id c_hi ]) 2)
  in
  (* Backward half: x <= 1 satisfies the condition, so the reifier is true. *)
  let not_x_ge_3 =
    Writer.pol w ~origin:"x <= 1 gives x <= 2" Pol.(sum [ id c_lo; id cons2 ])
  in
  let yes_r =
    Writer.pol_concluding w ~origin:"x <= 1 satisfies x <= 1, so r"
      ~claim:(Opb.ge [ (1, r) ] 1)
      Pol.(
        div (sum [ id bwd; id c_lo; id not_x_ge_3; axiom (Lit.negate (Lit.ge "x" 1)) ]) 2)
  in
  let contra =
    Writer.pol w ~origin:"the reifier cannot be both" Pol.(sum [ id not_r; id yes_r ])
  in
  Writer.delete_many w [ x_ge_1; x_ge_2; not_x_ge_3; not_r; yes_r ];
  contra

let test_reif_veripb () =
  match veripb_path () with
  | None ->
      incr failures;
      print_endline
        ("FAIL M3-T1 reif: " ^ Baguette_proof.Checker.not_found_message
       ^ " -- a red-based definition nothing checked is not a definition.")
  | Some veripb -> (
      let dir = Filename.temp_file "baguette_reif_veripb" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      let log = Filename.concat dir "log" in
      let run opb pbp = run_checker ~checker:veripb ~opb ~pbp ~log = Some true in
      let says needle =
        let out = try read_whole log with _ -> "" in
        let n = String.length needle in
        let rec go i =
          i + n <= String.length out && (String.sub out i n = needle || go (i + 1))
        in
        go 0
      in
      let rejected_saying name ~opb ~pbp ~needle =
        if run opb pbp then (
          incr failures;
          Printf.printf "FAIL %s (veripb ACCEPTED it)\n  model: %s\n  proof: %s\n" name
            opb pbp)
        else if says needle then Printf.printf "ok   %s\n" name
        else (
          incr failures;
          Printf.printf
            "FAIL %s -- it was rejected, but not on %S, so this lane cannot tell a \
             JUDGEMENT from a parse error\n\
             %s\n"
            name needle
            (try read_whole log with _ -> ""))
      in
      (* ---------------- the definition, over a satisfiable model ---------------- *)
      let e, opb = reif_sat_model dir "def" ~constrain_reifier:false in
      let pbp = Filename.concat dir "def.pbp" in
      let oc = open_out pbp in
      (* No audit: the two definition ids are deliberately still live at the [sol], so
         that the logged solution has to satisfy them. *)
      let w = Writer.create ~comments:true ~audit:false oc in
      Encoding.start_proof e w;
      ignore (Encoding.define_reif_int_lin_le e w ~reifier:"$r" [ (1, "x") ] 1);
      Writer.conclusion w
        (Writer.Sat (Encoding.assignment_lits e [ ("x", 3); ("$r", 0) ]));
      close_out oc;
      check
        "M3-T1: veripb accepts a red-defined reifier over a SATISFIABLE model -- the \
         redundance goals are real here, and the logged solution satisfies both rows"
        (run opb pbp);
      if not (run opb pbp) then
        Printf.printf "  model: %s\n  proof: %s\n%s\n" opb pbp
          (try read_whole log with _ -> "");
      let accepted_text = read_whole pbp in
      let rewrite name f =
        let path = Filename.concat dir (name ^ ".pbp") in
        let oc = open_out path in
        output_string oc
          (String.concat "\n" (List.map f (String.split_on_char '\n' accepted_text)));
        close_out oc;
        path
      in
      let is_red l =
        let t = String.trim l in
        let n = String.length t in
        let rec go i = i + 4 <= n && (String.sub t i 4 = "red " || go (i + 1)) in
        go 0
      in
      let ends_with suf l =
        let n = String.length suf and m = String.length l in
        m >= n && String.sub l (m - n) n = suf
      in
      (* (a) the two witnesses swapped. The forward half under `-> 1` asserts the
         condition outright, which x's ladder alone does not entail. *)
      let swapped =
        rewrite "swapped" (fun l ->
            if is_red l then
              String.sub l 0 (String.length l - 6)
              ^ if ends_with "-> 0 ;" l then "-> 1 ;" else "-> 0 ;"
            else l)
      in
      rejected_saying
        "M3-T1: veripb REJECTS the definition with its two witnesses swapped" ~opb
        ~pbp:swapped ~needle:"Proofgoal #1 could not be autoproven";
      (* (b) the forward half's big-M one too small. Still a definition-shaped line,
         still well formed, and now too strong -- the constant is not decoration. *)
      let small_m =
        rewrite "small_m" (fun l ->
            if is_red l && ends_with "-> 0 ;" l then
              let rec replace i =
                if i + 3 > String.length l then l
                else if String.sub l i 3 = "+2 " then
                  String.sub l 0 i ^ "+1 " ^ String.sub l (i + 3) (String.length l - i - 3)
                else replace (i + 1)
              in
              replace 0
            else l)
      in
      rejected_saying "M3-T1: veripb REJECTS a forward half whose big-M is one too small"
        ~opb ~pbp:small_m ~needle:"Proofgoal #1 could not be autoproven";
      (* (c) the witness after the terminator -- the trap lib/proof/opb.ml:74 records.
         It is SILENTLY not a witness: 3.0.2 emits "A witness must be specified for the
         red-rule" as a WARNING and carries on, and what fails is the redundance goal
         further down. Over a contradictory model even that goal discharges -- see the
         last lane of this function -- so a witness written after the `;` would be
         accepted with nothing but a warning. Only the wording says which failure this
         is, which is why it is the wording that is asserted. *)
      let after_semi =
        rewrite "after_semi" (fun l ->
            if is_red l then
              match String.index_opt l ':' with
              | Some i ->
                  let body = String.sub l 0 i in
                  let w = String.trim (String.sub l (i + 1) (String.length l - i - 1)) in
                  body ^ "; " ^ String.sub w 0 (max 0 (String.length w - 1))
              | None -> l
            else l)
      in
      rejected_saying
        "M3-T1: veripb REJECTS a red whose witness sits after the terminator" ~opb
        ~pbp:after_semi ~needle:"A witness must be specified for the red-rule";
      (* (d) a reifier the .opb already constrains. THE measurement behind the
         freshness precondition: the witness has to discharge that row under the
         substitution and cannot. It is why a model-declared reified bool gets its
         meaning from a .opb row and never from a `red`. [define_reif] refuses this
         outright, so the rows are emitted by hand -- the point is that the CHECKER
         answers, not our guard. *)
      let e2, opb2 = reif_sat_model dir "notfresh" ~constrain_reifier:true in
      let pbp2 = Filename.concat dir "notfresh.pbp" in
      let oc = open_out pbp2 in
      let w2 = Writer.create ~comments:true ~audit:false oc in
      Encoding.start_proof e2 w2;
      let fwd2, bwd2 =
        Encoding.reif_rows ~reifier:"b"
          ~cond:(Encoding.expand_int_lin_le e2 [ (1, "x") ] 1)
      in
      let bv = (Lit.bool_true "b").Lit.v in
      ignore (Writer.red w2 ~origin:"by hand" ~witness:[ (bv, Writer.Zero) ] fwd2);
      ignore (Writer.red w2 ~origin:"by hand" ~witness:[ (bv, Writer.One) ] bwd2);
      Writer.conclusion w2 (Writer.Sat (Encoding.assignment_lits e2 [ ("x", 0) ]));
      close_out oc;
      rejected_saying
        "M3-T1: veripb REJECTS a red-defined reifier the .opb already constrains -- the \
         freshness precondition is the checker's, not ours"
        ~opb:opb2 ~pbp:pbp2 ~needle:"Proofgoal 3 could not be autoproven";
      (* ---------------- the definition, cited ---------------- *)
      (* A definition nothing cites is not evidence. Here the contradiction is derived
         THROUGH the reifier: `~r` from the forward half, `r` from the backward half,
         and those two against each other. *)
      let e3, opb3, _, c_hi3, c_lo3 = reif_unsat_model dir "lazy" ~reifier_in_opb:false in
      let pbp3 = Filename.concat dir "lazy.pbp" in
      let oc = open_out pbp3 in
      let w3 = Writer.create ~comments:true ~audit:true oc in
      Encoding.start_proof e3 w3;
      let r3 = Encoding.define_reif_int_lin_le e3 w3 ~reifier:"$r" [ (1, "x") ] 1 in
      let contra3 =
        refute_through_reifier e3 w3 ~reifier:"$r" ~fwd:(Encoding.reif_fwd r3)
          ~bwd:(Encoding.reif_bwd r3) ~c_hi:c_hi3 ~c_lo:c_lo3
      in
      Encoding.retire_reif w3 r3;
      Writer.conclusion w3 (Writer.Unsat (Some contra3));
      close_out oc;
      check
        "M3-T1: veripb accepts a refutation derived THROUGH a red-defined reifier, both \
         halves cited"
        (run opb3 pbp3);
      if not (run opb3 pbp3) then
        Printf.printf "  model: %s\n  proof: %s\n%s\n" opb3 pbp3
          (try read_whole log with _ -> "");
      (* The same derivation, over the SAME rows, reached through the .opb door: this
         is what a model-declared reified bool looks like, and it is the check that the
         two doors really do agree about the encoding. *)
      let e4, opb4, rows4, c_hi4, c_lo4 =
        reif_unsat_model dir "eager" ~reifier_in_opb:true
      in
      let fwd4, bwd4 = Option.get rows4 in
      let pbp4 = Filename.concat dir "eager.pbp" in
      let oc = open_out pbp4 in
      let w4 = Writer.create ~comments:true ~audit:true oc in
      Encoding.start_proof e4 w4;
      let contra4 =
        refute_through_reifier e4 w4 ~reifier:"b" ~fwd:fwd4 ~bwd:bwd4 ~c_hi:c_hi4
          ~c_lo:c_lo4
      in
      Writer.conclusion w4 (Writer.Unsat (Some contra4));
      close_out oc;
      check
        "M3-T1: the same derivation over the same two rows is accepted when they are \
         .opb rows instead -- the two doors agree"
        (run opb4 pbp4);
      (* THE FINDING THAT SHAPES THIS WHOLE TEST, pinned so it cannot quietly stop
         being true: over a CONTRADICTORY .opb the swapped-witness definition above is
         ACCEPTED. Every redundance goal discharges from a contradictory database, so
         "veripb accepted the red line" is not evidence unless the model is
         satisfiable. This is the reason lane (a) does not live here. *)
      let pbp5 = Filename.concat dir "vacuous.pbp" in
      let oc = open_out pbp5 in
      let w5 = Writer.create ~comments:true ~audit:true oc in
      Encoding.start_proof e3 w5;
      let bad = (Lit.bool_true "$q").Lit.v in
      let fwd5, bwd5 =
        Encoding.reif_rows ~reifier:"$q"
          ~cond:(Encoding.expand_int_lin_le e3 [ (1, "x") ] 1)
      in
      (* Both witnesses wrong, on purpose. *)
      let a5 = Writer.red w5 ~origin:"wrong" ~witness:[ (bad, Writer.One) ] fwd5 in
      let b5 = Writer.red w5 ~origin:"wrong" ~witness:[ (bad, Writer.Zero) ] bwd5 in
      let cons2 = Option.get (Encoding.consistency_id e3 "x" 2) in
      let x_ge_2 = Writer.pol w5 ~origin:"x >= 2" Pol.(sum [ id c_hi3; id cons2 ]) in
      let contra5 =
        Writer.pol w5 ~origin:"x >= 2 against x <= 1" Pol.(sum [ id x_ge_2; id c_lo3 ])
      in
      Writer.delete_many w5 [ a5; b5; x_ge_2 ];
      Writer.conclusion w5 (Writer.Unsat (Some contra5));
      close_out oc;
      check
        "M3-T1 (measured, and the reason the definition lane uses a satisfiable model): \
         over a CONTRADICTORY .opb veripb accepts a red whose witnesses are both wrong"
        (run opb3 pbp5);
      Sys.readdir dir
      |> Array.iter (fun f -> try Sys.remove (Filename.concat dir f) with _ -> ());
      try Sys.rmdir dir with _ -> ())

(* Say which checker every I-X1 check in the suite is talking to, and its version.
   "veripb accepted it" is only meaningful if you know which veripb, and until M1-T18
   the answer was whichever build happened to come first on PATH -- which on the
   development machine was not the one intended. *)
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

(* ------------------------------------------------------------------ *)
(* Views (M4-T0)                                                       *)
(*                                                                     *)
(* A view [+/-x + k] gets NO PB variables of its own; it renders onto   *)
(* its base's order literals. lib/proof/lit.ml's "Views" section        *)
(* records the decision and what minting [y_ge_v] would have cost. The  *)
(* tests here are the three halves of that claim:                      *)
(*                                                                     *)
(*   the names  -- the rendering is exactly the base's literal, and     *)
(*                 PROOF-FORMAT section 3's scheme gains no second      *)
(*                 spelling;                                           *)
(*   the trim   -- [Encoding.view_ge] reaches [Holds]/[Fails] through   *)
(*                 the SAME two comparisons [Encoding.ge] makes;        *)
(*   the truth  -- veripb accepts a derivation written in a view's      *)
(*                 literals over a model written in the base's, and     *)
(*                 REJECTS one whose rendering is wrong (below).        *)
(* ------------------------------------------------------------------ *)

let up3 = Lit.shift Lit.identity 3 (* x + 3 *)
let rev7 = Lit.flip (Lit.shift Lit.identity (-7)) (* 7 - x *)

let test_view_lits () =
  check "view lit: the identity view renders as the plain literal"
    (Lit.to_string (Lit.view_ge "x" Lit.identity 3) = "x_ge_3");
  check_eq "view lit: [x+3 >= 5] IS [x >= 2]" ~expected:"x_ge_2"
    ~got:(Lit.to_string (Lit.view_ge "x" up3 5));
  check_eq "view lit: [x+3 <= 5] IS [x <= 2], the negated order literal"
    ~expected:"~x_ge_3"
    ~got:(Lit.to_string (Lit.view_le "x" up3 5));
  (* The sign flip turns a lower bound on the view into an UPPER bound on the base.
     This is the step an implementation gets right for the offset and wrong for the
     sense, so both directions are pinned. *)
  check_eq "view lit: [7-x >= 5] IS [x <= 2]" ~expected:"~x_ge_3"
    ~got:(Lit.to_string (Lit.view_ge "x" rev7 5));
  check_eq "view lit: [7-x <= 5] IS [x >= 2]" ~expected:"x_ge_2"
    ~got:(Lit.to_string (Lit.view_le "x" rev7 5));
  check_eq "view lit: a view's equality is the base's, at the translated value"
    ~expected:"x_eq_2"
    ~got:(Lit.to_string (Lit.view_eq "x" up3 5));
  check_eq "view lit: ... and through the mirror too" ~expected:"~x_eq_2"
    ~got:(Lit.to_string (Lit.view_ne "x" rev7 5));
  check "view lit: negative translated values still avoid '-'"
    (Lit.to_string (Lit.view_ge "x" up3 1) = "x_ge_m2");

  (* No new name exists, so there is nothing for [sanitize] to collide. That matters
     because [sanitize] is NON-INJECTIVE and M2-T9 found that keying on rendered names
     is a silent bug: these two distinct FlatZinc identifiers share one OPB name. A
     view of each must still be two different facts. *)
  let a = Lit.view_ge "a-b" up3 5 and b = Lit.view_ge "a_b" up3 5 in
  check "view lit: two bases that COLLIDE under sanitize render the same OPB name"
    (Lit.to_string a = Lit.to_string b);
  check
    "view lit: ... and are nonetheless distinct literals -- a view carries its base's \
     identifier, not its rendered name"
    (not (Lit.equal a b));
  check "view lit: the transform is applied to the VALUE, so the owner is untouched"
    (Lit.owner a.Lit.v = "a-b" && Lit.owner b.Lit.v = "a_b");

  (* The algebra: a view of a view is a view, flat. *)
  check "view lit: -(x-7) is 7-x"
    (Lit.affine_equal rev7 (Lit.flip (Lit.shift Lit.identity (-7))));
  check "view lit: shifting composes"
    (Lit.affine_equal (Lit.shift up3 2) (Lit.shift Lit.identity 5));
  check "view lit: flipping twice is the identity map"
    (Lit.affine_equal (Lit.flip (Lit.flip up3)) up3);
  check "view lit: apply and unapply are inverse, both signs"
    (List.for_all
       (fun a ->
         List.for_all (fun v -> Lit.unapply a (Lit.apply a v) = v) [ -3; 0; 4; 9 ])
       [ Lit.identity; up3; rev7 ]);
  check "view lit: is_identity only of the identity"
    (Lit.is_identity Lit.identity
    && (not (Lit.is_identity up3))
    && not (Lit.is_identity rev7))

let test_view_encoding () =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:5;
  let up = Encoding.View ("x", up3) (* x+3, so 3..8 *) in
  let rev = Encoding.View ("x", rev7) (* 7-x, so 2..7 *) in
  let c = Encoding.view_const 4 in
  let str = function
    | Encoding.Holds -> "Holds"
    | Encoding.Fails -> "Fails"
    | Encoding.Cond l -> Lit.to_string l
  in
  check "view enc: a view's declared range is the image of the base's"
    (Encoding.view_domain e up = (3, 8) && Encoding.view_domain e rev = (2, 7));
  check "view enc: a constant's declared range is itself"
    (Encoding.view_domain e c = (4, 4));

  (* The trim: the constants of PROOF-FORMAT section 3 ("x >= l is the constant true,
     x >= u+1 the constant false") reach a view through the base's declaration, not
     through a second copy of the rule. *)
  check_eq "view enc: at the view's own lower bound, [view >= lo] Holds" ~expected:"Holds"
    ~got:(str (Encoding.view_ge e up 3));
  check_eq "view enc: one past its upper bound, [view >= hi+1] Fails" ~expected:"Fails"
    ~got:(str (Encoding.view_ge e up 9));
  check_eq "view enc: in between, the base's literal" ~expected:"x_ge_2"
    ~got:(str (Encoding.view_ge e up 5));
  check_eq "view enc: a NEGATED view's lower bound Holds too" ~expected:"Holds"
    ~got:(str (Encoding.view_ge e rev 2));
  check_eq "view enc: ... and its upper bound Fails on the other side" ~expected:"Fails"
    ~got:(str (Encoding.view_ge e rev 8));
  check_eq "view enc: a negated view in between is a negated base literal"
    ~expected:"~x_ge_3"
    ~got:(str (Encoding.view_ge e rev 5));
  check_eq "view enc: view_le mirrors view_ge" ~expected:"~x_ge_3"
    ~got:(str (Encoding.view_le e up 5));
  check_eq "view enc: view_lt/view_gt are the off-by-one spellings" ~expected:"x_ge_2"
    ~got:(str (Encoding.view_gt e up 4));

  (* A constant never reaches [find], so it is never [Undeclared] and contributes
     nothing to the .opb. It is decided by comparing two integers. *)
  check "view enc: a constant's bound is arithmetic, not a lookup"
    (Encoding.view_ge e c 4 = Encoding.Holds
    && Encoding.view_ge e c 5 = Encoding.Fails
    && Encoding.view_le e c 4 = Encoding.Holds
    && Encoding.view_le e c 3 = Encoding.Fails
    && Encoding.view_eq e c 4 = Encoding.Holds
    && Encoding.view_ne e c 4 = Encoding.Fails);
  check "view enc: a view of an UNDECLARED base is refused, like the variable it is"
    (match Encoding.view_ge e (Encoding.View ("nope", up3)) 5 with
    | exception Encoding.Undeclared "nope" -> true
    | _ -> false);
  check "view enc: declaring nothing extra -- a view adds no constraint to the .opb"
    (Encoding.n_constraints e = 4 (* x's four ladder rungs, and nothing else *));
  check "view enc: a view's equality needs the BASE's direct encoding, and says so"
    (match Encoding.view_eq e up 5 with
    | exception Encoding.No_direct_encoding "x" -> true
    | _ -> false);
  (* Composition on the encoding side agrees with the core side. *)
  check "view enc: view_shift and view_negate stay flat"
    (Encoding.view_shift (Encoding.view_of_var "x") 3 = up
    && Encoding.view_shift (Encoding.view_negate (Encoding.view_of_var "x")) 7 = rev
    && Encoding.view_shift (Encoding.view_const 4) 3 = Encoding.view_const 7)

(* --------------------------------------------------------------------------
   (c) The checker's half.

   The model is written entirely in the BASE's literals. The derivation is written
   entirely in a VIEW's. If the rendering is the identity it claims to be, veripb
   accepts; if it is off, veripb has to refuse, and the refusal has to be a JUDGEMENT
   on the derivation rather than a complaint about the file.

   Over a SATISFIABLE model, deliberately. A derivation checked against a database
   that is already contradictory proves nothing about the derivation (D-0053 makes
   the point for [red]; it is the same trap here, since anything at all is RUP from a
   contradiction). So: x is pinned to 1 by two rows, the proof states four facts
   about two views of x, and the conclusion is SAT with x = 1 -- which the derived
   lines must therefore also satisfy.
   -------------------------------------------------------------------------- *)
let test_view_veripb () =
  match veripb_path () with
  | None ->
      incr failures;
      print_endline
        ("FAIL M4-T0 views: " ^ Baguette_proof.Checker.not_found_message
       ^ " -- a view rendering nothing checked is not a rendering, it is a hope.")
  | Some veripb -> (
      let dir = Filename.temp_file "baguette_view_veripb" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      let log = Filename.concat dir "log" in
      (* x in 0..5, pinned to 1 by two rows. Declared width 5: the order encoding is
         width-proportional (D-0028) and this suite shares a 15 GB machine. *)
      let model name =
        let e = Encoding.create () in
        Encoding.declare_int e "x" ~lo:0 ~hi:5;
        ignore (Encoding.add_int_lin_le e [ (1, "x") ] 1);
        ignore (Encoding.add_int_lin_le e [ (-1, "x") ] (-1));
        let opb = Filename.concat dir (name ^ ".opb") in
        let oc = open_out opb in
        Encoding.write_opb e oc;
        close_out oc;
        (e, opb)
      in
      (* [lits] are emitted as one-literal [rup] clauses, then SAT with x = 1. *)
      let proof name ~e ~lits =
        let pbp = Filename.concat dir (name ^ ".pbp") in
        let oc = open_out pbp in
        let w = Writer.create ~comments:true ~audit:false oc in
        Encoding.start_proof e w;
        List.iter (fun l -> ignore (Writer.rup_clause w ~origin:"view" [ l ])) lits;
        Writer.conclusion w (Writer.Sat (Encoding.assignment_lits e [ ("x", 1) ]));
        close_out oc;
        pbp
      in
      let says needle =
        let out = try read_whole log with _ -> "" in
        let n = String.length needle in
        let rec go i =
          i + n <= String.length out && (String.sub out i n = needle || go (i + 1))
        in
        go 0
      in
      let run opb pbp = run_checker ~checker:veripb ~opb ~pbp ~log = Some true in

      (* The view under test: y = x+3 (so y = 4), z = 7-x (so z = 6). Every literal
         below is produced by [Lit.view_ge]/[Lit.view_le] -- nothing is hand-written,
         or the lane would be testing the test. *)
      let e, opb = model "ok" in
      let good =
        [
          Lit.view_ge "x" up3 4 (* y >= 4  IS  x >= 1 *);
          Lit.view_le "x" up3 4 (* y <= 4  IS  x <= 1 *);
          Lit.view_ge "x" rev7 6 (* z >= 6  IS  x <= 1 *);
          Lit.view_le "x" rev7 6 (* z <= 6  IS  x >= 1 *);
        ]
      in
      (* The renderings of [y >= 4] and [z <= 6] are the SAME literal, because both
         say x >= 1. A rendering that minted per-view Booleans could not say that
         without a channelling row. *)
      check "M4-T0 (c): two views of one base render the same fact to one literal"
        (Lit.equal (List.nth good 0) (List.nth good 3)
        && Lit.equal (List.nth good 1) (List.nth good 2));
      let good_prefix = [ List.nth good 0; List.nth good 1; List.nth good 2 ] in
      let pbp = proof "ok" ~e ~lits:good in
      check
        "M4-T0 (c): veripb accepts a derivation written in TWO views' literals over a \
         model written in the base's, on a SATISFIABLE model"
        (run opb pbp);
      if not (run opb pbp) then
        Printf.printf "  model: %s\n  proof: %s\n%s\n" opb pbp
          (try read_whole log with _ -> "");

      (* A break lane. The three CORRECT view literals go in first and the wrong one
         last, so that a rejection at the last line says more than "something was
         refused": the three renderings before it were accepted, and it is this claim
         the checker judged.

         Asserted at full strength, which on VeriPB 3.0.2 means two things together.
         The Rust checker does not quote the offending constraint back -- it says
         "Verification error at <file>:<line>" and then names the judgement -- so an
         assertion on the judgement alone would be matched by ANY RUP failure in the
         proof, which is the weakness CLAUDE.md names. The lane therefore locates the
         wrong literal's own line in the .pbp it wrote and requires the checker to
         have failed on THAT line, on the RUP judgement, in the checker's full
         sentence. A parse error, a dangling label or a refusal on the grammar names
         neither. *)
      let rejected_at name ~file ~wrong =
        let e, opb = model file in
        let pbp = proof file ~e ~lits:(good_prefix @ [ wrong ]) in
        let lines = String.split_on_char '\n' (read_whole pbp) in
        let rendered = Lit.to_string wrong in
        let contains needle hay =
          let n = String.length needle and h = String.length hay in
          let rec go i = i + n <= h && (String.sub hay i n = needle || go (i + 1)) in
          n = 0 || go 0
        in
        let line_of =
          let rec go i = function
            | [] -> 0
            | l :: rest ->
                if contains "rup" l && contains (" " ^ rendered ^ " ") (l ^ " ") then i
                else go (i + 1) rest
          in
          go 1 lines
        in
        let judgement =
          "The constraint is not implied by reverse unit propagation (RUP) from core and \
           derived database."
        in
        let at = Printf.sprintf "%s:%d" pbp line_of in
        if line_of = 0 then (
          incr failures;
          Printf.printf "FAIL %s -- the lane could not find %s in the proof it wrote\n"
            name rendered)
        else if run opb pbp then (
          incr failures;
          Printf.printf "FAIL %s (veripb ACCEPTED it)\n  model: %s\n  proof: %s\n" name
            opb pbp)
        else if says at && says judgement then Printf.printf "ok   %s\n" name
        else (
          incr failures;
          Printf.printf
            "FAIL %s -- it was rejected, but not as a RUP judgement on %s, so this lane \
             cannot tell a JUDGEMENT from a parse error\n\
             %s\n"
            name at
            (try read_whole log with _ -> ""))
      in
      (* Break 1: the offset dropped. [y >= 4] rendered as [x_ge_4] -- the mistake of
         naming the view's own value on the base's ladder. In range, well-formed, and
         FALSE here, so the checker must judge it rather than refuse to read it. *)
      rejected_at "M4-T0 (c): veripb REJECTS a view literal whose offset was dropped"
        ~file:"drop_offset" ~wrong:(Lit.ge "x" 4);
      (* Break 2: the sense of the negated view off by one. [z >= 6] is [x <= 1], which
         is [~x_ge_2]; [~x_ge_1] is [x <= 0]. This is the [le x v = ~(x >= v+1)] step,
         and it is the error that stays IN RANGE -- the one a lane matching on an exit
         status, or on a name that does not exist in the .opb, would never reach. *)
      rejected_at
        "M4-T0 (c): veripb REJECTS a negated view's literal that is off by one rung"
        ~file:"off_by_a_rung"
        ~wrong:(Lit.negate (Lit.ge "x" 1));
      Sys.readdir dir
      |> Array.iter (fun f -> try Sys.remove (Filename.concat dir f) with _ -> ());
      try Sys.rmdir dir with _ -> ())

(* ------------------------------------------------------------------ *)
(* M5-T1/M5-T2: optimisation                                           *)
(*                                                                     *)
(* Every claim M5 rests on about `soli`, `obju` and `conclusion        *)
(* BOUNDS` is made here by running the checker, which is this file's   *)
(* charter. Two of them are the ones that decide whether the milestone *)
(* proves anything at all:                                             *)
(*                                                                     *)
(*   - `conclusion BOUNDS <lo>` is CHECKED. The project has been bitten *)
(*     three times by a step the checker accepts whatever it derives    *)
(* (a `pol` under a clause-borne refutation), so "veripb said       *)
   (*     VERIFIED BOUNDS" is worth nothing until the claim has been shown *)
(*     to redden when the derivation is removed and when it is one unit *)
(*     short. Both breaks are performed below.                         *)
(*   - a `soli` constraint is NOT ours to delete, and the deletion is   *)
(*     refused rather than merely inadvisable.                         *)
(* ------------------------------------------------------------------ *)

(* The scene, built through the project's own [Encoding] rather than typed out as OPB
   text, so that a change to the order encoding moves this test with it.

     x, y in 0..3,  x <= y,  x >= 2,  minimise y

   The optimum is y = 2, and the point of the scene is that NO SINGLE ROW implies it:
   the x <= y row alone says nothing about y's magnitude and the x >= 2 row mentions no
   y at all. Their sum does -- the x literals cancel against the ladder-free `~x_ge_k`
   of the first row and leave `y_ge_1 + y_ge_2 + y_ge_3 >= 2`, which is exactly the
   objective. So a lower bound of 2 has to be DERIVED here, and [break_undeduced] below
   is meaningful rather than vacuous. *)
let m5_scene dir =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:3;
  Encoding.declare_int e "y" ~lo:0 ~hi:3;
  let le = Encoding.add_int_lin_le e [ (1, "x"); (-1, "y") ] 0 in
  let lo = Encoding.add_int_lin_le e [ (-1, "x") ] (-2) in
  let terms, constant = Encoding.linear_terms_int_lin_le e [ (1, "y") ] in
  Encoding.set_objective e (Opb.objective ~constant terms);
  let opb = Filename.concat dir "m5.opb" in
  let oc = open_out opb in
  Encoding.write_opb e oc;
  close_out oc;
  let sol =
    String.concat " "
      (List.map Lit.to_string (Encoding.assignment_lits e [ ("x", 2); ("y", 2) ]))
  in
  (opb, Opb.n_checker_constraints (Encoding.constraints e), sol, le, lo)

let test_m5_bounds_and_soli () =
  match veripb_path () with
  | None ->
      incr failures;
      print_endline
        "FAIL M5: veripb not found -- `conclusion BOUNDS` was NOT checked, and neither \
         were its breaks. A missing checker is a failure, never a skip."
  | Some checker -> (
      let dir = Filename.temp_file "baguette_m5" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      let opb, f_count, sol, le, lo = m5_scene dir in
      (* The lower-bound derivation: the two model rows added together. [2 d] on top of
         it divides by two and rounds up, giving `y_ge_* >= 1` -- sound, and exactly one
         unit short of the claim, which is the M1-T44 shape. *)
      let lb = Printf.sprintf "@lb pol @c%d @c%d + ;" le lo in
      let weak = Printf.sprintf "@weak pol @c%d @c%d + 2 d ;" le lo in
      let run name body conclusion ~flags =
        let pbp = Filename.concat dir (name ^ ".pbp") in
        let oc = open_out pbp in
        Printf.fprintf oc
          "pseudo-Boolean proof version 3.0\n\
           f %d ;\n\
           @s1 soli %s ;\n\
           %s\n\
           output NONE ;\n\
           %s\n\
           end pseudo-Boolean proof ;\n"
          f_count sol body conclusion;
        close_out oc;
        let log = Filename.concat dir (name ^ ".log") in
        let rc =
          Sys.command
            (Printf.sprintf "%s %s %s %s > %s 2>&1" (Filename.quote checker) flags
               (Filename.quote opb) (Filename.quote pbp) (Filename.quote log))
        in
        (rc = 0, read_whole log)
      in
      let says hay needle =
        let hl = String.length hay and nl = String.length needle in
        let rec go i = i + nl <= hl && (String.sub hay i nl = needle || go (i + 1)) in
        go 0
      in
      (* THE CONTROL. Without it every rejection below could be a rejection of the
         scene rather than of the break -- M2-T14 found four lanes green because a
         malformed artefact was refused on the grammar. *)
      let ok, out = run "control" lb "conclusion BOUNDS 2 : @lb 2 ;" ~flags:"" in
      check "M5 control: the honest proof verifies, BOUNDS 2 <= obj <= 2" ok;
      check "M5 control: ... and the checker says so in its own words"
        (says out "VERIFIED BOUNDS 2 <= obj <= 2");
      (* BREAK 1: the lower bound is claimed with nothing on the page that implies it.
         If this were accepted, every `conclusion BOUNDS` this solver emits would be
         decorative and M5-T2 would prove nothing. *)
      let ok, out = run "undeduced" "" "conclusion BOUNDS 2 2 ;" ~flags:"" in
      check "M5 BREAK: an underived lower bound is REFUSED" (not ok);
      check "M5 BREAK: ... on the judgement, at full strength"
        (says out
           "Constraint not syntactically implied by any constraint in the database.");
      (* BREAK 2: a derivation that is sound but one unit short, cited for the stronger
         claim. This is the break that distinguishes "the id is read" from "an id is
         present": break 1 alone would still pass if the checker merely searched the
         database and found something. *)
      let ok, out = run "one_short" weak "conclusion BOUNDS 2 : @weak 2 ;" ~flags:"" in
      check "M5 BREAK: a lower bound one unit stronger than the cited id is REFUSED"
        (not ok);
      check "M5 BREAK: ... naming the hint, at full strength"
        (says out
           "Expected constraint is not syntactically implied by the constraint at the \
            hint.");
      (* BREAK 3: claiming a better optimum than was ever exhibited. *)
      let ok, out = run "too_good" lb "conclusion BOUNDS 3 : @lb 3 ;" ~flags:"" in
      check "M5 BREAK: a lower bound above the best logged solution is REFUSED" (not ok);
      check "M5 BREAK: ... at full strength"
        (says out
           "The lower bound claimed for `conclusion BOUNDS` is larger than the best \
            logged objective value.");
      (* BREAK 4: deleting the `soli` constraint, which is what I-X2's sweep would do if
         [Writer.improving]'s id were treated like any other. By default it is a WARNING
         and the proof still verifies -- which is the dangerous part, and why this lane
         asserts the warning text rather than the exit status. Under
         --force-checked-deletion it is a hard failure. *)
      let body = lb ^ "\ndel id @s1 ;" in
      let ok, out = run "del_soli" body "conclusion BOUNDS 2 : @lb 2 ;" ~flags:"" in
      check
        "M5: deleting the soli constraint still 'verifies' -- an acceptance that is not \
         evidence"
        ok;
      check "M5 BREAK: ... but the checker says the guarantee was weakened"
        (says out "Switching from stronger to weaker guarantee using unchecked deletion");
      let ok, out = run "del_soli_c" body "conclusion BOUNDS 2 : @lb 2 ;" ~flags:"-c" in
      check "M5 BREAK: and under --force-checked-deletion it is REFUSED" (not ok);
      check "M5 BREAK: ... at full strength"
        (says out
           "Checked deletion failed and `--force-checked-deletion` option used. \
            Proofgoal with ID #1 could not be autoproven.");
      (* The obju trap, docs/PROOF-FORMAT.md line 136, RE-MEASURED rather than quoted.
         It is filed against M5 and M5-T1 does not hit it, because branch and bound
         tightens a BOUND on a fixed objective and never updates the objective itself.
         Measured here so that "we avoided it" is a statement about a live fact.

         And the fact is narrower than the note says: the goal is autoproven when an
         improving constraint is already on the page ("proofgoal #1 is RUP"), so the
         trap fires on `obju` BEFORE any `soli` and not unconditionally. That is the
         shape the note filed, and it is the shape asserted here. *)
      let pbp = Filename.concat dir "obju.pbp" in
      let oc = open_out pbp in
      Printf.fprintf oc
        "pseudo-Boolean proof version 3.0\n\
         f %d ;\n\
         obju new +1 y_ge_1 +1 y_ge_2 ;\n\
         @s1 soli %s ;\n\
         output NONE ;\n\
         conclusion BOUNDS 2 2 ;\n\
         end pseudo-Boolean proof ;\n"
        f_count sol;
      close_out oc;
      let log = Filename.concat dir "obju.log" in
      let rc =
        Sys.command
          (Printf.sprintf "%s %s %s > %s 2>&1" (Filename.quote checker)
             (Filename.quote opb) (Filename.quote pbp) (Filename.quote log))
      in
      let out = read_whole log in
      check "M5: `obju` on a fresh objective is REFUSED (the trap M5 was warned about)"
        (rc <> 0);
      check "M5: ... with the wording docs/PROOF-FORMAT.md filed, re-measured"
        (says out
           "Proofgoal #1 could not be autoproven. Please add an explicit subproof for \
            proofgoal #1.");
      List.iter
        (fun f -> try Sys.remove f with _ -> ())
        (List.map (Filename.concat dir) (Array.to_list (Sys.readdir dir)));
      try Sys.rmdir dir with _ -> ())

(* Nothing in lib/ or bin/ emits `obju`. The trap above is avoided by construction, and
   this is what keeps that true: [Writer.objective_update] is kept because it carries the
   measurement and is what a future objective-reformulation row would reach for, but a
   caller appearing in the solver is the event this check exists to make visible. Same
   shape as test_mutation.ml's guard on [Writer.create_mutated]. *)
let test_m5_no_obju_caller () =
  (* dune runs a test with its cwd inside the build directory, which holds no lib/ or
     bin/ to grep, so the SOURCE tree has to be located first -- the same problem
     test_mutation.ml solves for scripts/mutate_proof.sh, solved the same way and with
     the same override. Getting this wrong is not a false negative, it is a silently
     inert check, so the resolution is asserted below before the grep is believed. *)
  let rec ancestors dir =
    let parent = Filename.dirname dir in
    if parent = dir then [ dir ] else dir :: ancestors parent
  in
  let root =
    let candidates =
      (match Sys.getenv_opt "BAGUETTE_ROOT" with Some r -> [ r ] | None -> [])
      @ ancestors (Sys.getcwd ())
      @ ancestors (Filename.dirname Sys.executable_name)
    in
    List.find_opt
      (fun d -> Sys.file_exists (Filename.concat d "lib/proof/writer.ml"))
      candidates
  in
  match root with
  | None ->
      incr failures;
      print_endline
        "FAIL M5: the source tree was not found from the cwd, the executable's path or \
         $BAGUETTE_ROOT, so the `obju` caller check did not run. This is not a pass."
  | Some root ->
      let grep pat =
        let tmp = Filename.temp_file "baguette_obju" "" in
        ignore
          (Sys.command
             (Printf.sprintf
                "grep -rn 'objective_update' %s/lib %s/bin 2>/dev/null %s > %s"
                (Filename.quote root) (Filename.quote root) pat (Filename.quote tmp)));
        let s = read_whole tmp in
        (try Sys.remove tmp with _ -> ());
        s
      in
      (* The definition is certainly there, so an empty result means the grep did not
         look rather than that it looked and found nothing. *)
      check
        "M5: the obju-caller search actually ran (it found the definition it looks past)"
        (String.trim (grep "") <> "");
      check
        "M5: nothing under lib/ or bin/ calls Writer.objective_update, so no run can \
         emit `obju`"
        (String.trim (grep "| grep -v 'lib/proof/writer.ml'") = "")

(* =====================================================================
   M7-T1: the limits are options, and the cost is counted
   =====================================================================

   The refusal that used to guard the order encoding came from a 15 GB laptop. It is
   gone from the default build. What is NOT gone is D-0028's actual cost -- proof size
   and checker time -- so the module now COUNTS what it minted and says so. These
   assertions pin the option's shape and the counter's arithmetic; the end-to-end
   behaviour (a wide model solving, veripb accepting its proof, the warning's text, the
   refusal's wording under a flag) is scripts/check_unlimited.sh. *)

let m7_eq name ~expected ~actual =
  if expected = actual then check name true
  else check (Printf.sprintf "%s -- expected %S, got %S" name expected actual) false

let m7_contains ~needle hay =
  let n = String.length needle and h = String.length hay in
  let rec go i = i + n <= h && (String.sub hay i n = needle || go (i + 1)) in
  n = 0 || go 0

let with_limits f =
  let sw = !Encoding.order_width_limit
  and sd = !Encoding.direct_values_limit
  and sn = !Encoding.width_warn_threshold
  and ss = !Encoding.warn_sink in
  Fun.protect
    ~finally:(fun () ->
      Encoding.order_width_limit := sw;
      Encoding.direct_values_limit := sd;
      Encoding.width_warn_threshold := sn;
      Encoding.warn_sink := ss)
    f

let test_m7_limits_are_options () =
  with_limits (fun () ->
      (* The SHIPPED defaults, as the module was loaded: no refusal, and a warning
         threshold at the old cap. This is the assertion that fails if someone puts the
         hardware-derived refusal back. *)
      (match m7_shipped_defaults with
      | None, None, Some n when n = Encoding.max_order_width ->
          check "M7-T1: the shipped default refuses nothing and warns at the old cap" true
      | w, d, t ->
          check
            (Printf.sprintf
               "M7-T1: shipped defaults are wrong -- width %s, direct %s, warn %s"
               (Encoding.limit_string w) (Encoding.limit_string d)
               (Encoding.limit_string t))
            false);
      (* Parsing. A value that is neither an integer nor `none` must RAISE. A mistyped
         budget that silently means "no budget" is the failure this row is about, and
         it is the one failure a limit-parsing function can have that nobody notices. *)
      let parses s = Encoding.limit_of_string ~what:"t" s in
      check "M7-T1: `none` is no limit" (parses "none" = None);
      check "M7-T1: `unlimited` is no limit" (parses "unlimited" = None);
      check "M7-T1: `off` is no limit" (parses "off" = None);
      check "M7-T1: the empty string is no limit" (parses "" = None);
      check "M7-T1: whitespace and case do not matter" (parses "  NoNe " = None);
      check "M7-T1: an integer is a limit" (parses "10000" = Some 10_000);
      check "M7-T1: zero is a limit, and a real one" (parses "0" = Some 0);
      List.iter
        (fun bad ->
          check
            (Printf.sprintf "M7-T1: %S is an ERROR, not a silent `none`" bad)
            (match parses bad with
            | _ -> false
            | exception Encoding.Bad_limit ("t", b) -> b = bad
            | exception _ -> false))
        [ "-1"; "-3"; "1e4"; "10 000"; "ten"; "10000x"; "0x10"; "0b11"; "1_0000" ];

      (* -1 in particular: the neighbouring convention spells `none` that way, which
         would make -3 the only negative that is an error. That is precisely the trap. *)

      (* The default. *)
      Encoding.order_width_limit := None;
      Encoding.direct_values_limit := None;
      check "M7-T1: no width limit by default"
        (Encoding.current_order_width_limit () = None);
      check "M7-T1: no direct-values limit by default"
        (Encoding.current_direct_values_limit () = None);
      m7_eq "M7-T1: and it renders as `unlimited`" ~expected:"unlimited"
        ~actual:(Encoding.order_width_limit_string ());
      m7_eq "M7-T1: a set limit renders as its number" ~expected:"77"
        ~actual:
          (Encoding.order_width_limit := Some 77;
           Encoding.order_width_limit_string ());
      Encoding.order_width_limit := None;

      (* The direct encoding, which had the second number. Under no limit a domain
         far past [max_direct_values] is requested without complaint; under a limit of
         one, the smallest domain there is is refused. Both halves, because a limit
         that is never seen to bite is not a limit. *)
      let e = Encoding.create () in
      Encoding.declare_int e "d" ~lo:0 ~hi:5;
      check "M7-T1: request_direct is accepted with no limit"
        (match Encoding.request_direct e "d" with _ -> true | exception _ -> false);
      Encoding.direct_values_limit := Some 1;
      let e2 = Encoding.create () in
      Encoding.declare_int e2 "d" ~lo:0 ~hi:5;
      check "M7-T1: and refused under --max-direct-values=1"
        (match Encoding.request_direct e2 "d" with
        | _ -> false
        | exception Encoding.Direct_too_large ("d", 6) -> true
        | exception _ -> false);
      Encoding.direct_values_limit := None;
      m7_eq "M7-T1: max_direct_values keeps its value as the SUGGESTED limit"
        ~expected:"100000"
        ~actual:(string_of_int Encoding.max_direct_values))

let test_m7_encoding_cost () =
  with_limits (fun () ->
      Encoding.order_width_limit := None;
      Encoding.width_warn_threshold := None;
      let e = Encoding.create () in
      let c0 = Encoding.cost e in
      check "M7-T1: an empty encoding cost nothing" (c0.Encoding.c_ladder_clauses = 0);
      check "M7-T1: and names no widest variable" (c0.Encoding.c_widest = None);
      Encoding.declare_int e "a" ~lo:0 ~hi:5;
      Encoding.declare_int e "b" ~lo:(-4) ~hi:4;
      Encoding.declare_int e "c" ~lo:7 ~hi:7;
      let c = Encoding.cost e in
      (* 4 + 7 + 0. The ladder is w - 1 clauses per variable and the counter is the SUM
         -- which is the number the per-variable cap never bounded, and said so in its
         own comment: a thousand variables at width 9 999 was always ten million
         clauses and always slipped through. *)
      m7_eq "M7-T1: the ladder total is the sum over variables" ~expected:"11"
        ~actual:(string_of_int c.Encoding.c_ladder_clauses);
      check "M7-T1: which is what the encoding actually minted"
        (c.Encoding.c_ladder_clauses = Encoding.n_constraints e);
      check "M7-T1: the widest variable is named, so a reader knows what to narrow"
        (c.Encoding.c_widest = Some ("b", -4, 4));
      m7_eq "M7-T1: and its width is reported" ~expected:"8"
        ~actual:(string_of_int (Encoding.widest_width c.Encoding.c_widest));
      check "M7-T1: a width-0 declaration does not become the widest"
        (c.Encoding.c_widest <> Some ("c", 7, 7));
      (* The warning is a function of the threshold and nothing else. *)
      let buf = Buffer.create 64 in
      Encoding.set_warn_sink (Buffer.add_string buf);
      Encoding.width_warn_threshold := Some 3;
      let e2 = Encoding.create () in
      Encoding.declare_int e2 "narrow" ~lo:0 ~hi:3;
      check "M7-T1: at the threshold, nothing is said" (Buffer.contents buf = "");
      Encoding.declare_int e2 "over" ~lo:0 ~hi:4;
      check "M7-T1: one over it, the encoding reports itself" (Buffer.contents buf <> "");
      check "M7-T1: naming the variable a reader must act on"
        (m7_contains ~needle:"`over`" (Buffer.contents buf)))

let () =
  report_checker ();
  test_lits ();
  test_opb ();
  test_pol ();
  test_writer_ids ();
  test_writer_not_truncated ();
  test_audit ();
  test_order_encoding ();
  test_ids_and_equality ();
  test_direct_encoding ();
  test_assignment_lits ();
  test_renaming_comments ();
  test_int_lin_le_soundness ();
  test_int_lin_le_worked_examples ();
  test_int_lin_le_add ();
  test_arith_matches_checked ();
  test_committing_door_refuses_overflow ();
  test_int_lin_le_veripb ();
  test_v3_emitted_text ();
  test_v3_levels ();
  test_v3_del_range_semantics ();
  test_v3_del_pair_spelling ();
  test_v3_wipe_level_against_checker ();
  test_v3_veripb ();
  test_pol_states_its_conclusion ();
  test_learned_survives_the_backjump ();
  test_reif_rows ();
  test_reif_big_m_rows ();
  test_reif_preconditions ();
  test_reif_emitted_text ();
  test_reif_veripb ();
  test_view_lits ();
  test_view_encoding ();
  test_view_veripb ();
  test_m5_bounds_and_soli ();
  test_m5_no_obju_caller ();
  test_m7_limits_are_options ();
  test_m7_encoding_cost ();
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "\nproof unit tests passed"
