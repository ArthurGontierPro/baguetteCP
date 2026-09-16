(* Unit tests for lib/flatzinc/compile.ml: Model.t -> store / encoding / propagators.

   Four things are checked here, in rising order of how much they would cost if they
   were wrong:

   1. **Variable identity.** [Var.of_int i] must denote [Model.var m i]. Nothing
      downstream can detect a permutation -- the CLI re-checks the solution against the
      model using the *same* wrong indices, so a permuted answer passes its own
      independent check and is printed with a proof veripb accepts. It is therefore
      asserted directly, on a model whose variables have distinguishable names and
      distinguishable domains, so a permutation cannot hide behind symmetry.

   2. **Shape.** One propagator instance per model row (D-0011): a `<=` is one
      instance and one .opb row, an equality is two of each, and a disequality is one
      instance and *two* rows. That last one is the asymmetric case, and so the one a
      later reader is most likely to "correct" -- compile.ml's header says why the
      single instance cites neither of its rows. Counted through [Engine.n_instances]
      and [Encoding.n_constraints].

   3. **Normalisation.** Constants folded into the right-hand side, repeated variables
      merged by summing coefficients, zero coefficients dropped -- checked both on
      [Compile.normalise_terms] directly and through what the resulting propagator
      actually prunes, since the second is what a wrong normalisation would corrupt.

   4. **Rejection.** SPEC 2.1 is normative: an unimplemented builtin must be named in
      an error, never silently ignored. Each rejection asserts on the *content* of the
      message, not merely that something was raised -- an error that does not name the
      builtin is not the error the spec asks for.

   And, because this project's rule is that a test which does not check the proof is
   half a test (CLAUDE.md), three models are run all the way: compiled here, solved by
   [Search.solve] writing a real .opb and .pbp, and handed to veripb. If veripb is
   missing the suite FAILS rather than skipping -- an unchecked proof is not a passing
   proof. The end-to-end models here are deliberately either SAT or root-refutable
   (refuted by bounds propagation with no decision active). That was originally because
   the branching UNSAT case did not verify at all -- D-0012/D-0014, both since
   overturned by D-0018/D-0021 -- and it stays that way now for a different reason: a
   model that needs a decision exercises the trace machinery rather than this file's
   translation, and test/models/ now holds five disequality models that do exercise it
   end to end. *)

module F = Baguette_flatzinc
module M = F.Model
module Compile = F.Compile
module Var = Baguette_core.Var
module Domain = Baguette_core.Domain
module Store = Baguette_core.Store
module Engine = Baguette_core.Engine
module Search = Baguette_core.Search
module Justify = Baguette_core.Justify
module Encoding = Baguette_proof.Encoding
module Writer = Baguette_proof.Writer

let failures = ref 0

let check name cond =
  if cond then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s\n" name)

let fail name detail =
  incr failures;
  Printf.printf "FAIL %s\n       %s\n" name detail

let contains ~needle haystack =
  let n = String.length needle and h = String.length haystack in
  if n = 0 then true
  else
    let found = ref false in
    for i = 0 to h - n do
      if (not !found) && String.equal (String.sub haystack i n) needle then found := true
    done;
    !found

let build src = F.Builder.of_string ~file:"test" src

(* --------------------------------------------------------------- 1. identity *)

let identity_model =
  {|
var 1..3: alpha;
var bool: flag;
array[1..2] of var -4..7: row;
var 0..0: fixed;
constraint int_le(alpha, 3);
solve satisfy;
|}

let test_variable_identity () =
  let m = build identity_model in
  let c = Compile.compile m in
  check "identity: store has exactly the model's variables"
    (Store.n_vars c.Compile.store = M.nvars m);
  let names_agree = ref true and domains_agree = ref true in
  for i = 0 to M.nvars m - 1 do
    let v = M.var m i in
    let sv = Var.of_int i in
    if not (String.equal (Store.name c.Compile.store sv) v.M.v_name) then
      names_agree := false;
    let d = Store.get c.Compile.store sv in
    let lo, hi =
      match v.M.v_dom with
      | M.Dbool -> (0, 1)
      | M.Drange (l, u) -> (l, u)
      | M.Dset _ -> (min_int, max_int)
    in
    if Domain.lo d <> lo || Domain.hi d <> hi then domains_agree := false
  done;
  check "identity: Store.name (Var.of_int i) = (Model.var m i).v_name, for every i"
    !names_agree;
  check "identity: every store domain is the model's declared domain" !domains_agree;
  (* The names are also what the .opb declares, and in the same order (D-0010: the
     store's initial domains and the encoding's declared domains must agree). *)
  let encoded = Encoding.vars c.Compile.encoding in
  let expected = List.init (M.nvars m) (fun i -> (M.var m i).M.v_name) in
  check "identity: the encoding declares the same names, in the same order"
    (List.equal String.equal encoded expected);
  List.iteri
    (fun i n ->
      let lo, hi = Encoding.domain c.Compile.encoding n in
      let d = Store.get c.Compile.store (Var.of_int i) in
      if Domain.lo d <> lo || Domain.hi d <> hi then
        fail "identity: encoding and store declared bounds agree (D-0010)"
          (Printf.sprintf "%s: store %d..%d, encoding %d..%d" n (Domain.lo d)
             (Domain.hi d) lo hi))
    encoded;
  check "identity: array elements keep their FlatZinc element names"
    (String.equal (Store.name c.Compile.store (Var.of_int 2)) "row[1]"
    && String.equal (Store.name c.Compile.store (Var.of_int 3)) "row[2]")

(* ------------------------------------------------------- 2. one instance per row *)

(* Two `var bool`s so that [declare_bool] contributes no order-consistency clauses of
   its own (there are none for a [0,1] domain), leaving [Encoding.n_constraints] equal
   to the number of model rows posted. *)
let two_bools body =
  Printf.sprintf "var bool: b;\nvar bool: c;\n%s\nsolve satisfy;\n" body

let instances_and_rows src =
  let c = Compile.compile (build src) in
  (Engine.n_instances c.Compile.engine, Encoding.n_constraints c.Compile.encoding)

let test_instance_counts () =
  let n, rows = instances_and_rows (two_bools "constraint int_lin_le([1,1],[b,c],1);") in
  check "shape: int_lin_le is one instance" (n = 1);
  check "shape: int_lin_le is one .opb row" (rows = 1);
  let n, rows = instances_and_rows (two_bools "constraint int_lin_eq([1,1],[b,c],1);") in
  check "shape: int_lin_eq is two instances, one per row (D-0011)" (n = 2);
  check "shape: int_lin_eq is two .opb rows (<= and >=)" (rows = 2);
  let n, rows = instances_and_rows (two_bools "constraint int_le(b,c);") in
  check "shape: int_le is one instance" (n = 1);
  check "shape: int_le is one .opb row" (rows = 1);
  let n, _ = instances_and_rows (two_bools "constraint int_lt(b,c);") in
  check "shape: int_lt is one instance" (n = 1);
  let n, rows = instances_and_rows (two_bools "constraint int_eq(b,c);") in
  check "shape: int_eq is two instances (it is the int_lin_eq shape)" (n = 2);
  check "shape: int_eq is two .opb rows" (rows = 2);
  let n, rows = instances_and_rows (two_bools "constraint int_ne(b,c);") in
  check "shape: int_ne is one instance" (n = 1);
  check "shape: int_ne is two .opb rows, and the instance cites neither (M1-T11)"
    (rows = 2);
  let n, rows = instances_and_rows (two_bools "constraint int_lin_ne([1,1],[b,c],1);") in
  check "shape: int_lin_ne is one instance" (n = 1);
  check "shape: int_lin_ne is two .opb rows (add_int_lin_ne's A/B pair)" (rows = 2);
  let n, rows =
    instances_and_rows
      (two_bools
         "constraint int_le(b,c);\n\
          constraint int_eq(b,c);\n\
          constraint int_lin_le([1,1],[b,c],2);")
  in
  check "shape: several constraints accumulate (1 + 2 + 1 instances)" (n = 4);
  check "shape: several constraints accumulate (1 + 2 + 1 rows)" (rows = 4)

(* --------------------------------------------------------------- 3. normalisation *)

(* [normalise_terms] is exposed (compile.ml has no .mli) precisely so the rule can be
   checked as a rule, not only through its downstream effects. *)
let test_normalise_terms () =
  let eq a b = List.equal (fun (c1, i1) (c2, i2) -> c1 = c2 && i1 = i2) a b in
  check "normalise: repeated indices are merged by summing coefficients"
    (eq (Compile.normalise_terms [ (1, 0); (2, 0); (3, 1) ]) [ (3, 0); (3, 1) ]);
  check "normalise: a coefficient that sums to zero is dropped"
    (eq (Compile.normalise_terms [ (1, 0); (-1, 0); (5, 1) ]) [ (5, 1) ]);
  check "normalise: an explicit zero coefficient is dropped"
    (eq (Compile.normalise_terms [ (0, 0); (4, 1) ]) [ (4, 1) ]);
  check "normalise: first-occurrence order is preserved"
    (eq (Compile.normalise_terms [ (1, 2); (1, 0); (1, 2) ]) [ (2, 2); (1, 0) ]);
  check "normalise: everything cancelling leaves an empty list"
    (eq (Compile.normalise_terms [ (2, 0); (-2, 0) ]) [])

(* Propagate once and report the resulting domain of variable [i]. The engine is the
   only thing that can show that the *propagator* got the same normalised terms the
   row did: a duplicate left unmerged makes bounds propagation strictly weaker. *)
let propagated src i =
  let c = Compile.compile (build src) in
  match Engine.propagate c.Compile.engine c.Compile.store with
  | Engine.Conflict _ -> None
  | Engine.Fixpoint ->
      let d = Store.get c.Compile.store (Var.of_int i) in
      Some (Domain.lo d, Domain.hi d)

let test_constant_folding () =
  (* int_le(x, 2) must become terms [(1, x)], rhs 2 -- so x's upper bound goes to 2. *)
  check "folding: int_le(x, 2) pushes x's upper bound to 2"
    (propagated "var 1..3: x;\nconstraint int_le(x,2);\nsolve satisfy;\n" 0 = Some (1, 2));
  check "folding: int_le(2, x) pushes x's lower bound to 2"
    (propagated "var 1..3: x;\nconstraint int_le(2,x);\nsolve satisfy;\n" 0 = Some (2, 3));
  check "folding: int_lt(x, 3) is x - 0 <= -1 + 3, so x <= 2"
    (propagated "var 1..5: x;\nconstraint int_lt(x,3);\nsolve satisfy;\n" 0 = Some (1, 2));
  check "folding: int_eq(x, 2) fixes x"
    (propagated "var 1..5: x;\nconstraint int_eq(x,2);\nsolve satisfy;\n" 0 = Some (2, 2));
  (* A constant inside the int_lin_le variable array is folded by the builder; the
     point here is that compile does not then lose it. 2*x + 3*1 <= 9 => x <= 3. *)
  check "folding: a constant in the int_lin_le array lands on the right-hand side"
    (propagated "var 0..9: x;\nconstraint int_lin_le([2,3],[x,1],9);\nsolve satisfy;\n" 0
    = Some (0, 3))

let test_duplicate_coefficients () =
  (* 1*x + 1*x <= 5 with x in 0..10. Merged, the propagator sees 2x <= 5 and pushes
     x <= 2. Left unmerged it sees two independent terms, each with slack 5, and can
     only reach x <= 5 -- so this distinguishes the two directly. *)
  check "normalise: the propagator sees the merged row (x + x <= 5 gives x <= 2)"
    (propagated "var 0..10: x;\nconstraint int_lin_le([1,1],[x,x],5);\nsolve satisfy;\n" 0
    = Some (0, 2));
  (* 3*x - 1*x <= 5 with x in 0..10: merged, 2x <= 5, so x <= 2. *)
  check "normalise: mixed-sign duplicates merge before propagation"
    (propagated "var 0..10: x;\nconstraint int_lin_le([3,-1],[x,x],5);\nsolve satisfy;\n"
       0
    = Some (0, 2));
  (* A zero coefficient must not make its variable part of the row: 0*y + 1*x <= 2
     leaves y alone entirely. *)
  check "normalise: a zero coefficient leaves its variable untouched"
    (propagated
       "var 0..10: x;\n\
        var 0..10: y;\n\
        constraint int_lin_le([1,0],[x,y],2);\n\
        solve satisfy;\n"
       1
    = Some (0, 10));
  check "normalise: the surviving term still propagates"
    (propagated
       "var 0..10: x;\n\
        var 0..10: y;\n\
        constraint int_lin_le([1,0],[x,y],2);\n\
        solve satisfy;\n"
       0
    = Some (0, 2))

(* ------------------------------------------------ 3b. the ground-constraint case *)

(* After folding, a term list can be empty. See compile.ml's comment on [post_le] for
   what was checked against veripb and why the constraint is posted rather than
   dropped; [test_end_to_end] below runs the failing case through the checker. *)
let test_ground_constraints () =
  let sat =
    Compile.compile
      (build
         "var 1..3: x;\n\
          constraint int_le(1,2);\n\
          constraint int_le(x,3);\n\
          solve satisfy;\n")
  in
  check "ground: a true ground constraint is still posted as an instance"
    (Engine.n_instances sat.Compile.engine = 2);
  check "ground: a true ground constraint is still posted as an .opb row"
    (* x in 1..3 contributes one order-consistency clause, plus two rows. *)
    (Encoding.n_constraints sat.Compile.encoding = 3);
  check "ground: a true ground constraint does not fail the model"
    (match Engine.propagate sat.Compile.engine sat.Compile.store with
    | Engine.Fixpoint -> true
    | Engine.Conflict _ -> false);
  let unsat =
    Compile.compile (build "var 1..3: x;\nconstraint int_le(2,1);\nsolve satisfy;\n")
  in
  check "ground: a false ground constraint conflicts at the root, it is not dropped"
    (match Engine.propagate unsat.Compile.engine unsat.Compile.store with
    | Engine.Conflict _ -> true
    | Engine.Fixpoint -> false)

(* ---------------------------------------------- 3c. the disequality path (M1-T11) *)

(* A disequality that compiles but propagates nothing would satisfy [expect_accepted]
   and still ignore the model, which is the one outcome SPEC 2.1 forbids outright. So
   the wiring is checked by what it prunes, not by what it accepts. Each case fixes one
   side with an equality first, because a disequality with two unfixed terms is entitled
   to infer nothing at all (lib/core/prop/ne.ml). *)
let test_disequalities () =
  check "ne: int_ne prunes the other side once one side is fixed"
    (propagated
       "var 1..2: x;\n\
        var 1..2: y;\n\
        constraint int_eq(x,1);\n\
        constraint int_ne(x,y);\n\
        solve satisfy;\n"
       1
    = Some (2, 2));
  (* 2x - y <> 0 with x fixed at 1 forbids y = 2, which is y's upper bound here, so a
     bound actually moves. The non-unit coefficient also exercises the division in
     [Ne.propagate] that no int_ne can reach, and would be lost by a normalisation that
     dropped or merged the wrong term. *)
  check "ne: int_lin_ne prunes through a non-unit coefficient"
    (propagated
       "var 0..2: x;\n\
        var 0..2: y;\n\
        constraint int_eq(x,1);\n\
        constraint int_lin_ne([2,-1],[x,y],0);\n\
        solve satisfy;\n"
       1
    = Some (0, 1));
  (* int_ne(x, x) normalises to the empty sum <> 0, which is false. It is posted rather
     than dropped, for the reason compile.ml's ground-constraint comment gives; and
     test/models/ne_self_unsat.fzn runs this same model past veripb, where the .opb's
     A/B pair degenerates to two contradictory units on its auxiliary Boolean. *)
  let self =
    Compile.compile (build "var 1..3: x;\nconstraint int_ne(x,x);\nsolve satisfy;\n")
  in
  check "ne: int_ne(x, x) is still one instance, not a dropped constraint"
    (Engine.n_instances self.Compile.engine = 1);
  check "ne: int_ne(x, x) conflicts at the root"
    (match Engine.propagate self.Compile.engine self.Compile.store with
    | Engine.Conflict _ -> true
    | Engine.Fixpoint -> false)

(* -------------------------------------------------------------- 4. rejections *)

(* Assert on the message, not merely that something raised: SPEC 2.1 requires the
   error to *name* what is not supported, and a test that only counts exceptions
   cannot tell a good diagnostic from "Failure". *)
let expect_rejected name ~needles src =
  match Compile.compile (build src) with
  | exception F.Error.Error e ->
      let msg = F.Error.to_string e in
      let missing = List.filter (fun n -> not (contains ~needle:n msg)) needles in
      if missing = [] then Printf.printf "ok   %s\n" name
      else
        fail name
          (Printf.sprintf "message does not mention %s\n       message: %s"
             (String.concat ", " (List.map (Printf.sprintf "`%s`") missing))
             msg)
  | exception exn -> fail name ("raised the wrong exception: " ^ Printexc.to_string exn)
  | _ -> fail name "compiled successfully; the constraint was silently accepted"

let expect_accepted name src =
  match Compile.compile (build src) with
  | exception F.Error.Error e ->
      fail name ("unexpectedly rejected: " ^ F.Error.to_string e)
  | exception exn -> fail name ("raised: " ^ Printexc.to_string exn)
  | _ -> Printf.printf "ok   %s\n" name

let test_rejections () =
  (* Both disequalities were rejections here until M1-T11, with a message naming M1-T9
     and claiming they needed the direct encoding. D-0019 overturned the reason and
     M1-T11 the rejection, so what used to assert that wording now asserts that the
     constraint compiles; [test_disequalities] is what checks it does something. *)
  expect_accepted "accept: int_lin_ne is compiled rather than rejected (M1-T11)"
    "var 0..3: x;\nvar 0..3: y;\nconstraint int_lin_ne([1,1],[x,y],2);\nsolve satisfy;\n";
  expect_accepted "accept: int_ne is compiled rather than rejected (M1-T11)"
    "var 0..3: x;\nvar 0..3: y;\nconstraint int_ne(x,y);\nsolve satisfy;\n";
  expect_rejected "reject: a set domain names the variable and what is missing"
    ~needles:[ "holes"; "relaxation"; "hull" ]
    "var {1,3,5}: pick;\nconstraint int_le(pick,5);\nsolve satisfy;\n";
  expect_rejected "reject: a set domain says which variable" ~needles:[ "`pick`" ]
    "var {1,3,5}: pick;\nconstraint int_le(pick,5);\nsolve satisfy;\n";
  expect_rejected "reject: minimize names the goal and the milestone"
    ~needles:[ "minimize"; "M5" ]
    "var 0..3: x;\nconstraint int_le(x,3);\nsolve minimize x;\n";
  expect_rejected "reject: maximize names the goal and the milestone"
    ~needles:[ "maximize"; "M5" ]
    "var 0..3: x;\nconstraint int_le(x,3);\nsolve maximize x;\n";
  expect_rejected "reject: input_order is not what Search.solve implements"
    ~needles:[ "input_order"; "first_fail"; "indomain_min" ]
    "var 0..3: x;\n\
     constraint int_le(x,3);\n\
     solve :: int_search([x],input_order,indomain_min,complete) satisfy;\n";
  expect_rejected "reject: indomain_max is not what Search.solve implements"
    ~needles:[ "indomain_max"; "indomain_min" ]
    "var 0..3: x;\n\
     constraint int_le(x,3);\n\
     solve :: int_search([x],first_fail,indomain_max,complete) satisfy;\n";
  expect_rejected "reject: seq_search is recursed into, not waved through"
    ~needles:[ "input_order" ]
    "var 0..3: x;\n\
     var 0..3: y;\n\
     constraint int_le(x,y);\n\
     solve :: \
     seq_search([int_search([x],first_fail,indomain_min,complete),int_search([y],input_order,indomain_min,complete)]) \
     satisfy;\n";
  expect_accepted "accept: first_fail + indomain_min matches what is implemented"
    "var 0..3: x;\n\
     constraint int_le(x,3);\n\
     solve :: int_search([x],first_fail,indomain_min,complete) satisfy;\n";
  expect_accepted "accept: a seq_search of implemented strategies"
    "var 0..3: x;\n\
     var 0..3: y;\n\
     constraint int_le(x,y);\n\
     solve :: \
     seq_search([int_search([x],first_fail,indomain_min,complete),int_search([y],first_fail,indomain_min,complete)]) \
     satisfy;\n";
  expect_accepted "accept: no annotation at all (SPEC 3.4's default)"
    "var 0..3: x;\nconstraint int_le(x,3);\nsolve satisfy;\n"

(* ------------------------------------- 4b. I-S1's oracle is arithmetically independent

   M1-T33, from D-0029's consequence list. [Model.check_assignment] used to evaluate
   `sum a_i v_i` with the same wrapping `+`/`*` as the propagator and the .opb expansion
   it exists to check, so on the overflow class it agreed with the bug -- and agreed
   *because* it computed the same wrong product. It now evaluates exactly.

   These checks live in this file rather than beside the other [check_assignment] checks
   in test/unit/test_output.ml because that file belongs to another session this round.
   They are about the oracle, not about compile.ml, and should move when the two files
   are next held together.

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

(* ------------------------------------------------------ 5. end to end, with veripb *)

(* I-S1: re-check the solution against the model itself rather than trusting the
   propagators. This is also the only place the *meaning* of a compiled constraint is
   re-derived independently of compile.ml -- it reads Model.t, not the store. *)
let evaluate (m : M.t) (assign : int array) =
  let value terms = List.fold_left (fun acc (a, i) -> acc + (a * assign.(i))) 0 terms in
  let operand = function M.Const n -> n | M.Var i -> assign.(i) in
  (* A Boolean operand read as a Boolean. A value that is neither 0 nor 1 is a bug in
     the store or a propagator, not a falsehood, so it is loud -- the same discipline
     [Output.bool_string] applies for the same reason (I-S1). *)
  let truth op =
    match operand op with
    | 0 -> false
    | 1 -> true
    | n -> failwith (Printf.sprintf "test_compile: non-Boolean value %d for a bool" n)
  in
  List.for_all
    (fun (c : M.constr) ->
      match c.M.k with
      | M.Int_lin_le (ts, r) -> value ts <= r
      | M.Int_lin_eq (ts, r) -> value ts = r
      | M.Int_le (a, b) -> operand a <= operand b
      | M.Int_lt (a, b) -> operand a < operand b
      | M.Int_eq (a, b) -> operand a = operand b
      (* Written from the FlatZinc definition of each builtin, deliberately NOT by
         calling [Model.check_assignment]: this helper's whole value is that it is a
         second, independent reading of what a constraint means (see its header). Two
         copies that agree are evidence; one copy called twice is not. An empty [xs] is
         the identity of its connective -- or([]) false, and([]) true -- which
         [List.exists]/[List.for_all] already give. M2-T1/M2-T2. *)
      | M.Bool_clause (ps, ns) ->
          List.exists truth ps || List.exists (fun o -> not (truth o)) ns
      | M.Array_bool_or (xs, r) -> truth r = List.exists truth xs
      | M.Array_bool_and (xs, r) -> truth r = List.for_all truth xs
      | M.Bool2int (b, x) -> operand x = if truth b then 1 else 0
      | M.Bool_eq (a, b) -> truth a = truth b
      | M.Bool_not (a, b) -> truth a <> truth b
      (* M1-T40. This arm used to be a [failwith] saying "compile rejects these",
         which stopped being true at M1-T11 -- so from M1-T11 until now the oracle had
         never once been run on a disequality, and the only thing standing between it
         and a silently wrong answer was that no model in this file contained one.
         The semantics below are the FlatZinc definition of the two builtins, read off
         the spec and deliberately NOT off [Model.check_assignment] or off
         [lib/core/prop/ne.ml] -- same rule as the Boolean row above, and the reason
         [evaluate] exists at all.

         The deliverable of M1-T40 is not these two lines, it is
         [test_end_to_end]'s three disequality models below: an oracle branch nobody
         has seen run is exactly what D-0030 is about, so the semantics and the models
         that reach them land together. Confirmed by inverting each arm in turn and
         watching those models fail. *)
      | M.Int_lin_ne (ts, r) -> value ts <> r
      | M.Int_ne (a, b) -> operand a <> operand b)
    m.M.constraints

(* Brute force over the declared box: the independent oracle for the expected answer.
   Nothing here is hand-asserted, for the reason test_endtoend.ml gives -- a test whose
   expected answer is written by hand is a test that can be talked into a bug. *)
let brute_force (m : M.t) =
  let n = M.nvars m in
  let assign = Array.make n 0 in
  let bounds =
    Array.map
      (fun (v : M.var) ->
        match v.M.v_dom with
        | M.Dbool -> (0, 1)
        | M.Drange (l, u) -> (l, u)
        | M.Dset _ -> failwith "test_compile: brute_force does not do set domains")
      m.M.vars
  in
  let found = ref None in
  (* The inner [if] is parenthesised on purpose: written without it, the dangling
     [else] binds to [if evaluate m assign] instead of to [if i = n], and [go 0] on a
     model with any variables at all falls through to [()] without ever enumerating
     anything -- [brute_force] then returns [None] for every model and silently agrees
     with any UNSAT the solver reports. *)
  let rec go i =
    if !found = None then
      if i = n then (if evaluate m assign then found := Some (Array.copy assign))
      else
        let lo, hi = bounds.(i) in
        for v = lo to hi do
          if !found = None then (
            assign.(i) <- v;
            go (i + 1))
        done
  in
  go 0;
  !found

(* Which checker to run: lib/proof/checker.ml, shared with scripts/checker.sh.
   Every test module open-coded this search, and every copy looked at
   ~/.local/bin/veripb first -- so a project-wide choice of checker lived in nine
   places and silently meant the Python 2.2.2 (M1-T18). [None] is a FAILURE at every
   call site below, never a skip. *)
let veripb_path () = Baguette_proof.Checker.find ()

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

(* The CLI's own conversion, written here the way bin/main.ml has to write it: a
   Search.assignment indexed by Var.t becomes an int array indexed by *model* variable
   index. This is the step that silently breaks if compile stops preserving order, so
   the end-to-end models below all go through it. *)
let assignment_array (m : M.t) (a : Search.assignment) =
  let arr = Array.make (M.nvars m) 0 in
  List.iter (fun (v, value) -> arr.(Var.to_int v) <- value) a;
  arr

let run_model ~title ~src =
  let m = build src in
  let c = Compile.compile m in
  let expected = brute_force m in
  let expect_sat = expected <> None in
  let dir = Filename.temp_file "baguette_compile" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  let opb = Filename.concat dir "model.opb" in
  let pbp = Filename.concat dir "model.pbp" in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ title ] c.Compile.encoding oc;
  close_out oc;
  let oc = open_out pbp in
  let writer = Writer.create ~comments:true ~audit:true oc in
  Encoding.start_proof c.Compile.encoding writer;
  let ctx =
    Justify.create ~writer ~encoding:c.Compile.encoding ~model_id:(fun () ->
        failwith
          "test_compile: search demanded Explanation.Trivial -- an instance is missing \
           its row id (D-0011)")
  in
  let entry_level = Store.level c.Compile.store in
  let outcome =
    Search.solve ~engine:c.Compile.engine ~store:c.Compile.store ~ctx
      ~check:(fun a -> evaluate m (assignment_array m a))
      ()
  in
  close_out oc;
  check
    (Printf.sprintf "%s: decision level restored on return (I-S3)" title)
    (entry_level = Store.level c.Compile.store);
  (match outcome with
  | Search.Sat a ->
      check (Printf.sprintf "%s: agrees with brute force (SAT)" title) expect_sat;
      check
        (Printf.sprintf "%s: the solution satisfies the model, re-checked (I-S1)" title)
        (evaluate m (assignment_array m a));
      check
        (Printf.sprintf "%s: the assignment covers every model variable" title)
        (List.length a = M.nvars m)
  | Search.Unsat ->
      check (Printf.sprintf "%s: agrees with brute force (UNSAT)" title) (not expect_sat));
  (match veripb_path () with
  | None ->
      incr failures;
      Printf.printf
        "FAIL %s: veripb not found -- I-X1 was NOT checked. Do not treat this as a pass.\n"
        title
  | Some veripb ->
      let log = Filename.concat dir "log" in
      let rc =
        Sys.command
          (Printf.sprintf "%s %s %s > %s 2>&1" (Filename.quote veripb)
             (Filename.quote opb) (Filename.quote pbp) (Filename.quote log))
      in
      check (Printf.sprintf "%s: veripb accepts the proof (I-X1)" title) (rc = 0);
      if rc <> 0 then
        Printf.printf "  veripb said:\n%s\n  model:\n%s\n  proof:\n%s\n" (read_file log)
          (read_file opb) (read_file pbp));
  List.iter
    (fun f -> try Sys.remove f with _ -> ())
    [ opb; pbp; Filename.concat dir "log" ];
  try Sys.rmdir dir with _ -> ()

let test_end_to_end () =
  (* SAT. Offset domains and a mix of constraint kinds, so the answer depends on the
     variable order being right: a permutation of x and y would break int_lt. *)
  run_model ~title:"e2e sat: x < y, x + y <= 5"
    ~src:
      "var 1..4: x;\n\
       var 1..4: y;\n\
       constraint int_lin_le([1,1],[x,y],5);\n\
       constraint int_lt(x,y);\n\
       solve satisfy;\n";
  (* UNSAT, refuted at the root by bounds propagation with no decision active: the >=
     row forces x2 >= 1, the <= row forces x2 <= 1, and 2*x1 = 3 has no integer
     solution. D-0013/D-0015: this is the case whose derivation veripb accepts. *)
  run_model ~title:"e2e unsat: 2*x1 + 4*x2 = 7 over [0,3]"
    ~src:
      "var 0..3: x1;\n\
       var 0..3: x2;\n\
       constraint int_lin_eq([2,4],[x1,x2],7);\n\
       solve satisfy;\n";
  (* UNSAT from a ground constraint alone: int_le(2, 1) folds to an empty term list
     with a negative right-hand side. The .opb row is `>= 1 ;` with no literals and the
     propagator conflicts on the first pass; both halves of that had to be checked
     against the real checker rather than assumed, which is what this run does. *)
  run_model ~title:"e2e unsat: a ground constraint that does not hold"
    ~src:
      "var 1..3: x;\nconstraint int_le(x,3);\nconstraint int_le(2,1);\nsolve satisfy;\n";
  (* M1-T40: the three models that reach [evaluate]'s disequality arms. Before these,
     both arms were a [failwith] nothing had ever executed.

     SAT, int_ne: the search must branch (a disequality infers nothing until all but
     one of its terms is fixed), so [evaluate] is called by [brute_force] over the
     whole box, again as [Search.solve]'s [~check], and once more on the answer. *)
  run_model ~title:"e2e sat: int_ne, the search must branch to find a witness"
    ~src:"var 1..2: x;\nvar 1..2: y;\nconstraint int_ne(x,y);\nsolve satisfy;\n";
  (* SAT, int_lin_ne, with coefficients past +/-1 so that [value]'s multiplication is
     exercised rather than only its addition: 2x + 3y <> 7 rules out (2,1) and (5,-1),
     and of those only (2,1) is in the box, so the oracle must reject exactly one of
     the four assignments -- an arm that answered [=] would pick that one and nothing
     else, which is what makes this model able to see the inversion. *)
  run_model ~title:"e2e sat: int_lin_ne, 2x + 3y <> 7, coefficients past +/-1"
    ~src:
      "var 1..2: x;\n\
       var 1..2: y;\n\
       constraint int_lin_ne([2,3],[x,y],7);\n\
       solve satisfy;\n";
  (* UNSAT at the root, and the case where the two arms cannot cover for each other:
     int_ne(x,x) is false for every x, so [brute_force] must return [None] -- an arm
     reading [=] makes it satisfiable everywhere and the run disagrees with the solver
     rather than merely picking a different witness. Compile folds the two occurrences
     into a zero coefficient and the empty false sum (see compile.ml's header), so the
     solver reaches UNSAT by a route that shares nothing with the oracle's reading. *)
  run_model ~title:"e2e unsat: int_ne(x, x) is false for every x"
    ~src:"var 1..3: x;\nconstraint int_ne(x,x);\nsolve satisfy;\n"

(* ------------------------------------------------------------------------- main *)

let () =
  print_endline "";
  test_variable_identity ();
  test_instance_counts ();
  test_normalise_terms ();
  test_constant_folding ();
  test_duplicate_coefficients ();
  test_ground_constraints ();
  test_disequalities ();
  test_rejections ();
  test_oracle_arithmetic ();
  test_end_to_end ();
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "\ncompile tests passed"
