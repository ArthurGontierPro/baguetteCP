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

(* M1-T53: bound this binary's OCaml heap so a runaway test aborts itself,
   naming the cap, rather than relying on an outer `ulimit -v` a bare
   `dune runtest --root .` does not apply. See mem_guard.ml. *)
let () = Mem_guard.install ()
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
  (* M5-T1 landed the milestone these two used to name, so what asserted the rejection
     now asserts that an objective over a VARIABLE compiles. The rejection did not
     disappear, it narrowed: a CONSTANT objective is still refused, because `conclusion
     BOUNDS` needs a `min:` line in the .opb and a constant has no order literals to
     write one out of. The four together are what stop the narrowing from becoming a
     silent widening -- I-M1's "a failing test is information" cuts both ways, and an
     expectation deleted rather than replaced is the information being thrown away. *)
  expect_accepted "accept: minimize over a variable compiles (M5-T1)"
    "var 0..3: x;\nconstraint int_le(x,3);\nsolve minimize x;\n";
  expect_accepted "accept: maximize over a variable compiles (M5-T1)"
    "var 0..3: x;\nconstraint int_le(x,3);\nsolve maximize x;\n";
  expect_rejected "reject: a CONSTANT objective says why it cannot be proved optimal"
    ~needles:[ "minimize"; "VARIABLE"; "min:"; "4.3" ]
    "var 0..3: x;\nconstraint int_le(x,3);\nsolve minimize 2;\n";
  expect_rejected "reject: ... and the same for maximize" ~needles:[ "maximize"; "var " ]
    "var 0..3: x;\nconstraint int_le(x,3);\nsolve maximize 2;\n";
  (* M7-T2 IMPLEMENTED these three, so the expectation moved from "rejected" to
     "accepted AND honoured". The rejection did not disappear -- it narrowed onto the
     tail that is still not implemented, which the four [expect_rejected]s below hold,
     and what the annotation actually DOES is asserted on the decision itself in
     [test_search_annotations]. An expectation deleted rather than replaced is the
     information thrown away (I-M1), so all three now sit here as acceptances. *)
  expect_accepted "accept: input_order is implemented (M7-T2)"
    "var 0..3: x;\n\
     constraint int_le(x,3);\n\
     solve :: int_search([x],input_order,indomain_min,complete) satisfy;\n";
  expect_accepted "accept: indomain_max is implemented (M7-T2)"
    "var 0..3: x;\n\
     constraint int_le(x,3);\n\
     solve :: int_search([x],first_fail,indomain_max,complete) satisfy;\n";
  expect_accepted "accept: seq_search mixing the two variable choices (M7-T2)"
    "var 0..3: x;\n\
     var 0..3: y;\n\
     constraint int_le(x,y);\n\
     solve :: \
     seq_search([int_search([x],first_fail,indomain_min,complete),int_search([y],input_order,indomain_min,complete)]) \
     satisfy;\n";
  (* M7-T2 obligation (d): the tail is REFUSED BY NAME, not silently replaced. These
     four are the strategies the MiniZinc-challenge census found beyond the implemented
     set, most frequent first (smallest 56, indomain_split 64, largest 12, dom_w_deg 4).
     Each needle is the strategy's own name: a message that does not name it is not the
     message docs/SPEC.md 3.4 asks for. *)
  expect_rejected "reject (d): `smallest` is named, not silently replaced"
    ~needles:[ "smallest"; "first_fail"; "input_order" ]
    "var 0..3: x;\n\
     constraint int_le(x,3);\n\
     solve :: int_search([x],smallest,indomain_min,complete) satisfy;\n";
  expect_rejected "reject (d): `largest` is named" ~needles:[ "largest" ]
    "var 0..3: x;\n\
     constraint int_le(x,3);\n\
     solve :: int_search([x],largest,indomain_min,complete) satisfy;\n";
  expect_rejected "reject (d): `indomain_split` is named"
    ~needles:[ "indomain_split"; "indomain_min"; "indomain_max" ]
    "var 0..3: x;\n\
     constraint int_le(x,3);\n\
     solve :: int_search([x],first_fail,indomain_split,complete) satisfy;\n";
  (* And a whole annotation FORM that is not implemented. Before M7-T2 this one fell
     into [search_of_annot]'s catch-all and was SILENTLY DROPPED -- the model was
     accepted and searched by the default, which is the one outcome docs/SPEC.md 3.4
     forbids. It is named and refused now. *)
  expect_rejected "reject (d): an unimplemented *_search FORM is named, not dropped"
    ~needles:[ "float_search"; "int_search"; "3.4" ]
    "var 0..3: x;\n\
     constraint int_le(x,3);\n\
     solve :: float_search([x],first_fail,indomain_min,complete) satisfy;\n";
  expect_rejected "reject (d): ... and so is priority_search"
    ~needles:[ "priority_search" ]
    "var 0..3: x;\n\
     constraint int_le(x,3);\n\
     solve :: \
     priority_search([x],[int_search([x],first_fail,indomain_min,complete)],smallest,complete) \
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
  let arith_aux x y (aux : M.aux) =
    (match aux.M.x_sign with
    | None -> true
    | Some b -> truth (M.Var b) = (operand x >= 0))
    && List.for_all (fun (v, b) -> truth (M.Var b) = (operand y >= v)) aux.M.y_ge
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
      | M.Int_ne (a, b) -> operand a <> operand b
      (* M3-T2. Same rule again: read off the FlatZinc definition of each reified
         builtin, as an equivalence in both directions, and NOT off
         [Model.check_assignment] or off lib/core/prop/reif*.ml. The `_reif` row of
         SPEC 2.1's M3 table is exactly these four, and [test_reified]'s run_model
         lanes below are what reach them. *)
      | M.Int_lin_le_reif (ts, r, b) -> truth b = (value ts <= r)
      | M.Int_le_reif (a, b, r) -> truth r = (operand a <= operand b)
      | M.Int_eq_reif (a, b, r) -> truth r = (operand a = operand b)
      | M.Int_ne_reif (a, b, r) -> truth r = (operand a <> operand b)
      (* M4-T4b, and the rule once more: read off docs/SPEC.md 2.1, not off
         [Model.check_assignment] and not off [Baguette_core.Arith.is_in_relation].
         [Stdlib.(/)] truncates toward zero, which is what the spec asks for; y = 0 is
         simply not in the relation, which is D-0033's "relational, not an error".

         The auxiliary Booleans are checked here too. They are ordinary variables of
         the model, so a brute-force enumeration reaches assignments that violate their
         definitions, and an oracle that ignored them would call those solutions -- and
         then disagree with [Model.check_assignment], which does not. *)
      | M.Int_times (a, b, c, aux) ->
          operand a * operand b = operand c && arith_aux a b aux
      | M.Int_div (a, b, c, aux) ->
          operand b <> 0 && operand a / operand b = operand c && arith_aux a b aux
      | M.Int_abs (a, c, aux) -> operand c = abs (operand a) && arith_aux a a aux
      (* M4-T1. The RELATION, restated here rather than shared with
         [Model.check_assignment] -- this oracle exists to disagree with the solver, and
         all_different's decomposition into pairwise rows is exactly the thing it has to
         be able to disagree about. *)
      | M.All_different xs ->
          let vs = List.map operand xs in
          let rec distinct = function
            | [] -> true
            | v :: rest -> (not (List.mem v rest)) && distinct rest
          in
          distinct vs
      (* M4-T3. This file's own reading of the relation, kept separate from
         [Model.check_assignment]'s: the index is 1-based and must land inside the array,
         and an out-of-range index makes the constraint FALSE rather than vacuous. Two
         independent statements of one rule is the point -- [test_element_oracle] above
         judges with [Model.check_assignment], this one judges the end-to-end solutions. *)
      | M.Array_int_element (i, vs, c) ->
          let k = operand i in
          k >= 1 && k <= Array.length vs && vs.(k - 1) = operand c)
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
   Every test module open-coded this search, and every copy resolved it differently --
   so a project-wide choice of checker lived in nine places and could silently mean a
   build nobody intended (M1-T18). [None] is a FAILURE at every
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

(* [?order] defaults to the model's OWN compiled annotation, which is what bin/main.ml
   passes (`?order:compiled.Compile.order` at its two Search call sites). So an
   annotated model run through here is searched the way the annotation says and its
   proof is checked in that shape -- M7-T2 obligation (c). [~order] overrides it, and
   exists for the break lane below. *)
let run_model_with ?order ?mutate ?(expect_reject = false) ~title ~src () =
  let m = build src in
  let c = Compile.compile m in
  let order = match order with Some o -> Some o | None -> c.Compile.order in
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
  (* This used to install a [~model_id] thunk that failed, to catch a propagator
     instance built without its row id. M1-T31 deleted the field: there is no ambient
     row for such an instance to fall back on, so the guard has nothing to guard. *)
  let ctx = Justify.create ~writer ~encoding:c.Compile.encoding in
  let entry_level = Store.level c.Compile.store in
  let outcome =
    Search.solve ~engine:c.Compile.engine ~store:c.Compile.store ~ctx
      ~check:(fun a -> evaluate m (assignment_array m a))
      ?order ()
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
  (* M7-T2 break lane: rewrite the emitted proof before the checker sees it. The
     mutation runs on the REAL proof of an annotated run, so what it corrupts is a line
     the annotated tree actually produced -- a lane that mutated a hand-written proof
     would prove nothing about this tree. *)
  (match mutate with
  | None -> ()
  | Some f ->
      let lines = String.split_on_char '\n' (read_file pbp) in
      let oc = open_out pbp in
      List.iter (fun l -> output_string oc (l ^ "\n")) (f lines);
      close_out oc);
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
      if expect_reject then (
        (* The break lane. An exit status alone cannot tell a JUDGEMENT from a parse
           error (CLAUDE.md, "A lane that asserts a rejection must assert the checker's
           WORDING"), so the wording is asserted too and the log is printed when it is
           not what was expected. *)
        let out = read_file log in
        check
          (Printf.sprintf "%s: veripb REJECTS the proof" title)
          (rc <> 0
          && (contains ~needle:"reverse unit propagation" out
             || contains ~needle:"Failed to check" out
             || contains ~needle:"not implied" out));
        if rc = 0 then
          Printf.printf "  veripb ACCEPTED a proof this lane requires it to reject.\n")
      else (
        check (Printf.sprintf "%s: veripb accepts the proof (I-X1)" title) (rc = 0);
        if rc <> 0 then
          Printf.printf "  veripb said:\n%s\n  model:\n%s\n  proof:\n%s\n" (read_file log)
            (read_file opb) (read_file pbp)));
  List.iter
    (fun f -> try Sys.remove f with _ -> ())
    [ opb; pbp; Filename.concat dir "log" ];
  try Sys.rmdir dir with _ -> ()

(* The pre-M7-T2 shape, kept so that every existing end-to-end call site reads exactly as
   it did. It takes the model's own compiled order, which for an unannotated model is
   [None] and therefore [Search.solve]'s own default. *)
let run_model ~title ~src = run_model_with ~title ~src ()

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
    ~src:"var 1..3: x;\nconstraint int_ne(x,x);\nsolve satisfy;\n";

  (* M3-T2, against the independent oracle and against veripb. Five lanes, one per
     dispatcher case plus the two degenerate conditions [Encoding]'s doors refuse by
     name -- a model that says something trivially true is still a model, and what
     compile does with it is answer, not raise. *)
  run_model ~title:"e2e reif: the reifier is decided by the domains (refuted)"
    ~src:
      "var 0..3: x;\n\
       var 0..3: y;\n\
       var bool: b;\n\
       constraint int_le_reif(x,y,b);\n\
       constraint int_lin_le([-1],[x],-3);\n\
       constraint int_lin_le([1],[y],1);\n\
       solve satisfy;\n";
  run_model ~title:"e2e reif: int_eq_reif with the equality entailed"
    ~src:
      "var 0..2: x;\n\
       var 0..2: y;\n\
       var bool: b;\n\
       constraint int_eq_reif(x,y,b);\n\
       constraint int_lin_le([1],[x],1);\n\
       constraint int_lin_le([-1],[x],-1);\n\
       constraint int_lin_le([1],[y],1);\n\
       constraint int_lin_le([-1],[y],-1);\n\
       solve satisfy;\n";
  run_model ~title:"e2e reif: int_ne_reif is the same author, inverted"
    ~src:
      "var 0..2: x;\n\
       var 0..2: y;\n\
       var bool: b;\n\
       constraint int_ne_reif(x,y,b);\n\
       constraint int_lin_le([1],[y],0);\n\
       constraint int_lin_le([-1],[y],0);\n\
       constraint bool_clause([b],[]);\n\
       solve satisfy;\n";
  run_model ~title:"e2e reif: a condition the declared domains already entail"
    ~src:
      "var 0..1: x;\n\
       var 2..3: y;\n\
       var bool: b;\n\
       constraint int_le_reif(x,y,b);\n\
       solve satisfy;\n";
  run_model ~title:"e2e reif: a condition the declared domains already refute"
    ~src:
      "var 2..3: x;\n\
       var 0..1: y;\n\
       var bool: b;\n\
       constraint int_le_reif(x,y,b);\n\
       solve satisfy;\n";
  (* M4-T4b. [brute_force] enumerates the declared box, [evaluate]'s three new arms
     judge it, and [Search.solve] has to agree -- including about the AUXILIARY
     Booleans, which the enumeration also ranges over. An oracle branch nobody has seen
     run is what D-0030 is about, so these lanes land with the arms they reach.

     Domains are deliberately tiny: the enumeration is over every variable including
     the auxiliaries, so a case variable of width w costs a factor of 2^w on its own. *)
  run_model ~title:"e2e arith: int_times over two straddling factors"
    ~src:
      "var -2..2: x;\n\
       var -1..1: y;\n\
       var -2..2: z;\n\
       constraint int_times(x,y,z);\n\
       solve satisfy;\n";
  run_model ~title:"e2e arith: int_div, divisor may be zero (D-0033)"
    ~src:
      "var -2..2: x;\n\
       var -1..1: y;\n\
       var -2..2: q;\n\
       constraint int_div(x,y,q);\n\
       solve satisfy;\n";
  run_model ~title:"e2e arith: int_div whose only divisor is zero is UNSAT, not an error"
    ~src:
      "var 1..2: x;\n\
       var 0..0: y;\n\
       var 0..2: q;\n\
       constraint int_div(x,y,q);\n\
       solve satisfy;\n";
  run_model ~title:"e2e arith: int_abs across zero"
    ~src:"var -2..2: x;\nvar 0..2: z;\nconstraint int_abs(x,z);\nsolve satisfy;\n";
  run_model ~title:"e2e arith: int_abs whose z cannot hold every |x| is still SAT"
    ~src:"var -3..3: x;\nvar 0..1: z;\nconstraint int_abs(x,z);\nsolve satisfy;\n"

(* ------------------------------------------------------- M3: the reified builtins *)

(* The front end's half of M3-T2: the four builtins are compiled, the two things that
   can be wrong about a reifier are positioned diagnostics, and a condition the declared
   domains already settle keeps its meaning instead of raising out of [Encoding]. *)
let test_reified () =
  expect_accepted "accept: int_lin_le_reif compiles (M3-T2)"
    "var 0..3: x;\n\
     var 0..3: y;\n\
     var bool: b;\n\
     constraint int_lin_le_reif([1,-1],[x,y],0,b);\n\
     solve satisfy;\n";
  expect_accepted "accept: int_le_reif compiles (M3-T2)"
    "var 0..3: x;\n\
     var 0..3: y;\n\
     var bool: b;\n\
     constraint int_le_reif(x,y,b);\n\
     solve satisfy;\n";
  expect_accepted "accept: int_eq_reif compiles (M3-T2)"
    "var 0..3: x;\n\
     var 0..3: y;\n\
     var bool: b;\n\
     constraint int_eq_reif(x,y,b);\n\
     solve satisfy;\n";
  expect_accepted "accept: int_ne_reif compiles (M3-T2)"
    "var 0..3: x;\n\
     var 0..3: y;\n\
     var bool: b;\n\
     constraint int_ne_reif(x,y,b);\n\
     solve satisfy;\n";
  (* A reifier is a `var bool` (D-0007), and the diagnostic says which variable. *)
  expect_rejected "reject: a non-Boolean reifier names the variable and the builtin"
    ~needles:[ "int_le_reif"; "`r`" ]
    "var 0..3: x;\n\
     var 0..3: y;\n\
     var 0..3: r;\n\
     constraint int_le_reif(x,y,r);\n\
     solve satisfy;\n";
  (* b <-> C(b) is not a definition -- [Encoding.reif_rows] raises [Reif_in_condition]
     for the same shape, and compile refuses it earlier, with a position. *)
  expect_rejected "reject: a reifier occurring in its own condition"
    ~needles:[ "int_lin_le_reif"; "`b`"; "not a definition" ]
    "var 0..3: x;\n\
     var bool: b;\n\
     constraint int_lin_le_reif([1,1],[x,b],2,b);\n\
     solve satisfy;\n";
  (* The degenerate cases. `x <= y` is entailed by the declared domains, so this is not
     a reification at all: [Encoding]'s doors refuse such a condition by name, and
     compile answers with a unit row fixing the reifier rather than propagating the
     exception. The two run_model lanes below are what check the ANSWER. *)
  expect_accepted "accept: a condition the declared domains entail fixes the reifier"
    "var 0..1: x;\n\
     var 2..3: y;\n\
     var bool: b;\n\
     constraint int_le_reif(x,y,b);\n\
     solve satisfy;\n";
  expect_accepted "accept: a condition the declared domains refute fixes the reifier"
    "var 2..3: x;\n\
     var 0..1: y;\n\
     var bool: b;\n\
     constraint int_le_reif(x,y,b);\n\
     solve satisfy;\n";
  expect_accepted "accept: an equality the declared domains settle fixes the reifier"
    "var 1..1: x;\n\
     var 1..1: y;\n\
     var bool: b;\n\
     constraint int_eq_reif(x,y,b);\n\
     solve satisfy;\n"

(* --------------------------------------------------- M4-T3: array_int_element *)

(* THE BRUTE-FORCE ORACLE, and the distinction lib/core/interval.ml's own tests make
   between equality and containment.

   Every total assignment over the DECLARED box is enumerated and judged by
   [Model.check_assignment] -- which is written from docs/SPEC.md and from nothing in
   lib/core/prop/, so it cannot agree with the propagator by construction -- and the
   survivors are projected back onto each variable. That projection is the
   domain-consistent closure of the WHOLE model.

   For a model whose only constraint is the element, the closure and the propagator's
   fixpoint must be EQUAL: lib/core/prop/element.ml declares [Domain], and D-0059 is
   explicit that the tag is a claim the code is held to. With a second constraint in the
   model, propagation to a fixpoint is not global domain consistency and only CONTAINMENT
   is claimed -- asserting equality there would be asserting something false about
   propagation in general rather than about this propagator. *)
let closure_and_fixpoint src =
  let m = build src in
  let c = Compile.compile m in
  let n = M.nvars m in
  let decl = Array.init n (fun i -> Store.get c.Compile.store (Var.of_int i)) in
  let acc = Array.make n [] in
  let values = Array.make n 0 in
  let rec go i =
    if i = n then (
      if M.check_assignment m values then
        Array.iteri
          (fun k v -> if not (List.mem v acc.(k)) then acc.(k) <- v :: acc.(k))
          values)
    else
      Domain.iter
        (fun v ->
          values.(i) <- v;
          go (i + 1))
        decl.(i)
  in
  go 0;
  let fixpoint =
    match Engine.propagate c.Compile.engine c.Compile.store with
    | Engine.Conflict _ -> None
    | Engine.Fixpoint ->
        Some
          (Array.init n (fun i ->
               Domain.to_list (Store.get c.Compile.store (Var.of_int i))))
  in
  (Array.map (List.sort compare) acc, fixpoint, c, m)

let show l = String.concat "," (List.map string_of_int l)

let test_element_oracle () =
  (* Exact: the element is the whole model, so the fixpoint IS the closure. `c`'s
     projection is {3, 5, 7} -- two interior HOLES, at 4 and 6, which a bounds-consistent
     element would not punch. That is the assertion D-0059 says starts separating the
     Bounds and Domain tags, and a propagator that only pushed bounds reddens here. *)
  let closure, fixpoint, _, _ =
    closure_and_fixpoint
      "var 1..4: i;\n\
       var 0..9: c;\n\
       constraint array_int_element(i, [3, 7, 3, 5], c);\n\
       solve satisfy;\n"
  in
  (match fixpoint with
  | None -> check "element (a): the single-constraint scene is satisfiable" false
  | Some f ->
      check "element (a): index -- fixpoint EQUALS the domain-consistent closure"
        (List.equal Int.equal f.(0) closure.(0));
      if not (List.equal Int.equal f.(1) closure.(1)) then
        fail "element (a): result -- fixpoint EQUALS the domain-consistent closure"
          (Printf.sprintf "closure {%s}, fixpoint {%s}" (show closure.(1)) (show f.(1)))
      else
        check "element (a): result -- fixpoint EQUALS the domain-consistent closure" true;
      check
        "element (a): and the closure really has interior holes, so the scene is one a \
         Bounds propagator would fail"
        (List.equal Int.equal closure.(1) [ 3; 5; 7 ]));
  (* Exact, and empty: every array value is outside c's declared range, so the closure is
     empty and the propagator must refute rather than merely narrow. *)
  let closure, fixpoint, _, _ =
    closure_and_fixpoint
      "var 1..3: i;\n\
       var 0..4: c;\n\
       constraint array_int_element(i, [7, 8, 9], c);\n\
       solve satisfy;\n"
  in
  check "element (a): the closure of the out-of-range scene is empty" (closure.(0) = []);
  check "element (a): and the propagator reports the conflict, not a narrowing"
    (fixpoint = None);
  (* Containment only: a second constraint is in the model. *)
  let closure, fixpoint, _, _ =
    closure_and_fixpoint
      "var 1..4: i;\n\
       var 0..9: c;\n\
       constraint array_int_element(i, [3, 7, 3, 5], c);\n\
       constraint int_le(c, 4);\n\
       solve satisfy;\n"
  in
  match fixpoint with
  | None -> check "element (a): the two-constraint scene is satisfiable" false
  | Some f ->
      check "element (a): index -- the fixpoint CONTAINS the closure (two constraints)"
        (List.for_all (fun v -> List.mem v f.(0)) closure.(0));
      check "element (a): result -- the fixpoint CONTAINS the closure (two constraints)"
        (List.for_all (fun v -> List.mem v f.(1)) closure.(1))

(* M4-T3's obligation (d): the index really is a VIEW.

   D-0058 bought exactly one property and this is it -- there is no auxiliary variable
   between the propagator and the index, so a value-level pruning lands in the index's
   OWN domain with no channelling step at which to lose it. Two independent assertions,
   because each fails differently:

   1. the store holds exactly the model's variables. An auxiliary [p = i - 1] would be a
      third one, and [Store.n_vars] would say so.
   2. the pruning is an interior HOLE in `i`. A channelled auxiliary could carry the two
      BOUNDS back to `i`, so a test that only checked lo/hi would pass against the shape
      D-0058 rejected; a hole is what a bounds-consistent channel cannot carry, which is
      why this is the assertion and not the bounds. *)
let test_element_view () =
  let src =
    "var 1..4: i;\n\
     var 0..9: c;\n\
     constraint array_int_element(i, [3, 7, 3, 5], c);\n\
     constraint int_le(c, 4);\n\
     solve satisfy;\n"
  in
  let m = build src in
  let c = Compile.compile m in
  check "element (d): the model has exactly two variables" (M.nvars m = 2);
  check
    "element (d): and the store holds exactly those -- no auxiliary for the shifted \
     index (D-0058)"
    (Store.n_vars c.Compile.store = M.nvars m);
  (match Engine.propagate c.Compile.engine c.Compile.store with
  | Engine.Conflict _ -> check "element (d): the scene propagates without conflict" false
  | Engine.Fixpoint ->
      let d = Store.get c.Compile.store (Var.of_int 0) in
      check "element (d): the index keeps both ends" (Domain.lo d = 1 && Domain.hi d = 3);
      check "element (d): and the pruning is an interior HOLE in the index's OWN domain"
        (Domain.is_hole d 2);
      check "element (d): every trail entry names a model variable, never a third one"
        (List.for_all
           (fun (e : Store.entry) -> Var.to_int e.Store.var < M.nvars m)
           (Store.trail_entries c.Compile.store)));
  check
    "element (d): the propagator declares DOMAIN consistency, and the oracle holds it to \
     it (D-0059)"
    (Baguette_core.Element.consistency = Baguette_core.Propagator.Domain)

let test_element_shape () =
  let three body =
    Printf.sprintf "var 1..3: i;\nvar 0..3: c;\n%s\nsolve satisfy;\n" body
  in
  let n, _ = instances_and_rows (three "constraint array_int_element(i, [1,2,3], c);") in
  check "element: one instance for one array_int_element" (n = 1);
  (* A constant index never reaches the propagator: compile.ml decomposes it to the
     int_eq shape, which is TWO Linear instances (D-0011) and no element at all. *)
  let n, _ = instances_and_rows (three "constraint array_int_element(2, [1,2,3], c);") in
  check
    "element: a constant index decomposes to int_eq -- two Linear instances, no element \
     instance"
    (n = 2);
  let n, rows =
    instances_and_rows (three "constraint array_int_element(4, [1,2,3], c);")
  in
  check "element: an out-of-range constant index is one ground row" (n = 1 && rows >= 1)

(* M4-T8 obligation (d): D-0064's level rule, demonstrated rather than asserted.

   A bound the ROOT fixpoint sets stays citable via [Explanation.Defining] at any
   search depth; one a DECISION sets is not, and lib/core/prop/element.ml's
   [established_at_root] is the per-literal check that draws that line (mirroring
   lib/core/prop/alldiff.ml:179's function of the same name -- alldiff.ml is
   read-only to this task, so this is element.ml's own copy, not a shared one).

   The check below reads the forced [Explanation.Combine]'s own summand list rather
   than going through [Search.rests_on_a_clause]: that function answers a narrower
   question ("would a root-conflict CLOSE its own pol"), and a [Defining] OMITTED
   (scene B, below) looks identical to it as "no Clause present either" -- both give
   [false] -- so it cannot tell "omitted" from "cancelled". Looking for the actual
   [Defining (_, Lit.le "c" 2)] summand is the direct question this test asks.

   Both scenes are the IDENTICAL model -- test/models/element_moved_unsat.fzn's own
   source, restated -- and reach the identical conflict; what differs is only the LEVEL
   it is reached at. [established_at_root] does not care whether a genuine decision
   literal sits on the trail, only where the support that moved the bound was pushed
   (lib/core/store.ml's [level_of_index]), so scene B pushes one bare level with
   [Store.new_level] before propagating and never resolves it -- the cheapest honest way
   to make every trail entry this run produces belong to level 1 rather than level 0,
   without hand-building a [Reason.justified] this test does not otherwise need. *)

(* A live proof writer, so [Encoding.at_least_one_id] and friends have an id to hand
   back when the conflict's explanation is forced -- without one, [Element]'s [need]
   raises exactly as it should (see its own comment), which is right for a
   propagate-only test elsewhere but not for one that deliberately forces the
   derivation here. The temp file is discarded; nothing about this test reads it back,
   only the constraint ids [start_proof] mints as a side effect of writing it. *)
let with_proof m f =
  let c = Compile.compile m in
  let dir = Filename.temp_file "baguette_el_lvl" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  let oc = open_out (Filename.concat dir "p.pbp") in
  let writer = Writer.create ~audit:true oc in
  Encoding.start_proof c.Compile.encoding writer;
  let result = f c in
  close_out oc;
  (try Sys.remove (Filename.concat dir "p.pbp") with _ -> ());
  (try Sys.rmdir dir with _ -> ());
  result

(* Whether the conflict's own top-level combine cites [Explanation.Defining] on
   exactly the literal this scene's residue would cancel: [c]'s moved upper bound,
   "c <= 2". Top level only -- residue_cancel's summands land directly in
   [no_position_conflict]'s own [Combine], never nested inside a [Term]. *)
let cites_defining_le (e : Baguette_core.Explanation.t) ~name ~bound =
  match Baguette_core.Explanation.force e with
  | Baguette_core.Explanation.Combine (summands, _) ->
      List.exists
        (function
          | Baguette_core.Explanation.Defining (_, l) ->
              Baguette_proof.Lit.equal l (Baguette_proof.Lit.le name bound)
          | _ -> false)
        summands
  | _ -> false

let test_element_defining_level_rule () =
  let src_a =
    "var 1..2: i;\n\
     var 1..2: j;\n\
     var 0..9: c;\n\
     constraint array_int_element(i, [1, 2], c);\n\
     constraint array_int_element(j, [3, 4], c);\n\
     solve satisfy;\n"
  in
  let m_a = build src_a in
  with_proof m_a (fun ca ->
      match Engine.propagate ca.Compile.engine ca.Compile.store with
      | Engine.Conflict c ->
          check
            "element (d) scene A: at the ROOT, `conclusion UNSAT`'s own derivation cites \
             Defining(c <= 2) -- the moved bound IS cancelled exactly"
            (cites_defining_le c.Store.c_why ~name:"c" ~bound:2)
      | Engine.Fixpoint ->
          check "element (d) scene A: the root scene is UNSAT, not a fixpoint" false);
  let m_b = build src_a in
  with_proof m_b (fun cb ->
      Store.new_level cb.Compile.store;
      match Engine.propagate cb.Compile.engine cb.Compile.store with
      | Engine.Conflict c ->
          check
            "element (d) scene B: the IDENTICAL conflict, reached one level deeper, does \
             NOT cite Defining(c <= 2) -- a bound this run only ever set at level 1 is \
             not cited, D-0064's level rule holding exactly where scene A shows it not \
             holding"
            (not (cites_defining_le c.Store.c_why ~name:"c" ~bound:2))
      | Engine.Fixpoint ->
          check "element (d) scene B: the scene is UNSAT one level deeper too" false)

(* ----------------------------------------- 5b. M7-T2: the annotation, HONOURED

   docs/SPEC.md 3.4 says a search annotation MUST be honoured when present. Until M7-T2
   the only way to honour it was to refuse the model; now it is implemented, and
   "implemented" is a claim about WHICH VARIABLE GETS BRANCHED ON, not about the answer.
   Two strategies that agree on every test are not tested -- a solver that ignored the
   annotation entirely would pass a suite that only checked answers, because the answer
   set does not depend on the order at all.

   So every assertion here is on the DECISION: [Compile.t.order] is called directly with
   the store and a candidate array, and its [d_var] / [d_split] / [d_high_first] are
   asserted. *)

let decision_of ?cands src =
  let m = build src in
  let c = Compile.compile m in
  let order =
    match c.Compile.order with
    | Some o -> o
    | None -> failwith "decision_of: this model was expected to carry a search annotation"
  in
  let cands =
    match cands with
    | Some idxs -> Array.of_list (List.map Var.of_int idxs)
    | None -> Search.unfixed c.Compile.store
  in
  (m, c, order c.Compile.store cands)

(* The scene for obligation (a). Two variables that every strategy can tell apart:

     wide   0..7   declared first, WIDEST domain
     narrow 0..1   declared second, NARROWEST domain

   input_order must pick [wide] (it is first in the annotation's array); first_fail must
   pick [narrow] (its domain has 2 values against 8). The two provably disagree, on the
   same model, differing in one token of the annotation. Neither constraint prunes, so
   both variables are still unfixed when the order is asked. *)
let scene ?(vars = "wide,narrow") ?(vsel = "input_order") ?(valsel = "indomain_min") () =
  Printf.sprintf
    "var 0..7: wide;\n\
     var 0..1: narrow;\n\
     constraint int_le(wide,7);\n\
     constraint int_le(narrow,1);\n\
     solve :: int_search([%s],%s,%s,complete) satisfy;\n"
    vars vsel valsel

let test_search_annotations () =
  print_endline "";
  (* --- (a) the variable choice. The two strategies disagree, and each is right. *)
  let _, _, d_in = decision_of (scene ~vsel:"input_order" ()) in
  let _, _, d_ff = decision_of (scene ~vsel:"first_fail" ()) in
  check "(a) input_order picks the FIRST variable of the annotation array (wide)"
    (Var.to_int d_in.Search.d_var = 0);
  check "(a) first_fail picks the SMALLEST-domain variable (narrow)"
    (Var.to_int d_ff.Search.d_var = 1);
  check "(a) ... and those are different variables, on one and the same model"
    (Var.to_int d_in.Search.d_var <> Var.to_int d_ff.Search.d_var);
  (* input_order reads the ANNOTATION's order, not declaration order. This is the
     assertion that fails if [phase.p_vars] is ever rebuilt from the store instead of
     from the array the annotation wrote: with the array reversed, input_order must
     follow it, and first_fail must NOT move. *)
  let _, _, d_in_rev = decision_of (scene ~vars:"narrow,wide" ~vsel:"input_order" ()) in
  let _, _, d_ff_rev = decision_of (scene ~vars:"narrow,wide" ~vsel:"first_fail" ()) in
  check "(a) input_order follows the ARRAY order, not declaration order"
    (Var.to_int d_in_rev.Search.d_var = 1);
  check "(a) ... while first_fail is indifferent to it"
    (Var.to_int d_ff_rev.Search.d_var = 1);
  (* --- (a) the value choice, on the SAME variable, so only the split can differ.
     indomain_min splits at lo and takes the low side first (that branch fixes x = lo);
     indomain_max splits at hi-1 and takes the HIGH side first (that branch fixes
     x = hi). Both halves have to move: "the same split, other side first" would be a
     different strategy, and asserting only [d_high_first] would not see it. *)
  let _, _, d_min = decision_of (scene ~vars:"wide" ~valsel:"indomain_min" ()) in
  let _, _, d_max = decision_of (scene ~vars:"wide" ~valsel:"indomain_max" ()) in
  check "(a) indomain_min splits at lo, low side first"
    (Var.to_int d_min.Search.d_var = 0
    && d_min.Search.d_split = 0 && not d_min.Search.d_high_first);
  check "(a) indomain_max splits at hi-1, HIGH side first"
    (Var.to_int d_max.Search.d_var = 0
    && d_max.Search.d_split = 6 && d_max.Search.d_high_first);
  check "(a) ... so the two value choices really do differ on the same variable"
    (d_min.Search.d_split <> d_max.Search.d_split
    && d_min.Search.d_high_first <> d_max.Search.d_high_first);

  (* --- (b) seq_search composes: the SECOND annotation is consulted only once the
     first has no unfixed variable left.

     The phases are given in the order [b] then [a], against declaration order [a] then
     [b], so "consult the first phase" and "take the lowest-indexed variable" give
     different answers and the assertion can tell them apart. The candidate array is the
     handle: [order] is documented to receive the UNFIXED variables, so dropping b from
     it is exactly the state "b is fixed", with no store surgery and nothing faked about
     what the order sees. *)
  let seq_src =
    "var 0..3: a;\n\
     var 0..3: b;\n\
     var 0..3: spare;\n\
     constraint int_le(a,3);\n\
     constraint int_le(b,3);\n\
     constraint int_le(spare,3);\n\
     solve :: \
     seq_search([int_search([b],input_order,indomain_min,complete),int_search([a],input_order,indomain_min,complete)]) \
     satisfy;\n"
  in
  let _, _, d1 = decision_of ~cands:[ 0; 1; 2 ] seq_src in
  check "(b) seq_search takes the FIRST phase while it still has an unfixed variable (b)"
    (Var.to_int d1.Search.d_var = 1);
  let _, _, d2 = decision_of ~cands:[ 0; 2 ] seq_src in
  check "(b) ... and only then the second phase (a)" (Var.to_int d2.Search.d_var = 0);
  (* And the fallback, which is the part of SPEC 3.4 that has to be written down: a
     variable no annotation mentions still has to be branched on, so when every phase is
     exhausted the order is [spec_order]. `spare` is in neither phase. *)
  let _, _, d3 = decision_of ~cands:[ 2 ] seq_src in
  check "(b) a variable no phase mentions falls back to SPEC 3.4's default"
    (Var.to_int d3.Search.d_var = 2 && d3.Search.d_split = 0 && not d3.Search.d_high_first)

(* --- (c) and its break. Changing the search changes the TREE and therefore the PROOF,
   so the annotation's real test is the checker.

   The models branch (2x + 2y = 5 is UNSAT by parity, which bounds propagation cannot
   see, so the refutation is the search's and not the root's), and each is run under the
   annotation it carries.

   THE BREAK. The hazard [Search.sequence] introduces is that a phase names variables by
   index and does not itself know which are still unfixed: drop the filter against the
   candidate array and the order hands back a decision on an ALREADY FIXED variable. That
   is not a worse search, it is an unsound proof -- the push is not narrowing, so the
   two child nogoods no longer resolve on one literal. [bad_order] is that mistake made
   deliberately, and the checker must refuse the result. *)
let test_search_annotated_proofs () =
  print_endline "";
  let parity_unsat vsel valsel =
    Printf.sprintf
      "var 0..3: x;\n\
       var 0..3: y;\n\
       constraint int_lin_eq([2,2],[x,y],5);\n\
       solve :: int_search([x,y],%s,%s,complete) satisfy;\n"
      vsel valsel
  in
  run_model ~title:"(c) annotated UNSAT: input_order + indomain_min"
    ~src:(parity_unsat "input_order" "indomain_min");
  run_model ~title:"(c) annotated UNSAT: input_order + indomain_max"
    ~src:(parity_unsat "input_order" "indomain_max");
  run_model ~title:"(c) annotated UNSAT: first_fail + indomain_max"
    ~src:(parity_unsat "first_fail" "indomain_max");
  run_model ~title:"(c) annotated SAT: 2x + 2y = 6 under indomain_max"
    ~src:
      "var 0..3: x;\n\
       var 0..3: y;\n\
       constraint int_lin_eq([2,2],[x,y],6);\n\
       solve :: int_search([y,x],input_order,indomain_max,complete) satisfy;\n";
  run_model ~title:"(c) annotated UNSAT under seq_search, two phases"
    ~src:
      "var 0..3: x;\n\
       var 0..3: y;\n\
       constraint int_lin_eq([2,2],[x,y],5);\n\
       solve :: \
       seq_search([int_search([y],input_order,indomain_max,complete),int_search([x],first_fail,indomain_min,complete)]) \
       satisfy;\n";
  (* The break. [bad_order] is [Search.sequence] with its liveness filter removed: it
     returns the first variable of the phase whatever its domain now is. *)
  (* --- BREAK 1: the order itself. [Search.branch] holds the decision contract -- a
     split must lie in [lo, hi) so that BOTH branches strictly narrow -- and an order
     that hands back an already-fixed variable violates it. This is where a mis-order is
     caught, and it is caught BEFORE the proof: the run raises rather than emitting a
     tree the checker would have to judge.

     That is the honest finding and it is why BREAK 2 exists as well. Search order is
     not a soundness property -- any tree that partitions is refutable, so an order that
     merely chooses BADLY produces a different proof that veripb still accepts. What
     veripb can catch is a proof line that does not follow, so BREAK 2 corrupts one. *)
  let fired = ref false in
  let bad_order (store : Store.t) (cands : Var.t array) =
    if !fired then Search.spec_order store cands
    else (
      fired := true;
      let v = Var.of_int 0 in
      let d = Store.get store v in
      { Search.d_var = v; d_split = Domain.lo d; d_high_first = false })
  in
  let colouring ann =
    Printf.sprintf
      "var 2..2: x;\n\
       var 0..1: a;\n\
       var 0..1: b;\n\
       var 0..1: c;\n\
       constraint int_le(x,2);\n\
       constraint int_ne(a,b);\n\
       constraint int_ne(b,c);\n\
       constraint int_ne(a,c);\n\
       solve :: %s satisfy;\n"
      ann
  in
  let ann_min = "int_search([a,b,c],input_order,indomain_min,complete)" in
  let ann_max = "int_search([a,b,c],input_order,indomain_max,complete)" in
  (match
     try
       run_model_with ~order:bad_order ~title:"(c) BREAK 1 (should not be reached)"
         ~src:(colouring ann_min) ();
       `No_raise
     with Invalid_argument msg -> `Raised msg
   with
  | `Raised msg ->
      check "(c) BREAK 1: a decision on an already-fixed variable is REFUSED, by name"
        (contains ~needle:"Search.branch" msg
        && contains ~needle:"outside" msg
        && contains ~needle:"strictly narrow" msg)
  | `No_raise ->
      fail "(c) BREAK 1: a decision on an already-fixed variable is REFUSED, by name"
        "the run completed; the decision contract did not fire");

  (* --- BREAK 2: the checker, over the annotated tree's OWN proof, and over a
     SATISFIABLE model -- which is the whole design of this lane.

     Measured while writing it, on the annotated UNSAT models above: with the database
     already contradictory, veripb 3.0.2 ACCEPTS a `rup` clause with a literal removed
     and ACCEPTS one with a literal's polarity flipped. That is the same vacuity D-0053
     records for `red`, here for `rup`: everything is RUP once the database is
     contradictory, so a break lane over an UNSAT model tests nothing. The model below is
     SAT, and it backtracks before it succeeds (indomain_max tries the value the
     disequalities refuse), so its proof carries real decision nogoods that the final
     `sol` has to be consistent with.

     The mutation flips the polarity of the single literal in a UNIT nogood. Removing a
     literal instead was measured and is NOT enough even here -- both weakenings this
     lane tried were still RUP-derivable. The assertion is on the checker's WORDING at
     full strength (CLAUDE.md: an exit status cannot tell a judgement from a parse
     error). *)
  let backtracking_sat ann =
    Printf.sprintf
      "var 0..2: a;\n\
       var 0..2: b;\n\
       constraint int_lin_le([1,1],[a,b],2);\n\
       constraint int_lin_le([-1,-1],[a,b],-2);\n\
       constraint int_ne(a,b);\n\
       constraint int_ne(a,2);\n\
       solve :: %s satisfy;\n"
      ann
  in
  let flip_a_unit_nogood lines =
    let flipped = ref false in
    let flip line =
      match String.split_on_char ' ' line with
      | [ id; "rup"; "+1"; lit; ">="; "1"; ";" ] when not !flipped ->
          flipped := true;
          let lit' =
            if String.length lit > 0 && lit.[0] = '~' then
              String.sub lit 1 (String.length lit - 1)
            else "~" ^ lit
          in
          String.concat " " [ id; "rup"; "+1"; lit'; ">="; "1"; ";" ]
      | _ -> line
    in
    (* Last such line, not the first: the earlier units are the ones the search has
       already resolved away, and the final one is the one the solution must respect. *)
    List.rev (List.map flip (List.rev lines))
  in
  run_model_with ~title:"(c) annotated UNSAT: graph colouring under indomain_max"
    ~src:(colouring ann_max) ();
  let ann_ab_max = "int_search([a,b],input_order,indomain_max,complete)" in
  run_model_with ~title:"(c) annotated SAT that backtracks first, under indomain_max"
    ~src:(backtracking_sat ann_ab_max) ();
  run_model_with ~expect_reject:true ~mutate:flip_a_unit_nogood
    ~title:"(c) BREAK 2: a unit nogood of the annotated tree, flipped, is REFUSED"
    ~src:(backtracking_sat ann_ab_max) ()

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
  test_reified ();
  test_end_to_end ();
  test_element_shape ();
  test_element_oracle ();
  test_element_view ();
  test_element_defining_level_rule ();
  test_search_annotations ();
  test_search_annotated_proofs ();
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "\ncompile tests passed"
