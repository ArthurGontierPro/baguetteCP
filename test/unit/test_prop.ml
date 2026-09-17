(* Unit tests for propagators (lib/core/prop/).

   M1-T7a: the int_lin_le reference propagator (lib/core/prop/linear.ml) and the shared
   chain helper it uses (lib/core/prop/order_reason.ml, docs/DECISIONS.md D-0010).
   Follows test_core.ml's shape: a [check] counter, one function per area, exit 1 on any
   failure. See docs/INVARIANTS.md for I-P1..I-P4, which the sections below are named
   after.

   M1-T8 adds int_lin_eq, int_le, int_lt, int_eq (lib/core/prop/lin_eq.ml,
   lib/core/prop/int_le.ml, int_lt.ml, int_eq.ml). All four delegate their actual
   propagation to [Linear]/[Lin_eq], so their explanations are, unmodified, exactly
   [Linear]'s [Cut (Trivial, Linear (units, units_rhs), 1, 1)] shape -- the sections
   below re-run [Linear]'s own I-P1..I-P4 style checks against them (soundness,
   checking, idempotence, the max-attainable guard) and, per this task, add one
   end-to-end veripb check per propagator with a multi-step bound-fact chain, the case
   D-0010 shows is the one a green suite can otherwise miss entirely. *)

module Domain = Baguette_core.Domain
module Store = Baguette_core.Store
module Var = Baguette_core.Var
module Explanation = Baguette_core.Explanation
module Reason = Baguette_core.Reason
module Propagator = Baguette_core.Propagator
module Linear = Baguette_core.Linear
module Lin_eq = Baguette_core.Lin_eq
module Int_le = Baguette_core.Int_le
module Int_lt = Baguette_core.Int_lt
module Int_eq = Baguette_core.Int_eq
module Order_reason = Baguette_core.Order_reason
module Lit = Baguette_proof.Lit
module Opb = Baguette_proof.Opb
module Writer = Baguette_proof.Writer
module Encoding = Baguette_proof.Encoding
module Justify = Baguette_core.Justify
module Ne = Baguette_core.Ne
module Trace = Baguette_core.Trace
module Engine = Baguette_core.Engine
module Search = Baguette_core.Search
module Checked = Baguette_core.Checked
module Bool_clause = Baguette_core.Bool_clause
module Bool2int = Baguette_core.Bool2int
module Flatzinc = Baguette_flatzinc
module Compile = Baguette_flatzinc.Compile

(* M1-T53: the inner heap guard. test_prop.exe is the binary that reached 14.9 GB RSS on
   2026-09-16 and had to be killed by hand, so a guard that covered only test_output and
   test_compile would have missed the one incident it exists to prevent. `ulimit -v` stays
   the outer backstop -- see mem_guard.ml's header for what this cannot see. *)
let () = Mem_guard.install ()
let failures = ref 0

(* Stands in for "some earlier derivation already established this", which is what
   [Explanation.trivial] meant at the setup pushes throughout this file until M1-T31
   deleted it. [Model_row] is the honest spelling of that -- a bound that came from a
   row -- and it keeps these setups on [linear.ml]'s citing path, which is what the
   shape tests below are about. The four [decision_scene_*] builders deliberately do
   NOT use it: what they simulate is a search decision, and that is now a different
   constructor with a different rendering (M1-T50). The id is out of range of every
   encoding in this file on purpose: nothing renders this citation, and if something
   ever did, veripb would reject the id rather than quietly accept a plausible one. *)
let placeholder_reason = Explanation.model_row 901

(* The same placeholder as ONE [Reason.justified], which is the shape every store mutator
   takes since M2-T8 (D-0026): the justification above plus [Reason.none]. The reason is
   empty because these setups are about [linear.ml]'s *citing* path and not about the
   trace line; a test that wants facts on the entry builds its own reason (see
   [test_trace_facts] and the D-0026 tests at the end of this file). It has to be written
   out, which is the point of the collapse -- before M2-T8 [Store.set_lo] meant
   "no facts" silently and [set_lo_with_facts] was the opt-in. *)
let placeholder_pruning = Reason.because Reason.none placeholder_reason

let check name cond =
  if cond then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s\n" name)

(* ------------------------------------------------------------------- helpers *)

let mk_store bounds =
  (* [bounds] : (name, lo, hi) list, one per variable, in Var.of_int order. These are
     the *declared* domains: nothing here ever mutates them behind a propagator's back
     except a test that deliberately wants to simulate an earlier propagator having
     already narrowed a variable (D-0010: declared vs. current). *)
  let names = Array.of_list (List.map (fun (n, _, _) -> n) bounds) in
  let domains = Array.of_list (List.map (fun (_, lo, hi) -> Domain.make lo hi) bounds) in
  Store.create ~names ~domains

let var i = Var.of_int i

(* Cartesian product of a list of (lo, hi) ranges, as int lists in the same order. *)
let rec cartesian ranges =
  match ranges with
  | [] -> [ [] ]
  | (lo, hi) :: rest ->
      let tails = cartesian rest in
      List.concat_map
        (fun v -> List.map (fun t -> v :: t) tails)
        (List.init (hi - lo + 1) (fun k -> lo + k))

let satisfies coeffs rhs assignment =
  List.fold_left2 (fun acc a v -> acc + (a * v)) 0 coeffs assignment <= rhs

(* Decode the value an order-encoding literal names, undoing the [le] encoding's +1
   shift (lib/proof/lit.ml: [le x v = neg (Ge (x, v + 1))]). *)
let decode_bound (l : Lit.t) =
  match l.Lit.v with
  | Lit.Ge (_, v) -> if l.Lit.positive then v else v - 1
  | Lit.Eq (_, v) -> v

(* The largest value a Linear row's term list can attain: each literal is 0/1, so a
   term with coefficient [a] contributes at most [max a 0]. A row whose own terms can
   never reach its stated [rhs] is unsatisfiable and no proof state accepts it -
   docs/DECISIONS.md D-0010 was exactly a row that failed this. *)
let max_attainable lterms = List.fold_left (fun acc (a, _) -> acc + max a 0) 0 lterms

(* ----------------------------------------------------- D-0013 Combine shape checks *)

(* D-0013: verify one summand of a [Combine] against the term it stands for --
   [bounds]/[terms] are the index-aligned (name, decl_lo, decl_hi) / (coeff, var)
   lists the test built the propagator from, [idx] the term's position. Declared
   (current bound == declared bound) must render as [Weaken], derived (tighter than
   declared) must render as [Term] citing something -- never the other way around,
   which is exactly the D-0009 distinction D-0013 makes structural. A [Weaken]
   chain's own literals are checked against [Order_reason.weaken_declared]'s output
   verbatim (not just its length), and against I-D0010's max-attainable guard: the
   chain's own literals, all at 1, must reach at least its own contribution -- true
   by construction here, but asserted directly rather than assumed, per this task's
   own instruction that every explanation's row gets this check. *)
(* [~strict] holds when the caller's [coeff] is known to be exactly what the
   *producing* instance itself used internally (true for [Linear] driven directly --
   [test_conflict], [check_entailment_case], [test_multi_step_chain]). [Lin_eq]'s
   [ge] half negates every coefficient before handing it to [Linear.make] (see
   lib/core/prop/lin_eq.ml), so a generic checker fed the *un*negated [terms] cannot
   know, from the sign of [coeff] alone, which of [x]'s two bounds the *actual*
   producing half cared about -- only its magnitude survives negation. Non-strict
   mode checks exactly that: the summand's own coefficient magnitude, and, for a
   [Weaken], that its literals are [Order_reason.weaken_declared]'s output at
   *either* polarity (the actual polarity is determined by the sign the producing
   half really used, invisible here) -- still catching a wrong chain, wrong
   magnitude, or wrong-shaped summand, just not "should this have cited instead". *)
let verify_one_summand ?(strict = true) test_name store bounds idx coeff summand =
  let ok = ref true in
  let expect cond msg =
    if not cond then ok := false;
    check (Printf.sprintf "%s: %s" test_name msg) cond
  in
  let name, decl_lo, decl_hi = List.nth bounds idx in
  let mag = abs coeff in
  let pos_lits, pos_c = Order_reason.weaken_declared ~coeff:mag ~name ~decl_lo ~decl_hi in
  let neg_lits, neg_c =
    Order_reason.weaken_declared ~coeff:(-mag) ~name ~decl_lo ~decl_hi
  in
  let check_weaken lits =
    expect
      (lits = pos_lits || lits = neg_lits)
      (Printf.sprintf
         "%s: weaken chain matches Order_reason.weaken_declared (coeff magnitude %d)" name
         mag);
    let contribution = if lits = pos_lits then pos_c else neg_c in
    expect
      (max_attainable lits >= contribution)
      (Printf.sprintf "%s: weaken chain can attain its own contribution" name)
  in
  (if not strict then
     match summand with
     | Explanation.Weaken lits -> check_weaken lits
     | Explanation.Term (c, _cited) ->
         expect (c = mag)
           (Printf.sprintf "%s: cited derived bound is scaled by abs(coeff) = %d" name mag)
   else
     let d = Store.get store (var idx) in
     let still_declared =
       if coeff >= 0 then Domain.lo d <= decl_lo else Domain.hi d >= decl_hi
     in
     match (summand, still_declared) with
     | Explanation.Weaken lits, true -> check_weaken lits
     | Explanation.Term (c, _cited), false ->
         expect (c = mag)
           (Printf.sprintf "%s: cited derived bound is scaled by abs(coeff) = %d" name mag)
     | Explanation.Weaken _, false ->
         expect false
           (Printf.sprintf
              "%s: bound is derived (tighter than declared) but the summand weakens \
               instead of citing"
              name)
     | Explanation.Term _, true ->
         expect false
           (Printf.sprintf
              "%s: bound is still declared but the summand cites instead of weakening"
              name));
  !ok

(* Verify a whole [Combine (summands, divisor)] against the row it came from:
   [excluded] is [Some idx], the pushed variable (excluded from the sum, divisor is
   [abs] its coefficient), or [None] for a row-level conflict (every term
   participates, divisor 1). Checks the base summand is [Term (1, Model_row _)] --
   never bare [Trivial], see explanation.ml's header on why -- and that every other
   nonzero term gets exactly one summand, verified by [verify_one_summand], in the
   same order as [terms]. *)
let verify_combine ?(strict = true) test_name store bounds terms expl ~excluded =
  let ok = ref true in
  let expect cond msg =
    if not cond then ok := false;
    check (Printf.sprintf "%s: %s" test_name msg) cond
  in
  match expl with
  | Explanation.Combine (base :: rest, divisor) ->
      let expected_divisor =
        match excluded with None -> 1 | Some idx -> abs (fst (List.nth terms idx))
      in
      expect (divisor = expected_divisor) "divisor is abs(pushed coefficient), or 1";
      (match base with
      | Explanation.Term (1, Explanation.Model_row _) -> ()
      | _ -> expect false "first summand is Term (1, Model_row _), not Trivial");
      let expected_others =
        List.mapi (fun i t -> (i, t)) terms
        |> List.filter (fun (i, (a, _)) -> a <> 0 && Some i <> excluded)
      in
      if List.length rest <> List.length expected_others then
        expect false "one summand per nonzero, non-pushed term"
      else
        List.iter2
          (fun (idx, (coeff, _x)) summand ->
            if not (verify_one_summand ~strict test_name store bounds idx coeff summand)
            then ok := false)
          expected_others rest;
      !ok
  | _ ->
      expect false "top-level shape is Combine (_ :: _, _)";
      false

(* The bound a D-0013 derivation pushes, recomputed independently from the store
   rather than from the [Explanation.t] itself (I-P1's own discipline: check the
   *effect*, not the mechanism that produced it) -- the sum, over every *other*
   nonzero term, of its current minimum contribution ([term_min]'s own formula),
   subtracted from [rhs]. Matches [Linear.propagate]'s [max_term] exactly. *)
let others_min store terms ~excluded =
  List.mapi (fun i t -> (i, t)) terms
  |> List.filter (fun (i, (a, _)) -> a <> 0 && Some i <> excluded)
  |> List.fold_left
       (fun acc (idx, (a, _x)) ->
         let d = Store.get store (var idx) in
         acc + if a >= 0 then a * Domain.lo d else a * Domain.hi d)
       0

(* ---------------------------------------------------------- I-P1: soundness *)

(* Brute force: enumerate every assignment within the *original* box, compute which
   values of each variable have support (extend to a full solution of the constraint
   over that same box), run the propagator once, and check every value it kept a bound
   for is consistent with - and every value it excluded had no - support. Bounds-only
   propagation can only report a value absent by moving lo/hi past it, so "excluded" is
   simply "outside the propagated [lo, hi]". *)
let check_soundness_case name coeffs rhs ranges =
  let n = List.length coeffs in
  let bounds = List.mapi (fun i (lo, hi) -> (Printf.sprintf "x%d" i, lo, hi)) ranges in
  let assignments = cartesian ranges in
  let solutions = List.filter (satisfies coeffs rhs) assignments in
  let has_support i v = List.exists (fun sol -> List.nth sol i = v) solutions in
  let store = mk_store bounds in
  let raw_terms = List.mapi (fun i a -> (a, var i)) coeffs in
  let prop = Linear.make store raw_terms rhs ~row_id:1 in
  let result = Linear.propagate prop store in
  match result with
  | Propagator.Conflict _ ->
      (* Sound iff there really is no solution at all in the original box. *)
      check (Printf.sprintf "%s: conflict only when truly unsat" name) (solutions = [])
  | Propagator.Fixpoint ->
      let ok = ref true in
      for i = 0 to n - 1 do
        let lo, hi = List.nth ranges i in
        let d = Store.get store (var i) in
        for v = lo to hi do
          let supported = has_support i v in
          let kept = Domain.mem d v in
          (* I-P1: never remove a supported value. It is fine (bounds consistency,
             not domain consistency) to keep an unsupported one. *)
          if supported && not kept then ok := false
        done
      done;
      check (Printf.sprintf "%s: I-P1 no supported value removed" name) !ok

let test_soundness () =
  check_soundness_case "2 vars, positive coeffs" [ 1; 1 ] 2 [ (-3, 3); (-3, 3) ];
  check_soundness_case "2 vars, one negative coeff" [ 1; -1 ] 0 [ (-3, 3); (-3, 3) ];
  check_soundness_case "3 vars, mixed signs" [ 2; -1; 3 ] 4 [ (-3, 3); (-3, 3); (-3, 3) ];
  check_soundness_case "3 vars, one zero coeff" [ 1; 0; -2 ] 1
    [ (-2, 2); (-2, 2); (-2, 2) ];
  check_soundness_case "2 vars, all-negative coeffs" [ -2; -3 ] (-5) [ (-3, 3); (-3, 3) ];
  check_soundness_case "tight, likely conflict" [ 1; 1; 1 ] (-8)
    [ (-3, 3); (-3, 3); (-3, 3) ]

(* -------------------------------------------------------- bounds consistency *)

(* After [propagate] returns [Fixpoint], each variable's lo and hi must have support in
   the relaxation: an assignment of the *other* variables within their (already
   tightened) domains that, together with this bound, satisfies the constraint. *)
let test_bounds_consistency () =
  let coeffs = [ 2; -1; 3 ] and rhs = 4 in
  let ranges = [ (-3, 3); (-3, 3); (-3, 3) ] in
  let bounds = List.mapi (fun i (lo, hi) -> (Printf.sprintf "x%d" i, lo, hi)) ranges in
  let store = mk_store bounds in
  let raw_terms = List.mapi (fun i a -> (a, var i)) coeffs in
  let prop = Linear.make store raw_terms rhs ~row_id:1 in
  match Linear.propagate prop store with
  | Propagator.Conflict _ -> check "bounds consistency: expected Fixpoint" false
  | Propagator.Fixpoint ->
      let n = List.length coeffs in
      let current_ranges =
        List.init n (fun i ->
            let d = Store.get store (var i) in
            (Domain.lo d, Domain.hi d))
      in
      let has_support_for i target =
        (* fix i to [target], let the others range over their current domain *)
        let other_ranges = List.filteri (fun j _ -> j <> i) current_ranges in
        let others = cartesian other_ranges in
        List.exists
          (fun other ->
            let full = ref [] and k = ref 0 in
            for j = n - 1 downto 0 do
              if j = i then full := target :: !full
              else (
                full := List.nth other !k :: !full;
                incr k)
            done;
            satisfies coeffs rhs !full)
          others
      in
      let ok = ref true in
      for i = 0 to n - 1 do
        let lo, hi = List.nth current_ranges i in
        if not (has_support_for i lo) then ok := false;
        if not (has_support_for i hi) then ok := false
      done;
      check "bounds consistency: lo/hi of every var has support" !ok

(* -------------------------------------------------------------- I-P2/I-P3 *)

let test_idempotence () =
  let coeffs = [ 2; -1; 3 ] and rhs = 4 in
  let ranges = [ (-3, 3); (-3, 3); (-3, 3) ] in
  let bounds = List.mapi (fun i (lo, hi) -> (Printf.sprintf "x%d" i, lo, hi)) ranges in
  let store = mk_store bounds in
  let raw_terms = List.mapi (fun i a -> (a, var i)) coeffs in
  let prop = Linear.make store raw_terms rhs ~row_id:1 in
  (match Linear.propagate prop store with
  | Propagator.Conflict _ -> check "idempotence: expected Fixpoint first pass" false
  | Propagator.Fixpoint -> check "idempotence: first pass is a fixpoint result" true);
  let snap = Store.snapshot store in
  (match Linear.propagate prop store with
  | Propagator.Conflict _ -> check "I-P2: second propagate must not conflict" false
  | Propagator.Fixpoint -> check "I-P2: second propagate reports Fixpoint" true);
  check "I-P2/I-P3: second propagate changed nothing" (Store.same_domains store snap)

(* -------------------------------------------------------------------- conflict *)

let test_conflict () =
  (* 2x + 3y <= 1, x and y declared [0,3] but already known (some earlier propagator)
     to be >= 1 each: min is 2+3=5 > 1. Declared bounds differ from current on
     purpose (D-0013's own case: both bounds here are derived, not declared, so the
     conflict cites rather than weakens both terms) -- at the declared bounds
     themselves the model row alone is already infeasible and needs no extra
     citation, which would make this a degenerate test of I-P1/I-P3 conflict
     reporting but not of the Combine shape. *)
  let bounds = [ ("x", 0, 3); ("y", 0, 3) ] in
  let store = mk_store bounds in
  let raw_terms = [ (2, var 0); (3, var 1) ] in
  let prop = Linear.make store raw_terms 1 ~row_id:1 in
  ignore (Store.set_lo store (var 0) 1 placeholder_pruning);
  ignore (Store.set_lo store (var 1) 1 placeholder_pruning);
  match Linear.propagate prop store with
  | Propagator.Fixpoint -> check "conflict: expected Conflict" false
  | Propagator.Conflict c ->
      let e = c.Store.c_why in
      (* [Explanation.lits] walks into [Combine]'s [Weaken] summands but not into a
         [Term]'s cited explanation until *that* is forced -- and here both x and y
         are cited via [placeholder_reason] (standing in for "some earlier propagator
         already established this"), which carries no literals of its own
         (lib/core/explanation.ml: a [Model_row] is the row itself, an indivisible
         reference, not a set of literals to enumerate). An empty result
         is therefore the *correct* answer for this specific setup, not a smell --
         asserted directly since D-0013 changed what a legitimate answer looks like
         here (it used to always be nonempty, back when every "other var" reason was
         a literal chain regardless of whether it was declared or derived). *)
      check "conflict: reported" true;
      check "conflict: lits does not raise"
        (ignore (Explanation.lits e);
         true);
      let e' = Explanation.force e in
      if verify_combine "conflict" store bounds raw_terms e' ~excluded:None then
        let max_term = 1 - others_min store raw_terms ~excluded:None in
        check "conflict: numeric contradiction (rhs - min contribution < 0)" (max_term < 0)

(* ---------------------------------------------------------- explanation entailment *)

(* Runs the propagator once, then inspects every trail entry it created: force the
   explanation and check, by direct arithmetic over the term list (not string
   comparison), that it really does entail the bound that got pushed - including that
   the row can attain its own rhs at all (docs/DECISIONS.md D-0010) and that every
   chain is the exact declared-bound-relative sequence. *)
let check_entailment_case name coeffs rhs bounds =
  let store = mk_store bounds in
  let raw_terms = List.mapi (fun i a -> (a, var i)) coeffs in
  let prop = Linear.make store raw_terms rhs ~row_id:1 in
  let before = Store.trail_length store in
  match Linear.propagate prop store with
  | Propagator.Conflict _ -> check (Printf.sprintf "%s: expected Fixpoint" name) false
  | Propagator.Fixpoint ->
      let after = Store.trail_length store in
      check (Printf.sprintf "%s: at least one pruning happened" name) (after > before);
      let entries = Store.trail_entries store in
      (* [trail_entries] returns *newest first* (see store.ml): the entries this call
         added are exactly the first [after - before] of them. *)
      let new_entries = List.filteri (fun i _ -> i < after - before) entries in
      List.iter
        (fun (e : Store.entry) ->
          let pushed_idx =
            match
              List.find_opt
                (fun i -> Var.equal (var i) e.var)
                (List.mapi (fun i _ -> i) bounds)
            with
            | Some i -> i
            | None -> failwith "entailment test: pushed var not found by index"
          in
          let a, _ = List.nth raw_terms pushed_idx in
          let expl = Explanation.force (Store.explanation store e) in
          let shape_ok =
            verify_combine name store bounds raw_terms expl ~excluded:(Some pushed_idx)
          in
          if shape_ok then
            let max_term = rhs - others_min store raw_terms ~excluded:(Some pushed_idx) in
            let d_now = Store.get store e.var in
            if a > 0 then
              check
                (Printf.sprintf "%s: pushed hi matches floor division" name)
                (Domain.hi d_now = Linear.floordiv max_term a)
            else if a < 0 then
              check
                (Printf.sprintf "%s: pushed lo matches ceil division" name)
                (Domain.lo d_now = Linear.ceildiv max_term a)
            else check (Printf.sprintf "%s: zero coefficient never pushes" name) false)
        new_entries

let test_explanation_entailment () =
  check_entailment_case "positive coeffs push hi" [ 1; 1 ] (-2)
    [ ("x", -3, 3); ("y", -3, 3) ];
  check_entailment_case "negative coeff pushes lo" [ -1; 1 ] (-5)
    [ ("x", -3, 3); ("y", -3, 3) ];
  check_entailment_case "mixed signs, three vars" [ 2; -1; 3 ] (-2)
    [ ("x", -3, 3); ("y", -3, 3); ("z", -3, 3) ]

(* ------------------------------------------ multi-step chains (D-0010 regression) *)

(* Direct check of the shared helper: a bound several steps away from the declared one
   must produce the full contiguous chain, not a single literal, and the raw value
   must never leak into the coefficient. *)
let test_order_reason () =
  let terms, rhs = Order_reason.lower_bound_terms ~coeff:2 ~name:"x" ~decl_lo:0 3 in
  check "Order_reason: lower chain length" (List.length terms = 3);
  check "Order_reason: lower chain values"
    (List.map (fun (_, l) -> decode_bound l) terms = [ 1; 2; 3 ]);
  check "Order_reason: lower chain coefficients"
    (List.for_all (fun (a, _) -> a = 2) terms);
  check "Order_reason: lower chain rhs is coeff * count, not coeff * bound" (rhs = 6);
  check "Order_reason: lower chain literals are Lit.ge"
    (List.for_all (fun (_, l) -> l.Lit.positive) terms);

  let terms2, rhs2 = Order_reason.upper_bound_terms ~coeff:3 ~name:"y" ~decl_hi:5 2 in
  check "Order_reason: upper chain length" (List.length terms2 = 3);
  check "Order_reason: upper chain values"
    (List.map (fun (_, l) -> decode_bound l) terms2 = [ 2; 3; 4 ]);
  check "Order_reason: upper chain rhs is coeff * count" (rhs2 = 9);
  check "Order_reason: upper chain literals are negated (Lit.le)"
    (List.for_all (fun (_, l) -> not l.Lit.positive) terms2);

  check "Order_reason: lower chain at the declared bound is empty"
    (Order_reason.lower_bound_terms ~coeff:1 ~name:"x" ~decl_lo:0 0 = ([], 0));
  check "Order_reason: upper chain at the declared bound is empty"
    (Order_reason.upper_bound_terms ~coeff:1 ~name:"x" ~decl_hi:5 5 = ([], 0))

(* D-0013's two term shapes, each with a coefficient other than 1 (docs/DECISIONS.md
   D-0013: "unit-coefficient tests prove nothing about [division]"; the task behind
   this module makes the same point about the chain literals) and, for the citing
   case, a bound more than one step from declared:

   1. "Cite": x's bound was already tightened by an earlier step (simulated here by
      pushing it with [placeholder_reason] before running this propagator, standing
      in for whatever real derivation established it -- this test only cares that
      *something* is cited, not what). The summand for x must be [Term], scaled by
      [abs coeff], never a [Weaken] chain, however many steps away from declared it
      is.
   2. "Weaken": x is left at its declared bound entirely untouched. The summand must
      be [Weaken], and -- this is the D-0013 shape a unit coefficient cannot
      exercise -- its chain spans x's *whole* declared width (not a prefix relative
      to any current value, there being no "current" to be relative to) at
      coefficient [abs coeff] per literal, polarity determined by the *sign* of
      coeff (see [Order_reason.weaken_declared]'s header). *)
let test_multi_step_chain () =
  let run_case name ~coeffs ~rhs ~bounds ~x_setup =
    let store = mk_store bounds in
    let raw_terms = List.mapi (fun i a -> (a, var i)) coeffs in
    let prop = Linear.make store raw_terms rhs ~row_id:1 in
    (match x_setup store with
    | None -> ()
    | Some (set, bound) -> (
        match set store (var 0) bound placeholder_pruning with
        | Store.Changed -> ()
        | _ -> check (Printf.sprintf "%s: setup prune applied" name) false));
    let before = Store.trail_length store in
    match Linear.propagate prop store with
    | Propagator.Conflict _ -> check (Printf.sprintf "%s: expected Fixpoint" name) false
    | Propagator.Fixpoint -> (
        let after = Store.trail_length store in
        let entries =
          List.filteri (fun i _ -> i < after - before) (Store.trail_entries store)
        in
        match
          List.find_opt (fun (e : Store.entry) -> Var.equal e.var (var 1)) entries
        with
        | None -> check (Printf.sprintf "%s: y was pushed" name) false
        | Some e ->
            let expl = Explanation.force (Store.explanation store e) in
            (* The Weaken cases carry real literals ([Explanation.lits] must reach
               them); the cite cases legitimately may not (see test_conflict's own
               note on [Trivial]). *)
            if x_setup store = None then
              check
                (Printf.sprintf "%s: lits reaches into the weaken chain" name)
                (Explanation.lits expl <> []);
            if verify_combine name store bounds raw_terms expl ~excluded:(Some 1) then
              let max_term = rhs - others_min store raw_terms ~excluded:(Some 1) in
              let d_now = Store.get store e.var in
              let b, _ = List.nth raw_terms 1 in
              if b > 0 then
                check
                  (Printf.sprintf "%s: y's pushed hi matches floor division" name)
                  (Domain.hi d_now = Linear.floordiv max_term b)
              else
                check
                  (Printf.sprintf "%s: y's pushed lo matches ceil division" name)
                  (Domain.lo d_now = Linear.ceildiv max_term b))
  in
  (* Cite, positive coefficient (2), bound seven steps above declared lo. *)
  run_case "multi-step cite (coeff 2, lower)" ~coeffs:[ 2; 1 ] ~rhs:6
    ~bounds:[ ("x", -5, 5); ("y", -5, 5) ]
    ~x_setup:(fun _ -> Some (Store.set_lo, 2));
  (* Cite, negative coefficient (-3), bound eight steps below declared hi. *)
  run_case "multi-step cite (coeff -3, upper)" ~coeffs:[ -3; 1 ] ~rhs:9
    ~bounds:[ ("x", -5, 5); ("y", -5, 5) ]
    ~x_setup:(fun _ -> Some (Store.set_hi, -3));
  (* Weaken, positive coefficient (3): x is left fully declared ([-5,5], 10 literals);
     the D-0013 shape a coefficient of 1 cannot exercise (D-0010's own regression was
     invisible at coefficient 1 for exactly this reason). *)
  run_case "multi-step weaken (coeff 3, lower)" ~coeffs:[ 3; 1 ] ~rhs:(-15)
    ~bounds:[ ("x", -5, 5); ("y", -5, 5) ]
    ~x_setup:(fun _ -> None);
  (* Weaken, negative coefficient (-2), x fully declared. *)
  run_case "multi-step weaken (coeff -2, upper)" ~coeffs:[ -2; 1 ] ~rhs:(-10)
    ~bounds:[ ("x", -5, 5); ("y", -5, 5) ]
    ~x_setup:(fun _ -> None)

(* ============================================================================
   M1-T8: int_lin_eq, int_le, int_lt, int_eq.

   All four delegate propagation wholesale to [Linear] (int_le, int_lt: directly;
   int_lin_eq, int_eq: via [Lin_eq], two [Linear] instances run to a shared
   fixpoint) -- see the module headers in lib/core/prop/{lin_eq,int_le,int_lt,int_eq}.ml
   for why. So every explanation any of them ever produces is, unmodified, [Linear]'s
   own [Cut (Trivial, Linear (units, units_rhs), 1, 1)] shape, and [verify_linear_shape]
   above already checks that shape against a set of (name, decl_lo, decl_hi) bounds and
   (coeff, var) terms regardless of which direction (le or ge) produced it: the
   coefficient check there only ever compares magnitudes ([abs orig_coeff]), and the
   chain-direction check reads the sign straight off the produced literal, not off the
   caller's [terms] list. So the original (unnegated) terms/bounds can always be handed
   to it, whichever of [Lin_eq]'s two [Linear] children actually pushed the bound. That
   is what makes reusing it here safe rather than a coincidence worth re-deriving. *)

(* D-0011: [Lin_eq.make]/[Int_eq.make] are no longer propagators -- they return a pair
   of ordinary [Linear.t] instances ([le], [ge]) for a caller (the engine) to post
   separately, each against its own model row. There is no library-level "run both to
   a shared fixpoint" any more: that alternation is the engine's job now (see
   lib/core/prop/lin_eq.ml's header for why). The soundness/checking/idempotence tests
   below still need to know what the *pair*, run to fixpoint, computes -- so this test
   file supplies that alternation itself, exactly the way a future engine will, but
   only as test-local glue for driving the black-box checks below. It is deliberately
   NOT reused by the veripb tests further down: those instead run [le]/[ge] as two
   separately-justified instances, which is the property D-0011 exists to protect. *)
let propagate_pair (le, ge) store =
  let rec loop () =
    let snap = Store.snapshot store in
    match Linear.propagate le store with
    | Propagator.Conflict _ as c -> c
    | Propagator.Fixpoint -> (
        match Linear.propagate ge store with
        | Propagator.Conflict _ as c -> c
        | Propagator.Fixpoint ->
            if Store.same_domains store snap then Propagator.Fixpoint else loop ())
  in
  loop ()

(* Generic soundness harness, parameterised over [propagate]/[vars]-shaped functions and
   a [satisfies] predicate, so int_lin_eq / int_le / int_lt / int_eq do not each need a
   hand-copied version of [check_soundness_case] above. Only ever asserts I-P1 (never
   remove a supported value) -- exactly right for int_eq, which is bounds- not
   domain-consistent (see lib/core/prop/int_eq.ml's header): a brute-force check phrased
   as "no supported value removed" is silent about values int_eq is allowed to leave
   behind, which is the honest thing for this consistency level to check. *)
let check_generic_soundness name ~make ~propagate ~n ~ranges ~satisfies =
  let bounds = List.mapi (fun i (lo, hi) -> (Printf.sprintf "x%d" i, lo, hi)) ranges in
  let assignments = cartesian ranges in
  let solutions = List.filter satisfies assignments in
  let has_support i v = List.exists (fun sol -> List.nth sol i = v) solutions in
  let store = mk_store bounds in
  let prop = make store in
  match propagate prop store with
  | Propagator.Conflict _ ->
      check (Printf.sprintf "%s: conflict only when truly unsat" name) (solutions = [])
  | Propagator.Fixpoint ->
      let ok = ref true in
      for i = 0 to n - 1 do
        let lo, hi = List.nth ranges i in
        let d = Store.get store (var i) in
        for v = lo to hi do
          if has_support i v && not (Domain.mem d v) then ok := false
        done
      done;
      check (Printf.sprintf "%s: I-P1 no supported value removed" name) !ok

let test_lin_eq_soundness () =
  let case name coeffs rhs ranges =
    check_generic_soundness name
      ~make:(fun store ->
        Lin_eq.make store (List.mapi (fun i a -> (a, var i)) coeffs) rhs ~le_id:1 ~ge_id:2)
      ~propagate:propagate_pair ~n:(List.length coeffs) ~ranges
      ~satisfies:(fun a ->
        List.fold_left2 (fun acc c v -> acc + (c * v)) 0 coeffs a = rhs)
  in
  case "int_lin_eq: 2 vars, positive coeffs" [ 1; 1 ] 2 [ (-3, 3); (-3, 3) ];
  case "int_lin_eq: 2 vars, one negative coeff" [ 1; -1 ] 0 [ (-3, 3); (-3, 3) ];
  case "int_lin_eq: 3 vars, mixed signs" [ 2; -1; 3 ] 4 [ (-3, 3); (-3, 3); (-3, 3) ];
  case "int_lin_eq: 3 vars, one zero coeff" [ 1; 0; -2 ] 1 [ (-2, 2); (-2, 2); (-2, 2) ];
  case "int_lin_eq: all-negative coeffs" [ -2; -3 ] (-5) [ (-3, 3); (-3, 3) ];
  case "int_lin_eq: unsatisfiable target" [ 1; 1; 1 ] (-20) [ (-3, 3); (-3, 3); (-3, 3) ]

let test_compare_soundness () =
  let case name make propagate rel ranges =
    check_generic_soundness name ~make ~propagate ~n:2 ~ranges ~satisfies:(fun a ->
        match a with [ x; y ] -> rel x y | _ -> false)
  in
  case "int_le: overlapping ranges"
    (fun store -> Int_le.make store (var 0) (var 1) ~row_id:1)
    Int_le.propagate ( <= )
    [ (-3, 3); (-3, 3) ];
  case "int_le: disjoint, x strictly above y's range"
    (fun store -> Int_le.make store (var 0) (var 1) ~row_id:1)
    Int_le.propagate ( <= )
    [ (2, 5); (-5, -2) ];
  case "int_lt: overlapping ranges"
    (fun store -> Int_lt.make store (var 0) (var 1) ~row_id:1)
    Int_lt.propagate ( < )
    [ (-3, 3); (-3, 3) ];
  case "int_lt: touching ranges (x may equal y's lo, still < possible)"
    (fun store -> Int_lt.make store (var 0) (var 1) ~row_id:1)
    Int_lt.propagate ( < )
    [ (0, 3); (0, 3) ]

let test_int_eq_soundness () =
  let case name ranges =
    check_generic_soundness name
      ~make:(fun store -> Int_eq.make store (var 0) (var 1) ~le_id:1 ~ge_id:2)
      ~propagate:propagate_pair ~n:2 ~ranges
      ~satisfies:(fun a -> match a with [ x; y ] -> x = y | _ -> false)
  in
  case "int_eq: overlapping ranges" [ (-3, 3); (-1, 5) ];
  case "int_eq: disjoint ranges (unsat)" [ (0, 2); (5, 8) ];
  case "int_eq: nested ranges" [ (-5, 5); (-2, 2) ]

(* ------------------------------------------------- I-P3: checking, all fixed *)

(* With every variable fixed to a single value, a propagator must report Conflict iff
   the assignment violates its constraint -- and nothing else, since there is nothing
   left to prune. [make] runs before [Store.fix] so the propagator's frozen declared
   bounds are the wide ones, exactly as test_conflict above does with [Store.set_lo]. *)
let test_checking () =
  let run_eq bounds coeffs rhs fix_values expect_conflict label =
    let store = mk_store bounds in
    let prop =
      Lin_eq.make store (List.mapi (fun i a -> (a, var i)) coeffs) rhs ~le_id:1 ~ge_id:2
    in
    List.iteri
      (fun i v -> ignore (Store.fix store (var i) v placeholder_pruning))
      fix_values;
    match propagate_pair prop store with
    | Propagator.Conflict _ -> check label expect_conflict
    | Propagator.Fixpoint -> check label (not expect_conflict)
  in
  run_eq
    [ ("x", 0, 3); ("y", 0, 3) ]
    [ 1; 1 ] 3 [ 1; 2 ] false
    "I-P3 int_lin_eq: satisfying fixed assignment is not a conflict";
  run_eq
    [ ("x", 0, 3); ("y", 0, 3) ]
    [ 1; 1 ] 3 [ 1; 3 ] true "I-P3 int_lin_eq: violating fixed assignment is a conflict";
  let run_le make propagate bounds fix_values expect_conflict label =
    let store = mk_store bounds in
    let prop = make store in
    List.iteri
      (fun i v -> ignore (Store.fix store (var i) v placeholder_pruning))
      fix_values;
    match propagate prop store with
    | Propagator.Conflict _ -> check label expect_conflict
    | Propagator.Fixpoint -> check label (not expect_conflict)
  in
  run_le
    (fun store -> Int_le.make store (var 0) (var 1) ~row_id:1)
    Int_le.propagate
    [ ("x", 0, 5); ("y", 0, 5) ]
    [ 2; 2 ] false "I-P3 int_le: x=2,y=2 (x<=y holds) is not a conflict";
  run_le
    (fun store -> Int_le.make store (var 0) (var 1) ~row_id:1)
    Int_le.propagate
    [ ("x", 0, 5); ("y", 0, 5) ]
    [ 3; 2 ] true "I-P3 int_le: x=3,y=2 (x<=y violated) is a conflict";
  run_le
    (fun store -> Int_lt.make store (var 0) (var 1) ~row_id:1)
    Int_lt.propagate
    [ ("x", 0, 5); ("y", 0, 5) ]
    [ 2; 3 ] false "I-P3 int_lt: x=2,y=3 (x<y holds) is not a conflict";
  run_le
    (fun store -> Int_lt.make store (var 0) (var 1) ~row_id:1)
    Int_lt.propagate
    [ ("x", 0, 5); ("y", 0, 5) ]
    [ 2; 2 ] true "I-P3 int_lt: x=2,y=2 (x<y violated) is a conflict";
  run_le
    (fun store -> Int_eq.make store (var 0) (var 1) ~le_id:1 ~ge_id:2)
    propagate_pair
    [ ("x", 0, 5); ("y", 0, 5) ]
    [ 3; 3 ] false "I-P3 int_eq: x=3,y=3 is not a conflict";
  run_le
    (fun store -> Int_eq.make store (var 0) (var 1) ~le_id:1 ~ge_id:2)
    propagate_pair
    [ ("x", 0, 5); ("y", 0, 5) ]
    [ 3; 4 ] true "I-P3 int_eq: x=3,y=4 is a conflict"

(* ------------------------------------------------------- idempotence at the interface *)

let test_new_idempotence () =
  let run_twice name make propagate bounds =
    let store = mk_store bounds in
    let prop = make store in
    (match propagate prop store with
    | Propagator.Conflict _ ->
        check (Printf.sprintf "%s: expected Fixpoint first pass" name) false
    | Propagator.Fixpoint -> check (Printf.sprintf "%s: first pass is Fixpoint" name) true);
    let snap = Store.snapshot store in
    (match propagate prop store with
    | Propagator.Conflict _ ->
        check (Printf.sprintf "%s: second propagate must not conflict" name) false
    | Propagator.Fixpoint ->
        check (Printf.sprintf "%s: second propagate reports Fixpoint" name) true);
    check
      (Printf.sprintf "%s: second propagate changed nothing" name)
      (Store.same_domains store snap)
  in
  run_twice "int_lin_eq"
    (fun store ->
      Lin_eq.make store [ (2, var 0); (-1, var 1); (3, var 2) ] 4 ~le_id:1 ~ge_id:2)
    propagate_pair
    [ ("x", -3, 3); ("y", -3, 3); ("z", -3, 3) ];
  run_twice "int_le"
    (fun store -> Int_le.make store (var 0) (var 1) ~row_id:1)
    Int_le.propagate
    [ ("x", -3, 3); ("y", -3, 3) ];
  run_twice "int_lt"
    (fun store -> Int_lt.make store (var 0) (var 1) ~row_id:1)
    Int_lt.propagate
    [ ("x", -3, 3); ("y", -3, 3) ];
  run_twice "int_eq"
    (fun store -> Int_eq.make store (var 0) (var 1) ~le_id:1 ~ge_id:2)
    propagate_pair
    [ ("x", -5, 5); ("y", -2, 8) ]

(* ------------------------------------------------- explanation shape, per pruning *)

(* Runs [propagate] once and checks every trail entry it created is a D-0013
   [Combine], verified by [verify_combine] against whichever term the entry's own
   variable is at. *)
let check_all_entries_shape name store bounds terms before =
  let after = Store.trail_length store in
  check (Printf.sprintf "%s: at least one pruning happened" name) (after > before);
  let entries = Store.trail_entries store in
  let new_entries = List.filteri (fun i _ -> i < after - before) entries in
  List.iter
    (fun (e : Store.entry) ->
      let pushed_idx =
        match
          List.find_opt
            (fun i -> Var.equal (var i) e.var)
            (List.mapi (fun i _ -> i) bounds)
        with
        | Some i -> i
        | None -> failwith (name ^ ": pushed var not found by index")
      in
      let expl = Explanation.force (Store.explanation store e) in
      ignore
        (verify_combine ~strict:false name store bounds terms expl
           ~excluded:(Some pushed_idx)))
    new_entries

let test_lin_eq_entailment () =
  let bounds = [ ("x", -3, 3); ("y", -3, 3); ("z", -3, 3) ] in
  let terms = [ (2, var 0); (-1, var 1); (3, var 2) ] in
  let store = mk_store bounds in
  let prop = Lin_eq.make store terms 4 ~le_id:1 ~ge_id:2 in
  let before = Store.trail_length store in
  match propagate_pair prop store with
  | Propagator.Conflict _ -> check "int_lin_eq entailment: expected Fixpoint" false
  | Propagator.Fixpoint ->
      check_all_entries_shape "int_lin_eq entailment" store bounds terms before

(* [make] must run before the simulated earlier pruning, not after -- D-0010's own
   rule ("[make] therefore reads each variable's domain out of the store at
   construction time ... this has to happen before anything ... has narrowed it"),
   restated here because getting the order backwards doesn't fail loudly: it just
   quietly captures the *narrowed* domain as "declared", so the citing case this
   test means to exercise silently degenerates into weakening an already-tight
   declared range instead -- which is another D-0010-shaped trap a green suite can
   miss, this time in the test rather than the propagator. *)
let test_compare_entailment () =
  let bounds = [ ("x", -5, 5); ("y", -5, 5) ] in
  let terms = [ (1, var 0); (-1, var 1) ] in
  (let store = mk_store bounds in
   let prop = Int_le.make store (var 0) (var 1) ~row_id:1 in
   ignore (Store.set_lo store (var 0) 2 placeholder_pruning);
   let before = Store.trail_length store in
   match Int_le.propagate prop store with
   | Propagator.Conflict _ -> check "int_le entailment: expected Fixpoint" false
   | Propagator.Fixpoint ->
       check_all_entries_shape "int_le entailment" store bounds terms before);
  let terms_lt = [ (1, var 0); (-1, var 1) ] in
  let store2 = mk_store bounds in
  let prop2 = Int_lt.make store2 (var 0) (var 1) ~row_id:1 in
  ignore (Store.set_lo store2 (var 0) 2 placeholder_pruning);
  let before2 = Store.trail_length store2 in
  match Int_lt.propagate prop2 store2 with
  | Propagator.Conflict _ -> check "int_lt entailment: expected Fixpoint" false
  | Propagator.Fixpoint ->
      check_all_entries_shape "int_lt entailment" store2 bounds terms_lt before2

let test_int_eq_entailment () =
  let bounds = [ ("x", -5, 5); ("y", -5, 5) ] in
  let terms = [ (1, var 0); (-1, var 1) ] in
  let store = mk_store bounds in
  let prop = Int_eq.make store (var 0) (var 1) ~le_id:1 ~ge_id:2 in
  ignore (Store.set_hi store (var 1) 1 placeholder_pruning);
  let before = Store.trail_length store in
  match propagate_pair prop store with
  | Propagator.Conflict _ -> check "int_eq entailment: expected Fixpoint" false
  | Propagator.Fixpoint ->
      check_all_entries_shape "int_eq entailment" store bounds terms before

(* ============================================================================
   End-to-end veripb checks (I-X1), one per propagator, each with a bound fact two
   or more steps from its declared bound -- the case D-0010 shows a green suite can
   miss entirely at one step. Follows test/unit/test_justify.ml's
   [veripb_path]/[run_veripb]/[setup_int_lin_le] shape. *)

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

(* Compared by rule body, not by name: 3.0 introduces every derived constraint with a
   label (`@c17 rup ... ;`) and these expectations are about what the rule says. The
   label is checked where it means something -- by the checker, which rejects a citation
   of a name that was never bound -- rather than duplicated into every text pin here. *)
let has_line text line =
  List.exists
    (fun l -> String.equal line (Writer.strip_label l))
    (String.split_on_char '\n' text)

(* A rule pinned by what it SAYS, through the module that wrote it. [Writer.rule_body]
   takes the 3.0 label off the front and the terminator off the back, so one expectation
   means the same thing under both proof formats -- the rule the orchestrator's
   2.0-to-3.0 note leaves behind: a test that reads emitted proof text goes through
   [Writer]. *)
let has_rule text body =
  List.exists
    (fun l -> String.equal body (Writer.rule_body l))
    (String.split_on_char '\n' text)

(* ---------------------------------------------------------------- M1-T42, measured

   The four builders below justify their pruning with a [pol] (an
   [Explanation.Combine]), and that makes them weak in a way D-0032's remedy does not
   reach. Both halves of this were measured before anything was changed, by deleting
   the facts from the justification each one exercises:

     build_int_lin_eq_multi   pol   fact as .opb row   ACCEPTED -- nothing went red
     build_int_le_multi       pol   fact as .opb row   ACCEPTED -- nothing went red
     build_int_lt_multi       pol   fact as .opb row   ACCEPTED -- nothing went red
     build_int_eq_multi       pol   fact as .opb row   ACCEPTED -- nothing went red
     test_lin_eq_pairing      pol   fact as .opb row   ACCEPTED -- nothing went red

   The reason is NOT D-0032's. A [rup] states a claim and the checker refutes a false
   one; a [pol] states a *derivation*, and veripb recomputes whatever the expression
   yields and accepts any well-formed one. Dropping a summand does not produce a false
   line, it produces a different -- weaker -- constraint, validly derived. So a factless
   control is impossible on a [pol]: there is nothing for the checker to refuse, whether
   or not the facts are model rows.

   Two things follow, and both are done below.

   1. What guards these four is an assertion on the emitted text: the derivation must
      cite the fact's id ([check_pol_cites]). That is a shape pin, and it is said to be
      one -- it is the same guard the int_ne builders already had in their verbatim
      [rup] pins, and it is what actually went red in the measurement above for those.

   2. The artefact that DOES carry a claim for these propagators is D-0018's trace line,
      which is what a real run writes for every pruning. So each of the four gets a
      second scene -- [decision_scene_*] below -- in D-0032's shape: the setup bound is
      established in the store alone, as a decision establishes it, the .opb holds only
      the propagator's own row, and the trace line is emitted and checked. Those scenes
      carry the factless controls, and there the control is real: with the fact in the
      store the claim alone is simply false of the model, and veripb rejects it.

   A finding from building scene 2, reported at the time rather than fixed because it
   was in lib/core: with the setup bound established by a *decision* (explanation
   [Trivial], which is what search.ml pushed), [linear.ml]'s [Snap_cite] cited that
   [Trivial], and [Justify.emit Trivial] answered [ctx.model_id ()] -- so the [Combine]
   emitted `pol <own row> <own row> +`, citing the propagator's own row where the fact
   should be. veripb accepted it, because a [pol] has no claim.

   **Fixed by M1-T50.** A decision's reason is [Explanation.Decision lit], not
   [Trivial]; [snapshot_source] takes a third branch, [Snap_assume], which weakens the
   term out of the row (a decision has no id to cite) while still contributing its
   literal to the trace fact. So the four [decision_scene_*] builders below now push a
   real decision, and the pol they would build no longer names the row twice. The trace
   line remains what scene 2 pins -- that has not changed, and neither has a byte of
   what these scenes emit. The shape itself is observed in test_matrix.ml, as
   [D_weaken_and_assume]. *)
let check_pol_cites base pbp w ~row ~fact =
  let text = read_file pbp in
  let want = Printf.sprintf "pol %s %s +" (Writer.cite w row) (Writer.cite w fact) in
  let ok = has_rule text want in
  if not ok then Printf.printf "     (actual proof text)\n%s\n" text;
  check (Printf.sprintf "%s: the pol cites the fact's id -- `%s`" base want) ok

let run_veripb ~name ~build =
  match veripb_path () with
  | None ->
      incr failures;
      Printf.printf
        "FAIL %s: veripb not found -- invariant I-X1 was NOT checked. Install it (see \
         docs/PROOF-FORMAT.md) and re-run; do not treat this as a pass.\n"
        name
  | Some veripb -> (
      let dir = Filename.temp_file "baguette_prop_veripb" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      let opb, pbp = build dir in
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
      if rc = 0 then Printf.printf "ok   %s (I-X1)\n" name
      else (
        incr failures;
        Printf.printf "FAIL %s: veripb rejected the proof (I-X1)\n%s\n" name out;
        Printf.printf "  model: %s\n  proof: %s\n" opb pbp);
      List.iter (fun f -> try Sys.remove f with _ -> ()) [ opb; pbp; log ];
      try Sys.rmdir dir with _ -> ())

(* int_lin_eq: x1 + x2 = 4, x1, x2 declared [0,5]. x2 is pinned to exactly 2 by a real
   model constraint (x2 <= 2 *and* x2 >= 2, i.e. x2 = 2 is asserted outright, four
   literals' worth of chain contribution split across upper and lower); the pruning we
   justify is x1's hi tightened by the >= (ge) half of the equality, whose reason cites
   x2's *upper*-bound chain -- x2's current hi (2) is three steps below its declared hi
   (5): x2 <= 2, x2 <= 3, x2 <= 4, strictly more than the one-step case D-0010 shows is
   not enough of a test. *)
let build_int_lin_eq_multi dir =
  let e = Encoding.create () in
  Encoding.declare_int e "x1" ~lo:0 ~hi:5;
  Encoding.declare_int e "x2" ~lo:0 ~hi:5;
  let c_x2_le = Encoding.add_constraint e (Opb.ge [ (1, Lit.le "x2" 2) ] 1) in
  let c_x2_ge = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "x2" 2) ] 1) in
  let opb_terms, const = Encoding.linear_terms_int_lin_le e [ (1, "x1"); (1, "x2") ] in
  let geq_id, leq_id = Encoding.add_equality e opb_terms (4 - const) in
  ignore leq_id;
  let opb = Filename.concat dir "linteq_multi.opb" in
  let pbp = Filename.concat dir "linteq_multi.pbp" in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "x1 + x2 = 4; x2 = 2 (established)" ] e oc;
  close_out oc;
  let store =
    Store.create ~names:[| "x1"; "x2" |] ~domains:[| Domain.make 0 5; Domain.make 0 5 |]
  in
  let le, ge =
    Lin_eq.make store
      [ (1, Var.of_int 0); (1, Var.of_int 1) ]
      4 ~le_id:leq_id ~ge_id:geq_id
  in
  (match
     Store.set_hi store (Var.of_int 1) 2
       (Reason.because Reason.none (Explanation.model_row c_x2_le))
   with
  | Store.Changed -> ()
  | _ -> failwith "build_int_lin_eq_multi: x2 <= 2 setup failed");
  (match
     Store.set_lo store (Var.of_int 1) 2
       (Reason.because Reason.none (Explanation.model_row c_x2_ge))
   with
  | Store.Changed -> ()
  | _ -> failwith "build_int_lin_eq_multi: x2 >= 2 setup failed");
  (* D-0011: [le] and [ge] are two independently-justified instances, each posted (in
     a real engine) against its own model row -- run them here exactly as the engine
     would run two separately-watched propagators, one after the other. *)
  (match Linear.propagate le store with
  | Propagator.Conflict _ -> failwith "build_int_lin_eq_multi: le pass conflicted"
  | Propagator.Fixpoint -> ());
  let before = Store.trail_length store in
  (match Linear.propagate ge store with
  | Propagator.Conflict _ -> failwith "build_int_lin_eq_multi: ge pass conflicted"
  | Propagator.Fixpoint -> ());
  let after = Store.trail_length store in
  let entries =
    List.filteri (fun i _ -> i < after - before) (Store.trail_entries store)
  in
  let entry =
    match
      List.find_opt (fun (en : Store.entry) -> Var.equal en.var (Var.of_int 0)) entries
    with
    | Some en -> en
    | None -> failwith "build_int_lin_eq_multi: x1's bound was never pushed by ge"
  in
  let expl = Explanation.force (Store.explanation store entry) in
  let oc = open_out pbp in
  let w = Writer.create ~comments:true ~audit:true oc in
  Encoding.start_proof e w;
  let ctx = Justify.create ~writer:w ~encoding:e in
  let id = Justify.emit ctx expl in
  Writer.delete w id;
  Writer.conclusion w (Writer.Sat (Encoding.assignment_lits e [ ("x1", 2); ("x2", 2) ]));
  close_out oc;
  check_pol_cites "int_lin_eq multi-step" pbp w ~row:geq_id ~fact:c_x2_le;
  (opb, pbp)

(* int_le: x <= y, x, y declared [0,5]. x >= 3 is established by a real model
   constraint, three steps above x's declared lo of 0 (x >= 1, x >= 2, x >= 3), and
   drives lo(y) up to 3 via int_le's own propagation -- the reason for that push cites
   x's full three-literal chain. *)
let build_int_le_multi dir =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:5;
  Encoding.declare_int e "y" ~lo:0 ~hi:5;
  let c_bound = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "x" 3) ] 1) in
  let model_row = Encoding.add_int_lin_le e [ (1, "x"); (-1, "y") ] 0 in
  let opb = Filename.concat dir "intle_multi.opb" in
  let pbp = Filename.concat dir "intle_multi.pbp" in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "x <= y; x >= 3 (established)" ] e oc;
  close_out oc;
  let store =
    Store.create ~names:[| "x"; "y" |] ~domains:[| Domain.make 0 5; Domain.make 0 5 |]
  in
  let prop = Int_le.make store (Var.of_int 0) (Var.of_int 1) ~row_id:model_row in
  (match
     Store.set_lo store (Var.of_int 0) 3
       (Reason.because Reason.none (Explanation.model_row c_bound))
   with
  | Store.Changed -> ()
  | _ -> failwith "build_int_le_multi: x >= 3 setup failed");
  let before = Store.trail_length store in
  (match Int_le.propagate prop store with
  | Propagator.Conflict _ -> failwith "build_int_le_multi: propagate conflicted"
  | Propagator.Fixpoint -> ());
  let after = Store.trail_length store in
  let entries =
    List.filteri (fun i _ -> i < after - before) (Store.trail_entries store)
  in
  let entry =
    match
      List.find_opt (fun (en : Store.entry) -> Var.equal en.var (Var.of_int 1)) entries
    with
    | Some en -> en
    | None -> failwith "build_int_le_multi: y's bound was never pushed"
  in
  let expl = Explanation.force (Store.explanation store entry) in
  let oc = open_out pbp in
  let w = Writer.create ~comments:true ~audit:true oc in
  Encoding.start_proof e w;
  let ctx = Justify.create ~writer:w ~encoding:e in
  let id = Justify.emit ctx expl in
  Writer.delete w id;
  Writer.conclusion w (Writer.Sat (Encoding.assignment_lits e [ ("x", 3); ("y", 3) ]));
  close_out oc;
  check_pol_cites "int_le multi-step" pbp w ~row:model_row ~fact:c_bound;
  (opb, pbp)

(* int_lt: x < y, x, y declared [0,5]. x >= 3 established (three steps), driving
   lo(y) up to 4 via int_lt -- same chain shape as int_le above, checked separately
   since int_lt is a different rhs (-1) over the same two-term row, not a re-run of
   the same proof. *)
let build_int_lt_multi dir =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:5;
  Encoding.declare_int e "y" ~lo:0 ~hi:5;
  let c_bound = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "x" 3) ] 1) in
  let model_row = Encoding.add_int_lin_le e [ (1, "x"); (-1, "y") ] (-1) in
  let opb = Filename.concat dir "intlt_multi.opb" in
  let pbp = Filename.concat dir "intlt_multi.pbp" in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "x < y; x >= 3 (established)" ] e oc;
  close_out oc;
  let store =
    Store.create ~names:[| "x"; "y" |] ~domains:[| Domain.make 0 5; Domain.make 0 5 |]
  in
  let prop = Int_lt.make store (Var.of_int 0) (Var.of_int 1) ~row_id:model_row in
  (match
     Store.set_lo store (Var.of_int 0) 3
       (Reason.because Reason.none (Explanation.model_row c_bound))
   with
  | Store.Changed -> ()
  | _ -> failwith "build_int_lt_multi: x >= 3 setup failed");
  let before = Store.trail_length store in
  (match Int_lt.propagate prop store with
  | Propagator.Conflict _ -> failwith "build_int_lt_multi: propagate conflicted"
  | Propagator.Fixpoint -> ());
  let after = Store.trail_length store in
  let entries =
    List.filteri (fun i _ -> i < after - before) (Store.trail_entries store)
  in
  let entry =
    match
      List.find_opt (fun (en : Store.entry) -> Var.equal en.var (Var.of_int 1)) entries
    with
    | Some en -> en
    | None -> failwith "build_int_lt_multi: y's bound was never pushed"
  in
  let expl = Explanation.force (Store.explanation store entry) in
  let oc = open_out pbp in
  let w = Writer.create ~comments:true ~audit:true oc in
  Encoding.start_proof e w;
  let ctx = Justify.create ~writer:w ~encoding:e in
  let id = Justify.emit ctx expl in
  Writer.delete w id;
  Writer.conclusion w (Writer.Sat (Encoding.assignment_lits e [ ("x", 3); ("y", 4) ]));
  close_out oc;
  check_pol_cites "int_lt multi-step" pbp w ~row:model_row ~fact:c_bound;
  (opb, pbp)

(* int_eq: x = y, x, y declared [0,5]. y <= 2 is established by a real model
   constraint, three steps below y's declared hi of 5 (y <= 2, y <= 3, y <= 4), which
   int_eq's le half turns into a push of x's hi down to 2, citing y's full
   three-literal upper chain. *)
let build_int_eq_multi dir =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:5;
  Encoding.declare_int e "y" ~lo:0 ~hi:5;
  let c_bound = Encoding.add_constraint e (Opb.ge [ (1, Lit.le "y" 2) ] 1) in
  let opb_terms, const = Encoding.linear_terms_int_lin_le e [ (1, "x"); (-1, "y") ] in
  let geq_id, leq_id = Encoding.add_equality e opb_terms (0 - const) in
  ignore geq_id;
  let opb = Filename.concat dir "inteq_multi.opb" in
  let pbp = Filename.concat dir "inteq_multi.pbp" in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "x = y; y <= 2 (established)" ] e oc;
  close_out oc;
  let store =
    Store.create ~names:[| "x"; "y" |] ~domains:[| Domain.make 0 5; Domain.make 0 5 |]
  in
  let le, _ge =
    Int_eq.make store (Var.of_int 0) (Var.of_int 1) ~le_id:leq_id ~ge_id:geq_id
  in
  (match
     Store.set_hi store (Var.of_int 1) 2
       (Reason.because Reason.none (Explanation.model_row c_bound))
   with
  | Store.Changed -> ()
  | _ -> failwith "build_int_eq_multi: y <= 2 setup failed");
  let before = Store.trail_length store in
  (* D-0011: only [le] is run -- it alone is the instance whose model row (leq_id) we
     are about to justify against; [ge] is irrelevant to this pruning and posting it
     would just be extra queue churn a real engine schedule would also pay. *)
  (match Linear.propagate le store with
  | Propagator.Conflict _ -> failwith "build_int_eq_multi: le pass conflicted"
  | Propagator.Fixpoint -> ());
  let after = Store.trail_length store in
  let entries =
    List.filteri (fun i _ -> i < after - before) (Store.trail_entries store)
  in
  let entry =
    match
      List.find_opt (fun (en : Store.entry) -> Var.equal en.var (Var.of_int 0)) entries
    with
    | Some en -> en
    | None -> failwith "build_int_eq_multi: x's bound was never pushed by le"
  in
  let expl = Explanation.force (Store.explanation store entry) in
  let oc = open_out pbp in
  let w = Writer.create ~comments:true ~audit:true oc in
  Encoding.start_proof e w;
  let ctx = Justify.create ~writer:w ~encoding:e in
  let id = Justify.emit ctx expl in
  Writer.delete w id;
  Writer.conclusion w (Writer.Sat (Encoding.assignment_lits e [ ("x", 2); ("y", 2) ]));
  close_out oc;
  check_pol_cites "int_eq multi-step" pbp w ~row:leq_id ~fact:c_bound;
  (opb, pbp)

(* ------------------------------ M1-T42 scene 2: the claim, and the factless control

   D-0032's shape, for the four integer propagators. The setup bound is established in
   the STORE and nowhere else -- as a decision establishes it, with no .opb row saying
   anything about it -- so the .opb holds exactly the propagator's own row(s). What is
   emitted is D-0018's trace line for the pruning: the claim, disjoined with the
   negation of the facts the propagator actually read. That line is the artefact that
   carries a claim, and it is the one a real run writes; the [pol] above cannot be
   controlled (see [check_pol_cites]'s header).

   With the fact in the store rather than in the model, `claim alone` is simply false of
   the .opb, so each [*_factless] control below is rejected by the checker -- and under
   a scene that posted the fact as a model row it would be ACCEPTED, which is the whole
   of D-0032 in one sentence. *)

let entry_since store before v what =
  let after = Store.trail_length store in
  let entries =
    List.filteri (fun i _ -> i < after - before) (Store.trail_entries store)
  in
  match List.find_opt (fun (en : Store.entry) -> Var.equal en.Store.var v) entries with
  | Some en -> en
  | None -> failwith (what ^ ": the bound under test was never pushed")

(* Each scene returns (encoding, the pruning's trail entry, the pruned variable's name,
   the row Justify's ctx falls back to, a solution of the .opb). *)
let decision_scene_int_le () =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:5;
  Encoding.declare_int e "y" ~lo:0 ~hi:5;
  let row = Encoding.add_int_lin_le e [ (1, "x"); (-1, "y") ] 0 in
  let store =
    Store.create ~names:[| "x"; "y" |] ~domains:[| Domain.make 0 5; Domain.make 0 5 |]
  in
  let prop = Int_le.make store (Var.of_int 0) (Var.of_int 1) ~row_id:row in
  (match
     Store.set_lo store (Var.of_int 0) 3
       (Reason.because Reason.none (Explanation.decision (Lit.ge "x" 3)))
   with
  | Store.Changed -> ()
  | _ -> failwith "decision_scene_int_le: the decision did not move x's bound");
  let before = Store.trail_length store in
  (match Int_le.propagate prop store with
  | Propagator.Conflict _ -> failwith "decision_scene_int_le: propagate conflicted"
  | Propagator.Fixpoint -> ());
  ( e,
    entry_since store before (Var.of_int 1) "decision_scene_int_le",
    "y",
    row,
    [ ("x", 3); ("y", 3) ] )

let decision_scene_int_lt () =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:5;
  Encoding.declare_int e "y" ~lo:0 ~hi:5;
  let row = Encoding.add_int_lin_le e [ (1, "x"); (-1, "y") ] (-1) in
  let store =
    Store.create ~names:[| "x"; "y" |] ~domains:[| Domain.make 0 5; Domain.make 0 5 |]
  in
  let prop = Int_lt.make store (Var.of_int 0) (Var.of_int 1) ~row_id:row in
  (match
     Store.set_lo store (Var.of_int 0) 3
       (Reason.because Reason.none (Explanation.decision (Lit.ge "x" 3)))
   with
  | Store.Changed -> ()
  | _ -> failwith "decision_scene_int_lt: the decision did not move x's bound");
  let before = Store.trail_length store in
  (match Int_lt.propagate prop store with
  | Propagator.Conflict _ -> failwith "decision_scene_int_lt: propagate conflicted"
  | Propagator.Fixpoint -> ());
  ( e,
    entry_since store before (Var.of_int 1) "decision_scene_int_lt",
    "y",
    row,
    [ ("x", 3); ("y", 4) ] )

let decision_scene_int_eq () =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:5;
  Encoding.declare_int e "y" ~lo:0 ~hi:5;
  let opb_terms, const = Encoding.linear_terms_int_lin_le e [ (1, "x"); (-1, "y") ] in
  let geq_id, leq_id = Encoding.add_equality e opb_terms (0 - const) in
  let store =
    Store.create ~names:[| "x"; "y" |] ~domains:[| Domain.make 0 5; Domain.make 0 5 |]
  in
  let le, _ge =
    Int_eq.make store (Var.of_int 0) (Var.of_int 1) ~le_id:leq_id ~ge_id:geq_id
  in
  (match
     Store.set_hi store (Var.of_int 1) 2
       (Reason.because Reason.none (Explanation.decision (Lit.le "y" 2)))
   with
  | Store.Changed -> ()
  | _ -> failwith "decision_scene_int_eq: the decision did not move y's bound");
  let before = Store.trail_length store in
  (match Linear.propagate le store with
  | Propagator.Conflict _ -> failwith "decision_scene_int_eq: le pass conflicted"
  | Propagator.Fixpoint -> ());
  ( e,
    entry_since store before (Var.of_int 0) "decision_scene_int_eq",
    "x",
    leq_id,
    [ ("x", 2); ("y", 2) ] )

let decision_scene_int_lin_eq () =
  let e = Encoding.create () in
  Encoding.declare_int e "x1" ~lo:0 ~hi:5;
  Encoding.declare_int e "x2" ~lo:0 ~hi:5;
  let opb_terms, const = Encoding.linear_terms_int_lin_le e [ (1, "x1"); (1, "x2") ] in
  let geq_id, leq_id = Encoding.add_equality e opb_terms (4 - const) in
  let store =
    Store.create ~names:[| "x1"; "x2" |] ~domains:[| Domain.make 0 5; Domain.make 0 5 |]
  in
  let le, ge =
    Lin_eq.make store
      [ (1, Var.of_int 0); (1, Var.of_int 1) ]
      4 ~le_id:leq_id ~ge_id:geq_id
  in
  (* x2 = 2, both bounds, by decision: two store pushes and not one .opb row. *)
  (match
     Store.set_hi store (Var.of_int 1) 2
       (Reason.because Reason.none (Explanation.decision (Lit.le "x2" 2)))
   with
  | Store.Changed -> ()
  | _ -> failwith "decision_scene_int_lin_eq: x2 <= 2 did not move");
  (match
     Store.set_lo store (Var.of_int 1) 2
       (Reason.because Reason.none (Explanation.decision (Lit.ge "x2" 2)))
   with
  | Store.Changed -> ()
  | _ -> failwith "decision_scene_int_lin_eq: x2 >= 2 did not move");
  (match Linear.propagate le store with
  | Propagator.Conflict _ -> failwith "decision_scene_int_lin_eq: le pass conflicted"
  | Propagator.Fixpoint -> ());
  let before = Store.trail_length store in
  (match Linear.propagate ge store with
  | Propagator.Conflict _ -> failwith "decision_scene_int_lin_eq: ge pass conflicted"
  | Propagator.Fixpoint -> ());
  ( e,
    entry_since store before (Var.of_int 0) "decision_scene_int_lin_eq",
    "x1",
    geq_id,
    [ ("x1", 2); ("x2", 2) ] )

(* [factless] deletes the facts, leaving the claim on its own -- exactly what a
   justification that forgot to record what it read would emit. *)
let write_trace_case dir ~file ~scene ~factless ~expect_lines =
  let e, (entry : Store.entry), target, row, sol = scene () in
  (* The scenes still report the row their propagator is about; nothing here resolves
     a row from the ctx any more (M1-T31). *)
  ignore row;
  let opb = Filename.concat dir (file ^ ".opb") in
  let pbp = Filename.concat dir (file ^ ".pbp") in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ file ] e oc;
  close_out oc;
  let facts = if factless then [] else Reason.lits entry.Store.reason in
  let oc = open_out pbp in
  let w = Writer.create ~comments:true ~audit:true oc in
  Encoding.start_proof e w;
  let ctx = Justify.create ~writer:w ~encoding:e in
  (match Trace.claims e entry target with
  | [] -> failwith (file ^ ": the pruning under test moved no bound, so it has no claim")
  | claims ->
      List.iter
        (fun claim ->
          let id =
            Trace.emit_line ctx ~origin:(file ^ ": D-0018 trace line") ~claim ~facts
          in
          Writer.delete w id)
        claims);
  Writer.conclusion w (Writer.Sat (Encoding.assignment_lits e sol));
  close_out oc;
  let text = read_file pbp in
  List.iter
    (fun line ->
      let ok = has_line text line in
      if not ok then Printf.printf "     (actual proof text)\n%s\n" text;
      check (Printf.sprintf "%s: emits `%s`" file line) ok)
    expect_lines;
  (opb, pbp)

let trace_builders =
  [
    ( "int_le",
      decision_scene_int_le,
      "rup +1 y_ge_3 +1 ~x_ge_3 >= 1 ;",
      "rup +1 y_ge_3 >= 1 ;" );
    ( "int_lt",
      decision_scene_int_lt,
      "rup +1 y_ge_4 +1 ~x_ge_3 >= 1 ;",
      "rup +1 y_ge_4 >= 1 ;" );
    ( "int_eq",
      decision_scene_int_eq,
      "rup +1 ~x_ge_3 +1 y_ge_3 >= 1 ;",
      "rup +1 ~x_ge_3 >= 1 ;" );
    ( "int_lin_eq",
      decision_scene_int_lin_eq,
      "rup +1 x1_ge_2 +1 x2_ge_3 >= 1 ;",
      "rup +1 x1_ge_2 >= 1 ;" );
  ]

(* ============================================================================
   D-0011: pairing. [Lin_eq.make]/[Int_eq.make] hand back TWO instances precisely so
   that each one justifies against exactly one model row, with nothing downstream ever
   having to inspect an explanation to guess which row it meant.

   Before M1-T12 this had to be checked by *trying* the wrong pairing and seeing
   whether veripb happened to catch it -- [Explanation.Trivial] carried no row
   identity of its own, so a caller could always cite it against the wrong
   [ctx.model_id] and the mistake was only ever a matter of proof-checker luck (see
   this file's history: it used to run that experiment and print a NOTE either way).

   [Explanation.Model_row] (docs/DECISIONS.md D-0013) removes the hazard structurally
   instead of by discipline: [Linear.make]'s [~row_id] bakes each instance's own row
   into every explanation it ever builds. The check below used to assert that by giving
   [ctx] a [model_id] thunk that failed if ever called and watching the proof verify
   anyway. M1-T31 finished the job and the assertion is now the type's: [Justify.ctx]
   has no [model_id] field, so there is no ambient row for a caller to get wrong, and
   [~row_id] is required rather than optional. What is left to check here is that the
   pairing is right -- that [le] names the `<=` row and [ge] the `>=` one -- which the
   checker still answers, because naming the wrong one of the two is a derivation
   veripb refuses. *)
let test_lin_eq_pairing () =
  let build dir =
    let e = Encoding.create () in
    Encoding.declare_int e "x1" ~lo:0 ~hi:5;
    Encoding.declare_int e "x2" ~lo:0 ~hi:5;
    let c_bound = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "x2" 2) ] 1) in
    let opb_terms, const = Encoding.linear_terms_int_lin_le e [ (1, "x1"); (1, "x2") ] in
    let geq_id, leq_id = Encoding.add_equality e opb_terms (4 - const) in
    let opb = Filename.concat dir "linteq_pairing.opb" in
    let oc = open_out opb in
    Encoding.write_opb ~comments:[ "x1 + x2 = 4; x2 >= 2 (established)" ] e oc;
    close_out oc;
    let store =
      Store.create ~names:[| "x1"; "x2" |] ~domains:[| Domain.make 0 5; Domain.make 0 5 |]
    in
    let le, _ge =
      Lin_eq.make store
        [ (1, Var.of_int 0); (1, Var.of_int 1) ]
        4 ~le_id:leq_id ~ge_id:geq_id
    in
    (match
       Store.set_lo store (Var.of_int 1) 2
         (Reason.because Reason.none (Explanation.model_row c_bound))
     with
    | Store.Changed -> ()
    | _ -> failwith "test_lin_eq_pairing: x2 >= 2 setup failed");
    let before = Store.trail_length store in
    (match Linear.propagate le store with
    | Propagator.Conflict _ -> failwith "test_lin_eq_pairing: le pass conflicted"
    | Propagator.Fixpoint -> ());
    let after = Store.trail_length store in
    let entries =
      List.filteri (fun i _ -> i < after - before) (Store.trail_entries store)
    in
    let entry =
      match
        List.find_opt (fun (en : Store.entry) -> Var.equal en.var (Var.of_int 0)) entries
      with
      | Some en -> en
      | None -> failwith "test_lin_eq_pairing: x1's bound was never pushed by le"
    in
    let expl = Explanation.force (Store.explanation store entry) in
    let pbp = Filename.concat dir "linteq_pairing.pbp" in
    let oc = open_out pbp in
    let w = Writer.create ~comments:true ~audit:true oc in
    Encoding.start_proof e w;
    (* [expl]'s base is [Model_row leq_id]. This used to install a [~model_id] thunk
       that failed if consulted; M1-T31 deleted the field, so the property it asserted
       -- that nothing here resolves a row from ambient state -- now holds of the type
       rather than of this scene. *)
    let ctx = Justify.create ~writer:w ~encoding:e in
    let id = Justify.emit ctx expl in
    Writer.delete w id;
    Writer.conclusion w (Writer.Sat (Encoding.assignment_lits e [ ("x1", 2); ("x2", 2) ]));
    close_out oc;
    (opb, pbp)
  in
  run_veripb
    ~name:
      "D-0011 pairing: le's explanation names its own row (Model_row leq_id) and still \
       verifies"
    ~build

(* ============================================================================
   M1-T9: int_ne and int_lin_ne (lib/core/prop/ne.ml), and the disequality rows
   lib/proof/encoding.ml posts for them.

   Three things are being tested here and it is worth keeping them apart, because
   this project has now had five findings that were invisible on the instance chosen
   to test the thing they broke (D-0009, D-0010, D-0012, D-0017, D-0018):

   1. the propagator's own behaviour -- I-P1 soundness by brute force, I-P3 checking,
      I-P2/I-P3 idempotence;
   2. the *text* of what is emitted -- the .opb rows and the [rup] line -- asserted
      verbatim, because the encoding is normative (docs/PROOF-FORMAT.md section 3) and
      a silent change of shape is exactly the class of defect D-0010 was;
   3. whether veripb accepts it (I-X1), including a deliberately wrong [rup] that it
      must *reject*. Without that last one, "veripb accepted our rup" says nothing:
      [rup] is the one rule that searches for its own justification, so a test that
      only ever feeds it true clauses cannot tell a correct explanation from a lucky
      one. This is the local version of M1-T15's point.

   Instance choice, deliberately one step past the smallest thing that works: every
   case below fixes its reason variables to values that are *interior* to their
   declared domains (so both halves of the "x <> v" clause are real literals, not
   dropped constants), prunes a value that is *interior* to the pruned variable's
   domain in at least one case (a genuine hole, not a bound move) and at a *bound* in
   another (where one half of the clause is dropped), and the int_lin_ne case uses
   three variables with coefficients 2, 3 and -1 rather than the +/-1 an int_ne would
   have exercised anyway. A disequality test where both variables are already fixed
   tests nothing at all. *)

let raises name f =
  match f () with exception _ -> check name true | _ -> check name false

(* Like [run_veripb], but the proof MUST be rejected. Used for the negative controls:
   a wrong explanation has to fail, or the positive checks prove nothing. *)
let run_veripb_rejects ~name ~build =
  match veripb_path () with
  | None ->
      incr failures;
      Printf.printf
        "FAIL %s: veripb not found -- invariant I-X1 was NOT checked. Install it (see \
         docs/PROOF-FORMAT.md) and re-run; do not treat this as a pass.\n"
        name
  | Some veripb -> (
      let dir = Filename.temp_file "baguette_prop_veripb_neg" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      let opb, pbp = build dir in
      let log = Filename.concat dir "log" in
      let rc =
        Sys.command
          (Printf.sprintf "%s %s %s > %s 2>&1" (Filename.quote veripb)
             (Filename.quote opb) (Filename.quote pbp) (Filename.quote log))
      in
      check (Printf.sprintf "%s (veripb rejects it, as it must)" name) (rc <> 0);
      List.iter (fun f -> try Sys.remove f with _ -> ()) [ opb; pbp; log ];
      try Sys.rmdir dir with _ -> ())

(* ---------------------------------------------- the "x <> v" clause, on its own *)

let test_ne_clause_lits () =
  let s lits = String.concat " " (List.map Lit.to_string lits) in
  let lits v = Encoding.ne_clause_lits ~name:"x" ~decl_lo:0 ~decl_hi:4 v in
  check "ne_clause_lits: an interior value gives both halves"
    (s (lits 2) = "~x_ge_2 x_ge_3");
  check "ne_clause_lits: at the declared lo, ~[x >= lo] is the constant false and drops"
    (s (lits 0) = "x_ge_1");
  check "ne_clause_lits: at the declared hi, [x >= hi+1] is the constant false and drops"
    (s (lits 4) = "~x_ge_4");
  (* A variable the model declares fixed cannot be different from that value: the
     clause is empty, i.e. false, which is the correct answer and not a degenerate
     one -- [Explanation.Clause []] renders as [rup >= 1 ;], a contradiction, and
     veripb accepts that line against a .opb whose ne rows are unsatisfiable. *)
  check "ne_clause_lits: a declared-fixed variable gives the empty (false) clause"
    (Encoding.ne_clause_lits ~name:"k" ~decl_lo:3 ~decl_hi:3 3 = []);
  raises "ne_clause_lits: a value outside the declared domain is an error" (fun () ->
      ignore (Encoding.ne_clause_lits ~name:"x" ~decl_lo:0 ~decl_hi:4 5));
  (* [Encoding.ne_clause] must agree with the explicit-bounds form: they are one
     implementation and the propagator calls the explicit one with bounds it froze at
     [make] time (D-0010), so a divergence would be invisible from the propagator. *)
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:4;
  check "ne_clause: the t-reading wrapper agrees with the explicit-bounds form"
    (Encoding.ne_clause e "x" 2 = lits 2)

(* ------------------------------------------------------- the .opb rows, verbatim *)

let test_ne_rows () =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:1 ~hi:2;
  Encoding.declare_int e "y" ~lo:1 ~hi:2;
  let before = Encoding.n_constraints e in
  let id_a, id_b = Encoding.add_int_lin_ne e [ (1, "x"); (-1, "y") ] 0 in
  check "add_int_lin_ne: exactly two ids, consecutive"
    (id_b = id_a + 1 && id_a = before + 1);
  check "add_int_lin_ne: exactly two .opb lines" (Encoding.n_constraints e - before = 2);
  (* The trap docs/PROOF-FORMAT.md section 2 records: an .opb line with '=' counts as
     TWO constraints for [f], which shifts every later id. These rows are plain '>='
     lines, and this is the assertion that says so rather than hoping. *)
  check "add_int_lin_ne: the f count still equals the id count (no '=' line)"
    (Opb.n_checker_constraints (Encoding.constraints e) = Encoding.n_constraints e);
  let rows = List.map Opb.constr_to_string (Encoding.constraints e) in
  check "add_int_lin_ne: row A is the 'sum <= c-1' side, selected by the aux bool"
    (List.nth rows (before + 0) = "+1 ~x_ge_2 +1 y_ge_2 +2 _ne0_ge_1 >= 2 ;");
  check "add_int_lin_ne: row B is the 'sum >= c+1' side"
    (List.nth rows (before + 1) = "+1 x_ge_2 +1 ~y_ge_2 +2 ~_ne0_ge_1 >= 2 ;");
  (* The aux Boolean is order-encoded on [0,1] (D-0007), so it contributes no
     consistency clause of its own -- which is why the two rows above are the only
     two lines this call added. *)
  check "add_int_lin_ne: the aux bool is declared, under a name FlatZinc cannot spell"
    (Encoding.is_declared e "$ne0" && not (Encoding.is_declared e "_ne0"));
  let id_c, _ = Encoding.add_int_lin_ne e [ (1, "x") ] 2 in
  check "add_int_lin_ne: a second disequality mints a second aux bool"
    (Encoding.is_declared e "$ne1" && id_c = id_b + 1)

(* ---------------------------------------------------------- I-P1: soundness *)

let satisfies_ne coeffs rhs assignment =
  List.fold_left2 (fun acc a v -> acc + (a * v)) 0 coeffs assignment <> rhs

(* Brute force, in the same shape as [check_soundness_case] above but over the box
   *after* the pre-fixing, since a disequality infers nothing until all but one of its
   terms is fixed. [pre] is (index, value) pairs fixed before propagation, standing in
   for whatever earlier propagator or decision fixed them.

   Two directions are checked. I-P1 (never remove a supported value) is the one the
   invariant demands. The converse -- with exactly one term left unfixed, every
   *unsupported* value of it is removed -- is the strength claim this algorithm
   actually makes, and it is asserted separately so that a regression that quietly
   stopped pruning would show up as a strength failure rather than as nothing. *)
let check_ne_soundness_case name coeffs rhs ranges pre =
  let n = List.length coeffs in
  let bounds = List.mapi (fun i (lo, hi) -> (Printf.sprintf "x%d" i, lo, hi)) ranges in
  let store = mk_store bounds in
  let prop = Ne.make store (List.mapi (fun i a -> (a, var i)) coeffs) rhs in
  List.iter (fun (i, v) -> ignore (Store.fix store (var i) v placeholder_pruning)) pre;
  let cur =
    List.init n (fun i ->
        let d = Store.get store (var i) in
        (Domain.lo d, Domain.hi d))
  in
  let solutions = List.filter (satisfies_ne coeffs rhs) (cartesian cur) in
  let has_support i v = List.exists (fun sol -> List.nth sol i = v) solutions in
  let nonzero_unfixed =
    List.length
      (List.filteri
         (fun i a -> a <> 0 && not (Domain.is_fixed (Store.get store (var i))))
         coeffs)
  in
  match Ne.propagate prop store with
  | Propagator.Conflict _ ->
      check (Printf.sprintf "%s: conflict only when truly unsat" name) (solutions = [])
  | Propagator.Fixpoint ->
      let sound = ref true and strong = ref true in
      List.iteri
        (fun i (lo, hi) ->
          let d = Store.get store (var i) in
          for v = lo to hi do
            let supported = has_support i v and kept = Domain.mem d v in
            if supported && not kept then sound := false;
            if nonzero_unfixed <= 1 && (not supported) && kept then strong := false
          done)
        cur;
      check (Printf.sprintf "%s: I-P1 no supported value removed" name) !sound;
      check
        (Printf.sprintf "%s: with one term left, every unsupported value is removed" name)
        !strong

let test_ne_soundness () =
  check_ne_soundness_case "int_ne x<>y, y fixed interior" [ 1; -1 ] 0
    [ (0, 4); (0, 4) ]
    [ (1, 2) ];
  check_ne_soundness_case "int_ne x<>y, nothing fixed (must not prune)" [ 1; -1 ] 0
    [ (0, 4); (0, 4) ]
    [];
  check_ne_soundness_case "int_ne x<>y, y fixed at x's declared lo" [ 1; -1 ] 0
    [ (0, 4); (0, 4) ]
    [ (1, 0) ];
  check_ne_soundness_case "int_lin_ne 2a+3b-c<>5, a and b fixed" [ 2; 3; -1 ] 5
    [ (0, 4); (0, 4); (0, 4) ]
    [ (0, 2); (1, 1) ];
  (* The quotient is not an integer: 2a must equal 5 - 3b = 2 ... with b = 0 it is 5,
     odd, so nothing is prunable and the propagator must leave the domain alone. *)
  check_ne_soundness_case "int_lin_ne 2a+3b<>5, non-integral quotient" [ 2; 3 ] 5
    [ (0, 4); (0, 4) ]
    [ (1, 0) ];
  check_ne_soundness_case "int_lin_ne, target outside the reachable range" [ 1; 1 ] 99
    [ (0, 4); (0, 4) ]
    [ (1, 3) ];
  (* A zero coefficient is not part of the constraint: fixing the other two must still
     leave the disequality able to prune the one real unfixed term. *)
  check_ne_soundness_case "int_lin_ne with a zero coefficient" [ 1; 0; -1 ] 0
    [ (0, 4); (0, 4); (0, 4) ]
    [ (0, 2) ];
  check_ne_soundness_case "int_ne, negative domains" [ 1; -1 ] 0
    [ (-3, 3); (-3, 3) ]
    [ (1, -2) ]

(* -------------------------------------------------- I-P3 checking, I-P2 fixpoint *)

let test_ne_checking () =
  let run name coeffs rhs ranges fix_values expect_conflict =
    let bounds = List.mapi (fun i (lo, hi) -> (Printf.sprintf "x%d" i, lo, hi)) ranges in
    let store = mk_store bounds in
    let prop = Ne.make store (List.mapi (fun i a -> (a, var i)) coeffs) rhs in
    List.iteri
      (fun i v -> ignore (Store.fix store (var i) v placeholder_pruning))
      fix_values;
    match Ne.propagate prop store with
    | Propagator.Conflict _ -> check name expect_conflict
    | Propagator.Fixpoint -> check name (not expect_conflict)
  in
  run "I-P3 int_ne: x=2,y=3 (x<>y holds) is not a conflict" [ 1; -1 ] 0
    [ (0, 4); (0, 4) ]
    [ 2; 3 ] false;
  run "I-P3 int_ne: x=2,y=2 (x<>y violated) is a conflict" [ 1; -1 ] 0
    [ (0, 4); (0, 4) ]
    [ 2; 2 ] true;
  run "I-P3 int_lin_ne: 2a+3b-c=5 exactly is a conflict" [ 2; 3; -1 ] 5
    [ (0, 4); (0, 4); (0, 4) ]
    [ 2; 1 - 0; 2 ]
    true;
  run "I-P3 int_lin_ne: one off the forbidden total is not a conflict" [ 2; 3; -1 ] 5
    [ (0, 4); (0, 4); (0, 4) ]
    [ 2; 1; 1 ] false;
  (* A zero coefficient must not be able to make the sum wrong. *)
  run "I-P3 int_lin_ne: a zero coefficient contributes nothing to the check" [ 1; 0; -1 ]
    0
    [ (0, 4); (0, 4); (0, 4) ]
    [ 2; 3; 2 ] true

let test_ne_idempotence () =
  let run name coeffs rhs ranges pre =
    let bounds = List.mapi (fun i (lo, hi) -> (Printf.sprintf "x%d" i, lo, hi)) ranges in
    let store = mk_store bounds in
    let prop = Ne.make store (List.mapi (fun i a -> (a, var i)) coeffs) rhs in
    List.iter (fun (i, v) -> ignore (Store.fix store (var i) v placeholder_pruning)) pre;
    (match Ne.propagate prop store with
    | Propagator.Conflict _ ->
        check (Printf.sprintf "%s: expected Fixpoint first pass" name) false
    | Propagator.Fixpoint -> ());
    let snap = Store.snapshot store in
    (match Ne.propagate prop store with
    | Propagator.Conflict _ ->
        check (Printf.sprintf "%s: I-P2 second propagate must not conflict" name) false
    | Propagator.Fixpoint ->
        check (Printf.sprintf "%s: I-P2 second propagate reports Fixpoint" name) true);
    check
      (Printf.sprintf "%s: I-P3 second propagate changed nothing" name)
      (Store.same_domains store snap)
  in
  run "int_ne idempotence (interior hole)" [ 1; -1 ] 0 [ (0, 4); (0, 4) ] [ (1, 2) ];
  (* The pruning takes the domain from 2 values to 1, so the second pass sees every
     term fixed and must take the *checking* branch instead -- and must not report a
     conflict there, since the value it removed is exactly the one that would have. *)
  run "int_ne idempotence (pruning fixes the variable)" [ 1; -1 ] 0
    [ (2, 3); (0, 4) ]
    [ (1, 2) ];
  run "int_lin_ne idempotence" [ 2; 3; -1 ] 5
    [ (0, 4); (0, 4); (0, 4) ]
    [ (0, 2); (1, 1) ]

(* ============================================================================
   End-to-end: the emitted text, and veripb (I-X1).

   Each build posts the disequality as real .opb rows, narrows the store the way an
   earlier propagator would have, runs the propagator, renders the explanation it
   produced through [Justify], and hands the pair to veripb. [check_lines] asserts the
   emitted text verbatim first, so a shape change is reported as a shape change rather
   than only as a checker rejection several lines later. *)

(* Shared skeleton: declare [decls], post the disequality's two rows, fix [pre] IN THE
   STORE, propagate, pick out the trail entry for [target] (or the conflict), emit it,
   conclude SAT with [sat].

   M1-T42 / D-0032: [pre] used to be pinned by real `.opb` rows as well as in the store,
   and that was measured to weaken every builder below. With `x = 2` posted as a model
   row, the model itself entails `y <> 2`, so a [rup] claiming `y <> 2` with NO REASON AT
   ALL is still true and veripb accepts it, correctly -- the test was asking "is this
   reason valid?" when the property that matters is "is this reason valid *because of
   the facts it cites*?". Measured before it was changed, by deleting the facts from the
   emitted clause: `ne_hole`, `ne_bound` and `lin_ne` all still passed the checker
   (only their verbatim text pins went red), while `ne_conflict`, whose scene already
   held its facts in the store alone, was REJECTED -- which is what a control looks like
   when it works.

   So the facts are established in the store and nowhere else. That is also the faithful
   arrangement: in a real run a fixed value comes from a decision or from another
   propagator, and neither of those is a model row. [build_ne_factless] and
   [build_lin_ne_factless] are the controls this makes possible, and they are
   meaningless under the old scene. *)
let build_ne_case dir ~file ~decls ~terms ~rhs ~pre ~target ~sat ~expect_lines
    ?(corrupt = fun lits -> lits) () =
  let e = Encoding.create () in
  List.iter (fun (n, lo, hi) -> Encoding.declare_int e n ~lo ~hi) decls;
  let decl_name i =
    let n, _, _ = List.nth decls i in
    n
  in
  ignore (Encoding.add_int_lin_ne e (List.map (fun (a, i) -> (a, decl_name i)) terms) rhs);
  let opb = Filename.concat dir (file ^ ".opb") in
  let pbp = Filename.concat dir (file ^ ".pbp") in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ file ] e oc;
  close_out oc;
  let store = mk_store (List.map (fun (n, lo, hi) -> (n, lo, hi)) decls) in
  let prop = Ne.make store (List.map (fun (a, i) -> (a, var i)) terms) rhs in
  List.iter
    (fun (i, v) ->
      match Store.fix store (var i) v placeholder_pruning with
      | Store.Changed | Store.Unchanged -> ()
      | Store.Conflict _ -> failwith (file ^ ": pre-fixing conflicted"))
    pre;
  let before = Store.trail_length store in
  let expl =
    match Ne.propagate prop store with
    | Propagator.Conflict c -> c.Store.c_why
    | Propagator.Fixpoint -> (
        let after = Store.trail_length store in
        let entries =
          List.filteri (fun i _ -> i < after - before) (Store.trail_entries store)
        in
        match
          List.find_opt (fun (en : Store.entry) -> Var.equal en.var (var target)) entries
        with
        | Some en -> Store.explanation store en
        | None -> failwith (file ^ ": nothing was pruned from the target variable"))
  in
  let expl =
    match Explanation.force expl with
    | Explanation.Clause lits -> Explanation.clause (corrupt lits)
    | other -> other
  in
  let oc = open_out pbp in
  let w = Writer.create ~comments:true ~audit:true oc in
  Encoding.start_proof e w;
  let ctx = Justify.create ~writer:w ~encoding:e in
  let id = Justify.emit ctx expl in
  Writer.delete w id;
  Writer.conclusion w (Writer.Sat (Encoding.assignment_lits e sat));
  close_out oc;
  let text = read_file pbp in
  List.iter
    (fun line ->
      let ok = has_line text line in
      if not ok then Printf.printf "     (actual proof text)\n%s\n" text;
      check (Printf.sprintf "%s: emits `%s`" file line) ok)
    expect_lines;
  (opb, pbp)

(* x, y in [0,4], x <> y, with x pinned to 2 by two real model rows. 2 is interior to
   both declared domains, so the pruning is a genuine hole in y (lo and hi both stay
   put) and every literal of the clause is a real one -- the case a test that pinned x
   to 0 would have silently degenerated. *)
let build_ne_hole dir =
  build_ne_case dir ~file:"ne_hole"
    ~decls:[ ("x", 0, 4); ("y", 0, 4) ]
    ~terms:[ (1, 0); (-1, 1) ]
    ~rhs:0
    ~pre:[ (0, 2) ]
    ~target:1
    ~sat:[ ("x", 2); ("y", 3) ]
    ~expect_lines:
      [
        (* the claim (y <> 2) first, then the negation of its reason (x = 2):
           docs/DECISIONS.md D-0018's trace-line shape, literally *)
        "rup +1 ~y_ge_2 +1 y_ge_3 +1 ~x_ge_2 +1 x_ge_3 >= 1 ;";
      ]
    ()

(* The same model with the wrong value claimed: y <> 1 rather than y <> 2. It is not
   entailed (y = 1 is perfectly possible with x = 2), so veripb must reject it. This
   is what makes the positive case above mean something. *)
let build_ne_hole_wrong dir =
  build_ne_case dir ~file:"ne_hole_wrong"
    ~decls:[ ("x", 0, 4); ("y", 0, 4) ]
    ~terms:[ (1, 0); (-1, 1) ]
    ~rhs:0
    ~pre:[ (0, 2) ]
    ~target:1
    ~sat:[ ("x", 2); ("y", 3) ]
    ~expect_lines:[]
    ~corrupt:(fun _ ->
      Encoding.ne_clause_lits ~name:"y" ~decl_lo:0 ~decl_hi:4 1
      @ Encoding.ne_clause_lits ~name:"x" ~decl_lo:0 ~decl_hi:4 2)
    ()

(* The pruned value sits at the pruned variable's declared lo, so one half of its
   clause is the constant false and drops: the claim is the single literal y_ge_1.
   The reason variable is still pinned interior, so the reason keeps both halves. *)
let build_ne_bound dir =
  build_ne_case dir ~file:"ne_bound"
    ~decls:[ ("x", 0, 4); ("y", 0, 4) ]
    ~terms:[ (1, 0); (-1, 1) ]
    ~rhs:0
    ~pre:[ (0, 0) ]
    ~target:1
    ~sat:[ ("x", 0); ("y", 1) ]
    ~expect_lines:[ "rup +1 y_ge_1 +1 x_ge_1 >= 1 ;" ]
    ()

(* int_lin_ne with three variables and coefficients 2, 3, -1: 2a + 3b - c <> 5, with
   a = 2 and b = 1 established, so c <> 2 -- an interior hole in c, reached through a
   division by a coefficient that is neither 1 nor -1. *)
let build_lin_ne dir =
  build_ne_case dir ~file:"lin_ne"
    ~decls:[ ("a", 0, 4); ("b", 0, 4); ("c", 0, 4) ]
    ~terms:[ (2, 0); (3, 1); (-1, 2) ]
    ~rhs:5
    ~pre:[ (0, 2); (1, 1) ]
    ~target:2
    ~sat:[ ("a", 2); ("b", 1); ("c", 3) ]
    ~expect_lines:
      [ "rup +1 ~c_ge_2 +1 c_ge_3 +1 ~a_ge_2 +1 a_ge_3 +1 ~b_ge_1 +1 b_ge_2 >= 1 ;" ]
    ()

(* A conflict: x and y are both fixed to 2 by earlier propagation that this proof does
   not itself log, so the .opb is satisfiable and the [rup] line is checked on its own
   merits. The clause is the same function of the same data as a pruning's -- see
   ne.ml's header -- which is what this case exists to pin down. *)
let build_ne_conflict dir =
  build_ne_case dir ~file:"ne_conflict"
    ~decls:[ ("x", 0, 4); ("y", 0, 4) ]
    ~terms:[ (1, 0); (-1, 1) ]
    ~rhs:0
    ~pre:[ (0, 2); (1, 2) ]
    ~target:0
    ~sat:[ ("x", 1); ("y", 0) ]
    ~expect_lines:[ "rup +1 ~x_ge_2 +1 x_ge_3 +1 ~y_ge_2 +1 y_ge_3 >= 1 ;" ]
    ()

(* The factless controls, one per disequality propagator. D-0032: without these the
   test cannot distinguish a justification that works from a model that makes any
   justification work.

   Each emits the CLAIM ALONE -- `y <> 2`, unconditionally -- which is exactly what a
   propagator that pruned without recording the facts it read would write. It is false
   of the model (x is free, so y = 2 is perfectly possible), so veripb must reject it.
   Under the old scene, where `x = 2` was pinned by `.opb` rows, both of these are
   ACCEPTED: measured, not predicted. *)
let build_ne_factless dir =
  build_ne_case dir ~file:"ne_factless"
    ~decls:[ ("x", 0, 4); ("y", 0, 4) ]
    ~terms:[ (1, 0); (-1, 1) ]
    ~rhs:0
    ~pre:[ (0, 2) ]
    ~target:1
    ~sat:[ ("x", 2); ("y", 3) ]
    ~expect_lines:[ "rup +1 ~y_ge_2 +1 y_ge_3 >= 1 ;" ]
    ~corrupt:(fun _ -> Encoding.ne_clause_lits ~name:"y" ~decl_lo:0 ~decl_hi:4 2)
    ()

let build_lin_ne_factless dir =
  build_ne_case dir ~file:"lin_ne_factless"
    ~decls:[ ("a", 0, 4); ("b", 0, 4); ("c", 0, 4) ]
    ~terms:[ (2, 0); (3, 1); (-1, 2) ]
    ~rhs:5
    ~pre:[ (0, 2); (1, 1) ]
    ~target:2
    ~sat:[ ("a", 2); ("b", 1); ("c", 3) ]
    ~expect_lines:[ "rup +1 ~c_ge_2 +1 c_ge_3 >= 1 ;" ]
    ~corrupt:(fun _ -> Encoding.ne_clause_lits ~name:"c" ~decl_lo:0 ~decl_hi:4 2)
    ()

(* ---------------------------------------------- the selector Boolean, both ways

   [conclusion SAT] hands veripb the model variables' literals only; the disequality's
   own auxiliary Boolean is left for the checker's unit propagation to fill in from
   whichever of the two rows is tight. That is the one part of this encoding that is
   not obviously local, so it is tested on *both* sides of c and with *two*
   disequalities live at once -- a run that only ever landed below c would leave row
   A's half of the mechanism unexercised, which is precisely the shape of the five
   findings this file's other headers keep citing.

   The rejected case is the point of the exercise: it shows the .opb really does
   forbid x = y, i.e. that the pair of rows is the disequality and not merely
   satisfiable alongside it. *)

let build_selector dir ~file ~sat =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:4;
  Encoding.declare_int e "y" ~lo:0 ~hi:4;
  ignore (Encoding.add_int_lin_ne e [ (1, "x"); (-1, "y") ] 0);
  ignore (Encoding.add_int_lin_ne e [ (1, "x"); (1, "y") ] 4);
  let opb = Filename.concat dir (file ^ ".opb") in
  let pbp = Filename.concat dir (file ^ ".pbp") in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ file ] e oc;
  close_out oc;
  let oc = open_out pbp in
  let w = Writer.create ~audit:true oc in
  Encoding.start_proof e w;
  Writer.conclusion w (Writer.Sat (Encoding.assignment_lits e sat));
  close_out oc;
  (opb, pbp)

let test_ne_selector () =
  run_veripb ~name:"int_ne rows: a solution above c (row A forces the selector)"
    ~build:(fun dir -> build_selector dir ~file:"sel_hi" ~sat:[ ("x", 3); ("y", 0) ]);
  run_veripb ~name:"int_ne rows: a solution below c (row B forces the selector)"
    ~build:(fun dir -> build_selector dir ~file:"sel_lo" ~sat:[ ("x", 0); ("y", 3) ]);
  run_veripb_rejects ~name:"int_ne rows: x = y is not a solution of the .opb"
    ~build:(fun dir -> build_selector dir ~file:"sel_eq" ~sat:[ ("x", 2); ("y", 2) ]);
  run_veripb_rejects ~name:"int_ne rows: x + y = 4 is not a solution of the .opb"
    ~build:(fun dir -> build_selector dir ~file:"sel_sum" ~sat:[ ("x", 1); ("y", 3) ])

(* ============================================================================
   test/models/ne_sat.fzn, end to end.

   The FlatZinc front end still *rejects* int_ne (lib/flatzinc/compile.ml's
   [reject_ne], called at the [Model.Int_ne] arm of [compile]), so the CLI cannot yet
   run this model and test/models/PENDING still lists it. Both of those files belong
   to another session this round. What can be checked from here is everything below
   that line: that the model's own store, encoding, propagators, search, proof and
   veripb all agree once the two constraints are posted the way [Compile] posts them.

   ne_sat.fzn is:

       var 1..2: x;  var 1..2: y;
       constraint int_ne(x, y);
       constraint int_lt(x, y);
       solve satisfy;

   which is worth noting is *not* by itself a test of int_ne: int_lt alone fixes
   x = 1, y = 2, so the disequality never prunes anything. That is exactly the shape
   of instance D-0009/D-0010/D-0017 were invisible on, so the same wiring is run a
   second time below over a model where int_ne is the only thing that can make
   progress. Both are checked by veripb. *)

let pack_ne ~id (p : Ne.t) =
  Propagator.pack ~id (module Ne.Int_ne : Propagator.S with type t = Ne.t) p

let pack_linear ~id (p : Linear.t) =
  Propagator.pack ~id (module Linear : Propagator.S with type t = Linear.t) p

(* [decls] and the two constraints, wired exactly as lib/flatzinc/compile.ml would:
   every variable declared into store and encoding in the same order, each row posted
   to the .opb before any propagator runs, each Linear instance given its own row id
   (D-0011). [check] is the independent re-verification I-S1 demands -- a hand-written
   one, as Search.solve's own header says a caller without a Model.t must supply. *)
let build_search_case dir ~file ~decls ~ne_terms ~ne_rhs ~lt_terms ~lt_rhs ~check_sol =
  let e = Encoding.create () in
  List.iter (fun (n, lo, hi) -> Encoding.declare_int e n ~lo ~hi) decls;
  let name_of i =
    let n, _, _ = List.nth decls i in
    n
  in
  ignore
    (Encoding.add_int_lin_ne e (List.map (fun (a, i) -> (a, name_of i)) ne_terms) ne_rhs);
  let lt_row =
    Encoding.add_int_lin_le e (List.map (fun (a, i) -> (a, name_of i)) lt_terms) lt_rhs
  in
  let opb = Filename.concat dir (file ^ ".opb") in
  let pbp = Filename.concat dir (file ^ ".pbp") in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ file ] e oc;
  close_out oc;
  let store = mk_store decls in
  let ne = Ne.make store (List.map (fun (a, i) -> (a, var i)) ne_terms) ne_rhs in
  let lt =
    Linear.make ~row_id:lt_row store (List.map (fun (a, i) -> (a, var i)) lt_terms) lt_rhs
  in
  let engine = Engine.create [ pack_ne ~id:0 ne; pack_linear ~id:1 lt ] in
  let oc = open_out pbp in
  let w = Writer.create ~comments:true ~audit:true oc in
  Encoding.start_proof e w;
  let ctx = Justify.create ~writer:w ~encoding:e in
  let outcome = Search.solve ~engine ~store ~ctx ~check:check_sol () in
  close_out oc;
  (outcome, store, opb, pbp)

let sat_values store (asn : Search.assignment) =
  List.map (fun (v, value) -> (Store.name store v, value)) asn

let build_ne_sat dir =
  let decls = [ ("x", 1, 2); ("y", 1, 2) ] in
  let check_sol asn =
    let get i = List.assoc (var i) asn in
    get 0 <> get 1 && get 0 < get 1
  in
  let outcome, store, opb, pbp =
    build_search_case dir ~file:"ne_sat" ~decls
      ~ne_terms:[ (1, 0); (-1, 1) ]
      ~ne_rhs:0
      ~lt_terms:[ (1, 0); (-1, 1) ]
      ~lt_rhs:(-1) ~check_sol
  in
  (match outcome with
  | Search.Sat asn ->
      check "ne_sat: the solver finds x = 1, y = 2"
        (sat_values store asn = [ ("x", 1); ("y", 2) ])
  | Search.Unsat -> check "ne_sat: the solver finds a solution" false);
  (opb, pbp)

(* The same wiring over a model int_lt cannot finish on its own: x, y in [0, 4] with
   x <> y and x < y + 0 ... would still be int_lt's job, so instead the linear row is
   x + y <= 5 and the disequality is 2x - y <> 0. Nothing here is fixed by bounds
   reasoning alone; the search must branch, int_ne must prune inside a branch, and the
   proof must survive it. This is the "one step past" instance: ne_sat above would
   have verified even if int_ne did nothing at all. *)
let build_ne_search dir =
  let decls = [ ("x", 0, 4); ("y", 0, 4) ] in
  let check_sol asn =
    let get i = List.assoc (var i) asn in
    (2 * get 0) - get 1 <> 0 && get 0 + get 1 <= 5
  in
  let outcome, store, opb, pbp =
    build_search_case dir ~file:"ne_search" ~decls
      ~ne_terms:[ (2, 0); (-1, 1) ]
      ~ne_rhs:0
      ~lt_terms:[ (1, 0); (1, 1) ]
      ~lt_rhs:5 ~check_sol
  in
  (match outcome with
  | Search.Sat asn ->
      let values = sat_values store asn in
      check
        (Printf.sprintf "ne_search: the solution %s satisfies both constraints"
           (String.concat " "
              (List.map (fun (n, v) -> Printf.sprintf "%s=%d" n v) values)))
        (check_sol asn)
  | Search.Unsat -> check "ne_search: the solver finds a solution" false);
  (* ... and int_ne is what made that true. Without it the same search takes the same
     first-fail, indomain_min path and lands on x = 0, y = 0, which the independent
     re-check (I-S1) rejects as [Unsound_solution]. Asserting this is the difference
     between "the run verified" and "the run verified *because* the disequality did
     something": every earlier finding in this project (D-0009, D-0010, D-0012,
     D-0017, D-0018) was invisible on an instance where the feature under test never
     had to act. *)
  let without_ne_is_wrong =
    let store = mk_store decls in
    let lt = Linear.make ~row_id:1 store [ (1, var 0); (1, var 1) ] 5 in
    let engine = Engine.create [ pack_linear ~id:0 lt ] in
    let scratch = Filename.concat dir "ne_search_without_ne.pbp" in
    let oc = open_out scratch in
    let w = Writer.create ~audit:false oc in
    let e2 = Encoding.create () in
    List.iter (fun (n, lo, hi) -> Encoding.declare_int e2 n ~lo ~hi) decls;
    ignore (Encoding.add_int_lin_le e2 [ (1, "x"); (1, "y") ] 5);
    Encoding.start_proof e2 w;
    let ctx = Justify.create ~writer:w ~encoding:e2 in
    let r =
      match Search.solve ~engine ~store ~ctx ~check:check_sol () with
      | _ -> false
      | exception Search.Unsound_solution _ -> true
    in
    close_out oc;
    (try Sys.remove scratch with _ -> ());
    r
  in
  check "ne_search: dropping int_ne makes the same search return a wrong answer"
    without_ne_is_wrong;
  (opb, pbp)

(* =============================================== M1-T23: overflow, and the cap

   Three things are checked here, and they are three different claims:

   1. [Checked] computes what the unchecked operators compute wherever the result
      fits, and raises wherever it does not. Without the first half the fix would be
      a behaviour change dressed as a soundness fix.

   2. The .opb row for an overflowing constraint is expanded from the SAME wrapped
      arithmetic the propagator's slack uses. This is the half of the gap that makes
      it a soundness bug rather than a rejected proof, and it is pinned as an
      assertion on the bytes lib/proof/encoding.ml emits -- which this task may not
      change, and did not need to. The pin stays true after the fix, because the fix
      is not in [Encoding]: it is that [Compile] never hands [Encoding] such a row.

   3. The propagators raise instead of wrapping, and [Compile] refuses the model
      before either can happen.

   The instance all three are built around is the one that demonstrated the gap:

       array [1..1] of int: c = [-2305843009213693952];    % -2^61
       var 3..4: x;
       constraint int_lin_le(c, [x], 0);
       constraint int_le(x, 3);

   x = 3 satisfies it (-2^61 * 3 = -6917529027641081856 <= 0), and before M1-T23
   baguette printed =====UNSATISFIABLE===== and emitted a proof veripb accepted.

   ---------------------------------------------------------------------------
   A ceiling on what any test here may DECLARE, and why
   ---------------------------------------------------------------------------

   **No test below declares a domain more than a few values wide.** Overflow is
   driven entirely through large COEFFICIENTS against modest domains, which is where
   the wrapped product actually comes from (`a_i * bound_i`), and through a bound
   fixed at min_int (a width of ZERO). That is a hard rule, not a stylistic one:
   docs/DECISIONS.md **D-0028** measures that a justification is Theta(declared
   width) per other term per pruning -- two variables declared 0..999999 and one row
   produce a 156 MB .opb and a single 29.8 MB `pol` line having pruned nothing -- and
   [Order_reason.weaken_declared] and [lower_bound_terms], which this file calls
   directly, are exactly the functions that build it. A test that declared a domain
   near max_int would not run slowly; it would try to allocate a literal per value
   and exhaust the machine. One such run did, mid-M1-T23, and took 14.9 GB before it
   was killed.

   The ONE place a wide bound appears below is [test_compile_cap]'s
   `var 0..4000000000000000000`, and it is safe for a specific, checked reason:
   lib/flatzinc/compile.ml runs the declared-bound check BEFORE [Store.create] and
   before [Encoding.declare_int], so the model is refused with a diagnostic and
   nothing ever enumerates it. That is the only shape a wide declared domain may have
   in this file -- a rejection, never a propagation. *)

let raises_overflow f =
  try
    ignore (f () : int);
    false
  with Checked.Overflow _ -> true

let raises_overflow_unit f =
  try
    ignore (f ());
    false
  with Checked.Overflow _ -> true

let test_checked_ops () =
  (* Agreement, over a grid where nothing can overflow: a checked operator that
     quietly rounded or mis-signed would be a worse bug than the one being fixed. *)
  let agree_add = ref true and agree_sub = ref true and agree_mul = ref true in
  for a = -40 to 40 do
    for b = -40 to 40 do
      if Checked.add a b <> a + b then agree_add := false;
      if Checked.sub a b <> a - b then agree_sub := false;
      if Checked.mul a b <> a * b then agree_mul := false
    done
  done;
  check "checked: add agrees with (+) wherever the result fits" !agree_add;
  check "checked: sub agrees with (-) wherever the result fits" !agree_sub;
  check "checked: mul agrees with ( * ) wherever the result fits" !agree_mul;
  (* The rounding, against the mathematical definition rather than against the
     implementation it replaced -- floats are exact at this size. This is the trap
     lib/core/prop/linear.ml's old header warns about: [Stdlib.(/)] truncates toward
     zero, which is neither floor nor ceil once a sign is negative. *)
  let agree_floor = ref true and agree_ceil = ref true in
  for a = -40 to 40 do
    for b = -12 to 12 do
      if b <> 0 then (
        let q = float_of_int a /. float_of_int b in
        if Checked.floordiv a b <> int_of_float (Float.floor q) then agree_floor := false;
        if Checked.ceildiv a b <> int_of_float (Float.ceil q) then agree_ceil := false)
    done
  done;
  check "checked: floordiv is the floor of the exact quotient, at every sign" !agree_floor;
  check "checked: ceildiv is the ceiling of the exact quotient, at every sign" !agree_ceil;
  (* ceildiv no longer routes through -(floordiv (-a) b): that negation has no answer
     for a = min_int, which is a second wrap on the path the fix is about. *)
  check "checked: ceildiv min_int 1 is min_int, where -(floordiv (-a) b) would wrap"
    (Checked.ceildiv min_int 1 = min_int);
  (* The boundary. Each of these is a place lib/ used to wrap silently. *)
  check "checked: max_int + 1 raises" (raises_overflow (fun () -> Checked.add max_int 1));
  check "checked: min_int - 1 raises" (raises_overflow (fun () -> Checked.sub min_int 1));
  check "checked: max_int + min_int does NOT raise (it fits, at -1)"
    (Checked.add max_int min_int = -1);
  check "checked: max_int * 2 raises" (raises_overflow (fun () -> Checked.mul max_int 2));
  check "checked: min_int * -1 raises"
    (raises_overflow (fun () -> Checked.mul min_int (-1)));
  check "checked: 2^61 * 4 raises (the demonstrating product)"
    (raises_overflow (fun () -> Checked.mul (-2305843009213693952) 4));
  check "checked: 2^30 * 2^30 does not raise (the fast path's own boundary)"
    (Checked.mul 0x3FFFFFFF 0x3FFFFFFF = 0x3FFFFFFF * 0x3FFFFFFF);
  check "checked: neg min_int raises" (raises_overflow (fun () -> Checked.neg min_int));
  check "checked: abs min_int raises" (raises_overflow (fun () -> Checked.abs min_int));
  check "checked: floordiv min_int (-1) raises"
    (raises_overflow (fun () -> Checked.floordiv min_int (-1)));
  check "checked: rem min_int (-1) answers 0 rather than trusting Stdlib.mod"
    (Checked.rem min_int (-1) = 0);
  check "checked: sum raises on a partial sum that leaves the range"
    (raises_overflow (fun () -> Checked.sum [ max_int; 1; -1 ]));
  (* The cap's own arithmetic, asserted rather than trusted: lib/core/checked.ml's
     header claims everything derived from a row of magnitude M is bounded by 9M + 6,
     so a limit of max_int / 16 has to leave that inside the range. If someone raises
     [limit], this is the check that goes red. *)
  check "checked: 16 * limit fits, so the stated envelope is inside the range"
    (Checked.limit > 0 && Checked.limit <= max_int / 16);
  check "checked: 9 * limit + 6 fits, which is the envelope the header derives"
    (raises_overflow (fun () -> Checked.add (Checked.mul 9 Checked.limit) 6) = false);
  check "checked: row_magnitude is |rhs| + sum |a| * max(|lo|,|hi|)"
    (Checked.row_magnitude [ (3, -5, 2); (-2, 0, 7) ] (-4) = Some (4 + (3 * 5) + (2 * 7)));
  check "checked: row_magnitude reports None rather than a wrapped number"
    (Checked.row_magnitude [ (max_int, 0, 2) ] 0 = None);
  check "checked: row_fits refuses a row it cannot even measure"
    (not (Checked.row_fits [ (max_int, 0, 2) ] 0));
  check "checked: bound_fits refuses min_int, which has no absolute value"
    (not (Checked.bound_fits min_int))

(* The .opb half of the gap. [Encoding] is read-only for this task and is unchanged:
   what is asserted is that it still folds sum_i a_i * lo_i with native arithmetic, so
   a row that reached it with an overflowing constant would come out stating a
   different constraint from the one in the model -- and the propagator, wrapping the
   identical product, would agree with it. That agreement is why veripb could not see
   the bug, and it is why the fix has to be a cap in lib/flatzinc/compile.ml rather
   than a check inside a propagator. *)
let test_opb_row_wraps_identically () =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:3 ~hi:4;
  let row = Encoding.expand_int_lin_le e [ (-2305843009213693952, "x") ] 0 in
  let text = Opb.constr_to_string row in
  (* The true row is vacuous: -2^61 * x <= 0 holds for every x >= 0, so with x in 3..4
     every assignment satisfies it. What comes out instead FORCES x_ge_4, because the
     folded constant -2^61 * 3 wrapped to +2^61. *)
  check "opb: the row for an overflowing constraint is itself wrapped"
    (text = "+2305843009213693952 x_ge_4 >= 2305843009213693952 ;");
  check "opb: and the propagator wraps the same product the same way"
    (-2305843009213693952 * 3 = 2305843009213693952)

(* The propagators refuse to wrap. Both are built directly, which is the one caller
   the compile-time cap does not cover -- and is exactly why the runtime policy is to
   raise rather than to decline quietly. *)
let test_propagators_raise_on_overflow () =
  let store = mk_store [ ("x", 3, 4) ] in
  let lin = Linear.make ~row_id:1 store [ (-2305843009213693952, var 0) ] 0 in
  check "linear: a term whose product overflows raises instead of conflicting"
    (raises_overflow_unit (fun () -> Linear.propagate lin store));
  (* Products that each fit, and a sum that does not: the second way a row's slack can
     be wrong, and the one a per-product check alone would miss. *)
  let big = (max_int / 2) + 1 in
  let store2 = mk_store [ ("a", big, big); ("b", big, big); ("c", 0, 1) ] in
  let lin2 = Linear.make ~row_id:1 store2 [ (1, var 0); (1, var 1); (1, var 2) ] 0 in
  check "linear: products that fit but a sum that does not also raises"
    (raises_overflow_unit (fun () -> Linear.propagate lin2 store2));
  (* int_ne's coefficients are 1 and -1, so its only overflowing product is -1 * y
     with y at min_int -- which is also the only input Stdlib.mod is not guaranteed to
     survive further down. *)
  let store3 = mk_store [ ("x", 0, 2); ("y", min_int, min_int) ] in
  let ne = Ne.Int_ne.make store3 (var 0) (var 1) in
  check "int_ne: negating a fixed value at min_int raises instead of wrapping"
    (raises_overflow_unit (fun () -> Ne.propagate ne store3));
  (* int_lin_ne, sum side: every product fits, the running total does not. *)
  let store4 = mk_store [ ("p", big, big); ("q", big, big); ("r", 0, 3) ] in
  let lne = Ne.make store4 [ (1, var 0); (1, var 1); (1, var 2) ] 0 in
  check "int_lin_ne: a fixed-term sum that leaves the range raises"
    (raises_overflow_unit (fun () -> Ne.propagate lne store4))

(* ------------------------------------------------- the cap, at the model's edge *)

let compile_src src = Compile.compile (Flatzinc.Builder.of_string ~file:"test" src)

let contains_sub ~needle haystack =
  let n = String.length needle and h = String.length haystack in
  n = 0
  ||
  let found = ref false in
  for i = 0 to h - n do
    if (not !found) && String.equal (String.sub haystack i n) needle then found := true
  done;
  !found

let expect_capped name ~needles src =
  match compile_src src with
  | exception Flatzinc.Error.Error e ->
      let msg = Flatzinc.Error.to_string e in
      let missing = List.filter (fun n -> not (contains_sub ~needle:n msg)) needles in
      if missing = [] then check name true
      else (
        check name false;
        Printf.printf "       message does not mention %s\n       message: %s\n"
          (String.concat ", " missing) msg)
  | exception exn ->
      check name false;
      Printf.printf "       raised the wrong exception: %s\n" (Printexc.to_string exn)
  | _ ->
      check name false;
      Printf.printf "       compiled successfully -- the model was accepted\n"

let expect_compiles name src =
  match compile_src src with
  | exception exn ->
      check name false;
      Printf.printf "       rejected: %s\n" (Printexc.to_string exn)
  | _ -> check name true

let test_compile_cap () =
  (* The demonstration, as a model. Before M1-T23 this printed
     =====UNSATISFIABLE===== with a proof veripb accepted; x = 3 satisfies it. *)
  expect_capped
    "cap: the model that shipped a wrong answer with a verified proof is refused"
    ~needles:[ "arithmetic limit"; "288230376151711743"; "wraps silently" ]
    "array [1..1] of int: c = [-2305843009213693952];\n\
     var 3..4: x;\n\
     constraint int_lin_le(c, [x], 0);\n\
     constraint int_le(x, 3);\n\
     solve satisfy;\n";
  (* The declaration half of the cap. The row here is small; what is too large is the
     domain itself, and the diagnostic has to name the variable. *)
  expect_capped "cap: a declared bound past the limit is refused at its declaration"
    ~needles:[ "`huge`"; "arithmetic limit"; "288230376151711743" ]
    "var 0..4000000000000000000: huge;\nconstraint int_le(huge, 3);\nsolve satisfy;\n";
  (* A disequality is capped on the same magnitude, even though its .opb rows are the
     pair with the big-M constant -- which is what the factor of 16 is sized for. *)
  expect_capped "cap: a disequality past the limit is refused too"
    ~needles:[ "disequality"; "arithmetic limit" ]
    "array [1..2] of int: c = [2305843009213693952, 1];\n\
     var 0..3: x;\n\
     var 0..3: y;\n\
     constraint int_lin_ne(c, [x, y], 1);\n\
     solve satisfy;\n";
  (* Coefficients so large that the magnitude cannot itself be computed still produce
     a diagnostic rather than an escaping Checked.Overflow. *)
  expect_capped "cap: a magnitude that does not itself fit still produces a diagnostic"
    ~needles:[ "arithmetic limit" ]
    (Printf.sprintf
       "array [1..2] of int: c = [%d, %d];\n\
        var 0..3: x;\n\
        var 0..3: y;\n\
        constraint int_lin_le(c, [x, y], 0);\n\
        solve satisfy;\n"
       max_int max_int);
  (* And the other direction, which is the half that stops the cap from being a way to
     reject anything awkward: a row whose magnitude sits just under the limit compiles,
     and its arithmetic is exact. 4 * 57646075230342348 + 4 = 230584300921369396, which
     is 79.9% of the limit. *)
  expect_compiles "cap: a row just under the limit still compiles"
    "array [1..4] of int: c = [57646075230342348, 57646075230342348, 57646075230342348, \
     57646075230342348];\n\
     var 0..1: a;\n\
     var 0..1: b;\n\
     var 0..1: d;\n\
     var 0..1: e;\n\
     constraint int_lin_le(c, [a, b, d, e], 4);\n\
     solve satisfy;\n"

(* ======================================================== M2-T1 / M2-T2: the Booleans

   The six Boolean builtins arrived on a branch that built, passed 1051 checks and 20
   models, and ran NONE of them: every bool-mentioning check in the suite predated the
   work, and there was no bool_clause / array_bool_or / array_bool_and / bool2int /
   bool_not test or model anywhere in the tree. The suite was green because the new code
   never executed. D-0030 names the rule that violates -- a test is not evidence until
   something has been seen to break it -- so every check below was watched going red
   against a deliberately broken propagator before it was committed.

   The sections mirror the integer ones above:

     1. the propagator's own behaviour: I-P1 by brute force, I-P3 checking, I-P2/I-P3
        idempotence -- and, for bool_clause, the *stronger* claim its header makes.
        [Propagator.Domain] is not a free upgrade over [Bounds]: SPEC 3.2 makes the
        declared level the bound on what an explanation may claim, so a propagator that
        declares DOMAIN and is only checked for "no supported value removed" has its
        declaration tested by nothing at all. [check_clause_consistency] therefore
        checks both directions -- no supported value removed AND no unsupported value
        left behind -- and the second half is what catches a clause that quietly stops
        unit-propagating.

     2. the emitted text: the .opb rows compile.ml posts for each decomposition, and the
        reasons the propagators build, both verbatim.

     3. veripb (I-X1), including negative controls it must REJECT. [rup] is the one rule
        that searches for its own justification, so a test that only ever feeds it true
        clauses cannot tell a correct explanation from a lucky one.

     4. D-0030's own check, on the two UNSAT models: that no single .opb row refutes
        them. That is the defect which made `root_unsat` unable to test the thing it was
        chosen to test, and it is checked here mechanically rather than by reading --
        with a control, because a check for a defect is itself only evidence once it has
        been seen to fire. *)

(* ------------------------------------------------------- bool_clause: brute force *)

(* A clause as (variable index, polarity) pairs, evaluated against an assignment --
   written from the definition of a disjunction and not by calling anything in
   lib/core/prop/, so that it is a second reading rather than the same one twice. *)
let clause_holds lits assignment =
  List.exists
    (fun (i, positive) ->
      let v = List.nth assignment i in
      if positive then v = 1 else v = 0)
    lits

let mk_bool_clause lits store =
  Bool_clause.make store (List.map (fun (i, p) -> (var i, p)) lits)

(* Both halves of DOMAIN consistency (SPEC 3.2), which is what bool_clause declares.
   One [propagate] call reaches this constraint's fixpoint: the only inference a clause
   has is forcing its last open literal, and doing that satisfies the clause, so there
   is never a second round. Asserted rather than assumed -- [test_bool_clause_
   idempotence] re-runs and requires nothing to move. *)
let check_clause_consistency name lits n =
  let ranges = List.init n (fun _ -> (0, 1)) in
  let bounds = List.mapi (fun i (lo, hi) -> (Printf.sprintf "b%d" i, lo, hi)) ranges in
  let assignments = cartesian ranges in
  let solutions = List.filter (clause_holds lits) assignments in
  let has_support i v = List.exists (fun sol -> List.nth sol i = v) solutions in
  let store = mk_store bounds in
  let prop = mk_bool_clause lits store in
  match Bool_clause.propagate prop store with
  | Propagator.Conflict _ ->
      check
        (Printf.sprintf "bool_clause %s: conflict only when truly unsat" name)
        (solutions = [])
  | Propagator.Fixpoint ->
      let sound = ref true and complete = ref true in
      List.iteri
        (fun i _ ->
          let d = Store.get store (var i) in
          for v = 0 to 1 do
            if has_support i v && not (Domain.mem d v) then sound := false;
            (* The DOMAIN half. A value with no support anywhere in the clause's
               solution set must be gone; for a clause that is precisely "the last open
               literal has been forced". *)
            if (not (has_support i v)) && Domain.mem d v then complete := false
          done)
        bounds;
      check (Printf.sprintf "bool_clause %s: I-P1 no supported value removed" name) !sound;
      check
        (Printf.sprintf "bool_clause %s: DOMAIN, no unsupported value left behind" name)
        !complete

let test_bool_clause_consistency () =
  (* Shapes, not repetitions: all-positive, all-negative, mixed, a unit of each
     polarity, a clause with a variable it does not mention (so the harness sees an
     untouched column), the tautology, the duplicate, and the empty clause. *)
  check_clause_consistency "(b0 \\/ b1 \\/ b2)" [ (0, true); (1, true); (2, true) ] 3;
  check_clause_consistency "(~b0 \\/ ~b1 \\/ ~b2)"
    [ (0, false); (1, false); (2, false) ]
    3;
  check_clause_consistency "(b0 \\/ ~b1 \\/ b2)" [ (0, true); (1, false); (2, true) ] 3;
  check_clause_consistency "(~b0 \\/ b1)" [ (0, false); (1, true) ] 2;
  check_clause_consistency "unit (b0)" [ (0, true) ] 1;
  check_clause_consistency "unit (~b0)" [ (0, false) ] 1;
  check_clause_consistency "(b0 \\/ b1) with an unmentioned b2" [ (0, true); (1, true) ] 3;
  (* A variable at both polarities: the clause is a tautology, the propagator must never
     fire, and [Bool_clause.make]'s header says that is achieved by the ordinary path
     rather than by a special case. *)
  check_clause_consistency "tautology (b0 \\/ ~b0)" [ (0, true); (0, false) ] 1;
  (* The same literal twice is merged by [make], so this clause is a unit and forces its
     variable. Without the merge it would read as two open literals and infer nothing --
     sound, but strictly weaker, which is what the DOMAIN half above catches. *)
  check_clause_consistency "duplicate (b0 \\/ b0)" [ (0, true); (0, true) ] 1;
  (* The empty clause is false and is a legal value here: compile.ml reaches it from
     `bool_clause([], [])`. *)
  check_clause_consistency "the empty clause" [] 1

(* ------------------------------------------------------------ bool_clause: I-P3 *)

let test_bool_clause_checking () =
  (* Every variable fixed: Conflict iff the assignment violates the clause, and nothing
     else, there being nothing left to prune. [make] runs before the fixing so the
     propagator's frozen declared bounds are the wide ones (D-0010). *)
  let run name lits n values expect_conflict =
    let bounds = List.init n (fun i -> (Printf.sprintf "b%d" i, 0, 1)) in
    let store = mk_store bounds in
    let prop = mk_bool_clause lits store in
    List.iteri
      (fun i v ->
        match Store.fix store (var i) v placeholder_pruning with
        | Store.Conflict _ -> failwith "test_bool_clause_checking: setup conflicted"
        | _ -> ())
      values;
    let got =
      match Bool_clause.propagate prop store with
      | Propagator.Conflict _ -> true
      | Propagator.Fixpoint -> false
    in
    check (Printf.sprintf "bool_clause I-P3 checking: %s" name) (got = expect_conflict)
  in
  let c3 = [ (0, true); (1, false); (2, true) ] in
  (* (b0 \/ ~b1 \/ b2) is violated by exactly one of the eight assignments. *)
  run "(b0 \\/ ~b1 \\/ b2) at 0,1,0 -- the only violating point" c3 3 [ 0; 1; 0 ] true;
  run "(b0 \\/ ~b1 \\/ b2) at 0,1,1" c3 3 [ 0; 1; 1 ] false;
  run "(b0 \\/ ~b1 \\/ b2) at 1,1,0" c3 3 [ 1; 1; 0 ] false;
  run "(b0 \\/ ~b1 \\/ b2) at 0,0,0" c3 3 [ 0; 0; 0 ] false;
  run "(b0 \\/ ~b1 \\/ b2) at 1,1,1" c3 3 [ 1; 1; 1 ] false;
  run "the empty clause is violated at b0 = 0" [] 1 [ 0 ] true;
  run "the empty clause is violated at b0 = 1" [] 1 [ 1 ] true

(* ------------------------------------------------------ bool_clause: I-P2 / I-P3 *)

let test_bool_clause_idempotence () =
  let run name lits n pre =
    let bounds = List.init n (fun i -> (Printf.sprintf "b%d" i, 0, 1)) in
    let store = mk_store bounds in
    let prop = mk_bool_clause lits store in
    List.iter
      (fun (i, v) ->
        match Store.fix store (var i) v placeholder_pruning with
        | Store.Conflict _ -> failwith "test_bool_clause_idempotence: setup conflicted"
        | _ -> ())
      pre;
    match Bool_clause.propagate prop store with
    | Propagator.Conflict _ ->
        check (Printf.sprintf "bool_clause idempotence: %s (conflict)" name) true
    | Propagator.Fixpoint -> (
        let snap = Store.snapshot store in
        match Bool_clause.propagate prop store with
        | Propagator.Conflict _ ->
            check
              (Printf.sprintf
                 "bool_clause idempotence: %s -- the second run conflicted where the \
                  first did not"
                 name)
              false
        | Propagator.Fixpoint ->
            check
              (Printf.sprintf "bool_clause I-P2/I-P3: %s, second run moves nothing" name)
              (Store.same_domains store snap))
  in
  let c3 = [ (0, true); (1, false); (2, true) ] in
  run "nothing fixed (two open, no inference)" c3 3 [];
  run "one literal false (still two open)" c3 3 [ (0, 0) ];
  run "two literals false (the unit case)" c3 3 [ (0, 0); (1, 1) ];
  run "already satisfied" c3 3 [ (0, 1) ];
  run "duplicate literal, unit on the first run" [ (0, true); (0, true) ] 1 []

(* ---------------------------------------- bool_clause: the unit push and its reason *)

let expl_lits e =
  match Explanation.force e with
  | Explanation.Clause ls -> Some (String.concat " " (List.map Lit.to_string ls))
  | _ -> None

let test_bool_clause_unit_push () =
  (* (a \/ ~b \/ c) with a false and b true forces c true, and the reason is the whole
     clause -- which for a clause is both the nogood and the implication, because the
     assignment that falsifies the forced literal is the assignment that conflicts.
     lib/core/prop/bool_clause.ml's header states that identity; this is the check. *)
  let store = mk_store [ ("a", 0, 1); ("b", 0, 1); ("c", 0, 1) ] in
  let prop = mk_bool_clause [ (0, true); (1, false); (2, true) ] store in
  ignore (Store.set_hi store (var 0) 0 placeholder_pruning);
  ignore (Store.set_lo store (var 1) 1 placeholder_pruning);
  let before = Store.trail_length store in
  (match Bool_clause.propagate prop store with
  | Propagator.Conflict _ -> check "bool_clause: the unit push happened" false
  | Propagator.Fixpoint ->
      check "bool_clause: the unit push forced c true"
        (Domain.lo (Store.get store (var 2)) = 1));
  check "bool_clause: the unit push wrote exactly one trail entry"
    (Store.trail_length store - before = 1);
  let entry = List.hd (Store.trail_entries store) in
  let expl = Store.explanation store entry in
  check "bool_clause: the reason is the clause itself, in declaration order"
    (expl_lits expl = Some "a_ge_1 ~b_ge_1 c_ge_1");
  check "bool_clause: literals are the order-encoding spelling of D-0007"
    (String.concat " " (List.map Lit.to_string (Bool_clause.literals prop))
    = "a_ge_1 ~b_ge_1 c_ge_1")

let test_bool_clause_conflict_reason () =
  (* Every literal false: the clause is violated and the conflict's reason is the same
     clause. Sharing one [Explanation.t] between prunings and conflicts is deliberate
     (the header says why), so this checks the conflict path reports it too. *)
  let store = mk_store [ ("a", 0, 1); ("b", 0, 1); ("c", 0, 1) ] in
  let prop = mk_bool_clause [ (0, true); (1, false); (2, true) ] store in
  ignore (Store.set_hi store (var 0) 0 placeholder_pruning);
  ignore (Store.set_lo store (var 1) 1 placeholder_pruning);
  ignore (Store.set_hi store (var 2) 0 placeholder_pruning);
  match Bool_clause.propagate prop store with
  | Propagator.Fixpoint -> check "bool_clause: an all-false clause conflicts" false
  | Propagator.Conflict c ->
      let e = c.Store.c_why in
      check "bool_clause: an all-false clause conflicts" true;
      check "bool_clause: the conflict's reason is the clause"
        (expl_lits e = Some "a_ge_1 ~b_ge_1 c_ge_1")

let test_bool_clause_empty_conflict () =
  let store = mk_store [ ("a", 0, 1) ] in
  let prop = mk_bool_clause [] store in
  match Bool_clause.propagate prop store with
  | Propagator.Fixpoint -> check "bool_clause: the empty clause conflicts at once" false
  | Propagator.Conflict c ->
      let e = c.Store.c_why in
      check "bool_clause: the empty clause conflicts at once" true;
      (* [Explanation.clause []] renders as `rup >= 1 ;`, closed the D-0022/I-X7 way. *)
      check "bool_clause: the empty clause's reason is the empty clause"
        (expl_lits e = Some "")

let test_bool_clause_rejects_non_bool () =
  (* The backstop [make] keeps for callers built by hand -- which every unit test is.
     compile.ml rejects a non-Boolean argument with a position long before this. *)
  let store = mk_store [ ("a", 0, 1); ("n", 0, 5) ] in
  raises "bool_clause: make refuses a literal that is not a var bool" (fun () ->
      ignore (mk_bool_clause [ (0, true); (1, true) ] store));
  (* [make] reads the store, so it must be called before anything narrows: a bool that
     has already been fixed no longer looks like [0, 1]. That is the D-0010 requirement
     as a test rather than only as a comment in the header. *)
  let store2 = mk_store [ ("a", 0, 1) ] in
  ignore (Store.set_hi store2 (var 0) 0 placeholder_pruning);
  raises "bool_clause: make refuses a bool that has already been narrowed" (fun () ->
      ignore (mk_bool_clause [ (0, true) ] store2))

(* --------------------------------------------------------------- bool2int: pushes *)

(* The four pushes of lib/core/prop/bool2int.ml, one named check each. This is the
   deliverable of this section: a channelling constraint that prunes one way and not the
   other is the classic silent weakness, and it is silent precisely because a MODEL
   cannot see it -- the search recovers the same answer by branching, so the printed
   output is identical. Only a direct assertion on the push can tell the difference. *)

let bool2int_case ~b_range ~x_range ~pre =
  let blo, bhi = b_range and xlo, xhi = x_range in
  let store = mk_store [ ("b", blo, bhi); ("x", xlo, xhi) ] in
  let prop = Bool2int.make store ~b:(var 0) ~x:(var 1) in
  List.iter
    (fun f ->
      match f store with
      | Store.Conflict _ -> failwith "bool2int_case: setup conflicted"
      | _ -> ())
    pre;
  (Bool2int.propagate prop store, store)

let dom_pair store =
  let d v = Store.get store (var v) in
  ((Domain.lo (d 0), Domain.hi (d 0)), (Domain.lo (d 1), Domain.hi (d 1)))

let test_bool2int_directions () =
  (* b -> x, lower bound. b is true; x, declared wide, must lose everything below 1. *)
  let _, s =
    bool2int_case ~b_range:(0, 1) ~x_range:(0, 5)
      ~pre:[ (fun st -> Store.set_lo st (var 0) 1 placeholder_pruning) ]
  in
  check "bool2int: b -> x raises lo(x) when b is true" (snd (dom_pair s) = (1, 1));
  (* b -> x, upper bound. b is false; x must lose everything above 0. *)
  let _, s =
    bool2int_case ~b_range:(0, 1) ~x_range:(0, 5)
      ~pre:[ (fun st -> Store.set_hi st (var 0) 0 placeholder_pruning) ]
  in
  check "bool2int: b -> x lowers hi(x) when b is false" (snd (dom_pair s) = (0, 0));
  (* b -> x with b untouched: b's DECLARED [0, 1] alone confines a wide x. This is the
     push test/models/bool_channel_sat.fzn depends on -- without it the linear row in
     that model has nothing to bite on and the answer changes. *)
  let _, s = bool2int_case ~b_range:(0, 1) ~x_range:(0, 5) ~pre:[] in
  check "bool2int: b's declared [0,1] alone confines a wide x to [0,1]"
    (snd (dom_pair s) = (0, 1));
  (* x -> b, lower bound. x's lo has been raised by something else (a linear row, in a
     real model) and b must follow. Dropping this direction is unsound in nothing and
     weaker in everything, which is exactly why a model cannot see it. *)
  let _, s =
    bool2int_case ~b_range:(0, 1) ~x_range:(0, 5)
      ~pre:[ (fun st -> Store.set_lo st (var 1) 1 placeholder_pruning) ]
  in
  check "bool2int: x -> b raises lo(b) when x >= 1" (fst (dom_pair s) = (1, 1));
  (* x -> b, upper bound. *)
  let _, s =
    bool2int_case ~b_range:(0, 1) ~x_range:(0, 5)
      ~pre:[ (fun st -> Store.set_hi st (var 1) 0 placeholder_pruning) ]
  in
  check "bool2int: x -> b lowers hi(b) when x <= 0" (fst (dom_pair s) = (0, 0));
  (* One pass reaches the fixpoint, which is the ordering argument in the header: x is
     narrowed to b's bounds first, then b to x's NEW bounds. Here x's lo is above b's,
     so the second step has real work and must still happen in the same call. *)
  let _, s =
    bool2int_case ~b_range:(0, 1) ~x_range:(0, 5)
      ~pre:[ (fun st -> Store.set_lo st (var 1) 1 placeholder_pruning) ]
  in
  check "bool2int: one pass does both directions, not just the first"
    (dom_pair s = ((1, 1), (1, 1)))

let test_bool2int_hole () =
  (* The header's claim about a hole: x = {0, 2} meets hi(x) := 1 and [Domain.set_hi]
     tightens past the hole (I-D2), leaving {0}. Declared consistency is BOUNDS, but the
     hole must not survive as a wrong upper bound of 2. *)
  let store =
    Store.create ~names:[| "b"; "x" |]
      ~domains:[| Domain.make 0 1; Domain.of_list [ 0; 2 ] |]
  in
  let prop = Bool2int.make store ~b:(var 0) ~x:(var 1) in
  match Bool2int.propagate prop store with
  | Propagator.Conflict _ ->
      check "bool2int: a hole in x is tightened past, not into" false
  | Propagator.Fixpoint ->
      let d = Store.get store (var 1) in
      check "bool2int: a hole in x is tightened past, not into"
        (Domain.lo d = 0 && Domain.hi d = 0)

let test_bool2int_soundness () =
  let case name x_range =
    check_generic_soundness name
      ~make:(fun store -> Bool2int.make store ~b:(var 0) ~x:(var 1))
      ~propagate:Bool2int.propagate ~n:2
      ~ranges:[ (0, 1); x_range ]
      ~satisfies:(fun a -> match a with [ b; x ] -> x = b | _ -> false)
  in
  case "bool2int: x declared wider than b" (0, 5);
  case "bool2int: x declared exactly [0,1]" (0, 1);
  case "bool2int: x declared with no overlap (unsat)" (2, 5);
  case "bool2int: x declared entirely negative (unsat)" (-4, -1);
  case "bool2int: x straddling zero" (-3, 3);
  case "bool2int: x declared {0} only" (0, 0);
  case "bool2int: x declared {1} only" (1, 1)

let test_bool2int_checking () =
  let run name xlo xhi bval xval expect_conflict =
    let store = mk_store [ ("b", 0, 1); ("x", xlo, xhi) ] in
    let prop = Bool2int.make store ~b:(var 0) ~x:(var 1) in
    let ok =
      match Store.fix store (var 0) bval placeholder_pruning with
      | Store.Conflict _ -> false
      | _ -> (
          match Store.fix store (var 1) xval placeholder_pruning with
          | Store.Conflict _ -> false
          | _ -> true)
    in
    if not ok then check (Printf.sprintf "bool2int I-P3 checking: %s (setup)" name) false
    else
      let got =
        match Bool2int.propagate prop store with
        | Propagator.Conflict _ -> true
        | Propagator.Fixpoint -> false
      in
      check (Printf.sprintf "bool2int I-P3 checking: %s" name) (got = expect_conflict)
  in
  run "b=0, x=0" 0 5 0 0 false;
  run "b=1, x=1" 0 5 1 1 false;
  run "b=0, x=1" 0 5 0 1 true;
  run "b=1, x=0" 0 5 1 0 true;
  run "b=1, x=3" 0 5 1 3 true;
  run "b=0, x=4" 0 5 0 4 true

let test_bool2int_idempotence () =
  let run name xlo xhi pre =
    let store = mk_store [ ("b", 0, 1); ("x", xlo, xhi) ] in
    let prop = Bool2int.make store ~b:(var 0) ~x:(var 1) in
    List.iter
      (fun f ->
        match f store with
        | Store.Conflict _ -> failwith "test_bool2int_idempotence: setup conflicted"
        | _ -> ())
      pre;
    match Bool2int.propagate prop store with
    | Propagator.Conflict _ ->
        check (Printf.sprintf "bool2int idempotence: %s (conflict)" name) true
    | Propagator.Fixpoint -> (
        let snap = Store.snapshot store in
        match Bool2int.propagate prop store with
        | Propagator.Conflict _ ->
            check
              (Printf.sprintf
                 "bool2int idempotence: %s -- the second run conflicted where the first \
                  did not"
                 name)
              false
        | Propagator.Fixpoint ->
            check
              (Printf.sprintf "bool2int I-P2/I-P3: %s, second run moves nothing" name)
              (Store.same_domains store snap))
  in
  run "nothing established, x wide" 0 5 [];
  run "b true" 0 5 [ (fun st -> Store.set_lo st (var 0) 1 placeholder_pruning) ];
  run "x >= 1" 0 5 [ (fun st -> Store.set_lo st (var 1) 1 placeholder_pruning) ];
  run "x already [0,1]" 0 1 []

let test_bool2int_conflicts () =
  (* A conflict whose reason is the EMPTY clause, and the header says why that is the
     correct and honest answer rather than a degenerate one: x is declared 2..5, b is a
     var bool, and the model is unsatisfiable from its declared domains alone. Both the
     fact read (b <= 1) and the bound it ran into (x >= 2) are still declared bounds,
     which have no literal -- they are the encoding's constant true (PROOF-FORMAT
     section 3) -- so the clause is empty, renders as `rup >= 1 ;` and is closed the
     D-0022/I-X7 way. Same route as `int_ne(x, x)`. *)
  let r, _ = bool2int_case ~b_range:(0, 1) ~x_range:(2, 5) ~pre:[] in
  (match r with
  | Propagator.Fixpoint -> check "bool2int: a declared-disjoint x conflicts at once" false
  | Propagator.Conflict c ->
      let e = c.Store.c_why in
      check "bool2int: a declared-disjoint x conflicts at once" true;
      check "bool2int: its reason is the empty clause (both bounds still declared)"
        (expl_lits e = Some ""));
  (* And a conflict whose reason is NOT empty: both bounds have been moved, so both have
     literals and both must appear. This is the half that would stay green if
     [ge_fact]/[le_fact] dropped every fact rather than only the declared ones -- the
     empty-clause case above cannot tell those two apart. *)
  let r, _ =
    bool2int_case ~b_range:(0, 1) ~x_range:(0, 5)
      ~pre:
        [
          (fun st -> Store.set_hi st (var 0) 0 placeholder_pruning);
          (fun st -> Store.set_lo st (var 1) 1 placeholder_pruning);
        ]
  in
  match r with
  | Propagator.Fixpoint -> check "bool2int: b false against x >= 1 conflicts" false
  | Propagator.Conflict c ->
      let e = c.Store.c_why in
      check "bool2int: b false against x >= 1 conflicts" true;
      check "bool2int: the conflict names both moved bounds, negated"
        (expl_lits e = Some "b_ge_1 ~x_ge_1")

let test_bool2int_rejects_non_bool () =
  let store = mk_store [ ("n", 0, 5); ("x", 0, 5) ] in
  raises "bool2int: make refuses a first argument that is not a var bool" (fun () ->
      ignore (Bool2int.make store ~b:(var 0) ~x:(var 1)))

(* ------------------------------------------ bool_clause and bool2int, past the checker *)

(* The row lib/flatzinc/compile.ml posts for a clause, by the same arithmetic:
     x_1 \/ ... \/ x_p \/ ~y_1 \/ ... \/ ~y_q  is  -sum_i x_i + sum_j y_j <= q - 1,
   expanded over the order encoding by the one door every other row goes through. The
   verbatim text of what that produces is pinned in [test_bool_rows]; here it is used so
   the rup is checked against the row a real model would actually carry. *)
let add_clause_row e (lits : (string * bool) list) =
  let q = List.length (List.filter (fun (_, p) -> not p) lits) in
  Encoding.add_int_lin_le e
    (List.map (fun (n, p) -> ((if p then -1 else 1), n)) lits)
    (q - 1)

(* [~model_id] is kept in the signature although [Justify.create] no longer takes one
   (M1-T31): the callers pass the row their explanation is about, and it documents the
   scene. It is no longer a fallback -- [expl] names its own row. *)
let write_and_emit dir base e ~expl ~model_id ~sol =
  ignore model_id;
  let opb = Filename.concat dir (base ^ ".opb") in
  let pbp = Filename.concat dir (base ^ ".pbp") in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ base ] e oc;
  close_out oc;
  let oc = open_out pbp in
  let w = Writer.create ~comments:true ~audit:true oc in
  Encoding.start_proof e w;
  let ctx = Justify.create ~writer:w ~encoding:e in
  let id = Justify.emit ctx expl in
  Writer.delete w id;
  Writer.conclusion w (Writer.Sat (Encoding.assignment_lits e sol));
  close_out oc;
  (opb, pbp)

(* (a \/ ~b \/ c) with a false and b true established by real model rows. The pruning is
   c := true and its reason is the clause; the rup must close in a single unit
   propagation against the clause row. *)
(* The two facts are established in the STORE ONLY -- deliberately NOT as .opb rows,
   and this is load-bearing for every control below it.

   Measured, not reasoned: an earlier version of this scene posted `~a` and `b` as model
   rows, the way build_int_le_multi and friends above do. That makes the .opb force
   c true on its own, so a REASON WITH ITS FACTS DROPPED is still entailed by the model
   and veripb accepts it. A break that deleted the facts from a justification passed the
   whole suite -- 332 checks and 28 models -- until the scene was changed. It is the
   D-0016 hazard (a valid but useless generalisation) and D-0009's (restating a
   constraint is trivially valid) in one place, and it is the tenth instance of this
   project's signature failure mode, caught here rather than shipped.

   With the facts held only in the store, the .opb says nothing about a or b, so the
   clause `a \/ ~b \/ c` is RUP (it is the row) while every weakening or corruption of
   it is not. That is what makes [build_bool_clause_wrong] and
   [build_bool_clause_weakened] real controls rather than decoration. It is also
   faithful: in a real run these bounds come from a decision or from another
   propagator, neither of which is a model row. *)
let bool_clause_scene () =
  let e = Encoding.create () in
  Encoding.declare_bool e "a";
  Encoding.declare_bool e "b";
  Encoding.declare_bool e "c";
  let row = add_clause_row e [ ("a", true); ("b", false); ("c", true) ] in
  let store =
    Store.create ~names:[| "a"; "b"; "c" |]
      ~domains:[| Domain.make 0 1; Domain.make 0 1; Domain.make 0 1 |]
  in
  let prop = mk_bool_clause [ (0, true); (1, false); (2, true) ] store in
  (match Store.set_hi store (var 0) 0 placeholder_pruning with
  | Store.Changed -> ()
  | _ -> failwith "bool_clause_scene: a := false failed");
  (match Store.set_lo store (var 1) 1 placeholder_pruning with
  | Store.Changed -> ()
  | _ -> failwith "bool_clause_scene: b := true failed");
  (e, row, store, prop)

let build_bool_clause_unit dir =
  let e, row, store, prop = bool_clause_scene () in
  (match Bool_clause.propagate prop store with
  | Propagator.Conflict _ -> failwith "build_bool_clause_unit: conflicted"
  | Propagator.Fixpoint -> ());
  let entry = List.hd (Store.trail_entries store) in
  let expl = Explanation.force (Store.explanation store entry) in
  write_and_emit dir "boolclause_unit" e ~expl ~model_id:row
    ~sol:[ ("a", 0); ("b", 1); ("c", 1) ]

(* The negative control. Same scene, same facts, but the claim's polarity is flipped:
   the derivation asserts c FALSE. That clause is not entailed -- a = 0, b = 1, c = 1
   satisfies every row in the .opb -- so veripb must reject it. Without this, "veripb
   accepted our rup" says nothing: [rup] searches for its own justification, and a test
   that only ever feeds it true clauses cannot tell a correct explanation from a lucky
   one. *)
let build_bool_clause_wrong dir =
  let e, row, _, _ = bool_clause_scene () in
  let expl =
    Explanation.clause [ Lit.bool_true "a"; Lit.bool_false "b"; Lit.bool_false "c" ]
  in
  write_and_emit dir "boolclause_wrong" e ~expl ~model_id:row
    ~sol:[ ("a", 0); ("b", 1); ("c", 1) ]

(* The second control, and the one that tests the direction the first cannot: a reason
   that is CORRECT AS FAR AS IT GOES but has dropped a literal. `~b \/ c` is a strictly
   stronger claim than the clause -- it asserts c whenever b holds, regardless of a --
   and a = 1, b = 1, c = 0 satisfies the .opb while falsifying it, so veripb must
   reject. A justification that quietly forgets a fact it read is the shape of break
   that a scene whose facts are model rows cannot see; see [bool_clause_scene]. *)
let build_bool_clause_weakened dir =
  let e, row, _, _ = bool_clause_scene () in
  let expl = Explanation.clause [ Lit.bool_false "b"; Lit.bool_true "c" ] in
  write_and_emit dir "boolclause_weakened" e ~expl ~model_id:row
    ~sol:[ ("a", 0); ("b", 1); ("c", 1) ]

(* The conflict route that ends in a REFUTATION rather than in a clause, which is the
   half a nogood over three literals cannot test: `a_ge_1 \/ ~b_ge_1 \/ c_ge_1` is a
   perfectly good derived constraint and is not contradicting, so nothing can be
   concluded from it alone -- the model-level refutations in test/models/bool_reif_unsat
   .fzn and bool_channel_unsat.fzn are where a nogood gets resolved down to the empty
   clause, and they run the whole pipeline. What IS testable here on its own is the
   empty clause: `bool_clause([], [])` conflicts immediately with [Explanation.clause []],
   which renders as `rup >= 1 ;` -- contradicting, and closed the D-0022/I-X7 way against
   an .opb whose only row is the false empty sum. Same route as `int_ne(x, x)` takes in
   test/models/ne_self_unsat.fzn, reached from the Boolean side.

   The three-literal conflict clause is not left unchecked: [Bool_clause] shares ONE
   [Explanation.t] between every pruning and every conflict of an instance (its header
   says why), so the value [build_bool_clause_unit] puts past the checker above is
   physically the same value a conflict of that clause would report. *)
let build_bool_clause_conflict dir =
  let e = Encoding.create () in
  Encoding.declare_bool e "a";
  ignore (add_clause_row e []);
  let store = Store.create ~names:[| "a" |] ~domains:[| Domain.make 0 1 |] in
  let prop = mk_bool_clause [] store in
  let expl =
    match Bool_clause.propagate prop store with
    | Propagator.Conflict c -> Explanation.force c.Store.c_why
    | Propagator.Fixpoint -> failwith "build_bool_clause_conflict: did not conflict"
  in
  let opb = Filename.concat dir "boolclause_empty.opb" in
  let pbp = Filename.concat dir "boolclause_empty.pbp" in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "bool_clause([], []) -- the false empty sum" ] e oc;
  close_out oc;
  let oc = open_out pbp in
  let w = Writer.create ~comments:true ~audit:true oc in
  Encoding.start_proof e w;
  let ctx = Justify.create ~writer:w ~encoding:e in
  let id = Justify.emit ctx expl in
  Writer.conclusion w (Writer.Unsat (Some id));
  close_out oc;
  (opb, pbp)

(* bool2int's four pushes, each emitted and checked separately -- the module header
   claims "test/unit/test_prop.ml runs every one of them past the real checker rather
   than taking this paragraph's word for it", and these four runs are what make that
   sentence true. [x] is declared 0..5, so the b -> x upper push moves a bound four
   steps and its claim is `~x_ge_2` rather than the one-step case D-0010 warns is not
   enough of a test. *)
let bool2int_scene ~pre =
  let e = Encoding.create () in
  Encoding.declare_bool e "b";
  Encoding.declare_int e "x" ~lo:0 ~hi:5;
  (* row LE: x - b <= 0, then row GE: b - x <= 0, in the order compile.ml posts them. *)
  let row_le = Encoding.add_int_lin_le e [ (1, "x"); (-1, "b") ] 0 in
  let row_ge = Encoding.add_int_lin_le e [ (-1, "x"); (1, "b") ] 0 in
  let store =
    Store.create ~names:[| "b"; "x" |] ~domains:[| Domain.make 0 1; Domain.make 0 5 |]
  in
  let prop = Bool2int.make store ~b:(var 0) ~x:(var 1) in
  List.iter
    (fun f ->
      match f e store with
      | Store.Changed -> ()
      | _ -> failwith "bool2int_scene: setup did not move a bound")
    pre;
  (e, row_le, row_ge, store, prop)

(* Which push to read off the trail. Two pushes can land on the same variable in one
   call (b true moves both of x's bounds), so naming the variable is not enough -- and
   picking the wrong entry would silently check a different push than the one the test
   is named after. *)
type which_bound = Lo | Hi

let bool2int_push dir base ~pre ~wvar ~wbound ~sol =
  let e, row_le, _, store, prop = bool2int_scene ~pre in
  let before = Store.trail_length store in
  (match Bool2int.propagate prop store with
  | Propagator.Conflict _ -> failwith (base ^ ": conflicted")
  | Propagator.Fixpoint -> ());
  let n_new = Store.trail_length store - before in
  let entries = List.filteri (fun i _ -> i < n_new) (Store.trail_entries store) in
  let moved (en : Store.entry) =
    match wbound with
    | Lo -> Domain.lo en.now > Domain.lo en.old
    | Hi -> Domain.hi en.now < Domain.hi en.old
  in
  let entry =
    match
      List.find_opt
        (fun (en : Store.entry) -> Var.equal en.var (var wvar) && moved en)
        entries
    with
    | Some en -> en
    | None -> failwith (base ^ ": the push under test never happened")
  in
  let expl = Explanation.force (Store.explanation store entry) in
  write_and_emit dir base e ~expl ~model_id:row_le ~sol

(* A setup bound, established in the store and NOT as an .opb row -- for the reason
   spelled out at [bool_clause_scene], which was measured here: with `b_ge_1` posted as
   a model row the .opb entails lo(x) := 1 by itself, so bool2int's reason verifies with
   its facts deleted and the four checks below stop testing the justification. The
   literal argument is kept so each caller still says which fact it is establishing. *)
let store_fact (_l : Lit.t) = ()

let build_bool2int_b_to_x_lo dir =
  bool2int_push dir "bool2int_b_to_x_lo"
    ~pre:
      [
        (fun e st ->
          store_fact (Lit.bool_true "b");
          ignore e;
          Store.set_lo st (var 0) 1 placeholder_pruning);
      ]
    ~wvar:1 ~wbound:Lo
    ~sol:[ ("b", 1); ("x", 1) ]

let build_bool2int_b_to_x_hi dir =
  bool2int_push dir "bool2int_b_to_x_hi"
    ~pre:
      [
        (fun e st ->
          store_fact (Lit.bool_false "b");
          ignore e;
          Store.set_hi st (var 0) 0 placeholder_pruning);
      ]
    ~wvar:1 ~wbound:Hi
    ~sol:[ ("b", 0); ("x", 0) ]

let build_bool2int_x_to_b_lo dir =
  (* x >= 1 established by a real row; the push under test is lo(b) := 1. Its clause is
     `b_ge_1 \/ ~x_ge_1`, which is RUP against row LE (x <= b), not against row GE --
     the checker has to find that for itself, which is the point of emitting it. *)
  bool2int_push dir "bool2int_x_to_b_lo"
    ~pre:
      [
        (fun e st ->
          store_fact (Lit.ge "x" 1);
          ignore e;
          Store.set_lo st (var 1) 1 placeholder_pruning);
      ]
    ~wvar:0 ~wbound:Lo
    ~sol:[ ("b", 1); ("x", 1) ]

let build_bool2int_x_to_b_hi dir =
  bool2int_push dir "bool2int_x_to_b_hi"
    ~pre:
      [
        (fun e st ->
          store_fact (Lit.le "x" 0);
          ignore e;
          Store.set_hi st (var 1) 0 placeholder_pruning);
      ]
    ~wvar:0 ~wbound:Hi
    ~sol:[ ("b", 0); ("x", 0) ]

(* The negative control for the channelling: the b -> x scene with the claim's polarity
   flipped. b is false, so x <= 0 is entailed and x >= 1 is not. *)
let build_bool2int_wrong dir =
  let e, row_le, _, _, _ =
    bool2int_scene
      ~pre:
        [
          (fun e st ->
            store_fact (Lit.bool_false "b");
            ignore e;
            Store.set_hi st (var 0) 0 placeholder_pruning);
        ]
  in
  let expl = Explanation.clause [ Lit.ge "x" 1; Lit.bool_true "b" ] in
  write_and_emit dir "bool2int_wrong" e ~expl ~model_id:row_le ~sol:[ ("b", 0); ("x", 0) ]

(* The control that was missing, and the reason this file's scenes stopped posting their
   setup facts as model rows. b is false, so bool2int pushes hi(x) := 0 with the reason
   `~x_ge_1 \/ b_ge_1` -- the claim, disjoined with the negation of the one fact it
   read. This emits the claim ALONE, which is what a justification that forgot to record
   its facts would emit: "x <= 0", unconditionally, which is simply false of the model
   (b = 1, x = 1 is a solution). veripb must reject it.

   Measured: deleting the facts from [implication] passed all 332 checks and all 28
   models before this control existed, because the four positive push checks above
   carried their facts as .opb rows and a factless claim was therefore still entailed.
   That is the tenth instance of this project's signature failure mode; it is the one
   the task asked to be looked for, and it was in this file rather than in lib/. *)
let build_bool2int_factless dir =
  let e, row_le, _, _, _ =
    bool2int_scene
      ~pre:
        [
          (fun e st ->
            store_fact (Lit.bool_false "b");
            ignore e;
            Store.set_hi st (var 0) 0 placeholder_pruning);
        ]
  in
  let expl = Explanation.clause [ Lit.le "x" 0 ] in
  write_and_emit dir "bool2int_factless" e ~expl ~model_id:row_le
    ~sol:[ ("b", 0); ("x", 0) ]

(* ------------------------------------------- the .opb rows, verbatim, per builtin *)

let compiled_rows src =
  let t = compile_src src in
  List.map Opb.constr_to_string (Encoding.constraints t.Compile.encoding)

let test_bool_rows () =
  (* The encoding is normative (docs/PROOF-FORMAT.md section 3) and a silent change of
     row shape is exactly the class of defect D-0010 was, so these are pinned as text.
     Every row below is a clause -- coefficient-1 literals against a right-hand side of
     1 -- which is what makes bool_clause's rup close in a single unit propagation, and
     is also the property the D-0030 check downstream rests on. *)
  let decl = "var bool: a;\nvar bool: b;\nvar bool: c;\n" in
  let rows src = compiled_rows (decl ^ src ^ "solve satisfy;\n") in
  check "bool_clause: the row is the clause, over the order encoding"
    (rows "constraint bool_clause([a, b], [c]);\n"
    = [ "+1 a_ge_1 +1 b_ge_1 +1 ~c_ge_1 >= 1 ;" ]);
  check "bool_clause: an all-negative clause"
    (rows "constraint bool_clause([], [a, b]);\n" = [ "+1 ~a_ge_1 +1 ~b_ge_1 >= 1 ;" ]);
  check "array_bool_or: one forward clause and one backward clause per operand"
    (rows "constraint array_bool_or([a, b], c);\n"
    = [
        "+1 ~c_ge_1 +1 a_ge_1 +1 b_ge_1 >= 1 ;";
        "+1 c_ge_1 +1 ~a_ge_1 >= 1 ;";
        "+1 c_ge_1 +1 ~b_ge_1 >= 1 ;";
      ]);
  check "array_bool_and: one forward clause per operand and one backward clause"
    (rows "constraint array_bool_and([a, b], c);\n"
    = [
        "+1 ~c_ge_1 +1 a_ge_1 >= 1 ;";
        "+1 ~c_ge_1 +1 b_ge_1 >= 1 ;";
        "+1 c_ge_1 +1 ~a_ge_1 +1 ~b_ge_1 >= 1 ;";
      ]);
  check "bool_eq: the two implications"
    (rows "constraint bool_eq(a, b);\n"
    = [ "+1 ~a_ge_1 +1 b_ge_1 >= 1 ;"; "+1 a_ge_1 +1 ~b_ge_1 >= 1 ;" ]);
  check "bool_not: they cannot both be false, and cannot both be true"
    (rows "constraint bool_not(a, b);\n"
    = [ "+1 a_ge_1 +1 b_ge_1 >= 1 ;"; "+1 ~a_ge_1 +1 ~b_ge_1 >= 1 ;" ]);
  (* An empty operand array is the identity of its connective, and compile.ml gets that
     from the ordinary path rather than from an empty-array special case. *)
  check "array_bool_or([], r): the forward clause degenerates to the unit ~r"
    (rows "constraint array_bool_or([], c);\n" = [ "+1 ~c_ge_1 >= 1 ;" ]);
  check "array_bool_and([], r): the backward clause degenerates to the unit r"
    (rows "constraint array_bool_and([], c);\n" = [ "+1 c_ge_1 >= 1 ;" ]);
  (* bool2int against an integer: the two halves of the equality, LE first. Pinned
     because lib/core/prop/bool2int.ml's worked RUP checks assume that order. *)
  (* x is declared 0..2, so its order encoding carries a consistency clause of its own
     (x >= 2 -> x >= 1) and that row comes FIRST. It is pinned here rather than skipped
     because every id in the proof counts from it: a row appearing or disappearing above
     the model rows shifts every later citation, which is PROOF-FORMAT section 2's trap
     in a different costume. `a` needs no such clause -- a var bool has exactly one
     order literal (D-0007), which is why the all-Boolean pins above have none. *)
  check "bool2int: x's consistency clause, then row LE (x - b <= 0), then row GE"
    (compiled_rows
       "var bool: a;\nvar 0..2: x;\nconstraint bool2int(a, x);\nsolve satisfy;\n"
    = [
        "+1 ~x_ge_2 +1 x_ge_1 >= 1 ;";
        "+1 ~x_ge_1 +1 ~x_ge_2 +1 a_ge_1 >= 2 ;";
        "+1 x_ge_1 +1 x_ge_2 +1 ~a_ge_1 >= 1 ;";
      ])

let test_bool_ground_rows () =
  (* Constants fold, and the row stays an EXACT statement of the constraint rather than
     a stronger one: each true constant literal weakens the right-hand side by one. A
     tautology therefore posts a vacuous row and NO propagator -- compile.ml's header
     calls that asymmetry load-bearing, because an instance over the remaining literals
     would assert something the constraint does not say and would prune values that are
     in solutions. *)
  let t =
    compile_src "var bool: a;\nconstraint bool_clause([a, true], []);\nsolve satisfy;\n"
  in
  (* `a \/ true`. The true constant weakens the right-hand side from 0 to... precisely
     to the point where the row says nothing: `+1 a_ge_1 >= 0` is satisfied by every
     assignment. That is the row being an EXACT statement of a tautology rather than a
     stronger one -- the unit `+1 a_ge_1 >= 1` would be wrong, and is what a fold that
     dropped the constant instead of counting it would produce. *)
  check "bool_clause with a true constant: the row is vacuous, not the unit a"
    (List.map Opb.constr_to_string (Encoding.constraints t.Compile.encoding)
    = [ "+1 a_ge_1 >= 0 ;" ]);
  check "bool_clause with a true constant: no propagator is posted"
    (Engine.n_instances t.Compile.engine = 0);
  let t =
    compile_src "var bool: a;\nconstraint bool_clause([a, false], []);\nsolve satisfy;\n"
  in
  check "bool_clause with a false constant: the constant simply drops"
    (List.map Opb.constr_to_string (Encoding.constraints t.Compile.encoding)
    = [ "+1 a_ge_1 >= 1 ;" ]);
  check "bool_clause with a false constant: the propagator is still posted"
    (Engine.n_instances t.Compile.engine = 1);
  (* `bool_clause([], [])` is the false clause: a legal, unsatisfiable model, posted with
     no special case. The row is the empty sum >= 1. *)
  let t = compile_src "var bool: a;\nconstraint bool_clause([], []);\nsolve satisfy;\n" in
  check "bool_clause([], []): the row is the false empty sum"
    (List.map Opb.constr_to_string (Encoding.constraints t.Compile.encoding)
    = [ ">= 1 ;" ]);
  (* A variable at both polarities is a tautology and posts a vacuous row -- but the
     propagator IS posted, because no constant folded away: it simply never fires. *)
  let t =
    compile_src "var bool: a;\nconstraint bool_clause([a], [a]);\nsolve satisfy;\n"
  in
  check "bool_clause(a, ~a): a tautology over one variable posts a vacuous row"
    (List.map Opb.constr_to_string (Encoding.constraints t.Compile.encoding)
    = [ ">= 0 ;" ])

let test_bool_type_rejections () =
  (* A `var 0..1` is NOT a `var bool`: FlatZinc types them differently and the difference
     is not cosmetic, since SPEC 2.2 prints a bool as false/true under its declared type
     and the propagators spell every literal as b_ge_1. The diagnostic has to name the
     variable and the way out. *)
  expect_capped "bool_clause: a var 0..1 argument is refused, by name"
    ~needles:[ "bool_clause"; "`n`"; "var bool"; "bool2int" ]
    "var 0..1: n;\nconstraint bool_clause([n], []);\nsolve satisfy;\n";
  expect_capped "array_bool_or: a non-Boolean operand is refused"
    ~needles:[ "array_bool_or"; "`n`"; "var bool" ]
    "var 0..1: n;\nvar bool: r;\nconstraint array_bool_or([n], r);\nsolve satisfy;\n";
  expect_capped "array_bool_and: a non-Boolean reifier is refused"
    ~needles:[ "array_bool_and"; "`n`"; "var bool" ]
    "var bool: a;\nvar 0..1: n;\nconstraint array_bool_and([a], n);\nsolve satisfy;\n";
  expect_capped "bool_eq: a non-Boolean argument is refused"
    ~needles:[ "bool_eq"; "`n`"; "var bool" ]
    "var bool: a;\nvar 0..1: n;\nconstraint bool_eq(a, n);\nsolve satisfy;\n";
  expect_capped "bool_not: a non-Boolean argument is refused"
    ~needles:[ "bool_not"; "`n`"; "var bool" ]
    "var bool: a;\nvar 0..1: n;\nconstraint bool_not(a, n);\nsolve satisfy;\n";
  expect_capped "bool2int: a non-Boolean FIRST argument is refused"
    ~needles:[ "bool2int"; "`n`"; "var bool" ]
    "var 0..1: n;\nvar 0..5: x;\nconstraint bool2int(n, x);\nsolve satisfy;\n";
  expect_capped "bool_clause: a non-Boolean integer constant is refused"
    ~needles:[ "bool_clause"; "Boolean" ]
    "var bool: a;\nconstraint bool_clause([a, 2], []);\nsolve satisfy;\n";
  (* And the other direction, so the type check cannot become a way to refuse anything
     awkward: bool2int's SECOND argument is an ordinary integer and must be accepted,
     wide domain and all. *)
  expect_compiles "bool2int: a wide integer second argument still compiles"
    "var bool: b;\nvar 0..1000: x;\nconstraint bool2int(b, x);\nsolve satisfy;\n"

(* -------------------------------------------- the six builtins actually get posted *)

let test_bool_instances_posted () =
  (* compile.ml ACCEPTING a constraint and compile.ml POSTING it are different things,
     and an ignored constraint still lets a model "solve". The models in test/models/
     answer this by having answers that depend on the Boolean constraint; this asks the
     same question of the instance count, where an off-by-one decomposition shows up
     directly rather than through a search that happens to recover. *)
  let n src = Engine.n_instances (compile_src src).Compile.engine in
  let decl = "var bool: a;\nvar bool: b;\nvar bool: c;\n" in
  check "bool_clause posts one instance"
    (n (decl ^ "constraint bool_clause([a, b], [c]);\nsolve satisfy;\n") = 1);
  check "array_bool_or posts one instance per clause (1 forward + 2 backward)"
    (n (decl ^ "constraint array_bool_or([a, b], c);\nsolve satisfy;\n") = 3);
  check "array_bool_and posts one instance per clause (2 forward + 1 backward)"
    (n (decl ^ "constraint array_bool_and([a, b], c);\nsolve satisfy;\n") = 3);
  check "bool_eq posts two instances, one per implication"
    (n (decl ^ "constraint bool_eq(a, b);\nsolve satisfy;\n") = 2);
  check "bool_not posts two instances"
    (n (decl ^ "constraint bool_not(a, b);\nsolve satisfy;\n") = 2);
  check "bool2int between two variables posts one instance"
    (n "var bool: b;\nvar 0..5: x;\nconstraint bool2int(b, x);\nsolve satisfy;\n" = 1);
  (* When either side is a constant there is nothing to channel and compile.ml routes to
     the ordinary ground equality, which is two Linear instances. Stated as a check so
     that routing cannot change silently. *)
  check "bool2int against a constant integer routes to the ordinary equality"
    (n "var bool: b;\nconstraint bool2int(b, 1);\nsolve satisfy;\n" = 2)

(* ------------------------------- D-0030: no single .opb row refutes the UNSAT models *)

(* The largest value a row's left-hand side can attain. Each pb variable is set once, so
   its contribution is the better of "all its positive occurrences" and "all its negated
   ones" -- which is why this cannot be a plain sum of positive coefficients: a row
   mentioning both x and ~x would be over-counted, and over-counting is the direction
   that would make this check pass when it should fail. *)
let max_attainable_lhs (c : Opb.constr) =
  let tbl = Hashtbl.create 16 in
  List.iter
    (fun (a, (l : Lit.t)) ->
      let key = Lit.var_name l.Lit.v in
      let p, n = try Hashtbl.find tbl key with Not_found -> (0, 0) in
      if l.Lit.positive then Hashtbl.replace tbl key (p + a, n)
      else Hashtbl.replace tbl key (p, n + a))
    (Opb.terms c);
  Hashtbl.fold (fun _ (p, n) acc -> acc + max (max p n) 0) tbl 0

(* test/models/, located the way test_flatzinc.ml and test_output.ml locate it. Not
   finding it is a FAILURE, never a skip: a check that silently does not run is the
   failure mode this whole section exists for. *)
let rec bool_find_up dir marker depth =
  if depth <= 0 then None
  else if Sys.file_exists (Filename.concat dir marker) then Some dir
  else
    let parent = Filename.dirname dir in
    if String.equal parent dir then None else bool_find_up parent marker (depth - 1)

let bool_models_dir =
  let marker = Filename.concat "test" (Filename.concat "models" "bool_reif_unsat.fzn") in
  match bool_find_up (Sys.getcwd ()) marker 12 with
  | Some d -> Some (Filename.concat d (Filename.concat "test" "models"))
  | None -> (
      match bool_find_up (Filename.dirname Sys.executable_name) marker 12 with
      | Some d -> Some (Filename.concat d (Filename.concat "test" "models"))
      | None -> None)

(* D-0030's finding, as a check. `root_unsat`'s .opb carries
   `+1 ~x_ge_2 +1 ~x_ge_3 >= 3` -- two coefficient-1 literals asked to sum to 3 -- so the
   model is refuted by a single row and a proof containing NO derivation at all verifies
   against it. An UNSAT instance with that property cannot test whether a derivation was
   load-bearing, which is why M1-T38 exists.

   Checked two ways, because the first is arithmetic on our own reading of the row and
   the second asks the checker:

     1. every row's maximum attainable left-hand side reaches its right-hand side;
     2. veripb REJECTS a proof that derives nothing and concludes `UNSAT : @ci`, for
        every model row id i in turn. If any one were accepted, that row alone refutes
        the model and everything above it is decoration. *)
let test_no_single_row_refutes name model =
  match bool_models_dir with
  | None ->
      incr failures;
      Printf.printf
        "FAIL %s: test/models was not found, so the D-0030 single-row check did NOT run. \
         Do not treat this as a pass.\n"
        name
  | Some dir_models -> (
      let t = compile_src (read_file (Filename.concat dir_models model)) in
      let e = t.Compile.encoding in
      let rows = Encoding.constraints e in
      let bad =
        List.filter
          (fun c -> Opb.relation c = Opb.Ge && max_attainable_lhs c < Opb.rhs c)
          rows
      in
      check
        (Printf.sprintf "%s: no .opb row is infeasible on its own (D-0030)" name)
        (bad = []);
      List.iter
        (fun c -> Printf.printf "       infeasible alone: %s\n" (Opb.constr_to_string c))
        bad;
      (* The same claim, put to the checker rather than to our arithmetic. *)
      match veripb_path () with
      | None ->
          incr failures;
          Printf.printf
            "FAIL %s: veripb not found -- the D-0030 single-row check did NOT run. Do \
             not treat this as a pass.\n"
            name
      | Some veripb -> (
          let dir = Filename.temp_file "baguette_d0030" "" in
          Sys.remove dir;
          Sys.mkdir dir 0o700;
          let opb = Filename.concat dir "m.opb" in
          let oc = open_out opb in
          Encoding.write_opb ~comments:[ name ] e oc;
          close_out oc;
          let n = Opb.n_checker_constraints rows in
          let accepted = ref [] in
          for i = 1 to n do
            let pbp = Filename.concat dir "empty.pbp" in
            let oc = open_out pbp in
            (* A proof that derives NOTHING. If the checker accepts it, row i alone is
               contradicting -- exactly root_unsat's defect. *)
            Printf.fprintf oc
              "pseudo-Boolean proof version 3.0\n\
               f %d ;\n\
               output NONE ;\n\
               conclusion UNSAT : @c%d ;\n\
               end pseudo-Boolean proof ;\n"
              n i;
            close_out oc;
            let log = Filename.concat dir "log" in
            let rc =
              Sys.command
                (Printf.sprintf "%s %s %s > %s 2>&1" (Filename.quote veripb)
                   (Filename.quote opb) (Filename.quote pbp) (Filename.quote log))
            in
            if rc = 0 then accepted := i :: !accepted;
            (try Sys.remove pbp with _ -> ());
            try Sys.remove log with _ -> ()
          done;
          check
            (Printf.sprintf
               "%s: veripb rejects a derivation-free proof against each of the %d model \
                rows (D-0030)"
               name n)
            (!accepted = []);
          if !accepted <> [] then
            Printf.printf
              "       rows accepted as contradicting on their own: %s -- this model is \
               as hollow as root_unsat\n"
              (String.concat ", "
                 (List.map (fun i -> Printf.sprintf "@c%d" i) (List.rev !accepted)));
          (try Sys.remove opb with _ -> ());
          try Sys.rmdir dir with _ -> ()))

(* The control for that check, without which it is not evidence. D-0030 registered
   root_unsat as [Known_slack] rather than weakening it away; this is the local mirror
   of that decision -- the procedure is run against the row that is known to be bad and
   must find it. If the check ever stops being able to see the defect, the two checks
   above would go on passing and mean nothing, which is the failure mode itself. *)
let test_single_row_check_can_fire () =
  (* root_unsat's second row, verbatim from D-0030. *)
  let c = Opb.ge [ (1, Lit.le "x" 1); (1, Lit.le "x" 2) ] 3 in
  check "D-0030 control: the max-attainable check DOES fire on root_unsat's bad row"
    (max_attainable_lhs c < Opb.rhs c);
  let ok = Opb.clause [ Lit.bool_true "a"; Lit.bool_false "b" ] in
  check "D-0030 control: it does not fire on an ordinary clause"
    (max_attainable_lhs ok >= Opb.rhs ok);
  (* The over-counting trap: a row mentioning one variable at both polarities can only
     reach 1, not 2, and a plain sum of positive coefficients would say 2 and call this
     row satisfiable. *)
  let both = Opb.ge [ (1, Lit.bool_true "a"); (1, Lit.bool_false "a") ] 2 in
  check "D-0030 control: a variable at both polarities is counted once, not twice"
    (max_attainable_lhs both = 1 && max_attainable_lhs both < Opb.rhs both)

(* ------------------------------------------------------------------------ main *)

(* ------------------------------------- I-X6 on the JUSTIFICATION half (M2-T8)

   D-0026 discharges I-X6 on the reason half by construction: a [Reason.t] is data and
   [Reason.lits] takes no store, so it cannot read live state even in principle. The
   justification half is still a thunk and still can, and a thunk that decided which trail
   entry witnesses a bound *at force time* rather than at push time would render a later
   bound as the reason for an earlier pruning. That is the defect
   [explain_cross_conflict] shipped until M1-T13, which was harmless only by accident.

   Nothing in the suite could see it. Measured: moving [Linear]'s per-term snapshot
   decision inside the thunk reddened zero checks across every unit binary and all 34
   models, because search forces what it forces immediately. This test is what closes
   that, and the way it closes it is the only way available -- run the same scene twice
   and force at two different moments:

     A: force immediately, while the store still says what the propagator read;
     B: move the cited bound to a DIFFERENT row's entry first, then force.

   A snapshotting thunk gives the same derivation both times. A live-reading one cites
   whatever moved the bound most recently, so B names row 902 where A names 901. The two
   runs are separate stores because [Explanation.force] memoises: forcing once in one
   store would make the second observation unreachable. *)
let test_ix6_justification_snapshot () =
  let scene ~move_after =
    let store = mk_store [ ("x", 0, 5); ("y", 0, 5) ] in
    (* rhs 10, not something tighter: the row must push x while leaving y a range, or the
       second push below lands on a fixed variable and conflicts instead of moving a
       bound -- which would make this a test of nothing. The precondition is asserted
       rather than assumed, and it is what caught that first draft. *)
    let prop = Linear.make store [ (2, var 0); (3, var 1) ] 10 ~row_id:1 in
    (* y >= 1, by "some earlier propagator" whose row is 901. *)
    ignore (Store.set_lo store (var 1) 1 placeholder_pruning);
    let before = Store.trail_length store in
    (match Linear.propagate prop store with
    | Propagator.Conflict _ -> failwith "test_ix6: expected a pruning"
    | Propagator.Fixpoint -> ());
    let e =
      match
        List.find_opt
          (fun (en : Store.entry) -> Var.equal en.Store.var (var 0))
          (List.filteri
             (fun i _ -> i < Store.trail_length store - before)
             (Store.trail_entries store))
      with
      | Some e -> e
      | None -> failwith "test_ix6: x was not pushed"
    in
    if move_after then
      (* A DIFFERENT row now holds y's lower bound. Under the O(1) support this is what
         [Store.lo_reasons] would answer from here on, so a thunk that asks again gets
         902 and a thunk that snapshotted keeps 901. *)
      ignore
        (Store.set_lo store (var 1) 2
           (Reason.because Reason.none (Explanation.model_row 902)));
    (Explanation.to_string (Explanation.force (Store.explanation store e)), store)
  in
  let a, _ = scene ~move_after:false in
  let b, store_b = scene ~move_after:true in
  (* The scene has to actually move the bound, or this test proves nothing. *)
  check "I-X6: the cited bound really was moved by another row before forcing"
    (Domain.lo (Store.get store_b (var 1)) = 2
    &&
    match Store.lo_reasons store_b (var 1) with
    | [ Explanation.Model_row 902 ] -> true
    | _ -> false);
  check "I-X6: the pruning's derivation cites the entry it read AT THE PUSH"
    (a = b && String.length a > 0);
  check "I-X6: and it is row 901's entry, not the row that moved the bound later"
    (let contains needle hay =
       let n = String.length needle and h = String.length hay in
       let rec go i = i + n <= h && (String.sub hay i n = needle || go (i + 1)) in
       go 0
     in
     contains "901" b && not (contains "902" b))

(* ------------------------------ D-0026: one pruning, two halves that agree (M2-T8)

   The reference propagator's reason and justification used to be two calls
   ([facts_of_snaps snaps] and [explain_of_snaps _ snaps _]) that happened to be given
   the same list, kept honest by a comment. They are one call now. What can still go
   wrong is what that one function computes, so this checks the three things the comment
   used to promise and no earlier test asserts:

     1. the reason's SCOPE is exactly the row's other terms -- not the pruned variable,
        not a term that is absent from the row;
     2. each fact is the bound relevant to that term's SIGN (D-0013's case split), at the
        value the bound had when the pruning was made;
     3. the two halves agree in the sense [Store.agreement_holds] means.

   Scene: 2*x + 3*y - 2*w <= 4 over 0..5, with y's lower bound and w's upper bound each
   already moved by an earlier (placeholder) propagator, so that the row has one derived
   lower bound, one derived upper bound and one term left at its declared bound. That mix
   is what makes (1) and (2) separable: a reason built over the wrong bound direction, or
   over the wrong variable, changes the answer here and nowhere else in this file. *)
let test_d0026_linear_pairing () =
  let store = mk_store [ ("x", 0, 5); ("y", 0, 5); ("w", 0, 5); ("q", 0, 5) ] in
  let prop = Linear.make store [ (2, var 0); (3, var 1); (-2, var 2) ] 4 ~row_id:1 in
  (* y >= 2 and w <= 3, each by "some earlier propagator". [q] is in the store and NOT
     in the row: a reason that leaked the whole store's bounds rather than the row's
     scope would name it. *)
  ignore (Store.set_lo store (var 1) 2 placeholder_pruning);
  ignore (Store.set_hi store (var 2) 3 placeholder_pruning);
  let before = Store.trail_length store in
  (match Linear.propagate prop store with
  | Propagator.Conflict _ ->
      check "D-0026 linear: expected a pruning, not a conflict" false
  | Propagator.Fixpoint -> ());
  let pushed =
    List.filter
      (fun (e : Store.entry) -> Var.equal e.Store.var (var 0))
      (List.filteri
         (fun i _ -> i < Store.trail_length store - before)
         (Store.trail_entries store))
  in
  match pushed with
  | [] -> check "D-0026 linear: x was pushed" false
  | e :: _ ->
      (* slack = 4 - (2*0 + 3*2 + (-2)*3) = 4, so max(2x) = 0 + 4 and x <= 2. Asserted
         rather than assumed: this is only a test of the reason if the pruning happened,
         and x's entry is the FIRST push of the pass, so its snapshot still sees y and w
         where the setup left them. *)
      check "D-0026 linear: the pruning under test landed"
        (Domain.hi (Store.get store (var 0)) = 2);
      (* (1) The scope is the other two terms, in term order, and nothing else. *)
      check "D-0026 linear: the reason's scope is exactly the row's OTHER terms"
        (Reason.owners e.Store.reason = [ "y"; "w" ]);
      (* (2) y has a positive coefficient so its LOWER bound is read; w has a negative
         one so its UPPER bound is. Swapping the case split (break 1 in the hand-back)
         gives [y <= 2; w >= 3] here. *)
      check "D-0026 linear: each fact is the bound its term's SIGN reads, at its value"
        (Reason.lits e.Store.reason = [ Lit.ge "y" 2; Lit.le "w" 3 ]);
      (* (3) And the two halves are about the same pruning. *)
      check "D-0026 linear: the reason and the justification agree"
        (Store.agreement_holds store
           (Reason.because e.Store.reason (Store.explanation store e)))

(* The same row with every other term left at its declared bound: the reason's scope is
   still the other terms -- the propagator DID read them -- but not one of the facts
   materialises, because at a declared bound the order encoding states the constant true.
   This is the pair of properties that used to be one constructor each ([Snap_weaken]
   contributing no literal) and is now one value with two projections; a [lits] that
   forgot to drop would put a nonexistent literal in every trace line, and an [owners]
   that dropped with it would leave M2-T3 unable to see the variable at all. *)
let test_d0026_all_declared () =
  let store = mk_store [ ("x", 0, 5); ("y", 0, 5) ] in
  let prop = Linear.make store [ (2, var 0); (3, var 1) ] 6 ~row_id:1 in
  let before = Store.trail_length store in
  (match Linear.propagate prop store with
  | Propagator.Conflict _ -> check "D-0026 declared: expected a pruning" false
  | Propagator.Fixpoint -> ());
  match
    List.filteri
      (fun i _ -> i < Store.trail_length store - before)
      (Store.trail_entries store)
  with
  | [] -> check "D-0026 declared: something was pushed" false
  | e :: _ ->
      check "D-0026 declared: the scope still names the term that was read"
        (Reason.owners e.Store.reason <> []);
      check "D-0026 declared: but no fact materialises, so the tail is empty"
        (Reason.lits e.Store.reason = []);
      check "D-0026 declared: and the halves still agree"
        (Store.agreement_holds store
           (Reason.because e.Store.reason (Store.explanation store e)))

let () =
  print_endline "\npropagator unit tests";
  test_soundness ();
  test_bounds_consistency ();
  test_idempotence ();
  test_conflict ();
  test_explanation_entailment ();
  test_order_reason ();
  test_multi_step_chain ();
  test_lin_eq_soundness ();
  test_compare_soundness ();
  test_int_eq_soundness ();
  test_checking ();
  test_new_idempotence ();
  test_lin_eq_entailment ();
  test_compare_entailment ();
  test_int_eq_entailment ();
  run_veripb ~name:"int_lin_eq: multi-step chain, checked end to end"
    ~build:build_int_lin_eq_multi;
  run_veripb ~name:"int_le: multi-step chain, checked end to end"
    ~build:build_int_le_multi;
  run_veripb ~name:"int_lt: multi-step chain, checked end to end"
    ~build:build_int_lt_multi;
  run_veripb ~name:"int_eq: multi-step chain, checked end to end"
    ~build:build_int_eq_multi;
  test_lin_eq_pairing ();
  (* M1-T42 scene 2, per propagator: the D-0018 trace line against a scene whose fact is
     in the store alone, then the same claim with its facts deleted, which the checker
     must reject. The pair is the point: neither half means anything without the other. *)
  List.iter
    (fun (name, scene, line, factless_line) ->
      run_veripb
        ~name:
          (Printf.sprintf "%s: the pruning's D-0018 trace line, fact in the store" name)
        ~build:(fun dir ->
          write_trace_case dir ~file:(name ^ "_decision") ~scene ~factless:false
            ~expect_lines:[ line ]);
      run_veripb_rejects
        ~name:(Printf.sprintf "%s: the same claim with no facts at all" name)
        ~build:(fun dir ->
          write_trace_case dir ~file:(name ^ "_factless") ~scene ~factless:true
            ~expect_lines:[ factless_line ]))
    trace_builders;
  test_ne_clause_lits ();
  test_ne_rows ();
  test_ne_soundness ();
  test_ne_checking ();
  test_ne_idempotence ();
  run_veripb ~name:"int_ne: an interior hole, reason pinned interior" ~build:build_ne_hole;
  run_veripb ~name:"int_ne: a pruning at the pruned variable's declared bound"
    ~build:build_ne_bound;
  run_veripb ~name:"int_lin_ne: 2a+3b-c<>5, three terms, coefficients past +/-1"
    ~build:build_lin_ne;
  run_veripb ~name:"int_ne: the conflict clause" ~build:build_ne_conflict;
  run_veripb_rejects ~name:"int_ne: a rup claiming the wrong value"
    ~build:build_ne_hole_wrong;
  run_veripb_rejects ~name:"int_ne: a rup that claims its hole with no facts at all"
    ~build:build_ne_factless;
  run_veripb_rejects ~name:"int_lin_ne: a rup that claims its hole with no facts at all"
    ~build:build_lin_ne_factless;
  test_ne_selector ();
  run_veripb ~name:"ne_sat.fzn, wired as Compile would: solved and verified"
    ~build:build_ne_sat;
  run_veripb ~name:"int_ne inside a search that must branch: solved and verified"
    ~build:build_ne_search;
  test_checked_ops ();
  test_opb_row_wraps_identically ();
  test_propagators_raise_on_overflow ();
  test_compile_cap ();

  (* ------------------------------------------------- M2-T1 / M2-T2: the Booleans *)
  test_bool_clause_consistency ();
  test_bool_clause_checking ();
  test_bool_clause_idempotence ();
  test_bool_clause_unit_push ();
  test_bool_clause_conflict_reason ();
  test_bool_clause_empty_conflict ();
  test_bool_clause_rejects_non_bool ();
  test_bool2int_directions ();
  test_bool2int_hole ();
  test_bool2int_soundness ();
  test_bool2int_checking ();
  test_bool2int_idempotence ();
  test_bool2int_conflicts ();
  test_bool2int_rejects_non_bool ();
  test_bool_rows ();
  test_bool_ground_rows ();
  test_bool_type_rejections ();
  test_bool_instances_posted ();
  run_veripb ~name:"bool_clause: the unit push's reason, checked end to end"
    ~build:build_bool_clause_unit;
  run_veripb ~name:"bool_clause: the empty clause refutes, closed the I-X7 way"
    ~build:build_bool_clause_conflict;
  run_veripb_rejects ~name:"bool_clause: a rup claiming the wrong polarity"
    ~build:build_bool_clause_wrong;
  run_veripb_rejects
    ~name:"bool_clause: a rup that has dropped one of the clause's literals"
    ~build:build_bool_clause_weakened;
  run_veripb ~name:"bool2int: b -> x, lower bound" ~build:build_bool2int_b_to_x_lo;
  run_veripb ~name:"bool2int: b -> x, upper bound" ~build:build_bool2int_b_to_x_hi;
  run_veripb ~name:"bool2int: x -> b, lower bound" ~build:build_bool2int_x_to_b_lo;
  run_veripb ~name:"bool2int: x -> b, upper bound" ~build:build_bool2int_x_to_b_hi;
  run_veripb_rejects ~name:"bool2int: a rup claiming the wrong polarity"
    ~build:build_bool2int_wrong;
  run_veripb_rejects ~name:"bool2int: a rup that claims its bound with no facts at all"
    ~build:build_bool2int_factless;
  test_single_row_check_can_fire ();

  (* ---------------------------------------------- M2-T8 / D-0026: the two halves *)
  test_d0026_linear_pairing ();
  test_d0026_all_declared ();
  test_ix6_justification_snapshot ();
  test_no_single_row_refutes "bool_reif_unsat" "bool_reif_unsat.fzn";
  test_no_single_row_refutes "bool_channel_unsat" "bool_channel_unsat.fzn";
  if !failures > 0 then (
    Printf.printf "\n%d FAILURE(S)\n" !failures;
    exit 1)
  else print_endline "\nall propagator checks passed"
