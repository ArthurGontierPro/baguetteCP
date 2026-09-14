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

let failures = ref 0

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
  ignore (Store.set_lo store (var 0) 1 Explanation.trivial);
  ignore (Store.set_lo store (var 1) 1 Explanation.trivial);
  match Linear.propagate prop store with
  | Propagator.Fixpoint -> check "conflict: expected Conflict" false
  | Propagator.Conflict e ->
      (* [Explanation.lits] walks into [Combine]'s [Weaken] summands but not into a
         [Term]'s cited explanation until *that* is forced -- and here both x and y
         are cited via the placeholder [Explanation.trivial] (standing in for "some
         earlier propagator already established this"), which carries no literals
         of its own (docs/core/explanation.ml: [Trivial] is the model row itself, an
         indivisible reference, not a set of literals to enumerate). An empty result
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
      pushing it with [Explanation.trivial] before running this propagator, standing
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
        match set store (var 0) bound Explanation.trivial with
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
      (fun i v -> ignore (Store.fix store (var i) v Explanation.trivial))
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
      (fun i v -> ignore (Store.fix store (var i) v Explanation.trivial))
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
   ignore (Store.set_lo store (var 0) 2 Explanation.trivial);
   let before = Store.trail_length store in
   match Int_le.propagate prop store with
   | Propagator.Conflict _ -> check "int_le entailment: expected Fixpoint" false
   | Propagator.Fixpoint ->
       check_all_entries_shape "int_le entailment" store bounds terms before);
  let terms_lt = [ (1, var 0); (-1, var 1) ] in
  let store2 = mk_store bounds in
  let prop2 = Int_lt.make store2 (var 0) (var 1) ~row_id:1 in
  ignore (Store.set_lo store2 (var 0) 2 Explanation.trivial);
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
  ignore (Store.set_hi store (var 1) 1 Explanation.trivial);
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

let veripb_path () =
  let candidates =
    [
      Filename.concat
        (Sys.getenv_opt "HOME" |> Option.value ~default:"")
        ".local/bin/veripb";
    ]
  in
  match List.find_opt Sys.file_exists candidates with
  | Some p -> Some p
  | None ->
      if Sys.command "command -v veripb >/dev/null 2>&1" = 0 then Some "veripb" else None

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
  (match Store.set_hi store (Var.of_int 1) 2 (Explanation.model_row c_x2_le) with
  | Store.Changed -> ()
  | _ -> failwith "build_int_lin_eq_multi: x2 <= 2 setup failed");
  (match Store.set_lo store (Var.of_int 1) 2 (Explanation.model_row c_x2_ge) with
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
  let ctx = Justify.create ~writer:w ~encoding:e ~model_id:(fun () -> geq_id) in
  let id = Justify.emit ctx expl in
  Writer.delete w id;
  Writer.conclusion w (Writer.Sat (Encoding.assignment_lits e [ ("x1", 2); ("x2", 2) ]));
  close_out oc;
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
  (match Store.set_lo store (Var.of_int 0) 3 (Explanation.model_row c_bound) with
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
  let ctx = Justify.create ~writer:w ~encoding:e ~model_id:(fun () -> model_row) in
  let id = Justify.emit ctx expl in
  Writer.delete w id;
  Writer.conclusion w (Writer.Sat (Encoding.assignment_lits e [ ("x", 3); ("y", 3) ]));
  close_out oc;
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
  (match Store.set_lo store (Var.of_int 0) 3 (Explanation.model_row c_bound) with
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
  let ctx = Justify.create ~writer:w ~encoding:e ~model_id:(fun () -> model_row) in
  let id = Justify.emit ctx expl in
  Writer.delete w id;
  Writer.conclusion w (Writer.Sat (Encoding.assignment_lits e [ ("x", 3); ("y", 4) ]));
  close_out oc;
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
  (match Store.set_hi store (Var.of_int 1) 2 (Explanation.model_row c_bound) with
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
  let ctx = Justify.create ~writer:w ~encoding:e ~model_id:(fun () -> leq_id) in
  let id = Justify.emit ctx expl in
  Writer.delete w id;
  Writer.conclusion w (Writer.Sat (Encoding.assignment_lits e [ ("x", 2); ("y", 2) ]));
  close_out oc;
  (opb, pbp)

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
   into every explanation it ever builds, so there is no [ctx.model_id] left for a
   caller to get wrong. The check below asserts exactly that -- [ctx]'s own
   [model_id] is a thunk that fails if ever called, and the proof still verifies,
   which is only possible if [expl] never once needed it. *)
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
    (match Store.set_lo store (Var.of_int 1) 2 (Explanation.model_row c_bound) with
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
    let ctx =
      Justify.create ~writer:w ~encoding:e ~model_id:(fun () ->
          failwith
            "test_lin_eq_pairing: ctx.model_id was consulted -- expl's base should be \
             Model_row leq_id, not Trivial")
    in
    let id = Justify.emit ctx expl in
    Writer.delete w id;
    Writer.conclusion w (Writer.Sat (Encoding.assignment_lits e [ ("x1", 2); ("x2", 2) ]));
    close_out oc;
    (opb, pbp)
  in
  run_veripb
    ~name:
      "D-0011 pairing: le's explanation never touches ctx.model_id (Model_row supersedes \
       Trivial) and still verifies"
    ~build

(* ------------------------------------------------------------------------ main *)

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
  if !failures > 0 then (
    Printf.printf "\n%d FAILURE(S)\n" !failures;
    exit 1)
  else print_endline "\nall propagator checks passed"
