(* Unit tests for propagators (lib/core/prop/).

   M1-T7a: the int_lin_le reference propagator (lib/core/prop/linear.ml) and the shared
   chain helper it uses (lib/core/prop/order_reason.ml, docs/DECISIONS.md D-0010).
   Follows test_core.ml's shape: a [check] counter, one function per area, exit 1 on any
   failure. See docs/INVARIANTS.md for I-P1..I-P4, which the sections below are named
   after. *)

module Domain = Baguette_core.Domain
module Store = Baguette_core.Store
module Var = Baguette_core.Var
module Explanation = Baguette_core.Explanation
module Propagator = Baguette_core.Propagator
module Linear = Baguette_core.Linear
module Order_reason = Baguette_core.Order_reason
module Lit = Baguette_proof.Lit

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

(* The constant a set of terms contributes at their *declared* bound (decl_lo for a
   non-negative coefficient, decl_hi for a negative one) - i.e. [a_i * decl_bound_i]
   summed over [indices]. A chain's [units_rhs] (D-0010) is measured *relative to*
   this constant, so recovering the "raw" quantity the propagator's own floor/ceil
   division used (docs/core/prop/linear.ml's [term_min]) needs this added back:
   raw_min_i = a_i * decl_bound_i + chain_contribution_i. *)
let const_contribution bounds terms indices =
  List.fold_left
    (fun acc idx ->
      let a, _ = List.nth terms idx in
      if a = 0 then acc
      else
        let _, lo, hi = List.nth bounds idx in
        let decl_bound = if a >= 0 then lo else hi in
        acc + (a * decl_bound))
    0 indices

let all_but bounds idx = List.filteri (fun i _ -> i <> idx) (List.mapi (fun i _ -> i) bounds)

(* Verify one [Cut (Trivial, Linear (lterms, units_rhs), 1, 1)] explanation against the
   constraint it came from: [bounds]/[terms] are the same index-aligned lists the test
   built the propagator from (declared domain and coefficient per variable, by [Var.of_int]
   position). Returns [(units_rhs, ok)] so callers can go on to check the derived bound. *)
let verify_linear_shape test_name store bounds terms lterms units_rhs =
  let ok = ref true in
  let expect cond msg =
    if not cond then ok := false;
    check (Printf.sprintf "%s: %s" test_name msg) cond
  in
  (* The row must at least be able to reach its own rhs. *)
  expect (max_attainable lterms >= units_rhs) "row can attain its own rhs";
  (* With our construction every chain step is tight, so the sum should be exact. *)
  let sum_coeffs = List.fold_left (fun acc (a, _) -> acc + a) 0 lterms in
  expect (sum_coeffs = units_rhs) "sum of coefficients matches rhs exactly";
  (* Every chain step's coefficient must be the |original coefficient| for its
     variable, and the v-sequence must be the exact contiguous run D-0010 specifies,
     relative to the *declared* bound, not the raw current one. *)
  let name_to_idx = List.mapi (fun i (n, _, _) -> (n, i)) bounds in
  let groups = Hashtbl.create 8 in
  let group_order = ref [] in
  List.iter
    (fun (a, l) ->
      let nm = Lit.owner l.Lit.v in
      if not (Hashtbl.mem groups nm) then group_order := nm :: !group_order;
      let prev = try Hashtbl.find groups nm with Not_found -> [] in
      Hashtbl.replace groups nm ((a, l) :: prev))
    lterms;
  List.iter
    (fun nm ->
      let group = List.rev (Hashtbl.find groups nm) in
      let idx = List.assoc nm name_to_idx in
      let _, decl_lo, decl_hi = List.nth bounds idx in
      let orig_coeff, _ = List.nth terms idx in
      let d = Store.get store (var idx) in
      expect
        (List.for_all (fun (a, _) -> a = abs orig_coeff) group)
        (Printf.sprintf "chain coefficients for %s match |%d|" nm orig_coeff);
      match group with
      | [] -> ()
      | (_, l0) :: _ ->
          if l0.Lit.positive then (
            (* lower-bound chain: v in decl_lo+1 .. current lo *)
            let b = Domain.lo d in
            let expected = List.init (b - decl_lo) (fun i -> decl_lo + 1 + i) in
            let actual = List.map (fun (_, l) -> decode_bound l) group in
            expect (actual = expected)
              (Printf.sprintf "lower chain for %s is decl_lo+1..%d" nm b))
          else
            (* upper-bound chain: v in current hi .. decl_hi-1 *)
            let b = Domain.hi d in
            let expected = List.init (decl_hi - b) (fun i -> b + i) in
            let actual = List.map (fun (_, l) -> decode_bound l) group in
            expect (actual = expected)
              (Printf.sprintf "upper chain for %s is %d..decl_hi-1" nm b))
    (List.rev !group_order);
  !ok

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
  let prop = Linear.make store raw_terms rhs in
  let result = Linear.propagate prop store in
  match result with
  | Propagator.Conflict _ ->
      (* Sound iff there really is no solution at all in the original box. *)
      check
        (Printf.sprintf "%s: conflict only when truly unsat" name)
        (solutions = [])
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
  check_soundness_case "3 vars, mixed signs" [ 2; -1; 3 ] 4
    [ (-3, 3); (-3, 3); (-3, 3) ];
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
  let prop = Linear.make store raw_terms rhs in
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
  let prop = Linear.make store raw_terms rhs in
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
     purpose, so the reason's chains are non-empty and worth checking - at the
     declared bounds themselves the model row alone is already infeasible and needs
     no extra literals, which would make this a degenerate test of I-P1/I-P3 conflict
     reporting but not of the chain shape. *)
  let bounds = [ ("x", 0, 3); ("y", 0, 3) ] in
  let store = mk_store bounds in
  let raw_terms = [ (2, var 0); (3, var 1) ] in
  let prop = Linear.make store raw_terms 1 in
  ignore (Store.set_lo store (var 0) 1 Explanation.trivial);
  ignore (Store.set_lo store (var 1) 1 Explanation.trivial);
  match Linear.propagate prop store with
  | Propagator.Fixpoint -> check "conflict: expected Conflict" false
  | Propagator.Conflict e ->
      let lits = Explanation.lits e in
      check "conflict: reported" true;
      check "conflict: explanation has literals" (lits <> []);
      (match Explanation.force e with
      | Explanation.Cut
          (Explanation.Trivial, Explanation.Linear (lterms, units_rhs), 1, 1) ->
          ignore (verify_linear_shape "conflict" store bounds raw_terms lterms units_rhs);
          let all_idx = List.mapi (fun i _ -> i) bounds in
          let const_all = const_contribution bounds raw_terms all_idx in
          check "conflict: numeric contradiction (c - const - units_rhs < 0)"
            (1 - const_all - units_rhs < 0);
          check "conflict: covers every term"
            (Hashtbl.length
               (let h = Hashtbl.create 8 in
                List.iter (fun (_, l) -> Hashtbl.replace h (Lit.owner l.Lit.v) ()) lterms;
                h)
            = List.length raw_terms)
      | _ -> check "conflict: unexpected explanation shape" false)

(* ---------------------------------------------------------- explanation entailment *)

(* Runs the propagator once, then inspects every trail entry it created: force the
   explanation and check, by direct arithmetic over the term list (not string
   comparison), that it really does entail the bound that got pushed - including that
   the row can attain its own rhs at all (docs/DECISIONS.md D-0010) and that every
   chain is the exact declared-bound-relative sequence. *)
let check_entailment_case name coeffs rhs bounds =
  let store = mk_store bounds in
  let raw_terms = List.mapi (fun i a -> (a, var i)) coeffs in
  let prop = Linear.make store raw_terms rhs in
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
          let a =
            match List.find_opt (fun (_, x) -> Var.equal x e.var) raw_terms with
            | Some (a, _) -> a
            | None -> failwith "entailment test: var not in constraint"
          in
          let expl = Explanation.force (Store.explanation store e) in
          match expl with
          | Explanation.Cut
              (Explanation.Trivial, Explanation.Linear (lterms, units_rhs), 1, 1) ->
              let shape_ok =
                verify_linear_shape name store bounds raw_terms lterms units_rhs
              in
              (* The Linear part must exclude exactly the pushed variable. *)
              check
                (Printf.sprintf "%s: pushed var absent from its own reason" name)
                (not
                   (List.exists
                      (fun (_, l) -> Lit.owner l.Lit.v = Store.name store e.var)
                      lterms));
              if shape_ok then begin
                let pushed_idx =
                  match
                    List.find_opt (fun i -> Var.equal (var i) e.var)
                      (List.mapi (fun i _ -> i) bounds)
                  with
                  | Some i -> i
                  | None -> failwith "entailment test: pushed var not found by index"
                in
                let const_others =
                  const_contribution bounds raw_terms (all_but bounds pushed_idx)
                in
                let max_term = rhs - const_others - units_rhs in
                let d_now = Store.get store e.var in
                if a > 0 then
                  check
                    (Printf.sprintf "%s: pushed hi matches floor division" name)
                    (Domain.hi d_now = Linear.floordiv max_term a)
                else if a < 0 then
                  check
                    (Printf.sprintf "%s: pushed lo matches ceil division" name)
                    (Domain.lo d_now = Linear.ceildiv max_term a)
                else
                  check (Printf.sprintf "%s: zero coefficient never pushes" name) false
              end
          | _ -> check (Printf.sprintf "%s: unexpected explanation shape" name) false)
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

(* End-to-end: a variable's bound is moved *before* the propagator's own [make] would
   see it as anything but declared - simulating an earlier propagator's pruning - so
   that when it is later used in someone else's reason, it is more than one step away
   from its declared bound. The point is exactly what D-0010 got wrong: a one-step
   bound looked fine, a multi-step one was rejected by veripb outright. *)
let test_multi_step_chain () =
  (* Lower-bound case: x's declared domain is [-5, 5]; before propagating, x is
     already known to be >= 2 (a gap of 7 from its declared lo). y's push must then
     cite the full 7-literal chain for x, not a single "x >= 2" literal. *)
  let bounds = [ ("x", -5, 5); ("y", -5, 5) ] in
  let store = mk_store bounds in
  let raw_terms = [ (1, var 0); (1, var 1) ] in
  let prop = Linear.make store raw_terms 2 in
  (match Store.set_lo store (var 0) 2 Explanation.trivial with
  | Store.Changed -> ()
  | _ -> check "multi-step lower: setup prune applied" false);
  let before = Store.trail_length store in
  (match Linear.propagate prop store with
  | Propagator.Conflict _ -> check "multi-step lower: expected Fixpoint" false
  | Propagator.Fixpoint ->
      let after = Store.trail_length store in
      let entries =
        List.filteri (fun i _ -> i < after - before) (Store.trail_entries store)
      in
      let y_entry =
        List.find_opt (fun (e : Store.entry) -> Var.equal e.var (var 1)) entries
      in
      (match y_entry with
      | None -> check "multi-step lower: y was pushed" false
      | Some e -> (
          match Explanation.force (Store.explanation store e) with
          | Explanation.Cut
              (Explanation.Trivial, Explanation.Linear (lterms, units_rhs), 1, 1) ->
              ignore (verify_linear_shape "multi-step lower" store bounds raw_terms
                        lterms units_rhs);
              let x_terms =
                List.filter (fun (_, l) -> Lit.owner l.Lit.v = "x") lterms
              in
              check "multi-step lower: x's chain has more than one literal"
                (List.length x_terms > 1);
              check "multi-step lower: x's chain is exactly 7 literals"
                (List.length x_terms = 7);
              check "multi-step lower: x's chain values are -4..2"
                (List.map (fun (_, l) -> decode_bound l) x_terms
                = [ -4; -3; -2; -1; 0; 1; 2 ])
          | _ -> check "multi-step lower: unexpected explanation shape" false)));

  (* Symmetric upper-bound case: x's declared domain is [-5, 5]; x is already known to
     be <= -3 (a gap of 8 from its declared hi). The constraint uses a negative
     coefficient on x so its *minimum* is driven by the upper bound. *)
  let bounds2 = [ ("x", -5, 5); ("y", -5, 5) ] in
  let store2 = mk_store bounds2 in
  let raw_terms2 = [ (-1, var 0); (1, var 1) ] in
  let prop2 = Linear.make store2 raw_terms2 (-2) in
  (match Store.set_hi store2 (var 0) (-3) Explanation.trivial with
  | Store.Changed -> ()
  | _ -> check "multi-step upper: setup prune applied" false);
  let before2 = Store.trail_length store2 in
  match Linear.propagate prop2 store2 with
  | Propagator.Conflict _ -> check "multi-step upper: expected Fixpoint" false
  | Propagator.Fixpoint ->
      let after2 = Store.trail_length store2 in
      let entries =
        List.filteri (fun i _ -> i < after2 - before2) (Store.trail_entries store2)
      in
      let y_entry =
        List.find_opt (fun (e : Store.entry) -> Var.equal e.var (var 1)) entries
      in
      (match y_entry with
      | None -> check "multi-step upper: y was pushed" false
      | Some e -> (
          match Explanation.force (Store.explanation store2 e) with
          | Explanation.Cut
              (Explanation.Trivial, Explanation.Linear (lterms, units_rhs), 1, 1) ->
              ignore
                (verify_linear_shape "multi-step upper" store2 bounds2 raw_terms2 lterms
                   units_rhs);
              let x_terms =
                List.filter (fun (_, l) -> Lit.owner l.Lit.v = "x") lterms
              in
              check "multi-step upper: x's chain has more than one literal"
                (List.length x_terms > 1);
              check "multi-step upper: x's chain is exactly 8 literals"
                (List.length x_terms = 8);
              check "multi-step upper: x's chain values are -3..4"
                (List.map (fun (_, l) -> decode_bound l) x_terms
                = [ -3; -2; -1; 0; 1; 2; 3; 4 ])
          | _ -> check "multi-step upper: unexpected explanation shape" false))

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
  if !failures > 0 then (
    Printf.printf "\n%d FAILURE(S)\n" !failures;
    exit 1)
  else print_endline "\nall propagator checks passed"
