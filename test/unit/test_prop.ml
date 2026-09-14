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
      ~make:(fun store -> Lin_eq.make store (List.mapi (fun i a -> (a, var i)) coeffs) rhs)
      ~propagate:propagate_pair ~n:(List.length coeffs) ~ranges
      ~satisfies:(fun a -> List.fold_left2 (fun acc c v -> acc + (c * v)) 0 coeffs a = rhs)
  in
  case "int_lin_eq: 2 vars, positive coeffs" [ 1; 1 ] 2 [ (-3, 3); (-3, 3) ];
  case "int_lin_eq: 2 vars, one negative coeff" [ 1; -1 ] 0 [ (-3, 3); (-3, 3) ];
  case "int_lin_eq: 3 vars, mixed signs" [ 2; -1; 3 ] 4 [ (-3, 3); (-3, 3); (-3, 3) ];
  case "int_lin_eq: 3 vars, one zero coeff" [ 1; 0; -2 ] 1 [ (-2, 2); (-2, 2); (-2, 2) ];
  case "int_lin_eq: all-negative coeffs" [ -2; -3 ] (-5) [ (-3, 3); (-3, 3) ];
  case "int_lin_eq: unsatisfiable target" [ 1; 1; 1 ] (-20) [ (-3, 3); (-3, 3); (-3, 3) ]

let test_compare_soundness () =
  let case name make propagate rel ranges =
    check_generic_soundness name ~make ~propagate ~n:2 ~ranges
      ~satisfies:(fun a -> match a with [ x; y ] -> rel x y | _ -> false)
  in
  case "int_le: overlapping ranges"
    (fun store -> Int_le.make store (var 0) (var 1))
    Int_le.propagate ( <= ) [ (-3, 3); (-3, 3) ];
  case "int_le: disjoint, x strictly above y's range"
    (fun store -> Int_le.make store (var 0) (var 1))
    Int_le.propagate ( <= ) [ (2, 5); (-5, -2) ];
  case "int_lt: overlapping ranges"
    (fun store -> Int_lt.make store (var 0) (var 1))
    Int_lt.propagate ( < ) [ (-3, 3); (-3, 3) ];
  case "int_lt: touching ranges (x may equal y's lo, still < possible)"
    (fun store -> Int_lt.make store (var 0) (var 1))
    Int_lt.propagate ( < ) [ (0, 3); (0, 3) ]

let test_int_eq_soundness () =
  let case name ranges =
    check_generic_soundness name
      ~make:(fun store -> Int_eq.make store (var 0) (var 1))
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
    let prop = Lin_eq.make store (List.mapi (fun i a -> (a, var i)) coeffs) rhs in
    List.iteri
      (fun i v -> ignore (Store.fix store (var i) v Explanation.trivial))
      fix_values;
    match propagate_pair prop store with
    | Propagator.Conflict _ -> check label expect_conflict
    | Propagator.Fixpoint -> check label (not expect_conflict)
  in
  run_eq [ ("x", 0, 3); ("y", 0, 3) ] [ 1; 1 ] 3 [ 1; 2 ] false
    "I-P3 int_lin_eq: satisfying fixed assignment is not a conflict";
  run_eq [ ("x", 0, 3); ("y", 0, 3) ] [ 1; 1 ] 3 [ 1; 3 ] true
    "I-P3 int_lin_eq: violating fixed assignment is a conflict";
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
    (fun store -> Int_le.make store (var 0) (var 1))
    Int_le.propagate [ ("x", 0, 5); ("y", 0, 5) ] [ 2; 2 ] false
    "I-P3 int_le: x=2,y=2 (x<=y holds) is not a conflict";
  run_le
    (fun store -> Int_le.make store (var 0) (var 1))
    Int_le.propagate [ ("x", 0, 5); ("y", 0, 5) ] [ 3; 2 ] true
    "I-P3 int_le: x=3,y=2 (x<=y violated) is a conflict";
  run_le
    (fun store -> Int_lt.make store (var 0) (var 1))
    Int_lt.propagate [ ("x", 0, 5); ("y", 0, 5) ] [ 2; 3 ] false
    "I-P3 int_lt: x=2,y=3 (x<y holds) is not a conflict";
  run_le
    (fun store -> Int_lt.make store (var 0) (var 1))
    Int_lt.propagate [ ("x", 0, 5); ("y", 0, 5) ] [ 2; 2 ] true
    "I-P3 int_lt: x=2,y=2 (x<y violated) is a conflict";
  run_le
    (fun store -> Int_eq.make store (var 0) (var 1))
    propagate_pair [ ("x", 0, 5); ("y", 0, 5) ] [ 3; 3 ] false
    "I-P3 int_eq: x=3,y=3 is not a conflict";
  run_le
    (fun store -> Int_eq.make store (var 0) (var 1))
    propagate_pair [ ("x", 0, 5); ("y", 0, 5) ] [ 3; 4 ] true
    "I-P3 int_eq: x=3,y=4 is a conflict"

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
    (fun store -> Lin_eq.make store [ (2, var 0); (-1, var 1); (3, var 2) ] 4)
    propagate_pair
    [ ("x", -3, 3); ("y", -3, 3); ("z", -3, 3) ];
  run_twice "int_le"
    (fun store -> Int_le.make store (var 0) (var 1))
    Int_le.propagate [ ("x", -3, 3); ("y", -3, 3) ];
  run_twice "int_lt"
    (fun store -> Int_lt.make store (var 0) (var 1))
    Int_lt.propagate [ ("x", -3, 3); ("y", -3, 3) ];
  run_twice "int_eq"
    (fun store -> Int_eq.make store (var 0) (var 1))
    propagate_pair [ ("x", -5, 5); ("y", -2, 8) ]

(* ------------------------------------------------- explanation shape, per pruning *)

(* Runs [propagate] once and checks every trail entry it created has a
   [Cut (Trivial, Linear (...), 1, 1)] explanation whose [Linear] child passes
   [verify_linear_shape] -- which starts with the max-attainable guard (I-D0010's
   check): a row that cannot reach its own rhs is unsatisfiable and no proof state
   accepts it. *)
let check_all_entries_shape name store bounds terms before =
  let after = Store.trail_length store in
  check (Printf.sprintf "%s: at least one pruning happened" name) (after > before);
  let entries = Store.trail_entries store in
  let new_entries = List.filteri (fun i _ -> i < after - before) entries in
  List.iter
    (fun (e : Store.entry) ->
      match Explanation.force (Store.explanation store e) with
      | Explanation.Cut
          (Explanation.Trivial, Explanation.Linear (lterms, units_rhs), 1, 1) ->
          ignore (verify_linear_shape name store bounds terms lterms units_rhs)
      | Explanation.Trivial ->
          (* A pruning whose reason needed no extra bound facts at all (units_rhs = 0,
             the model constraint alone suffices) can legitimately force straight to
             [Trivial] if a caller ever short-circuits [Cut (Trivial, Linear([],0),1,1)]
             -- none of these propagators do that, so seeing this would itself be
             worth investigating, but it is not a shape violation per se. *)
          check (Printf.sprintf "%s: unexpected bare Trivial reason" name) false
      | _ -> check (Printf.sprintf "%s: unexpected explanation shape" name) false)
    new_entries

let test_lin_eq_entailment () =
  let bounds = [ ("x", -3, 3); ("y", -3, 3); ("z", -3, 3) ] in
  let terms = [ (2, var 0); (-1, var 1); (3, var 2) ] in
  let store = mk_store bounds in
  let prop = Lin_eq.make store terms 4 in
  let before = Store.trail_length store in
  (match propagate_pair prop store with
  | Propagator.Conflict _ -> check "int_lin_eq entailment: expected Fixpoint" false
  | Propagator.Fixpoint -> check_all_entries_shape "int_lin_eq entailment" store bounds
                              terms before)

let test_compare_entailment () =
  let bounds = [ ("x", -5, 5); ("y", -5, 5) ] in
  let terms = [ (1, var 0); (-1, var 1) ] in
  (let store = mk_store bounds in
   ignore (Store.set_lo store (var 0) 2 Explanation.trivial);
   let prop = Int_le.make store (var 0) (var 1) in
   let before = Store.trail_length store in
   match Int_le.propagate prop store with
   | Propagator.Conflict _ -> check "int_le entailment: expected Fixpoint" false
   | Propagator.Fixpoint ->
       check_all_entries_shape "int_le entailment" store bounds terms before);
  let terms_lt = [ (1, var 0); (-1, var 1) ] in
  let store2 = mk_store bounds in
  ignore (Store.set_lo store2 (var 0) 2 Explanation.trivial);
  let prop2 = Int_lt.make store2 (var 0) (var 1) in
  let before2 = Store.trail_length store2 in
  match Int_lt.propagate prop2 store2 with
  | Propagator.Conflict _ -> check "int_lt entailment: expected Fixpoint" false
  | Propagator.Fixpoint ->
      check_all_entries_shape "int_lt entailment" store2 bounds terms_lt before2

let test_int_eq_entailment () =
  let bounds = [ ("x", -5, 5); ("y", -5, 5) ] in
  let terms = [ (1, var 0); (-1, var 1) ] in
  let store = mk_store bounds in
  ignore (Store.set_hi store (var 1) 1 Explanation.trivial);
  let prop = Int_eq.make store (var 0) (var 1) in
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

(* Pull the [Cut (Trivial, lin, 1, 1)]'s [Linear] child out of a forced explanation,
   failing loudly (not silently skipping) if the shape is ever something else -- a
   veripb build that quietly emitted nothing for the wrong reason would be worse than
   one that crashes here. *)
let linear_child_of expl =
  match expl with
  | Explanation.Cut (Explanation.Trivial, lin, 1, 1) -> lin
  | _ -> failwith "linear_child_of: unexpected explanation shape"

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
  ignore c_x2_le;
  ignore c_x2_ge;
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
  let le, ge = Lin_eq.make store [ (1, Var.of_int 0); (1, Var.of_int 1) ] 4 in
  (match Store.set_hi store (Var.of_int 1) 2 Explanation.trivial with
  | Store.Changed -> ()
  | _ -> failwith "build_int_lin_eq_multi: x2 <= 2 setup failed");
  (match Store.set_lo store (Var.of_int 1) 2 Explanation.trivial with
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
  let entries = List.filteri (fun i _ -> i < after - before) (Store.trail_entries store) in
  let entry =
    match
      List.find_opt (fun (en : Store.entry) -> Var.equal en.var (Var.of_int 0)) entries
    with
    | Some en -> en
    | None -> failwith "build_int_lin_eq_multi: x1's bound was never pushed by ge"
  in
  let expl = Explanation.force (Store.explanation store entry) in
  let linear_child = linear_child_of expl in
  let oc = open_out pbp in
  let w = Writer.create ~comments:true ~audit:true oc in
  Encoding.start_proof e w;
  let ctx = Justify.create ~writer:w ~encoding:e ~model_id:(fun () -> geq_id) in
  let id_linear = Justify.emit ctx linear_child in
  let id_cut = Justify.emit ctx expl in
  Writer.delete_many w [ id_linear; id_cut ];
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
  ignore c_bound;
  let model_row = Encoding.add_int_lin_le e [ (1, "x"); (-1, "y") ] 0 in
  let opb = Filename.concat dir "intle_multi.opb" in
  let pbp = Filename.concat dir "intle_multi.pbp" in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "x <= y; x >= 3 (established)" ] e oc;
  close_out oc;
  let store =
    Store.create ~names:[| "x"; "y" |] ~domains:[| Domain.make 0 5; Domain.make 0 5 |]
  in
  let prop = Int_le.make store (Var.of_int 0) (Var.of_int 1) in
  (match Store.set_lo store (Var.of_int 0) 3 Explanation.trivial with
  | Store.Changed -> ()
  | _ -> failwith "build_int_le_multi: x >= 3 setup failed");
  let before = Store.trail_length store in
  (match Int_le.propagate prop store with
  | Propagator.Conflict _ -> failwith "build_int_le_multi: propagate conflicted"
  | Propagator.Fixpoint -> ());
  let after = Store.trail_length store in
  let entries = List.filteri (fun i _ -> i < after - before) (Store.trail_entries store) in
  let entry =
    match
      List.find_opt (fun (en : Store.entry) -> Var.equal en.var (Var.of_int 1)) entries
    with
    | Some en -> en
    | None -> failwith "build_int_le_multi: y's bound was never pushed"
  in
  let expl = Explanation.force (Store.explanation store entry) in
  let linear_child = linear_child_of expl in
  let oc = open_out pbp in
  let w = Writer.create ~comments:true ~audit:true oc in
  Encoding.start_proof e w;
  let ctx = Justify.create ~writer:w ~encoding:e ~model_id:(fun () -> model_row) in
  let id_linear = Justify.emit ctx linear_child in
  let id_cut = Justify.emit ctx expl in
  Writer.delete_many w [ id_linear; id_cut ];
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
  ignore c_bound;
  let model_row = Encoding.add_int_lin_le e [ (1, "x"); (-1, "y") ] (-1) in
  let opb = Filename.concat dir "intlt_multi.opb" in
  let pbp = Filename.concat dir "intlt_multi.pbp" in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "x < y; x >= 3 (established)" ] e oc;
  close_out oc;
  let store =
    Store.create ~names:[| "x"; "y" |] ~domains:[| Domain.make 0 5; Domain.make 0 5 |]
  in
  let prop = Int_lt.make store (Var.of_int 0) (Var.of_int 1) in
  (match Store.set_lo store (Var.of_int 0) 3 Explanation.trivial with
  | Store.Changed -> ()
  | _ -> failwith "build_int_lt_multi: x >= 3 setup failed");
  let before = Store.trail_length store in
  (match Int_lt.propagate prop store with
  | Propagator.Conflict _ -> failwith "build_int_lt_multi: propagate conflicted"
  | Propagator.Fixpoint -> ());
  let after = Store.trail_length store in
  let entries = List.filteri (fun i _ -> i < after - before) (Store.trail_entries store) in
  let entry =
    match
      List.find_opt (fun (en : Store.entry) -> Var.equal en.var (Var.of_int 1)) entries
    with
    | Some en -> en
    | None -> failwith "build_int_lt_multi: y's bound was never pushed"
  in
  let expl = Explanation.force (Store.explanation store entry) in
  let linear_child = linear_child_of expl in
  let oc = open_out pbp in
  let w = Writer.create ~comments:true ~audit:true oc in
  Encoding.start_proof e w;
  let ctx = Justify.create ~writer:w ~encoding:e ~model_id:(fun () -> model_row) in
  let id_linear = Justify.emit ctx linear_child in
  let id_cut = Justify.emit ctx expl in
  Writer.delete_many w [ id_linear; id_cut ];
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
  ignore c_bound;
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
  let le, _ge = Int_eq.make store (Var.of_int 0) (Var.of_int 1) in
  (match Store.set_hi store (Var.of_int 1) 2 Explanation.trivial with
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
  let entries = List.filteri (fun i _ -> i < after - before) (Store.trail_entries store) in
  let entry =
    match
      List.find_opt (fun (en : Store.entry) -> Var.equal en.var (Var.of_int 0)) entries
    with
    | Some en -> en
    | None -> failwith "build_int_eq_multi: x's bound was never pushed by le"
  in
  let expl = Explanation.force (Store.explanation store entry) in
  let linear_child = linear_child_of expl in
  let oc = open_out pbp in
  let w = Writer.create ~comments:true ~audit:true oc in
  Encoding.start_proof e w;
  let ctx = Justify.create ~writer:w ~encoding:e ~model_id:(fun () -> leq_id) in
  let id_linear = Justify.emit ctx linear_child in
  let id_cut = Justify.emit ctx expl in
  Writer.delete_many w [ id_linear; id_cut ];
  Writer.conclusion w (Writer.Sat (Encoding.assignment_lits e [ ("x", 2); ("y", 2) ]));
  close_out oc;
  (opb, pbp)

(* ============================================================================
   D-0011: pairing. [Lin_eq.make]/[Int_eq.make] hand back TWO instances precisely so
   that each one justifies against exactly one model row, with nothing downstream ever
   having to inspect an explanation to guess which row it meant. The two checks below
   pin that property down directly, on [Lin_eq] (the general case; [Int_eq] is its
   two-variable specialisation and shares the same [Trivial]-resolution mechanics, so
   it does not need its own copy of this):

   1. [le]'s explanation, justified against [le]'s own row (the `<=` id from
      [Encoding.add_equality]), must verify -- this is just the ordinary case,
      asserted here to have a controlled baseline for (2).
   2. The SAME explanation, justified against [ge]'s row (the `>=` id) instead -- the
      pairing D-0011 exists to rule out -- is checked against veripb to see whether the
      checker itself catches the mismatch. *)

(* Shared setup: x1 + x2 = 4, x1/x2 declared [0,5], x2 established >= 2 by a genuine
   model constraint (one fact; the encoding's own consistency chain supplies
   "x2 >= 1"). Running [le] (the `<=` half) pushes hi(x1) to 2, citing x2's two-literal
   lower chain -- more than the one-step case D-0010 shows a suite can miss. Returns
   both ids from [Encoding.add_equality] so a caller can pick the right one, or -- for
   test (2) above -- deliberately the wrong one. *)
let setup_lin_eq_pairing dir tag =
  let e = Encoding.create () in
  Encoding.declare_int e "x1" ~lo:0 ~hi:5;
  Encoding.declare_int e "x2" ~lo:0 ~hi:5;
  let c_bound = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "x2" 2) ] 1) in
  ignore c_bound;
  let opb_terms, const = Encoding.linear_terms_int_lin_le e [ (1, "x1"); (1, "x2") ] in
  let geq_id, leq_id = Encoding.add_equality e opb_terms (4 - const) in
  let opb = Filename.concat dir (tag ^ ".opb") in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "x1 + x2 = 4; x2 >= 2 (established)" ] e oc;
  close_out oc;
  let store =
    Store.create ~names:[| "x1"; "x2" |] ~domains:[| Domain.make 0 5; Domain.make 0 5 |]
  in
  let le, _ge = Lin_eq.make store [ (1, Var.of_int 0); (1, Var.of_int 1) ] 4 in
  (match Store.set_lo store (Var.of_int 1) 2 Explanation.trivial with
  | Store.Changed -> ()
  | _ -> failwith "setup_lin_eq_pairing: x2 >= 2 setup failed");
  let before = Store.trail_length store in
  (match Linear.propagate le store with
  | Propagator.Conflict _ -> failwith "setup_lin_eq_pairing: le pass conflicted"
  | Propagator.Fixpoint -> ());
  let after = Store.trail_length store in
  let entries = List.filteri (fun i _ -> i < after - before) (Store.trail_entries store) in
  let entry =
    match
      List.find_opt (fun (en : Store.entry) -> Var.equal en.var (Var.of_int 0)) entries
    with
    | Some en -> en
    | None -> failwith "setup_lin_eq_pairing: x1's bound was never pushed by le"
  in
  let expl = Explanation.force (Store.explanation store entry) in
  (e, leq_id, geq_id, opb, expl, linear_child_of expl)

(* (1): [le]'s explanation against [le]'s own row (leq_id). The correct pairing. *)
let build_lin_eq_pairing_ok dir =
  let e, leq_id, _geq_id, opb, expl, linear_child =
    setup_lin_eq_pairing dir "linteq_pair_ok"
  in
  let pbp = Filename.concat dir "linteq_pair_ok.pbp" in
  let oc = open_out pbp in
  let w = Writer.create ~comments:true ~audit:true oc in
  Encoding.start_proof e w;
  let ctx = Justify.create ~writer:w ~encoding:e ~model_id:(fun () -> leq_id) in
  let id_linear = Justify.emit ctx linear_child in
  let id_cut = Justify.emit ctx expl in
  Writer.delete_many w [ id_linear; id_cut ];
  Writer.conclusion w (Writer.Sat (Encoding.assignment_lits e [ ("x1", 2); ("x2", 2) ]));
  close_out oc;
  (opb, pbp)

(* (2): the SAME [le] explanation, cited against [ge]'s row (geq_id) instead -- the
   mismatch D-0011 says must never happen, deliberately constructed to see whether
   veripb itself catches it. *)
let build_lin_eq_pairing_wrong dir =
  let e, _leq_id, geq_id, opb, expl, linear_child =
    setup_lin_eq_pairing dir "linteq_pair_wrong"
  in
  let pbp = Filename.concat dir "linteq_pair_wrong.pbp" in
  let oc = open_out pbp in
  let w = Writer.create ~comments:true ~audit:true oc in
  Encoding.start_proof e w;
  let ctx = Justify.create ~writer:w ~encoding:e ~model_id:(fun () -> geq_id) in
  let id_linear = Justify.emit ctx linear_child in
  let id_cut = Justify.emit ctx expl in
  Writer.delete_many w [ id_linear; id_cut ];
  Writer.conclusion w (Writer.Sat (Encoding.assignment_lits e [ ("x1", 2); ("x2", 2) ]));
  close_out oc;
  (opb, pbp)

(* Like [run_veripb], but returns the outcome instead of counting a rejection as a
   test failure -- used only for (2) above, where a rejection is what we are hoping to
   see and an accept is a finding to report rather than a bug in this test suite.
   [None] means veripb was not found (the earlier [run_veripb] call already reports
   that as a failure once; this probe just avoids reporting it a second time). *)
let veripb_accepts ~build =
  match veripb_path () with
  | None -> None
  | Some veripb ->
      let dir = Filename.temp_file "baguette_prop_veripb_probe" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      let opb, pbp = build dir in
      let log = Filename.concat dir "log" in
      let rc =
        Sys.command
          (Printf.sprintf "%s %s %s > %s 2>&1" (Filename.quote veripb)
             (Filename.quote opb) (Filename.quote pbp) (Filename.quote log))
      in
      List.iter (fun f -> try Sys.remove f with _ -> ()) [ opb; pbp; log ];
      (try Sys.rmdir dir with _ -> ());
      Some (rc = 0)

let test_lin_eq_pairing () =
  run_veripb
    ~name:"D-0011 pairing: le's explanation against its OWN row verifies"
    ~build:build_lin_eq_pairing_ok;
  match veripb_accepts ~build:build_lin_eq_pairing_wrong with
  | None -> ()
  | Some false ->
      check
        "D-0011 pairing: le's explanation against the WRONG (ge) row is rejected by \
         veripb"
        true
  | Some true ->
      Printf.printf
        "NOTE D-0011 pairing: veripb ACCEPTS le's explanation cited against the wrong \
         (ge) row too. A `pol` combination of two valid ids is unconditionally sound \
         cutting-planes reasoning regardless of which valid ids they are, and the \
         derived id here is never used for anything (it is deleted right after, and \
         `conclusion SAT` only checks the assignment against the *original* model, not \
         against anything this derivation proved) -- so nothing in this proof's \
         acceptance actually depends on Trivial resolving to the *right* row. The \
         checker does not enforce the pairing D-0011 requires; only discipline in this \
         codebase does. Recorded as a finding, not a test failure.\n"

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
