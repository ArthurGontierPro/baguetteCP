(* Unit tests for propagators (lib/core/prop/).

   M1-T7a: the int_lin_le reference propagator (lib/core/prop/linear.ml). Follows
   test_core.ml's shape: a [check] counter, one function per area, exit 1 on any
   failure. See docs/INVARIANTS.md for I-P1..I-P4, which the sections below are named
   after. *)

module Domain = Baguette_core.Domain
module Store = Baguette_core.Store
module Var = Baguette_core.Var
module Explanation = Baguette_core.Explanation
module Propagator = Baguette_core.Propagator
module Linear = Baguette_core.Linear
module Lit = Baguette_proof.Lit

let failures = ref 0

let check name cond =
  if cond then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s\n" name)

(* ------------------------------------------------------------------- helpers *)

let mk_store bounds =
  (* [bounds] : (name, lo, hi) list, one per variable, in Var.of_int order. *)
  let names = Array.of_list (List.map (fun (n, _, _) -> n) bounds) in
  let domains =
    Array.of_list (List.map (fun (_, lo, hi) -> Domain.make lo hi) bounds)
  in
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

(* Decode the bound value an order-encoding literal names, undoing the [le] encoding's
   +1 shift (lib/proof/lit.ml: [le x v = neg (Ge (x, v + 1))]). *)
let decode_bound (l : Lit.t) =
  match l.Lit.v with
  | Lit.Ge (_, v) -> if l.Lit.positive then v else v - 1
  | Lit.Eq (_, v) -> v

(* ---------------------------------------------------------- I-P1: soundness *)

(* Brute force: enumerate every assignment within the *original* box, compute which
   values of each variable have support (extend to a full solution of the constraint
   over that same box), run the propagator once, and check every value it kept a bound
   for is consistent with - and every value it excluded had no - support. Bounds-only
   propagation can only report a value absent by moving lo/hi past it, so "excluded" is
   simply "outside the propagated [lo, hi]". *)
let check_soundness_case name coeffs rhs ranges =
  let n = List.length coeffs in
  let bounds =
    List.mapi
      (fun i (lo, hi) -> (Printf.sprintf "x%d" i, lo, hi))
      ranges
  in
  let assignments = cartesian ranges in
  let solutions = List.filter (satisfies coeffs rhs) assignments in
  let has_support i v =
    List.exists (fun sol -> List.nth sol i = v) solutions
  in
  let store = mk_store bounds in
  let terms = List.mapi (fun i a -> (a, var i)) coeffs in
  let prop = Linear.make terms rhs in
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
  check_soundness_case "2 vars, positive coeffs" [ 1; 1 ] 2
    [ (-3, 3); (-3, 3) ];
  check_soundness_case "2 vars, one negative coeff" [ 1; -1 ] 0
    [ (-3, 3); (-3, 3) ];
  check_soundness_case "3 vars, mixed signs" [ 2; -1; 3 ] 4
    [ (-3, 3); (-3, 3); (-3, 3) ];
  check_soundness_case "3 vars, one zero coeff" [ 1; 0; -2 ] 1
    [ (-2, 2); (-2, 2); (-2, 2) ];
  check_soundness_case "2 vars, all-negative coeffs" [ -2; -3 ] (-5)
    [ (-3, 3); (-3, 3) ];
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
  let terms = List.mapi (fun i a -> (a, var i)) coeffs in
  let prop = Linear.make terms rhs in
  (match Linear.propagate prop store with
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
        let other_ranges =
          List.filteri (fun j _ -> j <> i) current_ranges
        in
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
      check "bounds consistency: lo/hi of every var has support" !ok)

(* -------------------------------------------------------------- I-P2/I-P3 *)

let test_idempotence () =
  let coeffs = [ 2; -1; 3 ] and rhs = 4 in
  let ranges = [ (-3, 3); (-3, 3); (-3, 3) ] in
  let bounds = List.mapi (fun i (lo, hi) -> (Printf.sprintf "x%d" i, lo, hi)) ranges in
  let store = mk_store bounds in
  let terms = List.mapi (fun i a -> (a, var i)) coeffs in
  let prop = Linear.make terms rhs in
  (match Linear.propagate prop store with
  | Propagator.Conflict _ -> check "idempotence: expected Fixpoint first pass" false
  | Propagator.Fixpoint ->
      check "idempotence: first pass is a fixpoint result" true);
  let snap = Store.snapshot store in
  (match Linear.propagate prop store with
  | Propagator.Conflict _ -> check "I-P2: second propagate must not conflict" false
  | Propagator.Fixpoint ->
      check "I-P2: second propagate reports Fixpoint" true);
  check "I-P2/I-P3: second propagate changed nothing" (Store.same_domains store snap)

(* -------------------------------------------------------------------- conflict *)

let test_conflict () =
  (* 2x + 3y <= 1, but x in [1,3], y in [1,3]: min is 2+3=5 > 1. *)
  let bounds = [ ("x", 1, 3); ("y", 1, 3) ] in
  let store = mk_store bounds in
  let terms = [ (2, var 0); (3, var 1) ] in
  let prop = Linear.make terms 1 in
  match Linear.propagate prop store with
  | Propagator.Fixpoint -> check "conflict: expected Conflict" false
  | Propagator.Conflict e ->
      let lits = Explanation.lits e in
      check "conflict: reported" true;
      check "conflict: explanation has literals" (lits <> []);
      (* Check the shape and the arithmetic: Cut (Trivial, Linear (terms, units_rhs), c1,
         c2) where c - units_rhs < 0, over *all* the constraint's terms. *)
      (match Explanation.force e with
      | Explanation.Cut (Explanation.Trivial, Explanation.Linear (lterms, units_rhs), 1, 1)
        ->
          let computed_rhs =
            List.fold_left (fun acc (a, l) -> acc + (a * decode_bound l)) 0 lterms
          in
          check "conflict: Linear rhs matches its own terms" (computed_rhs = units_rhs);
          check "conflict: numeric contradiction (c - units_rhs < 0)"
            (1 - units_rhs < 0);
          check "conflict: covers every term"
            (List.length lterms = List.length terms)
      | _ -> check "conflict: unexpected explanation shape" false)

(* ---------------------------------------------------------- explanation entailment *)

(* Runs the propagator once, then inspects every trail entry it created: force the
   explanation and check, by direct arithmetic over the term list (not string
   comparison), that it really does entail the bound that got pushed. *)
let check_entailment_case name coeffs rhs bounds =
  let store = mk_store bounds in
  let terms = List.mapi (fun i a -> (a, var i)) coeffs in
  let prop = Linear.make terms rhs in
  let before = Store.trail_length store in
  match Linear.propagate prop store with
  | Propagator.Conflict _ ->
      check (Printf.sprintf "%s: expected Fixpoint" name) false
  | Propagator.Fixpoint ->
      let after = Store.trail_length store in
      check (Printf.sprintf "%s: at least one pruning happened" name) (after > before);
      let entries = Store.trail_entries store in
      (* [trail_entries] returns oldest-first; keep only the ones this call added. *)
      let new_entries =
        List.filteri (fun i _ -> i >= before) entries
      in
      List.iter
        (fun (e : Store.entry) ->
          let a =
            match List.find_opt (fun (_, x) -> Var.equal x e.var) terms with
            | Some (a, _) -> a
            | None -> failwith "entailment test: var not in constraint"
          in
          let expl = Explanation.force (Store.explanation store e) in
          match expl with
          | Explanation.Cut
              (Explanation.Trivial, Explanation.Linear (lterms, units_rhs), 1, 1) ->
              let computed_rhs =
                List.fold_left (fun acc (a, l) -> acc + (a * decode_bound l)) 0 lterms
              in
              check
                (Printf.sprintf "%s: Linear rhs matches its own terms" name)
                (computed_rhs = units_rhs);
              (* The Linear part must exclude exactly the pushed variable. *)
              check
                (Printf.sprintf "%s: pushed var absent from its own reason" name)
                (not
                   (List.exists
                      (fun (_, l) -> Lit.owner l.Lit.v = Store.name store e.var)
                      lterms));
              let max_term = rhs - units_rhs in
              let d_now = Store.get store e.var in
              if a > 0 then
                check
                  (Printf.sprintf "%s: pushed hi matches floor division" name)
                  (Domain.hi d_now = Linear.floordiv max_term a)
              else if a < 0 then
                check
                  (Printf.sprintf "%s: pushed lo matches ceil division" name)
                  (Domain.lo d_now = Linear.ceildiv max_term a)
              else check (Printf.sprintf "%s: zero coefficient never pushes" name) false
          | _ ->
              check (Printf.sprintf "%s: unexpected explanation shape" name) false)
        new_entries

let test_explanation_entailment () =
  check_entailment_case "positive coeffs push hi"
    [ 1; 1 ] (-2)
    [ ("x", -3, 3); ("y", -3, 3) ];
  check_entailment_case "negative coeff pushes lo"
    [ -1; 1 ] (-5)
    [ ("x", -3, 3); ("y", -3, 3) ];
  check_entailment_case "mixed signs, three vars"
    [ 2; -1; 3 ] (-2)
    [ ("x", -3, 3); ("y", -3, 3); ("z", -3, 3) ]

(* ------------------------------------------------------------------------ main *)

let () =
  print_endline "\npropagator unit tests";
  test_soundness ();
  test_bounds_consistency ();
  test_idempotence ();
  test_conflict ();
  test_explanation_entailment ();
  if !failures > 0 then (
    Printf.printf "\n%d FAILURE(S)\n" !failures;
    exit 1)
  else print_endline "\nall propagator checks passed"
