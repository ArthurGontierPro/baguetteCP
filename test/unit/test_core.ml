(* Unit tests for the solver core.

   These check the invariants in docs/INVARIANTS.md directly. When a new propagator
   lands, add it to the soundness check (I-P1) - brute force over small domains catches
   the class of bug that is otherwise only visible as a rejected proof, hours later. *)

module Domain = Baguette_core.Domain
module Store = Baguette_core.Store
module Var = Baguette_core.Var
module Explanation = Baguette_core.Explanation
module Arena = Baguette_core.Explanation.Arena
module Lit = Baguette_proof.Lit

let failures = ref 0

let check name cond =
  if cond then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s\n" name)

let check_raises name f =
  match f () with
  | exception _ -> Printf.printf "ok   %s\n" name
  | _ ->
      incr failures;
      Printf.printf "FAIL %s (expected an exception)\n" name

(* Narrow a domain, asserting the operation reported a change. *)
let changed r = match r with Domain.Changed d -> d | _ -> failwith "expected Changed"

(* ------------------------------------------------------------------ domains *)

let test_domains () =
  let d = Domain.make 1 5 in
  check "domain: size of 1..5" (Domain.size d = 5);
  check "domain: bounds" (Domain.lo d = 1 && Domain.hi d = 5);
  check "domain: membership" (Domain.mem d 3 && not (Domain.mem d 6));
  check "domain: membership below lo" (not (Domain.mem d 0));
  check "domain: not fixed" (not (Domain.is_fixed d));
  check "domain: value of an unfixed domain" (Domain.value d = None);
  check "domain: enumeration" (Domain.to_list d = [ 1; 2; 3; 4; 5 ]);

  check_raises "domain: empty initial range rejected" (fun () -> Domain.make 5 1);

  (* I-D2: a hole punched at a bound must move the bound past it. *)
  (match Domain.remove d 1 with
  | Domain.Changed d' ->
      check "I-D2: removing lo moves lo" (Domain.lo d' = 2);
      check "I-D2: size drops by one" (Domain.size d' = 4)
  | _ -> check "I-D2: removing lo moves lo" false);

  (match Domain.remove d 5 with
  | Domain.Changed d' ->
      check "I-D2: removing hi moves hi" (Domain.hi d' = 4 && Domain.size d' = 4)
  | _ -> check "I-D2: removing hi moves hi" false);

  (match Domain.remove d 3 with
  | Domain.Changed d' ->
      check "domain: interior hole keeps bounds"
        (Domain.lo d' = 1 && Domain.hi d' = 5 && Domain.size d' = 4);
      check "domain: interior hole is absent" (not (Domain.mem d' 3));
      check "domain: interior hole drops out of enumeration"
        (Domain.to_list d' = [ 1; 2; 4; 5 ]);
      check "domain: re-removing a hole is a no-op"
        (match Domain.remove d' 3 with Domain.Unchanged -> true | _ -> false)
  | _ -> check "domain: interior hole" false);

  (* I-D2 again, this time the bound has to walk over a run of holes. *)
  let d2 = changed (Domain.remove (Domain.make 0 9) 1) in
  let d2 = changed (Domain.remove d2 2) in
  let d2 = changed (Domain.remove d2 3) in
  check "domain: holes parked next to lo" (Domain.lo d2 = 0 && Domain.size d2 = 7);
  let d2 = changed (Domain.remove d2 0) in
  check "I-D2: lo walks over a run of holes" (Domain.lo d2 = 4);
  check "I-D2: size is consistent after the walk" (Domain.size d2 = 6);
  check "domain: values below the new lo are gone" (not (Domain.mem d2 2));

  check "domain: no-op prune reports Unchanged"
    (match Domain.set_lo d 1 with Domain.Unchanged -> true | _ -> false);
  check "domain: weakening a bound reports Unchanged"
    (match Domain.set_lo d 0 with Domain.Unchanged -> true | _ -> false);
  check "domain: set_hi above hi reports Unchanged"
    (match Domain.set_hi d 9 with Domain.Unchanged -> true | _ -> false);

  check "domain: contradictory bound fails"
    (match Domain.set_lo d 9 with Domain.Failed -> true | _ -> false);
  check "domain: contradictory upper bound fails"
    (match Domain.set_hi d (-1) with Domain.Failed -> true | _ -> false);

  check "domain: fix outside domain fails"
    (match Domain.fix d 9 with Domain.Failed -> true | _ -> false);
  (match Domain.fix d 3 with
  | Domain.Changed d' ->
      check "domain: fix pins both bounds"
        (Domain.is_fixed d' && Domain.value d' = Some 3 && Domain.size d' = 1);
      check "domain: re-fixing is a no-op"
        (match Domain.fix d' 3 with Domain.Unchanged -> true | _ -> false)
  | _ -> check "domain: fix pins both bounds" false);

  (* Fixing to a value that was punched out must fail, not resurrect it. *)
  let holed = changed (Domain.remove (Domain.make 1 5) 3) in
  check "domain: fix onto a hole fails"
    (match Domain.fix holed 3 with Domain.Failed -> true | _ -> false);
  check "domain: bound tightening onto a hole skips it"
    (Domain.lo (changed (Domain.set_lo holed 3)) = 4);

  (* Removing every value must fail rather than produce an empty domain (I-D1). *)
  let shrink d v = match Domain.remove d v with Domain.Changed d' -> d' | _ -> d in
  let d3 = List.fold_left shrink (Domain.make 1 3) [ 1; 3 ] in
  check "I-D1: shrunk to a single value" (Domain.is_fixed d3 && Domain.lo d3 = 2);
  check "I-D1: removing the last value fails"
    (match Domain.remove d3 2 with Domain.Failed -> true | _ -> false);
  check "I-D1: emptying by bounds fails"
    (match Domain.set_lo d3 3 with Domain.Failed -> true | _ -> false);

  (* Holes and bounds together: 1..9 minus {4,5,6}, then squeeze the bounds inward. *)
  let d4 = List.fold_left shrink (Domain.make 1 9) [ 4; 5; 6 ] in
  check "domain: three interior holes" (Domain.size d4 = 6);
  let d4 = changed (Domain.set_lo d4 4) in
  check "domain: set_lo lands past the hole run" (Domain.lo d4 = 7);
  check "domain: size after the squeeze"
    (Domain.size d4 = 3 && Domain.to_list d4 = [ 7; 8; 9 ]);

  (* I-D3: every operation returns a subset of what it was given. *)
  let sub a b = List.for_all (fun v -> Domain.mem a v) (Domain.to_list b) in
  let base = List.fold_left shrink (Domain.make 0 8) [ 2; 5 ] in
  let steps =
    [
      Domain.set_lo base 1; Domain.set_hi base 7; Domain.remove base 3; Domain.fix base 4;
    ]
  in
  check "I-D3: results are subsets"
    (List.for_all (function Domain.Changed d' -> sub base d' | _ -> true) steps);

  (* Equality is over the value sets, not the representations: the right-hand domain
     never allocated a bitset, the left-hand one did and then walked its bound past it. *)
  let a = changed (Domain.remove (Domain.make 1 4) 1) in
  check "domain: equality ignores stale hole bits" (Domain.equal a (Domain.make 2 4));
  check "domain: equality separates different sets"
    (not (Domain.equal a (Domain.make 1 4)));

  check "domain: of_list builds the holes"
    (Domain.to_list (Domain.of_list [ 5; 1; 3; 1 ]) = [ 1; 3; 5 ]);
  check "domain: of_list bounds" (Domain.lo (Domain.of_list [ 5; 1; 3 ]) = 1);
  check_raises "domain: of_list of nothing is rejected" (fun () -> Domain.of_list []);

  check "domain: to_string of a range" (Domain.to_string (Domain.make 1 5) = "1..5");
  check "domain: to_string of a fixed domain" (Domain.to_string (Domain.singleton 7) = "7");
  check "domain: to_string shows holes"
    (Domain.to_string (changed (Domain.remove (Domain.make 1 5) 3)) = "1..5 \\ {3}");

  (* A domain too wide for a hole bitset declines the interior hole rather than
     allocating megabytes. Declining to prune is sound; bound moves still work. *)
  let wide = Domain.make 0 (1 lsl 21) in
  check "domain: huge domain declines an interior hole"
    (match Domain.remove wide 5 with Domain.Unchanged -> true | _ -> false);
  check "domain: huge domain still moves its bounds"
    (Domain.lo (changed (Domain.remove wide 0)) = 1)

(* -------------------------------------------------------------------- store *)

let sample_store () =
  Store.create ~names:[| "x"; "y"; "z" |]
    ~domains:[| Domain.make 0 10; Domain.make 0 10; Domain.make 0 10 |]

let test_store () =
  let s = sample_store () in
  let x = Var.of_int 0 and y = Var.of_int 1 in
  check "store: starts at level 0" (Store.level s = 0);
  check "store: variable count" (Store.n_vars s = 3);
  check "store: names" (Store.name s x = "x");

  let why = Explanation.trivial in
  check "store: prune applies"
    (match Store.set_lo s x 3 why with Store.Changed -> true | _ -> false);
  check "store: prune took effect" (Domain.lo (Store.get s x) = 3);
  check "store: redundant prune is a no-op"
    (match Store.set_lo s x 2 why with Store.Unchanged -> true | _ -> false);
  check "store: a no-op leaves no trail entry" (Store.trail_length s = 1);
  check "store: contradiction surfaces the explanation"
    (match Store.set_hi s x 1 why with Store.Conflict _ -> true | _ -> false);
  check "store: a conflict leaves the domain alone" (Domain.lo (Store.get s x) = 3);
  check "store: a conflict leaves no trail entry" (Store.trail_length s = 1);

  (* I-T1: backtracking restores exactly the state at the level mark. Comparing the
     whole domain array, not just a bound, is what makes this a real check. *)
  let snap0 = Store.snapshot s in
  let before_lo = Domain.lo (Store.get s x) and before_hi = Domain.hi (Store.get s y) in
  Store.new_level s;
  check "I-T2: level opened" (Store.level s = 1);
  ignore (Store.set_lo s x 7 why);
  ignore (Store.set_hi s y 2 why);
  let snap1 = Store.snapshot s in
  Store.new_level s;
  check "I-T2: second level opened" (Store.level s = 2);
  ignore (Store.fix s y 1 why);
  ignore (Store.remove s x 8 why);
  check "store: nested changes applied"
    (Domain.lo (Store.get s x) = 7 && Domain.is_fixed (Store.get s y));
  check "store: hole applied inside a level" (not (Domain.mem (Store.get s x) 8));
  check "I-T2: level marks are monotone"
    (match Store.level_marks s with [ a; b ] -> a <= b | _ -> false);
  check "I-T3: trail invariants hold at depth" (Store.check_invariants s);

  Store.backtrack s;
  check "I-T1: one level back restores exactly" (Store.same_domains s snap1);
  check "I-T1: the hole is gone again" (Domain.mem (Store.get s x) 8);
  check "store: level decremented" (Store.level s = 1);

  Store.backtrack_to s 0;
  check "I-T1: x restored" (Domain.lo (Store.get s x) = before_lo);
  check "I-T1: y restored" (Domain.hi (Store.get s y) = before_hi);
  check "I-T1: every domain restored exactly" (Store.same_domains s snap0);
  check "I-S3: level restored" (Store.level s = 0);
  check "I-T3: trail invariants hold after backtracking" (Store.check_invariants s);

  check_raises "store: backtracking past level 0 is an error" (fun () ->
      Store.backtrack s);
  check_raises "store: backtracking forwards is an error" (fun () ->
      Store.backtrack_to s 3);
  check_raises "store: mismatched create is rejected" (fun () ->
      Store.create ~names:[| "x" |] ~domains:[||]);

  (* A deeper descent, to check that repeated open/close cycles stay exact. *)
  let s2 = sample_store () in
  let vars = Array.init 3 Var.of_int in
  let snaps = Array.make 6 (Store.snapshot s2) in
  for lvl = 0 to 5 do
    snaps.(lvl) <- Store.snapshot s2;
    Store.new_level s2;
    ignore (Store.set_lo s2 vars.(lvl mod 3) (lvl + 1) Explanation.trivial);
    ignore (Store.remove s2 vars.((lvl + 1) mod 3) (9 - lvl) Explanation.trivial)
  done;
  check "store: descended six levels" (Store.level s2 = 6);
  let exact = ref true in
  for lvl = 5 downto 0 do
    Store.backtrack s2;
    if not (Store.same_domains s2 snaps.(lvl)) then exact := false
  done;
  check "I-T1: every level restores exactly on the way up" !exact;
  check "I-S3: back at level 0" (Store.level s2 = 0);
  check "store: trail is empty again" (Store.trail_length s2 = 0);

  (* I-T3: reasons resolve, and a reason recorded at a level is dropped with it. *)
  let s3 = sample_store () in
  let lit = Lit.ge "x" 4 in
  Store.new_level s3;
  ignore (Store.set_lo s3 (Var.of_int 0) 4 (Explanation.clause [ lit ]));
  let reason_count = Arena.length (Store.reasons s3) in
  check "I-T3: the reason was interned" (reason_count = 1);
  check "I-T3: the trail entry resolves to its reason"
    (match Store.trail_entries s3 with
    | e :: _ -> (
        match Store.explanation s3 e with
        | Explanation.Clause [ l ] -> Lit.to_string l = Lit.to_string lit
        | _ -> false)
    | [] -> false);
  Store.backtrack s3;
  check "I-T3: reasons are dropped with their level" (Arena.length (Store.reasons s3) = 0);
  check "I-T3: no orphan entries remain" (Store.check_invariants s3);

  check "store: all_fixed is false while anything is open" (not (Store.all_fixed s3));
  let s4 = Store.create ~names:[| "a" |] ~domains:[| Domain.make 2 2 |] in
  check "store: all_fixed is true when everything is pinned" (Store.all_fixed s4)

(* ------------------------------------------------------------- explanations *)

let test_explanations () =
  let l = Lit.ge "x" 3 in
  check "lit: order-encoding name" (Lit.to_string l = "x_ge_3");
  check "lit: upper bound is a negated order literal"
    (Lit.to_string (Lit.le "x" 4) = "~x_ge_5");
  check "lit: negative values avoid '-'" (Lit.to_string (Lit.ge "x" (-2)) = "x_ge_m2");
  check "lit: double negation" (Lit.to_string (Lit.negate (Lit.negate l)) = "x_ge_3");

  (* Deferred explanations must be computed at most once: forcing twice must not
     re-run the thunk. See docs/ARCHITECTURE.md section 4. *)
  let calls = ref 0 in
  let e =
    Explanation.deferred (fun () ->
        incr calls;
        Explanation.clause [ l ])
  in
  check "explanation: Deferred is not forced by construction"
    (not (Explanation.is_forced e));
  check "explanation: peeking does not force" (Explanation.peek e = None);
  check "explanation: printing does not force"
    (Explanation.to_string e = "deferred[?]" && !calls = 0);
  let _ = Explanation.force e in
  let _ = Explanation.force e in
  let _ = Explanation.force e in
  check "explanation: Deferred is memoised" (!calls = 1);
  check "explanation: forced value is the computed one"
    (match Explanation.force e with
    | Explanation.Clause [ l' ] -> Lit.to_string l' = "x_ge_3"
    | _ -> false);
  check "explanation: is_forced after forcing" (Explanation.is_forced e);

  (* A thunk may return another thunk. Forcing must drive through to a concrete head,
     and each layer must be memoised - a second force runs neither of them. *)
  let inner_calls = ref 0 and outer_calls = ref 0 in
  let nested =
    Explanation.deferred (fun () ->
        incr outer_calls;
        Explanation.deferred (fun () ->
            incr inner_calls;
            Explanation.linear [ (1, l) ] 1))
  in
  let head = Explanation.force nested in
  let head2 = Explanation.force nested in
  check "explanation: nested Deferred forces through to a concrete head"
    (match head with Explanation.Linear ([ (1, _) ], 1) -> true | _ -> false);
  check "explanation: nested Deferred is memoised at every layer"
    (!outer_calls = 1 && !inner_calls = 1);
  check "explanation: repeated force returns the same value" (head == head2);

  (* Forcing through a shared sub-explanation must not run its thunk twice either. *)
  let shared_calls = ref 0 in
  let shared =
    Explanation.deferred (fun () ->
        incr shared_calls;
        Explanation.clause [ Lit.ge "z" 1 ])
  in
  let combined = Explanation.cut shared shared 1 1 in
  let _ = Explanation.lits combined in
  let _ = Explanation.lits combined in
  check "explanation: a shared Deferred is forced once" (!shared_calls = 1);

  check "explanation: lits of a cut unions both sides"
    (List.length
       (Explanation.lits
          (Explanation.cut (Explanation.clause [ l ])
             (Explanation.clause [ Lit.ge "y" 1 ])
             1 1))
    = 2);
  check "explanation: lits of a cut does not double-count"
    (List.length (Explanation.lits combined) = 1);
  check "explanation: lits reaches through a Deferred"
    (List.map Lit.to_string
       (Explanation.lits (Explanation.deferred (fun () -> Explanation.clause [ l ])))
    = [ "x_ge_3" ]);
  check "explanation: lits of a linear reason are its terms"
    (List.map Lit.to_string
       (Explanation.lits (Explanation.linear [ (2, l); (3, Lit.ge "y" 1) ] 4))
    = [ "x_ge_3"; "y_ge_1" ]);
  check "explanation: trivial mentions nothing" (Explanation.lits Explanation.trivial = []);

  check "explanation: to_string of a linear reason"
    (Explanation.to_string (Explanation.linear [ (2, l) ] 4) = "linear(+2 x_ge_3 >= 4)");

  (* Arena: the trail stores indices, so resolution and truncation are invariants. *)
  let a = Arena.create ~capacity:1 () in
  let i0 = Arena.add a Explanation.trivial in
  let i1 = Arena.add a (Explanation.clause [ l ]) in
  let i2 = Arena.add a (Explanation.linear [ (1, l) ] 1) in
  check "arena: ids are dense" (i0 = 0 && i1 = 1 && i2 = 2);
  check "arena: it grows past its initial capacity" (Arena.length a = 3);
  check "arena: get resolves"
    (match Arena.get a i1 with Explanation.Clause [ _ ] -> true | _ -> false);
  check "arena: mem agrees with get" (Arena.mem a i2 && not (Arena.mem a 3));
  check "arena: null is not a member" (not (Arena.mem a Arena.null));
  check_raises "arena: get out of range raises" (fun () -> Arena.get a 3);
  Arena.truncate a 1;
  check "arena: truncate drops the tail" (Arena.length a = 1 && not (Arena.mem a i1));
  check_raises "arena: a truncated id no longer resolves" (fun () -> Arena.get a i1);
  check "arena: truncating longer than the arena is a no-op"
    (Arena.truncate a 5;
     Arena.length a = 1);

  (* force_at writes the memoised result back, so the arena holds the concrete reason. *)
  let b = Arena.create () in
  let n = ref 0 in
  let id =
    Arena.add b
      (Explanation.deferred (fun () ->
           incr n;
           Explanation.clause [ l ]))
  in
  let _ = Arena.force_at b id in
  let _ = Arena.force_at b id in
  check "arena: force_at memoises into the arena"
    (!n = 1 && match Arena.get b id with Explanation.Clause [ _ ] -> true | _ -> false)

let () =
  test_domains ();
  test_store ();
  test_explanations ();
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "\ncore unit tests passed"
