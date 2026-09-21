(* Unit tests for the solver core.

   These check the invariants in docs/INVARIANTS.md directly. When a new propagator
   lands, add it to the soundness check (I-P1) - brute force over small domains catches
   the class of bug that is otherwise only visible as a rejected proof, hours later. *)

module Domain = Baguette_core.Domain
module Store = Baguette_core.Store
module Var = Baguette_core.Var
module Explanation = Baguette_core.Explanation
module Reason = Baguette_core.Reason
module Arena = Baguette_core.Explanation.Arena
module Lit = Baguette_proof.Lit
module View = Baguette_core.View

(* M1-T53: the inner heap guard. test_prop.exe is the binary that reached 14.9 GB RSS on
   2026-09-16 and had to be killed by hand, so a guard that covered only test_output and
   test_compile would have missed the one incident it exists to prevent. `ulimit -v` stays
   the outer backstop -- see mem_guard.ml's header for what this cannot see. *)
let () = Mem_guard.install ()
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

  (* Any reason will do -- this test is about the trail, not the proof. M1-T31
     deleted [Explanation.trivial], which is what stood here; [Model_row] is the
     honest spelling of "some model row justifies it" and nothing renders it.

     M2-T8/D-0026: a mutator takes ONE [Reason.justified], both halves together. This
     test is not exercising the trace, so its reason is [Reason.none] -- written out,
     because there is no longer a mutator that means it by omission. *)
  let why = Reason.because ~concludes:None Reason.none (Explanation.model_row 1) in
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
    let r = Reason.because ~concludes:None Reason.none (Explanation.model_row 1) in
    ignore (Store.set_lo s2 vars.(lvl mod 3) (lvl + 1) r);
    ignore (Store.remove s2 vars.((lvl + 1) mod 3) (9 - lvl) r)
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
  ignore
    (Store.set_lo s3 (Var.of_int 0) 4
       (Reason.because ~concludes:None Reason.none (Explanation.clause [ lit ])));
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
  (* M1-T31/M1-T50. [Trivial] used to sit here and mention nothing at all, which is
     what made a reason set resting on a decision name no dependency -- the omission
     D-0035 says becomes unsoundness once M2-T3 learns clauses from it. A decision's
     reason set is exactly the literal it assumed. *)
  check "explanation: a decision mentions the literal it assumed"
    (List.map Lit.to_string (Explanation.lits (Explanation.decision l)) = [ "x_ge_3" ]);
  check "explanation: a model row mentions nothing"
    (Explanation.lits (Explanation.model_row 7) = []);
  check "explanation: to_string of a decision names its literal"
    (Explanation.to_string (Explanation.decision l) = "decision(x_ge_3)");

  (* A decision has no constraint id, so it cannot be a [pol] operand and the ADT
     refuses to build one out of it -- at the point the citation is made, not several
     layers down inside [Justify] (M1-T50). *)
  check_raises "explanation: term refuses to cite a decision" (fun () ->
      ignore (Explanation.term 2 (Explanation.decision l)));
  check_raises "explanation: cut refuses to cite a decision" (fun () ->
      ignore (Explanation.cut (Explanation.decision l) (Explanation.clause [ l ]) 1 1));

  check "explanation: to_string of a linear reason"
    (Explanation.to_string (Explanation.linear [ (2, l) ] 4) = "linear(+2 x_ge_3 >= 4)");

  (* Arena: the trail stores indices, so resolution and truncation are invariants. *)
  let a = Arena.create ~capacity:1 () in
  let i0 = Arena.add a (Explanation.model_row 1) in
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

(* ------------------------------------------------- who made the change (M2-T7)

   [Store.entry]'s [prop], the field docs/DECISIONS.md D-0011 says the trail lacks and
   M2-T3 cannot start without. These are the store's half: that the stamp is whatever
   [with_running] says and nothing else, that it is restored, and that [no_prop] really
   is what an unattributed change gets. The engine's half -- that the stamp names the
   instance that actually ran, and that the instance watches what it changed -- is
   test_engine.ml's, because only the engine can see a [Propagator.instance]. *)

let last_entry store = Store.trail_entry store (Store.trail_length store - 1)

let test_attribution () =
  let store =
    Store.create ~names:[| "x"; "y" |] ~domains:[| Domain.make 0 5; Domain.make 0 5 |]
  in
  let r = Reason.because ~concludes:None Reason.none (Explanation.model_row 1) in
  check "M2-T7: a fresh store has nobody running" (Store.running store = Store.no_prop);

  (* A mutation made by nobody -- Search's decision pushes and every direct call from a
     test take this path -- is attributed to nobody. It is not attributed to instance 0
     by accident, which is the failure mode a sentinel of [0] would have had. *)
  (match Store.set_lo store (Var.of_int 0) 1 r with
  | Store.Changed -> ()
  | _ -> failwith "test_attribution: setup");
  check "M2-T7: a change made outside any propagator is no_prop"
    ((last_entry store).Store.prop = Store.no_prop);

  (* And inside a bracket it is stamped with that id, on the entry, not just held in the
     field. *)
  Store.with_running store 7 (fun () ->
      check "M2-T7: with_running records the running instance" (Store.running store = 7);
      match Store.set_lo store (Var.of_int 0) 2 r with
      | Store.Changed ->
          check "M2-T7: apply stamps the running instance onto the entry"
            ((last_entry store).Store.prop = 7)
      | _ -> failwith "test_attribution: push under a bracket");
  check "M2-T7: with_running restores afterwards" (Store.running store = Store.no_prop);

  (* Nested brackets restore the outer id rather than clearing to no_prop. Nothing nests
     today; the point is that an engine that ever ran one propagator from inside another
     would still attribute correctly, so this is not a trap left for M2-T8. *)
  Store.with_running store 3 (fun () ->
      Store.with_running store 4 (fun () ->
          check "M2-T7: a nested bracket takes effect" (Store.running store = 4));
      check "M2-T7: a nested bracket restores the outer id" (Store.running store = 3));

  (* A propagator that raises -- [Checked]'s overflow guard does, by design -- must not
     leave the store claiming it is still running, or the next change made by anyone
     would be credited to it. *)
  (try Store.with_running store 5 (fun () -> raise Exit) with Exit -> ());
  check "M2-T7: with_running restores when the propagator raises"
    (Store.running store = Store.no_prop);

  (* A conflict is stamped from the same field, and a conflict with no bound facts says
     [Reason.none] -- which is what the D-0018 point 3 line keys off, and what the old
     one-shot [conflict_facts] slot meant when nobody had armed it. M2-T8 removed the
     default: it is the same behaviour, now written down at the call site. *)
  let c =
    Store.conflict store
      (Reason.because ~concludes:None Reason.none (Explanation.model_row 2))
  in
  check "M2-T7: a conflict built outside a propagator is no_prop"
    (c.Store.c_prop = Store.no_prop);
  check "M2-T7: a conflict records no facts unless asked"
    (Reason.lits c.Store.c_reason = []);
  Store.with_running store 2 (fun () ->
      let c =
        Store.conflict store
          (Reason.because ~concludes:None
             [ Reason.at_least ~name:"x" ~decl:0 1 ]
             (Explanation.model_row 2))
      in
      check "M2-T7: a conflict names the propagator that reported it" (c.Store.c_prop = 2);
      check "M2-T7: and carries its own bound facts"
        (Reason.lits c.Store.c_reason = [ Lit.ge "x" 1 ]));

  (* The stamp survives a backtrack the way every other field does: I-T1 restores
     domains, and an entry that is popped takes its attribution with it. *)
  Store.new_level store;
  Store.with_running store 11 (fun () ->
      match Store.set_lo store (Var.of_int 1) 1 r with
      | Store.Changed -> ()
      | _ -> failwith "test_attribution: level push");
  check "M2-T7: the deeper entry is attributed" ((last_entry store).Store.prop = 11);
  Store.backtrack store;
  check "M2-T7: backtracking pops the attributed entry with everything else"
    ((last_entry store).Store.prop = 7 && Store.check_invariants store)

(* ------------------------------------------------- reasons are data (M2-T8, D-0026)

   docs/DECISIONS.md D-0026 split the old single explanation channel into a declarative
   [Reason.t] (which facts) and an [Explanation.t] (how the checker is convinced). These
   tests are for the failure modes that split *creates*, which by construction no test
   written before M2-T8 can see: a reason materialised over the wrong scope, materialised
   at the wrong moment, or agreeing with its justification only by luck.

   "The existing suite still passes" is necessary and nowhere near sufficient here -- the
   whole point of a refactor that changes no behaviour is that the old suite is blind to
   whether the new structure is right. *)

let test_reason () =
  (* The ONE materialisation rule, and it is the one that used to be copied into
     [Linear.facts_of_snaps], [Ne.fixed_facts] and [Bool2int.ge_fact]: a fact at the
     variable's DECLARED bound has no literal, because the order encoding states it as
     the constant true (docs/PROOF-FORMAT.md section 3). Both directions, because a
     mirrored pair is where this project keeps shipping a half that nothing runs. *)
  check "D-0026: a lower fact past the declared bound materialises"
    (Reason.lits [ Reason.at_least ~name:"x" ~decl:0 3 ] = [ Lit.ge "x" 3 ]);
  check "D-0026: a lower fact AT the declared bound materialises to nothing"
    (Reason.lits [ Reason.at_least ~name:"x" ~decl:3 3 ] = []);
  check "D-0026: an upper fact past the declared bound materialises"
    (Reason.lits [ Reason.at_most ~name:"x" ~decl:9 4 ] = [ Lit.le "x" 4 ]);
  check "D-0026: an upper fact AT the declared bound materialises to nothing"
    (Reason.lits [ Reason.at_most ~name:"x" ~decl:4 4 ] = []);
  check "D-0026: Reason.none materialises to nothing" (Reason.lits Reason.none = []);

  (* Order and duplicates survive materialisation. The tail of a trace line is an
     artefact this project diffs byte for byte, so a [lits] that sorted or deduped would
     be a silent artefact change rather than a bug anyone would see as one. *)
  let three =
    [
      Reason.at_least ~name:"a" ~decl:0 1;
      Reason.at_most ~name:"b" ~decl:9 2;
      Reason.at_least ~name:"a" ~decl:0 1;
    ]
  in
  check "D-0026: lits preserves order and keeps duplicates"
    (Reason.lits three = [ Lit.ge "a" 1; Lit.le "b" 2; Lit.ge "a" 1 ]);

  (* The scope is what a reason names, INCLUDING the variables whose fact does not
     materialise. M2-T3 is meant to walk a reason's variables without building a single
     literal, so [owners] must not be a projection of [lits]. This is the check that
     fails if someone "simplifies" it to one. *)
  let mixed =
    [ Reason.at_least ~name:"kept" ~decl:0 2; Reason.at_least ~name:"dropped" ~decl:7 7 ]
  in
  check "D-0026: owners includes a variable whose fact has no literal"
    (Reason.owners mixed = [ "kept"; "dropped" ]
    && Reason.lits mixed = [ Lit.ge "kept" 2 ]);
  check "D-0026: owners dedupes but keeps first-seen order"
    (Reason.owners three = [ "a"; "b" ]);

  (* [fixed_at] is "x = v" as the two order facts [Ne] states, and each half drops at its
     own declared bound independently -- the case [Ne.fixed_facts] got right by hand and
     which now has to keep being right in one place for three callers. *)
  check "D-0026: fixed_at states both halves"
    (Reason.lits (Reason.fixed_at ~name:"x" ~decl_lo:0 ~decl_hi:9 4)
    = [ Lit.ge "x" 4; Lit.le "x" 4 ]);
  check "D-0026: fixed_at at the declared lo states only the upper half"
    (Reason.lits (Reason.fixed_at ~name:"x" ~decl_lo:0 ~decl_hi:9 0) = [ Lit.le "x" 0 ]);
  check "D-0026: fixed_at at the declared hi states only the lower half"
    (Reason.lits (Reason.fixed_at ~name:"x" ~decl_lo:0 ~decl_hi:9 9) = [ Lit.ge "x" 9 ]);
  check "D-0026: fixed_at on a one-value declaration states nothing"
    (Reason.lits (Reason.fixed_at ~name:"x" ~decl_lo:4 ~decl_hi:4 4) = []);

  (* [bound_for_coeff] is D-0013's case split, shared so a linear-shaped propagator's
     reason and its row arithmetic cannot disagree about WHICH bound was read. Getting
     this backwards is break 1 in the M2-T8 hand-back, and it is why the shared helper
     exists rather than each propagator writing the conditional. *)
  check "D-0026: a non-negative coefficient reads lo and states x >= v"
    (Reason.lits [ Reason.bound_for_coeff ~coeff:2 ~name:"x" ~decl_lo:0 ~decl_hi:9 3 ]
    = [ Lit.ge "x" 3 ]);
  check "D-0026: a negative coefficient reads hi and states x <= v"
    (Reason.lits [ Reason.bound_for_coeff ~coeff:(-2) ~name:"x" ~decl_lo:0 ~decl_hi:9 3 ]
    = [ Lit.le "x" 3 ]);

  (* NON-NARROWABLE, which is the property I-X6 needs and the one GCS's [Narrowable*]
     variants do not have. A reason built now and materialised after the store has moved
     must render the bound as it was AT THE PRUNING, not as it is now.

     Note what makes this test able to see its subject fail: it materialises the same
     reason twice, side by side with the bound that has since moved, and asserts the two
     are different. A test that only checked "the literals are x >= 3" would pass just as
     happily against a reason that re-read the store, because the store still said 3 at
     that instant. *)
  let store =
    Store.create ~names:[| "x"; "y" |] ~domains:[| Domain.make 0 9; Domain.make 0 9 |]
  in
  let j =
    Reason.because ~concludes:None
      [ Reason.at_least ~name:"x" ~decl:0 3 ]
      (Explanation.clause [ Lit.ge "x" 3 ])
  in
  (match Store.set_lo store (Var.of_int 0) 3 j with
  | Store.Changed -> ()
  | _ -> failwith "test_reason: setup");
  let e = last_entry store in
  let at_push = Reason.lits e.Store.reason in
  Store.new_level store;
  ignore
    (Store.set_lo store (Var.of_int 0) 7
       (Reason.because ~concludes:None Reason.none (Explanation.model_row 1)));
  check "I-X6: the store really did move under the reason"
    (Domain.lo (Store.get store (Var.of_int 0)) = 7);
  check "I-X6: a reason materialised later renders the bound as of the pruning"
    (Reason.lits e.Store.reason = at_push && at_push = [ Lit.ge "x" 3 ]);
  Store.backtrack store;
  check "I-X6: and still does after the later push is backtracked"
    (Reason.lits e.Store.reason = [ Lit.ge "x" 3 ])

(* ------------------------------------------ what holds a bound up (M2-T8)

   [Store.lo_support]/[hi_support] replaced [Linear.find_lo_reason]'s downward trail
   scan. M1-T28 recorded that the *direction* of that scan was load-bearing and that
   "the two differ only on a variable whose bound moved twice in one branch, which is
   why no type and no model in the suite can tell them apart". That is now a two-line
   test, because the answer is a value rather than a walk. *)
let test_bound_support () =
  let store =
    Store.create ~names:[| "x"; "y" |] ~domains:[| Domain.make 0 9; Domain.make 0 9 |]
  in
  let x = Var.of_int 0 in
  let r n = Reason.because ~concludes:None Reason.none (Explanation.model_row n) in
  let row_of_support sup =
    match Store.explanation store (Store.trail_entry store sup) with
    | Explanation.Model_row n -> n
    | _ -> -1
  in
  check "M2-T8: an untouched bound has no support"
    (Store.lo_support store x = Store.no_support
    && Store.hi_support store x = Store.no_support);

  ignore (Store.set_lo store x 2 (r 11));
  check "M2-T8: the entry that moved lo supports lo"
    (row_of_support (Store.lo_support store x) = 11);
  check "M2-T8: and moving lo did not give hi a support"
    (Store.hi_support store x = Store.no_support);

  (* Moving the OTHER bound must not steal the first one's support. *)
  ignore (Store.set_hi store x 8 (r 12));
  check "M2-T8: hi gets its own support and lo keeps its own"
    (row_of_support (Store.hi_support store x) = 12
    && row_of_support (Store.lo_support store x) = 11);

  (* THE M1-T28 property, which no model could see: with lo moved twice, the reason is
     the NEWEST entry that moved it, not the oldest. The old upward-scanning variant
     returned 11 here; the downward one and this array return 13. *)
  Store.new_level store;
  ignore (Store.set_lo store x 5 (r 13));
  check "M1-T28: the support is the NEWEST entry that moved the bound, not the oldest"
    (row_of_support (Store.lo_support store x) = 13);
  check "M2-T8: lo_reasons cites that entry's explanation"
    (match Store.lo_reasons store x with
    | [ Explanation.Model_row 13 ] -> true
    | _ -> false);

  (* And it is restored on the way back up, or a citation would name a popped entry. *)
  Store.backtrack store;
  check "M2-T8: backtracking restores the superseded support"
    (row_of_support (Store.lo_support store x) = 11
    && row_of_support (Store.hi_support store x) = 12);
  check "M2-T8: the support array agrees with the trail (check_invariants)"
    (Store.check_invariants store);

  (* An interior hole moves no bound, so it takes no support -- the case that makes
     "support" different from "the newest entry for this variable". *)
  ignore (Store.set_lo store x 2 (r 14));
  let before = Store.lo_support store x in
  ignore (Store.remove store x 5 (r 15));
  check "M2-T8: an interior hole does not become a bound's support"
    (Store.lo_support store x = before && Store.check_invariants store);

  (* [Domain.fix] moves both bounds at once and must support both. *)
  let s2 = Store.create ~names:[| "z" |] ~domains:[| Domain.make 0 9 |] in
  let z = Var.of_int 0 in
  ignore
    (Store.fix s2 z 4
       (Reason.because ~concludes:None Reason.none (Explanation.model_row 21)));
  check "M2-T8: fix supports both bounds it moved"
    (Store.lo_support s2 z = 0 && Store.hi_support s2 z = 0 && Store.check_invariants s2)

(* ------------------------------- the reason and the justification must agree (D-0026)

   D-0026 exists to turn "the two are kept in agreement by a comment" into a type. The
   type gets the two halves to one place; it cannot by itself say they are about the same
   pruning. [Store.agreement_holds] is that last step -- the reason may only name
   variables the justification mentions -- and [Store.apply] asserts it under
   BAGUETTE_DEBUG.

   The predicate is tested here, unconditionally. The WIRING is tested by
   [test_agreement_is_wired] below, which re-runs this binary with BAGUETTE_DEBUG=1 and
   performs the break, because [Debug.enabled] is read once at module initialisation and
   a check nothing runs is not a check. *)
let test_agreement () =
  (* Two stores: one where nothing has moved, and one where [y]'s lower bound is held up
     by a trail entry. The difference is the whole of the forward check's second arm. *)
  let fresh () =
    Store.create ~names:[| "x"; "y" |] ~domains:[| Domain.make 0 9; Domain.make 0 9 |]
  in
  let plain = fresh () in
  let derived = fresh () in
  ignore
    (Store.set_lo derived (Var.of_int 1) 2
       (Reason.because ~concludes:None Reason.none (Explanation.model_row 1)));
  let expl = Explanation.clause [ Lit.ge "x" 1; Lit.le "y" 4 ] in
  check "D-0026: a reason over the justification's own variables agrees"
    (Store.agreement_holds plain
       (Reason.because ~concludes:None [ Reason.at_least ~name:"y" ~decl:0 2 ] expl));
  check "D-0026: an empty reason agrees with anything"
    (Store.agreement_holds plain (Reason.because ~concludes:None Reason.none expl));
  check "D-0026: a reason naming a variable the justification never mentions DISAGREES"
    (not
       (Store.agreement_holds plain
          (Reason.because ~concludes:None [ Reason.at_least ~name:"z" ~decl:0 2 ] expl)));
  (* The disagreement is found even when the offending fact is one of several. *)
  check "D-0026: one stray fact among good ones still DISAGREES"
    (not
       (Store.agreement_holds plain
          (Reason.because ~concludes:None
             [
               Reason.at_least ~name:"x" ~decl:0 1;
               Reason.at_least ~name:"z" ~decl:0 5;
               Reason.at_most ~name:"y" ~decl:9 4;
             ]
             expl)));
  (* But a stray fact AT its declared bound is allowed, and this records the limit on
     purpose rather than leaving it to be discovered. Such a fact materialises to no
     literal, so it is in neither half of the pruning and can contradict neither; the
     forward arm skips it. [Bool2int] pushing `x <= 1` out of `b` still at its declared
     upper bound is exactly this shape, and requiring a support for it reddened three
     test binaries under BAGUETTE_DEBUG. What it costs: a reason may carry a *silent*
     variable outside the derivation's scope, which is wrong data for M2-T3 even though
     it is harmless to the proof. See the M2-T8 hand-back. *)
  check "D-0026: a stray fact that materialises to NOTHING is permitted (documented gap)"
    (Store.agreement_holds plain
       (Reason.because ~concludes:None [ Reason.at_least ~name:"z" ~decl:5 5 ] expl));

  (* THE CITE ARM, and the case that made the naive predicate wrong: a [Combine] that
     cites the id which established [y >= 2] contains no literal about [y] anywhere
     (D-0038 -- an explanation records how a bound was derived, not what). So the same
     reason that DISAGREES against a derivation mentioning nothing must AGREE once [y]'s
     bound is held up by a trail entry the derivation is entitled to cite.

     Both answers asserted against the same reason and the same justification, differing
     only in the store, which is what makes this a test of the arm rather than of the
     scene. *)
  let cited =
    Explanation.combine
      [
        Explanation.term 1 (Explanation.model_row 3);
        Explanation.term 2 (Explanation.model_row 9);
      ]
      2
  in
  let cite_reason = [ Reason.at_least ~name:"y" ~decl:0 2 ] in
  check "D-0038/D-0026: a cited bound agrees, because the trail holds it up"
    (Store.agreement_holds derived (Reason.because ~concludes:None cite_reason cited));
  check "D-0038/D-0026: and the SAME pair disagrees when nothing established that bound"
    (not (Store.agreement_holds plain (Reason.because ~concludes:None cite_reason cited)));
  (* The direction matters too: [y]'s LOWER bound is supported, its upper bound is not. *)
  check "D-0026: the support consulted is the one the fact's direction names"
    (not
       (Store.agreement_holds derived
          (Reason.because ~concludes:None [ Reason.at_most ~name:"y" ~decl:9 4 ] cited)));

  (* A [Weaken] summand shares NO literal with the reason (declared-width chain versus
     the current bound), so this has to compare scopes and not literals. A check written
     over [Explanation.lits] equality would call every real [Linear] pruning a
     disagreement. *)
  let weaken_only =
    Explanation.combine
      [
        Explanation.term 1 (Explanation.model_row 3);
        Explanation.weaken [ (2, Lit.ge "x" 1); (2, Lit.ge "x" 2) ];
      ]
      2
  in
  check "D-0026: a reason agrees with a justification that only WEAKENS its variable"
    (Store.agreement_holds plain
       (Reason.because ~concludes:None
          [ Reason.at_least ~name:"x" ~decl:0 2 ]
          weaken_only)
    && Reason.lits [ Reason.at_least ~name:"x" ~decl:0 2 ] <> Explanation.lits weaken_only
    );

  (* THE REVERSE DIRECTION, which is I-P5's: the derivation weakened [x] out of its own
     row, so the pruning depends on where [x] sits, so the reason must name it. Dropping
     it leaves a trace line over too short a tail -- an unconditional claim on a
     satisfiable model. *)
  check "I-P5/D-0026: a reason that OMITS a variable the derivation weakens DISAGREES"
    (not
       (Store.agreement_holds plain
          (Reason.because ~concludes:None Reason.none weaken_only)));
  check
    "I-P5/D-0026: naming a different variable does not substitute for the weakened one"
    (not
       (Store.agreement_holds plain
          (Reason.because ~concludes:None
             [ Reason.at_least ~name:"y" ~decl:0 2 ]
             weaken_only)));

  (* And it looks THROUGH a Deferred: a propagator's justification is a thunk, so a check
     that gave up on an unforced one would never fire in production. *)
  check "D-0026: the check forces a Deferred justification rather than passing it"
    (not
       (Store.agreement_holds plain
          (Reason.because ~concludes:None
             [ Reason.at_least ~name:"z" ~decl:0 2 ]
             (Explanation.deferred (fun () -> expl)))))

(* ---------------------------------------------------------------------------
   M2-L0 / D-0043, test (b): the agreement check becomes EXACT.

   M2-T8 handed this back as a known limitation and named it precisely: the forward arm
   of [agreement_holds] catches a reason naming the wrong *variable*, and not the right
   variable at the wrong *value*, because its second arm ("...or the fact has a support")
   is satisfied by any bound the trail happens to hold. It could not do better: nothing
   in the pruning said what it concluded, so there was no value to compare against.

   [Store.conclusion_holds] is that comparison, and it is exact in all three coordinates.
   The break the roadmap asks for is I-X9's shape and the M1-T44 defect: a claim ONE UNIT
   off the bound the trail actually holds. Off by one in either direction is wrong --
   a weaker claim is what M1-T51 measured the checker silently accepting, and a stronger
   one is a claim the store cannot back at all.
   --------------------------------------------------------------------------- *)
let test_conclusion () =
  let store =
    Store.create ~names:[| "x"; "y" |] ~domains:[| Domain.make 0 9; Domain.make 0 9 |]
  in
  let v = Var.of_int 0 in
  (* The justification mentions both variables, so the M2-T8 scope check PASSES on every
     [j] below -- which is what makes the last check in this test a measurement of what
     the conclusion adds rather than a restatement of what the scope check already did. *)
  let expl = Explanation.clause [ Lit.ge "x" 3; Lit.le "y" 4 ] in
  let j concludes =
    Reason.because ~concludes [ Reason.at_least ~name:"y" ~decl:0 1 ] expl
  in
  (* The change under test: x's lower bound moves 0 -> 3, its upper bound stays at 9. *)
  let old = Domain.make 0 9 and now = Domain.make 3 9 in
  let holds c = Store.conclusion_holds store v ~old ~now (j c) in
  check "D-0043 (b): the exact bound this change produced AGREES"
    (holds (Some (Reason.at_least ~name:"x" ~decl:0 3)));
  check "D-0043 (b): no conclusion at all agrees -- that is what [None] is for"
    (holds None);
  (* THE BREAK, both ways. One unit weak and one unit strong; the old check could see
     neither, because "x" has a support the moment anything moved its bound. *)
  check "D-0043 (b) THE BREAK: a conclusion ONE UNIT WEAK than the trail bound DISAGREES"
    (not (holds (Some (Reason.at_least ~name:"x" ~decl:0 2))));
  check
    "D-0043 (b) THE BREAK: a conclusion ONE UNIT STRONG than the trail bound DISAGREES"
    (not (holds (Some (Reason.at_least ~name:"x" ~decl:0 4))));
  (* The other two coordinates, so that "exact" means all three and not just the value. *)
  check "D-0043 (b): the right value on the WRONG VARIABLE disagrees"
    (not (holds (Some (Reason.at_least ~name:"y" ~decl:0 3))));
  check
    "D-0043 (b): the right variable in the direction this change did NOT move disagrees"
    (not (holds (Some (Reason.at_most ~name:"x" ~decl:9 9))));
  (* And the limitation being removed, stated as a test rather than as a claim: the OLD
     check accepts every one of the breaks above. It is not wrong -- it is answering a
     different question (which variables, not which value) -- so this is a record of what
     [conclusion_holds] adds, and it will go on passing. *)
  check
    "D-0043 (b): the M2-T8 scope check accepts the one-unit-off claim -- this is the \
     limitation the conclusion removes, not a defect in it"
    (Store.agreement_holds store (j (Some (Reason.at_least ~name:"x" ~decl:0 2))));
  (* THE SETTLE WINDOW, which BAGUETTE_DEBUG measured rather than anybody designing it.
     [Domain.set_lo] settles over the holes above the bound it is given (I-D2), so the
     bound a propagator asks for and the bound the trail ends up holding are two
     different numbers whenever a hole sits between them -- `x` over `0..9 \ {2}`, told
     `x >= 2`, lands at 3. Both are honest claims about that one change: 2 is what the
     row derives and what its [pol] is checked against, 3 is what lib/core/trace.ml's
     line claims while citing the hole as [settled_over]. The window between them is
     exactly the settled holes, and a claim that steps across a value which is NOT a
     hole is still rejected. *)
  let holed =
    match Domain.remove (Domain.make 0 9) 2 with
    | Domain.Changed d -> d
    | _ -> failwith "D-0043 (b): the hole scene punched no hole"
  in
  let settled =
    match Domain.set_lo holed 2 with
    | Domain.Changed d -> d
    | _ -> failwith "D-0043 (b): the settle scene moved no bound"
  in
  let across c = Store.conclusion_holds store v ~old:holed ~now:settled (j (Some c)) in
  check "D-0043 (b): the scene really settles -- x >= 2 over 0..9 \\ {2} lands at 3"
    (Domain.lo settled = 3);
  check
    "D-0043 (b): the bound the PROPAGATOR derived (2) is accepted although the trail \
     holds 3 -- the gap is one hole wide and the hole is what closes it"
    (across (Reason.at_least ~name:"x" ~decl:0 2));
  check "D-0043 (b): the bound the TRAIL holds (3) is accepted too"
    (across (Reason.at_least ~name:"x" ~decl:0 3));
  check
    "D-0043 (b): but 1 is REJECTED -- it steps across a value that is not a hole, so the \
     window is a settle and not slack"
    (not (across (Reason.at_least ~name:"x" ~decl:0 1)));
  (* An upper-bound move, so the [At_most] arm is not tested only by its refusals. *)
  let old = Domain.make 0 9 and now = Domain.make 0 4 in
  check "D-0043 (b): the same, exact, for an upper bound"
    (Store.conclusion_holds store v ~old ~now
       (j (Some (Reason.at_most ~name:"x" ~decl:9 4))));
  check "D-0043 (b): one unit off the new upper bound DISAGREES"
    (not
       (Store.conclusion_holds store v ~old ~now
          (j (Some (Reason.at_most ~name:"x" ~decl:9 5)))))

(* ---------------------------------------------------------------------------
   M2-L0 / D-0043, test (c): the partition, at the store.

   D-0043's optional conclusion is principled rather than partial: a pruning that moved a
   bound concludes it, a DECISION concludes nothing (D-0037 -- it is an assumption, and
   nothing in the proof establishes it), and a CONFLICT concludes falsity rather than a
   bound. The line-or-no-line half of this -- that lib/core/trace.ml writes a line for a
   pruning and none for a decision -- is asserted against [Trace.claims] in
   test_prop.ml's [test_conclusion_partition]; what belongs here is the store's own
   enforcement, because a decision's numbers AGREE with the bound it set, so
   [conclusion_holds] alone would accept one that claimed to have derived it.
   --------------------------------------------------------------------------- *)
let test_decision_concludes_nothing () =
  let decision c =
    Reason.because ~concludes:c Reason.none (Explanation.decision (Lit.ge "x" 3))
  in
  let pruning c =
    Reason.because ~concludes:c Reason.none (Explanation.clause [ Lit.ge "x" 3 ])
  in
  let fact = Some (Reason.at_least ~name:"x" ~decl:0 3) in
  check "D-0043 (c): a decision carrying no conclusion is accepted -- the control"
    (Store.decision_concludes_nothing (decision None));
  check
    "D-0043 (c) THE BREAK: a decision that claims to have DERIVED its bound is rejected \
     (D-0037: it is an assumption)"
    (not (Store.decision_concludes_nothing (decision fact)));
  check "D-0043 (c): the same conclusion on a derived pruning is fine"
    (Store.decision_concludes_nothing (pruning fact));
  (* The numbers agree -- which is the whole point of having a second check. A decision
     setting x >= 3 really does leave the trail at 3, so the exact check passes it. *)
  let store = Store.create ~names:[| "x" |] ~domains:[| Domain.make 0 9 |] in
  check
    "D-0043 (c): and [conclusion_holds] alone would NOT catch it -- the bound a decision \
     sets is the bound it would claim"
    (Store.conclusion_holds store (Var.of_int 0) ~old:(Domain.make 0 9)
       ~now:(Domain.make 3 9) (decision fact))

(* Performing the break, rather than reading the code: re-run this very binary with
   BAGUETTE_DEBUG=1 in a mode that pushes a disagreeing pruning, and require it to die.
   The control -- the same push with an agreeing reason -- must survive, or a non-zero
   exit would prove nothing about the check. *)
let disagreeing_push ~agree () =
  let store =
    Store.create ~names:[| "x"; "y" |] ~domains:[| Domain.make 0 5; Domain.make 0 5 |]
  in
  let name = if agree then "x" else "z" in
  let j =
    Reason.because ~concludes:None
      [ Reason.at_least ~name ~decl:0 3 ]
      (Explanation.clause [ Lit.ge "x" 1 ])
  in
  ignore (Store.set_lo store (Var.of_int 0) 2 j)

(* The same treatment for D-0043's two checks: a check that only a unit test calls is a
   predicate, not an invariant. These push through [Store.set_lo] for real, so what is
   being measured is that [apply] consults them. [off] is the one-unit-off conclusion
   (test (b)) and [decision] is the decision that claims its own bound (test (c)). *)
let conclusion_push ~off ~decision () =
  let store =
    Store.create ~names:[| "x"; "y" |] ~domains:[| Domain.make 0 5; Domain.make 0 5 |]
  in
  let concludes = Some (Reason.at_least ~name:"x" ~decl:0 (if off then 3 else 2)) in
  let justification =
    if decision then Explanation.decision (Lit.ge "x" 2)
    else Explanation.clause [ Lit.ge "x" 2 ]
  in
  ignore
    (Store.set_lo store (Var.of_int 0) 2
       (Reason.because ~concludes Reason.none justification))

let test_agreement_is_wired () =
  let run mode =
    Sys.command
      (Printf.sprintf "BAGUETTE_DEBUG=1 %s %s >/dev/null 2>&1"
         (Filename.quote Sys.executable_name)
         mode)
  in
  check "D-0026: BAGUETTE_DEBUG accepts a pruning whose reason agrees (the control)"
    (run "--agreeing-push" = 0);
  check "D-0026: BAGUETTE_DEBUG REJECTS a pruning whose reason names a stray variable"
    (run "--disagreeing-push" <> 0);
  check
    "D-0043 (b): BAGUETTE_DEBUG accepts a pruning whose conclusion IS the bound it set \
     (the control)"
    (run "--exact-conclusion" = 0);
  check
    "D-0043 (b): BAGUETTE_DEBUG REJECTS a pruning whose conclusion is ONE UNIT off the \
     bound the trail holds (I-X9's shape, the M1-T44 defect)"
    (run "--off-by-one-conclusion" <> 0);
  check
    "D-0043 (c): BAGUETTE_DEBUG REJECTS a DECISION that carries a conclusion, although \
     its numbers agree with the bound it set"
    (run "--decision-with-a-conclusion" <> 0)

(* ------------------------------------------------------------------ *)
(* Views (M4-T0)                                                       *)
(*                                                                     *)
(* A view is [+/-x + k] over a store variable, or a constant. It has no *)
(* domain, no store slot and no trail slot of its own; every operation  *)
(* is a translation of one integer onto the BASE. The three things      *)
(* below are the three ways that can be got wrong:                     *)
(*                                                                     *)
(*   (a) the link. Reading a view must see the base's LIVE domain and   *)
(*       pruning a view must move the base -- both directions, and the  *)
(*       negated sign is where an off-by-one hides.                    *)
(*   (b) the trail. A view must not smuggle a second trail past I-T1 /  *)
(* I-X4. The check is not "backtracking works" but "the entry     *)
   (*       pushed is ONE ordinary entry against the base". *)
(*   (d) constants. [Const c] must be a special case of the ARITHMETIC  *)
(*       and of nothing else -- in particular its conflict must be the  *)
(*       same VALUE a variable's failed narrowing produces.            *)
(* ------------------------------------------------------------------ *)

let view_store () =
  Store.create ~names:[| "x"; "y" |] ~domains:[| Domain.make 0 5; Domain.make 0 5 |]

let view_why () = Reason.because ~concludes:None Reason.none (Explanation.model_row 1)

let test_view_link () =
  let s = view_store () in
  let x = Var.of_int 0 in
  let why = view_why () in
  let plain = View.of_var x in
  let up = View.shift plain 3 in
  (* [7 - x], the reversed term, built by composition rather than by its own case. *)
  let down = View.sub_from 7 plain in
  check "view: an offset view's bounds are the image of the base's"
    (View.lo s up = 3 && View.hi s up = 8);
  check "view: a negated view SWAPS the bounds" (View.lo s down = 2 && View.hi s down = 7);
  check "view: a view of a view stays flat -- -(x+3)+10 is 7-x"
    (View.equal (View.shift (View.negate up) 10) down);

  (* Direction 1: pruning the BASE moves the view. *)
  ignore (Store.set_lo s x 1 why);
  check "view (a): pruning the base raises an offset view's lower bound"
    (View.lo s up = 4 && View.hi s up = 8);
  check "view (a): pruning the base lowers a NEGATED view's upper bound"
    (View.lo s down = 2 && View.hi s down = 6);

  (* Direction 2: pruning the VIEW moves the base. On the negated view, [down >= 3]
     is [x <= 4] -- a lower bound on the view is an UPPER bound on the base, and a
     view that got this wrong would prune the base the wrong way round while still
     looking self-consistent when read back through itself. *)
  check "view (a): a prune through the view reports Changed"
    (match View.set_lo s down 3 why with Store.Changed -> true | _ -> false);
  check "view (a): ... and it moved the BASE's upper bound" (Domain.hi (Store.get s x) = 4);
  check "view (a): ... which the offset view sees at once" (View.hi s up = 7);
  check "view (a): an offset view's own prune moves the base's lower bound"
    (match View.set_lo s up 5 why with
    | Store.Changed -> Domain.lo (Store.get s x) = 2
    | _ -> false);

  (* Holes travel too, in both directions and through the reversal. The base is kept
     wide enough here that removing 3 punches a real INTERIOR hole rather than moving
     a bound -- an earlier draft of this test narrowed the base first, so every
     "hole" check below passed against a bound move and could not see a reversal that
     was off by one. *)
  ignore (Store.remove s x 3 why);
  check "view (a): the scene really has an interior hole, so the checks below can see"
    (Domain.lo (Store.get s x) = 2
    && Domain.hi (Store.get s x) = 4
    && Domain.has_holes (Store.get s x)
    && not (Domain.mem (Store.get s x) 3));
  check "view (a): a hole in the base is a hole in the offset view"
    ((not (View.mem s up 6)) && View.mem s up 5 && View.mem s up 7);
  check "view (a): a hole in the base is the MIRRORED hole in a negated view"
    ((not (View.mem s down 4)) && View.mem s down 3 && View.mem s down 5);
  check "view (a): the materialised view domain agrees with mem, both signs"
    (Domain.to_list (View.domain s up) = List.filter (View.mem s up) [ 3; 4; 5; 6; 7; 8 ]
    && Domain.to_list (View.domain s down)
       = List.filter (View.mem s down) [ 2; 3; 4; 5; 6; 7 ]);
  check "view (a): ... and it really carries the hole, in both images"
    (Domain.has_holes (View.domain s up)
    && Domain.has_holes (View.domain s down)
    && Domain.to_list (View.domain s up) = [ 5; 7 ]
    && Domain.to_list (View.domain s down) = [ 3; 5 ]);
  check "view (a): size, is_fixed and value read through to the base"
    (View.size s up = Domain.size (Store.get s x)
    && View.is_fixed s up = Domain.is_fixed (Store.get s x));
  ignore (Store.fix s x 2 why);
  check "view (a): a fixed base gives every view its value"
    (View.value s up = Some 5 && View.value s down = Some 5 && View.value s plain = Some 2)

(* The cross-layer property: what a propagator sees and what the checker sees are one
   value. After [View.set_lo v n] the base's domain must ENTAIL the very literal
   [Lit.view_ge] renders for [v >= n] -- so the pruning the solver made and the fact
   the proof will claim cannot drift apart. Swept over both signs and a range of
   offsets, because the sign flip is where the two could agree on a name and disagree
   on a sense. *)
let test_view_agrees_with_its_literal () =
  let bad = ref None in
  let n_checked = ref 0 in
  let views = [ (false, 0); (false, 3); (false, -2); (true, 0); (true, 7); (true, -1) ] in
  List.iter
    (fun (negated, offset) ->
      for n = -4 to 12 do
        let s = view_store () in
        let x = Var.of_int 0 in
        let v =
          let base = View.of_var x in
          View.shift (if negated then View.negate base else base) offset
        in
        match View.set_lo s v n (view_why ()) with
        | Store.Conflict _ -> ()
        | Store.Unchanged | Store.Changed ->
            incr n_checked;
            let d = Store.get s x in
            let l = Option.get (View.lit_ge s v n) in
            let entailed =
              if l.Lit.positive then Domain.lo d >= Lit.value l.Lit.v
              else Domain.hi d <= Lit.value l.Lit.v - 1
            in
            (* And the solver's own reading of the view must agree with the bound
               it was asked for. *)
            if (not entailed) || View.lo s v < n then
              if !bad = None then
                bad :=
                  Some
                    (Printf.sprintf
                       "view (negated=%b, offset=%d) >= %d: base %s, literal %s, view lo \
                        %d"
                       negated offset n (Domain.to_string d) (Lit.to_string l)
                       (View.lo s v))
      done)
    views;
  check
    "view: after a prune, the base ENTAILS the literal the proof will name -- the \
     solver's fact and the checker's fact are one value"
    (match !bad with
    | None -> true
    | Some w ->
        Printf.printf "     first offender: %s\n" w;
        false);
  check "view: the literal sweep actually ran" (!n_checked > 50);
  Printf.printf "     (swept %d view prunings against their literals)\n" !n_checked

let test_view_trail () =
  let s = view_store () in
  let x = Var.of_int 0 in
  let why = view_why () in
  let up = View.shift (View.of_var x) 3 in
  let down = View.sub_from 7 (View.of_var x) in
  let snap0 = Store.snapshot s in
  Store.new_level s;
  let before = Store.trail_length s in
  ignore (View.set_lo s up 4 why);
  check "view (b): a view prune pushes exactly ONE trail entry"
    (Store.trail_length s = before + 1);
  check "view (b): the entry it pushed is against the BASE variable"
    (Var.equal (Store.trail_entry s (Store.trail_length s - 1)).Store.var x);
  ignore (View.set_lo s down 3 why);
  check "view (b): a negated view's prune is one entry too"
    (Store.trail_length s = before + 2);
  check "view (b): the two prunes together left the base at 1..4"
    (Domain.lo (Store.get s x) = 1 && Domain.hi (Store.get s x) = 4);
  let snap1 = Store.snapshot s in
  Store.new_level s;
  ignore (View.remove s up 5 why);
  check "view (b): a hole punched through a view is a real INTERIOR hole in the base"
    ((not (Domain.mem (Store.get s x) 2))
    && Domain.has_holes (Store.get s x)
    && Domain.lo (Store.get s x) = 1
    && Domain.hi (Store.get s x) = 4);
  check "I-T3: trail invariants hold after view prunes" (Store.check_invariants s);
  Store.backtrack s;
  check "view (b): one level back restores exactly, hole included"
    (Store.same_domains s snap1);
  check "view (b): ... and the view reads the restored value"
    (View.mem s up 5 && View.lo s up = 4 && not (Domain.has_holes (Store.get s x)));
  Store.backtrack_to s 0;
  check "view (b): every domain restored exactly after a view-driven descent"
    (Store.same_domains s snap0);
  check "view (b): the view is back to its declared image"
    (View.lo s up = 3 && View.hi s up = 8 && View.lo s down = 2 && View.hi s down = 7);
  check "view (b): the trail is back where it started" (Store.trail_length s = 0);
  check "I-S3: level restored after view prunes" (Store.level s = 0)

let test_view_constants () =
  let s = view_store () in
  let why = view_why () in
  let c = View.const 7 in
  check "view (d): a constant reads as a one-value domain"
    (View.lo s c = 7
    && View.hi s c = 7
    && View.size s c = 1
    && View.is_fixed s c
    && View.value s c = Some 7);
  check "view (d): membership is equality" (View.mem s c 7 && not (View.mem s c 6));
  check "view (d): the materialised domain is the singleton"
    (Domain.equal (View.domain s c) (Domain.singleton 7));
  check "view (d): a constant declares no variables to watch (I-T4)" (View.vars c = []);
  check "view (d): shifting and negating a constant STAY constants -- no second path"
    (View.equal (View.shift c 2) (View.const 9)
    && View.equal (View.negate c) (View.const (-7))
    && View.equal (View.sub_from 10 c) (View.const 3));

  (* The narrowings. A constant answers the same question a variable does, with the
     same three outcomes, and never touches the store. *)
  let before = Store.trail_length s in
  check "view (d): a narrowing that keeps the value is Unchanged"
    (match View.set_lo s c 7 why with Store.Unchanged -> true | _ -> false);
  check "view (d): an upper bound that keeps it is Unchanged too"
    (match View.set_hi s c 9 why with Store.Unchanged -> true | _ -> false);
  check "view (d): removing another value is Unchanged"
    (match View.remove s c 6 why with Store.Unchanged -> true | _ -> false);
  check "view (d): fixing it to its own value is Unchanged"
    (match View.fix s c 7 why with Store.Unchanged -> true | _ -> false);
  check "view (d): a narrowing that excludes it is a Conflict"
    (match View.set_lo s c 8 why with Store.Conflict _ -> true | _ -> false);
  check "view (d): so is an upper bound below it"
    (match View.set_hi s c 6 why with Store.Conflict _ -> true | _ -> false);
  check "view (d): so is removing its own value"
    (match View.remove s c 7 why with Store.Conflict _ -> true | _ -> false);
  check "view (d): so is fixing it elsewhere"
    (match View.fix s c 5 why with Store.Conflict _ -> true | _ -> false);
  check "view (d): none of that touched the trail" (Store.trail_length s = before);

  (* The part that makes it "not a special case": the conflict a constant reports is
     the SAME value the store itself produces when a variable's narrowing empties its
     domain -- [unattributed_conflict], with [Reason.none]. A constant that reached
     for [Store.conflict] instead would carry the pruning's own reason and so write a
     conflict line over too few facts, and it would do so only for constants. *)
  (* The [Reason.justified] handed in here carries a REAL fact, which is what makes
     this lane able to see the difference at all: with [Reason.none] on the way in,
     [Store.conflict] and [Store.unattributed_conflict] return the same value and the
     check passes against either. Measured -- the first draft used [Reason.none] and
     reddened nothing when the arm was rewired. *)
  let x = Var.of_int 0 in
  let with_facts =
    Reason.because ~concludes:None
      [ Reason.at_least ~name:"x" ~decl:0 3 ]
      (Explanation.model_row 1)
  in
  let from_var =
    match Store.set_lo s x 9 with_facts with Store.Conflict cf -> Some cf | _ -> None
  in
  let from_const =
    match View.set_lo s c 8 with_facts with Store.Conflict cf -> Some cf | _ -> None
  in
  check "view (d): the lane's own reason is non-empty, so it can see the difference"
    (not (Reason.is_empty with_facts.Reason.reason));
  check "view (d): a constant's conflict is shaped exactly like a variable's"
    (match (from_var, from_const) with
    | Some a, Some b ->
        a.Store.c_prop = b.Store.c_prop
        && Reason.is_empty a.Store.c_reason
        && Reason.is_empty b.Store.c_reason
        && a.Store.c_why = b.Store.c_why
    | _ -> false);

  (* And a constant is a view like any other: the generic code path above it does not
     ask whether it is one. *)
  check "view (d): is_const classifies, it does not gate"
    (View.is_const c && not (View.is_const (View.of_var x)))

let () =
  match Array.to_list Sys.argv with
  | _ :: "--agreeing-push" :: _ -> disagreeing_push ~agree:true ()
  | _ :: "--disagreeing-push" :: _ -> disagreeing_push ~agree:false ()
  | _ :: "--exact-conclusion" :: _ -> conclusion_push ~off:false ~decision:false ()
  | _ :: "--off-by-one-conclusion" :: _ -> conclusion_push ~off:true ~decision:false ()
  | _ :: "--decision-with-a-conclusion" :: _ ->
      conclusion_push ~off:false ~decision:true ()
  | _ ->
      test_domains ();
      test_store ();
      test_explanations ();
      test_attribution ();
      test_reason ();
      test_bound_support ();
      test_agreement ();
      test_conclusion ();
      test_decision_concludes_nothing ();
      test_agreement_is_wired ();
      test_view_link ();
      test_view_agrees_with_its_literal ();
      test_view_trail ();
      test_view_constants ();
      if !failures > 0 then (
        Printf.printf "\n%d failure(s)\n" !failures;
        exit 1)
      else print_endline "\ncore unit tests passed"
