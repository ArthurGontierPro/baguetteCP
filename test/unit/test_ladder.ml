(* Unit tests for lib/core/ladder.ml -- M2-L11: the order-encoding ladder chain as a ROW,
   so that PB conflict analysis resolves against the reason [Linear] actually used.

   ---------------------------------------------------------------------------
   What this row is answering, and why a passing proof is not the answer
   ---------------------------------------------------------------------------

   M2-L6's finding is that our integer propagator is STRONGER than PB propagation on the
   same row, because the strength is in the order encoding's ladder implications and those
   live in separate .opb rows (D-0028). docs/EXPLANATION-REVIEW.md section 4 points out
   that this is a PREDICTION and not merely a post-hoc explanation: PB conflict analysis
   will keep falling back for as long as a reason is the model row WITHOUT its ladder
   chain.

   So the thing under test is not "does the proof check". M1-T42, M1-T51 and M2-T9's
   "Break A" each found the checker accepting a well-formed but WRONG derivation, and a
   green veripb run over a lift that never fired would look exactly like a green veripb
   run over a lift that did. Every section below therefore has a BREAK, and the break is
   performed through a knob the solver exports ([Search.config]) rather than by editing
   emitted bytes -- a lane that mutates bytes proves the checker reads bytes, not that
   the ladder chain is load-bearing.

   The four sections are docs/ROADMAP.md M2-L11's four tests:

     (a) the `3a + 2b <= 14`, `lo(b) = 4` scene: the COMBINED row propagates `a <= 2`
         where the bare model row does not. Broken by withholding the ladder ids.
     (b) the learned row is NON-DEGENERATE -- not the empty contradiction -- and the
         counter says so. Broken by [pb_ladder = false], which is the M2-L6 build: the
         rows disappear entirely.
     (c) the proof veripb 3.0.2 accepts, AND the chain is not double-counted. Broken by
         [break_ladder_mult], which writes one rung at the wrong multiplier while still
         claiming the right conclusion -- sound, well-formed, and not the claimed row.
     (d) the standing hazard: [Order_reason.weaken_declared] and
         [Encoding.expand_int_lin_le] must still agree on the constant. Broken by
         offsetting the chain from the CURRENT bound instead of the DECLARED one, which
         is the specific drift the hazard is about.

   Domains here are 0..4 and smaller (D-0028: the order encoding is width-proportional
   and a wide domain is a proof that dwarfs the suite). *)

module F = Baguette_flatzinc
module Compile = F.Compile
module Store = Baguette_core.Store
module Domain = Baguette_core.Domain
module Search = Baguette_core.Search
module Justify = Baguette_core.Justify
module Ladder = Baguette_core.Ladder
module Learned = Baguette_core.Learned
module Reduce = Baguette_core.Reduce
module Pb = Baguette_core.Pb_analysis
module Explanation = Baguette_core.Explanation
module Order_reason = Baguette_core.Order_reason
module Engine = Baguette_core.Engine
module Propagator = Baguette_core.Propagator
module Encoding = Baguette_proof.Encoding
module Writer = Baguette_proof.Writer
module Opb = Baguette_proof.Opb
module Lit = Baguette_proof.Lit

let () = Mem_guard.install ()
let failures = ref 0

let check name cond =
  if cond then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s\n" name)

let check_eq name got want =
  if got = want then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s: got %d, want %d\n" name got want)

let contains ~needle haystack =
  let n = String.length needle and h = String.length haystack in
  if n = 0 then true
  else
    let found = ref false in
    for i = 0 to h - n do
      if (not !found) && String.equal (String.sub haystack i n) needle then found := true
    done;
    !found

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

(* ------------------------------------------------------------------ scenes *)

(* THE ROADMAP'S OWN SCENE, verbatim: `3a + 2b <= 14` over a, b declared 0..4. The second
   row is what establishes `lo(b) = 4`; it is a separate instance so that the row under
   test is the two-term one and nothing else. *)
let worked_src =
  "var 0..4: a;\n\
   var 0..4: b;\n\
   constraint int_lin_le([3,2],[a,b],14);\n\
   constraint int_lin_le([-1],[b],-4);\n\
   solve satisfy;\n"

(* test/models/ladder_lift_unsat.fzn, verbatim. See that file's header for why each part
   of it is needed; the short version is that R1 and R2 are jointly infeasible and BOUNDS
   PROPAGATION AT THE ROOT CANNOT SEE IT, so the search has to branch and the conflicts
   reach PB analysis at a decision level. *)
let fixture_src =
  "var 0..1: p;\n\
   var 0..1: q;\n\
   var 0..3: x1;\n\
   var 0..3: x2;\n\
   var 0..4: x3;\n\
   constraint int_lin_le([3,1,2],[x1,x2,x3],4);\n\
   constraint int_lin_le([-4,-2,-3],[x1,x2,x3],-8);\n\
   solve satisfy;\n"

let compile src = Compile.compile (F.Builder.of_string ~file:"test" src)

(* Every PB row the engine exposes, in instance order. *)
let all_rows (c : Compile.t) =
  let e = c.Compile.engine and s = c.Compile.store in
  List.filter_map (fun i -> Engine.row_of e s i) (List.init (Engine.n_instances e) Fun.id)

(* ------------------------------------------------- a brute-force entailment oracle *)

(* Does [row] hold at the 0-1 point [assign]? *)
let row_holds assign (row : Learned.t) =
  let s =
    List.fold_left
      (fun acc (tm : Learned.term) ->
        let l = tm.Learned.lit in
        let v = assign l.Lit.v in
        let bit = if l.Lit.positive then v else not v in
        if bit then acc + tm.Learned.coeff else acc)
      0 (Learned.terms row)
  in
  s >= Learned.degree row

(* Every pseudo-Boolean variable mentioned by any of [rows], sorted, deduplicated. *)
let universe rows =
  let acc = ref [] in
  List.iter
    (fun r ->
      List.iter
        (fun (tm : Learned.term) ->
          let v = tm.Learned.lit.Lit.v in
          if not (List.exists (fun w -> Lit.var_equal v w) !acc) then acc := v :: !acc)
        (Learned.terms r))
    rows;
  List.sort Lit.var_compare !acc

(* Count the 0-1 points at which every row of [premises] holds but [conclusion] does not.
   0 means [premises] entail [conclusion], over EVERY 0-1 point and not only the
   ladder-consistent ones -- which is the right standard, because a cutting-planes
   derivation is sound at every 0-1 point.

   Refuses to run past 2^20 points rather than quietly taking hours; the scenes here are
   two variables declared 0..4, i.e. 8 pseudo-Boolean variables. *)
let counterexamples ~premises ~conclusion =
  let vars = Array.of_list (universe (conclusion :: premises)) in
  let n = Array.length vars in
  if n > 20 then None
  else
    let bad = ref 0 in
    for mask = 0 to (1 lsl n) - 1 do
      let assign v =
        let rec idx i = if Lit.var_equal vars.(i) v then i else idx (i + 1) in
        mask land (1 lsl idx 0) <> 0
      in
      if List.for_all (row_holds assign) premises && not (row_holds assign conclusion)
      then incr bad
    done;
    Some !bad

(* ------------------------------------------------------------------ the checker *)

let veripb_path () = Baguette_proof.Checker.find ()

let veripb ~dir ~opb ~pbp =
  match veripb_path () with
  | None -> None
  | Some exe ->
      let log = Filename.concat dir "log" in
      let rc =
        Sys.command
          (Printf.sprintf "%s %s %s > %s 2>&1" (Filename.quote exe) (Filename.quote opb)
             (Filename.quote pbp) (Filename.quote log))
      in
      let out = read_file log in
      (try Sys.remove log with _ -> ());
      Some (rc = 0, out)

(* THE WORDING, at full strength. MEASURED on 2026-09-18 by running section (c)'s break
   against veripb 3.0.2, not guessed:

     "Expected constraint is not syntactically implied by the constraint at the hint."

   That sentence is a JUDGEMENT about the arithmetic of a `pol` whose claim was stated
   through [Justify.emit_stating] -- it is the checker saying "your row is not what your
   derivation computes". It is matched whole rather than on a fragment: "reverse unit
   propagation" would have matched any other RUP failure anywhere in the proof, and an
   exit status alone cannot tell a judgement from a parse error, which is the hole M2-T14
   found four lanes sitting in. *)
let ladder_rejection = "not syntactically implied by the constraint at the hint"

(* ------------------------------------------------------------------ a whole solve *)

type run = { r_stats : Search.stats; r_dir : string; r_opb : string; r_pbp : string }

(* Solve one model into a scratch directory, with the audit on, and keep the artefacts so
   the checker can be run over them. *)
let run ?(config = Search.default_config) src =
  let c = compile src in
  let dir = Filename.temp_file "baguette_ladder" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  let opb = Filename.concat dir "m.opb" and pbp = Filename.concat dir "m.pbp" in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "M2-L11" ] c.Compile.encoding oc;
  close_out oc;
  let oc = open_out pbp in
  let writer = Writer.create ~audit:true oc in
  Encoding.start_proof c.Compile.encoding writer;
  let ctx = Justify.create ~writer ~encoding:c.Compile.encoding in
  let stats = Search.stats_create () in
  (try
     ignore
       (Search.solve ~engine:c.Compile.engine ~store:c.Compile.store ~ctx
          ~check:(fun _ -> true)
          ~stats ~config ()
         : Search.outcome)
   with Writer.Audit_failed r ->
     incr failures;
     Printf.printf "FAIL the run raised Audit_failed: %s\n" r);
  close_out oc;
  { r_stats = stats; r_dir = dir; r_opb = opb; r_pbp = pbp }

let cleanup r =
  List.iter (fun f -> try Sys.remove f with _ -> ()) [ r.r_opb; r.r_pbp ];
  try Sys.rmdir r.r_dir with _ -> ()

(* =================================================================== (a) *)

(* Test (a), and it is the roadmap row restated as arithmetic.

     3a + 2b <= 14,  a, b declared 0..4,  lo(b) = 4 already established.

   [Linear] deduces `a <= 2`, correctly. The row's PB form is

     3~[a>=1] + 3~[a>=2] + 3~[a>=3] + 3~[a>=4] + 2~[b>=1] + ... + 2~[b>=4] >= 6

   and with b at 4 every b term is falsified, leaving slack (3+3+3+3) - 6 = 6 against the
   pivot's coefficient 3. THE BARE ROW DOES NOT PB-PROPAGATE `a <= 2`. With the two rungs
   of a's ladder added -- 3 on L_1 and 3+3 = 6 on L_2 -- it does, at coefficient 9
   against the same slack 6.

   The falsified predicate is written out by hand and NOT read from the store after
   propagation, deliberately: [Pb_analysis] freezes it AT THE PROPAGATION (I-X6), where
   `hi(a)` is still its declared 4. A predicate read from the post-propagation store
   would already know `a <= 2` and the test would be asserting a tautology. *)
let test_worked_case () =
  print_endline
    "\n-- M2-L11 (a): the combined row propagates a <= 2, the bare row does not";
  let c = compile worked_src in
  let store = c.Compile.store and enc = c.Compile.encoding in
  (* First: the propagator really does make this pruning. Without this the rest of the
     section is arithmetic about a deduction nobody claimed. *)
  (match Engine.propagate c.Compile.engine store with
  | Engine.Conflict _ -> check "a: the root fixpoint is conflict-free" false
  | Engine.Fixpoint -> check "a: the root fixpoint is conflict-free" true);
  (match Store.var_named store "a" with
  | None -> check "a: the model declares a" false
  | Some v ->
      check_eq "a: Linear deduces a <= 2 from 3a+2b<=14 with lo(b)=4"
        (Domain.hi (Store.get store v))
        2);
  (match Store.var_named store "b" with
  | None -> check "a: the model declares b" false
  | Some v -> check_eq "a: ...because lo(b) is 4" (Domain.lo (Store.get store v)) 4);
  (* The row itself, as the .opb holds it. There are two int_lin_le instances; the one
     under test is the two-term row, identified by its term count rather than by a
     guessed id. *)
  let rows = all_rows c in
  match List.find_opt (fun r -> List.length r.Propagator.r_terms = 8) rows with
  | None -> check "a: the 3a+2b<=14 row is exposed as a PB row" false
  | Some pb -> (
      check "a: the 3a+2b<=14 row is exposed as a PB row" true;
      let row = Learned.of_pb_row pb in
      check_eq "a: ...and its degree is 6, as PROOF-FORMAT section 3's substitution gives"
        (Learned.degree row) 6;
      (* Frozen at the propagation: lo(b) = 4 and a still at its declared 0..4. *)
      let falsified (l : Lit.t) =
        match l.Lit.v with
        | Lit.Ge ("b", k) when k <= 4 -> not l.Lit.positive
        | _ -> false
      in
      let pivot = Lit.le "a" 2 (* = ~[a>=3] *) in
      check "a: THE BARE MODEL ROW DOES NOT PB-PROPAGATE a <= 2"
        (not (Reduce.propagates row ~pivot ~falsified));
      check_eq "a: ...its slack is 6 against a pivot coefficient of 3"
        (Reduce.slack row ~falsified) 6;
      let ladder_id = Encoding.consistency_id enc in
      (match Ladder.lift ~row ~pivot ~falsified ~ladder_id with
      | None -> check "a: the ladder lift applies" false
      | Some lt -> (
          check "a: the ladder lift applies" true;
          check_eq "a: it climbs exactly two rungs of a's ladder (L_1 and L_2)"
            lt.Ladder.rungs 2;
          check "a: and it cites a's consistency rows, by the ids Encoding handed out"
            (List.map Option.some (Ladder.cited_ids lt)
            = [ ladder_id "a" 1; ladder_id "a" 2 ]);
          (* THE SHAPE, against the constraint the encoding actually appended and not
             against [Ladder]'s own comment. [Encoding.constraints] is in id order, so the
             row with id [cid] is at index [cid - 1]. If [declare_int] ever wrote the
             ladder differently, the [pol] would cite a row that does not say what this
             module assumed and the arithmetic would be wrong while still checking out as
             a well-formed derivation of something else. *)
          let appended = Array.of_list (Encoding.constraints enc) in
          List.iter2
            (fun v cid ->
              let c = appended.(cid - 1) in
              check
                (Printf.sprintf "a: ladder row L_%d is the constraint the .opb holds" v)
                (Learned.to_string (Learned.make (Opb.terms c) (Opb.rhs c))
                = Learned.to_string (Ladder.ladder_row ~name:"a" v)))
            [ 1; 2 ] (Ladder.cited_ids lt);
          (* NOT THE SAME OBJECT AS [Order_reason]'s CHAIN, and it cannot become one.
             [Order_reason.weaken_declared] builds LITERAL AXIOMS, which name no
             constraint id at all; this module cites ROW IDS. Asserted rather than argued,
             because "they are different objects" is exactly the kind of claim that stops
             being true when someone unifies them. *)
          let ws, _ =
            Order_reason.weaken_declared ~coeff:3 ~name:"a" ~decl_lo:0 ~decl_hi:4
          in
          check "a: Order_reason's chain cites no constraint id -- it is literal axioms"
            (Pb.cited_ids (Explanation.combine [ Explanation.weaken ws ] 1) = []);
          check
            "a: ...while the ladder chain cites the model row and its rungs, once each"
            (Pb.cited_ids (Ladder.derive lt (Explanation.model_row 999))
            = 999 :: Ladder.cited_ids lt);
          (* THE ASSERTION THE WHOLE ROW IS FOR. *)
          check "a: THE COMBINED ROW DOES PB-PROPAGATE a <= 2"
            (Reduce.propagates lt.Ladder.lifted ~pivot ~falsified);
          check_eq "a: ...at pivot coefficient 9 -- 3 of its own plus 3 + 3 lifted"
            (Option.value ~default:0 (Reduce.coeff_of lt.Ladder.lifted pivot))
            9;
          check_eq "a: ...against the same slack 6, which the lift does not move"
            (Reduce.slack lt.Ladder.lifted ~falsified)
            6;
          (* NOT DOUBLE-COUNTED, in the crispest available form: a ladder addition
             substitutes one rung for the next and leaves the degree exactly where it
             was. A chain counted twice would move it. *)
          check_eq "a: the lift is degree-neutral -- the chain is not counted twice"
            (Learned.degree lt.Ladder.lifted)
            (Learned.degree row);
          (* And the reduction, which is what PB analysis actually asks for. *)
          let v = { Reduce.row = lt.Ladder.lifted; pivot; falsified } in
          (match Reduce.round_to_one.Reduce.reduce v with
          | None -> check "a: roundToOne reduces the lifted row" false
          | Some o ->
              check "a: roundToOne reduces the lifted row" true;
              check "a: ...and its own postcondition holds on the result"
                (Reduce.postcondition_holds Reduce.round_to_one v o);
              check_eq "a: ...leaving slack exactly 0, which is what Reduce promises"
                (Reduce.slack o.Reduce.reduced ~falsified)
                0);
          (* The oracle, both ways round. The second half is the FINDING as an oracle:
             the model row alone genuinely does not entail the lifted row, which is why
             the ladder rows have to be premises and not decoration. *)
          let l1 = Ladder.ladder_row ~name:"a" 1 and l2 = Ladder.ladder_row ~name:"a" 2 in
          (match
             counterexamples ~premises:[ row; l1; l2 ] ~conclusion:lt.Ladder.lifted
           with
          | None -> check "a: the oracle ran" false
          | Some n ->
              check_eq "a: {model row, L_1, L_2} entail the lifted row at every 0-1 point"
                n 0);
          match counterexamples ~premises:[ row ] ~conclusion:lt.Ladder.lifted with
          | None -> check "a: the oracle ran" false
          | Some n ->
              check "a: ...and the MODEL ROW ALONE does not -- the ladder rows are needed"
                (n > 0)));
      (* ---------------------------------------------------------------- the break *)
      (* Withhold the ladder ids. Nothing else changes: the same row, the same pivot, the
         same frozen predicate. If the chain were decoration the lift would still find
         something; it finds nothing, and the bare row still does not propagate. *)
      match Ladder.lift ~row ~pivot ~falsified ~ladder_id:(fun _ _ -> None) with
      | Some _ ->
          incr failures;
          print_endline
            "FAIL a/break: the lift claimed rungs with no ladder ids available. It is \
             citing a row the encoding did not hand it."
      | None ->
          check "a/break: with the ladder ids withheld the lift finds nothing" true;
          check "a/break: ...and the bare row still does not propagate a <= 2"
            (not (Reduce.propagates row ~pivot ~falsified)))

(* =================================================================== (b) *)

(* Test (b). Before this row no counter in this solver could tell a learned CONTRADICTION
   from a learned INEQUALITY, so "PB learning improved" was not a claim any measurement
   could carry -- and M2-L6's "36 of 36 degenerate" went unchallenged because of it (it is
   26 of 36 NON-degenerate; see [Search.n_pb_nondegenerate]). This section is the counter
   that can tell them apart, plus the break that shows this fixture's number is about the
   ladder and not about the weather.

   The control matters as much as the measurement: [test_degenerate_control] below runs a
   model whose learned rows really ARE the empty contradiction and asserts the counter
   reads 0 there. A counter that only ever goes up is not evidence.

   The break is [pb_ladder = false], which is behaviourally the M2-L6 build: the lift is a
   RETRY after the bare row fails, so with it off every conflict takes the derivation
   M2-L6 took. On this fixture that means NOTHING is learned on the PB path at all. *)
let test_nondegenerate_counter () =
  print_endline
    "\n-- M2-L11 (b): a NON-DEGENERATE learned row, and the counter that says so";
  let on = run fixture_src in
  let s = on.r_stats in
  check_eq "b: the fixture reaches PB analysis twice" s.Search.n_pb_attempts 2;
  check_eq "b: both conflicts learn a PB row" s.Search.n_pb_learned 2;
  check_eq "b: ...with no fallback" s.Search.n_pb_fallback 0;
  check_eq "b: BOTH LEARNED ROWS ARE NON-DEGENERATE -- not the empty contradiction"
    s.Search.n_pb_nondegenerate 2;
  check_eq "b: both were reached by resolving against model row PLUS a ladder chain"
    s.Search.n_pb_lifted 2;
  check "b: ...citing at least one ladder rung each" (s.Search.n_pb_rungs >= 2);
  (* The rows themselves, so that "non-degenerate" is a shape and not just a counter. *)
  let rows = Search.stats_pb_rows s in
  check "b: rows to inspect" (rows <> []);
  List.iteri
    (fun i (t : Pb.t) ->
      check
        (Printf.sprintf "b: row %d carries literals -- it is an inequality, not 0 >= k" i)
        (not (Learned.is_empty t.Pb.row));
      check
        (Printf.sprintf "b: row %d records the ladder rungs it used" i)
        (t.Pb.ladder_rungs > 0);
      (* The ladder rows are PREMISES, so the oracle must be shown them. It is: they are
         in [antecedent_rows], and this is the assertion that keeps them there. *)
      check
        (Printf.sprintf "b: row %d lists one antecedent row per cited id" i)
        (List.length t.Pb.antecedent_rows = List.length t.Pb.antecedents);
      match counterexamples ~premises:t.Pb.antecedent_rows ~conclusion:t.Pb.row with
      | None -> print_endline "     (oracle skipped: too many variables)"
      | Some n ->
          check_eq
            (Printf.sprintf "b: row %d is entailed by its antecedents at every 0-1 point"
               i)
            n 0)
    rows;
  cleanup on;
  (* ---------------------------------------------------------------- the break *)
  let off =
    run ~config:{ Search.default_config with Search.pb_ladder = false } fixture_src
  in
  let t = off.r_stats in
  check_eq "b/break: with the ladder withheld the same conflicts are still analysed"
    t.Search.n_pb_attempts 2;
  check_eq "b/break: ...and NOTHING is learned on the PB path" t.Search.n_pb_learned 0;
  check_eq "b/break: ...every conflict falls back to the M2-L3 clause path"
    t.Search.n_pb_fallback 2;
  check_eq "b/break: ...so the non-degenerate count is 0, which is M2-L6's number"
    t.Search.n_pb_nondegenerate 0;
  cleanup off

(* THE CONTROL for (b). backjump_lineq_unsat.fzn's source, verbatim: the int_lin_eq
   family, where the `>=` half rounds to `sum >= 3`, the `<=` half rounds to `sum <= 2`,
   and the two add to `0 >= k` in ONE elimination. Those rows genuinely ARE the empty
   contradiction -- the emitted proof states them as a bare `ia >= 9007199254740992` with
   no terms at all -- and the counter must read 0 on them.

   Without this, [n_pb_nondegenerate] could be a counter that only ever goes up, which is
   not evidence of anything. With it, the counter is shown to distinguish the two shapes
   on real solves in both directions. *)
let degenerate_src =
  "var 0..1: p;\n\
   var 0..1: q;\n\
   array [1..3] of int: c = [18014398509481984, 18014398509481984, 18014398509481984];\n\
   var 0..3: x1;\n\
   var 0..3: x2;\n\
   var 0..3: x3;\n\
   constraint int_lin_eq(c, [x1, x2, x3], 45035996273704960);\n\
   solve satisfy;\n"

let test_degenerate_control () =
  print_endline
    "\n-- M2-L11 (b, control): the counter reads 0 where the rows really are degenerate";
  let r = run degenerate_src in
  let s = r.r_stats in
  (* M2-L13 MOVED THIS NUMBER FROM 3 TO 1, and the move is the row working rather than
     the test drifting. The empty contradiction now has a RUNTIME CONSUMER
     (lib/core/prop/pb.ml, registered by [Search.register_learned_pb]), so the row
     derived at the first conflict refutes the model at the very next node and the other
     two conflicts never happen. The three-row figure is still reachable and is asserted
     below with [propagate_learned = false], which is what makes this an improvement
     rather than a lost measurement.

     What this control is FOR is unchanged and still checked on whatever rows are
     learned: [n_pb_nondegenerate] must read 0 where the rows really are degenerate. *)
  check_eq "b/control: the int_lin_eq family learns a PB row" s.Search.n_pb_learned 1;
  check_eq "b/control: ...strictly stronger than its clause" s.Search.n_pb_stronger 1;
  check_eq "b/control: ...and it is the EMPTY CONTRADICTION, so 0 here"
    s.Search.n_pb_nondegenerate 0;
  check_eq "b/control: ...reached with no ladder rung, in one elimination each"
    s.Search.n_pb_lifted 0;
  (* M2-L13's own control: with the learned constraint given no runtime consumer the
     search takes all three conflicts again, and the counter still reads 0 on all three.
     Both halves matter -- the first says the drop above is M2-L13's doing and not a
     silently weakened assertion, the second says the degeneracy claim is about the rows
     and not about how many of them there are. *)
  let off = run ~config:Search.no_propagate_learned degenerate_src in
  let so = off.r_stats in
  check_eq "b/control (M2-L13 off): the same model takes three conflicts again"
    so.Search.n_pb_learned 3;
  check_eq "b/control (M2-L13 off): ...every one strictly stronger than its clause"
    so.Search.n_pb_stronger 3;
  check_eq "b/control (M2-L13 off): ...and every one degenerate, so 0 here"
    so.Search.n_pb_nondegenerate 0;
  check "b/control: so propagating the learned row is what cut three conflicts to one"
    (so.Search.n_pb_learned > s.Search.n_pb_learned);
  cleanup off;
  List.iter
    (fun (t : Pb.t) ->
      check "b/control: the row has no terms and a positive degree"
        (Learned.is_empty t.Pb.row && Learned.degree t.Pb.row > 0);
      check_eq "b/control: ...from one elimination" t.Pb.steps 1)
    (Search.stats_pb_rows s);
  cleanup r

(* =================================================================== (c) *)

(* Test (c). Every model's proof is checked by scripts/run_model_tests.sh; what this
   section adds is the pair a suite-wide green cannot give: the SAME artefacts, accepted
   with the ladder derivation in them and REJECTED when one rung's multiplier is wrong.

   The break is worth reading twice. [break_ladder_mult] writes the first rung at one MORE
   than its multiplier. The result is still SOUND -- adding a larger positive multiple of
   a real .opb row is still cutting planes -- and still well-formed, and every id it names
   is live. The only thing wrong with it is the arithmetic, which is exactly the class
   M1-T42, M1-T51 and M2-T9's "Break A" found the checker accepting. It is caught here
   only because [Pb_analysis.introduce] STATES its claim, so the checker compares our
   arithmetic against its own at the line where they first differ. *)
let expect_checker ~title ~accepted r =
  match veripb ~dir:r.r_dir ~opb:r.r_opb ~pbp:r.r_pbp with
  | None ->
      incr failures;
      Printf.printf
        "FAIL %s: veripb was not found -- the lane did NOT run. This is a FAILURE, never \
         a skip.\n"
        title
  | Some (ok, out) ->
      if accepted then
        if ok then check (Printf.sprintf "%s: veripb accepts the proof" title) true
        else (
          incr failures;
          Printf.printf "FAIL %s: veripb REJECTED a proof it should accept:\n%s\n" title
            out)
      else if ok then (
        incr failures;
        Printf.printf
          "FAIL %s: the break was performed and veripb ACCEPTED the proof anyway. The \
           claim Pb_analysis.introduce states is not being compared against anything; \
           say so rather than deleting the test.\n"
          title)
      else (
        check (Printf.sprintf "%s: veripb rejects the proof" title) true;
        if contains ~needle:ladder_rejection out then
          check
            (Printf.sprintf "%s: ...with the checker's own judgement on the pol" title)
            true
        else (
          incr failures;
          Printf.printf
            "FAIL %s: veripb rejected, but not with the wording this lane asserts. An \
             exit status cannot tell a JUDGEMENT from a parse error. It said:\n\
             %s\n"
            title out))

let test_proof () =
  print_endline "\n-- M2-L11 (c): veripb 3.0.2 on the ladder derivation, and the break";
  let ok = run fixture_src in
  expect_checker ~title:"c" ~accepted:true ok;
  (* The chain must not be double-counted, and the proof is where that would show. A
     ladder row cited twice at the same multiplier would derive a different row from the
     one stated, so the acceptance above is already evidence -- but the shape is asserted
     directly as well, because "the checker did not complain" is not a description of
     what was written. *)
  List.iter
    (fun (t : Pb.t) ->
      let ids = Pb.cited_ids t.Pb.derivation in
      check "c: the derivation cites no id twice"
        (List.length ids = List.length (List.sort_uniq compare ids));
      check "c: every cited id is a real .opb row (model or ladder), so no `w` retires it"
        (List.for_all (fun i -> i >= 1) ids);
      check "c: the antecedent ids and the cited ids are the same set"
        (List.sort compare ids = List.sort compare t.Pb.antecedents))
    (Search.stats_pb_rows ok.r_stats);
  cleanup ok;
  let broken =
    run ~config:{ Search.default_config with Search.break_ladder_mult = true } fixture_src
  in
  expect_checker ~title:"c/break" ~accepted:false broken;
  cleanup broken

(* =================================================================== (d) *)

(* Test (d): THE STANDING HAZARD. [Order_reason.weaken_declared] and
   [Encoding.expand_int_lin_le] perform the same order-encoding substitution from opposite
   sides -- the propagator's and the .opb's -- and docs/DECISIONS.md D-0010 says in as many
   words that "the two must agree on the constant or the pieces don't combine". Nothing
   asserted it, and [Linear] cannot: [summands_of_snap] uses the chain's LITERALS and
   discards the constant (`let lits, _ = ...`). So a drift in the constant would be silent
   here until some later row tried to use it -- which is what M2-L11 has now done, since
   lib/core/ladder.ml resolves against exactly these rows.

   TWO CURRENCIES, and the whole hazard lives in the gap between them.

     - [Order_reason]'s header speaks about the STORED row, i.e. [Opb.le]'s output before
       [Opb.normalise] touches it. There a term with a positive coefficient appears with a
       NEGATIVE coefficient on the positive literal, so an axiom of the same polarity
       cancels it and nothing falls out to the right-hand side: the returned constant is
       0. A term with a negative coefficient appears positively, so the axiom is the
       NEGATED literal and a constant of |coeff| falls out per rung: the returned constant
       is |coeff| * width.
     - The .opb, the checker and [Learned] all hold the NORMALISED row, where every
       coefficient is positive and the polarity has moved into the literal. There the
       cancellation always produces a constant, so the right-hand side always moves, by
       |coeff| * width, WHICHEVER SIGN the coefficient had.

   Both halves are asserted below. Asserting only the second would let the returned
   constant drift freely (nothing reads it today); asserting only the first would not
   notice if [Encoding]'s expansion changed shape. *)
let var_of (l : Lit.t) = match l.Lit.v with Lit.Ge (n, _) | Lit.Eq (n, _) -> n

let mentions name c =
  List.exists (fun (_, l) -> String.equal (var_of l) name) (Opb.terms c)

let weaken_identity ~title ~lo ~hi ~coeff ~other_coeff =
  let enc = Encoding.create () in
  Encoding.declare_int enc "u" ~lo ~hi;
  Encoding.declare_int enc "v" ~lo:0 ~hi:3;
  let r = Encoding.expand_int_lin_le enc [ (coeff, "u"); (other_coeff, "v") ] 7 in
  let ws, k = Order_reason.weaken_declared ~coeff ~name:"u" ~decl_lo:lo ~decl_hi:hi in
  let combined = Opb.normalise (Opb.ge (Opb.terms r @ ws) (Opb.rhs r)) in
  let width = hi - lo in
  check
    (Printf.sprintf "d: %s -- the chain removes every literal of u" title)
    (not (mentions "u" combined));
  check (Printf.sprintf "d: %s -- v's terms are untouched" title) (mentions "v" combined);
  check_eq
    (Printf.sprintf "d: %s -- the normalised right-hand side moves by |coeff| * width"
       title)
    (Opb.rhs combined)
    (Opb.rhs r - (abs coeff * width));
  check_eq
    (Printf.sprintf "d: %s -- and the constant Order_reason returns is D-0010's" title)
    k
    (if coeff > 0 then 0 else abs coeff * width)

let test_coupling () =
  print_endline
    "\n-- M2-L11 (d): Order_reason.weaken_declared and Encoding.expand_int_lin_le agree";
  weaken_identity ~title:"a positive coefficient" ~lo:0 ~hi:4 ~coeff:3 ~other_coeff:2;
  weaken_identity ~title:"a negative coefficient" ~lo:0 ~hi:4 ~coeff:(-3) ~other_coeff:2;
  weaken_identity ~title:"a negative declared bound" ~lo:(-2) ~hi:2 ~coeff:2
    ~other_coeff:(-1);
  weaken_identity ~title:"a unit coefficient" ~lo:1 ~hi:5 ~coeff:1 ~other_coeff:1;
  weaken_identity ~title:"a width of one" ~lo:0 ~hi:1 ~coeff:(-2) ~other_coeff:3;
  (* The same identity on a row the FRONT END compiled, so the agreement is checked on the
     rows the solver actually emits and not only on hand-built ones. This is also the row
     lib/core/ladder.ml lifts in section (a), so a drift here and a drift there are the
     same drift. *)
  let c = compile worked_src in
  let enc = c.Compile.encoding in
  let r = Encoding.expand_int_lin_le enc [ (3, "a"); (2, "b") ] 14 in
  let ws, k = Order_reason.weaken_declared ~coeff:2 ~name:"b" ~decl_lo:0 ~decl_hi:4 in
  let combined = Opb.normalise (Opb.ge (Opb.terms r @ ws) (Opb.rhs r)) in
  check "d: on the compiled 3a+2b<=14 row, b's chain leaves only a's literals"
    ((not (mentions "b" combined)) && mentions "a" combined);
  check_eq "d: ...and the right-hand side moves by 2 * 4" (Opb.rhs combined)
    (Opb.rhs r - 8);
  check_eq "d: ...with Order_reason's own constant still 0 for a positive coefficient" k 0;
  (* The row [Ladder] actually lifts is the same object, so pin the two together: the
     degree PB analysis sees is the normalised right-hand side the encoding wrote. *)
  (match List.find_opt (fun x -> List.length x.Propagator.r_terms = 8) (all_rows c) with
  | None -> check "d: the compiled row is exposed to PB analysis" false
  | Some pb ->
      check_eq "d: the row PB analysis resolves against IS the row the .opb holds"
        (Learned.degree (Learned.of_pb_row pb))
        (Opb.rhs r));
  (* ---------------------------------------------------------------- the break *)
  (* THE DRIFT THE HAZARD IS ABOUT, performed: build the chain from the CURRENT bound
     instead of the DECLARED one. D-0010's whole point is that the offset is "always the
     declared bound (fixed at the model's construction) and never the raw current value";
     this is what happens when it is not. b has been narrowed to 4..4 on this scene, so a
     chain offset at 3 is one rung long where the real one is four. *)
  let drifted, _ =
    Order_reason.weaken_declared ~coeff:2 ~name:"b" ~decl_lo:3 ~decl_hi:4
  in
  let broken = Opb.normalise (Opb.ge (Opb.terms r @ drifted) (Opb.rhs r)) in
  check "d/break: a chain offset at the CURRENT bound is shorter than the declared one"
    (List.length drifted < List.length ws);
  check "d/break: ...so it leaves b's literals standing" (mentions "b" broken);
  check "d/break: ...and moves the right-hand side by the wrong amount"
    (Opb.rhs broken <> Opb.rhs r - 8);
  (* And the constant drifts with it, on the sign where the constant is not always 0 --
     which is the half of D-0010 that a reader of [Linear] alone would never see move,
     because [Linear] throws the constant away. *)
  let _, full_k = Order_reason.weaken_declared ~coeff:(-2) ~name:"b" ~decl_lo:0 ~decl_hi:4
  and _, drift_k =
    Order_reason.weaken_declared ~coeff:(-2) ~name:"b" ~decl_lo:3 ~decl_hi:4
  in
  check_eq "d/break: the declared-width chain's constant is 2 * 4" full_k 8;
  check_eq "d/break: ...and the drifted one's is 2 * 1, which is the silent disagreement"
    drift_k 2

(* ------------------------------------------------------------------ main *)

let () =
  test_worked_case ();
  test_nondegenerate_counter ();
  test_degenerate_control ();
  test_proof ();
  test_coupling ();
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "\nall ladder tests passed"
