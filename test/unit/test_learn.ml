(* Unit tests for lib/core/learn.ml and the search that uses it -- M2-L3: 1UIP clause
   learning over order literals, its semantic minimisation, its `rup` derivation and the
   backjump it licenses.

   The roadmap row names six tests and each is a section below. Two of them are BREAKS,
   and a break that reddens nothing is worth more to know about than a green run, so each
   break here is performed through a knob the solver exports ([Search.config]) rather than
   by editing the emitted text: a break lane that mutates bytes proves the checker reads
   bytes, not that the solver's ordering is load-bearing.

   Every scene is driven through the real front end ([Builder] -> [Compile] -> [Search]),
   so nothing here builds a store, an encoding or a [Reason.justified] by hand -- the
   objects under test are the ones the CLI produces.

   Domains are 0..1 and 0..3 throughout (D-0028: the order encoding is width-proportional
   and a wide domain is a proof that dwarfs the suite). *)

module F = Baguette_flatzinc
module M = F.Model
module Compile = F.Compile
module Store = Baguette_core.Store
module Search = Baguette_core.Search
module Justify = Baguette_core.Justify
module Learn = Baguette_core.Learn
module Encoding = Baguette_proof.Encoding
module Writer = Baguette_proof.Writer
module Lit = Baguette_proof.Lit
module Learned = Baguette_core.Learned
module Linear = Baguette_core.Linear
module Reduce = Baguette_core.Reduce
module Pb = Baguette_core.Pb_analysis
module Checked = Baguette_core.Checked
module Propagator = Baguette_core.Propagator

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

(* ------------------------------------------------------------------ the scenes *)

(* THE DESIGNATED BACKJUMP SCENE, and it is also test/models/backjump_unsat.fzn.

   p and q are unconstrained and have the smallest domains, so first-fail branches on
   them first and the refutation of x <> y /\ x = y happens two levels below decisions it
   does not depend on. That is the whole scene: the decision closure of every conflict
   names x's level alone, so the frames owning p's and q's levels find a nogood that does
   not mention them and skip their siblings. It is the smallest shape in which a backjump
   is observable at all, and without the two spectators it is [ne_eq_unsat] and skips
   nothing. *)
let backjump_src =
  "var 0..1: p;\n\
   var 0..1: q;\n\
   var 0..3: x;\n\
   var 0..3: y;\n\
   constraint int_ne(x, y);\n\
   constraint int_eq(x, y);\n\
   solve satisfy;\n"

(* test/models/trace_settle_sat.fzn, verbatim. Two things make it the scene for I-S4:
   its conflict's cut resolves entries whose trace lines are filed at the conflict's own
   level, so a `w` retiring that level really does take away what the learned clause's
   [rup] rests on; and its decision settles past a hole, so the derivation crosses a level
   (`i_s4_crossings`) as well. *)
let settle_src =
  "var 2..3: y;\n\
   var 0..4: x;\n\
   var 0..4: w;\n\
   var 0..1: z;\n\
   constraint int_ne(x, y);\n\
   constraint int_lin_le([-1,-1],[x,w],-4);\n\
   constraint int_lin_le([1,-1],[w,y],0);\n\
   constraint int_lin_le([1,-1],[x,z],2);\n\
   constraint int_lin_le([1,-1],[z,y],-2);\n\
   solve satisfy;\n"

(* test/models/trace_settle_holes_sat.fzn, verbatim: the same shape with two holes, so the
   cut folds one and the hole line I-S4 is literally about is among the supports. *)
let holes_src =
  "var 2..4: y;\n\
   var 0..5: x;\n\
   var 0..4: w;\n\
   var 0..2: z;\n\
   var 3..3: p;\n\
   constraint int_ne(x, y);\n\
   constraint int_ne(x, p);\n\
   constraint int_lin_le([-1,-1],[x,w],-4);\n\
   constraint int_lin_le([1,-1],[w,y],0);\n\
   constraint int_lin_le([1,-1],[x,z],2);\n\
   constraint int_lin_le([1,-1],[z,y],-2);\n\
   solve satisfy;\n"

(* M2-L10: three new instances, added because a single skipping instance
   (backjump_src / backjump_unsat.fzn, 2 skips) is not something M2-L4/L6/L8 can
   measure against. Each is verbatim its test/models/*.fzn twin, and each is picked to
   take a DIFFERENT path through the skip machinery -- see the .fzn header of each for
   the full argument and the measured node/decision/skip counts. *)

(* test/models/backjump_deep_unsat.fzn, verbatim: backjump_src with a THIRD spectator
   (r), so one refutation skips three siblings rather than two -- "the backjump crosses
   more than one level". Non-convertible, same as backjump_src: the learned clauses sit
   on a threshold strictly inside x's/y's ladder. *)
let deep_src =
  "var 0..1: p;\n\
   var 0..1: q;\n\
   var 0..1: r;\n\
   var 0..3: x;\n\
   var 0..3: y;\n\
   constraint int_ne(x, y);\n\
   constraint int_eq(x, y);\n\
   solve satisfy;\n"

(* test/models/backjump_bool_unsat.fzn, verbatim: bool_reif_unsat's Boolean refutation
   (array_bool_or/array_bool_and/bool_eq/bool_clause, D-0030) with two spectators in
   front of it. Every learned clause here is over Boolean order literals, D-0007's
   single-rung ladder, so [Learned.to_linear_row] accepts all of them -- the CONVERTIBLE
   path, which backjump_src and deep_src do not exercise. *)
let bool_src =
  "var 0..1: p;\n\
   var 0..1: q;\n\
   var bool: a;\n\
   var bool: b;\n\
   var bool: c;\n\
   var bool: d;\n\
   constraint array_bool_or([a, b], c);\n\
   constraint array_bool_and([a, b], d);\n\
   constraint bool_eq(c, d);\n\
   constraint bool_clause([a, b], []);\n\
   constraint bool_clause([], [a, b]);\n\
   solve satisfy;\n"

(* test/models/backjump_lineq_unsat.fzn, verbatim: near_limit_unsat's int_lin_eq
   refutation under checked arithmetic (coefficients near Checked.limit) with two
   spectators in front of it. A third, non-Boolean, non-int_ne shape: linear-equality
   reasoning rather than value-consistency disequality. Non-convertible, like deep_src:
   its learned clauses also sit on thresholds strictly inside an integer ladder. *)
let lineq_src =
  "var 0..1: p;\n\
   var 0..1: q;\n\
   array [1..3] of int: c = [18014398509481984, 18014398509481984, 18014398509481984];\n\
   var 0..3: x1;\n\
   var 0..3: x2;\n\
   var 0..3: x3;\n\
   constraint int_lin_eq(c, [x1, x2, x3], 45035996273704960);\n\
   solve satisfy;\n"

type run = {
  r_outcome : Search.outcome;
  r_stats : Search.stats;
  r_proof : string;
  r_entry_level : int;
  r_exit_level : int;
  r_audit_error : string option;
  r_compile : Compile.t;
      (* M2-L6: the store and the encoding, kept so that a test can build the RUNTIME
         instance of a learned row and actually run it. Test (a)'s claim is that the PB
         row propagates where the clause does not, and "propagates" is a statement about
         a propagator, not about a conversion function returning [Some]. *)
}

(* Solve one model into a scratch directory and hand back everything the sections below
   ask about. The audit is ON: I-X2's live set must be empty at [conclusion], and a
   learned clause is the first object in this solver whose lifetime is not a level's, so
   it is exactly the thing that leaks if [Search.solve] forgets to retire it. A raised
   [Writer.Audit_failed] is captured rather than allowed to abort the binary, so that the
   failure is reported as one check rather than as a crash. *)
let run ?(config = Search.default_config) ?order src =
  let m = F.Builder.of_string ~file:"test" src in
  let c = Compile.compile m in
  let dir = Filename.temp_file "baguette_learn" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  let opb = Filename.concat dir "m.opb" and pbp = Filename.concat dir "m.pbp" in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "M2-L3" ] c.Compile.encoding oc;
  close_out oc;
  let oc = open_out pbp in
  let writer = Writer.create ~audit:true oc in
  Encoding.start_proof c.Compile.encoding writer;
  let ctx = Justify.create ~writer ~encoding:c.Compile.encoding in
  let stats = Search.stats_create () in
  let entry_level = Store.level c.Compile.store in
  let audit_error = ref None in
  let outcome =
    try
      Search.solve ~engine:c.Compile.engine ~store:c.Compile.store ~ctx
        ~check:(fun _ -> true)
        ~stats ~config ?order ()
    with Writer.Audit_failed r ->
      audit_error := Some r;
      Search.Unsat
  in
  let exit_level = Store.level c.Compile.store in
  close_out oc;
  let r =
    {
      r_outcome = outcome;
      r_stats = stats;
      r_proof = read_file pbp;
      r_entry_level = entry_level;
      r_exit_level = exit_level;
      r_audit_error = !audit_error;
      r_compile = c;
    }
  in
  (r, dir, opb, pbp)

let cleanup dir files =
  List.iter (fun f -> try Sys.remove f with _ -> ()) files;
  try Sys.rmdir dir with _ -> ()

(* Which checker to run: lib/proof/checker.ml, shared with scripts/checker.sh. [None] is
   a FAILURE at every call site below, never a skip. *)
let veripb_path () = Baguette_proof.Checker.find ()

(* Run the checker and hand back (accepted?, what it said). *)
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

(* Both breaks in this file surface the same way -- a `rup` the checker cannot re-derive
   -- and the wording below was MEASURED on 2026-09-18 by running each break lane, not
   guessed:

     "The constraint is not implied by reverse unit propagation (RUP) from core and
      derived database."

   It is matched at FULL strength rather than on its "reverse unit propagation" fragment.
   The fragment is the least specific thing the checker says about this class, so a
   different RUP failure elsewhere in the proof would match it and the lane would report
   the wrong break. Asserting the wording at all is what separates "the checker said no"
   from "the checker judged this step": a file that failed to parse says neither. *)
let rejection_wordings = [ "is not implied by reverse unit propagation" ]

let rejection_recognised out =
  List.exists (fun w -> contains ~needle:w out) rejection_wordings

(* Assert that a run's proof is REJECTED, and that the rejection is one this project
   recognises under whichever checker is on this machine. *)
let expect_rejected ~title ~dir ~opb ~pbp =
  match veripb ~dir ~opb ~pbp with
  | None ->
      incr failures;
      Printf.printf
        "FAIL %s: veripb not found -- the break was NOT checked. Do not treat this as a \
         pass.\n"
        title
  | Some (true, _) ->
      incr failures;
      Printf.printf
        "FAIL %s: the break was performed and veripb ACCEPTED the proof anyway. The \
         ordering this test exists to protect is not load-bearing; say so rather than \
         deleting the test.\n"
        title
  | Some (false, out) ->
      check (Printf.sprintf "%s: veripb rejects the proof" title) true;
      if rejection_recognised out then
        check
          (Printf.sprintf "%s: the rejection is one of the two known wordings" title)
          true
      else (
        incr failures;
        Printf.printf
          "FAIL %s: veripb rejected, but with a wording neither checker's known \
           rejection matches. It said:\n\
           %s\n"
          title out)

let expect_accepted ~title ~dir ~opb ~pbp =
  match veripb ~dir ~opb ~pbp with
  | None ->
      incr failures;
      Printf.printf
        "FAIL %s: veripb not found -- I-X1 was NOT checked. Do not treat this as a pass.\n"
        title
  | Some (true, _) ->
      check (Printf.sprintf "%s: veripb accepts the proof (I-X1)" title) true
  | Some (false, out) ->
      incr failures;
      Printf.printf "FAIL %s: veripb rejected the proof. It said:\n%s\n" title out

(* ================================================================ (a2) minimisation *)

(* A clause, evaluated. An order literal [x >= v] is a question about an integer, so a
   clause over order literals has a truth value at every point of the box -- which is what
   makes "the reduction preserves meaning" a decidable question over these widths rather
   than an argument. *)
let lit_holds assign (l : Lit.t) =
  let v = List.assoc (Lit.owner l.Lit.v) assign in
  let raw = match l.Lit.v with Lit.Ge (_, k) -> v >= k | Lit.Eq (_, k) -> v = k in
  if l.Lit.positive then raw else not raw

let clause_holds assign lits = List.exists (lit_holds assign) lits

(* Do two clauses over one variable agree at every point of [lo..hi]? *)
let agree_on ~name ~lo ~hi a b =
  let ok = ref true in
  for v = lo to hi do
    if clause_holds [ (name, v) ] a <> clause_holds [ (name, v) ] b then ok := false
  done;
  !ok

let nx k = Lit.negate (Lit.ge "x" k) (* ~[x >= k], i.e. x <= k-1 *)
let px k = Lit.ge "x" k (* [x >= k] *)

let test_minimise_pure () =
  (* The two directions of the ladder, each stated as the header states it. *)
  check "a2: among negative literals the LARGEST threshold survives"
    (Learn.minimise [ nx 1; nx 3 ] = [ nx 3 ]);
  check "a2: among positive literals the SMALLEST threshold survives"
    (Learn.minimise [ px 3; px 1 ] = [ px 1 ]);
  check "a2: the two directions do not merge with each other"
    (List.length (Learn.minimise [ nx 3; px 1 ]) = 2);
  check "a2: literals about different variables do not merge"
    (List.length (Learn.minimise [ nx 3; Lit.negate (Lit.ge "y" 3) ]) = 2);
  check "a2: a direct-encoding literal is never merged, even with another on its variable"
    (List.length (Learn.minimise [ Lit.eq "x" 1; Lit.eq "x" 2 ]) = 2);
  (* Idempotence, on every input the sections below can produce. *)
  let inputs =
    [
      [ nx 1; nx 2; nx 3 ];
      [ px 1; px 2; px 3 ];
      [ nx 3; px 1; nx 1; px 3 ];
      [ nx 2 ];
      [];
      [ px 2; nx 2 ];
    ]
  in
  check "a2: minimisation is idempotent"
    (List.for_all (fun l -> Learn.minimise (Learn.minimise l) = Learn.minimise l) inputs);
  (* IT NEVER DROPS A LITERAL THE CUT NEEDS. Dropping one that is not implied by a
     survivor would change the clause's meaning, and over a ladder that is decidable: the
     reduced clause must hold at exactly the points the original holds at. Checked over a
     box one wider than the declared one at each end, so a threshold at the boundary is
     not accidentally agreed on. *)
  check "a2: the reduction preserves the clause's meaning at every point of the ladder"
    (List.for_all
       (fun l ->
         (* width-ok: no store, no encoding and no ladder is allocated here -- this is the
            range a clause is EVALUATED over by [agree_on], seven integers in a for-loop,
            and it is deliberately one wider than the thresholds at each end so that a
            boundary is not agreed on by accident. *)
         agree_on ~name:"x" ~lo:(-1) ~hi:5 l (Learn.minimise l)
         (* width-ok: see above *))
       inputs);
  (* The break, as a pure function first: keeping the WEAKEST threshold does not preserve
     meaning, and the point at which it stops is exhibited rather than asserted in the
     abstract. [~[x>=1]] holds only at x <= 0; [~[x>=1] \/ ~[x>=3]] holds at x <= 2. *)
  let weakest = Learn.minimise ~policy:Learn.Weakest [ nx 1; nx 3 ] in
  check "a2 BREAK: keeping the weakest threshold keeps the OTHER literal"
    (weakest = [ nx 1 ]);
  check "a2 BREAK: and it does NOT preserve the clause's meaning"
    (not (agree_on ~name:"x" ~lo:(-1) ~hi:5 [ nx 1; nx 3 ] weakest));
  check
    "a2 BREAK: the point it goes wrong at is x = 2 -- the original holds there, the \
     weakest-reduced clause does not"
    (clause_holds [ ("x", 2) ] [ nx 1; nx 3 ] && not (clause_holds [ ("x", 2) ] weakest))

(* And the same break where it matters: through the solver, with the real checker over
   the proof. A break that only reddens a unit test of a pure function has not shown that
   the reduction is load-bearing in the PROOF.

   The branching order is [random_order] at a pinned seed, and that is a finding rather
   than a convenience. Under the normative order ([spec_order], first-fail /
   indomain_min) the reduction NEVER FIRES on any of the 34 shipped models -- measured,
   `stats.n_min_dropped` is 0 on every one of them -- because the decision closure has
   already reduced the nogood to one level per variable per direction before minimisation
   sees it, which is [Analysis.add_node]'s strongest-per-slot merge doing this row's work
   one layer up. Under other orders it does fire, and this is one of them: seed 12 on the
   settle scene drops a literal, the proof still verifies, and keeping the weakest
   threshold instead makes the checker reject it.

   A fresh [Random.State] per decision, so the order is a deterministic function of the
   seed and of nothing else -- a break lane pinned to a seed has to be reproducible from
   the seed alone. *)
let seeded_order seed store cands =
  Search.random_order (Random.State.make [| seed |]) store cands

let test_minimise_break_in_a_proof () =
  let order = seeded_order 12 in
  let r, dir, opb, pbp = run ~order settle_src in
  check "a2: the scene the break needs really does minimise something"
    (r.r_stats.Search.n_min_dropped > 0);
  expect_accepted ~title:"a2: the minimised proof" ~dir ~opb ~pbp;
  cleanup dir [ opb; pbp ];
  let _, dir2, opb2, pbp2 =
    run ~order
      ~config:{ Search.default_config with Search.policy = Learn.Weakest }
      settle_src
  in
  expect_rejected ~title:"a2 BREAK: weakest-threshold minimisation" ~dir:dir2 ~opb:opb2
    ~pbp:pbp2;
  cleanup dir2 [ opb2; pbp2 ];
  (* And the finding itself, asserted so that it cannot rot quietly: under the NORMATIVE
     order the reduction is idle on this scene. If that ever stops being true, this check
     reddens and the sentence above has to be rewritten rather than believed. *)
  let n, dn, on_, pn = run settle_src in
  check
    "a2: under the normative order the reduction fires on NOTHING here -- the decision \
     closure got there first (measured, not argued)"
    (n.r_stats.Search.n_min_dropped = 0);
  cleanup dn [ on_; pn ]

(* ============================================================ (b) I-S4 ordering *)

(* The learned clause is a [rup], so what its derivation needs is that everything it rests
   on is LIVE AT THAT MOMENT -- which is what forces it to precede the `w` retiring its
   level (D-0018 point 4). [Search.config.break_i_s4] retires the level first. Two things
   must then happen, and both are asserted: the solver's own I-S4 check must report it
   (that is the check this row owed, and a check that only the checker can see is a check
   this project does not have), and the checker must reject the proof. *)
let test_i_s4_ordering () =
  let r, dir, opb, pbp = run settle_src in
  check "b: the settle scene is solved" (r.r_outcome <> Search.Unsat);
  check "b: it learns something" (r.r_stats.Search.n_learned > 0);
  check "b: the learned clauses' derivations really do rest on hole lines"
    (r.r_stats.Search.i_s4_supports > 0);
  check "b: and I-S4's liveness half holds on every one of them"
    (Search.stats_i_s4_broken r.r_stats = []);
  check
    "b: the audit is clean -- every level-0 learned id was retired exactly once (I-X2)"
    (r.r_audit_error = None);
  expect_accepted ~title:"b: the correctly-ordered proof" ~dir ~opb ~pbp;
  cleanup dir [ opb; pbp ];
  (* The break: the `w` first, the derivation second. *)
  let rb, dirb, opbb, pbpb =
    run ~config:{ Search.default_config with Search.break_i_s4 = true } settle_src
  in
  check "b BREAK: the solver's own I-S4 check reports the violation"
    (Search.stats_i_s4_broken rb.r_stats <> []);
  expect_rejected ~title:"b BREAK: derivation after the `w` retiring its level" ~dir:dirb
    ~opb:opbb ~pbp:pbpb;
  cleanup dirb [ opbb; pbpb ]

(* The other half of the I-S4 debt, and it is a finding rather than a check: the level-0
   learned clause DOES rest on hole lines filed above level 0, which is precisely the
   crossing I-S4's level argument does not cover. It is not a violation here because a
   [rup] names no id -- see learn.ml's header -- and the number is reported so that M2-L6,
   whose reduction steps would be a [pol], does not have to discover it. *)
let test_i_s4_crossings_are_real () =
  let r, dir, opb, pbp = run holes_src in
  check "b: the crossing this row was sent to look for is REAL, not hypothetical"
    (r.r_stats.Search.i_s4_crossings > 0);
  check
    "b: and it is not a violation -- the same run's liveness half is clean and the \
     checker accepts"
    (Search.stats_i_s4_broken r.r_stats = []);
  expect_accepted ~title:"b: a proof whose level-0 clause rests on lines above level 0"
    ~dir ~opb ~pbp;
  cleanup dir [ opb; pbp ]

(* ============================================================ (c) node counts *)

(* Strictly fewer nodes, asserted against [Search.stats.nodes] -- M1-T36's real counter,
   the one `--stats` prints -- and never against the `lvl` proxy, which moves with the
   proof's shape and has moved in this very row (test_engine.ml's [unsat_markers] went
   3 -> 7 on an unchanged tree).

   Both runs are of the SAME scene through the SAME binary; the only difference is
   [config.learn]. *)
let test_node_count_decreases () =
  let off, dir1, opb1, pbp1 = run ~config:Search.no_learning backjump_src in
  let on, dir2, opb2, pbp2 = run backjump_src in
  check "c: the designated scene is UNSAT with learning off" (off.r_outcome = Search.Unsat);
  check "c: and with learning on" (on.r_outcome = Search.Unsat);
  check "c: learning off skips nothing -- M1's search, unaltered"
    (off.r_stats.Search.skipped = 0 && off.r_stats.Search.n_learned = 0);
  check "c: learning on DOES back jump" (on.r_stats.Search.skipped > 0);
  check
    (Printf.sprintf
       "c: the node count strictly DECREASES: %d nodes with learning, %d without"
       on.r_stats.Search.nodes off.r_stats.Search.nodes)
    (on.r_stats.Search.nodes < off.r_stats.Search.nodes);
  check
    "c: the same tree is still exhausted, so the decrease is pruning and not a search \
     that stopped early"
    (Search.stats_consistent on.r_stats ~exhausted:true
    && Search.stats_consistent off.r_stats ~exhausted:true);
  check_eq "c: M1-T36's identity with learning off is unchanged" off.r_stats.Search.nodes
    ((2 * off.r_stats.Search.decisions) + 1);
  check_eq "c: and with learning on it is the identity minus the skips"
    on.r_stats.Search.nodes
    ((2 * on.r_stats.Search.decisions) + 1 - on.r_stats.Search.skipped);
  (* Both proofs verify. A node count that fell because the search stopped reasoning is
     not a saving, and the checker is what says so. *)
  expect_accepted ~title:"c: the proof with learning off" ~dir:dir1 ~opb:opb1 ~pbp:pbp1;
  expect_accepted ~title:"c: the proof with learning on" ~dir:dir2 ~opb:opb2 ~pbp:pbp2;
  cleanup dir1 [ opb1; pbp1 ];
  cleanup dir2 [ opb2; pbp2 ]

(* D-0044's fork, measured rather than asserted. This row took (ii) -- proof-only -- and
   the number that justifies it is how often the cut would have converted to a runtime
   row. If this ever stops being 0 on an integer scene, [Learned.to_linear_row] has grown
   a case and fork (i) is worth revisiting; until then, restricting the cut to the shapes
   that convert would have meant learning nothing at all here. *)
let test_conversion_rate () =
  let r, dir, opb, pbp = run backjump_src in
  check "c: the integer scene learns clauses" (r.r_stats.Search.n_learned > 0);
  check_eq "c: and NONE of them converts to a runtime linear row (D-0044's amendment)"
    r.r_stats.Search.n_converts 0;
  cleanup dir [ opb; pbp ]

(* ================================================ the backjump does not change answers

   The one thing a backjump can get wrong that nothing else in this file would catch: it
   skips branches, and a branch skipped that was not refuted is a solution missed. The
   proof would not say so -- a wrong UNSAT whose refutation the checker accepts is exactly
   the shape M1-T44 was, and it was found by a fuzzer and not by a proof.

   So: every scene here, under forty branching orders each, with learning ON and OFF,
   answering the same thing. Learning OFF is M1's search unaltered, and M1's search is the
   one `test_endtoend.ml` and `test_matrix.ml` check against brute force; this makes it the
   oracle for the backjump rather than re-implementing one. The orders are seeded
   [random_order]s, so the sweep covers trees `spec_order` never builds -- which is where
   the skip rule is actually stressed, since the normative order's conflicts almost always
   rest on the deepest decisions and skip nothing. *)
let test_backjump_answers_the_same () =
  let bad = ref 0 and skips = ref 0 and total = ref 0 in
  List.iter
    (fun src ->
      for seed = 0 to 39 do
        let order = seeded_order seed in
        let on, d1, o1, p1 = run ~order src in
        let off, d2, o2, p2 = run ~order ~config:Search.no_learning src in
        incr total;
        skips := !skips + on.r_stats.Search.skipped;
        let same =
          match (on.r_outcome, off.r_outcome) with
          | Search.Unsat, Search.Unsat -> true
          | Search.Sat a, Search.Sat b -> List.length a = List.length b
          | _ -> false
        in
        if not same then (
          incr bad;
          Printf.printf
            "  seed %d: learning says %s, M1's search says %s -- a skipped branch was \
             not refuted\n"
            seed
            (match on.r_outcome with Search.Sat _ -> "SAT" | _ -> "UNSAT")
            (match off.r_outcome with Search.Sat _ -> "SAT" | _ -> "UNSAT"));
        cleanup d1 [ o1; p1 ];
        cleanup d2 [ o2; p2 ]
      done)
    [ backjump_src; settle_src; holes_src ];
  check
    (Printf.sprintf
       "backjump: %d order/scene pairs agree with M1's search, over %d skipped siblings"
       !total !skips)
    (!bad = 0);
  (* And the sweep has to have exercised the thing it is about. A sweep in which nothing
     was ever skipped agrees with M1's search for the least interesting reason there is. *)
  check "backjump: the sweep really did skip branches" (!skips > 0)

(* ================================================== M2-L10: backjump instance coverage

   docs/ROADMAP.md M2-L10: one skipping instance in the whole suite (backjump_src, 2
   skips) is not something the retention (M2-L4), fallback-rate (M2-L6) or benchmark
   (M2-L8) rows can measure against. Three more instances, each asserting [skipped > 0]
   through [Search.stats] -- the same counter `--stats` prints, never by inspection --
   and each taking a DIFFERENT path: deep_src crosses more than one level in a single
   refutation, bool_src's learned clauses convert and deep_src's/lineq_src's do not,
   lineq_src is a wholly different propagator family (int_lin_eq, not int_ne/int_eq or
   Boolean clauses). Every proof here is also checked by
   test/models/backjump_deep_unsat.fzn, backjump_bool_unsat.fzn and
   backjump_lineq_unsat.fzn's own run through scripts/verify_proof.sh; this in-process
   run re-confirms the same path from inside the solver. *)
let test_m2l10_coverage () =
  let scene ~title ~convertible src =
    let r, dir, opb, pbp = run src in
    check (Printf.sprintf "%s: solved to UNSAT" title) (r.r_outcome = Search.Unsat);
    check
      (Printf.sprintf "%s: skipped > 0 (Search.stats, the real --stats counter)" title)
      (r.r_stats.Search.skipped > 0);
    check
      (Printf.sprintf "%s: at least one clause learned" title)
      (r.r_stats.Search.n_learned > 0);
    if convertible then
      check_eq
        (Printf.sprintf "%s: every learned clause converts (Boolean order literals)" title)
        r.r_stats.Search.n_converts r.r_stats.Search.n_learned
    else
      check_eq
        (Printf.sprintf "%s: no learned clause converts (threshold inside a ladder)" title)
        r.r_stats.Search.n_converts 0;
    expect_accepted ~title:(title ^ ": the emitted proof") ~dir ~opb ~pbp;
    cleanup dir [ opb; pbp ]
  in
  scene ~title:"M2-L10 deep (3-level backjump)" ~convertible:false deep_src;
  scene ~title:"M2-L10 bool (convertible)" ~convertible:true bool_src;
  scene ~title:"M2-L10 lineq (non-convertible, int_lin_eq)" ~convertible:false lineq_src;
  (* And the multi-level claim itself: deep_src's single refutation skips at least
     three siblings, strictly more than backjump_src's two. *)
  let deep, dir, opb, pbp = run deep_src in
  check_eq "M2-L10 deep: skips exactly 3, one per spectator (p, q, r)"
    deep.r_stats.Search.skipped 3;
  cleanup dir [ opb; pbp ]

(* ============================================================ (d) I-S3 *)

let test_i_s3 () =
  List.iter
    (fun (title, src) ->
      let r, dir, opb, pbp = run src in
      check
        (Printf.sprintf
           "d: I-S3 -- level on return equals level on entry, learning on (%s)" title)
        (r.r_entry_level = r.r_exit_level);
      cleanup dir [ opb; pbp ])
    [
      ("backjump scene", backjump_src);
      ("settle scene", settle_src);
      ("holes scene", holes_src);
    ]

(* ============================================================ (f) determinism *)

(* The gate's own question, asked inside the binary: two runs of one solver over one
   model, byte for byte. A learned database iterated in hash order is the specific way
   learning breaks it, and this is the check that would see it. *)
let test_determinism () =
  List.iter
    (fun (title, src) ->
      let a, d1, o1, p1 = run src in
      let b, d2, o2, p2 = run src in
      check
        (Printf.sprintf "f: two runs emit a byte-identical proof (%s)" title)
        (String.equal a.r_proof b.r_proof);
      check
        (Printf.sprintf "f: and byte-identical counters (%s)" title)
        (a.r_stats.Search.nodes = b.r_stats.Search.nodes
        && a.r_stats.Search.skipped = b.r_stats.Search.skipped
        && a.r_stats.Search.n_learned = b.r_stats.Search.n_learned);
      cleanup d1 [ o1; p1 ];
      cleanup d2 [ o2; p2 ])
    [ ("backjump scene", backjump_src); ("holes scene", holes_src) ]

(* ================================================================ M2-L6

   The PB conflict-analysis lane. Six tests, one per lettered requirement of
   docs/ROADMAP.md M2-L6, and the two that matter most are (a) -- the learned inequality
   is strictly stronger than the clause -- and (b) -- the fallback rate is non-degenerate,
   so a build that silently always fell back could not pass. *)

(* A [Learned.t] evaluated at a 0-1 assignment of its literals. The assignment is a
   function because the oracle below enumerates it as a bitmask, not as a list. *)
let row_holds (assign : Lit.t -> bool) (row : Learned.t) =
  let lhs =
    List.fold_left
      (fun acc (tm : Learned.term) ->
        if assign tm.Learned.lit then acc + tm.Learned.coeff else acc)
      0 (Learned.terms row)
  in
  lhs >= Learned.degree row

(* Every literal any of these rows mentions, positive form, deduplicated and sorted so
   the enumeration below is a function of the SET and not of the order. *)
let literal_universe (rows : Learned.t list) =
  let pos (l : Lit.t) = { l with Lit.positive = true } in
  List.sort_uniq Lit.compare
    (List.concat_map (fun r -> List.map pos (Learned.lits r)) rows)

(* ------------------------------------------------------------------ (e) the oracle *)

(* THE ORACLE: the learned inequality is entailed by the rows it was derived from.

   Brute-forced over every 0-1 assignment to the literals involved -- NOT over the
   integer box, and the difference is the point. A cutting-planes derivation (positive
   linear combination, literal-axiom weakening, Chvatal-Gomory division) is sound at every
   0-1 point, whether or not that point respects the order encoding's ladder. So this
   oracle is the right statement about a [pol], and, unlike "every solution of the model
   satisfies the row", it is NEVER VACUOUS -- which matters here because the models that
   exercise this path are unsatisfiable, and a vacuous oracle is one that cannot fail.

   The counts are reported so that a run where the premises are satisfied by NO assignment
   is visible as such rather than passing silently. *)
let oracle_entails ~title (t : Pb.t) =
  let rows = t.Pb.antecedent_rows in
  let universe = literal_universe (t.Pb.row :: rows) in
  let n = List.length universe in
  if n > 16 then
    check
      (Printf.sprintf "%s: oracle SKIPPED, %d literals is too wide to enumerate" title n)
      false
  else
    let arr = Array.of_list universe in
    let premises_met = ref 0 and violations = ref 0 in
    for mask = 0 to (1 lsl n) - 1 do
      let assign (l : Lit.t) =
        let rec idx i =
          if i >= n then None
          else if Lit.equal arr.(i) { l with Lit.positive = true } then Some i
          else idx (i + 1)
        in
        match idx 0 with
        | None -> false
        | Some i ->
            let bit = mask land (1 lsl i) <> 0 in
            if l.Lit.positive then bit else not bit
      in
      if List.for_all (row_holds assign) rows then (
        incr premises_met;
        if not (row_holds assign t.Pb.row) then incr violations)
    done;
    (* The premise count is REPORTED, not asserted. For a conflict derived from rows that
       are jointly infeasible over 0-1 points -- which is what an [int_lin_eq] whose
       right-hand side is not a multiple of its coefficients gives, and it is precisely
       why the search conflicts there -- no point satisfies them and the entailment below
       is vacuously true. A vacuous check is not evidence, so it is labelled as such here
       and the non-vacuous oracle is [test_oracle_primitives]. *)
    Printf.printf "     (%s: %d of %d 0-1 points satisfy the antecedents%s)\n" title
      !premises_met (1 lsl n)
      (if !premises_met = 0 then " -- ENTAILMENT VACUOUS HERE, see test_oracle_primitives"
       else "");
    check
      (Printf.sprintf
         "%s: oracle -- the learned row holds at every point satisfying the antecedents"
         title)
      (!violations = 0)

let test_oracle () =
  print_endline
    "\n-- M2-L6 (e): the learned inequality is entailed by the rows it came from";
  let r, dir, opb, pbp = run lineq_src in
  let rows = Search.stats_pb_rows r.r_stats in
  check "e: the run learned at least one PB row to run the oracle on" (rows <> []);
  List.iteri (fun i t -> oracle_entails ~title:(Printf.sprintf "e: row %d" i) t) rows;
  cleanup dir [ opb; pbp ]

(* ------------------------------------------------------------------ (a) strength *)

(* Test (a), and it is the row's whole justification: the learned inequality is STRICTLY
   STRONGER than the clause the same conflict yields -- it propagates where the clause
   does not.

   "Propagates" is taken literally. [Learned.to_linear] is asked for the runtime instance
   of each object; the clause has none at all (D-0044's fork, measured by M2-L3: a 1UIP
   cut over integer variables puts thresholds strictly inside a ladder and
   [to_linear_row] refuses them), and the PB row does. The instance is then RUN, at the
   root, and asked to do something -- because an instance that exists but never prunes
   would not have justified the row either. *)
let test_strictly_stronger () =
  print_endline
    "\n-- M2-L6 (a): the learned inequality propagates where the clause does not";
  let r, dir, opb, pbp = run lineq_src in
  let st = r.r_stats in
  let c = r.r_compile in
  let decl = Learned.decl_of_encoding c.Compile.encoding in
  check_eq "a: conflicts analysed" st.Search.n_pb_attempts 3;
  check_eq "a: PB rows learned, no fallback" st.Search.n_pb_learned 3;
  check_eq "a: ...and the fallback count is 0" st.Search.n_pb_fallback 0;
  (* The clause path, on the SAME conflicts, converts nothing. This is M2-L3's own
     measured result and it is restated here because it is the baseline (a) beats. *)
  check_eq "a: the 1UIP clauses of those conflicts convert: none" st.Search.n_converts 0;
  check "a: ...while the PB rows do convert" (st.Search.n_pb_converts > 0);
  check_eq "a: ...and every one of them is stronger than its clause"
    st.Search.n_pb_stronger st.Search.n_pb_learned;
  (* WHAT THE ROW ACTUALLY IS, measured, and it is stronger than the roadmap asked for
     and degenerate in a way the roadmap did not anticipate. Both halves are asserted
     here rather than summarised, because "strictly stronger" is worth nothing as a claim
     if the shape behind it is not on the record.

     Every learned row on this model is the EMPTY ROW WITH POSITIVE DEGREE -- that is,
     CONTRADICTION -- derived in one elimination from the two halves of the int_lin_eq.
     It is legitimate cutting planes and veripb checks it (test (c)): the `>=` half gives
     x1+x2+x3 >= 2.5 and a Chvatal-Gomory division rounds it to >= 3, the `<=` half
     rounds to <= 2, and the two add to 0 >= k/2. The clause path cannot do this at all:
     a clause is a disjunction of negated bounds and the empty clause is the only
     contradiction it has, which a 1UIP cut over a non-empty decision stack never is.

     So the row IS strictly stronger -- it entails the clause, being false everywhere --
     and it is ALSO degenerate as a propagation test, because a contradiction converts
     and prunes trivially. The honest statement is the one made here; a scene where the
     PB path learns a non-trivial INEQUALITY that outpropagates its clause was looked for
     and not found, and lib/core/pb_analysis.ml's "MEASURED" section says why: the ladder
     implications live in separate .opb rows, so the reason row usually does not
     PB-propagate its pivot and the analysis falls back before it gets that far. *)
  let rows = Search.stats_pb_rows st in
  (match rows with
  | [] -> check "a: a PB row to instantiate" false
  | t :: _ -> (
      check "a: the learned row is the empty contradiction -- no terms, positive degree"
        (Learned.terms t.Pb.row = [] && Learned.degree t.Pb.row > 0);
      check "a: it was reached in one elimination from two model rows"
        (t.Pb.steps = 1 && List.length t.Pb.antecedent_rows = 2);
      check "a: ...and it cites model rows only, which is the I-S4 discharge for a pol"
        (List.length (Pb.cited_ids t.Pb.derivation) = 2);
      (* Strictly stronger, checked rather than asserted: a contradiction is false at
         every 0-1 point, so it entails anything -- in particular the clause the same
         conflict yielded, which is NOT false everywhere. *)
      check "a: the contradiction is false at every 0-1 point (so it entails the clause)"
        ((not (row_holds (fun _ -> true) t.Pb.row))
        && not (row_holds (fun _ -> false) t.Pb.row));
      let store = c.Compile.store in
      check "a: the PB row has a runtime linear form where the clause has none"
        (Learned.to_linear_row t.Pb.row ~decl <> None);
      match Learned.to_linear ~row_id:0 store ~decl t.Pb.row with
      | None -> check "a: the PB row builds a Linear instance" false
      | Some lin ->
          check "a: the PB row builds a Linear instance" true;
          let before = List.map (fun v -> (v, Store.get store v)) (Linear.vars lin) in
          let outcome = Linear.propagate lin store in
          let moved = List.exists (fun (v, d) -> Store.get store v <> d) before in
          check "a: running it at the root prunes, or conflicts -- it is not inert"
            (moved || match outcome with Propagator.Conflict _ -> true | _ -> false)));
  cleanup dir [ opb; pbp ]

(* ------------------------------------------------------------------ (a2) the criterion *)

(* Test (a2). Learning the first ASSERTIVE constraint gives the highest backjump in SAT;
   Le Berre et al. (arXiv 2107.13085) show there is no such guarantee for PB. So the
   criterion here must be slack-based, and a cut carrying SEVERAL conflict-level literals
   must be ACCEPTED rather than resolved away.

   Three things are asserted, and the third is the one that would catch a regression:

     1. the criterion in force is the slack one, by name;
     2. its postcondition HOLDS on what it stopped on;
     3. on at least one learned row, the row carries more than one literal falsified at
        the conflict level -- and [Analysis.one_uip]'s clausal rule would therefore NOT
        have been satisfied there. That is the M2-L2 assertion which must not fire here,
        and it is checked by counting rather than by trusting the header. *)
let test_slack_criterion () =
  print_endline "\n-- M2-L6 (a2): the stopping criterion is the slack one, not 1UIP";
  check_eq "a2: the default criterion is the slack-based one" 0
    (String.compare Search.default_config.Search.pb_criterion.Pb.crit_name
       "assertive-slack");
  check "a2: and it is not a literal count -- [first_resolution] is the other instance"
    (List.length Pb.criteria >= 2);
  let r, dir, opb, pbp = run lineq_src in
  let rows = Search.stats_pb_rows r.r_stats in
  check "a2: rows to inspect" (rows <> []);
  List.iteri
    (fun i (t : Pb.t) ->
      check
        (Printf.sprintf "a2: row %d was stopped by the slack criterion" i)
        (String.equal t.Pb.criterion_name "assertive-slack"))
    rows;
  (* MEASURED, and worth stating because it is not what a reader would guess: on this
     model every learned row comes out a UNIT -- one literal. That is the criterion
     working, not failing: a unit row asserts at the lower level immediately. It does mean
     this model cannot exercise the "several conflict-level literals" case, so that case
     is tested directly on the criterion below rather than hoped for from a fixture. *)
  Printf.printf "     (rows learned here have %s terms)\n"
    (String.concat ","
       (List.map
          (fun (t : Pb.t) -> string_of_int (List.length (Learned.terms t.Pb.row)))
          rows));
  cleanup dir [ opb; pbp ];
  (* THE ASSERTION THE ROADMAP ASKS FOR, stated on the criterion itself so that no fixture
     has to happen to produce the shape.

     A row with THREE literals all falsified at the conflict level, whose slack once the
     conflict level is undone is small enough to propagate. The clausal 1UIP rule counts
     three conflict-level literals and says "keep resolving"; the slack rule looks at the
     arithmetic and says "stop, this is good". Le Berre et al. (arXiv 2107.13085) is the
     statement that the second is right and the first has no guarantee behind it for PB.

     [3a + 3b + 3c >= 3], with a, b and c all falsified at level 5 and nothing falsified
     below it. At level 4 nothing is falsified, so the slack is 9 - 3 = 6... which does
     NOT propagate. Tighten it: degree 8, so slack at level 4 is 9 - 8 = 1 and every
     coefficient 3 exceeds it. The row therefore propagates at level 4 and is accepted,
     while carrying three conflict-level literals. *)
  let la = Lit.ge "a" 1 and lb = Lit.ge "b" 1 and lc = Lit.ge "c" 1 in
  let row = Learned.make [ (3, la); (3, lb); (3, lc) ] 8 in
  let level_of (l : Lit.t) = if List.exists (Lit.equal l) [ la; lb; lc ] then 5 else 0 in
  let v = { Pb.c_row = row; c_conflict_level = 5; c_steps = 1; c_level_of = level_of } in
  check_eq "a2: the scene really does carry three conflict-level literals"
    (List.length
       (List.filter
          (fun (tm : Learned.term) -> level_of tm.Learned.lit = 5)
          (Learned.terms row)))
    3;
  check "a2: the slack criterion ACCEPTS it -- several conflict-level literals is fine"
    (Pb.assertive_slack.Pb.stop v);
  check "a2: ...and its postcondition holds on it"
    (Pb.postcondition_holds Pb.assertive_slack v);
  check
    "a2: ...whereas the clausal 1UIP rule would NOT have stopped here (3 > 1), which is \
     the M2-L2 assertion that must not fire in this lane"
    (List.length
       (List.filter
          (fun (tm : Learned.term) -> level_of tm.Learned.lit = 5)
          (Learned.terms row))
    > 1);
  (* And the criterion is not vacuously true: a row that says nothing at the lower level
     is REJECTED, so [stop] is a real test and not a constant. *)
  let loose = Learned.make [ (3, la); (3, lb); (3, lc) ] 3 in
  check "a2: ...and a row that asserts nothing below the conflict level is REJECTED"
    (not (Pb.assertive_slack.Pb.stop { v with Pb.c_row = loose }))

(* ------------------------------------------------------------------ (b) the rate *)

(* Test (b). The clause path is PERMANENT (D-0044), so a build in which PB analysis never
   succeeded would be green in every other measure this suite has. The rate is therefore
   instrumented, reported by --stats, and asserted NON-DEGENERATE on a fixture: at least
   one model where it is 0, and at least one where it is 1, so that neither "always
   falls back" nor "the counter is never incremented" can pass.

   [bool_src] falls back because [array_bool_or] exposes no PB row; [lineq_src] does not
   fall back at all. Both facts are about lib/core/propagator.ml's [pb_row] being [None]
   for a clause propagator, which is deliberate and documented there. *)
let test_fallback_rate () =
  print_endline "\n-- M2-L6 (b): the fallback rate is instrumented and non-degenerate";
  let a, d1, o1, p1 = run lineq_src in
  let b, d2, o2, p2 = run bool_src in
  check_eq "b: lineq -- conflicts analysed" a.r_stats.Search.n_pb_attempts 3;
  check "b: lineq -- the rate is 0.00, i.e. the PB path really ran"
    (Search.stats_pb_fallback_rate a.r_stats = 0.);
  check "b: lineq -- and rows were learned" (a.r_stats.Search.n_pb_learned > 0);
  check "b: bool -- the rate is 1.00, i.e. the fallback really is taken"
    (Search.stats_pb_fallback_rate b.r_stats = 1.);
  check "b: bool -- and the reason is recorded, not just counted"
    (Search.stats_pb_fallbacks b.r_stats <> []);
  check "b: bool -- the reason names the propagator that has no PB row"
    (match Search.stats_pb_fallbacks b.r_stats with
    | m :: _ -> contains ~needle:"no PB row" m
    | [] -> false);
  (* The denominator is real: attempts = learned + fallbacks, on both runs. A counter
     that did not satisfy this would be one the rate could not be computed from. *)
  check_eq "b: lineq -- attempts = learned + fallbacks" a.r_stats.Search.n_pb_attempts
    (a.r_stats.Search.n_pb_learned + a.r_stats.Search.n_pb_fallback);
  check_eq "b: bool -- attempts = learned + fallbacks" b.r_stats.Search.n_pb_attempts
    (b.r_stats.Search.n_pb_learned + b.r_stats.Search.n_pb_fallback);
  (* And with the PB path switched off, nothing is attempted at all -- so the counters
     measure this row's code and not something that was happening anyway. *)
  let c, d3, o3, p3 = run ~config:Search.no_pb lineq_src in
  check_eq "b: with cfg.pb off, nothing is attempted" c.r_stats.Search.n_pb_attempts 0;
  check_eq "b: ...and nothing is learned by this path" c.r_stats.Search.n_pb_learned 0;
  check "b: ...while the M2-L3 clause path is unaffected"
    (c.r_stats.Search.n_learned = a.r_stats.Search.n_learned);
  cleanup d1 [ o1; p1 ];
  cleanup d2 [ o2; p2 ];
  cleanup d3 [ o3; p3 ]

(* ------------------------------------------------------------------ (c) the proof *)

(* Test (c). The PB row reaches the page as a [pol] that STATES what it derives, so the
   checker compares our [Learned.combine] arithmetic against its own and rejects the line
   where they differ. That makes this test much sharper than "the proof is accepted": it
   is the arithmetic of this row being checked by veripb rather than by an assertion.

   Both the model that learns PB rows and the model that falls back are checked, so the
   two paths are covered and not just the one. *)
let test_proof_accepted () =
  print_endline "\n-- M2-L6 (c): the proof is accepted, with the stated pol on the page";
  List.iter
    (fun (title, src) ->
      let r, dir, opb, pbp = run src in
      check
        (Printf.sprintf "c: %s: the audit is clean (I-X2: every learned id retired)" title)
        (r.r_audit_error = None);
      expect_accepted ~title:(Printf.sprintf "c: %s" title) ~dir ~opb ~pbp;
      cleanup dir [ opb; pbp ])
    [
      ("lineq (PB path)", lineq_src);
      ("bool (fallback path)", bool_src);
      ("backjump (fallback path)", backjump_src);
    ]

(* ------------------------------------------------------------------ (d) I-X8 *)

(* Test (d). I-X8 / D-0029: coefficient growth must RAISE, not wrap. [Learned.combine] is
   the one place in this solver where coefficients multiply without bound, so it is where
   the cap is met.

   Two halves, and the second is what makes the first worth having:

     1. the arithmetic raises. A scene built to force growth past [Checked]'s cap asserts
        [Checked.Overflow], not a wrapped negative coefficient.
     2. the LOOP turns that raise into a fallback rather than into a crash. An overflow
        during conflict analysis is a reason to learn a clause instead; it is never a
        reason to abandon a solve, and it is never a reason to wrap. *)
let test_overflow_raises () =
  print_endline "\n-- M2-L6 (d): coefficient growth raises (I-X8 / D-0029)";
  let l1 = Lit.ge "x" 1 and l2 = Lit.ge "y" 1 in
  let big = max_int / 4 in
  let a = Learned.make [ (big, l1) ] 1 in
  let b = Learned.make [ (big, l2) ] 1 in
  (* A modest combination is fine and does not raise: the break has to be the cap, not
     any multiplication at all. *)
  check "d: a combination inside the cap does not raise"
    (try
       let _ = Learned.combine a 1 b 1 in
       true
     with Checked.Overflow _ -> false);
  check "d: growth past the cap RAISES Checked.Overflow, it does not wrap"
    (try
       let r = Learned.combine a big b big in
       (* If we get here the cap did not fire. Report the coefficient we got, because a
          wrapped NEGATIVE coefficient is the specific failure I-X8 exists to prevent and
          it would otherwise look like an ordinary row. *)
       Printf.printf
         "     (no raise; first coefficient came out as %d -- a negative here is the \
          wrap I-X8 forbids)\n"
         (match Learned.terms r with tm :: _ -> tm.Learned.coeff | [] -> 0);
       false
     with Checked.Overflow _ -> true);
  (* And the scaled degree overflows too, which is the other operand of the same rule. *)
  check "d: the degree is checked as well as the coefficients"
    (try
       let _ =
         Learned.combine
           (Learned.make [ (1, l1) ] big)
           big
           (Learned.make [ (1, l2) ] big)
           big
       in
       false
     with Checked.Overflow _ -> true)

(* ------------------------------------------------- determinism of the PB path *)

(* The gate requires two runs to emit a byte-identical proof, and a learned row whose
   terms came out of a hash table is the way that breaks. M2-L3 checks this for the clause
   path; the PB path adds rows to the same proof, so it is checked here too. *)
let test_pb_determinism () =
  print_endline "\n-- M2-L6: two runs emit a byte-identical proof with the PB path on";
  let a, d1, o1, p1 = run lineq_src in
  let b, d2, o2, p2 = run lineq_src in
  check "pb: two runs emit a byte-identical proof" (String.equal a.r_proof b.r_proof);
  check_eq "pb: and identical PB counters" a.r_stats.Search.n_pb_learned
    b.r_stats.Search.n_pb_learned;
  check "pb: and identical learned rows"
    (List.length (Search.stats_pb_rows a.r_stats)
     = List.length (Search.stats_pb_rows b.r_stats)
    && List.for_all2
         (fun (x : Pb.t) (y : Pb.t) ->
           String.equal (Learned.to_string x.Pb.row) (Learned.to_string y.Pb.row))
         (Search.stats_pb_rows a.r_stats)
         (Search.stats_pb_rows b.r_stats));
  cleanup d1 [ o1; p1 ];
  cleanup d2 [ o2; p2 ]

(* THE NON-VACUOUS ORACLE (docs/ROADMAP.md M2-L6 test (e)).

   [test_oracle] above runs the entailment on rows a real solve derived, which is the
   right thing to check but is vacuous on the models that exercise this path: their
   antecedents have no 0-1 model at all, which is exactly why the search conflicts on
   them. So the entailment is also checked here, exhaustively, on rows chosen so that the
   premises ARE satisfiable -- and the number of points at which they hold is asserted to
   be positive, so this oracle cannot go vacuous without failing.

   What is checked is the soundness of the two primitives the derivation is built from,
   at every 0-1 point:

     1. [Learned.combine a ca b cb] -- a positive linear combination, including the
        complementary-literal cancellation that [Learned.make] deliberately does not do.
        The cancellation is the step most likely to be wrong and the one the checkers
        would catch only indirectly.
     2. [Reduce]'s output -- literal-axiom weakening followed by Chvatal-Gomory division.
        Division is sound at 0-1 points (if [sum a_i l_i >= b] holds then
        [sum ceil(a_i/d) l_i >= ceil(b/d)] holds), which is what makes the whole
        derivation sound at points that do not respect the order encoding's ladder.

   Together with test (c) -- where the [pol] STATES the row and veripb compares our
   arithmetic with its own -- this is the derivation checked from both ends. *)
let entails ~title ~(premises : Learned.t list) ~(conclusion : Learned.t) =
  let universe = literal_universe (conclusion :: premises) in
  let n = List.length universe in
  let arr = Array.of_list universe in
  let premises_met = ref 0 and violations = ref 0 in
  for mask = 0 to (1 lsl n) - 1 do
    let assign (l : Lit.t) =
      let rec idx i =
        if i >= n then None
        else if Lit.equal arr.(i) { l with Lit.positive = true } then Some i
        else idx (i + 1)
      in
      match idx 0 with
      | None -> false
      | Some i ->
          let bit = mask land (1 lsl i) <> 0 in
          if l.Lit.positive then bit else not bit
    in
    if List.for_all (row_holds assign) premises then (
      incr premises_met;
      if not (row_holds assign conclusion) then incr violations)
  done;
  check
    (Printf.sprintf "%s: the premises are satisfiable (%d of %d points) -- not vacuous"
       title !premises_met (1 lsl n))
    (!premises_met > 0);
  check
    (Printf.sprintf "%s: and the conclusion holds at every one of them" title)
    (!violations = 0)

let test_oracle_primitives () =
  print_endline "\n-- M2-L6 (e): the derivation's primitives are sound at every 0-1 point";
  let a = Lit.ge "a" 1 and b = Lit.ge "b" 1 and c = Lit.ge "c" 1 and d = Lit.ge "d" 1 in
  (* 1. plain addition. *)
  let r1 = Learned.make [ (3, a); (2, b) ] 4 in
  let r2 = Learned.make [ (1, b); (4, c) ] 3 in
  entails ~title:"e: combine 1*r1 + 1*r2" ~premises:[ r1; r2 ]
    ~conclusion:(Learned.combine r1 1 r2 1);
  entails ~title:"e: combine 2*r1 + 3*r2" ~premises:[ r1; r2 ]
    ~conclusion:(Learned.combine r1 2 r2 3);
  (* 2. the CANCELLATION, which is the step [Learned.make] does not do and the one this
     row added. [a] on one side and [~a] on the other must cancel and lower the degree,
     and the result must still be entailed. *)
  let p = Learned.make [ (3, a); (2, b) ] 3 in
  let q = Learned.make [ (3, Lit.negate a); (2, c) ] 2 in
  let cancelled = Learned.combine p 1 q 1 in
  check "e: the complementary pair really did cancel -- no [a] term survives"
    (not
       (List.exists
          (fun (tm : Learned.term) -> Lit.var_equal tm.Learned.lit.Lit.v a.Lit.v)
          (Learned.terms cancelled)));
  entails ~title:"e: combine with cancellation" ~premises:[ p; q ] ~conclusion:cancelled;
  (* 3. REDUCTION: weaken, then divide. Both rules, on a row where they differ -- this is
     lib/core/reduce.ml's own worked case, [3v + 3u + 1w >= 5] with pivot [v]. *)
  let v = Lit.ge "v" 1 and u = Lit.ge "u" 1 and w = Lit.ge "w" 1 in
  let row = Learned.make [ (3, v); (3, u); (1, w) ] 5 in
  let falsified _ = false in
  let view = { Reduce.row; pivot = v; falsified } in
  List.iter
    (fun (rule : Reduce.t) ->
      match rule.Reduce.reduce view with
      | None ->
          check (Printf.sprintf "e: %s reduces the worked case" rule.Reduce.name) false
      | Some o ->
          check (Printf.sprintf "e: %s reduces the worked case" rule.Reduce.name) true;
          entails
            ~title:(Printf.sprintf "e: %s's reduced row" rule.Reduce.name)
            ~premises:[ row ] ~conclusion:o.Reduce.reduced)
    [ Reduce.division; Reduce.round_to_one ];
  (* And the difference between the two rules is real, which is what makes checking both
     worth doing: [round_to_one] keeps [u], [division] throws it away. *)
  (match (Reduce.division.Reduce.reduce view, Reduce.round_to_one.Reduce.reduce view) with
  | Some dv, Some rt ->
      check "e: round_to_one keeps strictly more than division does"
        (List.length (Learned.terms rt.Reduce.reduced)
        > List.length (Learned.terms dv.Reduce.reduced))
  | _ -> check "e: both rules applied" false);
  (* 4. The whole step, end to end: reduce a reason and add it to a conflicting row, the
     way [Pb_analysis.step] does, and check the result is entailed by both originals. *)
  let conflict = Learned.make [ (2, Lit.negate v); (2, d) ] 2 in
  match Reduce.round_to_one.Reduce.reduce view with
  | None -> check "e: the end-to-end step reduced" false
  | Some o ->
      let combined = Learned.combine conflict 1 o.Reduce.reduced 2 in
      check "e: the end-to-end step reduced" true;
      entails ~title:"e: conflict + 2 * reduce(reason)" ~premises:[ conflict; row ]
        ~conclusion:combined

let () =
  test_minimise_pure ();
  test_minimise_break_in_a_proof ();
  test_i_s4_ordering ();
  test_i_s4_crossings_are_real ();
  test_node_count_decreases ();
  test_conversion_rate ();
  test_m2l10_coverage ();
  test_backjump_answers_the_same ();
  test_i_s3 ();
  test_determinism ();
  test_strictly_stronger ();
  test_slack_criterion ();
  test_fallback_rate ();
  test_proof_accepted ();
  test_overflow_raises ();
  test_oracle ();
  test_oracle_primitives ();
  test_pb_determinism ();
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "learning unit tests passed"
