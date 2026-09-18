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

(* M1-T46: the two checkers word a rejection differently, so a break lane that matched one
   wording alone would be a vacuous diagnosis on the other binary. Both breaks in this
   file surface the same way -- a `rup` the checker cannot re-derive -- and the pair below
   was MEASURED on 2026-09-18 by running each break lane under each binary, not guessed:

     3.0.2  "The constraint is not implied by reverse unit propagation (RUP) from core
             and derived database."
     2.2.2  "Verification failed. ... Hint: Failed to show '1 w_ge_3 >= 1' by reverse
             unit propagation."

   Worth one sentence, because it is the one place this project's standing rule needs
   qualifying: M1-T46 found that the two checkers' rejections "share no substring", and
   that is true of the wordings it measured (a non-contradiction, and a deleted id). It is
   NOT true of a RUP failure -- both say "reverse unit propagation". Matching only that
   would still be wrong here, because it is the least specific thing either says and a
   different RUP failure elsewhere in the proof would match it; so both wordings are
   listed in full-strength form and either one counts. *)
let rejection_wordings =
  [ "is not implied by reverse unit propagation"; "Failed to show" ]

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
   backjump_lineq_unsat.fzn's own run through scripts/verify_proof.sh, under BOTH
   BAGUETTE_PROOF_FORMAT settings and both veripb binaries -- this in-process run only
   re-confirms the default (3.0) path, since [run] does not expose a format knob. *)
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
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "learning unit tests passed"
