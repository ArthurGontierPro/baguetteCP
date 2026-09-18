(* Unit tests for M2-L13 / D-0054: the PB explanation as a SOLVING-side object.

   D-0054's sentence is the whole brief: a PB line for proof logging and a PB explanation
   for solving are different objects. The first must be sound, complete and citable; the
   second must be USEFUL TO PROPAGATION. This file tests the second, and every lane that
   touches the proof puts the emitted artefact in front of veripb 3.0.2, because a test
   that solves a model and does not check the proof is half a test. A missing checker is
   a FAILURE here, never a skip.

   The obligations, in the order docs/ROADMAP.md M2-L13 states them:

     (a) A scene where the learned PB row PRUNES and a clause over the SAME literals does
         not. This is the row's entire justification and M2-L6 looked for it and did not
         find it. It is [test_row_beats_clause] (hand-built, so the arithmetic is
         visible) and [test_php_scene] (a real solve, so it is not only a scene).
     (b) Node count must MOVE. [test_php_scene], against its own
         [no_propagate_learned] control.
     (c) Every proof still verified. Every solving lane below calls [check_verified].
     (d) The declared consistency level is honest. [test_declared_level], which asserts
         BOTH directions: the propagator only ever moves bounds, and it does NOT achieve
         domain consistency -- a hole survives it, which is exactly why the declaration
         is BOUNDS and not DOMAIN.
     (e) A break for each, performed. The clause control in (a) is (a)'s break, the
         [no_propagate_learned] control is (b)'s, the surviving hole is (d)'s, and (c)'s
         is [test_break_degree]: the propagator is given a constraint STRONGER than the
         row on the page, and the checker must reject the prunings that follow. That last
         one is the only oracle there is for a wrong slack rule -- an over-strong
         propagator still answers UNSAT on an unsatisfiable model, so the answer cannot
         see it.

   Domains are 0..1 or single digits throughout (D-0028: the order encoding is
   width-proportional and a wide domain is a proof that dwarfs the suite). *)

module F = Baguette_flatzinc
module Compile = F.Compile
module Store = Baguette_core.Store
module Domain = Baguette_core.Domain
module Var = Baguette_core.Var
module Pb = Baguette_core.Pb
module Clause = Baguette_core.Clause
module Propagator = Baguette_core.Propagator
module Search = Baguette_core.Search
module Justify = Baguette_core.Justify
module Learned = Baguette_core.Learned
module Encoding = Baguette_proof.Encoding
module Writer = Baguette_proof.Writer
module Lit = Baguette_proof.Lit

let () = Mem_guard.install ()
let failures = ref 0

let check name cond =
  if cond then Printf.printf "ok   %s\n" name
  else (
    Printf.printf "FAIL %s\n" name;
    incr failures)

let check_eq name got want =
  if got = want then Printf.printf "ok   %s\n" name
  else (
    Printf.printf "FAIL %s: got %d, want %d\n" name got want;
    incr failures)

let read_file f =
  let ic = open_in_bin f in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let contains ~needle hay =
  let n = String.length needle and h = String.length hay in
  let rec go i = i + n <= h && (String.sub hay i n = needle || go (i + 1)) in
  n = 0 || go 0

let store_of boxes =
  let names = Array.of_list (List.map fst boxes) in
  let domains = Array.of_list (List.map (fun (_, (lo, hi)) -> Domain.make lo hi) boxes) in
  Store.create ~names ~domains

(* The declared bounds an instantiation needs. In the solver they come from
   [Learned.decl_of_encoding], i.e. from the ENCODING and never from the store, because a
   learned constraint is built mid-search when the store's bounds are narrow. Here the
   two agree because nothing has narrowed yet, which is the condition that makes a
   hand-built scene safe. *)
let decl_of boxes name =
  List.find_map (fun (n, (lo, hi)) -> if n = name then Some (lo, hi) else None) boxes

let domains_of store boxes = List.mapi (fun i _ -> Store.get store (Var.of_int i)) boxes

(* ---------------------------------------------------------------------------
   (a) THE ROW: the PB inequality prunes where the clause over the same literals
   does not -- and the clause is the CONTROL, run on the same store, in the same
   scene, so that "prunes" is a comparison and not an adjective.

   The scene, over three `var bool`s (D-0007: a Boolean is the order encoding on [0, 1],
   so `a` is [a >= 1]):

       2*[a>=1] + 1*[b>=1] + 1*[c>=1]  >=  2,     with `a` fixed to 0.

   Slack = (1 + 1) - 2 = 0 once [a>=1] is falsified, and both remaining coefficients beat
   it, so BOTH b and c are forced to 1. The clause over the same three literals --
   `a \/ b \/ c` -- has two open literals and can say nothing at all. That gap is the
   whole of D-0054's "as strong as possible": the clause is the degree-1 WEAKENING of the
   row, and here the weakening costs two prunings.

   A second shape is checked beside it because a propagator that only ever prunes is half
   a propagator: with the degree at 3 the same falsification leaves slack -1 and the row
   CONFLICTS, while the clause still says nothing. *)
let boxes3 = [ ("a", (0, 1)); ("b", (0, 1)); ("c", (0, 1)) ]
let lits3 = [ Lit.ge "a" 1; Lit.ge "b" 1; Lit.ge "c" 1 ]
let terms3 = [ (2, Lit.ge "a" 1); (1, Lit.ge "b" 1); (1, Lit.ge "c" 1) ]

let test_row_beats_clause () =
  print_endline "\n-- M2-L13 (a): the PB row prunes where the clause cannot";
  let decl = decl_of boxes3 in
  (* `a` fixed to 0, i.e. [a>=1] falsified. Nothing else is known. The store is BORN
     narrow rather than narrowed through a mutator: the declared bounds an instance
     freezes come from [decl] and not from the store, which is exactly the hazard
     lib/core/learned.ml's "Why the [Linear.t] is built here" spells out, so a scene that
     starts narrow is the honest shape of a mid-search store. *)
  let scene () = store_of [ ("a", (0, 0)); ("b", (0, 1)); ("c", (0, 1)) ] in
  (* --- the PB row --- *)
  let s_pb = scene () in
  let row = Option.get (Pb.of_terms s_pb ~decl ~degree:2 terms3) in
  let before_pb = domains_of s_pb boxes3 in
  let out_pb = Pb.propagate row s_pb in
  let after_pb = domains_of s_pb boxes3 in
  check_eq "a: the PB row instantiates over all three order literals it names"
    (Pb.width row) 3;
  check "a: ...and it PRUNES -- both remaining literals are forced to 1"
    (out_pb = Propagator.Fixpoint
    && Domain.lo (Store.get s_pb (Var.of_int 1)) = 1
    && Domain.lo (Store.get s_pb (Var.of_int 2)) = 1);
  check "a: ...which is two bounds that were open before" (before_pb <> after_pb);
  (* --- THE CONTROL: the clause over the SAME literals, the SAME scene --- *)
  let s_cl = scene () in
  let cl = Option.get (Clause.of_lits s_cl ~decl lits3) in
  let before_cl = domains_of s_cl boxes3 in
  let out_cl = Clause.propagate cl s_cl in
  check "a: BREAK/CONTROL -- the clause over the same literals moves NOTHING"
    (out_cl = Propagator.Fixpoint && domains_of s_cl boxes3 = before_cl);
  check "a: ...and the two propagators really were given the same literal set"
    (List.sort compare (Clause.literals cl) = List.sort compare (Pb.literals row));
  (* --- the conflict shape, same comparison --- *)
  let s_pb3 = scene () in
  let row3 = Option.get (Pb.of_terms s_pb3 ~decl ~degree:3 terms3) in
  check "a: at degree 3 the same falsification CONFLICTS"
    (match Pb.propagate row3 s_pb3 with
    | Propagator.Conflict _ -> true
    | Propagator.Fixpoint -> false);
  let s_cl3 = scene () in
  let cl3 = Option.get (Clause.of_lits s_cl3 ~decl lits3) in
  check "a: BREAK/CONTROL -- and the clause still does not, not even conflict"
    (Clause.propagate cl3 s_cl3 = Propagator.Fixpoint
    && domains_of s_cl3 boxes3 = before_cl)

(* ---------------------------------------------------------------------------
   (a), continued: the SAME comparison over ORDER LITERALS on an integer variable,
   because the Boolean case is the one where a PB row and a clause are least far apart.

       3*[x>=3] + 2*[y>=2]  >=  3,   x, y in 0..4, with [y>=2] falsified (y <= 1).

   Slack = 3 - 3 = 0 and 3 > 0, so [x>=3] is forced and lo(x) moves to 3 -- a bound three
   steps up the ladder. The clause `[x>=3] \/ [y>=2]` in the same scene forces the same
   literal, because with one literal false and one open a clause IS unit. So this shape
   is NOT a separation on its own; what separates them is the FIRST scene, where two
   literals are open. Both are kept, and this one is labelled as the case where the
   clause keeps up, because a file that only showed the favourable scene would be
   choosing its evidence. *)
let boxes2 = [ ("x", (0, 4)); ("y", (0, 4)) ]

let test_order_literal_scene () =
  print_endline "\n-- M2-L13 (a): the same comparison over integer order literals";
  let decl = decl_of boxes2 in
  let terms = [ (3, Lit.ge "x" 3); (2, Lit.ge "y" 2) ] in
  let scene () = store_of [ ("x", (0, 4)); ("y", (0, 1)) ] in
  let s1 = scene () in
  let row = Option.get (Pb.of_terms s1 ~decl ~degree:3 terms) in
  ignore (Pb.propagate row s1);
  check "a/int: the PB row moves lo(x) three rungs up the ladder"
    (Domain.lo (Store.get s1 (Var.of_int 0)) = 3);
  let s2 = scene () in
  let cl = Option.get (Clause.of_lits s2 ~decl [ Lit.ge "x" 3; Lit.ge "y" 2 ]) in
  ignore (Clause.propagate cl s2);
  check
    "a/int: and here the CLAUSE keeps up -- one literal false, one open, so it is unit"
    (Domain.lo (Store.get s2 (Var.of_int 0)) = 3);
  (* Now the coefficients that separate them, on the same two variables: raise the
     degree so that the row still forces [x>=3] with BOTH literals open, which no clause
     ever does. 3*[x>=3] + 2*[y>=2] >= 3 with nothing known has slack 2, and 3 > 2. *)
  let s3 = store_of boxes2 in
  let row3 = Option.get (Pb.of_terms s3 ~decl ~degree:3 terms) in
  ignore (Pb.propagate row3 s3);
  check "a/int: with NOTHING known the row still forces [x>=3] -- 3 > slack 2"
    (Domain.lo (Store.get s3 (Var.of_int 0)) = 3);
  let s4 = store_of boxes2 in
  let cl4 = Option.get (Clause.of_lits s4 ~decl [ Lit.ge "x" 3; Lit.ge "y" 2 ]) in
  ignore (Clause.propagate cl4 s4);
  check "a/int: BREAK/CONTROL -- the clause with two open literals moves nothing"
    (Domain.lo (Store.get s4 (Var.of_int 0)) = 0)

(* ---------------------------------------------------------------------------
   (a), and the reason D-0054 gives for the row existing at all: the LADDER.

   lib/core/prop/pb.ml folds a variable's ladder into a rung's effective coefficient,
   because falsifying `[x>=3]` falsifies `[x>=5]` with it. Without that, the plain slack
   rule is blind to the order encoding and reads a row that MEANS `x >= 2` as saying
   nothing at all. This is the scene, minimal:

       1*[x>=1] + 1*[x>=2] + 1*[x>=3]  >=  3,   x in 0..3.

   Plainly: total coefficient 3, degree 3, slack 0, and 1 > 0 for each -- so here even
   the plain rule fires. Take the degree down to 2 and the plain rule stops (slack 1, no
   coefficient above 1) while the ladder rule still forces `[x>=2]`, because falsifying
   it costs [x>=2] AND [x>=3], i.e. 2 > 1. The row says `x >= 2` and the ladder-aware
   propagator says so. *)
let test_ladder_effective () =
  print_endline "\n-- M2-L13 (a): the ladder is folded into the effective coefficient";
  let boxes = [ ("x", (0, 3)) ] in
  let decl = decl_of boxes in
  let terms = [ (1, Lit.ge "x" 1); (1, Lit.ge "x" 2); (1, Lit.ge "x" 3) ] in
  let s = store_of boxes in
  let row = Option.get (Pb.of_terms s ~decl ~degree:2 terms) in
  ignore (Pb.propagate row s);
  check "a/ladder: the row `[x>=1]+[x>=2]+[x>=3] >= 2` forces x >= 2"
    (Domain.lo (Store.get s (Var.of_int 0)) = 2);
  (* THE CONTROL that says this is the ladder and not something else: the same three
     coefficients on three DIFFERENT variables carry no implication between them, and
     then nothing may be forced. If this reddened, the rule above would be unsound. *)
  let boxes' = [ ("p", (0, 1)); ("q", (0, 1)); ("r", (0, 1)) ] in
  let decl' = decl_of boxes' in
  let terms' = [ (1, Lit.ge "p" 1); (1, Lit.ge "q" 1); (1, Lit.ge "r" 1) ] in
  let s' = store_of boxes' in
  let row' = Option.get (Pb.of_terms s' ~decl:decl' ~degree:2 terms') in
  ignore (Pb.propagate row' s');
  check
    "a/ladder: BREAK/CONTROL -- the same row over three UNRELATED variables forces \
     nothing"
    (domains_of s' boxes' = List.map (fun _ -> Domain.make 0 1) boxes')

(* ---------------------------------------------------------------------------
   (d) The declared consistency level, in both directions

   SPEC 3.2 makes the declared level the bound on what an explanation may claim, so a
   module that declared DOMAIN and delivered BOUNDS would be claiming more than it
   delivers. Two things are asserted, and the second is the one a reader should look for:

     - it declares BOUNDS, and it only ever MOVES BOUNDS. [Store.set_lo] and
       [Store.set_hi] are the only mutators lib/core/prop/pb.ml calls, so it cannot punch
       an interior hole ([Store.remove_with_facts], of which I-X10 records [Ne] is the
       sole caller in lib/).
     - and BOUNDS is not an understatement dressed up as modesty: the propagator does NOT
       achieve domain consistency, and the scene below shows a value with no support
       SURVIVING it. `[x>=3] \\/ ~[x>=2]` over x in 0..4 is the constraint
       `x >= 3 or x <= 1`, i.e. a HOLE at 2. Unit propagation moves no bound (both
       literals are open) and 2 stays in the domain. A lane that declared DOMAIN here
       would be claiming that 2 had been removed. It has not been, and this is the break
       that says so. *)
let test_declared_level () =
  print_endline "\n-- M2-L13 (d): the declared level is BOUNDS, and it is honest";
  check "d: Pb declares BOUNDS" (Pb.consistency = Propagator.Bounds);
  check "d: ...and so does the learned face"
    (Pb.Learned_pb.consistency = Propagator.Bounds);
  check "d: ...and Clause, which is its degree-1 case, agrees"
    (Clause.consistency = Propagator.Bounds);
  check "d: ...while Clause.Bool_clause still declares DOMAIN on its [0,1] precondition"
    (Clause.Bool_clause.consistency = Propagator.Domain);
  (* The hole that survives. *)
  let boxes = [ ("x", (0, 4)) ] in
  let decl = decl_of boxes in
  let terms = [ (1, Lit.ge "x" 3); (1, Lit.le "x" 1) ] in
  let s = store_of boxes in
  let row = Option.get (Pb.of_terms s ~decl ~degree:1 terms) in
  let out = Pb.propagate row s in
  let d = Store.get s (Var.of_int 0) in
  check "d: BREAK -- `x>=3 or x<=1` leaves a HOLE at 2 that BOUNDS does not punch"
    (out = Propagator.Fixpoint && Domain.lo d = 0 && Domain.hi d = 4 && Domain.mem d 2);
  (* And the same constraint DOES conflict once the hole is all that is left, which is
     the half of the claim that makes the level BOUNDS rather than nothing at all. *)
  let s2 = store_of [ ("x", (2, 2)) ] in
  let row2 = Option.get (Pb.of_terms s2 ~decl ~degree:1 terms) in
  check "d: ...and it still CONFLICTS when the variable is driven into that hole"
    (match Pb.propagate row2 s2 with
    | Propagator.Conflict _ -> true
    | Propagator.Fixpoint -> false)

(* ---------------------------------------------------------------------------
   The real solve: a search harness through the front end, so nothing below is a
   hand-built scene. Every proof it emits goes to veripb. *)

type run_result = {
  r_outcome : Search.outcome;
  r_stats : Search.stats;
  r_dir : string;
  r_opb : string;
  r_pbp : string;
}

let run ?(config = Search.default_config) src =
  let m = F.Builder.of_string ~file:"test" src in
  let c = Compile.compile m in
  let dir = Filename.temp_file "baguette_pb" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  let opb = Filename.concat dir "m.opb" and pbp = Filename.concat dir "m.pbp" in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "M2-L13" ] c.Compile.encoding oc;
  close_out oc;
  let oc = open_out pbp in
  let writer = Writer.create ~audit:true oc in
  Encoding.start_proof c.Compile.encoding writer;
  let ctx = Justify.create ~writer ~encoding:c.Compile.encoding in
  let stats = Search.stats_create () in
  let outcome =
    Search.solve ~engine:c.Compile.engine ~store:c.Compile.store ~ctx
      ~check:(fun _ -> true)
      ~stats ~config ()
  in
  close_out oc;
  { r_outcome = outcome; r_stats = stats; r_dir = dir; r_opb = opb; r_pbp = pbp }

let cleanup r =
  List.iter (fun f -> try Sys.remove f with _ -> ()) [ r.r_opb; r.r_pbp ];
  try Sys.rmdir r.r_dir with _ -> ()

(* lib/proof/checker.ml, shared with scripts/checker.sh. [None] is a FAILURE at every
   call site, never a skip. *)
let veripb r =
  match Baguette_proof.Checker.find () with
  | None ->
      check "M2-L13: veripb 3.0.2 is on PATH -- a missing checker is a failure" false;
      None
  | Some exe ->
      let log = Filename.concat r.r_dir "log" in
      let rc =
        Sys.command
          (Printf.sprintf "%s %s %s > %s 2>&1" (Filename.quote exe)
             (Filename.quote r.r_opb) (Filename.quote r.r_pbp) (Filename.quote log))
      in
      let out = read_file log in
      (try Sys.remove log with _ -> ());
      Some (rc = 0, out)

let check_verified name r =
  match veripb r with
  | None -> ()
  | Some (ok, out) ->
      if not ok then Printf.printf "     checker said: %s\n" (String.trim out);
      check name ok

(* PIGEONHOLE 5 -> 4, the same shape as test/models/php_unsat.fzn and deliberately
   smaller: twenty `var 0..1`s, so the order encoding is one rung per variable and the
   memory ceiling is nowhere near. Hardness is combinatorial, which is M2-L14's point and
   the reason a learned constraint has a second subtree to pay off in at all. *)
let php_src =
  "array [1..20] of var 0..1: x;\n\
   constraint int_lin_eq([1,1,1,1],[x[1],x[2],x[3],x[4]],1);\n\
   constraint int_lin_eq([1,1,1,1],[x[5],x[6],x[7],x[8]],1);\n\
   constraint int_lin_eq([1,1,1,1],[x[9],x[10],x[11],x[12]],1);\n\
   constraint int_lin_eq([1,1,1,1],[x[13],x[14],x[15],x[16]],1);\n\
   constraint int_lin_eq([1,1,1,1],[x[17],x[18],x[19],x[20]],1);\n\
   constraint int_lin_le([1,1,1,1,1],[x[1],x[5],x[9],x[13],x[17]],1);\n\
   constraint int_lin_le([1,1,1,1,1],[x[2],x[6],x[10],x[14],x[18]],1);\n\
   constraint int_lin_le([1,1,1,1,1],[x[3],x[7],x[11],x[15],x[19]],1);\n\
   constraint int_lin_le([1,1,1,1,1],[x[4],x[8],x[12],x[16],x[20]],1);\n\
   solve satisfy;\n"

(* ---------------------------------------------------------------------------
   (a) on a real solve, (b) the node count, (c) the proof.

   [n_pb_prunes] counts bounds a REGISTERED LEARNED PB INSTANCE actually moved, read off
   the trail (M2-T7 stamps every entry with the instance that pushed it) rather than
   reported by the propagator. M2-L12 measured the same quantity as 0 for the learned
   CLAUSE over the whole suite, which is the number this row exists to move.

   Do NOT read [n_pb_converts] as a success measure here. That counter is
   [Learned.to_linear_row], i.e. the proof-side gate M2-L13 removed from the propagation
   path; bin/main.ml labels it MEASURED ONLY and docs/ROADMAP.md M2-L13 says in terms not
   to measure this row by it. *)
let test_php_scene () =
  print_endline "\n-- M2-L13 (a)(b)(c): a real solve -- prunings, node count, proof";
  let on = run php_src in
  let off = run ~config:Search.no_propagate_learned php_src in
  check "b: the scene is UNSAT on both builds"
    (on.r_outcome = Search.Unsat && off.r_outcome = Search.Unsat);
  check "a: learned PB rows were registered as engine instances"
    (on.r_stats.Search.n_pb_instances > 0);
  check "a: ...and one of them actually MOVED a bound -- the counter M2-L12 read as 0"
    (on.r_stats.Search.n_pb_prunes > 0);
  check "a: ...and one of them refuted a node outright"
    (on.r_stats.Search.n_pb_inst_conflicts > 0);
  (* (b). The tree must MOVE, and the control is the same solver with the registration
     switched off -- not a different model and not a remembered figure. *)
  check
    (Printf.sprintf "b: the tree SHRINKS -- %d nodes with propagation, %d without"
       on.r_stats.Search.nodes off.r_stats.Search.nodes)
    (on.r_stats.Search.nodes < off.r_stats.Search.nodes);
  check
    "b: BREAK/CONTROL -- with the registration off nothing is registered and nothing \
     prunes"
    (off.r_stats.Search.n_pb_instances = 0 && off.r_stats.Search.n_pb_prunes = 0);
  (* (c). Both proofs, because the emission path must be unaffected by which propagator
     set was running. *)
  check_verified "c: the proof with learned-PB propagation ON verifies" on;
  check_verified "c: the proof with it OFF verifies" off;
  cleanup on;
  cleanup off

(* ---------------------------------------------------------------------------
   (e) THE BREAK for (c), and it is the only oracle a wrong slack rule has.

   [config.break_pb_degree] registers the learned row's runtime instance with a degree ONE
   HIGHER than the row [Pb_analysis.introduce] put on the page. The instance then enforces
   a constraint the proof does not state, so the prunings it makes are no longer reverse
   unit propagation against it.

   Note what does NOT change: the ANSWER. An over-strong propagator on an unsatisfiable
   model still returns UNSAT, and every counter in [Search.stats] is still a plausible
   number. A lane that checked the answer, or the counters, or merely that the solver did
   not crash, would be green on a build whose every learned pruning is unjustified. Only
   the checker can see it, which is why this lane exists and why it asserts the WORDING
   of the rejection rather than an exit status: an exit status cannot tell a JUDGEMENT
   from a parse error, and M2-T14 found four lanes green because a malformed artefact was
   refused on the grammar.

   The claim here is specifically "a line failed reverse unit propagation", and that is
   the wording asserted. It is the right strength for this lane because the honest
   control immediately below emits the SAME proof shape from the SAME code path and is
   ACCEPTED -- so a rejection for any other reason would have to be one this pipeline
   does not otherwise produce. *)
let test_break_degree () =
  print_endline "\n-- M2-L13 (e): the break -- a propagator stronger than its own row";
  let honest = run php_src in
  check_verified "e: CONTROL -- the honest build's proof is ACCEPTED" honest;
  cleanup honest;
  let broken =
    run ~config:{ Search.default_config with break_pb_degree = true } php_src
  in
  (match veripb broken with
  | None -> ()
  | Some (ok, out) ->
      check
        "e: BREAK -- with the instance one degree stronger than its row, veripb REJECTS"
        (not ok);
      check
        "e: ...and it rejects on the JUDGEMENT, saying `reverse unit propagation`, not \
         on the grammar"
        ((not ok) && contains ~needle:"reverse unit propagation" out);
      if ok then
        Printf.printf
          "     THE BREAK DID NOT FIRE. A propagator enforcing a constraint stronger \
           than the row on the page emitted a proof this checker accepts, which is a \
           finding about the lane or about the checker and must not be absorbed.\n"
      else if not (contains ~needle:"reverse unit propagation" out) then
        Printf.printf "     checker said: %s\n" (String.trim out));
  cleanup broken

(* ---------------------------------------------------------------------------
   [Clause] is the degree-1 case, structurally -- the D-0044 claim made checkable

   lib/core/prop/clause.ml has no propagation loop of its own any more: its [t] is
   [Pb.t], its constructors build one at degree 1 with unit coefficients, and its
   [propagate] IS [Pb.propagate]. That is asserted here rather than left to the module
   header, because the header is the thing a later change would forget to update. *)
let test_clause_is_degree_one () =
  print_endline "\n-- M2-L13: Clause is the degree-1 case, and it is the same code";
  let boxes = [ ("p", (0, 1)); ("q", (0, 1)) ] in
  let decl = decl_of boxes in
  let s = store_of boxes in
  let cl = Option.get (Clause.of_lits s ~decl [ Lit.ge "p" 1; Lit.ge "q" 1 ]) in
  check_eq "the clause built by Clause.of_lits has degree 1" (Pb.degree cl) 1;
  check "...and every coefficient 1" (List.for_all (fun c -> c = 1) (Pb.coeffs cl));
  check_eq "...and its width is the literal count" (Pb.width cl) 2;
  (* And the propagators are literally the same function. *)
  check "Clause.propagate IS Pb.propagate" (Clause.propagate == Pb.propagate);
  (* The Boolean entry still checks its [0,1] precondition, which is what DOMAIN rests
     on for [Clause.Bool_clause]. *)
  let wide = store_of [ ("x", (0, 5)) ] in
  let refused =
    try
      ignore (Clause.make wide [ (Var.of_int 0, true) ]);
      false
    with Invalid_argument _ -> true
  in
  check "Clause.make still refuses a non-Boolean, which is what DOMAIN rests on" refused

(* ---------------------------------------------------------------------------
   Retention: more citations, and the soft cap still refuses to evict a cited row

   M2-L12 made the cap SOFT -- a cited constraint is refused eviction and the refusal is
   counted -- and M2-L13 creates more citations, one per registered PB row on top of one
   per registered clause. The coupling is the same one D-0051's "what would reverse this"
   section names: a trace line from a registered instance is RUP only while the learned
   constraint is on the page.

   Checked on a real solve under a TIGHT fifo cap, which is the configuration that makes
   the guard do something: the policy wants to evict and is refused. *)
let test_retention_citations () =
  print_endline "\n-- M2-L13: retention -- the extra citations are honoured";
  let cfg =
    { Search.default_config with retention = Baguette_core.Retention.fifo ~cap:1 }
  in
  let r = run ~config:cfg php_src in
  let db = Search.stats_db r.r_stats in
  check "retention: the run registered learned PB instances"
    (r.r_stats.Search.n_pb_instances > 0);
  check "retention: ...and cited at least as many constraints as it registered"
    (Baguette_core.Retention.n_cited db
    >= r.r_stats.Search.n_pb_instances + r.r_stats.Search.n_clause_instances);
  check "retention: a tight cap really did try to evict"
    (Baguette_core.Retention.n_added db > 1);
  (* The one that would catch a wrongly evicted citation: a [rup] citing a constraint
     the policy retired reaches the checker as "Trying to access constraint with ID n
     that has already been deleted", a long way from the eviction. *)
  check_verified "retention: the proof under fifo:1 verifies" r;
  cleanup r

let () =
  test_row_beats_clause ();
  test_order_literal_scene ();
  test_ladder_effective ();
  test_declared_level ();
  test_clause_is_degree_one ();
  test_php_scene ();
  test_break_degree ();
  test_retention_citations ();
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "\nM2-L13 PB-propagator unit tests passed"
