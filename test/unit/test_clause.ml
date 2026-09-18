(* Unit tests for M2-L12: making a learned constraint propagate.

   Two halves, because the row has two steps and they share no mechanism:

     - [Clause], the widened propagator (D-0052): a clause over general ORDER LITERALS,
       declaring BOUNDS, with [Clause.Bool_clause] still declaring DOMAIN because its
       [0, 1] restriction makes that true. Its Boolean face is tested at length in
       test_prop.ml and is not repeated here; what is here is what the widening added.
     - the search-level wiring: a learned unit as a global bound tightening applied at
       every node, a wider learned clause as a registered engine instance, and the
       CITATION that couples both to lib/core/retention.ml.

   Every search scene is driven through the real front end ([Builder] -> [Compile] ->
   [Search]) and every proof a scene emits is put in front of veripb, because a test that
   solves a model and does not check the proof is half a test. A missing checker is a
   FAILURE here, never a skip.

   Domains are single digits throughout (D-0028: the order encoding is width-proportional
   and a wide domain is a proof that dwarfs the suite). *)

module F = Baguette_flatzinc
module Compile = F.Compile
module Store = Baguette_core.Store
module Domain = Baguette_core.Domain
module Var = Baguette_core.Var
module Clause = Baguette_core.Clause
module Propagator = Baguette_core.Propagator
module Search = Baguette_core.Search
module Justify = Baguette_core.Justify
module Retention = Baguette_core.Retention
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

let read_file f =
  let ic = open_in_bin f in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let mk_store bounds =
  let names = Array.of_list (List.map (fun (n, _, _) -> n) bounds) in
  let domains = Array.of_list (List.map (fun (_, lo, hi) -> Domain.make lo hi) bounds) in
  Store.create ~names ~domains

let var i = Var.of_int i

(* The declared bounds an [of_lits] caller has to supply. In the solver they come from
   [Learned.decl_of_encoding], i.e. from the ENCODING and never from the store -- see
   [Clause.of_lits]'s comment. Here the two agree because nothing has narrowed yet, which
   is exactly the condition that makes a hand-built scene safe. *)
let decl_of bounds name =
  List.find_map (fun (n, lo, hi) -> if n = name then Some (lo, hi) else None) bounds

(* ---------------------------------------------------------------------------
   (e) The declared consistency levels, and each one's precondition

   SPEC 3.2 makes the declared level the bound on what an explanation may claim, so a
   module that declared DOMAIN and delivered BOUNDS would be claiming more than it
   delivers -- and D-0052 names that as the honest counter-argument to its own verdict.
   The three declarations are asserted here, and the one that needs a precondition has it
   checked below in [test_bool_face_rejects_non_bool]. *)
let test_declared_levels () =
  check "M2-L12 (e): the widened Clause declares BOUNDS"
    (Clause.consistency = Propagator.Bounds);
  check "M2-L12 (e): Clause.Bool_clause still declares DOMAIN"
    (Clause.Bool_clause.consistency = Propagator.Domain);
  check "M2-L12 (e): a learned clause instance declares BOUNDS"
    (Clause.Learned_clause.consistency = Propagator.Bounds);
  (* The four builtin faces are the same Boolean restriction under other names. *)
  check "M2-L12 (e): the array_bool_* / bool_eq / bool_not faces declare DOMAIN"
    (Clause.Array_bool_or.consistency = Propagator.Domain
    && Clause.Array_bool_and.consistency = Propagator.Domain
    && Clause.Bool_eq.consistency = Propagator.Domain
    && Clause.Bool_not.consistency = Propagator.Domain)

(* DOMAIN is true of [Clause.Bool_clause] only because [make] refuses anything that is
   not the order encoding on [0, 1]. Without that refusal the declaration would be a
   claim about arbitrary integers, which is precisely what BOUNDS exists for. *)
let test_bool_face_rejects_non_bool () =
  let store = mk_store [ ("x", 0, 5) ] in
  let refused =
    try
      ignore (Clause.make store [ (var 0, true) ]);
      false
    with Invalid_argument _ -> true
  in
  check
    "M2-L12 (e): Clause.make still refuses a non-Boolean, which is what DOMAIN rests on"
    refused

(* ---------------------------------------------------------------------------
   (b) The opposite-direction pair is a HOLE, not a tautology

   This is D-0052's sharpest correction to the module it widened. The pre-M2-L12 comment
   at what was bool_clause.ml:120-128 said a variable occurring at both polarities leaves
   a TAUTOLOGY, so "the propagator correctly never fires". True for `b \/ ~b`. For
   `x >= 3 \/ x <= 1` it is false twice over, and both halves are asserted here:

     - it CONFLICTS when the variable is driven into the hole;
     - it PRUNES when one side becomes false and the other is still open.

   A lane asserting the old reading -- "never fires" -- would redden on both. That is the
   break this section is, and it is performed rather than described: [test_hole_is_not_a_
   tautology_control] below runs the SAME clause shape over a Boolean, where the old
   reading IS right, so a bug that made the propagator fire on everything cannot pass by
   making the two assertions above pass. *)
let hole_clause store bounds =
  (* x >= 3 \/ x <= 1, as the proof literals a learned clause would carry. *)
  match Clause.of_lits store ~decl:(decl_of bounds) [ Lit.ge "x" 3; Lit.le "x" 1 ] with
  | Some p -> p
  | None -> failwith "Clause.of_lits refused an order-literal clause"

let test_hole_is_not_a_tautology () =
  let bounds = [ ("x", 0, 5) ] in
  (* Two open literals: nothing is inferred, and -- this is the BOUNDS declaration being
     honest rather than a weakness admitted in prose -- the hole at 2 is NOT punched. A
     DOMAIN-consistent clause propagator would have removed it; D-0052 says chasing it
     would need [Store.remove_with_facts] and told this row not to. *)
  let store = mk_store bounds in
  let p = hole_clause store bounds in
  (match Clause.propagate p store with
  | Propagator.Fixpoint ->
      let d = Store.get store (var 0) in
      check "M2-L12 (b): two open literals infer nothing"
        (Domain.lo d = 0 && Domain.hi d = 5);
      check "M2-L12 (b)/(e): BOUNDS is honest -- the interior hole at 2 is NOT removed"
        (Domain.mem d 2)
  | Propagator.Conflict _ -> check "M2-L12 (b): two open literals infer nothing" false);
  (* The PRUNING half. x in 2..5 falsifies `x <= 1`, so `x >= 3` is the unit and the
     bound MOVES. A tautology never licenses this. *)
  let store = mk_store bounds in
  let p = hole_clause store bounds in
  Store.set_lo store (var 0) 2
    (Baguette_core.Reason.because ~concludes:None []
       (Baguette_core.Explanation.clause []))
  |> ignore;
  (match Clause.propagate p store with
  | Propagator.Fixpoint ->
      check "M2-L12 (b): x<=1 falsified leaves x>=3 the unit, and lo MOVES to 3"
        (Domain.lo (Store.get store (var 0)) = 3)
  | Propagator.Conflict _ ->
      check "M2-L12 (b): x<=1 falsified leaves x>=3 the unit, and lo MOVES to 3" false);
  (* The CONFLICT half. x fixed at 2 is in the hole: both literals are false, so the
     clause is violated. The old tautology reading would have declared a fixpoint and let
     a violating assignment through, which is an I-P3 failure. *)
  let store = mk_store bounds in
  let p = hole_clause store bounds in
  let r =
    Baguette_core.Reason.because ~concludes:None [] (Baguette_core.Explanation.clause [])
  in
  ignore (Store.set_lo store (var 0) 2 r);
  ignore (Store.set_hi store (var 0) 2 r);
  match Clause.propagate p store with
  | Propagator.Conflict _ ->
      check "M2-L12 (b): x driven into the hole at 2 CONFLICTS -- not a tautology" true
  | Propagator.Fixpoint ->
      check "M2-L12 (b): x driven into the hole at 2 CONFLICTS -- not a tautology" false

(* The control. Over a `var bool` the same shape -- one variable at both polarities -- IS
   a tautology, and the propagator must stay silent whatever the store says. Without this
   the two assertions above would also pass for a propagator that fired indiscriminately.

   `b >= 1 \/ b <= 0` over [0, 1] is `b \/ ~b`. Fix b either way and nothing happens. *)
let test_hole_is_not_a_tautology_control () =
  let bounds = [ ("b", 0, 1) ] in
  List.iter
    (fun v ->
      let store = mk_store bounds in
      let p =
        match
          Clause.of_lits store ~decl:(decl_of bounds)
            [ Lit.bool_true "b"; Lit.bool_false "b" ]
        with
        | Some p -> p
        | None -> failwith "of_lits refused a Boolean clause"
      in
      let r =
        Baguette_core.Reason.because ~concludes:None []
          (Baguette_core.Explanation.clause [])
      in
      ignore (Store.set_lo store (var 0) v r);
      ignore (Store.set_hi store (var 0) v r);
      match Clause.propagate p store with
      | Propagator.Fixpoint ->
          check
            (Printf.sprintf
               "M2-L12 (b) control: b \\/ ~b with b = %d really IS a tautology -- silent"
               v)
            true
      | Propagator.Conflict _ ->
          check
            (Printf.sprintf
               "M2-L12 (b) control: b \\/ ~b with b = %d really IS a tautology -- silent"
               v)
            false)
    [ 0; 1 ]

(* [of_lits] declines what it cannot move, and the decline is a case that really arises:
   a 1UIP cut can carry a direct-encoding literal ([Learn.slot] returns [None] for one).
   A positive [Eq] would have to fix a variable and a negative one to punch an interior
   hole -- [Store.remove_with_facts], which I-X10 records [Ne] is the sole caller of in
   lib/ and which D-0052 told this row not to reach for. *)
let test_of_lits_declines () =
  let bounds = [ ("x", 0, 5) ] in
  let store = mk_store bounds in
  check "M2-L12: of_lits declines a direct-encoding literal"
    (Clause.of_lits store ~decl:(decl_of bounds) [ Lit.ge "x" 3; Lit.ne "x" 2 ] = None);
  check "M2-L12: of_lits declines a variable the encoding does not declare"
    (Clause.of_lits store ~decl:(decl_of bounds) [ Lit.ge "nosuch" 1 ] = None);
  (* A width-1 clause is a clause: nothing here special-cases it, which is what makes the
     search's separate treatment of a unit a CHOICE about cost rather than a necessity. *)
  match Clause.of_lits store ~decl:(decl_of bounds) [ Lit.ge "x" 3 ] with
  | None -> check "M2-L12: of_lits accepts a unit order literal" false
  | Some p ->
      check "M2-L12: of_lits accepts a unit order literal" (Clause.width p = 1);
      ignore (Clause.propagate p store);
      check "M2-L12: a unit clause instance moves the bound on its own"
        (Domain.lo (Store.get store (var 0)) = 3)

(* ---------------------------------------------------------------------------
   The search scenes

   [rev_order] is the branching order these scenes need and it is not a fuzzer knob: it
   picks the LAST unfixed variable rather than the smallest domain, which is what makes
   the search branch a DIFFERENT variable at successive levels. Under SPEC 3.4's
   first-fail/indomain_min every scene in test/models/ re-branches the same variable down
   a spine, and a learned unit is then always exactly the sibling branch the search takes
   next -- measured, and it is why [glob-prune] is 0 over all 39 models. The order is
   legal by [Search.branch]'s only requirement (the split lies in [lo, hi)) and it is
   used here for the reason test_random.ml's [random_order] exists: to reach a tree shape
   the normative order does not build. *)
let rev_order store cands =
  let best = ref cands.(0) in
  Array.iter (fun v -> if Var.to_int v > Var.to_int !best then best := v) cands;
  {
    Search.d_var = !best;
    d_split = Domain.lo (Store.get store !best);
    d_high_first = false;
  }

type run = {
  r_outcome : Search.outcome;
  r_stats : Search.stats;
  r_dir : string;
  r_opb : string;
  r_pbp : string;
}

(* Solve one model into a scratch directory. The audit is ON: I-X2's live set must be
   empty at [conclusion], and a learned constraint with a runtime consumer is the first
   object in this solver whose lifetime is coupled to a propagator, so it is exactly what
   leaks if [Search.solve] forgets to release and retire it. *)
let run ?(config = Search.default_config) ?order src =
  let m = F.Builder.of_string ~file:"test" src in
  let c = Compile.compile m in
  let dir = Filename.temp_file "baguette_clause" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  let opb = Filename.concat dir "m.opb" and pbp = Filename.concat dir "m.pbp" in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "M2-L12" ] c.Compile.encoding oc;
  close_out oc;
  let oc = open_out pbp in
  let writer = Writer.create ~audit:true oc in
  Encoding.start_proof c.Compile.encoding writer;
  let ctx = Justify.create ~writer ~encoding:c.Compile.encoding in
  let stats = Search.stats_create () in
  let outcome =
    Search.solve ~engine:c.Compile.engine ~store:c.Compile.store ~ctx
      ~check:(fun _ -> true)
      ~stats ~config ?order ()
  in
  close_out oc;
  { r_outcome = outcome; r_stats = stats; r_dir = dir; r_opb = opb; r_pbp = pbp }

let cleanup r =
  List.iter (fun f -> try Sys.remove f with _ -> ()) [ r.r_opb; r.r_pbp ];
  try Sys.rmdir r.r_dir with _ -> ()

(* lib/proof/checker.ml, shared with scripts/checker.sh. [None] is a FAILURE at every
   call site below, never a skip. *)
let veripb r =
  match Baguette_proof.Checker.find () with
  | None ->
      check "M2-L12 (c): veripb 3.0.2 is on PATH -- a missing checker is a failure" false;
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

(* test/models/backjump_bool_unsat.fzn, verbatim: the Boolean reification chain, with
   two integer spectators in front of it so that the branching order has something to
   choose between. Under [rev_order] this is the scene in which a learned UNIT actually
   moves a bound -- one of exactly two in test/models/ that do (the other is
   bool_reif_unsat.fzn), measured by probing all 39 under this order. *)
let bool_src =
  "var 0..1: p :: output_var;\n\
   var 0..1: q :: output_var;\n\
   var bool: a :: output_var;\n\
   var bool: b :: output_var;\n\
   var bool: c :: output_var;\n\
   var bool: d :: output_var;\n\
   constraint array_bool_or([a, b], c);\n\
   constraint array_bool_and([a, b], d);\n\
   constraint bool_eq(c, d);\n\
   constraint bool_clause([a, b], []);\n\
   constraint bool_clause([], [a, b]);\n\
   solve satisfy;\n"

(* test/models/backjump_deep_unsat.fzn, verbatim: `x != y` and `x = y` behind three
   spectators. Its learned clauses are two units and two of width 3, so it is the scene
   for step 2 -- the widths are not arranged here, they are what the solver derives. *)
let deep_src =
  "var 0..1: p :: output_var;\n\
   var 0..1: q :: output_var;\n\
   var 0..1: r :: output_var;\n\
   var 0..3: x :: output_var;\n\
   var 0..3: y :: output_var;\n\
   constraint int_ne(x, y);\n\
   constraint int_eq(x, y);\n\
   solve satisfy;\n"

(* ---------------------------------------------------------------------------
   (a) A learned unit actually prunes -- and does not, without step 1

   THE MEASURED CONTEXT, because a green check here would otherwise read as more than it
   is. Under SPEC 3.4's normative first-fail/indomain_min order, [glob-prune] is ZERO on
   all 39 models: that order re-branches the same variable down a spine, so a unit 1UIP
   clause is always exactly the sibling branch the search takes next and is always
   already in force by the time it is applied. A unit can only move a bound where the
   search LEAVES the level its variable was branched at and opens a fresh node above it,
   which needs successive levels to branch DIFFERENT variables. [rev_order] builds such a
   tree; the normative order does not.

   So this section asserts that the machinery works, not that the suite gets faster. The
   node counts are asserted to be EQUAL on purpose -- see the last check. *)
let test_unit_prunes () =
  let on = run ~order:rev_order bool_src in
  let off = run ~config:Search.no_propagate_learned ~order:rev_order bool_src in
  check "M2-L12 (a): the scene learns at least one unit"
    (List.length (Search.stats_globals on.r_stats) > 0);
  check "M2-L12 (a): with step 1 ON a learned unit MOVES a bound"
    (on.r_stats.Search.n_global_prunes > 0);
  (* The break, and it is a control rather than a mutation: with
     [propagate_learned = false] the same search learns the same clauses and applies none
     of them. A build in which the counter moved anyway would be one in which something
     other than step 1 was doing the pruning. *)
  check "M2-L12 (a) break: with step 1 OFF nothing is applied and nothing prunes"
    (Search.stats_globals off.r_stats = []
    && off.r_stats.Search.n_global_prunes = 0
    && off.r_stats.Search.n_clause_instances = 0);
  check "M2-L12 (a): the same clauses are still LEARNED with step 1 off"
    (off.r_stats.Search.n_learned = on.r_stats.Search.n_learned
    && off.r_stats.Search.n_learned > 0);
  check "M2-L12 (a): both builds agree on the answer"
    (match (on.r_outcome, off.r_outcome) with
    | Search.Unsat, Search.Unsat -> true
    | Search.Sat _, Search.Sat _ -> true
    | _ -> false);
  (* MEASURED AND PINNED, not hoped for. The pruning happens at a node the search was
     going to refute anyway, so the tree is the same size. Over all 39 models under both
     orders the node counts are identical with step 1 on and off; this check is that
     result written down, so that the day a change makes the tree SMALLER it reddens here
     and is noticed rather than absorbed. *)
  check
    "M2-L12 (a): ...and the tree is the SAME SIZE -- step 1 prunes, it does not search \
     less"
    (on.r_stats.Search.nodes = off.r_stats.Search.nodes);
  check_verified "M2-L12 (a)/(c): the proof with step 1 ON verifies" on;
  check_verified "M2-L12 (a)/(c): the proof with step 1 OFF verifies" off;
  cleanup on;
  cleanup off

(* ---------------------------------------------------------------------------
   (a2) A multi-literal learned clause is registered and propagates *)
let test_clause_instance () =
  let on = run ~order:rev_order deep_src in
  let off = run ~config:Search.no_propagate_learned ~order:rev_order deep_src in
  check "M2-L12 step 2: at least one multi-literal learned clause became an instance"
    (on.r_stats.Search.n_clause_instances > 0);
  check "M2-L12 step 2 break: with propagate_learned OFF none is registered"
    (off.r_stats.Search.n_clause_instances = 0);
  check "M2-L12 step 2: no learned clause was silently dropped"
    (on.r_stats.Search.n_clause_declined = 0 && on.r_stats.Search.n_global_declined = 0);
  check "M2-L12 step 2: registering instances mid-search leaves the answer alone"
    (on.r_stats.Search.nodes = off.r_stats.Search.nodes);
  check_verified "M2-L12 (c): the proof of a search with registered instances verifies" on;
  check_verified "M2-L12 (c): ...and the control proof verifies too" off;
  cleanup on;
  cleanup off

(* ---------------------------------------------------------------------------
   (d) I-X3 and the liveness coupling

   D-0052's "new obligation": a trace line from a learned instance is RUP only while that
   learned constraint is LIVE. Before M2-L12 nothing propagated a learned constraint, so
   [Retention]'s policy and the propagator set were independent -- which is the
   independence D-0051's keep-all verdict was written on.

   Two lanes, and the second is what makes the first evidence:

     - OUR machinery catches it. A learned constraint with a consumer is cited, and
       retiring a cited constraint raises [Retention.Cited] naming what cites it.
     - the release is not a way round the guard: once the search is over the citation is
       dropped and the ordinary retirement goes through, with the double-delete and
       not-owned guards still on. *)
let test_citation_guard () =
  let r = run ~order:rev_order deep_src in
  check "M2-L12 (d): the search cited at least one learned constraint"
    (Retention.n_cited (Search.stats_db r.r_stats) > 0);
  check "M2-L12 (d): and the end-of-search sweep still emptied the database"
    (Retention.size (Search.stats_db r.r_stats) = 0);
  cleanup r;
  let off = run ~config:Search.no_propagate_learned ~order:rev_order deep_src in
  check "M2-L12 (d) control: with no consumer, nothing is cited at all"
    (Retention.n_cited (Search.stats_db off.r_stats) = 0);
  cleanup off;
  (* And the guard itself, on a database built here so the scene is exact. *)
  let m = F.Builder.of_string ~file:"test" deep_src in
  let c = Compile.compile m in
  let dir = Filename.temp_file "baguette_cite" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  let pbp = Filename.concat dir "m.pbp" in
  let oc = open_out pbp in
  let writer = Writer.create oc in
  Encoding.start_proof c.Compile.encoding writer;
  let ctx = Justify.create ~writer ~encoding:c.Compile.encoding in
  let db = Retention.create () in
  let row = Learned.of_clause [ Lit.ge "x" 1; Lit.le "y" 2 ] in
  let cid = Learned.introduce ctx row ~origin:"M2-L12 test (d)" in
  ignore (Retention.add db ~cid ~row ~lbd:2 ~origin:"M2-L12 test (d)");
  Retention.cite db ~cid ~by:"learned_clause instance #7 (M2-L12)";
  let caught =
    try
      Retention.retire db ctx ~why:"eviction" [ cid ];
      None
    with Retention.Cited msg -> Some msg
  in
  (match caught with
  | None ->
      check
        "M2-L12 (d): retiring a CITED learned constraint is refused by our own machinery"
        false
  | Some msg ->
      check
        "M2-L12 (d): retiring a CITED learned constraint is refused by our own machinery"
        true;
      check "M2-L12 (d): and the refusal names what cites it"
        (let needle = "learned_clause instance #7" in
         let n = String.length needle in
         let rec go i =
           i + n <= String.length msg && (String.sub msg i n = needle || go (i + 1))
         in
         go 0));
  (* Released, the same retirement goes through: [release_all] is what [Search.solve]'s
     end-of-search sweep does, and it is a statement about lifetime rather than a way
     round the guard. *)
  Retention.release_all db;
  let went_through =
    try
      Retention.retire db ctx ~why:"end of search" [ cid ];
      true
    with Retention.Cited _ -> false
  in
  check "M2-L12 (d): once released, the same retirement goes through" went_through;
  close_out oc;
  (try Sys.remove pbp with _ -> ());
  try Sys.rmdir dir with _ -> ()

let () =
  test_declared_levels ();
  test_bool_face_rejects_non_bool ();
  test_hole_is_not_a_tautology ();
  test_hole_is_not_a_tautology_control ();
  test_of_lits_declines ();
  test_unit_prunes ();
  test_clause_instance ();
  test_citation_guard ();
  if !failures > 0 then (
    Printf.printf "\n%d check(s) FAILED\n" !failures;
    exit 1)
