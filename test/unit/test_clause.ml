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
   the search branch a DIFFERENT variable at successive levels. The order is legal by
   [Search.branch]'s only requirement (the split lies in [lo, hi)) and it is used here
   for the reason test_random.ml's [random_order] exists: to reach a tree shape the
   normative order does not build.

   TWO THINGS THIS COMMENT USED TO SAY ARE NO LONGER TRUE, and both were re-measured on
   2026-09-18 rather than reasoned about:

     - it said "every scene in test/models/ re-branches the same variable down a spine".
       M2-L14's five combinatorial models (php_*, colour_unsat) are declared entirely
       over 0..1, so the split `x <= 0` against `x >= 1` leaves both children singletons
       and first-fail can only pick an unfixed variable next. They branch a different
       variable at every level by construction.
     - it said "[glob-prune] is 0 over all 39 models". The suite is 44, and under the
       normative order [glob-prune] is 0 on all 44 as of main 0e265f1 -- but NOT in this
       build: M2-L13 gives the learned PB row a runtime consumer, the tree shape changes,
       and php_unsat then prunes 1 and php_wide_unsat 6 from learned UNITS that main's
       search never derived at all (main learns 0 globals on either model). So M2-L12's
       step 1 started paying because M2-L13 changed the search, which is worth knowing
       before anyone reads a green check here as "units never fire under the normative
       order". *)
let rev_order store cands =
  let best = ref cands.(0) in
  Array.iter (fun v -> if Var.to_int v > Var.to_int !best then best := v) cands;
  Search.Split
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
   moves a bound -- one of exactly two of the then-39 models that did (the other is
   bool_reif_unsat.fzn), measured by probing all 39 under this order. That probe has not
   been re-run over M2-L14's five additions, so "exactly two" is a figure about the 39
   and is not claimed about the 44. *)
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
   is. When M2-L12 wrote this, [glob-prune] was ZERO on all 39 models under SPEC 3.4's
   normative first-fail/indomain_min order: that order re-branched the same variable down
   a spine, so a unit 1UIP clause was always exactly the sibling branch the search took
   next and was always already in force by the time it was applied. A unit can only move
   a bound where the search LEAVES the level its variable was branched at and opens a
   fresh node above it, which needs successive levels to branch DIFFERENT variables.
   [rev_order] builds such a tree.

   RE-MEASURED 2026-09-18, on the 44-model suite and in THIS build, because two things
   moved under that paragraph. M2-L14's php_* and colour_unsat are declared over 0..1 and
   so branch a different variable at every level anyway; and M2-L13 gives the learned PB
   row a runtime consumer, which changes the tree enough that php_unsat and
   php_wide_unsat now derive learned UNITS (2 and 4) and prune from them (1 and 6) where
   main 0e265f1 derives none at all. So the zero above is a fact about the pre-M2-L14
   suite, not a law about the normative order.

   What the section still asserts is unchanged: that the machinery works on a scene built
   to exercise it, not that the suite gets faster. The node counts are asserted to be
   EQUAL on purpose -- see the last check. *)
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
  (* MEASURED AND PINNED, not hoped for. On THIS scene the pruning happens at a node the
     search was going to refute anyway, so the tree is the same size, and this check is
     that result written down.

     The generalisation it used to carry -- "over all 39 models under both orders the
     node counts are identical with step 1 on and off" -- IS SPENT, and spending it is
     the point of M2-L13 and M2-L14 rather than a regression. Swept over the 44 models on
     2026-09-18 in this build, [propagate_learned] on versus off is 479 nodes against
     2265 -- php_wide_unsat 77 against 1439, and even the old 39 subtotal 179 against
     231, which was the number M2-L12 pinned as immovable. The equality below is
     therefore a claim about this scene and the M2-L12 step-1 mechanism on it, and it is
     kept precisely because it is the tripwire: the day a change makes THIS tree smaller
     it reddens here and is noticed rather than absorbed. *)
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
  (* M2-L12 step 3: the CAP IS SOFT. A policy that names a cited constraint has its
     choice refused by [reduce] -- counted, not raised -- so BAGUETTE_RETENTION=lbd:0
     stays runnable with propagation on instead of aborting the solver. That distinction
     is the whole of why the filter is in [reduce] and not left to [retire]'s guard:
     [Cited] is a FAULT (a caller deleting something it should have known was in use),
     an unmeetable cap is a POLICY OUTCOME. *)
  let db2 = Retention.create ~policy:(Retention.lbd ~cap:0) () in
  let cid2 = Learned.introduce ctx row ~origin:"M2-L12 test (d) soft cap" in
  ignore (Retention.add db2 ~cid:cid2 ~row ~lbd:2 ~origin:"M2-L12 test (d) soft cap");
  Retention.cite db2 ~cid:cid2 ~by:"the learned unit x_ge_1 (M2-L12)";
  let evicted = Retention.reduce db2 ctx in
  check "M2-L12 step 3: an lbd:0 cap does NOT evict a cited constraint"
    (evicted = [] && Retention.size db2 = 1 && Retention.n_pinned db2 = 1);
  (* The control: the same policy on the same database with no citation evicts it. *)
  Retention.release_all db2;
  check "M2-L12 step 3 control: uncited, the same cap DOES evict it"
    (Retention.reduce db2 ctx = [ cid2 ] && Retention.size db2 = 0);
  close_out oc;
  (try Sys.remove pbp with _ -> ());
  try Sys.rmdir dir with _ -> ()

(* ---------------------------------------------------------------------------
   M11-complexity-T3 (D-0142, D-0140's E2 (a)): one walk per learned-clause run

   A learned clause's run used to be [Pb.propagate] (whose [Pb.quiet] walks the clause)
   followed by [rewatch], whose [best] walked it again once per watch to replace. Now
   [Pb.quiet] records the first two non-false literals and [rewatch_quiet] chooses the
   watches from them. The claim is that nothing observable moves: [Pb.quiet] answers as
   the list walk it replaced, and a run leaves the same trail, the same boxes and the SAME
   TWO WATCHES as [Pb.propagate] followed by [rewatch] (the watches decide every later
   wake, so they are part of what must not move).

   Random clauses over two Booleans and two small integers (both polarities, rungs of one
   variable, repeats), passed through [Learn.minimise] as every registered learned clause
   is (one literal per (variable, polarity), [Learned_clause.make]'s precondition), with
   random narrowed boxes and random starting watches,
   each run twice from the same state: once through [Learned_clause.propagate], once
   through the old composition. *)
let old_quiet store (t : Clause.t) =
  let module Pb = Baguette_core.Pb in
  t.Pb.degree = 1
  &&
  let free (tm : Pb.term) = Pb.status store tm.a <> Pb.Unsat_lit in
  let rec other xi = function
    | [] -> false
    | (tm : Pb.term) :: rest -> (Var.to_int tm.a.x <> xi && free tm) || other xi rest
  in
  let rec first = function
    | [] -> false
    | (tm : Pb.term) :: rest ->
        if free tm then other (Var.to_int tm.a.x) rest else first rest
  in
  first t.Pb.terms

let test_one_walk () =
  let module Pb = Baguette_core.Pb in
  let module LC = Clause.Learned_clause in
  let bounds = [ ("p", 0, 1); ("q", 0, 1); ("x", 0, 4); ("y", 0, 3) ] in
  let rng = Random.State.make [| 0x0142; 2 |] in
  let trials = 4000 in
  let quiet_same = ref 0 and run_same = ref 0 and n_quiet = ref 0 and moved = ref 0 in
  let first_diff = ref None in
  let observe store (lc : LC.t) r =
    let out =
      match r with
      | exception e -> `Raised (Printexc.to_string e)
      | Propagator.Fixpoint -> `Fix
      | Propagator.Conflict c ->
          `Conflict (Baguette_core.Reason.to_string c.Store.c_reason)
    in
    let trail =
      List.init (Store.trail_length store) (fun i ->
          let e = Store.trail_entry store i in
          ( Var.to_int e.Store.var,
            Domain.lo e.Store.now,
            Domain.hi e.Store.now,
            Baguette_core.Reason.to_string e.Store.reason ))
    in
    (out, trail, lc.LC.w1, lc.LC.w2)
  in
  for trial = 1 to trials do
    let n = 2 + Random.State.int rng 7 in
    let lits =
      Baguette_core.Learn.minimise
        (List.init n (fun _ ->
             let nm, lo, hi = List.nth bounds (Random.State.int rng 4) in
             let k = lo + 1 + Random.State.int rng (hi - lo) in
             if Random.State.bool rng then Lit.ge nm k else Lit.le nm (k - 1)))
    in
    let narrowed =
      List.map
        (fun (nm, lo, hi) ->
          let lo' = lo + Random.State.int rng (hi - lo + 1) in
          let hi' = lo' + Random.State.int rng (hi - lo' + 1) in
          (nm, lo', hi'))
        bounds
    in
    let s_new = mk_store narrowed and s_old = mk_store narrowed in
    match Clause.of_lits s_new ~decl:(decl_of bounds) lits with
    | None -> failwith "of_lits refused an order-literal clause"
    | Some pb ->
        let w = Pb.width pb in
        let w1 = Random.State.int rng w and w2 = Random.State.int rng w in
        let lc_new = LC.make pb and lc_old = LC.make pb in
        lc_new.LC.w1 <- w1;
        lc_new.LC.w2 <- w2;
        lc_old.LC.w1 <- w1;
        lc_old.LC.w2 <- w2;
        let q_old = old_quiet s_new pb in
        if Pb.quiet s_new pb = q_old then incr quiet_same;
        if q_old then incr n_quiet;
        let got = observe s_new lc_new (LC.propagate lc_new s_new) in
        let want =
          observe s_old lc_old
            (let r = Pb.propagate pb s_old in
             LC.rewatch s_old lc_old;
             r)
        in
        if got = want then incr run_same
        else if !first_diff = None then first_diff := Some trial;
        if q_old && (lc_new.LC.w1 <> w1 || lc_new.LC.w2 <> w2) then incr moved
  done;
  check
    (Printf.sprintf
       "E2a: %d random clauses, Pb.quiet answers as the list walk it replaced" trials)
    (!quiet_same = trials);
  check
    (Printf.sprintf
       "E2a: ...and a learned-clause run leaves the same outcome, trail and two watches \
        as Pb.propagate + rewatch (first difference: %s)"
       (match !first_diff with None -> "none" | Some i -> string_of_int i))
    (!run_same = trials);
  check
    (Printf.sprintf "E2a: ...%d of the runs are quiet (> 1000)" !n_quiet)
    (!n_quiet > 1000);
  check
    (Printf.sprintf
       "E2a: ...and %d quiet runs MOVE a watch (> 300), the case the scan answers" !moved)
    (!moved > 300)

let () =
  test_declared_levels ();
  test_bool_face_rejects_non_bool ();
  test_hole_is_not_a_tautology ();
  test_hole_is_not_a_tautology_control ();
  test_of_lits_declines ();
  test_unit_prunes ();
  test_clause_instance ();
  test_citation_guard ();
  test_one_walk ();
  if !failures > 0 then (
    Printf.printf "\n%d check(s) FAILED\n" !failures;
    exit 1)
