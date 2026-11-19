(* test_search_strategy.ml: the opt-in search strategies of M10-search-strategy --
   restarts and phase saving (T2), the activity order (T3). docs/DECISIONS.md D-0137.

   Two kinds of lane, and the second is the one that matters:

   - the POLICIES as pure state machines (lib/core/restart.ml, lib/core/phase.ml): the
     Luby sequence, when each schedule says a restart is due, the CLI spelling;
   - the SEARCH with them on, end to end through the real checker: a run that restarts
     in the middle still answers what the run without restarts answers, its proof is
     VERIFIED, every id it received is deleted (I-X2, audit on), M1-T36's node identity
     still holds with [restart_unexplored] in it, and the proof contains no rule kind the
     restart-free proof of the same model does not (D-0137 section 1: a restart is the
     backjump this solver already writes, and adds no rule). A SATISFIABLE model is among
     them on purpose: on an UNSAT one the database ends contradictory and a `rup` checked
     there proves less (D-0053, D-0066).

   Every model here declares domains of single digits (CLAUDE.md: no wide domain).

   M11-complexity-T4 (D-0152) adds a third kind: the per-node structures of search.ml
   that replaced a scan, each checked against the scan it replaced on random inputs. *)

module Encoding = Baguette_proof.Encoding
module Writer = Baguette_proof.Writer
module Var = Baguette_core.Var
module Search = Baguette_core.Search
module Justify = Baguette_core.Justify
module Restart = Baguette_core.Restart

let () = Mem_guard.install ()
let failures = ref 0

let check name cond =
  if cond then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s\n" name)

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

let contains hay needle =
  let hl = String.length hay and nl = String.length needle in
  let rec go i = i + nl <= hl && (String.sub hay i nl = needle || go (i + 1)) in
  go 0

(* ------------------------------------------------------------- the policies *)

let test_luby () =
  let got = List.init 15 (fun i -> Restart.luby (i + 1)) in
  check "Restart.luby: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8"
    (got = [ 1; 1; 2; 1; 1; 2; 4; 1; 1; 2; 1; 1; 2; 4; 8 ]);
  check "Restart.luby: luby(31) = 16, luby(32) = 1"
    (Restart.luby 31 = 16 && Restart.luby 32 = 1);
  check "Restart.luby: refuses index 0"
    (match Restart.luby 0 with _ -> false | exception Invalid_argument _ -> true)

(* Feed conflicts one at a time and record after how many each restart became due. *)
let run_schedule policy ~runs ~lbd =
  let t = Restart.create policy in
  List.init runs (fun _ ->
      let n = ref 0 in
      while
        Restart.on_conflict t ~lbd:(Some (lbd ()));
        incr n;
        (not (Restart.due t)) && !n < 100_000
      do
        ()
      done;
      Restart.on_restart t;
      !n)

let test_schedules () =
  check "Restart: luby:3 runs take 3 3 6 3 3 6 12 conflicts"
    (run_schedule (Restart.Luby 3) ~runs:7 ~lbd:(fun () -> 2) = [ 3; 3; 6; 3; 3; 6; 12 ]);
  check "Restart: geom:2:2 runs take 2 4 8 16 conflicts"
    (run_schedule (Restart.Geom (2, 2.0)) ~runs:4 ~lbd:(fun () -> 2) = [ 2; 4; 8; 16 ]);
  check "Restart: none is never due"
    (let t = Restart.create Restart.No_restarts in
     for _ = 1 to 1000 do
       Restart.on_conflict t ~lbd:(Some 5)
     done;
     not (Restart.due t));
  (* LBD: with constant LBDs the recent average equals the global one, and K < 1 then
     never fires; a burst of worse clauses after a good start fires as soon as the window
     is full of them. *)
  check "Restart: lbd never fires on a constant LBD stream (recent * K < global)"
    (let t = Restart.create (Restart.Lbd { window = 4; k = 0.8 }) in
     let fired = ref false in
     for _ = 1 to 200 do
       Restart.on_conflict t ~lbd:(Some 3);
       if Restart.due t then fired := true
     done;
     not !fired);
  check "Restart: lbd fires once the window holds clauses worse than the run's average"
    (let t = Restart.create (Restart.Lbd { window = 4; k = 0.8 }) in
     for _ = 1 to 100 do
       Restart.on_conflict t ~lbd:(Some 2)
     done;
     let before = Restart.due t in
     for _ = 1 to 4 do
       Restart.on_conflict t ~lbd:(Some 10)
     done;
     (not before) && Restart.due t);
  check "Restart: lbd needs a full window after a restart (the ring is cleared)"
    (let t = Restart.create (Restart.Lbd { window = 4; k = 0.8 }) in
     for _ = 1 to 100 do
       Restart.on_conflict t ~lbd:(Some 2)
     done;
     for _ = 1 to 4 do
       Restart.on_conflict t ~lbd:(Some 10)
     done;
     Restart.on_restart t;
     for _ = 1 to 3 do
       Restart.on_conflict t ~lbd:(Some 10)
     done;
     not (Restart.due t));
  (* The floor (D-0137 section 1): run k may not restart before luby(k+1) conflicts. At
     run 14 luby(15) = 8 > window 4, so a run that would fire at 4 waits until 8. *)
  check "Restart: lbd's Luby floor holds run 14 to luby(15) = 8 conflicts"
    (let t = Restart.create (Restart.Lbd { window = 4; k = 0.8 }) in
     for _ = 1 to 100 do
       Restart.on_conflict t ~lbd:(Some 1)
     done;
     for _ = 1 to 14 do
       Restart.on_restart t
     done;
     let at = ref 0 in
     let n = ref 0 in
     while !at = 0 && !n < 50 do
       Restart.on_conflict t ~lbd:(Some 50);
       incr n;
       if Restart.due t then at := !n
     done;
     !at = 8);
  check "Restart: stable switches mode only at a restart, after its phase budget"
    (let t = Restart.create (Restart.Stable 1) in
     for _ = 1 to Restart.stable_first_phase + 10 do
       Restart.on_conflict t ~lbd:(Some 3)
     done;
     let before = Restart.switches t in
     Restart.on_restart t;
     before = 0 && Restart.switches t = 1)

let test_of_string () =
  let ok s p = match Restart.of_string s with Ok q -> q = p | Error _ -> false in
  let bad s = match Restart.of_string s with Ok _ -> false | Error _ -> true in
  check "Restart.of_string: the defaults"
    (ok "none" Restart.No_restarts && ok "luby" (Restart.Luby 100)
    && ok "geom" (Restart.Geom (100, 1.5))
    && ok "lbd" (Restart.Lbd { window = 50; k = 0.8 })
    && ok "stable" (Restart.Stable 100));
  check "Restart.of_string: parameters"
    (ok "luby:7" (Restart.Luby 7)
    && ok "geom:10:2" (Restart.Geom (10, 2.0))
    && ok "lbd:20:0.7" (Restart.Lbd { window = 20; k = 0.7 }));
  check "Restart.of_string: refuses rather than defaulting"
    (bad "" && bad "lubyy" && bad "luby:0" && bad "luby:x" && bad "geom:10:0.5"
   && bad "lbd:0" && bad "luby:1:2");
  check "Restart: to_string round-trips"
    (List.for_all
       (fun p -> Restart.of_string (Restart.to_string p) = Ok p)
       [ Restart.No_restarts; Restart.Luby 3; Restart.Geom (5, 2.0); Restart.Stable 9 ])

(* ------------------------------------------------------- the search, end to end *)

(* n-queens over 0/1 cells: one per row and per column (int_lin_eq), at most one per
   diagonal (int_lin_le). Satisfiable for n = 6, and first-fail/min reaches its first
   solution through conflicts that LEARN (8 of them at n = 6, measured with the CLI), so a
   restart lands in the middle of a run that then answers SAT. The integer-variable
   n-queens over int_ne/int_lin_ne would not do: its conflicts learn nothing (the holes'
   Ne reasons decline 1UIP), and a conflict that learned nothing never restarts (D-0137
   section 1). With [~opt], the first row's column is a variable [c1] to minimise; 6-queens
   has no solution with a queen in a corner of row 1, so the optimum 2 is PROVED by
   conflicts. *)
let queens ?(opt = false) n =
  let b = Buffer.create 4096 in
  let add fmt = Printf.ksprintf (Buffer.add_string b) fmt in
  let ones k = String.concat "," (List.init k (fun _ -> "1")) in
  let row cells =
    String.concat "," (List.map (fun (i, j) -> Printf.sprintf "b%d%d" i j) cells)
  in
  for i = 1 to n do
    for j = 1 to n do
      add "var 0..1: b%d%d :: output_var;\n" i j
    done
  done;
  if opt then add "var 1..%d: c1 :: output_var;\n" n;
  for i = 1 to n do
    add "constraint int_lin_eq([%s],[%s],1);\n" (ones n)
      (row (List.init n (fun j -> (i, j + 1))))
  done;
  for j = 1 to n do
    add "constraint int_lin_eq([%s],[%s],1);\n" (ones n)
      (row (List.init n (fun i -> (i + 1, j))))
  done;
  let diag cells =
    if List.length cells > 1 then
      add "constraint int_lin_le([%s],[%s],1);\n" (ones (List.length cells)) (row cells)
  in
  for d = -(n - 2) to n - 2 do
    diag
      (List.filter_map
         (fun i -> if i - d >= 1 && i - d <= n then Some (i, i - d) else None)
         (List.init n (fun i -> i + 1)))
  done;
  for s = 3 to (2 * n) - 1 do
    diag
      (List.filter_map
         (fun i -> if s - i >= 1 && s - i <= n then Some (i, s - i) else None)
         (List.init n (fun i -> i + 1)))
  done;
  if opt then (
    add "constraint int_lin_eq([%s,-1],[%s,c1],0);\n"
      (String.concat "," (List.init n (fun j -> string_of_int (j + 1))))
      (row (List.init n (fun j -> (1, j + 1))));
    add "solve minimize c1;\n")
  else add "solve satisfy;\n";
  Buffer.contents b

(* 5 pigeons, 4 holes, 0/1 cells: unsatisfiable, and the refutation takes conflicts. *)
let pigeons =
  let b = Buffer.create 512 in
  for p = 1 to 5 do
    for h = 1 to 4 do
      Buffer.add_string b (Printf.sprintf "var 0..1: x%d%d :: output_var;\n" p h)
    done
  done;
  for p = 1 to 5 do
    Buffer.add_string b
      (Printf.sprintf "constraint int_lin_eq([1,1,1,1],[x%d1,x%d2,x%d3,x%d4],1);\n" p p p
         p)
  done;
  for h = 1 to 4 do
    Buffer.add_string b
      (Printf.sprintf "constraint int_lin_le([1,1,1,1,1],[x1%d,x2%d,x3%d,x4%d,x5%d],1);\n"
         h h h h h)
  done;
  Buffer.add_string b "solve satisfy;\n";
  Buffer.contents b

type run = {
  answer : string; (* "SAT", "UNSAT", or "OPT v" *)
  verdict : string;
  proof : string;
  restarts : int;
  kept : int; (* levels kept by restarts, summed: > 0 only for a partial restart *)
  live : int;
  consistent : bool;
}

let solve_with dir name src (config : Search.config) =
  let m = Baguette_flatzinc.Builder.of_string ~file:name src in
  let compiled = Baguette_flatzinc.Compile.compile m in
  let opb = Filename.concat dir (name ^ ".opb")
  and pbp = Filename.concat dir (name ^ ".pbp") in
  let encoding = compiled.Baguette_flatzinc.Compile.encoding in
  let oc = open_out opb in
  Encoding.write_opb encoding oc;
  close_out oc;
  let poc = open_out pbp in
  let writer = Writer.create ~audit:true poc in
  Encoding.start_proof encoding writer;
  let ctx = Justify.create ~writer ~encoding in
  let check asn =
    let values = Array.make (Baguette_flatzinc.Model.nvars m) 0 in
    List.iter (fun (v, x) -> values.(Var.to_int v) <- x) asn;
    Baguette_flatzinc.Model.check_assignment m values
  in
  let stats = Search.stats_create () in
  let engine = compiled.Baguette_flatzinc.Compile.engine
  and store = compiled.Baguette_flatzinc.Compile.store
  and order = compiled.Baguette_flatzinc.Compile.order in
  let answer, exhausted =
    match compiled.Baguette_flatzinc.Compile.objective with
    | None -> (
        match Search.solve ~engine ~store ~ctx ~check ~stats ~config ?order () with
        | Search.Sat _ -> ("SAT", false)
        | Search.Unsat -> ("UNSAT", true))
    | Some objective -> (
        match
          Search.optimise ~engine ~store ~ctx ~check ~stats ~config ~objective ?order
            ~on_solution:(fun _ -> ())
            ()
        with
        (* [exhausted:false]: an optimisation that reaches the objective's floor
           stops at that solution without closing the tree ([record_improving]'s
           [`Proved]), so only the bound half of M1-T36 is owed. *)
        | Search.Opt (_, v) -> (Printf.sprintf "OPT %d" v, false)
        | Search.Opt_unsat -> ("UNSAT", true))
  in
  let live = List.length (Writer.live_ids writer) in
  close_out poc;
  let verdict =
    match Baguette_proof.Checker.find () with
    | None -> "NO CHECKER"
    | Some vp ->
        let log = Filename.concat dir (name ^ ".log") in
        ignore
          (Sys.command
             (Printf.sprintf "%s %s %s > %s 2>&1" (Filename.quote vp) (Filename.quote opb)
                (Filename.quote pbp) (Filename.quote log)));
        let out = read_file log in
        if contains out "VERIFIED" then
          String.concat " "
            (List.filter (fun l -> contains l "VERIFIED") (String.split_on_char '\n' out))
        else "REJECTED: " ^ out
  in
  {
    answer;
    verdict;
    proof = read_file pbp;
    restarts = Search.stats_restarts stats;
    kept = stats.Search.restart_targets;
    live;
    consistent = Search.stats_consistent stats ~exhausted;
  }

(* The rule keywords a proof uses: the first word of every line that is not a comment. *)
let rule_kinds proof =
  String.split_on_char '\n' proof
  |> List.filter_map (fun l ->
         let l = String.trim l in
         if l = "" || l.[0] = '%' then None
         else
           (* strip an `@label ` prefix *)
           let l =
             if l.[0] = '@' then
               match String.index_opt l ' ' with
               | Some i -> String.sub l (i + 1) (String.length l - i - 1)
               | None -> l
             else l
           in
           match String.index_opt l ' ' with
           | Some i -> Some (String.sub l 0 i)
           | None -> Some l)
  |> List.sort_uniq compare

let test_restarting_search () =
  let dir = Filename.temp_file "baguette_m10" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  let cases =
    [ ("queens6", queens 6); ("pigeons54", pigeons); ("queens6opt", queens ~opt:true 6) ]
  in
  let policies =
    [
      ("luby:1", { Search.default_config with Search.restarts = Restart.Luby 1 });
      ( "geom:1:1.2",
        { Search.default_config with Search.restarts = Restart.Geom (1, 1.2) } );
      ( "lbd:2:1",
        {
          Search.default_config with
          Search.restarts = Restart.Lbd { window = 2; k = 1.0 };
        } );
      ( "luby:1+phase",
        {
          Search.default_config with
          Search.restarts = Restart.Luby 1;
          Search.phase_saving = true;
        } );
      ("phase", { Search.default_config with Search.phase_saving = true });
      (* M10-T3 *)
      ("activity", { Search.default_config with Search.search = Search.Activity_order });
      ( "activity+luby:1+phase",
        {
          Search.default_config with
          Search.search = Search.Activity_order;
          Search.restarts = Restart.Luby 1;
          Search.phase_saving = true;
        } );
      ( "alternate+luby:1",
        {
          Search.default_config with
          Search.search = Search.Alternate;
          Search.restarts = Restart.Luby 1;
        } );
      ( "activity+luby:1+reuse",
        {
          Search.default_config with
          Search.search = Search.Activity_order;
          Search.restarts = Restart.Luby 1;
          Search.reuse_trail = true;
        } );
    ]
  in
  List.iter
    (fun (name, src) ->
      let base = solve_with dir (name ^ "_base") src Search.default_config in
      check
        (Printf.sprintf "M10-T2 %s: control run answers %s, %s" name base.answer
           base.verdict)
        (contains base.verdict "VERIFIED" && base.restarts = 0);
      let base_kinds = rule_kinds base.proof in
      List.iter
        (fun (pname, config) ->
          let tag =
            Printf.sprintf "%s_%s" name
              (String.map (function ':' | '+' | '.' -> '_' | c -> c) pname)
          in
          let r = solve_with dir tag src config in
          let restarting = pname <> "phase" && pname <> "activity" in
          check
            (Printf.sprintf
               "M10-T2 %s --restarts/--phase %s: same answer (%s), %d restarts" name pname
               r.answer r.restarts)
            (r.answer = base.answer && ((not restarting) || r.restarts > 0));
          check
            (Printf.sprintf "M10-T2 %s %s: the proof is VERIFIED (%s)" name pname
               r.verdict)
            (contains r.verdict "VERIFIED"
            && contains r.verdict "UNSATISFIABLE" = contains base.verdict "UNSATISFIABLE"
            );
          check
            (Printf.sprintf "M10-T2 %s %s: every id received is deleted (I-X2, audit)"
               name pname)
            (r.live = 0);
          check
            (Printf.sprintf "M10-T2 %s %s: M1-T36's identity with restart_unexplored" name
               pname)
            r.consistent;
          let extra =
            List.filter (fun k -> not (List.mem k base_kinds)) (rule_kinds r.proof)
          in
          check
            (Printf.sprintf
               "M10-T2 %s %s: no rule kind the restart-free proof lacks (D-0137 s.1)%s"
               name pname
               (if extra = [] then "" else ": " ^ String.concat "," extra))
            (extra = []))
        policies)
    cases

(* Without the flags nothing moves: the config's defaults are the pre-M10 search, and the
   strategy state is not even built. *)
let test_defaults_are_off () =
  check "M10-T2: default_config has restarts off and phase saving off"
    (Search.default_config.Search.restarts = Restart.No_restarts
    && not Search.default_config.Search.phase_saving);
  let dir = Filename.temp_file "baguette_m10d" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  let a = solve_with dir "q6a" (queens 6) Search.default_config in
  let b =
    solve_with dir "q6b" (queens 6)
      { Search.default_config with Search.restarts = Restart.No_restarts }
  in
  check "M10-T2: --restarts none is byte-identical to the default proof"
    (a.proof = b.proof)

(* ------------------------------------------------------ M10-T3: the activity scores *)

module Activity = Baguette_core.Activity
module Store = Baguette_core.Store
module Domain = Baguette_core.Domain
module Lit = Baguette_proof.Lit

let test_activity_unit () =
  let store =
    Store.create ~names:[| "a"; "b"; "c" |]
      ~domains:[| Domain.make 0 3; Domain.make 0 1; Domain.make 0 1 |]
  in
  let v i = Var.of_int i in
  let cands = [| v 0; v 1; v 2 |] in
  let a = Activity.create 3 in
  check "Activity: all scores 0 -> first-fail's choice (smallest domain, earliest): b"
    (Var.to_int (Activity.select a store cands) = 1);
  Activity.bump_lits a store [ Lit.pos (Lit.Ge ("c", 1)) ];
  check "Activity: a bumped variable outranks first-fail: c"
    (Var.to_int (Activity.select a store cands) = 2);
  Activity.decay a;
  Activity.bump_lits a store [ Lit.pos (Lit.Ge ("a", 2)); Lit.neg (Lit.Ge ("a", 1)) ];
  check "Activity: a later bump weighs more (EVSIDS), and once per clause per variable"
    (Var.to_int (Activity.select a store cands) = 0
    && Activity.score a (v 0) = 1.0 /. Activity.decay_factor
    && Activity.n_bumps a = 2);
  for _ = 1 to 5000 do
    Activity.decay a
  done;
  Activity.bump_lits a store [ Lit.pos (Lit.Ge ("b", 1)) ];
  check
    (Printf.sprintf
       "Activity: rescaling keeps every score finite and the order intact (%d rescales)"
       (Activity.n_rescales a))
    (Activity.n_rescales a > 0
    && Float.is_finite (Activity.score a (v 1))
    && Var.to_int (Activity.select a store cands) = 1
    && Activity.score a (v 0) >= Activity.score a (v 2))

(* The trail-reuse rule must actually keep a level somewhere, or the partial-restart lane
   above tested full restarts under another name. *)
let test_reuse_keeps_levels () =
  let dir = Filename.temp_file "baguette_m10r" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  let cfg =
    {
      Search.default_config with
      Search.search = Search.Activity_order;
      Search.restarts = Restart.Luby 1;
      Search.reuse_trail = true;
    }
  in
  let runs =
    List.map
      (fun (n, src) -> solve_with dir n src cfg)
      [ ("rq8", queens 8); ("rp54", pigeons); ("rq6o", queens ~opt:true 6) ]
  in
  let kept = List.fold_left (fun acc r -> acc + r.kept) 0 runs in
  check
    (Printf.sprintf
       "M10-T3: --reuse-trail keeps levels at some restart (%d kept over %d restarts), \
        every proof VERIFIED"
       kept
       (List.fold_left (fun acc r -> acc + r.restarts) 0 runs))
    (kept > 0 && List.for_all (fun r -> contains r.verdict "VERIFIED") runs)

(* D-0137 section 1, determinism: every schedule is a function of the conflicts, so two
   runs with the strategies on write the same proof byte for byte, as the default does
   (scripts/check_determinism.sh only runs the default). *)
let test_determinism_with_flags () =
  let dir = Filename.temp_file "baguette_m10det" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  let cfg =
    {
      Search.default_config with
      Search.search = Search.Alternate;
      Search.restarts = Restart.Luby 1;
      Search.phase_saving = true;
    }
  in
  let cfg2 =
    {
      cfg with
      Search.search = Search.Activity_order;
      Search.restarts = Restart.Lbd { window = 2; k = 1.0 };
      Search.reuse_trail = true;
    }
  in
  List.iter
    (fun (tag, c) ->
      let a = solve_with dir ("d1" ^ tag) (queens 8) c in
      let b = solve_with dir ("d2" ^ tag) (queens 8) c in
      check
        (Printf.sprintf
           "M10: two runs with %s write the same proof byte for byte (%d restarts)" tag
           a.restarts)
        (a.proof = b.proof && a.restarts > 0))
    [ ("alternate+luby:1+phase", cfg); ("activity+lbd+reuse+phase", cfg2) ]

(* ------------------------------------------- D-0152: the structures against their scans *)

module Reason = Baguette_core.Reason
module Explanation = Baguette_core.Explanation

(* S1: [learned_kind] after [set_learned_kind] answers what the two id lists answered,
   [List.mem] in the PB list first, then in the clause list, nothing below
   [first_learned_id]. Ids are registered sparsely and past 64 and 128, so the table
   grows more than once, and the queries include ids below the boundary and past the end. *)
let test_learned_kinds () =
  let rng = Random.State.make [| 0x0152; 1 |] in
  let ok = ref true in
  for round = 1 to 50 do
    let s = Search.stats_create () in
    let first = 10 + Random.State.int rng 50 in
    s.Search.first_learned_id <- first;
    let pb = ref [] and cl = ref [] in
    for _ = 1 to 1 + Random.State.int rng (if round mod 5 = 0 then 300 else 30) do
      let id = first - 3 + Random.State.int rng 400 in
      if not (List.mem id !pb || List.mem id !cl) then
        if Random.State.bool rng then (
          pb := id :: !pb;
          Search.set_learned_kind s id Search.kind_pb)
        else (
          cl := id :: !cl;
          Search.set_learned_kind s id Search.kind_clause)
    done;
    for id = -2 to first + 450 do
      let want =
        if id < first then Search.kind_none
        else if List.mem id !pb then Search.kind_pb
        else if List.mem id !cl then Search.kind_clause
        else Search.kind_none
      in
      if not (Char.equal (Search.learned_kind s id) want) then ok := false
    done
  done;
  check "D-0152 S1: the kind table answers what the two id lists answered" !ok;
  let s = Search.stats_create () in
  check "D-0152 S1: a fresh stats knows no learned id (first_learned_id = max_int)"
    (Char.equal (Search.learned_kind s 0) Search.kind_none
    && Char.equal (Search.learned_kind s (-1)) Search.kind_none)

(* S5: [level_set ls] is [List.mem _ ls], on lists with repeats, the empty list, and a
   negative level (the scan's fallback). *)
let test_level_set () =
  let rng = Random.State.make [| 0x0152; 5 |] in
  let ok = ref true in
  for _ = 1 to 2000 do
    let n = Random.State.int rng 12 in
    let ls =
      List.init n (fun _ ->
          if Random.State.int rng 40 = 0 then -1 - Random.State.int rng 3
          else Random.State.int rng 30)
    in
    let f = Search.level_set ls in
    for l = -5 to 35 do
      if f l <> List.mem l ls then ok := false
    done
  done;
  check "D-0152 S5: level_set is List.mem on 2 000 random level lists" !ok

(* S3 and S4, on one random walk of a store: levels (some empty, so two marks share a
   position, and some opened with no push yet, so a mark sits at the trail's end), bound
   moves, interior holes, and backtracks. At every step [decision_entries] equals
   [decision_entries_scan], [unfixed] equals the [Domain.size > 1] filter, and
   [first_fail] over it equals the full scan. *)
let test_marks_and_unfixed () =
  let n = 6 in
  let names = Array.init n (Printf.sprintf "v%d") in
  let domains = Array.init n (fun i -> Domain.make 0 (if i < 2 then 1 else 9)) in
  let s = Store.create ~names ~domains in
  let r = Reason.because ~concludes:None Reason.none (Explanation.model_row 1) in
  let rng = Random.State.make [| 0x0152; 3 |] in
  let entries_ok = ref true and unfixed_ok = ref true and ff_ok = ref true in
  let shared = ref 0 and holes = ref 0 in
  let full_first_fail cands =
    let best = ref cands.(0) in
    Array.iter
      (fun v ->
        if Domain.size (Store.get s v) < Domain.size (Store.get s !best) then best := v)
      cands;
    !best
  in
  for _ = 1 to 6000 do
    (match Random.State.int rng 7 with
    | 0 | 1 -> Store.new_level s
    | 2 | 3 | 4 ->
        let v = Var.of_int (Random.State.int rng n) in
        let d = Store.get s v in
        if Domain.lo d < Domain.hi d then
          ignore
            (match Random.State.int rng 3 with
            | 0 -> Store.set_lo s v (Domain.lo d + 1) r
            | 1 -> Store.set_hi s v (Domain.hi d - 1) r
            | _ ->
                if Domain.hi d - Domain.lo d >= 2 then (
                  incr holes;
                  Store.remove s v (Domain.lo d + 1) r)
                else Store.set_lo s v (Domain.lo d + 1) r)
    | _ -> if Store.level s > 0 then Store.backtrack s);
    let a = Search.decision_entries s and b = Search.decision_entries_scan s in
    if not (List.equal (fun (i, e) (j, e') -> i = j && e == e') a b) then
      entries_ok := false;
    let ms = Store.level_marks s in
    if List.length (List.sort_uniq Int.compare ms) < List.length ms then incr shared;
    let u = Search.unfixed s in
    let want =
      Array.of_list
        (List.filter (fun v -> Domain.size (Store.get s v) > 1) (List.init n Var.of_int))
    in
    if u <> want then unfixed_ok := false;
    if Array.length u > 0 && not (Var.equal (Search.first_fail s u) (full_first_fail u))
    then ff_ok := false
  done;
  check "D-0152 S3: decision_entries over the marks equals the trail scan" !entries_ok;
  check
    (Printf.sprintf "D-0152 S3: ...including %d states with two levels at one position"
       !shared)
    (!shared > 100);
  check "D-0152 S4: unfixed by is_fixed equals the Domain.size > 1 filter" !unfixed_ok;
  check
    (Printf.sprintf
       "D-0152 S4: first_fail stopping at size 2 equals the full scan (%d holes punched)"
       !holes)
    (!ff_ok && !holes > 100)

let () =
  print_endline "";
  test_learned_kinds ();
  test_level_set ();
  test_marks_and_unfixed ();
  test_determinism_with_flags ();
  test_activity_unit ();
  test_luby ();
  test_schedules ();
  test_of_string ();
  test_defaults_are_off ();
  test_restarting_search ();
  test_reuse_keeps_levels ();
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "\nsearch-strategy tests passed"
