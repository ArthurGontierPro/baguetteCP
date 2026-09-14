(* The baguette CLI.
     baguette MODEL.fzn [--proof PREFIX] [--proof-comments] [--all]

   docs/ARCHITECTURE.md gives this file one job -- "parse args, wire everything, print
   results" -- and the wiring is the whole of M1-T14. Everything below it already
   worked; none of it was reachable from a command line, which is why all five models
   in test/models/ were xfail while the engine underneath them solved and emitted
   proofs veripb accepted.

   The pipeline, in the order it must happen:

     Builder.of_file   .fzn text            -> Model.t
     Compile.compile   Model.t              -> store, engine, encoding
     Encoding.write_opb                     -> PREFIX.opb        (I-X5: before the proof
                                                                  references it)
     Encoding.start_proof                   -> the proof's `f N` header
     Search.solve                           -> Sat assignment | Unsat, proof written
     Output.solution / Output.unsatisfiable -> stdout, SPEC 2.2

   Two things here are less obvious than they look.

   **The variable-index bridge.** [Search.assignment] is a [(Var.t * int) list] over the
   solver's own variable identities; [Model.check_assignment] and [Output.solution] both
   want an [int array] indexed by *model* variable index. Those two index spaces coincide
   only because [Compile.compile] builds the store in [Model.vars] order and promises to
   keep doing so. [assignment_values] below is where they meet, and it re-checks the
   promise rather than assuming it: an off-by-one here would print a wrong answer that
   the independent check (I-S1) would then happily confirm, because it would be checking
   the same permuted array.

   **A proof is written even without --proof.** [Search.solve] needs a [Justify.ctx],
   which needs a [Writer.t], which needs a channel; there is no "solve without logging"
   mode and docs/SPEC.md 1 is explicit that there should not be one ("The proof is not a
   debugging aid. It is a primary output"). Without --proof the proof is written to a
   temporary file and deleted, so the work -- and the audit -- still happens and the run
   still fails loudly if the solver cannot justify itself. It is the file that is
   optional, not the proof. *)

module Model = Baguette_flatzinc.Model
module Builder = Baguette_flatzinc.Builder
module Compile = Baguette_flatzinc.Compile
module Output = Baguette_flatzinc.Output
module Fz_error = Baguette_flatzinc.Error
module Var = Baguette_core.Var
module Store = Baguette_core.Store
module Search = Baguette_core.Search
module Justify = Baguette_core.Justify
module Writer = Baguette_proof.Writer
module Encoding = Baguette_proof.Encoding

type options = {
  model : string;
  proof_prefix : string option;
  proof_comments : bool;
  all_solutions : bool;
}

(* Exit codes. 0 covers both SAT and UNSAT: an UNSAT model is a successful run that
   proved something, not a failure, and scripts/run_model_tests.sh reads a non-zero exit
   as the solver having fallen over. *)
let exit_ok = 0
let exit_usage = 2
let exit_unsupported = 3
let exit_internal = 4

let usage () =
  prerr_endline "usage: baguette MODEL.fzn [--proof PREFIX] [--proof-comments] [--all]";
  prerr_endline "";
  prerr_endline "  --proof PREFIX    write PREFIX.opb and PREFIX.pbp (SPEC 4.1); verify";
  prerr_endline "                    them with: veripb PREFIX.opb PREFIX.pbp";
  prerr_endline "  --proof-comments  annotate the proof with the step that produced each";
  prerr_endline "                    rule -- large, and only useful when debugging one";
  prerr_endline "  --all             every solution, not just the first (not implemented)";
  prerr_endline "";
  prerr_endline "  BAGUETTE_PROOF_AUDIT=0 disables the constraint-id audit (I-X2), which";
  prerr_endline "  is on by default here even though the library's own default is off.";
  exit exit_usage

let parse_args argv =
  let model = ref None in
  let proof_prefix = ref None in
  let proof_comments = ref false in
  let all_solutions = ref false in
  let rec go i =
    if i >= Array.length argv then ()
    else
      match argv.(i) with
      | "--proof" ->
          if i + 1 >= Array.length argv then usage ();
          proof_prefix := Some argv.(i + 1);
          go (i + 2)
      | "--proof-comments" ->
          proof_comments := true;
          go (i + 1)
      | "--all" ->
          all_solutions := true;
          go (i + 1)
      | "-h" | "--help" -> usage ()
      | arg when String.length arg > 0 && arg.[0] = '-' ->
          Printf.eprintf "unknown option: %s\n" arg;
          usage ()
      | arg ->
          if !model <> None then usage ();
          model := Some arg;
          go (i + 1)
  in
  go 1;
  match !model with
  | None -> usage ()
  | Some m ->
      {
        model = m;
        proof_prefix = !proof_prefix;
        proof_comments = !proof_comments;
        all_solutions = !all_solutions;
      }

(* --------------------------------------------------------- the index bridge *)

(* [Search.assignment] to a [Model.vars]-indexed array. The two index spaces agree by
   construction (see Compile's header) and this is the one place that depends on it, so
   this is where it is checked rather than assumed: every model variable must be
   assigned exactly once, and the store must agree about its name. *)
let assignment_values m store (assignment : Search.assignment) =
  let n = Model.nvars m in
  let values = Array.make n 0 in
  let seen = Array.make n false in
  List.iter
    (fun (v, value) ->
      let i = Var.to_int v in
      if i < 0 || i >= n then
        failwith
          (Printf.sprintf "solver variable %d is outside the model's %d variables" i n);
      let declared = (Model.var m i).Model.v_name in
      let in_store = Store.name store v in
      if not (String.equal declared in_store) then
        failwith
          (Printf.sprintf
             "variable index %d is %S in the model and %S in the store -- Compile must \
              build the store in Model.vars order"
             i declared in_store);
      seen.(i) <- true;
      values.(i) <- value)
    assignment;
  Array.iteri
    (fun i s ->
      if not s then
        failwith
          (Printf.sprintf "variable %S (index %d) was not assigned"
             (Model.var m i).Model.v_name i))
    seen;
  values

(* ------------------------------------------------------------------ running *)

(* The proof channel, plus how to finish with it. Without --proof it is a temporary
   file that is removed afterwards: see the header. *)
let open_proof_channel opts =
  match opts.proof_prefix with
  | Some prefix ->
      let path = prefix ^ ".pbp" in
      (open_out path, fun () -> ())
  | None -> (
      let path = Filename.temp_file "baguette" ".pbp" in
      (open_out path, fun () -> try Sys.remove path with Sys_error _ -> ()))

let audit_enabled () =
  (* The library defaults this off and turns it on with BAGUETTE_PROOF_AUDIT=1
     (docs/ARCHITECTURE.md section 6). The CLI inverts that default deliberately: I-X2
     is cheap at these sizes, it has already caught one real defect (D-0015), and a user
     running the solver should get the check without having known to ask for it. *)
  match Sys.getenv_opt "BAGUETTE_PROOF_AUDIT" with Some "0" -> false | _ -> true

let solve opts (m : Model.t) =
  let compiled = Compile.compile m in
  let store = compiled.Compile.store in
  let encoding = compiled.Compile.encoding in
  (* I-X5: the .opb is complete and on disk before any proof rule can cite it. *)
  (match opts.proof_prefix with
  | Some prefix ->
      let oc = open_out (prefix ^ ".opb") in
      Encoding.write_opb ~comments:[ "baguette: " ^ opts.model ] encoding oc;
      close_out oc
  | None -> ());
  let proof_oc, cleanup = open_proof_channel opts in
  let writer =
    Writer.create ~comments:opts.proof_comments ~audit:(audit_enabled ()) proof_oc
  in
  Encoding.start_proof encoding writer;
  (* Every propagator instance carries its own row id (D-0011/D-0015), so a [Trivial]
     explanation reaching the proof layer means one did not, and there is no honest way
     to guess which row it meant. Fail rather than pick. *)
  let ctx =
    Justify.create ~writer ~encoding ~model_id:(fun () ->
        failwith
          "an explanation reached the proof layer as Trivial: some propagator instance \
           was built without its model row id (D-0011)")
  in
  let check assignment =
    Model.check_assignment m (assignment_values m store assignment)
  in
  let outcome =
    Fun.protect
      ~finally:(fun () ->
        close_out proof_oc;
        cleanup ())
      (fun () -> Search.solve ~engine:compiled.Compile.engine ~store ~ctx ~check ())
  in
  match outcome with
  | Search.Sat assignment ->
      print_string (Output.solution m (assignment_values m store assignment))
  | Search.Unsat -> print_string Output.unsatisfiable

(* --------------------------------------------------------------------- main *)

let () =
  let opts = parse_args Sys.argv in
  if not (Sys.file_exists opts.model) then (
    Printf.eprintf "no such file: %s\n" opts.model;
    exit exit_usage);
  if opts.all_solutions then (
    (* SPEC 2.2 describes `==========` for an exhausted search, and Output.exhausted
       renders it, but Search.solve stops at the first solution: there is no
       all-solutions mode to print it after. Saying so beats printing one solution and
       letting the `----------` imply there were no others. *)
    prerr_endline
      "baguette: --all is not implemented -- Search.solve returns the first solution \
       only. Re-run without it.";
    exit exit_unsupported);
  match Fz_error.catch (fun () -> Builder.of_file opts.model) with
  | Error e ->
      prerr_endline (Fz_error.to_string e);
      exit exit_usage
  | Ok m -> (
      match Fz_error.catch (fun () -> solve opts m) with
      | Ok () -> exit exit_ok
      | Error e ->
          (* Compile raises through the front end's error type for everything SPEC 2.1
             requires a diagnostic for: an unimplemented builtin, a domain the encoding
             cannot express, an objective, a search annotation that is not what the
             search actually does. *)
          prerr_endline (Fz_error.to_string e);
          exit exit_unsupported
      | exception Search.Unsound_solution assignment ->
          (* I-P1. The solver found an assignment its own propagators accepted and the
             model rejects. That is a propagator soundness bug, and the only correct
             thing to do with it is stop. *)
          Printf.eprintf
            "baguette: INTERNAL -- a propagator is unsound (I-P1). The search returned \
             an assignment that does not satisfy the model:\n";
          List.iter
            (fun (v, value) ->
              Printf.eprintf "  %s = %d\n" (Model.var m (Var.to_int v)).Model.v_name value)
            assignment;
          exit exit_internal
      | exception Writer.Audit_failed msg ->
          (* I-X2: some constraint id was minted and never retired. The answer may well
             be right, but the proof is not one we are entitled to stand behind. *)
          Printf.eprintf "baguette: INTERNAL -- proof audit failed (I-X2): %s\n" msg;
          exit exit_internal)
