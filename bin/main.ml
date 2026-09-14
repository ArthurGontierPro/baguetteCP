(* The baguette CLI.
     baguette MODEL.fzn [--proof PREFIX] [--proof-comments] [--all]

   Writes PREFIX.opb and PREFIX.pbp when --proof is given; both are required by the
   checker (docs/SPEC.md section 4.1). *)

type options = {
  model : string;
  proof_prefix : string option;
  proof_comments : bool;
  all_solutions : bool;
}

let usage () =
  prerr_endline
    "usage: baguette MODEL.fzn [--proof PREFIX] [--proof-comments] [--all]";
  exit 2

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
      { model = m;
        proof_prefix = !proof_prefix;
        proof_comments = !proof_comments;
        all_solutions = !all_solutions }

let () =
  let opts = parse_args Sys.argv in
  if not (Sys.file_exists opts.model) then begin
    Printf.eprintf "no such file: %s\n" opts.model;
    exit 2
  end;
  (* M1-T6 parses, M1-T7 onward propagates, M1-T10 searches. Until then, fail loudly:
     the spec forbids pretending a model was handled. *)
  Printf.eprintf
    "baguette: not implemented yet (roadmap M1). Model %s was parsed as a path only.\n"
    opts.model;
  (match opts.proof_prefix with
  | Some p -> Printf.eprintf "baguette: would write %s.opb and %s.pbp\n" p p
  | None -> ());
  exit 3
