(* Which veripb this project checks against.

   The OCaml half of [scripts/checker.sh]; the two must agree, and that script's
   header carries the full reasoning. Summary:

     1. $VERIPB, if set. An explicit choice wins and is never silently replaced --
        a $VERIPB that does not resolve is an error, not a fall-through.
     2. $HOME/.cargo/bin/veripb   VeriPB 3.0.2, Rust. The checker of record (D-0023).
     3. $HOME/.local/bin/veripb   VeriPB 2.2.2, Python. Fallback.
     4. `veripb` on $PATH.

   PATH is last deliberately. Both builds are installed on the development machine
   and ~/.local/bin comes first on PATH, so "whatever is on PATH" silently meant the
   Python 2.2.2. Every test module used to open-code its own copy of that search,
   which is how a project-wide decision came to live in nine places at once.

   This lives in lib/proof/ rather than in test/ because which checker the proofs are
   contracted against is part of the proof contract, not a property of one test
   executable. It is the only module here that touches the environment.

   [find] returns [None] when nothing resolves. Every caller must treat that as a
   FAILURE and say so: an unchecked proof is not a passing test. [not_found_message]
   is the text to print; use it rather than inventing a new one, so the diagnostic a
   developer sees is the same from every direction. *)

let candidates () =
  let home = try Sys.getenv "HOME" with Not_found -> "" in
  [ Filename.concat home ".cargo/bin/veripb"; Filename.concat home ".local/bin/veripb" ]

let on_path name =
  Sys.command (Printf.sprintf "command -v %s >/dev/null 2>&1" (Filename.quote name)) = 0

let runnable p = (Sys.file_exists p && not (Sys.is_directory p)) || on_path p

(* [Some path] to run, [None] if nothing resolves.

   Memoised: every one of these is a [Sys.command] shelling out, and the test modules
   ask once per case. *)
let cached = ref None

let find () =
  match !cached with
  | Some r -> r
  | None ->
      let r =
        match Sys.getenv_opt "VERIPB" with
        | Some v when String.trim v <> "" ->
            (* Explicit and broken is an error, not a reason to pick another. *)
            if runnable v then Some v else None
        | _ -> (
            match List.find_opt runnable (candidates ()) with
            | Some p -> Some p
            | None -> if on_path "veripb" then Some "veripb" else None)
      in
      cached := Some r;
      r

let not_found_message =
  "veripb not found, so the proof was NOT checked. This is a FAILURE, not a skip: an \
   unchecked proof is not a passing test (CLAUDE.md). Looked at $VERIPB, then \
   ~/.cargo/bin/veripb (3.0.2, the checker of record), then ~/.local/bin/veripb (2.2.2), \
   then $PATH. scripts/bootstrap.sh installs one; scripts/checker.sh prints which one \
   would be used."
