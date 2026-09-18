(* Which veripb this project checks against.

   The OCaml half of [scripts/checker.sh]; the two must agree, and that script's
   header carries the full reasoning. Summary:

     1. $VERIPB, if set. An explicit choice wins and is never silently replaced --
        a $VERIPB that does not resolve is an error, not a fall-through.
     2. $HOME/.cargo/bin/veripb   VeriPB 3.0.2, Rust. The checker of record (D-0023).
     3. `veripb` on $PATH.

   There is exactly ONE checker now (D-0046 removed format 2.0 and with it the Python
   VeriPB this project used to keep as a second implementation), so the list is short --
   but it is still a list, and PATH is still last. The reason is historical and worth
   keeping: two builds used to be installed side by side with the other one first on
   PATH, so "whatever is on PATH" silently meant the wrong checker, which is the failure
   M1-T18 exists to remove. A $PATH entry is whatever the machine happens to offer;
   naming the path we mean is not.

   Every test module used to open-code its own copy of this search, which is how a
   project-wide decision came to live in nine places at once.

   This lives in lib/proof/ rather than in test/ because which checker the proofs are
   contracted against is part of the proof contract, not a property of one test
   executable. It is the only module here that touches the environment.

   [find] returns [None] when nothing resolves. Every caller must treat that as a
   FAILURE and say so: an unchecked proof is not a passing test. [not_found_message]
   is the text to print; use it rather than inventing a new one, so the diagnostic a
   developer sees is the same from every direction. *)

let candidates () =
  let home = try Sys.getenv "HOME" with Not_found -> "" in
  [ Filename.concat home ".cargo/bin/veripb" ]

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
   unchecked proof is not a passing test (CLAUDE.md). VeriPB 3.0.2 is the only checker \
   this project has -- there is no second implementation to fall back to (D-0046) -- so \
   a missing one means NOTHING was verified. Looked at $VERIPB, then ~/.cargo/bin/veripb \
   (3.0.2, the checker of record), then $PATH. scripts/bootstrap.sh installs it; \
   scripts/checker.sh prints which one would be used."
