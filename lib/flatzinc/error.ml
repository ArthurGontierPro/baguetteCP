(* The single error type of the FlatZinc front end.

   Lexer, parser, builder and compile.ml all raise [Error], and so does the .scp reader
   (lib/scp/reader.ml). Callers that want an exit code rather than an exception use
   [catch] and [to_string]: bin/main.ml prints [to_string] on stderr and exits non-zero,
   because SPEC 2.1 requires an unsupported builtin to exit non-zero, never to be
   skipped. *)

type t = { pos : Pos.t; msg : string }

exception Error of t

(* [failf pos "..."] raises; its result type is polymorphic so it can be used in any
   position. *)
let failf pos fmt = Printf.ksprintf (fun msg -> raise (Error { pos; msg })) fmt
let to_string { pos; msg } = Printf.sprintf "%s: error: %s" (Pos.to_string pos) msg

(* Note: this module's [Error] exception shadows the [Error] constructor of [result],
   hence the qualified [Stdlib.Error] below. *)
let catch f = try Stdlib.Ok (f ()) with Error e -> Stdlib.Error e
