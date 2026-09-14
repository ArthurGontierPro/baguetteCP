(* The single error type of the FlatZinc front end.

   Lexer, parser and builder all raise [Error]. Callers that want an exit code rather
   than an exception use [catch] / [to_string]; bin/main.ml is expected to print
   [to_string] on stderr and exit non-zero (SPEC 2.1: an unsupported builtin must exit
   non-zero, never be skipped). *)

type t = { pos : Pos.t; msg : string }

exception Error of t

(* [failf pos "..."] raises; its result type is polymorphic so it can be used in any
   position. *)
let failf pos fmt = Printf.ksprintf (fun msg -> raise (Error { pos; msg })) fmt

let to_string { pos; msg } = Printf.sprintf "%s: error: %s" (Pos.to_string pos) msg

(* Note: this module's [Error] exception shadows the [Error] constructor of [result],
   hence the qualified [Stdlib.Error] below. *)
let catch f = try Stdlib.Ok (f ()) with Error e -> Stdlib.Error e
