(* Source positions for FlatZinc diagnostics.

   SPEC 2.1 requires clear errors; a clear error about a FlatZinc file is one that says
   where in the file the problem is. Every Error.t carries one of these. *)

type t = { file : string; line : int; col : int }

let make file line col = { file; line; col }
let unknown = { file = "<unknown>"; line = 0; col = 0 }

let to_string p =
  if p.line = 0 then p.file else Printf.sprintf "%s:%d:%d" p.file p.line p.col
