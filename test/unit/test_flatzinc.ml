(* Unit tests for the FlatZinc front end: lexing, parsing, model building.

   Fill in as M1-T6 lands. Every accepted construct from docs/SPEC.md section 2.1 should
   have a case here, and every rejected one should have a case confirming the error names
   the offending builtin rather than silently skipping it. *)

let failures = ref 0

let check name cond =
  if cond then Printf.printf "ok   %s\n" name
  else begin
    incr failures;
    Printf.printf "FAIL %s\n" name
  end

let () =
  check "flatzinc: placeholder — replace as M1-T6 lands" true;
  if !failures > 0 then begin
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1
  end
  else print_endline "\nflatzinc unit tests passed"
