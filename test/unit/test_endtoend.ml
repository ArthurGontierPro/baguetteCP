(* The integration test: model -> propagators -> engine -> search -> proof -> veripb.

   Owned by the orchestrator, deliberately. Three separate bugs in M1-T7 were each
   invisible to the session that wrote the code and to its own green test suite, and
   showed up only when the halves were run together against the real checker. This file
   is the place where that happens on purpose, and no single session can make it pass
   alone.

   Empty until M1-T8 and M1-T10 land. *)

let () = print_endline "\nend-to-end tests: none yet (M1-T8, M1-T10)"
