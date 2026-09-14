(* Debug-mode invariant checking.

   docs/INVARIANTS.md asks that assertions guarded by BAGUETTE_DEBUG=1 check as many of
   the invariants as is affordable. The flag is read once, at module initialisation, so
   the common (disabled) path is a single boolean test that the compiler can hoist. *)

let enabled =
  match Sys.getenv_opt "BAGUETTE_DEBUG" with
  | Some ("1" | "true" | "yes" | "on") -> true
  | _ -> false

(* [check name f] evaluates [f] only when debugging is on. Raising rather than using
   [assert] so the message survives a build with -noassert, and so the invariant tag
   (I-D2, I-T1, ...) reaches the person reading the failure. *)
let check name f = if enabled && not (f ()) then failwith ("invariant violated: " ^ name)
