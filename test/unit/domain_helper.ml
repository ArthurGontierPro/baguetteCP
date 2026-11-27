(* Test-only constructors over [Domain] (M22-review-T5). NOT a test binary: like
   mem_guard.ml it is absent from the [names] of test/unit/dune, so dune links it into
   every suite that uses it.

   Both functions lived in lib/core/domain.ml with no caller in [lib/] or [bin/], and the
   first is a trap there: a domain built by [of_list] carries holes that no trail entry
   explains, so a conflict resting on one is justified by a [pol] over model rows that is
   not contradictory, and veripb rejected four refutations when M7-T11 tried it (D-0072,
   lib/core/trace.ml's [remover] header). The solver gives the store the HULL of a set
   domain and one [Ne] per hole instead. Tests still want a holed domain built in one
   call, so the two live here, where nothing in the solver can reach them. *)

open Baguette_core

(* A domain with exactly [values] as its members: the hull, with the gaps removed as
   holes. Raises [Domain.Bad_domain] on an empty list. *)
let of_list values =
  match List.sort_uniq Stdlib.compare values with
  | [] -> raise (Domain.Bad_domain "empty domain from an empty value list")
  | first :: _ as sorted ->
      let last = List.fold_left (fun _ v -> v) first sorted in
      let d = Domain.make first last in
      let rec go d v present =
        if v > last then d
        else
          match present with
          | p :: rest when p = v -> go d (v + 1) rest
          | _ -> (
              match Domain.remove d v with
              | Domain.Changed d' -> go d' (v + 1) present
              | Domain.Unchanged -> go d (v + 1) present
              | Domain.Failed -> raise (Domain.Bad_domain "of_list: domain became empty"))
      in
      go d first sorted

(* The [change] that applying [r] to [d] makes. [Failed] is not a change: the empty
   domain is never stored (I-D1). *)
let change_of d (r : Domain.result) =
  match r with
  | Domain.Unchanged | Domain.Failed -> Domain.NoChange
  | Domain.Changed d' -> Domain.classify ~old:d ~now:d'
