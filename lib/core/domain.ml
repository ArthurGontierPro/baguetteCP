(* Finite integer domains: a bounds pair plus a hole set.

   Rationale for the representation is in docs/ARCHITECTURE.md section 2 — most
   propagation in a linear-heavy workload is bounds reasoning, so the bounds are the fast
   path and holes are only populated by the propagators that actually punch them.

   Invariants (docs/INVARIANTS.md):
     I-D1  lo <= hi, or the domain is empty and was reported as a failure
     I-D2  lo and hi are in the domain: holes never sit at a bound *)

module ISet = Set.Make (Int)

type t = { lo : int; hi : int; holes : ISet.t }

type result =
  | Unchanged
  | Changed of t
  | Failed

exception Bad_domain of string

let make lo hi =
  if lo > hi then raise (Bad_domain (Printf.sprintf "empty initial domain %d..%d" lo hi));
  { lo; hi; holes = ISet.empty }

let lo d = d.lo
let hi d = d.hi
let is_fixed d = d.lo = d.hi
let mem d v = v >= d.lo && v <= d.hi && not (ISet.mem v d.holes)

let value d = if is_fixed d then Some d.lo else None

let size d =
  let holes_inside =
    ISet.cardinal (ISet.filter (fun v -> v >= d.lo && v <= d.hi) d.holes)
  in
  d.hi - d.lo + 1 - holes_inside

(* Restore I-D2 by walking the bounds past any holes sitting on them, and drop holes that
   have fallen outside the bounds so the set does not grow without bound. *)
let normalise d =
  let rec up d =
    if d.lo > d.hi then None
    else if ISet.mem d.lo d.holes then up { d with lo = d.lo + 1 }
    else Some d
  in
  let rec down d =
    if d.lo > d.hi then None
    else if ISet.mem d.hi d.holes then down { d with hi = d.hi - 1 }
    else Some d
  in
  match up d with
  | None -> None
  | Some d -> (
      match down d with
      | None -> None
      | Some d ->
          let holes = ISet.filter (fun v -> v > d.lo && v < d.hi) d.holes in
          Some { d with holes })

let settle d = match normalise d with None -> Failed | Some d -> Changed d

let set_lo d v =
  if v <= d.lo then Unchanged else if v > d.hi then Failed else settle { d with lo = v }

let set_hi d v =
  if v >= d.hi then Unchanged else if v < d.lo then Failed else settle { d with hi = v }

let remove d v =
  if not (mem d v) then Unchanged else settle { d with holes = ISet.add v d.holes }

let fix d v =
  if not (mem d v) then Failed
  else if is_fixed d then Unchanged
  else Changed { lo = v; hi = v; holes = ISet.empty }

let iter f d =
  for v = d.lo to d.hi do
    if not (ISet.mem v d.holes) then f v
  done

let to_list d =
  let acc = ref [] in
  iter (fun v -> acc := v :: !acc) d;
  List.rev !acc

let to_string d =
  if is_fixed d then string_of_int d.lo
  else if ISet.is_empty d.holes then Printf.sprintf "%d..%d" d.lo d.hi
  else
    Printf.sprintf "%d..%d \\ {%s}" d.lo d.hi
      (String.concat "," (List.map string_of_int (ISet.elements d.holes)))
