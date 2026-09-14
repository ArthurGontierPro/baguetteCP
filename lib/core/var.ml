(* Variable identity. Abstract on purpose: variables are dense indices into the store's
   arrays, and nothing outside the store should rely on that. *)

type t = int

let of_int i = i
let to_int v = v
let equal : t -> t -> bool = Int.equal
let compare : t -> t -> int = Int.compare
let hash (v : t) = v

module Map = Map.Make (Int)
module Set = Set.Make (Int)
