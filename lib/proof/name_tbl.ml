(* A hash table keyed by a FlatZinc IDENTIFIER (a variable's name, or a rendered literal
   name): the one table every name lookup on the hot path goes through (M20-pernode-T4,
   D-0236).

   Specialised to [string] so that a probe compares keys with [String.equal] rather than
   the polymorphic [compare] (a C call per probe, D-0080), and hashed with [String.hash]
   rather than [Hashtbl.hash]. The two hash functions RETURN THE SAME VALUE on every
   string (both are [caml_hash_mix_string] under seed 0 and the same final mix; D-0236
   checks it on 100 000 names), so a table built here has the bucket layout and the
   iteration order the generic table had, and swapping one in can change no output. What
   differs is the price: [Hashtbl.hash] enters the generic structural hash ([caml_hash],
   its work queue and tag dispatch, behind [caml_c_call]) before it reaches the string
   mixer, and [String.hash] is a [noalloc] call straight to it. On elitserien handball12
   that dispatch was half of every name hash (D-0236 section 2). *)
include Hashtbl.Make (struct
  type t = string

  let equal = String.equal
  let hash (s : string) = String.hash s
end)
