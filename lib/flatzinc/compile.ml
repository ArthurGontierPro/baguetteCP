(* M1-T14 stub. Replaced by agent-compile; fails loudly so an undelivered half is red
   rather than quietly absent. *)
type t = {
  store : Baguette_core.Store.t;
  engine : Baguette_core.Engine.t;
  encoding : Baguette_proof.Encoding.t;
}

let compile (_ : Model.t) : t = failwith "Compile.compile: not implemented (M1-T14)"
