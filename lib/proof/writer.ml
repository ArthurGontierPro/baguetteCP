(* Writing the .pbp proof file.

   This module owns the constraint-id counter. The rule is: an id you receive is an id
   you are responsible for deleting (invariant I-X2). OCaml cannot enforce that
   statically, so [audit] mode tracks live ids and asserts the set is empty at
   [conclusion]. Enable with BAGUETTE_PROOF_AUDIT=1. *)

type cid = int

type t = {
  oc : out_channel;
  mutable next_id : cid;
  live : (cid, string) Hashtbl.t;  (* id -> what introduced it, for audit failures *)
  audit : bool;
  comments : bool;
}

let create ?(comments = false) oc =
  let audit =
    match Sys.getenv_opt "BAGUETTE_PROOF_AUDIT" with Some "1" -> true | _ -> false
  in
  { oc; next_id = 0; live = Hashtbl.create 256; audit; comments }

let line t fmt = Printf.fprintf t.oc (fmt ^^ "\n")

let comment t fmt =
  if t.comments then Printf.fprintf t.oc ("* " ^^ fmt ^^ "\n")
  else Printf.ifprintf t.oc ("* " ^^ fmt ^^ "\n")

let fresh t ~origin =
  t.next_id <- t.next_id + 1;
  if t.audit then Hashtbl.replace t.live t.next_id origin;
  t.next_id

(* Preamble: version line, then the count of model constraints loaded from the .opb. *)
let header t ~n_model_constraints =
  line t "pseudo-Boolean proof version 2.0";
  line t "f %d" n_model_constraints;
  (* The f rule makes the model constraints ids 1..n. *)
  t.next_id <- n_model_constraints;
  if t.audit then
    for i = 1 to n_model_constraints do
      Hashtbl.replace t.live i "model"
    done

(* A cutting-planes derivation, given as reverse Polish over ids. *)
let pol t ~origin steps =
  line t "pol %s" steps;
  fresh t ~origin

(* Reverse unit propagation of a clause. Prefer [pol] where the reasoning is known;
   see docs/PROOF-FORMAT.md section 2. *)
let rup t ~origin lits =
  let body =
    String.concat " " (List.map (fun l -> "1 " ^ Lit.to_string l) lits)
  in
  line t "rup %s >= 1 ;" body;
  fresh t ~origin

let delete t id =
  line t "del id %d" id;
  if t.audit then Hashtbl.remove t.live id

let solution t lits =
  line t "sol %s" (String.concat " " (List.map Lit.to_string lits))

let check_audit t =
  if t.audit && Hashtbl.length t.live > 0 then begin
    Printf.eprintf "proof audit: %d constraint ids never deleted (invariant I-X2)\n"
      (Hashtbl.length t.live);
    Hashtbl.iter (fun id origin -> Printf.eprintf "  id %d from %s\n" id origin) t.live;
    failwith "proof audit failed"
  end

type verdict = Sat | Unsat | Bounds of int * int

let conclusion t v =
  (match v with
  | Sat -> line t "output NONE"; line t "conclusion SAT"
  | Unsat -> line t "output NONE"; line t "conclusion UNSAT"
  | Bounds (lo, hi) -> line t "output NONE"; line t "conclusion BOUNDS %d %d" lo hi);
  line t "end pseudo-Boolean proof";
  check_audit t;
  flush t.oc
