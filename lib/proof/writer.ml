(* Writing the .pbp proof file.

   This module owns the constraint-id counter. The rule is: an id you receive is an id
   you are responsible for deleting (invariant I-X2). OCaml cannot enforce that
   statically, so [audit] mode tracks live ids and asserts the set is empty at
   [conclusion]. Enable with BAGUETTE_PROOF_AUDIT=1.

   What the audit set contains: the ids handed back by rule emission. The model
   constraints loaded by [f] are *not* in it. ARCHITECTURE section 6 words the
   obligation as "an id you received is an id you are responsible for deleting", and
   nobody receives a model-constraint id -- they are fixed by the .opb. Deleting them
   would be legal but pointless. [model_ids] still lists them, for a caller that does want
   to retire them.

   Syntax notes, checked against veripb 2.2.2 (proof format 2.0) rather than taken
   from the doc:
     - [output NONE] is mandatory before [conclusion]; [conclusion] before [end].
     - deletion is [del id N M ...], not [del N M ...].
     - [#] is *not* a comment marker, it is the SetLevel rule and takes an integer.
       Only [*] introduces a comment. See the note in the final report.
     - [conclusion BOUNDS] is only accepted when the .opb carries an objective. *)

type cid = int

(* ---------------------------------------------------------------------------
   Cutting-planes expressions, reverse Polish.
   --------------------------------------------------------------------------- *)

module Pol = struct
  type t =
    | Id of cid
    | Axiom of Lit.t  (* the literal axiom  l >= 0 *)
    | Add of t * t
    | Mul of t * int
    | Div of t * int
    | Sat of t
    | Weaken of t * Lit.pbvar

  let id c = Id c
  let axiom l = Axiom l
  let add a b = Add (a, b)
  let mul a k =
    if k < 1 then invalid_arg "Pol.mul: multiplier must be >= 1"
    else if k = 1 then a
    else Mul (a, k)
  let div a k = if k < 1 then invalid_arg "Pol.div: divisor must be >= 1" else Div (a, k)
  let saturate a = Sat a
  (* VeriPB's weakening step ignores the sign of its argument, so it takes the
     variable, not a literal: [c x w] drops x's term and its coefficient from the
     degree. *)
  let weaken a v = Weaken (a, v)

  let sum = function
    | [] -> invalid_arg "Pol.sum: empty"
    | x :: rest -> List.fold_left add x rest

  (* sum of  a_i * c_i,  the shape almost every linear justification has. *)
  let lin_comb = function
    | [] -> invalid_arg "Pol.lin_comb: empty"
    | (k, c) :: rest ->
        List.fold_left (fun acc (k, c) -> add acc (mul (id c) k)) (mul (id c) k) rest

  let rec write b = function
    | Id c -> Buffer.add_string b (string_of_int c)
    | Axiom l -> Buffer.add_string b (Lit.to_string l)
    | Add (a, c) -> write b a; Buffer.add_char b ' '; write b c; Buffer.add_string b " +"
    | Mul (a, k) ->
        write b a;
        Buffer.add_string b (Printf.sprintf " %d *" k)
    | Div (a, k) ->
        write b a;
        Buffer.add_string b (Printf.sprintf " %d d" k)
    | Sat a -> write b a; Buffer.add_string b " s"
    | Weaken (a, v) ->
        write b a;
        Buffer.add_string b (Printf.sprintf " %s w" (Lit.var_name v))

  let to_string p =
    let b = Buffer.create 64 in
    write b p;
    Buffer.contents b
end

(* ---------------------------------------------------------------------------
   The writer.
   --------------------------------------------------------------------------- *)

type entry = { origin : string; level : int }

type t = {
  oc : out_channel;
  mutable next_id : cid;
  live : (cid, entry) Hashtbl.t;  (* id -> what introduced it, for audit failures *)
  model : (cid, unit) Hashtbl.t;  (* ids fixed by the .opb, not an obligation *)
  audit : bool;
  comments : bool;
  mutable level : int;
  mutable finished : bool;
}

let audit_enabled () =
  match Sys.getenv_opt "BAGUETTE_PROOF_AUDIT" with Some "1" -> true | _ -> false

let create ?(comments = false) ?audit oc =
  let audit = match audit with Some b -> b | None -> audit_enabled () in
  {
    oc;
    next_id = 0;
    live = Hashtbl.create 256;
    model = Hashtbl.create 64;
    audit;
    comments;
    level = 0;
    finished = false;
  }

let auditing t = t.audit
let last_id t = t.next_id
let live_count t = Hashtbl.length t.live
let live_ids t = Hashtbl.fold (fun id _ acc -> id :: acc) t.live [] |> List.sort compare
let is_live t id = Hashtbl.mem t.live id

(* The proof is append-only and is never rewound (invariant I-X4); once [conclusion]
   has run, nothing more may be written to it. *)
let is_finished t = t.finished

let line t fmt =
  if t.finished then invalid_arg "Writer: the proof has already ended";
  Printf.fprintf t.oc (fmt ^^ "\n")

(* Comments are the [*] rule. [#] is SetLevel, not a comment -- see the header. *)
let comment t fmt =
  if t.comments then Printf.fprintf t.oc ("* " ^^ fmt ^^ "\n")
  else Printf.ifprintf t.oc ("* " ^^ fmt ^^ "\n")

(* A comment that is emitted whether or not --proof-comments is on. Used for the
   few markers that make a proof navigable at all. *)
let always_comment t fmt = Printf.fprintf t.oc ("* " ^^ fmt ^^ "\n")

let fresh t ~origin =
  t.next_id <- t.next_id + 1;
  if t.audit then Hashtbl.replace t.live t.next_id { origin; level = t.level };
  t.next_id

(* Preamble: version line, then the count of model constraints loaded from the .opb. *)
let header t ~n_model_constraints =
  line t "pseudo-Boolean proof version 2.0";
  line t "f %d" n_model_constraints;
  (* The f rule makes the model constraints ids 1..n. *)
  t.next_id <- n_model_constraints;
  if t.audit then
    for i = 1 to n_model_constraints do
      Hashtbl.replace t.model i ()
    done

let model_ids t = Hashtbl.fold (fun id () acc -> id :: acc) t.model [] |> List.sort compare

(* ------------------------- deletion levels ------------------------------- *)

(* docs/PROOF-FORMAT.md section 5: reasons logged during search are retired on
   backtrack. VeriPB has a level stack for exactly this: [# l] puts subsequently
   derived constraints on level l, and [w l] wipes every constraint on level l and
   above. One [w] per backtrack beats one [del] per reason. *)
let set_level t l =
  if l < 0 then invalid_arg "Writer.set_level: negative level";
  line t "# %d" l;
  t.level <- l

let current_level t = t.level

let wipe_level t l =
  line t "w %d" l;
  if t.audit then begin
    let doomed =
      Hashtbl.fold
        (fun id (e : entry) acc -> if e.level >= l then id :: acc else acc)
        t.live []
    in
    List.iter (Hashtbl.remove t.live) doomed
  end
  (* VeriPB's LevelStack does not move the current level on a wipe, so neither do we:
     the mirror has to stay exact (invariant I-X3). *)

(* ------------------------------ rules ------------------------------------ *)

(* A cutting-planes derivation. *)
let pol t ~origin p =
  line t "pol %s" (Pol.to_string p);
  fresh t ~origin

(* Escape hatch for reverse-Polish text built elsewhere. Prefer [pol]. *)
let pol_raw t ~origin steps =
  line t "pol %s" steps;
  fresh t ~origin

(* Reverse unit propagation of a PB constraint. Prefer [pol] where the reasoning is
   known; see docs/PROOF-FORMAT.md section 2. *)
let rup t ~origin c =
  line t "rup %s" (Opb.constr_to_string c);
  fresh t ~origin

(* Reverse unit propagation of a clause -- the common case. *)
let rup_clause t ~origin lits = rup t ~origin (Opb.clause lits)

(* Redundance-based strengthening: used only to introduce definitions (direct-encoding
   channelling, reified variables). The witness maps variables to 0, 1 or a literal. *)
type witness_value = Zero | One | To of Lit.t

let witness_value_to_string = function
  | Zero -> "0"
  | One -> "1"
  | To l -> Lit.to_string l

let red t ~origin ~witness c =
  (match witness with [] -> invalid_arg "Writer.red: empty witness" | _ -> ());
  let w =
    String.concat " "
      (List.map
         (fun (v, value) ->
           Printf.sprintf "%s -> %s" (Lit.var_name v) (witness_value_to_string value))
         witness)
  in
  line t "red %s %s" (Opb.constr_to_string c) w;
  fresh t ~origin

(* ---------------------------- deletion ----------------------------------- *)

let forget t id =
  if t.audit then begin
    Hashtbl.remove t.live id;
    Hashtbl.remove t.model id
  end

let delete_many t ids =
  match ids with
  | [] -> ()
  | _ ->
      line t "del id %s" (String.concat " " (List.map string_of_int ids));
      List.iter (forget t) ids

let delete t id = delete_many t [ id ]

let delete_core t id =
  line t "delc id %d" id;
  forget t id

(* Move constraints into the core set (after an improving solution, M5). *)
let core t ids =
  match ids with
  | [] -> ()
  | _ -> line t "core id %s" (String.concat " " (List.map string_of_int ids))

(* ---------------------------- solutions ---------------------------------- *)

let lits_to_string lits = String.concat " " (List.map Lit.to_string lits)

(* [sol] records a solution and derives nothing. The assignment must propagate to a
   total assignment, so hand it every decision variable's literals. *)
let solution t lits = line t "sol %s" (lits_to_string lits)

(* [solx] records a solution *and* adds the clause excluding it; that clause is an
   id you own. *)
let solution_excluding t ~origin lits =
  line t "solx %s" (lits_to_string lits);
  fresh t ~origin

(* Improving solution for optimisation (M5). Adds the objective-bound constraint. *)
let improving t ~origin lits =
  line t "soli %s" (lits_to_string lits);
  fresh t ~origin

(* Objective update (M5). [diff] gives the change, [`New] the whole new objective. *)
let objective_update t ~origin kind terms =
  let body =
    String.concat " "
      (List.map (fun (a, l) -> Printf.sprintf "%+d %s" a (Lit.to_string l)) terms)
  in
  line t "obju %s %s ;" (match kind with `New -> "new" | `Diff -> "diff") body;
  fresh t ~origin

(* ----------------------------- audit ------------------------------------- *)

exception Audit_failed of string

let () =
  Printexc.register_printer (function
    | Audit_failed r -> Some ("proof audit failed (invariant I-X2)\n" ^ r)
    | _ -> None)

let audit_report t =
  let b = Buffer.create 256 in
  Buffer.add_string b
    (Printf.sprintf "proof audit: %d constraint id(s) never deleted (invariant I-X2)\n"
       (Hashtbl.length t.live));
  List.iter
    (fun id ->
      let (e : entry) = Hashtbl.find t.live id in
      Buffer.add_string b (Printf.sprintf "  id %d from %s (level %d)\n" id e.origin e.level))
    (live_ids t);
  Buffer.contents b

let check_audit t =
  if t.audit && Hashtbl.length t.live > 0 then begin
    (* No printing here: the exception carries the report and has a printer, so a
       solver that lets it escape still shows it, and a test that expects it is not
       forced to swallow stderr. *)
    raise (Audit_failed (audit_report t))
  end

(* --------------------------- conclusion ---------------------------------- *)

type verdict =
  | Sat of Lit.t list
      (* The satisfying assignment. [] falls back on a previously logged [sol],
         which the checker only accepts when deletion checking is on; passing the
         assignment is the form that always works. *)
  | Unsat of cid option
      (* The id of the derived contradiction. [None] makes the checker search the
         database for one -- accepted, but it is work we can spare it, and under the
         audit an undeleted contradiction id would fail I-X2 anyway. *)
  | Bounds of {
      lower : int;
      lower_id : cid option;  (* the constraint that establishes the lower bound *)
      upper : int option;  (* None is INF: no solution was found *)
      upper_assignment : Lit.t list;
    }

(* [output NONE] is required by the checker before [conclusion]; the doc's rule table
   does not mention it. NONE is the honest guarantee: we do not emit an output
   formula, so we claim nothing about one. *)
let conclusion ?(output = "NONE") t v =
  line t "output %s" output;
  (match v with
  | Sat [] -> line t "conclusion SAT"
  | Sat lits -> line t "conclusion SAT : %s" (lits_to_string lits)
  | Unsat None -> line t "conclusion UNSAT"
  | Unsat (Some id) ->
      line t "conclusion UNSAT : %d" id;
      forget t id
  | Bounds { lower; lower_id; upper; upper_assignment } ->
      let b = Buffer.create 64 in
      Buffer.add_string b (Printf.sprintf "conclusion BOUNDS %d" lower);
      (match lower_id with
      | Some id ->
          Buffer.add_string b (Printf.sprintf " : %d" id);
          forget t id
      | None -> ());
      Buffer.add_string b
        (match upper with None -> " INF" | Some u -> Printf.sprintf " %d" u);
      if upper <> None && upper_assignment <> [] then
        Buffer.add_string b (Printf.sprintf " : %s" (lits_to_string upper_assignment));
      line t "%s" (Buffer.contents b));
  line t "end pseudo-Boolean proof";
  t.finished <- true;
  flush t.oc;
  check_audit t
