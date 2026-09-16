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

   This module emits TWO formats -- see [type format] below, D-0023, and
   docs/PROOF-FORMAT.md sections 2 and 2a. They are separate grammars, and every
   difference between them was found by running a checker, not by reading a spec.

   Syntax notes for 2.0, checked against veripb 2.2.2:
     - [output NONE] is mandatory before [conclusion]; [conclusion] before [end].
     - deletion is [del id N M ...], not [del N M ...].
     - [#] is *not* a comment marker, it is the SetLevel rule and takes an integer.
       Only [*] introduces a comment. See the note in the final report.
     - [conclusion BOUNDS] is only accepted when the .opb carries an objective.

   And for 3.0, checked against veripb 3.0.2:
     - every rule ends in [;]; [rup] already does and must not get a second.
     - comments are [%]; [*] is refused outright.
     - [red]'s witness follows a [:], before the terminator.
     - [#] and [w] DO NOT EXIST. See [wipe_level] and D-0024.
     - constraints carry [@label]s and are cited by name, never by number. *)

type cid = int

(* ---------------------------------------------------------------------------
   Cutting-planes expressions, reverse Polish.
   --------------------------------------------------------------------------- *)

module Pol = struct
  type t =
    | Id of cid
    | Axiom of Lit.t (* the literal axiom  l >= 0 *)
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
    | Add (a, c) ->
        write b a;
        Buffer.add_char b ' ';
        write b c;
        Buffer.add_string b " +"
    | Mul (a, k) ->
        write b a;
        Buffer.add_string b (Printf.sprintf " %d *" k)
    | Div (a, k) ->
        write b a;
        Buffer.add_string b (Printf.sprintf " %d d" k)
    | Sat a ->
        write b a;
        Buffer.add_string b " s"
    | Weaken (a, v) ->
        write b a;
        Buffer.add_string b (Printf.sprintf " %s w" (Lit.var_name v))

  let to_string p =
    let b = Buffer.create 64 in
    write b p;
    Buffer.contents b

  (* The same, with constraint references rendered by [cite] instead of as integers.
     VeriPB 3.0 lets a `pol` name its operands (`pol @c7 @c9 +`), which is the whole
     point of D-0023: an id our counter got wrong is then a hard "label not assigned"
     error rather than a silently different constraint. *)
  let rec write_cited b cite = function
    | Id c -> Buffer.add_string b (cite c)
    | Axiom l -> Buffer.add_string b (Lit.to_string l)
    | Add (a, c) ->
        write_cited b cite a;
        Buffer.add_char b ' ';
        write_cited b cite c;
        Buffer.add_string b " +"
    | Mul (a, k) ->
        write_cited b cite a;
        Buffer.add_string b (Printf.sprintf " %d *" k)
    | Div (a, k) ->
        write_cited b cite a;
        Buffer.add_string b (Printf.sprintf " %d d" k)
    | Sat a ->
        write_cited b cite a;
        Buffer.add_string b " s"
    | Weaken (a, v) ->
        write_cited b cite a;
        Buffer.add_string b (Printf.sprintf " %s w" (Lit.var_name v))

  let to_string_cited ~cite p =
    let b = Buffer.create 64 in
    write_cited b cite p;
    Buffer.contents b
end

(* ---------------------------------------------------------------------------
   Which proof format to emit.

   3.0 is what ships (M1-T19); 2.0 is still emitted on request, with
   BAGUETTE_PROOF_FORMAT=2.0 or [create ~format:V2_0], and the whole suite is green
   under both. They are NOT dialects of one another -- see D-0023 and
   docs/PROOF-FORMAT.md section 2a. The differences that matter here:

     - every rule is terminated by `;`
     - comments are `%`, not `*`
     - `#` (set level) and `w` (wipe level) DO NOT EXIST. The level stack this
       project's backtracking is built on (D-0008) is gone, and the writer has to
       keep the tags itself and delete explicitly.
     - `red`'s witness follows a `:`, before the terminator, not a `;`
     - `delc` drops its `id` keyword
     - constraints may be labelled `@name` and cited by name
     - veripb 2.2.2 cannot read a 3.0 proof at all ("Unsupported version"), so this
       is a one-way switch for every consumer of a proof at once.
   --------------------------------------------------------------------------- *)

type format = V2_0 | V3_0

let format_to_string = function V2_0 -> "2.0" | V3_0 -> "3.0"

let format_of_string = function
  | "2.0" | "2" -> Some V2_0
  | "3.0" | "3" -> Some V3_0
  | _ -> None

(* ---------------------------------------------------------------------------
   The writer.
   --------------------------------------------------------------------------- *)

type entry = { origin : string; level : int }

type t = {
  oc : out_channel;
  fmt : format;
  mutable next_id : cid;
  live : (cid, entry) Hashtbl.t; (* id -> what introduced it, for audit failures *)
  model : (cid, unit) Hashtbl.t; (* ids fixed by the .opb, not an obligation *)
  tags : (cid, int) Hashtbl.t;
      (* 3.0 only, and always on there rather than under [audit]: the level each live
         derived id was tagged with. In 2.0 the checker keeps this and [w] consults
         it; 3.0 has no level stack, so [wipe_level] has to reproduce `w l` from this
         table. It is a mirror of checker state (invariant I-X3) and stops being
         optional the moment the checker stops holding it. *)
  audit : bool;
  comments : bool;
  mutable level : int;
  mutable finished : bool;
}

let audit_enabled () =
  match Sys.getenv_opt "BAGUETTE_PROOF_AUDIT" with Some "1" -> true | _ -> false

(* BAGUETTE_PROOF_FORMAT=3.0 switches emission, the same way BAGUETTE_PROOF_AUDIT
   switches the audit. An unrecognised value is an error rather than a silent 2.0:
   a typo that quietly emitted the format you were trying to leave is exactly the
   kind of "green for the wrong reason" this project keeps finding. *)
let format_from_env () =
  match Sys.getenv_opt "BAGUETTE_PROOF_FORMAT" with
  | None | Some "" -> V3_0
  | Some s -> (
      match format_of_string (String.trim s) with
      | Some f -> f
      | None ->
          invalid_arg
            (Printf.sprintf
               "BAGUETTE_PROOF_FORMAT=%S is not a proof format this writer emits. Use \
                2.0 or 3.0."
               s))

(* The format a writer gets when nobody says otherwise. Read once: the .opb has to be
   written before the proof exists (invariant I-X5) and has to agree with it about
   labelling, so [Encoding.write_opb] consults this before any writer is created. *)
let default_format =
  let cached = ref None in
  fun () ->
    match !cached with
    | Some f -> f
    | None ->
        let f = format_from_env () in
        cached := Some f;
        f

let create ?(comments = false) ?audit ?format oc =
  let audit = match audit with Some b -> b | None -> audit_enabled () in
  let fmt = match format with Some f -> f | None -> default_format () in
  {
    oc;
    fmt;
    next_id = 0;
    live = Hashtbl.create 256;
    model = Hashtbl.create 64;
    tags = Hashtbl.create 256;
    audit;
    comments;
    level = 0;
    finished = false;
  }

let format t = t.fmt
let v3 t = t.fmt = V3_0

(* How a constraint is referred to. In 3.0 every constraint -- model rows included,
   via Opb.label_of -- carries the label `@c<id>`, so nothing in an emitted proof is
   a bare integer any more. *)
let cite t id = if v3 t then Opb.label_of id else string_of_int id
let cite_all t ids = String.concat " " (List.map (cite t) ids)
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

(* A rule, terminated the way the format wants. 3.0 ends every rule with `;`; 2.0
   ends it at the newline. Rules whose body already carries a `;` -- [rup] and the
   OPB constraint rendering it uses -- go through [line] directly: a second one is a
   syntax error in 3.0. *)
let rule t body = if v3 t then line t "%s ;" body else line t "%s" body

(* The label a rule that YIELDS an id is prefixed with, so later rules can cite it by
   name. Empty in 2.0. [sol] must not get one: VeriPB 3.0 says in as many words that
   "the rule `sol` cannot be prefixed with a label", and it is right -- it yields
   nothing to name. *)
let label_for t id = if v3 t then Opb.label_of id ^ " " else ""

(* Comments. 2.0 spells them [*]; 3.0 spells them [%] and rejects [*] outright
   ("Expected a top level rule name"). [#] is a comment in neither: in 2.0 it is
   SetLevel, in 3.0 it introduces a proofgoal id. *)
let comment_char t = if v3 t then '%' else '*'

let comment t fmt =
  if t.comments then Printf.fprintf t.oc ("%c " ^^ fmt ^^ "\n") (comment_char t)
  else Printf.ifprintf t.oc ("%c " ^^ fmt ^^ "\n") (comment_char t)

(* A comment that is emitted whether or not --proof-comments is on. Used for the
   few markers that make a proof navigable at all. *)
let always_comment t fmt = Printf.fprintf t.oc ("%c " ^^ fmt ^^ "\n") (comment_char t)

let fresh t ~origin =
  t.next_id <- t.next_id + 1;
  if t.audit then Hashtbl.replace t.live t.next_id { origin; level = t.level };
  if v3 t then Hashtbl.replace t.tags t.next_id t.level;
  t.next_id

(* Preamble: version line, then the count of model constraints loaded from the .opb.

   The count is NOT the trap PROOF-FORMAT section 2 used to describe it as. Both
   checkers reject a wrong one outright and name the right number ("The formula
   contains 3 constraints, but the rule expected that there are 2"), measured on
   both. What used to be silent was the *consequence* of miscounting inside
   [Encoding] -- a `pol` citing a shifted id. In 3.0 that is gone too: citations are
   labels. *)
let header t ~n_model_constraints =
  line t "pseudo-Boolean proof version %s" (format_to_string t.fmt);
  rule t (Printf.sprintf "f %d" n_model_constraints);
  (* The f rule makes the model constraints ids 1..n. *)
  t.next_id <- n_model_constraints;
  if t.audit then
    for i = 1 to n_model_constraints do
      Hashtbl.replace t.model i ()
    done

let model_ids t =
  Hashtbl.fold (fun id () acc -> id :: acc) t.model [] |> List.sort compare

(* ------------------------- deletion levels ------------------------------- *)

(* docs/PROOF-FORMAT.md section 5: reasons logged during search are retired on
   backtrack. VeriPB has a level stack for exactly this: [# l] puts subsequently
   derived constraints on level l, and [w l] wipes every constraint on level l and
   above. One [w] per backtrack beats one [del] per reason. *)
let set_level t l =
  if l < 0 then invalid_arg "Writer.set_level: negative level";
  (* 3.0 has no SetLevel rule -- `#` there introduces a proofgoal id and `# 1` is a
     parse error. The level is still real; it is just ours to carry now, so record it
     and leave a comment where the marker used to be. That comment is emitted
     unconditionally: without it a 3.0 proof has nothing in it that says where a
     decision began, and the proofs in this project are read by hand. *)
  if v3 t then always_comment t "level %d" l else line t "# %d" l;
  t.level <- l

let current_level t = t.level

(* ------------------------------------------------------------------ reading it back

   [set_level] is the only thing that writes a level marker, so the spelling belongs
   here rather than in each test that greps a proof for it. The reason this is a
   function and not a convention: a test that hard-codes `# 1` does not FAIL when the
   default flips to 3.0 -- it finds nothing, and an assertion of the form
   `not (contains "# 1" proof)` passes vacuously. A test that has silently stopped
   testing is worse than a red one, and the 3.0 flip turned up five of them.

   Both spellings are recognised whatever the active format, so these cannot go stale
   the next time the default moves. *)

(* A proof line with its 3.0 label removed: `@c17 rup ... ;` becomes `rup ... ;`.

   Tests that pin what a rule SAYS want the body; the label is the constraint's name,
   which 2.0 does not have and which the checker verifies for them (a citation of a
   name that was never bound is a parse error, which is the whole point of D-0023's
   labels). Stripping it here keeps such an assertion meaning the same thing in both
   formats instead of meaning nothing in one of them. *)
let strip_label line =
  if String.length line > 0 && line.[0] = '@' then
    match String.index_opt line ' ' with
    | Some i -> String.sub line (i + 1) (String.length line - i - 1)
    | None -> line
  else line

(* The rule's text with its 3.0 decoration removed: label off the front, terminator
   off the back. This is the projection a pin on "what this step says" wants -- 3.0
   terminates every rule, so a `pol` that read `pol 3 4 + 2 d` in 2.0 reads
   `@c17 pol 3 4 + 2 d ;` now, while saying exactly the same thing. (A `rup` carries
   its own `;` in both formats, as part of the constraint syntax rather than as the
   rule terminator, so it is unaffected either way.) *)
let rule_body line =
  let l = String.trim (strip_label line) in
  let n = String.length l in
  if n >= 1 && l.[n - 1] = ';' then String.trim (String.sub l 0 (n - 1)) else l

let level_marker fmt l =
  match fmt with
  | V2_0 -> Printf.sprintf "# %d" l
  | V3_0 -> Printf.sprintf "%% level %d" l

(* [Some l] when [line] is a level marker in either format. 2.0 writes the SetLevel
   rule `# l`; 3.0 has no such rule (D-0024) and [set_level] leaves `% level l`. *)
let level_of_line line =
  let line = String.trim line in
  let has p =
    String.length line >= String.length p && String.sub line 0 (String.length p) = p
  in
  let num_after k =
    int_of_string_opt (String.trim (String.sub line k (String.length line - k)))
  in
  if has "# " then num_after 2 else if has "% level " then num_after 8 else None

(* Does [proof] open decision level [l]? *)
let opens_level l proof =
  List.exists (fun line -> level_of_line line = Some l) (String.split_on_char '\n' proof)

(* Compress a sorted id list into maximal runs, so a backtrack is one `del range`
   line in the common case instead of one id per retired reason. Contiguity is the
   common case exactly because ids are handed out in order and a level's constraints
   are derived consecutively.

   A run is INCLUSIVE of both ends: [(3, 5)] means the ids 3, 4 and 5. `del range`
   is not -- see [del_run] below, which is where the two conventions meet. *)
let runs ids =
  let rec go acc lo hi = function
    | [] -> List.rev ((lo, hi) :: acc)
    | x :: rest when x = hi + 1 -> go acc lo x rest
    | x :: rest -> go ((lo, hi) :: acc) x x rest
  in
  match ids with [] -> [] | x :: rest -> go [] x x rest

(* The deletion rule that retires exactly the inclusive run [lo, hi] and nothing else.

   **`del range LO HI` deletes the HALF-OPEN span [LO, HI)**: the constraint named by
   HI survives. That is not a reading of a grammar, it is measured against VeriPB
   3.0.2 -- the checker of record -- and it is pinned by [test_v3_del_range_semantics]
   in test/unit/test_proof.ml, which runs the checker rather than asserting our own
   text. M1-T22: we emitted `del range lo hi` for an inclusive run, so every run of
   two or more ids left its last id live in the checker while [t.tags] and (under
   audit) [t.live] had already dropped it -- the I-X3 mirror disagreeing with the
   thing it mirrors. Not unsound; the proof simply kept a constraint it believed gone.

   So the run [lo, hi] is written `del range <lo> <hi+1>`, and there is a catch: in
   3.0 every reference is a LABEL, and an unbound label is a hard parse error --
   "The label `@c9` is not assigned to a constraint ID". When [hi] is the newest id
   the writer has handed out there is no `@c(hi+1)` yet, so the range cannot name its
   own upper bound and the run goes out as an explicit `del id` list instead. That is
   still ONE line -- `del id` takes a list -- it is only longer. Both shapes delete
   the same set; the fallback is about what can be spelled, not about semantics.

   The hi+1 label may itself already be deleted (a lower-level run retired it
   earlier). That is fine and is measured too: a deleted label still resolves, and
   `del range` tolerates already-deleted ids inside the span. *)
let del_run t (lo, hi) =
  if lo = hi then rule t (Printf.sprintf "del id %s" (cite t lo))
  else if hi < t.next_id then
    rule t (Printf.sprintf "del range %s %s" (cite t lo) (cite t (hi + 1)))
  else
    rule t
      (Printf.sprintf "del id %s"
         (cite_all t (List.init (hi - lo + 1) (fun k -> lo + k))))

let wipe_level t l =
  if v3 t then (
    (* VeriPB 3.0 deleted the level stack that D-0008 built backtracking on. `w l`
       retired every constraint TAGGED at level >= l, and the checker held the tags;
       now [t.tags] does, so the same set is computed here and deleted explicitly.
       This reproduces `w l` exactly -- it is not "delete what was derived since",
       which would be wrong the moment a level is re-entered after a `# 0` interlude
       (search does exactly that: `# 1`, `# 0`, two root prunings, `# 1` again).

       The cost is honest and belongs in the record: PROOF-FORMAT section 5's whole
       argument for levels was one proof line per backtrack rather than one deletion
       per reason, and that argument is gone. Runs recover most of it -- a level's
       ids are usually consecutive, so it is usually still one line -- but "usually"
       is not "always" and the proof now grows with the number of retired reasons in
       the worst case. See D-0024.

       [del_run] is what turns an inclusive run into a rule; `del range` is half-open
       and that difference is the whole of M1-T22. *)
    let doomed =
      Hashtbl.fold (fun id lv acc -> if lv >= l then id :: acc else acc) t.tags []
      |> List.sort compare
    in
    List.iter (Hashtbl.remove t.tags) doomed;
    List.iter (del_run t) (runs doomed))
  else line t "w %d" l;
  if t.audit then
    let doomed =
      Hashtbl.fold
        (fun id (e : entry) acc -> if e.level >= l then id :: acc else acc)
        t.live []
    in
    List.iter (Hashtbl.remove t.live) doomed
(* VeriPB's LevelStack does not move the current level on a wipe, so neither do we:
   the mirror has to stay exact (invariant I-X3). *)

(* ------------------------------ rules ------------------------------------ *)

(* Every rule below that yields an id takes its label from the id it is ABOUT to be
   given, so [fresh] has to run first and the body is written afterwards. *)
let emit_yielding t ~origin body_of_id =
  let id = t.next_id + 1 in
  rule t (label_for t id ^ body_of_id id);
  let id' = fresh t ~origin in
  assert (id = id');
  id

(* A cutting-planes derivation. *)
let pol t ~origin p =
  emit_yielding t ~origin (fun _ ->
      "pol " ^ if v3 t then Pol.to_string_cited ~cite:(cite t) p else Pol.to_string p)

(* Escape hatch for reverse-Polish text built elsewhere. Prefer [pol]. *)
let pol_raw t ~origin steps = emit_yielding t ~origin (fun _ -> "pol " ^ steps)

(* Reverse unit propagation of a PB constraint. Prefer [pol] where the reasoning is
   known; see docs/PROOF-FORMAT.md section 2.

   The body already ends in " ;" (Opb.constr_to_string), which is the 3.0 terminator,
   so this goes through [line] rather than [rule]: `rup ... ; ;` is a syntax error. *)
let rup t ~origin c =
  let id = t.next_id + 1 in
  line t "%srup %s" (label_for t id) (Opb.constr_to_string c);
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
  (* 2.0: `red <constraint> ; <witness>` -- the witness follows the constraint's own
     terminator. 3.0: `red <constraint> : <witness> ;` -- the rule ends at the first
     `;`, so a witness written after one is silently not a witness, and the checker
     says "A witness must be specified for the red-rule". Measured both ways. *)
  let id = t.next_id + 1 in
  if v3 t then line t "%sred %s : %s ;" (label_for t id) (Opb.constr_body c) w
  else line t "red %s %s" (Opb.constr_to_string c) w;
  fresh t ~origin

(* ---------------------------- deletion ----------------------------------- *)

let forget t id =
  if t.audit then (
    Hashtbl.remove t.live id;
    Hashtbl.remove t.model id)

let delete_many t ids =
  match ids with
  | [] -> ()
  | _ ->
      rule t (Printf.sprintf "del id %s" (cite_all t ids));
      if v3 t then List.iter (Hashtbl.remove t.tags) ids;
      List.iter (forget t) ids

let delete t id = delete_many t [ id ]

(* 3.0 drops the `id` keyword from [delc] and takes the constraint reference directly
   ("Expected a constraint ID (label or signed integer) ... but found `id`"). [del]
   and [core] keep theirs. Measured; there is no pattern to infer. *)
let delete_core t id =
  rule t
    (if v3 t then Printf.sprintf "delc %s" (cite t id) else Printf.sprintf "delc id %d" id);
  if v3 t then Hashtbl.remove t.tags id;
  forget t id

(* Move constraints into the core set (after an improving solution, M5). *)
let core t ids =
  match ids with [] -> () | _ -> rule t (Printf.sprintf "core id %s" (cite_all t ids))

(* ---------------------------- solutions ---------------------------------- *)

let lits_to_string lits = String.concat " " (List.map Lit.to_string lits)

(* [sol] records a solution and derives nothing. The assignment must propagate to a
   total assignment, so hand it every decision variable's literals. *)
let solution t lits = rule t (Printf.sprintf "sol %s" (lits_to_string lits))

(* [solx] records a solution *and* adds the clause excluding it; that clause is an
   id you own.

   NOT USABLE IN 3.0 as it stands: "Logging and excluding a solution with 'solx' is
   only possible if a preserved set is specified". 3.0 ties solution exclusion to the
   `preserved` machinery, which this project has no encoding for. Nothing in M1 emits
   it; enumeration (and M5's `soli`, untested here) will have to face this. *)
let solution_excluding t ~origin lits =
  let id = t.next_id + 1 in
  rule t (Printf.sprintf "%ssolx %s" (label_for t id) (lits_to_string lits));
  fresh t ~origin

(* Improving solution for optimisation (M5). Adds the objective-bound constraint. *)
let improving t ~origin lits =
  let id = t.next_id + 1 in
  rule t (Printf.sprintf "%ssoli %s" (label_for t id) (lits_to_string lits));
  fresh t ~origin

(* Objective update (M5). [diff] gives the change, [`New] the whole new objective. *)
let objective_update t ~origin kind terms =
  let body =
    String.concat " "
      (List.map (fun (a, l) -> Printf.sprintf "%+d %s" a (Lit.to_string l)) terms)
  in
  (* Already `;`-terminated, so 3.0 needs no second one -- but 3.0 does demand an
     explicit subproof for the proofgoals an objective update raises ("Proofgoal #1
     could not be autoproven"), which this does not emit. M5 territory; recorded in
     D-0023 as measured-and-not-solved rather than left to be discovered. *)
  let id = t.next_id + 1 in
  line t "%sobju %s %s ;" (label_for t id)
    (match kind with `New -> "new" | `Diff -> "diff")
    body;
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
      Buffer.add_string b
        (Printf.sprintf "  id %d from %s (level %d)\n" id e.origin e.level))
    (live_ids t);
  Buffer.contents b

let check_audit t =
  if t.audit && Hashtbl.length t.live > 0 then
    (* No printing here: the exception carries the report and has a printer, so a
       solver that lets it escape still shows it, and a test that expects it is not
       forced to swallow stderr. *)
    raise (Audit_failed (audit_report t))

(* --------------------------- conclusion ---------------------------------- *)

type verdict =
  | Sat of Lit.t list
    (* The satisfying assignment. It is logged with [sol] and the conclusion is the
       bare [conclusion SAT]; [] skips the [sol] and relies on one logged earlier.

       Not the inline [conclusion SAT : <assignment>] form, and that is M1-T18's
       finding rather than a style preference. The assignment we have is over the
       *model* variables only -- the order-encoding families of the FlatZinc
       variables. The .opb also carries encoding auxiliaries (the [_neN] selectors of
       PROOF-FORMAT section 3), and nothing in the solver knows what they should be.
       veripb 2.2.2 unit-propagates the inline assignment and fills them in; veripb
       3.0.2 does not -- "the solution given for the conclusion is not propagated" --
       and reads every unmentioned variable as false, so a model needing a selector
       true has its honest proof REJECTED. test/models/ne_conflict_sat.fzn is such a
       model and was the single disagreement between the two checkers.

       A solution logged with [sol] *is* propagated, by both. Measured, not argued:
       the checker's own hint says "if the solution should be propagated, then log
       the solution inside the proof". [solx] is not an alternative -- 3.0.2 refuses
       it outside a preserved set. *)
  | Unsat of cid option
    (* The id of the derived contradiction. [None] makes the checker search the
       database for one -- accepted, but it is work we can spare it, and under the
       audit an undeleted contradiction id would fail I-X2 anyway. *)
  | Bounds of {
      lower : int;
      lower_id : cid option; (* the constraint that establishes the lower bound *)
      upper : int option; (* None is INF: no solution was found *)
      upper_assignment : Lit.t list;
    }

(* [output NONE] is required by the checker before [conclusion]; the doc's rule table
   does not mention it. NONE is the honest guarantee: we do not emit an output
   formula, so we claim nothing about one. *)
let conclusion ?(output = "NONE") t v =
  (* [sol] first: it is a derivation rule and [output] must be the line immediately
     before [conclusion] (SPEC section 4.3). *)
  (match v with Sat (_ :: _ as lits) -> solution t lits | _ -> ());
  rule t (Printf.sprintf "output %s" output);
  (match v with
  | Sat _ -> rule t "conclusion SAT"
  | Unsat None -> rule t "conclusion UNSAT"
  | Unsat (Some id) ->
      rule t (Printf.sprintf "conclusion UNSAT : %s" (cite t id));
      forget t id
  | Bounds { lower; lower_id; upper; upper_assignment } ->
      let b = Buffer.create 64 in
      Buffer.add_string b (Printf.sprintf "conclusion BOUNDS %d" lower);
      (match lower_id with
      | Some id ->
          Buffer.add_string b (Printf.sprintf " : %s" (cite t id));
          forget t id
      | None -> ());
      Buffer.add_string b
        (match upper with None -> " INF" | Some u -> Printf.sprintf " %d" u);
      if upper <> None && upper_assignment <> [] then
        Buffer.add_string b (Printf.sprintf " : %s" (lits_to_string upper_assignment));
      rule t (Buffer.contents b));
  rule t "end pseudo-Boolean proof";
  t.finished <- true;
  flush t.oc;
  check_audit t
