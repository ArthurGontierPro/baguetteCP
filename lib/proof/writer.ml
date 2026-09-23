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

   This module emits ONE format: VeriPB 3.0, checked against veripb 3.0.2, the sole
   checker of record. D-0046 removed format 2.0 and the BAGUETTE_PROOF_FORMAT switch;
   docs/PROOF-FORMAT.md section 2a is the rule contract, and its section 2 survives
   only as the historical record of what 2.0 did. Every syntax note below was found by
   running the checker, not by reading a spec:
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

  (* Constraint references are rendered by [cite], never as bare integers: VeriPB 3.0
     lets a `pol` name its operands (`pol @c7 @c9 +`), which is the whole point of
     D-0023 -- an id our counter got wrong is then a hard "label not assigned" error
     rather than a silently different constraint. The positional rendering this used to
     sit beside went with format 2.0 (D-0046); there is no unlabelled `pol` any more. *)
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
   The format this writer emits.

   VeriPB 3.0, and only 3.0 (D-0046; M1-T19 made it the default, D-0025 made it the
   checker of record). The shape of the grammar, kept here because every one of these
   is a thing the writer does differently from the 2.0 this project used to emit, and
   the reasoning for each survives in docs/PROOF-FORMAT.md section 2a and D-0023/24:

     - every rule is terminated by `;`
     - comments are `%`; `*` is refused outright
     - `#` (set level) and `w` (wipe level) DO NOT EXIST. The level stack this
       project's backtracking is built on (D-0008) is not the checker's any more, so
       the writer keeps the tags itself and deletes explicitly ([wipe_level], D-0024).
     - `red`'s witness follows a `:`, before the terminator
     - `delc` takes its constraint reference directly, with no `id` keyword
     - constraints carry `@name` labels and are cited by name, never by number.
   --------------------------------------------------------------------------- *)

let proof_version = "3.0"

(* ---------------------------------------------------------------------------
   The writer.
   --------------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------------
   Deliberate corruption: the mutation knobs (M1-T26).

   The mutation gate exists to show that a derivation is load-bearing: corrupt one
   step and the checker must reject. Until M1-T26 the corruption was applied to the
   emitted *text*, by awk, in scripts/mutate_proof.sh. That harness had to re-derive
   from the text what this module already knew -- which token of a `pol` is a
   coefficient and which is a constraint reference, which ids are still live, which
   claim was emitted under a decision -- and it got one of them structurally wrong:
   every derived constraint carries a label and is cited by it, so
   *deleting* a step un-defines that label and the later citation fails to PARSE. The
   checker rejects, the lane goes green, and nothing about the derivation was tested.
   That is D-0020's failure mode, and it is not fixable in awk: the information
   needed to avoid it is here, not in the output.

   So the knobs are typed and sit next to the derivation, GCS-style. A knob names a
   [kind] of corruption and a [site]; the site is matched against the [~origin] every
   rule emission already carries ("combine(2 summand(s), / 1)", "trace: y_ge_2 from
   3 fact(s)"), so a lane says which derivation it is corrupting instead of hunting
   for it in the text.

   HOW A KNOB IS PREVENTED FROM FIRING IN A NORMAL RUN. Five things, and none of
   them is a convention:

   1. [mutation] is NOT mutable. A writer's corruption status is fixed when it is
      created and there is no setter, so no code path can turn a live writer into a
      corrupting one.
   2. [create] takes no mutation argument at all and always builds [None]. The only
      way to obtain a corrupting writer is [create_mutated], which *requires* a
      [Mutation.t]: there is no default, and no way to ask for one by accident.
   3. [create_mutated] consults NO environment variable and no global. Compare
      [audit] (BAGUETTE_PROOF_AUDIT), which is deliberately switchable from outside
      the program; this deliberately is not. Nothing outside an OCaml call site can
      turn it on.
   4. Nothing in lib/ or bin/ names [create_mutated]. test/unit/test_mutation.ml
      asserts that by grepping the tree, so the day a propagator "temporarily" reaches
      for it the mutation suite goes red.
   5. Every corrupted proof says so in its own text: [header] emits an unconditional
      `DELIBERATELY CORRUPTED` comment naming the knob. A corrupted proof can
      therefore never be mistaken for a real one, by a human or by a grep.

   At most ONE corruption is applied per proof ([mutation_note] latches), because a
   lane that changed two things does not say which one the checker objected to.

   A knob that finds no site does NOT silently emit a clean proof and let the lane
   read the checker's "accepted" as slack: [mutation_fired] reports whether it fired
   and the caller must fail the lane when it did not. That is the same rule as the
   script's exit 3, moved into a value. *)

module Mutation = struct
  type kind =
    | Perturb_coefficient
      (* `pol`: the first divisor `N d` becomes `N+1 d`, else the first multiplier
         `N *` becomes `N+1 *`, else the first literal axiom -- which is the
         coefficient 1 -- is doubled. The text knob `pol-coeff`, typed. *)
    | Swap_citation
      (* `pol`: the first constraint reference is replaced by a DIFFERENT one that is
         still live and not already cited in the same step. The writer knows the live
         set exactly ([tags] plus the model rows), so unlike the text knob this cannot
         swap in a retired id and score a rejection that is really "that id is gone". *)
    | Truncate_derivation
      (* `pol`: keep only the leftmost operand and throw the rest of the derivation
         away. The step still yields its id and still BINDS ITS LABEL, so every later
         citation parses and the checker has to judge the derivation rather than the
         grammar. This is what the text knob `drop-line` was trying to be and cannot
         be under 3.0 -- see the note above, and M1-T26's table. *)
    | Drop_literal
      (* `rup`/`red`: drop the last term of the claim. Refused outright on a claim with
         fewer than two terms: dropping the only literal corrupts the CLAIM rather than
         the reason behind it, and a lane that does that says nothing about the reason
         (GCS dev_docs/constraints.md:1085). The refusal shows up as "did not fire". *)
    | Strengthen_rhs
  (* `rup`/`red`: raise the degree by one, which strengthens the claim. Lowering it
     weakens the claim, which usually still checks and is therefore not a test. *)

  type t = {
    kind : kind;
    site : string;
        (* matched as a substring of a rule's [~origin]; "" matches any origin *)
    occurrence : int; (* 1-based, over the sites the knob can actually corrupt *)
  }

  let kind_name = function
    | Perturb_coefficient -> "perturb-coefficient"
    | Swap_citation -> "swap-citation"
    | Truncate_derivation -> "truncate-derivation"
    | Drop_literal -> "drop-literal"
    | Strengthen_rhs -> "strengthen-rhs"

  let all_kinds =
    [
      Perturb_coefficient;
      Swap_citation;
      Truncate_derivation;
      Drop_literal;
      Strengthen_rhs;
    ]

  (* Which rule a knob can corrupt. A knob is never applied to a rule it does not
     name: that is what stops "drop a literal" quietly doing nothing to a `pol` and
     the lane reading the resulting clean proof as a finding. *)
  let corrupts_pol = function
    | Perturb_coefficient | Swap_citation | Truncate_derivation -> true
    | Drop_literal | Strengthen_rhs -> false

  let corrupts_claim = function
    | Drop_literal | Strengthen_rhs -> true
    | Perturb_coefficient | Swap_citation | Truncate_derivation -> false

  let make ?(occurrence = 1) ~site kind =
    if occurrence < 1 then
      invalid_arg "Writer.Mutation.make: occurrence is 1-based and must be >= 1";
    { kind; site; occurrence }

  let describe m =
    Printf.sprintf "%s at site %S, occurrence %d" (kind_name m.kind) m.site m.occurrence
end

type entry = { origin : string; level : int }

type t = {
  oc : out_channel;
  mutable next_id : cid;
  live : (cid, entry) Hashtbl.t; (* id -> what introduced it, for audit failures *)
  model : (cid, unit) Hashtbl.t; (* ids fixed by the .opb, not an obligation *)
  objective : (cid, entry) Hashtbl.t;
      (* M5-T1: the objective-improving constraints `soli` handed back. Not an
         obligation either, and for a sharper reason than [model]'s -- these are ids we
         DID receive, and deleting one is an unchecked deletion that weakens the
         checker's guarantee over the conclusion that follows it. See [improving]. *)
  tags : (cid, int) Hashtbl.t;
      (* Always on, rather than under [audit]: the level each live derived id was
         tagged with. VeriPB 3.0 has no level stack -- the checker used to keep this
         and `w` used to consult it (D-0024) -- so [wipe_level] reproduces `w l` from
         this table. It is a mirror of checker state (invariant I-X3) and stopped being
         optional the moment the checker stopped holding it. *)
  audit : bool;
  comments : bool;
  mutable level : int;
  mutable finished : bool;
  mutable n_model : int;
      (* how many constraints [f] loaded, so ids 1..n_model are the model rows. Kept
         because [Swap_citation] needs the live set and the model rows are the half of
         it that no table holds; [model] is populated only under [audit]. *)
  mutation : Mutation.t option;
      (* NOT mutable, and [create] always sets it to [None]: see the block comment on
         [module Mutation] for why every one of those two words matters. *)
  mutable mutation_hits : int; (* corruptible sites the knob has passed over *)
  mutable mutation_note : string option;
      (* [Some description] once the knob has fired. Latched: one corruption per proof,
         so a rejection names one suspect. *)
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
    objective = Hashtbl.create 8;
    tags = Hashtbl.create 256;
    audit;
    comments;
    level = 0;
    finished = false;
    n_model = 0;
    mutation = None;
    mutation_hits = 0;
    mutation_note = None;
  }

(* A writer that emits ONE deliberately wrong step, for the mutation gate. Off is not
   a setting here: a normal writer comes from [create] and cannot become this one.
   Read the block comment on [module Mutation] before calling it, and do not call it
   from lib/ or bin/ -- test_mutation.ml checks that nothing there does. *)
let create_mutated ?comments ?audit ~mutation oc =
  { (create ?comments ?audit oc) with mutation = Some mutation }

(* What was corrupted, or [None] if the knob never found a site it could corrupt.

   A lane MUST check this. A knob that did not fire leaves a perfectly honest proof,
   the checker accepts it, and a lane reading that acceptance as "the step was not
   load-bearing" would be reporting a finding about a corruption that never happened
   -- which is the shape of every bug this harness exists to catch. *)
let mutation_note t = t.mutation_note
let mutation_fired t = t.mutation_note <> None
let mutation_plan t = t.mutation

(* How a constraint is referred to. Every constraint -- model rows included, via
   Opb.label_of -- carries the label `@c<id>`, so nothing in an emitted proof is a bare
   integer. *)
let cite _t id = Opb.label_of id
let cite_all t ids = String.concat " " (List.map (cite t) ids)
let auditing t = t.audit
let last_id t = t.next_id
let live_count t = Hashtbl.length t.live
let live_ids t = Hashtbl.fold (fun id _ acc -> id :: acc) t.live [] |> List.sort compare

(* M5-T1. The ids [improving] handed back, which are discharged by the conclusion and
   never deleted. Exposed so a test can assert they are still on the page rather than
   inferring it from the absence of a `del`. *)
let objective_ids t =
  Hashtbl.fold (fun id _ acc -> id :: acc) t.objective [] |> List.sort compare

let is_live t id = Hashtbl.mem t.live id

(* The proof is append-only and is never rewound (invariant I-X4); once [conclusion]
   has run, nothing more may be written to it. *)
let is_finished t = t.finished

(* ---------------------------------------------------------------- M1-T47
   Accounting for the time this module spends WRITING.

   M1-T35 split the CLI's run into phases and found that one of them, [search], is
   propagation, search and .pbp emission fused: bin/main.ml can only bracket
   [Search.solve], and every emission point is below it. So no row of bench/ could
   support "propagation costs X". This is the hook that separates them.

   WHAT IS ACCUMULATED, exactly, because a column that looks authoritative and is not
   is worse than no column:

     * The three functions below -- [line], [comment], [always_comment] -- are the
       only places this module writes to [t.oc], plus the [flush] in [conclusion],
       which is timed too. Every RULE goes through [line] (via [rule], or directly
       where the body already carries its own `;`). But [comment] and
       [always_comment] do NOT go through [line], and that is not a corner case:
       [set_level] emits its level marker as an [always_comment], so every level
       marker in every proof bypasses [line]. All three are instrumented.
     * NOT the building of a rule's body. [rule t (Printf.sprintf ...)],
       [Pol.to_string_cited], [Opb.constr_to_string], [lits_to_string] all run at the
       CALL SITE, before [line] is entered, and are not in this number. So this is a
       LOWER bound on emission cost, and search-minus-emission is an UPPER bound on
       propagation. Both are labelled that way wherever they are printed.

   WHY [kfprintf] AND NOT A TIMER AROUND THE BODY. [Printf.fprintf oc fmt] returns a
   closure that consumes the format's remaining arguments; the output happens as they
   are applied, i.e. AFTER [line t fmt] has returned. A [let t0 = now () in ... ; r]
   wrapper around the body therefore times the format set-up and nothing else -- it
   reads as a plausible small number and is measuring the wrong thing. Measured here
   before this was written: on width_sat_depth the naive wrapper reports 39 us against
   this one's 286 us. [kfprintf]'s continuation runs after the last argument has been
   printed, which is the only place the end of a line can be observed.

   WHY IT IS OFF BY DEFAULT. [Sys.time] costs ~0.72 us per read on this machine
   (measured, see bench/README.md section 3b) because CLOCK_PROCESS_CPUTIME_ID is a
   real syscall, not a vDSO read. Two reads per emitted line is ~1.4 us per line of
   instrument on top of the thing being measured, which on a 545-line proof is most
   of a millisecond. That is far too much to carry in a normal run, so the gate is a
   single bool dereference (~1.6 ns, measured) and the CLI closes it only under
   --time. The overhead that remains INSIDE a --time run is real and is published
   rather than hidden: [emitted_lines] is counted whether or not the clock is on, so
   the correction is always computable. *)

let emit_clock = ref false
let emit_us = ref 0
let emit_lines = ref 0

(* CPU microseconds, the same clock and rounding bin/main.ml's Timing uses, so that
   the two numbers can be subtracted. *)
let emit_now () = int_of_float ((Sys.time () *. 1_000_000.) +. 0.5)

(* Turn the per-line clock on. The CLI does this under --time and nothing else does;
   a normal run pays one dereference per line and no syscall. *)
let time_emission = emit_clock

(* CPU microseconds spent inside the writer's own output calls since the process
   started. Cumulative and process-wide rather than per-writer: a caller brackets the
   region it cares about by differencing two reads. Reads 0 while the clock is off,
   which is why [emitted_lines] exists beside it. *)
let emitted_us () = !emit_us

(* Lines actually written -- rules, level markers, comments that were not suppressed.
   Counted unconditionally, so it is a witness that the accumulator was reached even
   in a run with the clock off, and so that the instrument's own cost
   ([emitted_lines] x one clock read) can be subtracted from [emitted_us]. *)
let emitted_lines () = !emit_lines

let line t fmt =
  if t.finished then invalid_arg "Writer: the proof has already ended";
  if not !emit_clock then (
    incr emit_lines;
    Printf.fprintf t.oc (fmt ^^ "\n"))
  else
    let t0 = emit_now () in
    Printf.kfprintf
      (fun _ ->
        incr emit_lines;
        emit_us := !emit_us + (emit_now () - t0))
      t.oc (fmt ^^ "\n")

(* A rule, terminated by `;`. Rules whose body already carries one -- [rup] and the
   OPB constraint rendering it uses -- go through [line] directly: a second `;` is a
   syntax error. *)
let rule t body = line t "%s ;" body

(* The label a rule that YIELDS an id is prefixed with, so later rules can cite it by
   name. [sol] must not get one: VeriPB 3.0 says in as many words that "the rule `sol`
   cannot be prefixed with a label", and it is right -- it yields nothing to name. *)
let label_for _t id = Opb.label_of id ^ " "

(* Comments are [%]; [*] is refused outright ("Expected a top level rule name"), and
   [#] is not a comment either -- it introduces a proofgoal id. *)

(* Both arms are timed, and only the arm that writes is counted. A suppressed comment
   still walks its format -- [ifprintf] is not free -- and that cost is incurred
   because the proof machinery is there, so it belongs in the emission number; but it
   puts no line in the file, so it must not inflate [emitted_lines], which is what the
   instrument's own overhead is computed from. The consequence, stated rather than left
   to be found: a suppressed comment costs two clock reads that [emitted_lines] does not
   account for, so the reported overhead under-states itself by that much. Zero on every
   model in the suite -- the only callers of [comment] are three lazy direct-encoding
   paths in Encoding that nothing but test/unit/test_proof.ml reaches -- and it would
   take a caller emitting far more suppressed comments than rules to matter. *)
let comment t fmt =
  if not !emit_clock then
    if t.comments then (
      incr emit_lines;
      Printf.fprintf t.oc ("%% " ^^ fmt ^^ "\n"))
    else Printf.ifprintf t.oc ("%% " ^^ fmt ^^ "\n")
  else
    let t0 = emit_now () in
    let stop _ = emit_us := !emit_us + (emit_now () - t0) in
    if t.comments then
      Printf.kfprintf
        (fun oc ->
          incr emit_lines;
          stop oc)
        t.oc
        ("%% " ^^ fmt ^^ "\n")
    else Printf.ikfprintf stop t.oc ("%% " ^^ fmt ^^ "\n")

(* A comment that is emitted whether or not --proof-comments is on. Used for the
   few markers that make a proof navigable at all -- and for the level markers
   themselves ([set_level]), which is why this bypass of [line] is not a detail: on a
   model with 196 decisions it is 196 of the proof's lines. *)
let always_comment t fmt =
  if not !emit_clock then (
    incr emit_lines;
    Printf.fprintf t.oc ("%% " ^^ fmt ^^ "\n"))
  else
    let t0 = emit_now () in
    Printf.kfprintf
      (fun _ ->
        incr emit_lines;
        emit_us := !emit_us + (emit_now () - t0))
      t.oc
      ("%% " ^^ fmt ^^ "\n")

let fresh t ~origin =
  t.next_id <- t.next_id + 1;
  if t.audit then Hashtbl.replace t.live t.next_id { origin; level = t.level };
  Hashtbl.replace t.tags t.next_id t.level;
  t.next_id

(* Preamble: version line, then the count of model constraints loaded from the .opb.

   The count is NOT the trap PROOF-FORMAT section 2 used to describe it as. The
   checker rejects a wrong one outright and names the right number ("The formula
   contains 3 constraints, but the rule expected that there are 2"), measured. What
   used to be silent was the *consequence* of miscounting inside [Encoding] -- a `pol`
   citing a shifted id. That is gone too: citations are labels. *)
let header t ~n_model_constraints =
  line t "pseudo-Boolean proof version %s" proof_version;
  (* A corrupted proof says so in its own first comment, unconditionally -- not under
     --proof-comments, because the point is that this line cannot be switched off.
     Nothing but [create_mutated] can produce it, so its presence in a file is proof
     that the file came from the mutation gate and its absence is proof that it did
     not. *)
  (match t.mutation with
  | Some m ->
      always_comment t
        "DELIBERATELY CORRUPTED PROOF (Writer.create_mutated): %s. Emitted by the M1-T26 \
         mutation gate; a normal run cannot produce this line."
        (Mutation.describe m)
  | None -> ());
  rule t (Printf.sprintf "f %d" n_model_constraints);
  (* The f rule makes the model constraints ids 1..n. *)
  t.next_id <- n_model_constraints;
  t.n_model <- n_model_constraints;
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
  (* VeriPB 3.0 has no SetLevel rule -- `#` there introduces a proofgoal id and `# 1`
     is a parse error. The level is still real; it is just ours to carry now, so record
     it and leave a comment where the marker used to be. That comment is emitted
     unconditionally: without it a proof has nothing in it that says where a decision
     began, and the proofs in this project are read by hand. *)
  always_comment t "level %d" l;
  t.level <- l

let current_level t = t.level

(* Allocate ids at a CHOSEN level for the duration of [f] -- docs/DECISIONS.md D-0045's
   addendum, and the entry point M2-L1 was sent to build.

   The problem it exists for, measured before it was written (M2-L1, 2026-09-18, by
   hand): [fresh] tags every id with [t.level], unconditionally and with no override,
   and [wipe_level l] deletes every id tagged at level >= l. So a constraint derived at
   the conflict level is deleted by the backjump that retires that level, and a later
   `pol` citing it is rejected -- "Trying to access constraint with ID 3 that has
   already been deleted" (veripb 3.0.2).

   A learned constraint exists precisely to outlive the conflict that produced it, so it
   must be introduced at level 0. Note what this is NOT: it is not a [fresh ~level]
   argument that writes [t.tags] directly. The level is moved for real, by [set_level],
   so that [t.tags] and the emitted proof keep saying the same thing about where an id
   landed (invariant I-X3) instead of only our own table knowing; this is a bracket
   around [set_level] rather than a new allocation path.

   The cost is honest and is two marker lines per bracketed derivation: the `% level l`
   comment on the way in and another on the way out. D-0045's objection to reaching for
   [set_level] was that it puts a marker "in the middle of a derivation" -- true, and the
   answer is that this brackets a WHOLE derivation rather than sitting inside one.

   [f] is run at [l] and the level is restored even if it raises, because a writer left
   at the wrong level would mis-tag every id minted after it and the failure would
   surface as a deletion somewhere else entirely. *)
let with_level t l f =
  let saved = t.level in
  if saved = l then f ()
  else (
    set_level t l;
    let r =
      try f ()
      with e ->
        set_level t saved;
        raise e
    in
    set_level t saved;
    r)

(* The level an id is tagged with, or [None] if the id is not tagged -- it was retired,
   or it is a model row, which nothing tags. A test that wants to see WHERE an id landed
   asks here rather than grepping the proof. *)
let tag_of t id = Hashtbl.find_opt t.tags id

(* ------------------------------------------------------------------ reading it back

   [set_level] is the only thing that writes a level marker, so the spelling belongs
   here rather than in each test that greps a proof for it. The reason this is a
   function and not a convention: a test that hard-codes a spelling does not FAIL when
   that spelling moves -- it finds nothing, and an assertion of the form
   `not (contains "# 1" proof)` passes vacuously. A test that has silently stopped
   testing is worse than a red one, and the 2.0-to-3.0 flip turned up five of them. *)

(* A proof line with its label removed: `@c17 rup ... ;` becomes `rup ... ;`.

   Tests that pin what a rule SAYS want the body; the label is the constraint's name,
   and the checker verifies it for them (a citation of a name that was never bound is a
   parse error, which is the whole point of D-0023's labels). Stripping it here keeps
   such an assertion about the rule rather than about its name. *)
let strip_label line =
  if String.length line > 0 && line.[0] = '@' then
    match String.index_opt line ' ' with
    | Some i -> String.sub line (i + 1) (String.length line - i - 1)
    | None -> line
  else line

(* The rule's text with its decoration removed: label off the front, terminator off the
   back. This is the projection a pin on "what this step says" wants -- every rule is
   labelled and terminated, so a step that derives `@c3 @c4 + 2 d` is emitted as
   `@c17 pol @c3 @c4 + 2 d ;`. (A `rup` carries its own `;` as part of the constraint
   syntax rather than as the rule terminator, so it is unaffected either way.) *)
let rule_body line =
  let l = String.trim (strip_label line) in
  let n = String.length l in
  if n >= 1 && l.[n - 1] = ';' then String.trim (String.sub l 0 (n - 1)) else l

let level_marker l = Printf.sprintf "%% level %d" l

(* [Some l] when [line] is a level marker. VeriPB 3.0 has no SetLevel rule (D-0024), so
   [set_level] leaves the comment `% level l` and that is the only spelling there is. *)
let level_of_line line =
  let line = String.trim line in
  let p = "% level " in
  let k = String.length p in
  if String.length line >= k && String.sub line 0 k = p then
    int_of_string_opt (String.trim (String.sub line k (String.length line - k)))
  else None

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
   `del range` tolerates already-deleted ids inside the span.

   ---- M1-T29: the newest-id run no longer costs one citation per retired reason ----

   The paragraph above is why that fallback existed; what follows is why it is gone.
   The run [lo, hi] with [hi] the newest id is now written as a PAIR of rules --

     del range @c<lo> @c<hi> ;      the half-open span [lo, hi): everything but [hi]
     del id    @c<hi> ;             and then [hi] itself

   -- which is two lines of bounded length instead of one line carrying [hi - lo + 1]
   citations. The run's own last id is a label that certainly exists (we just handed
   it out), so nothing here needs a bound that has not been assigned yet.

   The two routes this replaces, and why neither was taken:

   * A NUMERIC exclusive bound, `del range @c<lo> <hi+1>`. It is one line and 3.0.2
     does tolerate an integer one past the last id -- measured -- but it reintroduces
     the bare-integer citation D-0023's labels removed, at the one site where the
     bound is the thing most likely to drift. It is also brittle in a way worth
     recording: measured against 3.0.2, `<hi+1>` is accepted and `<hi+2>` is a hard
     error ("Accessing the database out of bound with index 6. The index should be
     between -6 and 5"), while `<hi>` silently under-deletes. A spelling whose only
     legal value is the one we compute is a spelling with no margin.
   * Minting one extra always-live constraint past the newest id, purely to give the
     range an upper bound to name. That is O(1) proof text per backtrack but leaves a
     constraint in the checker's database per backtrack, which trades a term that
     grows with the reasons at ONE level for one that grows with the whole search, and
     adds a rule that means nothing.

   The pair also makes the dangerous direction LOUD, which is the reason to prefer it
   over the numeric bound even setting D-0023 aside. Over-deletion is the silent
   failure -- a range whose upper bound is one too high retires a constraint a later
   line may cite (with D-0039 and I-S4, that now includes a trace line citing a hole
   line), and nothing in our own bookkeeping notices, because an over-deleted id is
   not an un-retired id and the I-X2 audit is checking us against ourselves. Here an
   upper bound one too high is caught by the very next rule, measured against 3.0.2
   in [test_v3_del_pair_spelling]:

     - `@c<hi+1>` not yet assigned -> "The label `@c6` is not assigned to a
       constraint ID at line 6 col 15" (a parse error naming the label -- D-0023's
       trap staying closed);
     - `@c<hi+1>` assigned -> "Trying to access constraint with ID 5 that has already
       been deleted", raised by the trailing `del id`.

   Deletion ORDER is unchanged in the sense I-S4 needs: both rules of the pair retire
   ids from the same doomed set of the same [wipe_level] call, so no line survives its
   own citee any longer or shorter than it did before. What changed is only how many
   tokens the retirement is spelled with.

   The cost, stated rather than left to be found: for a run of 2, 3 or 4 ids the pair
   is a few bytes LONGER than the list it replaces (about 39 bytes against 8 + 6n).
   It is used unconditionally anyway -- a threshold would buy back ~0.5% of today's
   proof bytes at the price of a second shape that fires on no shipped model and is
   therefore exercised by nothing but a unit test, and this project's signature defect
   is a check that cannot see its own subject fail. One shape, exercised 14 times by
   the model suite, is worth more than the bytes. *)
let del_run t (lo, hi) =
  if lo = hi then rule t (Printf.sprintf "del id %s" (cite t lo))
  else if hi < t.next_id then
    rule t (Printf.sprintf "del range %s %s" (cite t lo) (cite t (hi + 1)))
  else (
    rule t (Printf.sprintf "del range %s %s" (cite t lo) (cite t hi));
    rule t (Printf.sprintf "del id %s" (cite t hi)))

let wipe_level t l =
  (* M2-L4: a backjump may not be a second owner of a learned constraint's lifetime, and
     this line is what makes that structural instead of a fact about [Search]'s call
     sites.

     A learned constraint is introduced at level 0 ([Justify.with_level ctx 0], D-0045's
     addendum as M2-L1 resolved it) precisely so that no backjump retires it. Levels are
     non-negative, so the ONLY wipe that could reach a level-0 tag is [wipe_level 0] --
     and every caller in lib/ passes a decision level, which is >= 1. That was true by
     inspection and would have stayed true only by inspection: a fifth call site passing
     0 would have deleted every learned constraint on the page, silently from our side
     (a second [forget] is a no-op, so the I-X2 audit cannot see the resulting double
     delete -- D-0045) and loudly from the checker's, a long way from the mistake.

     There is no legitimate [wipe_level 0]. Retiring the level-0 lines is [Trace]'s
     [permanent_ids] and [Retention.retire_all], each of which deletes what it owns and
     nothing else. So this refuses rather than documents. *)
  if l <= 0 then
    invalid_arg
      "Writer.wipe_level: level must be >= 1. Level 0 holds the learned constraints and \
       the permanent trace lines, whose lifetimes are owned by Retention and Trace \
       respectively (M2-L4); no backjump may retire them.";
  (* VeriPB 3.0 deleted the level stack that D-0008 built backtracking on. `w l` retired
     every constraint TAGGED at level >= l, and the checker held the tags; now [t.tags]
     does, so the same set is computed here and deleted explicitly. This reproduces
     `w l` exactly -- it is not "delete what was derived since", which would be wrong the
     moment a level is re-entered after an interlude at a lower level (search does
     exactly that: level 1, level 0, two root prunings, level 1 again).

     The cost is honest and belongs in the record: PROOF-FORMAT section 5's whole
     argument for levels was one proof line per backtrack rather than one deletion per
     reason, and that argument is gone. Runs recover most of it -- a level's ids are
     usually consecutive, so it is usually still one or two lines -- but "usually" is not
     "always", and a level whose ids interleave with deletions costs a pair of lines per
     run. What the proof no longer grows with, since M1-T29, is the number of reasons
     retired at one level: every shape [del_run] can emit is of bounded length. See
     D-0024, which is the record of what `w` did and why this function has to imitate it.

     [del_run] is what turns an inclusive run into a rule; `del range` is half-open and
     that difference is the whole of M1-T22. *)
  let doomed =
    Hashtbl.fold (fun id lv acc -> if lv >= l then id :: acc else acc) t.tags []
    |> List.sort compare
  in
  List.iter (Hashtbl.remove t.tags) doomed;
  List.iter (del_run t) (runs doomed);
  if t.audit then
    let doomed =
      Hashtbl.fold
        (fun id (e : entry) acc -> if e.level >= l then id :: acc else acc)
        t.live []
    in
    List.iter (Hashtbl.remove t.live) doomed
(* VeriPB's LevelStack does not move the current level on a wipe, so neither do we:
   the mirror has to stay exact (invariant I-X3). *)

(* ------------------------- applying a knob -------------------------------
   All of this is dead code in a writer built by [create]: every entry point below
   starts by matching [t.mutation], which is [None] there and cannot become anything
   else. Nothing here writes to the channel. *)

let contains_sub ~needle hay =
  let n = String.length needle and h = String.length hay in
  if n = 0 then true
  else if n > h then false
  else
    let found = ref false in
    let i = ref 0 in
    while (not !found) && !i <= h - n do
      if String.sub hay !i n = needle then found := true;
      incr i
    done;
    !found

(* The knob to apply to a rule with this [~origin], or [None]. [mutation_note] latches,
   so this stops answering once the knob has fired: one corruption per proof. *)
let knob_for t ~corrupts ~origin =
  match t.mutation with
  | Some m
    when t.mutation_note = None && corrupts m.Mutation.kind
         && contains_sub ~needle:m.Mutation.site origin ->
      Some m
  | _ -> None

(* Rewrite the FIRST node, in the order the step is written (reverse Polish, so an
   operand comes before the operator that consumes it), for which [f] returns a
   replacement. [None] when no node matches.

   This is the part the text harness could not get right. In `pol 3 4 *` the `4` is a
   multiplier and the `3` a constraint reference; awk has to guess that from the token
   that follows, and it guessed with a special case per shape. Here they are different
   constructors. *)
let rec rewrite_first f (p : Pol.t) =
  match p with
  | Pol.Id _ | Pol.Axiom _ -> f p
  | Pol.Add (a, b) -> (
      match rewrite_first f a with
      | Some a' -> Some (Pol.Add (a', b))
      | None -> (
          match rewrite_first f b with Some b' -> Some (Pol.Add (a, b')) | None -> f p))
  | Pol.Mul (a, k) -> (
      match rewrite_first f a with Some a' -> Some (Pol.Mul (a', k)) | None -> f p)
  | Pol.Div (a, k) -> (
      match rewrite_first f a with Some a' -> Some (Pol.Div (a', k)) | None -> f p)
  | Pol.Sat a -> (
      match rewrite_first f a with Some a' -> Some (Pol.Sat a') | None -> f p)
  | Pol.Weaken (a, v) -> (
      match rewrite_first f a with Some a' -> Some (Pol.Weaken (a', v)) | None -> f p)

let rec first_operand (p : Pol.t) =
  match p with
  | Pol.Id _ | Pol.Axiom _ -> p
  | Pol.Add (a, _) -> first_operand a
  | Pol.Mul (a, _) -> first_operand a
  | Pol.Div (a, _) -> first_operand a
  | Pol.Sat a -> first_operand a
  | Pol.Weaken (a, _) -> first_operand a

let rec cited_ids acc (p : Pol.t) =
  match p with
  | Pol.Id c -> c :: acc
  | Pol.Axiom _ -> acc
  | Pol.Add (a, b) -> cited_ids (cited_ids acc a) b
  | Pol.Mul (a, _) | Pol.Div (a, _) | Pol.Weaken (a, _) -> cited_ids acc a
  | Pol.Sat a -> cited_ids acc a

(* Ids a corrupted citation may name: the model rows, which nothing retires, plus the
   derived ids still tagged live. Citing a retired id is a rejection about the
   DATABASE ("Trying to access constraint with ID N that has already been deleted"),
   not about the derivation -- the text harness had to reconstruct this set by
   replaying every `del` in the proof, which is where M1-T22's half-open off-by-one
   lived. A wrong answer here can only make the knob decline to fire, never manufacture
   a pass. *)
let citable_ids t =
  let live = ref [] in
  Hashtbl.iter (fun id _ -> live := id :: !live) t.tags;
  for i = t.n_model downto 1 do
    live := i :: !live
  done;
  List.sort_uniq compare !live

let apply_to_pol t kind (p : Pol.t) =
  match kind with
  | Mutation.Perturb_coefficient -> (
      let divisor = function Pol.Div (a, k) -> Some (Pol.Div (a, k + 1)) | _ -> None in
      let multiplier = function
        | Pol.Mul (a, k) -> Some (Pol.Mul (a, k + 1))
        | _ -> None
      in
      (* A bare literal axiom IS the coefficient 1, so doubling it is the same kind of
         perturbation as bumping a multiplier. *)
      let axiom = function Pol.Axiom l -> Some (Pol.Mul (Pol.Axiom l, 2)) | _ -> None in
      match rewrite_first divisor p with
      | Some q -> Some q
      | None -> (
          match rewrite_first multiplier p with
          | Some q -> Some q
          | None -> rewrite_first axiom p))
  | Mutation.Swap_citation ->
      let cited = cited_ids [] p in
      let candidates = List.filter (fun c -> not (List.mem c cited)) (citable_ids t) in
      rewrite_first
        (function
          | Pol.Id c -> (
              (* Nearest id first, so the swap is a plausible off-by-one rather than a
                 wild jump -- the corruption an id counter would actually make. *)
              match
                List.sort
                  (fun a b -> compare (abs (a - c), a) (abs (b - c), b))
                  candidates
              with
              | x :: _ -> Some (Pol.Id x)
              | [] -> None)
          | _ -> None)
        p
  | Mutation.Truncate_derivation ->
      let q = first_operand p in
      if q == p then None else Some q
  | Mutation.Drop_literal | Mutation.Strengthen_rhs -> None

(* [corrupt_pol] is what [pol] calls. It returns the expression to emit, and records
   what it did. A corruption that renders identically to the honest step has not
   happened, whatever the knob thinks: that guard is the in-emitter twin of the
   script's `cmp -s` check, and it is why a knob applied to a one-operand `pol` reports
   "did not fire" rather than producing a clean proof a lane would misread. *)
let corrupt_pol t ~origin (p : Pol.t) =
  match knob_for t ~corrupts:Mutation.corrupts_pol ~origin with
  | None -> p
  | Some m -> (
      let render q = Pol.to_string_cited ~cite:(cite t) q in
      match apply_to_pol t m.Mutation.kind p with
      | Some q when render q <> render p ->
          t.mutation_hits <- t.mutation_hits + 1;
          if t.mutation_hits = m.Mutation.occurrence then (
            t.mutation_note <-
              Some
                (Printf.sprintf "%s\n  origin: %s\n  before: pol %s\n   after: pol %s"
                   (Mutation.kind_name m.Mutation.kind)
                   origin (render p) (render q));
            q)
          else p
      | _ -> p)

(* The same for the claim rules, [rup] and [red].

   Which claim a lane corrupts is chosen by naming its [~origin], not by a heuristic
   over the text. That matters for the reason trap (GCS dev_docs/constraints.md:1085):
   dropping a literal from a reason is only a corruption when the literal traces back
   to a search DECISION, because anything a propagator derived is in the proof as a
   clause of its own and the checker has it either way. The text harness guessed at
   that by preferring a clause emitted between a level marker and its wipe; a lane here
   states the derivation it means. *)
let corrupt_claim t ~origin (c : Opb.constr) =
  match knob_for t ~corrupts:Mutation.corrupts_claim ~origin with
  | None -> c
  | Some m -> (
      let applied =
        match m.Mutation.kind with
        | Mutation.Drop_literal ->
            let ts = c.Opb.terms in
            let n = List.length ts in
            (* One-term claim: dropping its only literal corrupts the claim, not the
               reason. Refused, and the refusal reaches the lane as "did not fire". *)
            if n < 2 then None
            else
              Some
                ( { c with Opb.terms = List.filteri (fun i _ -> i < n - 1) ts },
                  Printf.sprintf "dropped the last of %d terms" n )
        | Mutation.Strengthen_rhs ->
            (* Raising the degree strengthens the claim, so the checker must reject it
               unless the honest claim was weaker than it needed to be. Lowering it
               weakens the claim, which usually still checks: not a test. *)
            Some
              ( { c with Opb.rhs = c.Opb.rhs + 1 },
                Printf.sprintf "degree raised from %d to %d" c.Opb.rhs (c.Opb.rhs + 1) )
        | Mutation.Perturb_coefficient | Mutation.Swap_citation
        | Mutation.Truncate_derivation ->
            None
      in
      match applied with
      | Some (c', what) when Opb.constr_to_string c' <> Opb.constr_to_string c ->
          t.mutation_hits <- t.mutation_hits + 1;
          if t.mutation_hits = m.Mutation.occurrence then (
            t.mutation_note <-
              Some
                (Printf.sprintf "%s (%s)\n  origin: %s\n  before: %s\n   after: %s"
                   (Mutation.kind_name m.Mutation.kind)
                   what origin (Opb.constr_to_string c) (Opb.constr_to_string c'));
            c')
          else c
      | _ -> c)

(* ------------------------------ rules ------------------------------------ *)

(* Every rule below that yields an id takes its label from the id it is ABOUT to be
   given, so [fresh] has to run first and the body is written afterwards. *)
let emit_yielding t ~origin body_of_id =
  let id = t.next_id + 1 in
  rule t (label_for t id ^ body_of_id id);
  let id' = fresh t ~origin in
  assert (id = id');
  id

(* A cutting-planes derivation, and the ONLY way this module writes a `pol` line.

   There used to be a [pol_raw] beside it, taking reverse-Polish text built elsewhere.
   It had no caller anywhere in the tree and it is deleted (M1-T39). Three reasons, and
   the first is the one that makes this a decision rather than tidying:

   1. It bypassed [corrupt_pol], so it was the one emission path the mutation harness
      could not reach. D-0030 makes it structurally impossible for a knob to fire in a
      normal run; the dual obligation is that no emission path is structurally
      incapable of being corrupted, or a future caller gets a derivation no lane can
      ever gate. A proof step this file writes must be a proof step this file can
      knowingly break.
   2. It bypassed [Pol.to_string_cited], so it emitted positional text where everything
      else emits labels. A caller would have had to re-derive the labelling
      rule this module already knows -- the "a project-wide fact copied into several
      files" failure this tree has recorded twice already (Checker.find, and the
      level-marker spellings that D-0023's round collapsed into this module).
   3. Nothing is lost. [Pol.t] spans the whole cutting-planes vocabulary
      docs/PROOF-FORMAT.md section 2 lists -- ids, literal axioms, `+`, `* k`, `d k`,
      `s`, `w v` -- so there is no derivation the raw form could state that [pol]
      cannot. It bought no expressiveness, only an unchecked path. *)
let pol t ~origin p =
  (* [corrupt_pol] is the identity for every writer [create] built. *)
  let p = corrupt_pol t ~origin p in
  emit_yielding t ~origin (fun _ -> "pol " ^ Pol.to_string_cited ~cite:(cite t) p)

(* Reverse unit propagation of a PB constraint. Prefer [pol] where the reasoning is
   known; see docs/PROOF-FORMAT.md section 2.

   The body already ends in " ;" (Opb.constr_to_string), which is the rule terminator,
   so this goes through [line] rather than [rule]: `rup ... ; ;` is a syntax error. *)
let rup t ~origin c =
  let c = corrupt_claim t ~origin c in
  let id = t.next_id + 1 in
  line t "%srup %s" (label_for t id) (Opb.constr_to_string c);
  fresh t ~origin

(* Reverse unit propagation of a clause -- the common case. *)
let rup_clause t ~origin lits = rup t ~origin (Opb.clause lits)

(* ---------------- stating what a step CONCLUDES (M1-T51) ------------------

   [pol] writes a derivation and nothing else. Its conclusion is whatever the reverse-
   Polish expression happens to evaluate to, and until this rule existed the proof
   contained no statement of what the propagator BELIEVED it had derived. A `pol` that
   computes something strictly weaker than the bound the propagator then pruned to is
   a sound proof line under an unsound prune, and the checker has nothing to object
   to. M1-T42 could only reach 8 of its 9 cells for exactly this reason: every `pol`
   guard in the suite was a regex over emitted text, so it could see the derivation
   change shape but never see the checker judge it.

   [implied] closes that. `ia C : @hint ;` asks the checker whether [C] is
   syntactically implied by the constraint at [hint] -- a one-constraint check, no
   search -- and it is the missing half of a `pol`: the derivation says how, the `ia`
   says what.

   docs/PROOF-FORMAT.md section 2a lists no `e` and no `ia` and is INCOMPLETE on this
   point; see the M1-T51 hand-back. The measured rejection wording, for a lane that
   asserts this control fires:

     "Expected constraint is not syntactically implied by the constraint at the hint."

   The hint is mandatory here even though the checker accepts the rule without one.
   Unhinted, `ia C ;` searches the WHOLE database and 3.0.2 says so ("Constraint not
   syntactically implied by any constraint in the database"), which makes it a much
   weaker control than it looks: the claim being implied by some ladder clause or some
   older derivation says nothing about the `pol` on the line above. A control that can
   be satisfied by a constraint other than its subject is this project's signature
   failure mode. The hint is what makes the rule name its subject.

   The syntax was not guessed: `ia <body> : @chint ;` -- the hint follows a `:`, before
   the terminator, exactly as [red]'s witness does. After the `;` it is not a hint at
   all: it is parsed as the LABEL OF THE NEXT RULE, so `ia C ; @c1` verifies against the
   whole database and a bogus `ia C ; @NOPE` verifies too. That is the trap this comment
   exists to record.

   It yields an id like any other rule, so I-X2 applies to what it hands back. *)
let implied t ~origin ~hint c =
  let c = corrupt_claim t ~origin c in
  let id = t.next_id + 1 in
  line t "%sia %s : %s ;" (label_for t id) (Opb.constr_body c) (cite t hint);
  fresh t ~origin

(* Redundance-based strengthening: used only to introduce definitions (direct-encoding
   channelling, reified variables). The witness maps variables to 0, 1 or a literal. *)
type witness_value = Zero | One | To of Lit.t

let witness_value_to_string = function
  | Zero -> "0"
  | One -> "1"
  | To l -> Lit.to_string l

let red t ~origin ~witness c =
  (match witness with [] -> invalid_arg "Writer.red: empty witness" | _ -> ());
  let c = corrupt_claim t ~origin c in
  let w =
    String.concat " "
      (List.map
         (fun (v, value) ->
           Printf.sprintf "%s -> %s" (Lit.var_name v) (witness_value_to_string value))
         witness)
  in
  (* `red <constraint> : <witness> ;` -- the rule ends at the first `;`, so a witness
     written after one is silently not a witness, and the checker says "A witness must
     be specified for the red-rule". Measured. *)
  let id = t.next_id + 1 in
  line t "%sred %s : %s ;" (label_for t id) (Opb.constr_body c) w;
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
      List.iter (Hashtbl.remove t.tags) ids;
      List.iter (forget t) ids

let delete t id = delete_many t [ id ]

(* A `pol` that states its own conclusion, and the form a propagator should reach for.

   Emits three lines where [pol] emits one:

     @cN   pol <derivation> ;        the reasoning
           ia  <claim> : @cN ;       the claim, checked against that reasoning
           del id @cN ;              the reasoning, retired

   and returns the id of the CLAIM, not of the derivation. Three consequences worth
   stating, because each one was a choice:

   1. The caller receives exactly one id and owes exactly one deletion, so I-X2 reads
      the same as it does for [pol]. The derivation's id never escapes this function.
   2. What escapes is the claim, so a later step that cites this id cites the bound the
      [Explanation] says was derived, not whatever the cutting-planes expression
      happened to evaluate to. Where those differ the difference now surfaces at the
      `ia` instead of propagating silently into the parent derivation.
   3. The derivation is deleted immediately. It has served its purpose the moment the
      `ia` is checked, and leaving it live would make every pruning grow the checker's
      database by two constraints instead of one.

   The internal [pol] goes through [corrupt_pol] exactly as a bare [pol] does, so the
   mutation harness reaches the derivation here through the lanes it already has --
   which is the D-0030 dual obligation in the [pol] comment above, and the reason this
   is a wrapper rather than a second emission path. *)
let pol_concluding t ~origin ~claim p =
  let derivation = pol t ~origin p in
  let id = implied t ~origin ~hint:derivation claim in
  delete t derivation;
  id

(* [delc] takes its constraint reference directly, with no `id` keyword ("Expected a
   constraint ID (label or signed integer) ... but found `id`"). [del] and [core] keep
   theirs. Measured; there is no pattern to infer. *)
let delete_core t id =
  rule t (Printf.sprintf "delc %s" (cite t id));
  Hashtbl.remove t.tags id;
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

   NOT USABLE as it stands: "Logging and excluding a solution with 'solx' is only
   possible if a preserved set is specified". VeriPB 3.0 ties solution exclusion to the
   `preserved` machinery, which this project has no encoding for. Nothing in M1 emits
   it; enumeration (and M5's `soli`, untested here) will have to face this. *)
let solution_excluding t ~origin lits =
  let id = t.next_id + 1 in
  rule t (Printf.sprintf "%ssolx %s" (label_for t id) (lits_to_string lits));
  fresh t ~origin

(* Improving solution for optimisation (M5-T1). The checker reads the objective out of
   the .opb, builds the strictly-improving constraint "obj <= <this solution's value> - 1"
   for itself, and hands back its id -- we never write that constraint, so we cannot write
   it wrongly.

   THE ID IT RETURNS IS NOT YOURS TO DELETE, and this is the one place in the writer where
   that is true of an id a rule hands back. Measured on 3.0.2, 2026-09-21: deleting a
   `soli` constraint before the conclusion is an UNCHECKED deletion, and the checker says
   so --

     Warning: Switching from stronger to weaker guarantee using unchecked deletion. This
     means that any solution after this deletion is not necessarily a solution for the
     original problem.

   -- while under --force-checked-deletion the same line is a hard failure ("Checked
   deletion failed ... Proofgoal with ID #1 could not be autoproven"). Since `conclusion
   BOUNDS` is checked AFTER that point, a proof that deletes its own `soli` constraints
   and is then accepted has been accepted under a weakened guarantee: it is the same shape
   as D-0053's `red` over a contradictory database, an acceptance that is not evidence.
   Worse, deleting them silently discards the recorded objective value -- the first
   version of M5-T1 did exactly that and the checker refused the conclusion outright with
   "The claimed upper bound of 2 mismatches the best recorded upper bound of 4".

   So the id is registered in [t.objective] and NOT in [t.live]: it is discharged by the
   conclusion, for precisely the reason docs/PROOF-FORMAT.md section 5 already gives for
   the contradiction `conclusion UNSAT` cites and for `BOUNDS`'s own lower-bound id --
   "they cannot be deleted before being referenced". The audit reports them separately so
   that "nothing was leaked" and "nothing was retired that could not be" stay distinct
   claims rather than one silence. *)
let improving t ~origin lits =
  let id = t.next_id + 1 in
  rule t (Printf.sprintf "%ssoli %s" (label_for t id) (lits_to_string lits));
  let id = fresh t ~origin in
  forget t id;
  if t.audit then Hashtbl.replace t.objective id { origin; level = t.level };
  id

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
       veripb 3.0.2 does not propagate it -- "the solution given for the conclusion is
       not propagated" -- and reads every unmentioned variable as false, so a model
       needing a selector true has its honest proof REJECTED.
       test/models/ne_conflict_sat.fzn is such a model, and was the single point on
       which the 2.2.2 this project used to check against disagreed (D-0046 retired it;
       the finding is why this form is not used).

       A solution logged with [sol] *is* propagated. Measured, not argued:
       the checker's own hint says "if the solution should be propagated, then log
       the solution inside the proof". [solx] is not an alternative -- 3.0.2 refuses
       it outside a preserved set. *)
  | Unsat of cid option
    (* The id of the derived contradiction. [None] makes the checker search the
       database for one -- accepted, but it is work we can spare it, and under the
       audit an undeleted contradiction id would fail I-X2 anyway. *)
  | Bounds of {
      lower : int option;
      (* [None] is INF, the same convention [upper] uses, and it is the ONLY conclusion
         available for an infeasible optimisation problem. `conclusion UNSAT` is not:
         3.0.2 refuses it outright over a formula that carries a `min:` line, and names
         the replacement itself -- "'conclusion UNSAT' can only be used without an
         objective. Use 'conclusion BOUNDS INF INF' for infeasible optimization
         problems." Measured 2026-09-21 (M5-T2). *)
      lower_id : cid option; (* the constraint that establishes the lower bound *)
      upper : int option; (* None is INF: no solution was found *)
      upper_assignment : Lit.t list;
    }

(* [output NONE] is required by the checker before [conclusion]; the doc's rule table
   does not mention it. NONE is the honest guarantee: we do not emit an output
   formula, so we claim nothing about one. *)
let conclusion ?(output = "NONE") t v =
  (* [sol] first: it is a derivation rule and [output] must be the line immediately
     before [conclusion] (SPEC section 4.3).

     M7-T6/D-0070: EVERY [Sat], including one with no literals. The [_ :: _] guard this
     line used to carry was a mechanical carry-over from the shape M1-T18 replaced --
     [Sat [] -> "conclusion SAT"] against [Sat lits -> "conclusion SAT : <lits>"], where
     the empty case meant "no assignment to inline" and skipping it was right. It was
     not right for [sol]: `conclusion SAT` REQUIRES a logged solution, so the empty case
     emitted a conclusion resting on nothing and 3.0.2 refused the whole proof with "No
     solution has been logged in the proof and no solution has been given in the
     conclusion". It is reachable from a model that declares no variables, which is two
     of the three corpus rejections D-0068 measured.

     It is not the other reading -- an empty assignment on a NON-EMPTY model, where a
     bare `sol ;` would be a wrong line rather than a missing one. [Search.solve] builds
     these literals with [Encoding.assignment_lits] over the assignment of EVERY store
     variable, so the list is empty exactly when the encoding has no variables, which is
     exactly when the .opb has none either and the empty assignment is the complete one.
     test/unit/test_proof.ml's control lane asserts the non-empty side rather than
     leaving that as an argument. *)
  (match v with Sat lits -> solution t lits | _ -> ());
  rule t (Printf.sprintf "output %s" output);
  (match v with
  | Sat _ -> rule t "conclusion SAT"
  | Unsat None -> rule t "conclusion UNSAT"
  | Unsat (Some id) ->
      rule t (Printf.sprintf "conclusion UNSAT : %s" (cite t id));
      forget t id
  | Bounds { lower; lower_id; upper; upper_assignment } ->
      let b = Buffer.create 64 in
      Buffer.add_string b
        (match lower with
        | None -> "conclusion BOUNDS INF"
        | Some l -> Printf.sprintf "conclusion BOUNDS %d" l);
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
  (* The fourth write to [t.oc], and the only one that is not a line: it is where the
     buffered proof actually reaches the kernel, so on a proof of any size it is the
     single largest emission cost in the whole of [search]. It bypasses [line] by
     construction and is accumulated here rather than left out. It adds no line, so
     [emit_lines] does not move. *)
  (if not !emit_clock then flush t.oc
   else
     let t0 = emit_now () in
     flush t.oc;
     emit_us := !emit_us + (emit_now () - t0));
  check_audit t
