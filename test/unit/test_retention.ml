(* Unit tests for lib/core/retention.ml -- the learned-constraint database, who owns a
   learned constraint's lifetime, and the retention policy (M2-L4, absorbing M2-T4).

   The roadmap row names three tests and each is a section below. Each includes a BREAK,
   because this project has three times had a proof accepted that was well formed and
   wrong (M1-T42, M1-T51, M2-T9's "Break A"), and a passing proof is therefore not by
   itself a result on this sequence.

   What each break is FOR, since a break that does not separate is decoration:

     (a) the double delete. Its guard is [Retention.retire]'s membership test, and the
         reason the guard has to exist rather than the audit catching it is D-0045's
         closing paragraph: [BAGUETTE_PROOF_AUDIT=1] CANNOT see a double delete, because
         a second [Writer.forget] is a no-op and the live set is already clean. So the
         break runs the deletion the guard refuses and shows what the CHECKER says -- the
         only thing that would otherwise have noticed, a long way from the mistake.

     (b) I-X3. A learned constraint that something still cites must not be retired. Same
         shape: the guard refuses, and the break performs it anyway and shows the
         checker's own rejection, so "our machinery catches it" is a claim with the
         alternative measured next to it.

     (a3) the OWNER. [Writer.wipe_level 0] would make a backjump a second owner of every
         learned constraint. It is refused, and the break shows what deleting a level-0
         id under a live citation costs.

   WHAT EACH BREAK REDDENS -- measured on 2026-09-18 by performing it, running this
   binary, and counting, not by reasoning about what it ought to catch. A guard whose
   removal reddens nothing is a guard nothing needs.

   | the break | reddens |
   |---|---|
   | [Retention.retire]'s guards off ([?unchecked] defaulted to true) | 10 of 65 |
   | the sweep reads [stats_learned] instead of the database -- THE bug this row is about | **18 of 65**, and the checker rejects: *"Trying to access constraint with ID 16 that has already been deleted"* |
   | [Writer.wipe_level] allows level 0 again | 2 of 65 |

   The middle row is the one to read. It is the pre-M2-L4 sweep put back: delete every id
   ever INTRODUCED rather than every id still HELD, which double-deletes whatever the
   policy already evicted. It is a double delete from ONE owner, which is a shape D-0045's
   two-owner warning does not cover, and the audit cannot see it -- so those 18 red checks
   and the checker's own words are the whole of the evidence that the fix is load-bearing.

   Declared domains here are 0..1 and 0..3, per CLAUDE.md: the order encoding is
   width-proportional (D-0028) and these scenes exist to make a database non-empty, not
   to be large. *)

module F = Baguette_flatzinc
module Compile = Baguette_flatzinc.Compile
module Store = Baguette_core.Store
module Justify = Baguette_core.Justify
module Search = Baguette_core.Search
module Retention = Baguette_core.Retention
module Learned = Baguette_core.Learned
module Lit = Baguette_proof.Lit
module Opb = Baguette_proof.Opb
module Encoding = Baguette_proof.Encoding
module Writer = Baguette_proof.Writer
module Pol = Baguette_proof.Writer.Pol

let () = Mem_guard.install ()
let failures = ref 0

let check name cond =
  if cond then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s\n" name)

let contains ~needle haystack =
  let n = String.length needle and h = String.length haystack in
  if n = 0 then true
  else if n > h then false
  else
    let found = ref false in
    for i = 0 to h - n do
      if (not !found) && String.equal (String.sub haystack i n) needle then found := true
    done;
    !found

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

let scratch prefix =
  let dir = Filename.temp_file prefix "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  dir

let cleanup dir =
  Array.iter
    (fun f -> try Sys.remove (Filename.concat dir f) with _ -> ())
    (try Sys.readdir dir with _ -> [||]);
  try Sys.rmdir dir with _ -> ()

(* ------------------------------------------------------------------ the checker *)

let veripb_path () = Baguette_proof.Checker.find ()

let veripb ~dir ~opb ~pbp =
  match veripb_path () with
  | None -> None
  | Some exe ->
      let log = Filename.concat dir "checker.log" in
      let rc =
        Sys.command
          (Printf.sprintf "%s %s %s > %s 2>&1" (Filename.quote exe) (Filename.quote opb)
             (Filename.quote pbp) (Filename.quote log))
      in
      let out = read_file log in
      (try Sys.remove log with _ -> ());
      Some (rc = 0, out)

(* The wording of the rejection every break in this file produces, MEASURED on 2026-09-18
   by running each break lane against VeriPB 3.0.2 and reading what it printed -- not
   taken from docs/PROOF-FORMAT.md and not guessed:

     "Trying to access constraint with ID 5 that has already been deleted"

   Matched at full strength minus the id, which varies with the scene. CLAUDE.md requires
   the wording rather than the exit status, because an exit status cannot tell a JUDGEMENT
   from a parse error -- and it requires full strength rather than a fragment, because a
   fragment like "deleted" would also match a `del range` diagnostic that means something
   else. *)
let deleted_wording = "that has already been deleted"

let expect_accepted ~title ~dir ~opb ~pbp =
  match veripb ~dir ~opb ~pbp with
  | None ->
      incr failures;
      Printf.printf "FAIL %s: %s -- I-X1 was NOT checked. Do not treat this as a pass.\n"
        title Baguette_proof.Checker.not_found_message
  | Some (true, _) ->
      check (Printf.sprintf "%s: veripb accepts the proof (I-X1)" title) true
  | Some (false, out) ->
      incr failures;
      Printf.printf "FAIL %s: veripb rejected the proof. It said:\n%s\n" title out

let expect_deleted_rejection ~title ~dir ~opb ~pbp =
  match veripb ~dir ~opb ~pbp with
  | None ->
      incr failures;
      Printf.printf
        "FAIL %s: %s -- the break was NOT checked. Do not treat this as a pass.\n" title
        Baguette_proof.Checker.not_found_message
  | Some (true, _) ->
      incr failures;
      Printf.printf
        "FAIL %s: the break was performed and veripb ACCEPTED the proof anyway. The \
         guard this lane exists to justify is not load-bearing; say so rather than \
         deleting the test.\n"
        title
  | Some (false, out) ->
      if contains ~needle:deleted_wording out then
        check
          (Printf.sprintf "%s: veripb rejects it, in the words this lane asserts" title)
          true
      else (
        incr failures;
        Printf.printf
          "FAIL %s: veripb rejected, but not with the wording this lane claims (%S). It \
           said:\n\
           %s\n"
          title deleted_wording out)

(* ------------------------------------------------------------------ the scenes *)

(* test/models/backjump_deep_unsat.fzn, verbatim. Chosen because it learns FOUR
   constraints from a search of a handful of nodes, which is the smallest thing a cap can
   fire on: with [cap = 2] the policy evicts two mid-search and the sweep takes two, so
   both halves of [n_added = n_evicted + n_swept] carry traffic. A scene where the cap
   never fires would let every check below pass vacuously. *)
let deep_src =
  "var 0..1: p;\n\
   var 0..1: q;\n\
   var 0..1: r;\n\
   var 0..3: x;\n\
   var 0..3: y;\n\
   constraint int_ne(x, y);\n\
   constraint int_eq(x, y);\n\
   solve satisfy;\n"

(* test/models/backjump_bool_unsat.fzn, verbatim: a second scene on the CONVERTIBLE path
   (Boolean order literals, D-0007's single-rung ladder), so the lanes below are not all
   measured on one shape of learned clause. It learns TWO constraints where [deep_src]
   learns four, which is why the cap travels with the scene below rather than being one
   constant: at cap 2 this scene's policy never fires and every lane over it would pass
   without the eviction path having run once. Measured, not assumed -- the first version
   of this file used one cap and the "not vacuous" check is what caught it. *)
let bool_src =
  "var 0..1: p;\n\
   var 0..1: q;\n\
   var bool: a;\n\
   var bool: b;\n\
   var bool: c;\n\
   var bool: d;\n\
   constraint array_bool_or([a, b], c);\n\
   constraint array_bool_and([a, b], d);\n\
   constraint bool_eq(c, d);\n\
   constraint bool_clause([a, b], []);\n\
   constraint bool_clause([], [a, b]);\n\
   solve satisfy;\n"

(* The scenes, each with the cap at which its policy actually fires. See [bool_src]. *)
let scenes = [ ("deep", deep_src, 2); ("bool", bool_src, 1) ]

type run = {
  r_proof : string;
  r_db : Retention.t;
  r_stats : Search.stats;
  r_audit_error : string option;
  r_dir : string;
  r_opb : string;
  r_pbp : string;
}

(* Solve one model into a scratch directory with the audit ON.

   The audit matters here for a reason it does not elsewhere: I-X2's live set must be
   empty at [conclusion], and a learned constraint is the one object in this solver whose
   lifetime is not a level's, so a retention policy that forgets to delete something
   surfaces here and nowhere else. [Writer.Audit_failed] is caught rather than allowed to
   abort, so a leak is one red check and not a dead binary. *)
(* M2-L12 added [?propagate_learned], defaulting to the SHIPPED build (true). Several
   lanes below now run both ways, and the reason is the row's finding rather than
   thoroughness: with a learned constraint given a runtime consumer, every constraint on
   these two scenes is CITED, so no policy can evict anything and the lanes that measure
   the policy's own mechanics have no eviction to measure. [false] is the M2-L4 build in
   which they do -- the same binary, one config field -- and it is the side M2-L4's
   original assertions are kept verbatim on. *)
let run ?(policy = Retention.keep_all) ?(propagate_learned = true) src =
  let m = F.Builder.of_string ~file:"test" src in
  let c = Compile.compile m in
  let dir = scratch "baguette_retention" in
  let opb = Filename.concat dir "m.opb" and pbp = Filename.concat dir "m.pbp" in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "M2-L4" ] c.Compile.encoding oc;
  close_out oc;
  let oc = open_out pbp in
  let writer = Writer.create ~audit:true oc in
  Encoding.start_proof c.Compile.encoding writer;
  let ctx = Justify.create ~writer ~encoding:c.Compile.encoding in
  let stats = Search.stats_create () in
  let audit_error = ref None in
  (try
     ignore
       (Search.solve ~engine:c.Compile.engine ~store:c.Compile.store ~ctx
          ~check:(fun _ -> true)
          ~stats
          ~config:{ Search.default_config with retention = policy; propagate_learned }
          ())
   with Writer.Audit_failed r -> audit_error := Some r);
  close_out oc;
  {
    r_proof = read_file pbp;
    r_db = Search.stats_db stats;
    r_stats = stats;
    r_audit_error = !audit_error;
    r_dir = dir;
    r_opb = opb;
    r_pbp = pbp;
  }

(* Every constraint id cited by a `del` rule in a proof, in order, WITH repeats.

   Written over the emitted text rather than over our own bookkeeping on purpose: I-X2 is
   a property of the proof, and the audit checks us against ourselves (D-0045). A
   `del range LO HI` is half-open (M1-T22) and names a span rather than its members, so
   it is expanded here to `[LO, HI)`; a `del id` names its citations directly. Labels are
   `@cN` (D-0023), so the id is what follows the `c`. *)
let del_citations proof =
  let ids = ref [] in
  let id_of tok =
    let t = String.trim tok in
    if String.length t >= 2 && t.[0] = '@' && t.[1] = 'c' then
      int_of_string_opt (String.sub t 2 (String.length t - 2))
    else None
  in
  List.iter
    (fun line ->
      let line = String.trim line in
      let toks = String.split_on_char ' ' line |> List.filter (fun s -> s <> "") in
      match toks with
      | "del" :: "id" :: rest ->
          List.iter
            (fun t -> match id_of t with Some i -> ids := i :: !ids | None -> ())
            rest
      | "del" :: "range" :: lo :: hi :: _ -> (
          match (id_of lo, id_of hi) with
          | Some a, Some b ->
              for i = a to b - 1 do
                ids := i :: !ids
              done
          | _ -> ())
      | _ -> ())
    (String.split_on_char '\n' proof);
  List.rev !ids

let has_duplicate l =
  let sorted = List.sort compare l in
  let rec go = function a :: (b :: _ as rest) -> a = b || go rest | _ -> false in
  go sorted

(* ============================================================ (a) I-X2, deletion on *)

(* Every learned id deleted exactly once, and the two sources of a deletion -- the policy
   and the end-of-search sweep -- adding up to the number introduced with nothing
   left over and nothing counted twice. *)
let test_a_exactly_once () =
  List.iter
    (fun (name, src, cap) ->
      (* M2-L12: on the M2-L4 build. This lane is about I-X2 -- every learned id deleted
         exactly ONCE, by the policy or by the sweep, adding up -- and it needs the
         policy to actually evict to be about anything. On the shipped build it cannot,
         because every learned constraint on these scenes has a consumer and [reduce]
         refuses to evict a cited one; [test_a_pinned_on_the_shipped_build] below is that
         side, with the same adding-up check on it. *)
      let r = run ~policy:(Retention.lbd ~cap) ~propagate_learned:false src in
      let db = r.r_db in
      let title s = Printf.sprintf "(a) %s: %s" name s in
      (* Not vacuous: if the cap never fired, every check below would be a check about
         [keep_all] wearing a policy's name. *)
      check
        (title "the policy actually evicted something (the lane is not vacuous)")
        (Retention.n_evicted db > 0);
      check
        (title "added = evicted + swept, and nothing is still held")
        (Retention.n_added db = Retention.n_evicted db + Retention.n_swept db
        && Retention.size db = 0);
      check
        (title "the search introduced as many ids as the database was given")
        (List.length (Search.stats_learned r.r_stats) = Retention.n_added db);
      (* The proof's own answer, independent of our bookkeeping. *)
      let cites = del_citations r.r_proof in
      check (title "no id is cited by two `del` rules") (not (has_duplicate cites));
      List.iter
        (fun cid ->
          check
            (Printf.sprintf "%s: learned id %d is deleted exactly once in the proof text"
               (title "") cid)
            (List.length (List.filter (fun i -> i = cid) cites) = 1))
        (Search.stats_learned r.r_stats);
      check
        (title "I-X2: the live set is empty at conclusion (no Audit_failed)")
        (r.r_audit_error = None);
      expect_accepted
        ~title:(title "the proof with the policy on")
        ~dir:r.r_dir ~opb:r.r_opb ~pbp:r.r_pbp;
      cleanup r.r_dir)
    scenes

(* M2-L12, the other side of the lane above: the SHIPPED build, where the same cap
   evicts NOTHING.

   This is not a weaker version of the check above, it is the finding. Every learned
   constraint on these two scenes gets a runtime consumer -- a unit becomes a global
   bound tightening, a wider clause a registered [Clause.Learned_clause] instance -- and
   [Retention.reduce] refuses to evict a cited constraint, so the cap is SOFT. I-X2 still
   has to hold: everything the policy could not evict has to be swept at the end, which
   is the adding-up check repeated here against a zero eviction count. *)
let test_a_pinned_on_the_shipped_build () =
  List.iter
    (fun (name, src, cap) ->
      let r = run ~policy:(Retention.lbd ~cap) src in
      let db = r.r_db in
      let title s = Printf.sprintf "(a) %s shipped: %s" name s in
      check
        (title "every learned constraint has a consumer, so the policy evicts NOTHING")
        (Retention.n_evicted db = 0 && Retention.n_cited db > 0);
      check
        (title "...and the refusals are counted rather than raised")
        (Retention.n_pinned db > 0);
      check
        (title "I-X2 still adds up: what the cap could not evict, the sweep took")
        (Retention.n_added db = Retention.n_swept db && Retention.size db = 0);
      check
        (title "no id is cited by two `del` rules")
        (not (has_duplicate (del_citations r.r_proof)));
      check
        (title "I-X2: the live set is empty at conclusion (no Audit_failed)")
        (r.r_audit_error = None);
      expect_accepted ~title:(title "the proof") ~dir:r.r_dir ~opb:r.r_opb ~pbp:r.r_pbp;
      cleanup r.r_dir)
    scenes

(* The guard, at the module level: a second retirement of one id is refused, and the
   refusal happens BEFORE anything is written. *)
let test_a_double_delete_guard () =
  let dir = scratch "baguette_ret_dd" in
  let pbp = Filename.concat dir "m.pbp" in
  let oc = open_out pbp in
  let e = Encoding.create () in
  let model = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "uu" 2) ] 1) in
  ignore model;
  let w = Writer.create ~audit:true oc in
  let opb = Filename.concat dir "m.opb" in
  let ooc = open_out opb in
  Encoding.write_opb e ooc;
  close_out ooc;
  Encoding.start_proof e w;
  let ctx = Justify.create ~writer:w ~encoding:e in
  let db = Retention.create ~policy:Retention.keep_all () in
  let row = Learned.of_clause [ Lit.ge "uu" 2 ] in
  let cid = Learned.introduce ctx row ~origin:"test" in
  ignore (Retention.add db ~cid ~row ~lbd:1 ~origin:"test");
  ignore (Retention.retire db ctx ~why:"first" [ cid ]);
  let before = pos_out oc in
  let caught =
    try
      ignore (Retention.retire db ctx ~why:"second" [ cid ]);
      None
    with Retention.Double_delete m -> Some m
  in
  check "(a) a second retirement of one id raises Double_delete" (caught <> None);
  check "(a) the Double_delete message names the invariant and the first owner"
    (match caught with
    | Some m -> contains ~needle:"SECOND time" m && contains ~needle:"D-0045" m
    | None -> false);
  check "(a) the refused deletion wrote NOTHING to the proof" (pos_out oc = before);
  check "(a) an id the database does not hold cannot be deleted through it"
    (try
       ignore (Retention.retire db ctx ~why:"stranger" [ cid + 99 ]);
       false
     with Retention.Not_owned _ -> true);
  close_out oc;
  cleanup dir

(* The BREAK for (a): perform the second deletion the guard refuses, and let the checker
   answer. This is what makes the guard's existence a measurement -- without it the double
   delete is invisible to us (a second [Writer.forget] is a no-op) and is caught only
   here. *)
let test_a_double_delete_break () =
  let dir = scratch "baguette_ret_ddb" in
  let opb = Filename.concat dir "m.opb" and pbp = Filename.concat dir "m.pbp" in
  let e = Encoding.create () in
  let c_pos = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "uu" 2) ] 1) in
  let c_neg = Encoding.add_constraint e (Opb.ge [ (1, Lit.negate (Lit.ge "uu" 2)) ] 1) in
  let ooc = open_out opb in
  Encoding.write_opb e ooc;
  close_out ooc;
  let oc = open_out pbp in
  let w = Writer.create ~audit:false oc in
  Encoding.start_proof e w;
  let ctx = Justify.create ~writer:w ~encoding:e in
  let db = Retention.create ~policy:Retention.keep_all () in
  let row = Learned.of_clause [ Lit.ge "uu" 2 ] in
  let cid = Learned.introduce ctx row ~origin:"break" in
  ignore (Retention.add db ~cid ~row ~lbd:1 ~origin:"break");
  ignore (Retention.retire db ctx ~why:"the owner's deletion" [ cid ]);
  (* ~unchecked is the break: the same call with the guards off. *)
  Retention.retire ~unchecked:true db ctx ~why:"a second owner's deletion" [ cid ];
  let contra = Writer.pol w ~origin:"contradiction" Pol.(sum [ id c_pos; id c_neg ]) in
  Writer.conclusion w (Writer.Unsat (Some contra));
  close_out oc;
  expect_deleted_rejection ~title:"(a) BREAK: the same learned id deleted twice" ~dir ~opb
    ~pbp;
  cleanup dir

(* The OWNER, made structural. [Writer.wipe_level 0] is what would turn a backjump into a
   second owner of every learned constraint, and it is refused. *)
let test_a_wipe_level_zero_refused () =
  let dir = scratch "baguette_ret_w0" in
  let pbp = Filename.concat dir "m.pbp" in
  let oc = open_out pbp in
  let w = Writer.create ~audit:false oc in
  let msg =
    try
      Writer.wipe_level w 0;
      None
    with Invalid_argument m -> Some m
  in
  check "(a) Writer.wipe_level 0 is refused" (msg <> None);
  check "(a) ...and the refusal names who does own level 0"
    (match msg with
    | Some m -> contains ~needle:"Retention" m && contains ~needle:"Trace" m
    | None -> false);
  check "(a) a negative level is still refused"
    (try
       Writer.wipe_level w (-1);
       false
     with Invalid_argument _ -> true);
  check "(a) a decision level is still accepted"
    (try
       Writer.wipe_level w 1;
       true
     with Invalid_argument _ -> false);
  close_out oc;
  cleanup dir

(* And what it would have cost. A level-0 id deleted while a later line still cites it is
   caught by the checker and by nothing of ours -- the wording below is the whole reason
   the refusal above is a refusal and not a comment. *)
let test_a_level_zero_deletion_costs () =
  let dir = scratch "baguette_ret_w0b" in
  let opb = Filename.concat dir "m.opb" and pbp = Filename.concat dir "m.pbp" in
  let e = Encoding.create () in
  let c_pos = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "uu" 2) ] 1) in
  let c_neg = Encoding.add_constraint e (Opb.ge [ (1, Lit.negate (Lit.ge "uu" 2)) ] 1) in
  let ooc = open_out opb in
  Encoding.write_opb e ooc;
  close_out ooc;
  let oc = open_out pbp in
  let w = Writer.create ~audit:false oc in
  Encoding.start_proof e w;
  let level0 = Writer.pol w ~origin:"a level-0 line" (Pol.id c_pos) in
  check "(a) a line derived at level 0 is tagged 0" (Writer.tag_of w level0 = Some 0);
  Writer.delete w level0;
  ignore (Writer.pol w ~origin:"citing it afterwards" (Pol.id level0));
  let contra = Writer.pol w ~origin:"contradiction" Pol.(sum [ id c_pos; id c_neg ]) in
  Writer.conclusion w (Writer.Unsat (Some contra));
  close_out oc;
  expect_deleted_rejection ~title:"(a) BREAK: a level-0 id deleted and then cited" ~dir
    ~opb ~pbp;
  cleanup dir

(* ================================================================= (b) I-X3 *)

(* A deleted reason must not be referenced by any live trail entry. The guard is
   [Retention.cite] plus [retire]'s check on it. *)
let test_b_cited_is_caught () =
  let dir = scratch "baguette_ret_cite" in
  let opb = Filename.concat dir "m.opb" and pbp = Filename.concat dir "m.pbp" in
  let e = Encoding.create () in
  ignore (Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "uu" 2) ] 1));
  let ooc = open_out opb in
  Encoding.write_opb e ooc;
  close_out ooc;
  let oc = open_out pbp in
  let w = Writer.create ~audit:true oc in
  Encoding.start_proof e w;
  let ctx = Justify.create ~writer:w ~encoding:e in
  let db = Retention.create ~policy:(Retention.lbd ~cap:0) () in
  let row = Learned.of_clause [ Lit.ge "uu" 2 ] in
  let cid = Learned.introduce ctx row ~origin:"cited" in
  ignore (Retention.add db ~cid ~row ~lbd:1 ~origin:"cited");
  Retention.cite db ~cid ~by:"trail entry 7 (x >= 2)";
  let before = pos_out oc in
  (* M2-L12 SPLIT THIS IN TWO, and the split is the point rather than a relaxation.

     Through the POLICY ([cap = 0] wants this constraint gone on the very next reduce)
     the eviction is now REFUSED AND COUNTED, not raised. A cap that cannot be met
     because everything under it is in use is a policy outcome, and with a learned
     constraint given a runtime consumer it is the ordinary case -- raising there would
     make BAGUETTE_RETENTION abort the solver on any real model.

     Through [retire] DIRECTLY it still raises, because that is a caller deleting
     something it should have known was in use: a fault, and the one the row asks our
     machinery to catch instead of the checker. Every assertion M2-L4 made about the
     message is kept, on that call. *)
  check "(b) the policy does not evict a constraint that is still cited"
    (Retention.reduce db ctx = []);
  check "(b) ...and the refusal is counted rather than raised" (Retention.n_pinned db = 1);
  let direct =
    try
      Retention.retire db ctx ~why:"a caller that should have known better" [ cid ];
      None
    with Retention.Cited m -> Some m
  in
  check "(b) retiring a cited constraint DIRECTLY still raises" (direct <> None);
  check "(b) the refusal names I-X3 and what cites it"
    (match direct with
    | Some m -> contains ~needle:"I-X3" m && contains ~needle:"trail entry 7" m
    | None -> false);
  check "(b) the refusal names what the checker would OTHERWISE have said"
    (match direct with Some m -> contains ~needle:deleted_wording m | None -> false);
  check "(b) the refused eviction wrote NOTHING to the proof" (pos_out oc = before);
  check "(b) the constraint is still held after the refusal" (Retention.holds db cid);
  (* Release the citation and the same eviction now goes through: the guard is about the
     citation and not about this constraint. *)
  Retention.uncite db ~cid;
  check "(b) once the citation is released the eviction proceeds"
    (Retention.reduce db ctx = [ cid ]);
  check "(b) ...and the database no longer holds it" (not (Retention.holds db cid));
  close_out oc;
  cleanup dir

(* The BREAK for (b): delete the cited constraint anyway, then cite it. The checker is
   what notices, which is exactly what the row says must not be allowed to be the case. *)
let test_b_cited_break () =
  let dir = scratch "baguette_ret_citeb" in
  let opb = Filename.concat dir "m.opb" and pbp = Filename.concat dir "m.pbp" in
  let e = Encoding.create () in
  let c_pos = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "uu" 2) ] 1) in
  let c_neg = Encoding.add_constraint e (Opb.ge [ (1, Lit.negate (Lit.ge "uu" 2)) ] 1) in
  let ooc = open_out opb in
  Encoding.write_opb e ooc;
  close_out ooc;
  let oc = open_out pbp in
  let w = Writer.create ~audit:false oc in
  Encoding.start_proof e w;
  let ctx = Justify.create ~writer:w ~encoding:e in
  let db = Retention.create ~policy:Retention.keep_all () in
  let row = Learned.of_clause [ Lit.ge "uu" 2 ] in
  let cid = Learned.introduce ctx row ~origin:"cited" in
  ignore (Retention.add db ~cid ~row ~lbd:1 ~origin:"cited");
  Retention.cite db ~cid ~by:"a live trail entry";
  Retention.retire ~unchecked:true db ctx ~why:"the break" [ cid ];
  ignore (Writer.pol w ~origin:"the citation that was still live" (Pol.id cid));
  let contra = Writer.pol w ~origin:"contradiction" Pol.(sum [ id c_pos; id c_neg ]) in
  Writer.conclusion w (Writer.Unsat (Some contra));
  close_out oc;
  expect_deleted_rejection ~title:"(b) BREAK: a cited learned constraint deleted" ~dir
    ~opb ~pbp;
  cleanup dir

(* M2-L4 asserted here that no learned constraint is cited by anything, on any scene,
   because none of them propagated -- and said in as many words that this "is the
   assertion that FAILS the day one does, which is when the activity policy stops being
   the constant zero and this row's choice has to be revisited".

   **M2-L12 is that day, and the assertion did fail**, which is the whole of why it was
   written. It is INVERTED here rather than deleted, so the property is still pinned and
   still has a control: on the shipped build a real search cites, on the
   [propagate_learned = false] build it does not. What the revisiting concluded is in
   lib/core/retention.ml's header -- keep_all stands, on a different argument. *)
let test_b_citations_in_a_real_search () =
  List.iter
    (fun (name, src, cap) ->
      let r = run ~policy:(Retention.lbd ~cap) src in
      check
        (Printf.sprintf
           "(b) %s: a real search DOES cite a learned constraint now (M2-L12) -- \
            activity is no longer the constant zero"
           name)
        (Retention.n_cited r.r_db > 0);
      check
        (Printf.sprintf "(b) %s: ...and the scene did learn something to be cited" name)
        (Retention.n_added r.r_db > 0);
      cleanup r.r_dir;
      (* The control, and it is the same binary: without a consumer there is nothing to
         cite, which is the state M2-L4 measured and the state this assertion had to be
         able to tell apart from the one above. *)
      let off = run ~policy:(Retention.lbd ~cap) ~propagate_learned:false src in
      check
        (Printf.sprintf
           "(b) %s control: with propagate_learned off nothing is cited at all" name)
        (Retention.n_cited off.r_db = 0 && Retention.n_added off.r_db > 0);
      cleanup off.r_dir)
    scenes

(* ==================================================== (c) .pbp bytes, on and off *)

(* The row asks for the bytes both ways, and M1-T59's duplicate `rup` lines are why: they
   are harmless per-proof and stop being harmless per-pruning, and a retention policy that
   evicts and lets the same clause be re-learned is how that happens.

   Three things are asserted, and the third is the finding:

     - both proofs are ACCEPTED. A cheaper policy that broke the proof would be no
       policy at all.
     - the two proofs DIFFER. A before/after whose two sides are identical is no
       evidence (CLAUDE.md), and this comparison would be exactly that if the policy
       silently did nothing.
     - the policy does NOT cause re-derivation: the duplicate count is the same with the
       policy on and off, because nothing consults the database before introducing a
       learned constraint. So M1-T59's duplicates are still a property of what is
       learned, not of what is retained -- which is the thing to re-measure the day
       something does consult it. *)
let test_c_bytes_both_ways () =
  List.iter
    (fun (name, src, cap) ->
      (* M2-L12: on the M2-L4 build, for the reason [test_a_exactly_once] states -- a
         bytes-on-versus-off comparison needs the policy to evict, and on the shipped
         build it cannot. The shipped build's answer is the lane below, and it is the
         opposite assertion: byte-IDENTICAL, because nothing was evicted. *)
      let off = run ~policy:Retention.keep_all ~propagate_learned:false src in
      let on = run ~policy:(Retention.lbd ~cap) ~propagate_learned:false src in
      let title s = Printf.sprintf "(c) %s: %s" name s in
      expect_accepted ~title:(title "policy OFF") ~dir:off.r_dir ~opb:off.r_opb
        ~pbp:off.r_pbp;
      expect_accepted ~title:(title "policy ON") ~dir:on.r_dir ~opb:on.r_opb ~pbp:on.r_pbp;
      check
        (title "the policy evicted, so the comparison has two sides")
        (Retention.n_evicted on.r_db > 0 && Retention.n_evicted off.r_db = 0);
      check (title "the two proofs are not byte-identical") (off.r_proof <> on.r_proof);
      (* Reported so the figure is in the run's output and not only in a commit message:
         a reader of a red suite can see which way the bytes went. *)
      Printf.printf
        "     (c) %s: .pbp bytes  off=%d  on(lbd cap=%d)=%d  (%+d)  -- `del` citations \
         off=%d on=%d\n"
        name (String.length off.r_proof) cap (String.length on.r_proof)
        (String.length on.r_proof - String.length off.r_proof)
        (List.length (del_citations off.r_proof))
        (List.length (del_citations on.r_proof));
      check
        (title "eviction does not cause re-derivation (the duplicate count is unmoved)")
        (Retention.n_duplicate on.r_db = Retention.n_duplicate off.r_db);
      check
        (title "the same ids are introduced either way")
        (List.length (Search.stats_learned on.r_stats)
        = List.length (Search.stats_learned off.r_stats));
      cleanup off.r_dir;
      cleanup on.r_dir)
    scenes

(* M2-L12: the same comparison on the SHIPPED build, where it comes out the other way.

   D-0051's cap sweep was re-run for this row (lib/core/retention.ml's header has the
   table) and its conclusion is that eviction still buys nothing -- but for a new reason:
   what a policy may evict has no consumer, and what has a consumer it may not evict. On
   these two scenes that is total: nothing is evicted at any cap, so the proof under
   `lbd:<cap>` is BYTE-IDENTICAL to the proof under keep_all.

   Asserting byte-identity is the opposite of what a before/after usually wants, and it is
   asserted here for the same reason CLAUDE.md distrusts it: identical bytes are no
   evidence UNLESS you know why. Here the why is checked beside it -- zero evicted, a
   positive pinned count -- so the identity is a measurement and not two runs of the same
   binary by accident. *)
let test_c_bytes_on_the_shipped_build () =
  List.iter
    (fun (name, src, cap) ->
      let off = run ~policy:Retention.keep_all src in
      let on = run ~policy:(Retention.lbd ~cap) src in
      let title s = Printf.sprintf "(c) %s shipped: %s" name s in
      expect_accepted ~title:(title "policy OFF") ~dir:off.r_dir ~opb:off.r_opb
        ~pbp:off.r_pbp;
      expect_accepted ~title:(title "policy ON") ~dir:on.r_dir ~opb:on.r_opb ~pbp:on.r_pbp;
      check
        (title "the cap evicted nothing, because everything under it is cited")
        (Retention.n_evicted on.r_db = 0 && Retention.n_pinned on.r_db > 0);
      check
        (title "...so the two proofs ARE byte-identical, and that is the finding")
        (off.r_proof = on.r_proof);
      cleanup off.r_dir;
      cleanup on.r_dir)
    scenes

(* ==================================================== determinism and the policy axis *)

(* The gate requires two runs of one binary to be byte-identical, and a learned database
   iterated in hash order is the specific way learning breaks it (learn.ml's header names
   this module as the inheritor of that obligation). Two solves of one scene under one
   policy must produce one proof. *)
let test_determinism () =
  List.iter
    (fun policy ->
      let a = run ~policy deep_src and b = run ~policy deep_src in
      check
        (Printf.sprintf "determinism: two runs under %s emit the same proof"
           (Retention.name policy))
        (a.r_proof = b.r_proof);
      cleanup a.r_dir;
      cleanup b.r_dir)
    (Retention.policies ~cap:2)

(* Each policy on the axis is a policy: it evicts only what the database holds, and the
   proof it produces is accepted. [keep_all] evicting nothing is part of the statement. *)
let test_policy_axis () =
  List.iter
    (fun policy ->
      let r = run ~policy deep_src in
      let title s = Printf.sprintf "axis %s: %s" (Retention.name policy) s in
      check
        (title "added = evicted + swept, nothing left held")
        (Retention.n_added r.r_db = Retention.n_evicted r.r_db + Retention.n_swept r.r_db
        && Retention.size r.r_db = 0);
      check
        (title "no id is cited by two `del` rules")
        (not (has_duplicate (del_citations r.r_proof)));
      expect_accepted ~title:(title "the proof") ~dir:r.r_dir ~opb:r.r_opb ~pbp:r.r_pbp;
      cleanup r.r_dir)
    (Retention.policies ~cap:2)

let () =
  test_a_exactly_once ();
  test_a_pinned_on_the_shipped_build ();
  test_a_double_delete_guard ();
  test_a_double_delete_break ();
  test_a_wipe_level_zero_refused ();
  test_a_level_zero_deletion_costs ();
  test_b_cited_is_caught ();
  test_b_cited_break ();
  test_b_citations_in_a_real_search ();
  test_c_bytes_both_ways ();
  test_c_bytes_on_the_shipped_build ();
  test_determinism ();
  test_policy_axis ();
  if !failures > 0 then (
    Printf.printf "\n%d FAILURE(S)\n" !failures;
    exit 1)
  else print_endline "\nall retention tests passed"
