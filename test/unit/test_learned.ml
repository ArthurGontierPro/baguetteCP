(* Unit tests for lib/core/learned.ml -- the learned-constraint type, its runtime
   instance, and its proof-side introduction and deletion (M2-L1, D-0044, D-0045).

   The roadmap row names six tests and each is a section below. Two of them are the
   reason this file exists at all rather than being tests of a new propagator:

     (b) is THE D-0044 CHECK. If a degree-1, unit-coefficient [Learned.t] over order
         literals does NOT propagate as [Bool_clause] does on the same scene, D-0044's
         central claim -- "a clause is the degree-1 case of a PB inequality, not a
         separate type" -- is wrong, and M2-L3's staging has to be revisited. It is
         written as a brute force over every scene rather than as a handful of cases,
         because a claim that broad is not settled by three examples.

     (f) is I-X10's closure, and what it asks of this row is unusual: the gate in
         test_trace.ml fires when a NEW module appears in lib/core/prop/. This row's
         whole architectural bet is that no such module appears, so the gate staying
         silent is the bet paying off rather than the check being missed. The section
         below asserts that in as many words, so that "the gate did not fire" is
         recorded as a measurement instead of an absence.

   The collision D-0045's addendum predicted -- a learned constraint deleted by the
   backjump that follows learning it -- is measured in test_proof.ml, next to
   [Writer.wipe_level], because it is a property of the writer and not of this type.

   Declared domains here are 0..4 and 0..1. D-0028 makes the order encoding
   width-proportional, and the declared width is also the brute-force oracle's search
   space: 5^2 = 25 assignments and 2^3 = 8, with 15^2 and 3^3 sub-boxes over them. *)

module Domain = Baguette_core.Domain
module Store = Baguette_core.Store
module Var = Baguette_core.Var
module Reason = Baguette_core.Reason
module Explanation = Baguette_core.Explanation
module Propagator = Baguette_core.Propagator
module Linear = Baguette_core.Linear

(* M2-L12/D-0052: bool_clause.ml was widened to general order literals and renamed
   [Clause]; the Boolean face this file exercises is [Clause.make] plus the DOMAIN-
   declaring submodules. Aliased under the old name so that every check below still says
   which propagator it is about. What the widening ADDED is tested in test_clause.ml. *)
module Bool_clause = Baguette_core.Clause
module Engine = Baguette_core.Engine
module Justify = Baguette_core.Justify
module Learned = Baguette_core.Learned
module Lit = Baguette_proof.Lit
module Opb = Baguette_proof.Opb
module Encoding = Baguette_proof.Encoding
module Writer = Baguette_proof.Writer

let () = Mem_guard.install ()
let failures = ref 0

let check name cond =
  if cond then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s\n" name)

(* ----------------------------------------------------------------- scaffolding *)

let store_of boxes =
  let names = Array.of_list (List.map fst boxes) in
  let domains = Array.of_list (List.map (fun (_, (lo, hi)) -> Domain.make lo hi) boxes) in
  Store.create ~names ~domains

let encoding_of decls =
  let enc = Encoding.create () in
  List.iter (fun (n, (lo, hi)) -> Encoding.declare_int enc n ~lo ~hi) decls;
  enc

(* Run one packed instance to its own fixpoint (I-P3 says one pass suffices for
   [Linear]; [Bool_clause] needs to be re-run because assigning a literal can expose the
   next unit). Returns [true] on conflict. Bracketed with [Store.with_running] so the
   trail is attributed exactly as the engine would attribute it. *)
let run_to_fixpoint (inst : Propagator.instance) store =
  let rec go n =
    if n > 40 then failwith "run_to_fixpoint: did not settle"
    else
      let before = Store.trail_length store in
      match
        Store.with_running store inst.Propagator.id (fun () -> inst.Propagator.run store)
      with
      | Propagator.Conflict _ -> true
      | Propagator.Fixpoint ->
          if Store.trail_length store > before then go (n + 1) else false
  in
  go 0

let domains_of store =
  List.init (Store.n_vars store) (fun i ->
      let d = Store.get store (Var.of_int i) in
      (Domain.lo d, Domain.hi d))

(* Narrow one variable to [lo, hi] by POSTING A ROW, not by building a store that was
   born narrow.

   Two propagators in this file read a variable's DECLARED domain at [make] time and
   would see a different one if the scene were set up by construction: [Linear] freezes
   it (D-0010), and [Bool_clause] outright refuses a literal whose variable is not
   declared over [0, 1] (D-0007) -- which is what caught the first version of test (b).
   Posting `-x <= -lo` / `x <= hi` reaches the same box through the same door the solver
   uses, so every propagator in the scene agrees about what was declared.

   The same trick test_analysis.ml uses for a decision, and for the same reason: no test
   here ever constructs a [Reason.justified] by hand. *)
let narrow store name (lo, hi) =
  let v = Option.get (Store.var_named store name) in
  let post terms rhs =
    let lin = Linear.make ~row_id:900 store terms rhs in
    let i =
      Propagator.pack ~id:90 (module Linear : Propagator.S with type t = Linear.t) lin
    in
    ignore (run_to_fixpoint i store)
  in
  if lo > Domain.lo (Store.get store v) then post [ (-1, v) ] (-lo);
  if hi < Domain.hi (Store.get store v) then post [ (1, v) ] hi

(* A [Justify.ctx] writing into a scratch file, plus the path so a test can read the
   proof back. [~audit] threads through to [Writer.create]. *)
let ctx_in_file ?(audit = false) ~decls () =
  let path = Filename.temp_file "baguette-learned" ".pbp" in
  let oc = open_out path in
  let w = Writer.create ~audit oc in
  let enc = encoding_of decls in
  Writer.header w ~n_model_constraints:0;
  (Justify.create ~writer:w ~encoding:enc, enc, w, oc, path)

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let count_substring hay needle =
  let n = String.length needle in
  let rec go i acc =
    if i + n > String.length hay then acc
    else if String.sub hay i n = needle then go (i + 1) (acc + 1)
    else go (i + 1) acc
  in
  go 0 0

(* ------------------------------------------------------------ the type itself *)

(* [make]'s normalisation, which everything below rests on: positive coefficients,
   merged repeats, zeros dropped. A negative coefficient is absorbed by negating its
   literal and raising the degree, which is the standard PB normalisation and is what
   makes "every coefficient is >= 1" a property of the type rather than of its callers. *)
let test_normalisation () =
  let a = Lit.ge "x" 2 and b = Lit.ge "y" 1 in
  let t = Learned.make [ (-2, a); (3, b); (0, Lit.ge "z" 1) ] 1 in
  check "make: a zero coefficient contributes nothing at all"
    (List.length (Learned.terms t) = 2);
  check "make: every coefficient is positive after normalisation"
    (List.for_all (fun tm -> tm.Learned.coeff > 0) (Learned.terms t));
  check "make: negating a literal raises the degree by |a|" (Learned.degree t = 3);
  check "make: the negated literal is the one that was negative"
    (List.exists
       (fun tm -> Lit.equal tm.Learned.lit (Lit.negate a) && tm.Learned.coeff = 2)
       (Learned.terms t));
  let merged = Learned.make [ (1, a); (2, a); (1, b) ] 2 in
  check "make: repeated literals are merged, not listed twice"
    (List.length (Learned.terms merged) = 2
    && List.exists
         (fun tm -> Lit.equal tm.Learned.lit a && tm.Learned.coeff = 3)
         (Learned.terms merged));
  let c = Learned.of_clause [ a; b ] in
  check "of_clause is make at degree 1 with unit coefficients" (Learned.is_clause c);
  check "a degree-2 row is not a clause"
    (not (Learned.is_clause (Learned.make [ (1, a); (1, b) ] 2)))

(* --------------------------------------------------------------- (a) the oracle *)

(* The bounds-consistent narrowing of  2x + 3y <= rhs  over a box, computed by
   enumeration rather than by arithmetic. This is the I-P1 oracle: it knows nothing
   about slack, division or rounding, so a propagator agreeing with it is agreeing with
   the constraint's meaning and not with a second copy of its own code. *)
let oracle_lin_le coeffs rhs box =
  let vars = Array.of_list box in
  let n = Array.length vars in
  let support = Array.make n [] in
  let rec go i assign acc =
    if i = n then (
      if acc <= rhs then
        List.iteri (fun j v -> support.(j) <- v :: support.(j)) (List.rev assign))
    else
      let lo, hi = vars.(i) in
      for v = lo to hi do
        go (i + 1) (v :: assign) (acc + (List.nth coeffs i * v))
      done
  in
  go 0 [] 0;
  if Array.exists (fun s -> s = []) support then None
  else
    Some
      (Array.to_list
         (Array.map
            (fun s -> (List.fold_left min max_int s, List.fold_left max min_int s))
            support))

(* Test (a). A model row, its .opb expansion, and the [Learned.t] built from that
   expansion must all prune the same way -- and the same way the oracle does.

   The expansion is [Encoding.linear_terms_int_lin_le], which is what
   lib/flatzinc/compile.ml itself uses for every `int_lin_le` it compiles (through
   [Encoding.add_int_lin_le]), so this IS the round trip through the .fzn path's own
   encoding, with the parser and the builder left out because they contribute nothing
   the round trip is about.

   The expansion is a "<=" over positive rungs; a [Learned.t] is a ">=", so every
   coefficient flips sign once and the degree is the negated right-hand side. Getting
   that flip wrong is the most likely way to write a test that passes vacuously, so the
   [None] case below is checked too: a row with an interior threshold has no linear form
   at all, and [to_linear] must say so rather than invent one. *)
let test_oracle_round_trip () =
  let decls = [ ("x", (0, 4)); ("y", (0, 4)) ] in
  let enc = encoding_of decls in
  let decl = Learned.decl_of_encoding enc in
  let coeffs = [ 2; 3 ] in
  let rhs = 7 in
  let opb_terms, const = Encoding.linear_terms_int_lin_le enc [ (2, "x"); (3, "y") ] in
  let learned =
    Learned.make (List.map (fun (a, l) -> (-a, l)) opb_terms) (-(rhs - const))
  in
  check "(a) the expansion is over order literals, one rung per declared step"
    (List.length opb_terms = 8);
  let boxes = ref [] in
  for xl = 0 to 4 do
    for xh = xl to 4 do
      for yl = 0 to 4 do
        for yh = yl to 4 do
          boxes := ((xl, xh), (yl, yh)) :: !boxes
        done
      done
    done
  done;
  let agree = ref 0 and disagree = ref 0 and oracle_disagree = ref 0 in
  List.iter
    (fun ((xl, xh), (yl, yh)) ->
      let mk () = store_of [ ("x", (xl, xh)); ("y", (yl, yh)) ] in
      (* the model row, as the front end builds it *)
      let s1 = mk () in
      let row =
        Linear.make ~row_id:1 s1
          [
            (2, Store.var_named s1 "x" |> Option.get);
            (3, Store.var_named s1 "y" |> Option.get);
          ]
          rhs
      in
      let i1 =
        Propagator.pack ~id:0 (module Linear : Propagator.S with type t = Linear.t) row
      in
      let c1 = run_to_fixpoint i1 s1 in
      (* the same row, round-tripped through Learned.t *)
      let s2 = mk () in
      let i2 = Option.get (Learned.instance ~id:0 ~row_id:1 s2 ~decl learned) in
      let c2 = run_to_fixpoint i2 s2 in
      if c1 = c2 && domains_of s1 = domains_of s2 then incr agree else incr disagree;
      (* and both against the oracle *)
      match oracle_lin_le coeffs rhs [ (xl, xh); (yl, yh) ] with
      | None -> if not c1 then incr oracle_disagree
      | Some want -> if c1 || domains_of s1 <> want then incr oracle_disagree)
    !boxes;
  check
    (Printf.sprintf
       "(a) round trip: Learned.t prunes identically to the model row on all %d boxes"
       (List.length !boxes))
    (!disagree = 0 && !agree = List.length !boxes);
  check "(a) and the model row itself agrees with the brute-force oracle (I-P1)"
    (!oracle_disagree = 0);
  (* The boundary the module header states, asserted rather than left as prose: an
     interior threshold on an integer variable has no linear form. *)
  let interior = Learned.of_clause [ Lit.ge "x" 3; Lit.ge "y" 2 ] in
  check "(a) an interior threshold has no linear form, and to_linear says None"
    (Learned.to_linear_row interior ~decl = None)

(* ------------------------------------------------------- (b) THE D-0044 CHECK *)

(* If this section goes red, D-0044's central claim is wrong.

   The scene is a three-literal clause over `var bool`s, which D-0007 order-encodes on
   [0, 1]: "b is true" is [b >= 1] and "b is false" is [~(b >= 1)]. So the clause
   b0 \/ b1 \/ ~b2 is the PB constraint  b0_ge_1 + b1_ge_1 + ~b2_ge_1 >= 1  over exactly
   the variables the .opb already contains -- no conversion, no auxiliary variable, which
   is the property D-0044 says our eager order encoding buys us and Pumpkin's LLG lacks.

   "Propagates exactly as Bool_clause does" is checked over EVERY scene: each of the
   three Booleans independently fixed to 0, fixed to 1, or left open, so 27 in all. On
   each one both propagators are run to fixpoint and compared on (i) whether they
   conflict and (ii) the resulting domains, value for value. Anything weaker would let a
   [Learned.t] that merely never contradicts [Bool_clause] pass as one that agrees with
   it.

   [Bool_clause] is DOMAIN consistent and the learned instance is [Linear], which is
   BOUNDS consistent. That is not a gap here and it is worth saying why rather than
   hoping: a Boolean has no interior, so on a 0/1 variable bounds and domain consistency
   are the same relation, and unit propagation on a clause is exactly what bounds
   propagation on the corresponding linear row does. The 27 scenes are what turns that
   argument into a measurement. *)
let test_d0044_clause_is_degree_one () =
  let decls = [ ("b0", (0, 1)); ("b1", (0, 1)); ("b2", (0, 1)) ] in
  let enc = encoding_of decls in
  let decl = Learned.decl_of_encoding enc in
  let learned =
    Learned.of_clause [ Lit.bool_true "b0"; Lit.bool_true "b1"; Lit.bool_false "b2" ]
  in
  check "(b) the clause really is the degree-1 unit-coefficient case"
    (Learned.is_clause learned && Learned.degree learned = 1);
  check "(b) and it has a linear form, so no new propagator family is needed"
    (Learned.to_linear_row learned ~decl <> None);
  let opts = [ (0, 0); (1, 1); (0, 1) ] in
  let scenes =
    List.concat_map
      (fun a -> List.concat_map (fun b -> List.map (fun c -> (a, b, c)) opts) opts)
      opts
  in
  let disagree = ref [] and fired = ref 0 and conflicted = ref 0 in
  List.iter
    (fun (a, b, c) ->
      let mk () = store_of [ ("b0", (0, 1)); ("b1", (0, 1)); ("b2", (0, 1)) ] in
      let scene s =
        narrow s "b0" a;
        narrow s "b1" b;
        narrow s "b2" c
      in
      let s1 = mk () in
      let v n = Option.get (Store.var_named s1 n) in
      let cl = Bool_clause.make s1 [ (v "b0", true); (v "b1", true); (v "b2", false) ] in
      let i1 =
        Propagator.pack ~id:0
          (module Bool_clause : Propagator.S with type t = Bool_clause.t)
          cl
      in
      scene s1;
      let c1 = run_to_fixpoint i1 s1 in
      let s2 = mk () in
      let i2 = Option.get (Learned.instance ~id:0 ~row_id:1 s2 ~decl learned) in
      scene s2;
      let c2 = run_to_fixpoint i2 s2 in
      if c1 then incr conflicted;
      if (not c1) && domains_of s1 <> [ a; b; c ] then incr fired;
      if c1 <> c2 || domains_of s1 <> domains_of s2 then
        disagree := (a, b, c) :: !disagree)
    scenes;
  if !disagree <> [] then
    Printf.printf
      "     D-0044 IS WRONG: a degree-1 Learned.t and Bool_clause disagree on %d of %d \
       scenes. M2-L3's staging must be revisited -- see docs/DECISIONS.md D-0044's \
       status register, which nominates THIS test as what converts its central claim.\n"
      (List.length !disagree) (List.length scenes);
  check
    (Printf.sprintf
       "(b) D-0044: a degree-1 Learned.t propagates exactly as Bool_clause on all %d \
        scenes"
       (List.length scenes))
    (!disagree = []);
  (* A comparison in which neither side ever did anything would pass vacuously. *)
  check "(b) the scenes are non-vacuous: some conflict and some force a literal"
    (!conflicted > 0 && !fired > 0);
  (* NEGATIVE CONTROL. The comparison above says "these two agree"; on its own that is
     also what it would say if the comparison were blind. So run it again against a
     DIFFERENT clause -- the same one with its last literal dropped -- and require it to
     disagree. If this passes, the agreement above is a measurement. *)
  let wrong = Learned.of_clause [ Lit.bool_true "b0"; Lit.bool_true "b1" ] in
  let saw_disagreement = ref false in
  List.iter
    (fun (a, b, c) ->
      let mk () = store_of [ ("b0", (0, 1)); ("b1", (0, 1)); ("b2", (0, 1)) ] in
      let scene s =
        narrow s "b0" a;
        narrow s "b1" b;
        narrow s "b2" c
      in
      let s1 = mk () in
      let v n = Option.get (Store.var_named s1 n) in
      let cl = Bool_clause.make s1 [ (v "b0", true); (v "b1", true); (v "b2", false) ] in
      let i1 =
        Propagator.pack ~id:0
          (module Bool_clause : Propagator.S with type t = Bool_clause.t)
          cl
      in
      scene s1;
      let c1 = run_to_fixpoint i1 s1 in
      let s2 = mk () in
      let i2 = Option.get (Learned.instance ~id:0 ~row_id:1 s2 ~decl wrong) in
      scene s2;
      let c2 = run_to_fixpoint i2 s2 in
      if c1 <> c2 || domains_of s1 <> domains_of s2 then saw_disagreement := true)
    scenes;
  check
    "(b) CONTROL: the same comparison DOES separate a different clause, so the \
     agreement      above is not blind"
    !saw_disagreement

(* ------------------------------------------------- (c) I-T4, attribution *)

(* A propagator that runs the learned instance under SOMEBODY ELSE'S id. The only route
   to a wrong [entry.prop] is [Store.with_running], which the engine needs public --
   test_engine.ml's [Steals_credit] walks through it for the same reason. *)
module Steals_credit = struct
  type t = { inner : Linear.t; victim : int }

  let name = "steals_credit"
  let consistency = Propagator.Bounds
  let vars t = Linear.vars t.inner

  let propagate t store =
    Store.with_running store t.victim (fun () -> Linear.propagate t.inner store)
end

(* Test (c). The learned instance is registered with a live engine, its prunings are
   accepted by [Engine.check_attribution], and a deliberately mis-stamped one is not.

   WHICH mis-stamp, and why it matters (M2-L2's note, hours old): stamping one id high
   can land on an instance that DOES watch the variable, and then the second arm of the
   check -- the watcher arm -- cannot see it. So the break here is chosen deliberately
   and both halves are reported:

     - the FIRST arm ("the trail credits that change to #k") fires whenever the stamp
       differs from the running instance's own id, whatever k is. That is the arm this
       break trips, and it trips for the learned instance exactly as it does for a model
       row's.
     - the SECOND arm (the stealer does not watch the variable) is the one M2-L2 warns
       is blind to a plausible id, and it is not what catches this.

   The victim chosen is the id of the other instance in the engine, which is a real
   instance that really does watch the variable -- i.e. the hardest case, the one a
   naive "is this id registered at all?" check would wave through. *)
let test_it4_attribution () =
  let decls = [ ("x", (0, 4)); ("y", (0, 4)) ] in
  let enc = encoding_of decls in
  let decl = Learned.decl_of_encoding enc in
  let store = store_of decls in
  let x = Option.get (Store.var_named store "x") in
  let y = Option.get (Store.var_named store "y") in
  (* A model row to fill id #0, so the learned instance is genuinely added later. *)
  let row = Linear.make ~row_id:1 store [ (1, x); (1, y) ] 6 in
  let base =
    Propagator.pack ~id:0 (module Linear : Propagator.S with type t = Linear.t) row
  in
  let engine = Engine.create [ base ] in
  check "(c) the engine starts with one instance" (Engine.n_instances engine = 1);
  (* the learned row:  x + y <= 3,  as  -[x>=1..4] - [y>=1..4] >= -3 *)
  let rungs v = List.init 4 (fun i -> (-1, Lit.ge v (i + 1))) in
  let learned = Learned.make (rungs "x" @ rungs "y") (-3) in
  let id = Engine.next_id engine in
  let inst = Option.get (Learned.instance ~id ~row_id:99 store ~decl learned) in
  Engine.add engine inst;
  check "(c) the learned instance got the engine's next id and was registered"
    (Engine.n_instances engine = 2 && inst.Propagator.id = 1);
  check "(c) and it is a Linear instance -- no new propagator family"
    (inst.Propagator.inst_name = Linear.name);
  (match Engine.propagate engine store with
  | Engine.Fixpoint ->
      check "(c) check_attribution accepts every pruning the learned instance made"
        (Store.trail_length store > 0);
      check "(c) the learned row actually pruned (x + y <= 3 over 0..4)"
        (Domain.hi (Store.get store x) = 3 && Domain.hi (Store.get store y) = 3)
  | Engine.Conflict _ -> check "(c) the scene should not conflict" false);
  (* Now the break. A fresh engine whose learned instance steals #0's credit. *)
  let store2 = store_of decls in
  let x2 = Option.get (Store.var_named store2 "x") in
  let y2 = Option.get (Store.var_named store2 "y") in
  let row2 = Linear.make ~row_id:1 store2 [ (1, x2); (1, y2) ] 6 in
  let base2 =
    Propagator.pack ~id:0 (module Linear : Propagator.S with type t = Linear.t) row2
  in
  let engine2 = Engine.create [ base2 ] in
  let lin2 = Option.get (Learned.to_linear ~row_id:99 store2 ~decl learned) in
  let thief =
    Propagator.pack ~id:1
      (module Steals_credit : Propagator.S with type t = Steals_credit.t)
      { Steals_credit.inner = lin2; victim = 0 }
  in
  Engine.add engine2 thief;
  let reddened =
    try
      ignore (Engine.propagate engine2 store2);
      false
    with Engine.Mis_attributed msg ->
      check "(c) the break is caught on the FIRST arm (a stamp that is not the runner's)"
        (let has s =
           let n = String.length s in
           let rec go i =
             i + n <= String.length msg && (String.sub msg i n = s || go (i + 1))
           in
           go 0
         in
         has "the trail credits that change");
      true
  in
  check
    "(c) a mis-stamped id reddens: the learned instance stealing #0's credit raises \
     Mis_attributed"
    reddened

(* ----------------------------------------------------- (d) I-X2, exactly one del *)

(* Test (d). Under BAGUETTE_PROOF_AUDIT the learned id must be deleted exactly once.

   Three runs, and the middle one is the one that matters: a test that only ever shows
   the audit passing cannot tell a working audit from no audit at all.

     1. introduce + retire  -> [Writer.conclusion] returns, and the proof contains
                               exactly one del naming the learned id.
     2. introduce only      -> [conclusion] must RAISE [Writer.Audit_failed]. This is
                               M1-T29's preserved break (474a05f) applied to a learned
                               constraint instead of a reason.
     3. introduce + retire twice -> two dels. Checked so that "exactly once" is a count
                               and not a synonym for "at least once"; the audit itself
                               cannot see a double delete (the second [forget] is a
                               no-op on a table the first emptied), so the PROOF TEXT is
                               what has to be counted, and this records that the audit
                               is not the check for this half. *)
let test_ix2_deleted_exactly_once () =
  let decls = [ ("x", (0, 4)) ] in
  let learned = Learned.of_clause [ Lit.ge "x" 1 ] in
  let once () =
    let ctx, _, w, oc, path = ctx_in_file ~audit:true ~decls () in
    let id = Learned.introduce ctx learned ~origin:"M2-L1 test (d)" in
    Learned.retire ctx id;
    Writer.conclusion w (Writer.Unsat None);
    close_out oc;
    (id, read_file path)
  in
  let id, text = once () in
  let label = Opb.label_of id in
  check "(d) with the retire, the audit passes and the proof holds one learned id"
    (count_substring text (Printf.sprintf "del id %s" label) = 1
    || count_substring text (Printf.sprintf "del id %d" id) = 1);
  (* The break: drop the del. *)
  let broke =
    let ctx, _, w, oc, _ = ctx_in_file ~audit:true ~decls () in
    let _ = Learned.introduce ctx learned ~origin:"M2-L1 test (d), break" in
    let r =
      try
        Writer.conclusion w (Writer.Unsat None);
        false
      with Writer.Audit_failed _ -> true
    in
    close_out oc;
    r
  in
  check "(d) BREAK: dropping the retire makes the I-X2 audit FAIL at conclusion" broke;
  (* And a double delete is visible in the proof even though the audit cannot see it. *)
  let twice =
    let ctx, _, w, oc, path = ctx_in_file ~audit:true ~decls () in
    let id = Learned.introduce ctx learned ~origin:"M2-L1 test (d), twice" in
    Learned.retire ctx id;
    Learned.retire ctx id;
    Writer.conclusion w (Writer.Unsat None);
    close_out oc;
    let text = read_file path in
    count_substring text (Printf.sprintf "del id %s" (Opb.label_of id))
    + count_substring text (Printf.sprintf "del id %d" id)
  in
  check
    "(d) a double retire writes TWO dels -- the audit cannot see it, the proof text can"
    (twice = 2)

(* ------------------------------------------------------------- (e) determinism *)

(* Test (e). The learned database must not be iterated in hash order.

   [scripts/check_determinism.sh] requires two runs of one binary to be byte-identical,
   and the WORKLOG briefing flags a hash-ordered learned database as the specific way
   learning breaks that gate. This checks the property at its source rather than at the
   gate: the same learned constraint built from the same literals in a DIFFERENT ORDER
   must render to the same bytes, and emitting one must write the same proof text twice.

   The first half is the one with teeth. A [Learned.t] that kept its terms in the order
   they were handed to [make] would pass every other test in this file and fail only
   when something upstream (a [Hashtbl.fold] in a future conflict analysis, say) handed
   them over in a different order on a different run -- at which point the gate would go
   red in a file that has nothing to do with learning. *)
let test_determinism () =
  let a = Lit.ge "x" 2 and b = Lit.ge "y" 1 and c = Lit.bool_false "z" in
  let orders =
    [
      [ (1, a); (2, b); (3, c) ];
      [ (3, c); (1, a); (2, b) ];
      [ (2, b); (3, c); (1, a) ];
      [ (3, c); (2, b); (1, a) ];
    ]
  in
  let rendered = List.map (fun o -> Learned.to_string (Learned.make o 2)) orders in
  check "(e) CONTROL: the four input orders really are different lists"
    (List.length (List.sort_uniq compare (List.map (List.map snd) orders)) = 4);
  check "(e) a Learned.t renders identically however its terms were ordered"
    (List.for_all (fun s -> s = List.hd rendered) rendered);
  let opbs =
    List.map (fun o -> Opb.constr_to_string (Learned.to_opb (Learned.make o 2))) orders
  in
  check "(e) and so does its .opb/.pbp rendering"
    (List.for_all (fun s -> s = List.hd opbs) opbs);
  let decls = [ ("x", (0, 4)); ("y", (0, 4)); ("z", (0, 1)) ] in
  let emit o =
    let ctx, _, w, oc, path = ctx_in_file ~decls () in
    let id = Learned.introduce ctx (Learned.make o 2) ~origin:"M2-L1 test (e)" in
    Learned.retire ctx id;
    Writer.conclusion w (Writer.Unsat None);
    close_out oc;
    read_file path
  in
  let texts = List.map emit orders in
  check "(e) and two emissions of the same constraint are byte-identical"
    (List.for_all (fun s -> s = List.hd texts) texts)

(* --------------------------------------------------------------- (f) I-X10 *)

(* Test (f). I-X10 says every pruning must close to the .opb, and test_trace.ml's gate
   fires when a new module appears in lib/core/prop/ without a classification.

   What the roadmap row expected was that red line. It did not come, and the reason is
   the row's own architecture rather than a gap: a learned constraint is instantiated as
   a [Linear] instance, so NO module appears in lib/core/prop/ and there is no new family
   to classify. The gate is behaving correctly by staying silent.

   That is not the end of the obligation, though, and this section states the part that
   survives. [Linear] is classified [Single_row] because its [Combine] is based on
   [Model_row row_id] -- ONE row of the .opb. A learned instance's [row_id] is not an
   .opb row; it is a constraint DERIVED from several of them. So the closure to the .opb
   runs through the learned constraint's own introduction line, which must be on the page
   BEFORE anything cites it. That is exactly D-0040's "derive it explicitly ahead of the
   line that uses it", and [Learned.introduce] is where it is discharged.

   So the three checks below are: the family did not change; the constraint is
   introduced before it is cited; and the introduction is a real line in the proof rather
   than an id conjured from the counter. *)
let test_ix10_no_new_family () =
  let prop_dir = "lib/core/prop" in
  let root =
    let rec up d n =
      if n > 6 then None
      else if Sys.file_exists (Filename.concat d prop_dir) then Some d
      else up (Filename.concat d Filename.parent_dir_name) (n + 1)
    in
    up (Sys.getcwd ()) 0
  in
  (match root with
  | None -> check "(f) the repository root was found" false
  | Some r ->
      let on_disk = Array.to_list (Sys.readdir (Filename.concat r prop_dir)) in
      check "(f) lib/core/prop/ was read and is not empty" (on_disk <> []);
      check
        "(f) I-X10: learning added NO module to lib/core/prop/, so test_trace.ml's \
         closure gate correctly does not fire"
        (not (List.mem "learned.ml" on_disk));
      check "(f) and learned.ml is where it belongs, in lib/core/"
        (Sys.file_exists (Filename.concat r "lib/core/learned.ml")));
  (* The obligation that does survive: the introduction is a line, and it precedes any
     citation of the id it mints. *)
  let decls = [ ("x", (0, 4)) ] in
  let ctx, _, w, oc, path = ctx_in_file ~decls () in
  let learned = Learned.of_clause [ Lit.ge "x" 1 ] in
  let before = Writer.last_id w in
  let id = Learned.introduce ctx learned ~origin:"M2-L1 test (f)" in
  Learned.retire ctx id;
  Writer.conclusion w (Writer.Unsat None);
  close_out oc;
  let text = read_file path in
  check "(f) introduce mints a new id rather than reusing one" (id > before);
  check "(f) and writes a real rule for it, ahead of anything that could cite it"
    (count_substring text "rup" >= 1
    && count_substring text "x_ge_1" >= 1
    &&
    let needle = Printf.sprintf "del id %s" (Opb.label_of id) in
    let idx_of hay n =
      let ln = String.length n in
      let rec go i =
        if i + ln > String.length hay then -1
        else if String.sub hay i ln = n then i
        else go (i + 1)
      in
      go 0
    in
    let d = idx_of text needle in
    let r = idx_of text "rup" in
    r >= 0 && (d < 0 || r < d))

let () =
  test_normalisation ();
  test_oracle_round_trip ();
  test_d0044_clause_is_degree_one ();
  test_it4_attribution ();
  test_ix2_deleted_exactly_once ();
  test_determinism ();
  test_ix10_no_new_family ();
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "\nlearned-constraint unit tests passed"
