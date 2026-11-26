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
  let agree = ref 0
  and disagree = ref 0
  and oracle_disagree = ref 0
  and row_mismatch = ref 0 in
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
      let i2 = Option.get (Learned.pb_instance ~id:0 ~row_id:1 s2 ~decl learned) in
      (* D-0226: the row the instance exposes is read back off its flat arrays; it must be
         the row on the page, pair for pair and at the page's degree. *)
      (match i2.Propagator.inst_row s2 with
      | Some r
        when r.Propagator.r_terms = Learned.raw_terms learned
             && r.Propagator.r_degree = Learned.degree learned
             && r.Propagator.r_cid = 1 ->
          ()
      | _ -> incr row_mismatch);
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
  check "D-0226: the learned instance's row is the row on the page, read off its arrays"
    (!row_mismatch = 0);
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
      let i2 = Option.get (Learned.pb_instance ~id:0 ~row_id:1 s2 ~decl learned) in
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
      let i2 = Option.get (Learned.pb_instance ~id:0 ~row_id:1 s2 ~decl wrong) in
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
(* M2-L13: [inner] is now a packed [Propagator.instance] rather than a [Linear.t], so
   this can wrap whatever family a learned row instantiates as. It wrapped a [Linear.t]
   only because [Learned.to_linear] handed one over, and that function is gone. Nothing
   about what the break does changed: it runs the real propagator under SOMEBODY ELSE'S
   id through [Store.with_running], which is the only route to a wrong [entry.prop]. *)
module Steals_credit = struct
  type t = { inner : Propagator.instance; victim : int }

  let name = "steals_credit"
  let consistency = Propagator.Bounds
  let vars t = t.inner.Propagator.inst_vars

  let propagate t store =
    Store.with_running store t.victim (fun () -> t.inner.Propagator.run store)
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
  let inst = Option.get (Learned.pb_instance ~id ~row_id:99 store ~decl learned) in
  Engine.add engine inst;
  check "(c) the learned instance got the engine's next id and was registered"
    (Engine.n_instances engine = 2 && inst.Propagator.id = 1);
  (* M2-L13 / D-0054 REPLACED THIS ASSERTION AND THE CLAIM UNDER IT. Until M2-L13 a
     learned row was instantiated as a [Linear] -- D-0044's "no new propagator family"
     bet -- through [Learned.to_linear_row], which decided the question by an ALGEBRAIC
     IDENTITY OVER THE DECLARED BOX. That was a proof-side test doing a solving-side job
     (D-0050, D-0054) and it is gone. The runtime object is now a PB slack propagator
     over the order literals the row already names, and the family it belongs to is
     lib/core/prop/pb.ml, of which lib/core/prop/clause.ml is the degree-1 face. The bet
     was collected the other way; test (f) below says what survives of it. *)
  check "(c) and it is a learned_pb instance -- D-0054's solving-side object"
    (inst.Propagator.inst_name = "learned_pb");
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
  let lin2 = Option.get (Learned.pb_instance ~id:1 ~row_id:99 store2 ~decl learned) in
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

   What the M2-L1 roadmap row expected was that red line. It did not come then, because a
   learned constraint was instantiated as a [Linear] instance and no module appeared in
   lib/core/prop/ at all.

   **M2-L13 MADE IT COME, and that is the gate working rather than a regression.**
   D-0054 replaced the [Linear] instantiation with lib/core/prop/pb.ml, a slack
   propagator over order literals, so there IS a new family now and test_trace.ml's I-X10
   table had to classify it -- Single_row, with the standing of the order-encoding ladder
   rows spelled out there. The check below is unchanged and still passes, because what it
   asserts is narrower and still true: [learned.ml] itself is not a propagator and does
   not live in prop/.

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
      check "(f) I-X10: learned.ml is not a propagator family, so it adds no module here"
        (not (List.mem "learned.ml" on_disk));
      check
        "(f) ...while M2-L13's propagator IS one, and test_trace.ml's gate classifies it"
        (List.mem "pb.ml" on_disk);
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

(* M11-complexity-T4 (D-0152, D-0140 L2): [to_linear_row] with typed sorts and a
   one-pass grouping, against the code it replaced, copied here as the reference
   (polymorphic sorts, [List.partition] per variable). Random rows over four integer
   variables, both polarities, rungs inside and outside the declared box, repeated
   variables, and one undeclared name; the answer must be equal, [None] included. *)
let test_l2_to_linear_row_reference () =
  let reference t ~decl =
    let ladder_form t =
      let rec go acc const = function
        | [] -> Some (List.sort compare acc, const)
        | tm :: rest -> (
            let coeff = tm.Learned.coeff and lit = tm.Learned.lit in
            match lit.Lit.v with
            | Lit.Eq _ | Lit.Bit _ -> None
            | Lit.Ge (x, v) ->
                if lit.Lit.positive then go ((x, v, coeff) :: acc) const rest
                else go ((x, v, -coeff) :: acc) (const + coeff) rest)
      in
      go [] 0 (Learned.terms t)
    in
    match ladder_form t with
    | None -> None
    | Some (rungs, const0) ->
        let rec group = function
          | [] -> []
          | (x, v, c) :: rest ->
              let mine, others =
                List.partition (fun (y, _, _) -> String.equal x y) rest
              in
              (x, (v, c) :: List.map (fun (_, v, c) -> (v, c)) mine) :: group others
        in
        let rec fold acc const = function
          | [] -> Some (List.rev acc, const)
          | (x, rungs) :: rest -> (
              match decl x with
              | None -> None
              | Some (lo, hi) -> (
                  let rungs =
                    List.filter (fun (_, c) -> c <> 0) (List.sort compare rungs)
                  in
                  match Learned.linear_of_rungs ~lo ~hi rungs with
                  | None -> None
                  | Some (0, k) -> fold acc (const + k) rest
                  | Some (a, k) -> fold ((-a, x) :: acc) (const + k) rest))
        in
        Option.map
          (fun (terms, const) -> (terms, const - Learned.degree t))
          (fold [] const0 (group rungs))
  in
  let decl = function
    | "p" -> Some (0, 1)
    | "q" -> Some (0, 3)
    | "r" -> Some (1, 4)
    | "s" -> Some (-2, 2)
    | _ -> None
  in
  let rng = Random.State.make [| 0x0152; 2 |] in
  let names = [| "p"; "q"; "r"; "s"; "zz" |] in
  let agree = ref true and some = ref 0 in
  for _ = 1 to 5000 do
    let n = 1 + Random.State.int rng 8 in
    let terms =
      List.init n (fun _ ->
          let x =
            names.(Random.State.int rng (if Random.State.int rng 10 = 0 then 5 else 4))
          in
          let l = Lit.ge x (Random.State.int rng 8 - 3) in
          ( 1 + Random.State.int rng 2,
            if Random.State.int rng 3 = 0 then Lit.negate l else l ))
    in
    let t = Learned.make terms (1 + Random.State.int rng 3) in
    let a = Learned.to_linear_row t ~decl and b = reference t ~decl in
    if a <> b then agree := false;
    if a <> None then incr some
  done;
  check
    (Printf.sprintf
       "D-0152 L2: to_linear_row equals the polymorphic, quadratic reference on 5 000 \
        random rows (%d with a linear form)"
       !some)
    (!agree && !some > 100)

(* M11-complexity-T9 (D-0157): [make], [combine], [add_multiples] and [to_string] against
   the code they replaced, kept in learned.ml as [make_reference] / [combine_reference]
   (the fold of it, for [add_multiples]) and copied here for [to_string]. Every result
   must be EQUAL: the same terms in the same order and the same degree, or the same
   [Checked.Overflow] with the same message. Coefficients near 2^60 are drawn often
   enough that both arms are reached, the overflow arm and the one-merge arm, and the
   lanes say how often each was. *)
module Checked = Baguette_core.Checked

let rng_t9 = Random.State.make [| 0x0157; 9 |]
let names_t9 = [| "a"; "b"; "c"; "d"; "X_INTRODUCED_7_"; "q.r" |]

let lit_t9 () =
  let x = names_t9.(Random.State.int rng_t9 (Array.length names_t9)) in
  let v = Random.State.int rng_t9 6 - 1 in
  let l =
    match Random.State.int rng_t9 10 with
    | 0 -> Lit.eq x v
    | 1 -> Lit.bit x (abs v)
    | _ -> Lit.ge x v
  in
  if Random.State.bool rng_t9 then Lit.negate l else l

let big_t9 () = (1 lsl 60) + Random.State.int rng_t9 1_000_000

let coeff_t9 ~big =
  if big && Random.State.int rng_t9 6 = 0 then big_t9 ()
  else 1 + Random.State.int rng_t9 5

(* A row through [make], so in [make]'s order. *)
let row_t9 ~big =
  let n = Random.State.int rng_t9 9 in
  Learned.make
    (List.init n (fun _ -> (coeff_t9 ~big, lit_t9 ())))
    (Random.State.int rng_t9 7 - 2)

let outcome_t9 f = try Ok (f ()) with Checked.Overflow m -> Error m

let same_t9 r1 r2 =
  match (r1, r2) with
  | Ok a, Ok b -> Learned.equal a b
  | Error m1, Error m2 -> String.equal m1 m2
  | _ -> false

let test_t9_make () =
  (* A raw list in one of four shapes: anything (repeats, zeros, negative coefficients),
     a model row's expansion (one sorted block per variable, variables in random order,
     a variable sometimes twice), a [make] output's own terms, and blocks that overlap. *)
  let raw () =
    match Random.State.int rng_t9 4 with
    | 0 ->
        List.init (Random.State.int rng_t9 12) (fun _ ->
            (Random.State.int rng_t9 9 - 4, lit_t9 ()))
    | 1 ->
        List.concat
          (List.init
             (1 + Random.State.int rng_t9 5)
             (fun _ ->
               let x = names_t9.(Random.State.int rng_t9 (Array.length names_t9)) in
               let a = Random.State.int rng_t9 7 - 3 in
               let lo = Random.State.int rng_t9 3 - 1 in
               List.init (Random.State.int rng_t9 5) (fun i -> (a, Lit.ge x (lo + 1 + i)))))
    | 2 -> Learned.raw_terms (row_t9 ~big:false)
    | _ ->
        List.concat
          (List.init
             (2 + Random.State.int rng_t9 3)
             (fun _ ->
               List.init (Random.State.int rng_t9 4) (fun i -> (1 + i, Lit.ge "b" i))))
  in
  let agree = ref true in
  for _ = 1 to 20_000 do
    let r = raw () and d = Random.State.int rng_t9 9 - 4 in
    if not (Learned.equal (Learned.make r d) (Learned.make_reference r d)) then
      agree := false
  done;
  check "D-0157: make equals make_reference on 20 000 raw lists of four shapes" !agree;
  (* The sort on its own, payload included: stability is part of the claim. *)
  let agree = ref true in
  for _ = 1 to 20_000 do
    let l =
      match Random.State.int rng_t9 2 with
      | 0 -> List.init (Random.State.int rng_t9 14) (fun i -> (lit_t9 (), i))
      | _ ->
          List.concat
            (List.init
               (1 + Random.State.int rng_t9 4)
               (fun k ->
                 let x = names_t9.(Random.State.int rng_t9 3) in
                 List.init (Random.State.int rng_t9 5) (fun i ->
                     (Lit.ge x (i + Random.State.int rng_t9 2), (10 * k) + i))))
    in
    let want = List.stable_sort (fun (l1, _) (l2, _) -> Lit.compare l1 l2) l in
    let got = Learned.sort_by_lit l in
    if
      not
        (List.equal
           (fun (l1, i1) (l2, i2) -> Lit.equal l1 l2 && Int.equal i1 i2)
           got want)
    then agree := false
  done;
  check "D-0157: sort_by_lit is List.stable_sort, payload order included, on 20 000 lists"
    !agree

let test_t9_combine () =
  let mult () =
    match Random.State.int rng_t9 8 with
    | 0 -> 0
    | 1 -> big_t9 ()
    | 2 -> 1 lsl 31
    | 3 -> -1
    | _ -> 1 + Random.State.int rng_t9 6
  in
  let agree = ref true and n_ok = ref 0 and n_over = ref 0 and n_merged = ref 0 in
  for _ = 1 to 30_000 do
    let a = row_t9 ~big:true and b = row_t9 ~big:true in
    let ca = mult () and cb = mult () in
    let got = outcome_t9 (fun () -> Learned.combine a ca b cb) in
    let want = outcome_t9 (fun () -> Learned.combine_reference a ca b cb) in
    if not (same_t9 got want) then agree := false;
    if Learned.add_mass (Learned.scaled_mass ca a) (Learned.scaled_mass cb b) >= 0 then
      incr n_merged;
    match want with Ok _ -> incr n_ok | Error _ -> incr n_over
  done;
  check
    (Printf.sprintf
       "D-0157: combine equals combine_reference on 30 000 pairs (%d rows, %d by the one \
        merge; %d overflows, message for message)"
       !n_ok !n_merged !n_over)
    (!agree && !n_merged > 5000 && !n_ok - !n_merged > 1000 && !n_over > 1000);
  (* The pivot cancels: the shape every elimination has. *)
  let p = Lit.ge "a" 2 in
  let r1 = Learned.make [ (3, p); (2, Lit.ge "b" 1) ] 3
  and r2 = Learned.make [ (1, Lit.negate p); (1, Lit.ge "c" 1) ] 1 in
  let c = Learned.combine r1 1 r2 3 in
  check "D-0157: the pivot cancels and the degree loses min(p, n)"
    (Learned.equal c (Learned.make [ (2, Lit.ge "b" 1); (3, Lit.ge "c" 1) ] 3))

exception Stop_t9

let test_t9_add_multiples () =
  (* The fold [Ladder.lift] ran, with its stop: [before] is counted, and raises at the
     [stop_at]-th call when [stop_at] is drawn. *)
  let fold ~before row summands =
    List.fold_left
      (fun acc (m, r) ->
        before ();
        Learned.combine_reference acc 1 r m)
      row summands
  in
  let run f ~stop_at =
    let calls = ref 0 in
    let before () =
      incr calls;
      if !calls = stop_at then raise Stop_t9
    in
    let r =
      try Ok (f ~before) with
      | Checked.Overflow m -> Error ("overflow " ^ m)
      | Stop_t9 -> Error "stopped"
    in
    (r, !calls)
  in
  let ladder name w =
    Learned.make [ (1, Lit.ge name w); (1, Lit.negate (Lit.ge name (w + 1))) ] 1
  in
  let agree = ref true and n_ok = ref 0 and n_over = ref 0 and n_stop = ref 0 in
  let n_merged = ref 0 in
  for _ = 1 to 30_000 do
    let big = Random.State.int rng_t9 3 = 0 in
    let row = row_t9 ~big in
    let summands =
      List.init (Random.State.int rng_t9 7) (fun _ ->
          let m =
            if big && Random.State.int rng_t9 4 = 0 then big_t9 ()
            else Random.State.int rng_t9 6
          in
          let r =
            if Random.State.bool rng_t9 then ladder "a" (Random.State.int rng_t9 5)
            else row_t9 ~big
          in
          (m, r))
    in
    let stop_at =
      if Random.State.int rng_t9 5 = 0 then 1 + Random.State.int rng_t9 4 else 0
    in
    let got, gcalls =
      run (fun ~before -> Learned.add_multiples ~before row summands) ~stop_at
    in
    let want, wcalls = run (fun ~before -> fold ~before row summands) ~stop_at in
    if
      summands <> []
      && List.fold_left
           (fun acc (m, r) -> Learned.add_mass acc (Learned.scaled_mass m r))
           (Learned.mass row) summands
         >= 0
    then incr n_merged;
    let eq =
      match (got, want) with
      | Ok a, Ok b -> Learned.equal a b
      | Error x, Error y -> String.equal x y
      | _ -> false
    in
    if not (eq && gcalls = wcalls) then agree := false;
    match want with
    | Ok _ -> incr n_ok
    | Error "stopped" -> incr n_stop
    | Error _ -> incr n_over
  done;
  check
    (Printf.sprintf
       "D-0157: add_multiples equals the fold of combine_reference, stop calls counted, \
        on 30 000 rows (%d rows, %d overflows, %d stops; %d by the one merge)"
       !n_ok !n_over !n_stop !n_merged)
    (!agree && !n_ok > 1000 && !n_over > 100 && !n_stop > 100 && !n_merged > 5000)

let test_t9_to_string () =
  let reference t =
    Printf.sprintf "%s >= %d"
      (String.concat " "
         (List.map
            (fun (tm : Learned.term) ->
              Printf.sprintf "+%d %s" tm.Learned.coeff (Lit.to_string tm.Learned.lit))
            (Learned.terms t)))
      (Learned.degree t)
  in
  let agree = ref true in
  for _ = 1 to 5_000 do
    let t = row_t9 ~big:true in
    if not (String.equal (Learned.to_string t) (reference t)) then agree := false
  done;
  let t = Learned.make [ (2, Lit.ge "x" (-3)) ] min_int in
  check "D-0157: to_string is the Printf rendering, byte for byte, on 5 000 rows"
    (!agree && String.equal (Learned.to_string t) (reference t))

(* -------------------------------------------- D-0197: long rows under a small stack

   2021_ATSP_instance10_0p25 died mid-search with "Fatal error: exception Stack overflow":
   PB conflict analysis built a row of 32 168 204 terms (a conflict row lifted onto the
   ladder of a variable 22 million values wide), and [Learned.make]'s merge recursed once
   per term, past the 1 GiB OCaml stack. Reproducing that takes four minutes and 26 GB.

   What this does instead: the walks run inside a FRESH FIBER whose stack may grow to
   64 Ki words (512 KiB) only -- [Gc.stack_limit] bounds every fiber stack, and a fiber
   started after it is lowered starts small, where the main stack may already have grown.
   200 000 terms is then about ten times what one frame per term can hold, and nothing
   that walks a row in constant stack notices the limit. Measured before the fix: the
   [make] and [Pol] checks below raise [Stack_overflow] here. Every walk the fix touched
   is driven: [make] on an unsorted row of two overlapping runs (the stable merge of
   [sort_by_lit], then the summing of equal literals), [make_reference], [combine] and
   [combine_reference], a [Pol.sum] of 200 000 operands written and counted, and
   [Store.drop_page_only_lemmas] over 200 000 summands. *)
let in_small_stack f =
  let saved = Gc.get () in
  Gc.set { saved with Gc.stack_limit = 64 * 1024 };
  Fun.protect
    ~finally:(fun () -> Gc.set { (Gc.get ()) with Gc.stack_limit = saved.Gc.stack_limit })
    (fun () ->
      Effect.Deep.match_with f ()
        {
          Effect.Deep.retc = (fun x -> Ok x);
          exnc = (function Stack_overflow -> Error "Stack_overflow" | e -> raise e);
          effc = (fun _ -> None);
        })

let test_d0197_long_rows_small_stack () =
  let n = 200_000 in
  let probe =
    in_small_stack (fun () ->
        let rec deep k = if k = 0 then 0 else 1 + deep (k - 1) in
        deep n)
  in
  check "D-0197: the small stack is small (one frame per term overflows it)"
    (probe = Error "Stack_overflow");
  let run = List.init n (fun i -> (1, Lit.ge "x" (i + 1))) in
  let raw = run @ run in
  let expect_doubled t =
    Learned.degree t = 3
    && List.length (Learned.terms t) = n
    && List.for_all (fun (tm : Learned.term) -> tm.Learned.coeff = 2) (Learned.terms t)
  in
  check "D-0197: make on 2 x 200 000 overlapping terms, in a 512 KiB stack"
    (match in_small_stack (fun () -> Learned.make raw 3) with
    | Ok t -> expect_doubled t
    | Error _ -> false);
  check "D-0197: make_reference on the same row, in a 512 KiB stack"
    (match in_small_stack (fun () -> Learned.make_reference raw 3) with
    | Ok t -> expect_doubled t
    | Error _ -> false);
  let a = Learned.make run 1 in
  let b = Learned.make (List.map (fun (c, l) -> (c, Lit.negate l)) run) 1 in
  check
    "D-0197: combine and combine_reference of two 200 000-term rows, in a 512 KiB stack"
    (match
       in_small_stack (fun () ->
           (Learned.combine a 1 b 2, Learned.combine_reference a 1 b 2))
     with
    | Ok (c, r) -> Learned.equal c r && List.length (Learned.terms c) = n
    | Error _ -> false);
  let p = Writer.Pol.sum (List.init n (fun i -> Writer.Pol.id (i + 1))) in
  check "D-0197: a 200 000-operand pol is written and counted in a 512 KiB stack"
    (match
       in_small_stack (fun () ->
           (Writer.Pol.to_string_cited ~cite:string_of_int p, Writer.Pol.tokens p))
     with
    | Ok (str, toks) ->
        toks = (2 * n) - 1
        && String.length str > 6
        && String.sub str 0 6 = "1 2 + "
        && String.ends_with ~suffix:(Printf.sprintf " %d +" n) str
    | Error _ -> false);
  let summands =
    List.init n (fun i -> Explanation.Term (1, Explanation.Model_row (i + 1)))
  in
  check "D-0197: drop_page_only_lemmas over 200 000 summands, in a 512 KiB stack"
    (match in_small_stack (fun () -> Store.drop_page_only_lemmas summands) with
    | Ok l -> List.length l = n
    | Error _ -> false)

let () =
  test_t9_make ();
  test_d0197_long_rows_small_stack ();
  test_t9_combine ();
  test_t9_add_multiples ();
  test_t9_to_string ();
  test_l2_to_linear_row_reference ();
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
