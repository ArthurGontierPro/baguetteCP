(* M1-T16, part 2: the randomised differential tester.

   ---------------------------------------------------------------------------
   What this is, and the trap it is built to avoid
   ---------------------------------------------------------------------------

   Generate a small model, solve it, and check three things against something other
   than the solver:

     1. the answer agrees with brute-force enumeration of the whole declared box
        (SAT with a specific solution, or UNSAT),
     2. a solution really satisfies every constraint, re-checked from the model text
        rather than trusted from the propagators (I-S1),
     3. **veripb accepts the emitted proof** -- which is the part that matters, and the
        part that turns a fuzzer into a proof-logging test.

   The trap, from the Glasgow Constraint Solver, is that a naive random sweep is close
   to no evidence: they generated 987 random instances that reached a conflict, ablated
   a load-bearing constraint, and only 37 of them noticed -- about 96% coincidence. A
   count of passing cases is therefore not a coverage claim, and this file does not make
   one. It counts, per interesting state, how many generated instances actually REACHED
   that state, and prints the fractions. A state nothing reaches is printed as 0%, said
   out loud, and not quietly absorbed into the total.

   So the generator is biased rather than uniform, toward the shapes that have actually
   broken things in this project:

     - domains that are NOT 0..n (offset, straddling zero, or entirely negative) -- the
       D-0010 / D-0021 shape, three times out of four,
     - coefficients that do not divide evenly, and coefficients sharing a common factor,
       so the Combine division is non-trivial and rounds,
     - a parity trap on half the cases: every coefficient +-2 and the right-hand side
       odd, which no bound can refute, so the search MUST guess wrong at least once and
       the D-0018 trace is actually written. Without that bias almost every random
       instance is decided at the root and the whole branch-level mechanism goes
       untested -- which is exactly how D-0017 survived.

   Each of those biases is stated as an ASSERTED rate below, not as a sentence here. A
   comment claiming a search shape is worth nothing: test/models/guess_wrong_sat.fzn
   shipped with a header saying its search had to guess wrong, and the search fixed
   every variable at the root instead.

   ---------------------------------------------------------------------------
   Determinism
   ---------------------------------------------------------------------------

   Fixed seed by default, printed on every run; BAGUETTE_RANDOM_SEED overrides it. The
   budget knob is BAGUETTE_RANDOM_CASES, a case COUNT rather than a wall-clock limit,
   and that is deliberate: a time budget would make the set of cases actually run depend
   on how loaded the machine is, so a failure seen in CI might not reproduce here, which
   is precisely the property this file needs. The default is sized to a few seconds of
   `make check`; a soak is `BAGUETTE_RANDOM_CASES=2000`, which on this machine takes a
   few minutes and is dominated by veripb rather than by the solver.

   A failure prints the model as a paste-ready OCaml literal for test_matrix.ml's
   instance list, so a random finding becomes a named, permanent case in one step
   rather than living only in a seed.

   ---------------------------------------------------------------------------
   The one known failure this file does not print a hundred times
   ---------------------------------------------------------------------------

   [int_ne] prunes through [Store.remove], which records no bound facts, so a
   disequality pruning that moves a bound emits a D-0018 trace line with an empty
   reason -- an unconditional claim that is false. test_matrix.ml's
   [known_bug_ne_trace_facts] pins that with a named minimal instance and the full
   diagnosis, and it is one of THREE disequality findings this task turned up. Each has
   a signature that can be recognised from the run rather than from the error text:

     - clause-in-a-pol   (D-0019's last consequence, already known): int_lin_le's
                          Snap_cite path folded a disequality's clause into a `pol`,
     - factless trace    (new): a disequality moved a bound, then a branch failed,
     - root conflict     (new): a disequality conflicted with no decision on the stack.

   A veripb rejection matching one of those is counted in its own bucket, printed once
   with its count, and asserted to be ZERO in a single check -- the same shape
   test_mutation.ml's [known_slack] uses, so a bucket cannot rot into a list of quietly
   ignored failures and each turns green by itself when its bug is fixed. Every
   rejection that does NOT match a signature is a hard, per-case failure with a full
   repro, because that would be something new. *)

module Encoding = Baguette_proof.Encoding
module Writer = Baguette_proof.Writer
module Var = Baguette_core.Var
module Domain = Baguette_core.Domain
module Store = Baguette_core.Store
module Propagator = Baguette_core.Propagator
module Explanation = Baguette_core.Explanation
module Linear = Baguette_core.Linear
module Lin_eq = Baguette_core.Lin_eq
module Int_le = Baguette_core.Int_le
module Int_lt = Baguette_core.Int_lt
module Int_eq = Baguette_core.Int_eq
module Ne = Baguette_core.Ne
module Engine = Baguette_core.Engine
module Search = Baguette_core.Search
module Justify = Baguette_core.Justify
module Trace = Baguette_core.Trace

let failures = ref 0
let checks = ref 0

let check name cond =
  incr checks;
  if cond then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s\n" name)

let fail fmt =
  incr checks;
  incr failures;
  Printf.ksprintf (fun s -> Printf.printf "FAIL %s\n" s) fmt

(* ================================================================== models *)

type cstr =
  | Lin_le of (int * int) list * int
  | Lin_eq of (int * int) list * int
  | Lin_ne of (int * int) list * int
  | Le of int * int
  | Lt of int * int
  | Eq of int * int
  | Ne of int * int

type model = { vars : (string * int * int) array; cstrs : cstr list }

let value_of terms assign =
  List.fold_left (fun acc (a, i) -> acc + (a * assign.(i))) 0 terms

let satisfies m assign =
  List.for_all
    (function
      | Lin_le (t, r) -> value_of t assign <= r
      | Lin_eq (t, r) -> value_of t assign = r
      | Lin_ne (t, r) -> value_of t assign <> r
      | Le (i, j) -> assign.(i) <= assign.(j)
      | Lt (i, j) -> assign.(i) < assign.(j)
      | Eq (i, j) -> assign.(i) = assign.(j)
      | Ne (i, j) -> assign.(i) <> assign.(j))
    m.cstrs

let brute_force m =
  let n = Array.length m.vars in
  let assign = Array.make n 0 in
  let found = ref None in
  let rec go i =
    if !found <> None then ()
    else if i = n then (if satisfies m assign then found := Some (Array.copy assign))
    else
      let _, lo, hi = m.vars.(i) in
      for v = lo to hi do
        if !found = None then (
          assign.(i) <- v;
          go (i + 1))
      done
  in
  go 0;
  !found

let independent_check m (assignment : Search.assignment) =
  let n = Array.length m.vars in
  let assign = Array.make n 0 in
  List.iter (fun (v, value) -> assign.(Var.to_int v) <- value) assignment;
  let in_box = ref true in
  Array.iteri
    (fun i (_, lo, hi) -> if assign.(i) < lo || assign.(i) > hi then in_box := false)
    m.vars;
  !in_box && satisfies m assign

(* A failure has to be reproducible without the seed, so the model prints as something
   that can be pasted straight into test_matrix.ml's [instances]. *)
let show_terms t =
  "[ "
  ^ String.concat "; " (List.map (fun (a, i) -> Printf.sprintf "(%d, %d)" a i) t)
  ^ " ]"

let show_model m =
  let vars =
    String.concat "; "
      (Array.to_list
         (Array.map (fun (n, lo, hi) -> Printf.sprintf "(%S, %d, %d)" n lo hi) m.vars))
  in
  let cstrs =
    String.concat ";\n             "
      (List.map
         (function
           | Lin_le (t, r) -> Printf.sprintf "Lin_le (%s, %d)" (show_terms t) r
           | Lin_eq (t, r) -> Printf.sprintf "Lin_eq (%s, %d)" (show_terms t) r
           | Lin_ne (t, r) -> Printf.sprintf "Lin_ne (%s, %d)" (show_terms t) r
           | Le (i, j) -> Printf.sprintf "Le (%d, %d)" i j
           | Lt (i, j) -> Printf.sprintf "Lt (%d, %d)" i j
           | Eq (i, j) -> Printf.sprintf "Eq (%d, %d)" i j
           | Ne (i, j) -> Printf.sprintf "Ne (%d, %d)" i j)
         m.cstrs)
  in
  Printf.sprintf
    "        {\n\
    \          vars = [| %s |];\n\
    \          cstrs =\n\
    \            [ %s ];\n\
    \        }" vars cstrs

(* ============================================================== the probe *)

(* The same observations test_matrix.ml makes, kept to the ones this file reports as
   coverage. [deep] is off here: this file runs hundreds of instances and forcing every
   pruning explanation is the expensive half. *)
type obs = {
  mutable branch_failed : bool;
  mutable cross_conflict : bool;
  mutable div_nontrivial : bool;
  mutable div_remainder : bool;
  mutable root_conflict : bool;
  mutable deep_decisions : bool;
  mutable ne_moved_bound : bool;
  mutable ne_root_conflict : bool;
  mutable clause_in_pol : bool;
}

let new_obs () =
  {
    branch_failed = false;
    cross_conflict = false;
    div_nontrivial = false;
    div_remainder = false;
    root_conflict = false;
    deep_decisions = false;
    ne_moved_bound = false;
    ne_root_conflict = false;
    clause_in_pol = false;
  }

let floordiv a b =
  let q = a / b and r = a mod b in
  if r <> 0 && r < 0 <> (b < 0) then q - 1 else q

let ceildiv a b = -(floordiv (-a) b)

let term_min store (tm : Linear.term) =
  let d = Store.get store tm.Linear.x in
  if tm.Linear.coeff >= 0 then tm.Linear.coeff * Domain.lo d
  else tm.Linear.coeff * Domain.hi d

(* [Linear]'s own rounding, replicated rather than called, so that "this push divided by
   more than one" and "this division had a remainder" are observations the test makes
   rather than reports the code under test hands it. *)
let scan_linear obs (lin : Linear.t) store =
  let terms = lin.Linear.terms in
  let mins = List.map (fun tm -> term_min store tm) terms in
  let slack = lin.Linear.rhs - List.fold_left ( + ) 0 mins in
  if slack >= 0 then
    List.iter
      (fun ((tm : Linear.term), m) ->
        let coeff = tm.Linear.coeff in
        if coeff <> 0 then
          let max_term = m + slack in
          let d = Store.get store tm.Linear.x in
          let pushes =
            if coeff > 0 then floordiv max_term coeff < Domain.hi d
            else ceildiv max_term coeff > Domain.lo d
          in
          if pushes then (
            if abs coeff > 1 then obs.div_nontrivial <- true;
            if max_term mod coeff <> 0 then obs.div_remainder <- true))
      (List.combine terms mins)

(* Does this derivation fold a [Clause] into a `pol` as though it were a chain-sum?
   That is the D-0019 composition gap between [int_ne] and [int_lin_le]'s Snap_cite
   path: a clause is a real constraint but not a unit-coefficient bound statement, and
   adding it into a cutting-planes sum does not produce the contradiction the caller
   believes it does. *)
let clause_folded_into_pol e =
  let found = ref false in
  let rec go ~in_pol e =
    match Explanation.force e with
    | Explanation.Clause _ -> if in_pol then found := true
    | Explanation.Cut (a, b, _, _) ->
        go ~in_pol:true a;
        go ~in_pol:true b
    | Explanation.Combine (summands, _) ->
        List.iter
          (function
            | Explanation.Term (_, e) -> go ~in_pol:true e | Explanation.Weaken _ -> ())
          summands
    | _ -> ()
  in
  go ~in_pol:false e;
  !found

let classify obs store e =
  if Store.level store = 0 then obs.root_conflict <- true;
  if clause_folded_into_pol e then obs.clause_in_pol <- true;
  match Explanation.force e with
  | Explanation.Combine ([ Explanation.Term (1, _); Explanation.Term (1, _) ], 1) ->
      obs.cross_conflict <- true
  | _ -> ()

module Probe_linear = struct
  type t = { lin : Linear.t; obs : obs }

  let name = "int_lin_le"
  let consistency = Propagator.Bounds
  let vars t = Linear.vars t.lin

  let propagate t store =
    scan_linear t.obs t.lin store;
    match Linear.propagate t.lin store with
    | Propagator.Conflict e ->
        classify t.obs store e;
        Propagator.Conflict e
    | Propagator.Fixpoint -> Propagator.Fixpoint
end

module Probe_ne = struct
  type t = { ne : Ne.t; obs : obs }

  let name = "int_lin_ne"
  let consistency = Propagator.Value
  let vars t = Ne.vars t.ne

  (* Whether a disequality pruning moved a BOUND, which is the trigger for the
     factless-trace-line bug this file buckets rather than prints per case. *)
  let propagate t store =
    let before =
      List.map
        (fun v ->
          let d = Store.get store v in
          (Domain.lo d, Domain.hi d))
        (Ne.vars t.ne)
    in
    let r = Ne.propagate t.ne store in
    let after =
      List.map
        (fun v ->
          let d = Store.get store v in
          (Domain.lo d, Domain.hi d))
        (Ne.vars t.ne)
    in
    if List.exists2 (fun a b -> a <> b) before after then t.obs.ne_moved_bound <- true;
    match r with
    | Propagator.Conflict e ->
        classify t.obs store e;
        if Store.level store = 0 then t.obs.ne_root_conflict <- true;
        Propagator.Conflict e
    | Propagator.Fixpoint -> Propagator.Fixpoint
end

let pack_linear ~id obs lin =
  Propagator.pack ~id
    (module Probe_linear : Propagator.S with type t = Probe_linear.t)
    { Probe_linear.lin; obs }

let pack_ne ~id obs ne =
  Propagator.pack ~id
    (module Probe_ne : Propagator.S with type t = Probe_ne.t)
    { Probe_ne.ne; obs }

(* ============================================================ wiring a model *)

let build_store m =
  Store.create
    ~names:(Array.map (fun (n, _, _) -> n) m.vars)
    ~domains:(Array.map (fun (_, lo, hi) -> Domain.make lo hi) m.vars)

let negate_terms t = List.map (fun (a, x) -> (-a, x)) t

let build m store obs =
  let e = Encoding.create () in
  Array.iter (fun (n, lo, hi) -> Encoding.declare_int e n ~lo ~hi) m.vars;
  let nm i =
    let n, _, _ = m.vars.(i) in
    n
  in
  let named t = List.map (fun (a, i) -> (a, nm i)) t in
  let vars_of t = List.map (fun (a, i) -> (a, Var.of_int i)) t in
  let next = ref 0 in
  let id () =
    let i = !next in
    incr next;
    i
  in
  let instances =
    List.concat_map
      (fun c ->
        match c with
        | Lin_le (t, r) ->
            let row = Encoding.add_int_lin_le e (named t) r in
            [ pack_linear ~id:(id ()) obs (Linear.make ~row_id:row store (vars_of t) r) ]
        | Le (i, j) ->
            let row = Encoding.add_int_lin_le e (named [ (1, i); (-1, j) ]) 0 in
            [
              pack_linear ~id:(id ()) obs
                (Int_le.make ~row_id:row store (Var.of_int i) (Var.of_int j));
            ]
        | Lt (i, j) ->
            let row = Encoding.add_int_lin_le e (named [ (1, i); (-1, j) ]) (-1) in
            [
              pack_linear ~id:(id ()) obs
                (Int_lt.make ~row_id:row store (Var.of_int i) (Var.of_int j));
            ]
        | Lin_eq (t, r) ->
            let le_id = Encoding.add_int_lin_le e (named t) r in
            let ge_id = Encoding.add_int_lin_le e (named (negate_terms t)) (-r) in
            let le, ge = Lin_eq.make ~le_id ~ge_id store (vars_of t) r in
            [ pack_linear ~id:(id ()) obs le; pack_linear ~id:(id ()) obs ge ]
        | Eq (i, j) ->
            let t = [ (1, i); (-1, j) ] in
            let le_id = Encoding.add_int_lin_le e (named t) 0 in
            let ge_id = Encoding.add_int_lin_le e (named (negate_terms t)) 0 in
            let le, ge = Int_eq.make ~le_id ~ge_id store (Var.of_int i) (Var.of_int j) in
            [ pack_linear ~id:(id ()) obs le; pack_linear ~id:(id ()) obs ge ]
        | Lin_ne (t, r) ->
            let _ = Encoding.add_int_lin_ne e (named t) r in
            [ pack_ne ~id:(id ()) obs (Ne.make store (vars_of t) r) ]
        | Ne (i, j) ->
            let _ = Encoding.add_int_lin_ne e (named [ (1, i); (-1, j) ]) 0 in
            [
              pack_ne ~id:(id ()) obs (Ne.Int_ne.make store (Var.of_int i) (Var.of_int j));
            ])
      m.cstrs
  in
  (e, Engine.create instances)

(* ================================================================== veripb *)

(* Which checker to run: lib/proof/checker.ml, shared with scripts/checker.sh.
   Every test module open-coded this search, and every copy looked at
   ~/.local/bin/veripb first -- so a project-wide choice of checker lived in nine
   places and silently meant the Python 2.2.2 (M1-T18). [None] is a FAILURE at every
   call site below, never a skip. *)
let veripb = Baguette_proof.Checker.find ()

let contains needle s =
  let n = String.length needle and m = String.length s in
  let rec go i = i + n <= m && (String.sub s i n = needle || go (i + 1)) in
  n = 0 || go 0

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

let run_veripb ~dir ~opb ~pbp =
  match veripb with
  | None -> None
  | Some exe ->
      let log = Filename.concat dir "check.log" in
      let rc =
        Sys.command
          (Printf.sprintf "%s %s %s > %s 2>&1" (Filename.quote exe) (Filename.quote opb)
             (Filename.quote pbp) (Filename.quote log))
      in
      Some (rc = 0, try read_file log with _ -> "")

(* ============================================================== generator *)

(* Biased on purpose; see the header. [r] is the only source of randomness in the file,
   so one seed reproduces a whole run exactly. *)

(* Three cases in four have a domain that is not 0..n: offset upward, straddling zero,
   or entirely negative. The D-0010 and D-0021 findings both lived here. *)
let gen_domain r =
  let width = 1 + Random.State.int r 4 in
  let lo =
    match Random.State.int r 4 with
    | 0 -> 0
    | 1 -> 1 + Random.State.int r 3
    | 2 -> -1 - Random.State.int r 3
    | _ -> -5 + Random.State.int r 3
  in
  (lo, lo + width)

(* Coefficients avoid 1 more often than a uniform draw would, and 0 appears rarely --
   it is a real case (an inert term) but an uninteresting one to spend the budget on. *)
let gen_coeff r =
  match Random.State.int r 10 with
  | 0 -> 0
  | 1 | 2 -> 1
  | 3 -> -1
  | 4 | 5 -> 2
  | 6 -> -2
  | 7 -> 3
  | 8 -> -3
  | _ -> -4

let gen_terms r n =
  let k = 2 + Random.State.int r (max 1 (n - 1)) in
  let idx = List.init n Fun.id in
  let rec take k l acc =
    match (k, l) with
    | 0, _ | _, [] -> List.rev acc
    | k, x :: rest -> take (k - 1) rest (x :: acc)
  in
  let chosen = take (min k n) (List.sort (fun _ _ -> Random.State.int r 3 - 1) idx) [] in
  List.map (fun i -> (gen_coeff r, i)) chosen

let span m terms =
  List.fold_left
    (fun (lo, hi) (a, i) ->
      let _, vlo, vhi = m.vars.(i) in
      if a >= 0 then (lo + (a * vlo), hi + (a * vhi)) else (lo + (a * vhi), hi + (a * vlo)))
    (0, 0) terms

(* An rhs inside the row's own span, so the row is not trivially true or trivially
   false: a row that cannot possibly do anything spends budget without testing
   anything. *)
let gen_rhs r m terms =
  let lo, hi = span m terms in
  if hi <= lo then lo else lo + Random.State.int r (hi - lo + 1)

(* The parity trap: every coefficient +-2 and the right-hand side odd, with the rhs
   inside the row's own span. No bound can refute it, so the search HAS to branch and a
   nogood is actually written. Without this bias almost every random instance is settled
   at the root and D-0018's whole mechanism goes untested, which is exactly how D-0017
   survived a green suite -- so the rate this achieves is reported, not assumed.

   The coefficients are +-2 rather than any even number because [Linear]'s rounding is
   itself a refutation engine: with coefficients 4 and -6 the repeated floor/ceil closes
   a parity-infeasible row at the ROOT, which is sound and useful and defeats the point
   of the trap. Measured, not guessed. *)
let gen_parity_row r m n =
  let idx = List.init n Fun.id in
  let terms = List.map (fun i -> ((if Random.State.bool r then 2 else -2), i)) idx in
  let lo, hi = span m terms in
  if hi - lo < 4 then None
  else
    let v = lo + 1 + Random.State.int r (hi - lo - 1) in
    let v = if v mod 2 = 0 then v + 1 else v in
    if v > hi || v mod 2 = 0 then None else Some (Lin_eq (terms, v))

(* A domain wide enough that the parity trap has room to branch. *)
let gen_wide_domain r =
  let width = 3 + Random.State.int r 3 in
  let lo =
    match Random.State.int r 4 with
    | 0 -> 0
    | 1 -> 1 + Random.State.int r 3
    | 2 -> -1 - Random.State.int r 3
    | _ -> -5 + Random.State.int r 3
  in
  (lo, lo + width)

let gen_free_model r =
  let n = 2 + Random.State.int r 3 in
  let vars =
    Array.init n (fun i ->
        let lo, hi = gen_domain r in
        (Printf.sprintf "v%d" i, lo, hi))
  in
  let m0 = { vars; cstrs = [] } in
  let extra = 1 + Random.State.int r 3 in
  let rest =
    List.init extra (fun _ ->
        let i = Random.State.int r n and j = Random.State.int r n in
        let j = if j = i then (j + 1) mod n else j in
        match Random.State.int r 10 with
        | 0 -> Le (i, j)
        | 1 -> Lt (i, j)
        | 2 -> Eq (i, j)
        | 3 -> Ne (i, j)
        | 4 | 5 ->
            let t = gen_terms r n in
            Lin_eq (t, gen_rhs r m0 t)
        | 6 ->
            let t = gen_terms r n in
            Lin_ne (t, gen_rhs r m0 t)
        | _ ->
            let t = gen_terms r n in
            Lin_le (t, gen_rhs r m0 t))
  in
  { m0 with cstrs = rest }

(* The parity model keeps its extra constraints WEAK on purpose: a second random linear
   row usually refutes the model at the root on its own, and the trap is then wasted. A
   comparison or a disequality between two variables cannot do that, but it does change
   which branch the search tries first and how deep it has to go. *)
let gen_parity_model r =
  (* Three or four variables, never two: with two, [Linear]'s rounding closes a
     parity-infeasible row at the root about half the time and the trap is wasted. *)
  let n = 3 + Random.State.int r 2 in
  let vars =
    Array.init n (fun i ->
        let lo, hi = gen_wide_domain r in
        (Printf.sprintf "v%d" i, lo, hi))
  in
  let m0 = { vars; cstrs = [] } in
  match gen_parity_row r m0 n with
  | None -> None
  | Some row ->
      let extras =
        if Random.State.int r 2 = 0 then []
        else
          let i = Random.State.int r n in
          let j = (i + 1) mod n in
          [
            (match Random.State.int r 3 with
            | 0 -> Le (i, j)
            | 1 -> Lt (i, j)
            | _ -> Ne (i, j));
          ]
      in
      Some { m0 with cstrs = row :: extras }

let gen_model r =
  if Random.State.int r 2 = 0 then
    match gen_parity_model r with Some m -> m | None -> gen_free_model r
  else gen_free_model r

(* ============================================================== one case *)

(* [Known_ne_trace] and [Known_ne_root] are the two rejections test_matrix.ml already
   pins with named minimal instances. They are bucketed here rather than printed per
   case, and each bucket carries its own single assertion below, so each turns green on
   its own when its bug is fixed. Anything else is [Broken] and gets a full repro. *)
type verdict =
  | Verified
  | Known_ne_trace
  | Known_ne_root
  | Known_ne_in_pol
  | Broken of string

let tmpdir () =
  let d = Filename.temp_file "baguette_random" "" in
  Sys.remove d;
  Sys.mkdir d 0o700;
  d

let run_case ~dir ~n m =
  let opb = Filename.concat dir "m.opb" and pbp = Filename.concat dir "m.pbp" in
  let expected = brute_force m in
  let store = build_store m in
  let obs = new_obs () in
  let encoding, engine = build m store obs in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ Printf.sprintf "random case %d" n ] encoding oc;
  close_out oc;
  let oc = open_out pbp in
  let writer = Writer.create ~audit:true oc in
  Encoding.start_proof encoding writer;
  let ctx =
    Justify.create ~writer ~encoding ~model_id:(fun () ->
        failwith "test_random: search demanded Explanation.Trivial (D-0011)")
  in
  let trace = Trace.create () in
  let entry_level = Store.level store in
  let result =
    match Search.solve ~engine ~store ~ctx ~check:(independent_check m) ~trace () with
    | o ->
        close_out oc;
        Ok o
    | exception e ->
        close_out oc;
        Error (Printexc.to_string e)
  in
  ignore Verified;
  obs.branch_failed <- Trace.emitted_ids trace <> [];
  let proof = try read_file pbp with _ -> "" in
  obs.deep_decisions <-
    List.exists
      (fun l -> String.length l >= 3 && String.sub l 0 3 = "# 2")
      (String.split_on_char '\n' proof);
  let verdict =
    match result with
    | Error e -> Broken (Printf.sprintf "the solver raised %s" e)
    | Ok o -> (
        if Store.level store <> entry_level then
          Broken "I-S3: the decision level on return does not match the level on entry"
        else
          let answer_ok =
            match o with
            | Search.Sat a -> expected <> None && independent_check m a
            | Search.Unsat -> expected = None
          in
          if not answer_ok then
            Broken
              (match o with
              | Search.Sat _ ->
                  "the solver answered SAT with an assignment brute force rejects, or on \
                   a model brute force says is UNSAT"
              | Search.Unsat ->
                  "the solver answered UNSAT but brute force found a solution")
          else
            match run_veripb ~dir ~opb ~pbp with
            | None -> Broken "veripb is not available, so nothing was checked"
            | Some (true, _) -> Verified
            | Some (false, log) ->
                (* Attribute by what the checker actually complained about, not only
                   by what the run did: several instances reach more than one of the
                   three disequality gaps, and a bucket that guessed from the run alone
                   would credit the wrong one. *)
                if
                  contains "by reverse unit propagation" log
                  && obs.ne_moved_bound && obs.branch_failed
                then Known_ne_trace
                else if contains "not a contradiction" log && obs.clause_in_pol then
                  Known_ne_in_pol
                else if contains "not a contradiction" log && obs.ne_root_conflict then
                  Known_ne_root
                else
                  Broken
                    (Printf.sprintf "veripb rejected the proof:\n%s\n     the proof:\n%s"
                       (String.concat "\n"
                          (List.map
                             (fun l -> "       " ^ l)
                             (String.split_on_char '\n' (String.trim log))))
                       (String.concat "\n"
                          (List.map
                             (fun l -> "       " ^ l)
                             (String.split_on_char '\n' proof)))))
  in
  List.iter (fun f -> try Sys.remove f with _ -> ()) [ opb; pbp ];
  (verdict, obs)

(* ================================================================== main *)

let getenv_int name default =
  match Sys.getenv_opt name with
  | None -> default
  | Some s -> ( try int_of_string (String.trim s) with _ -> default)

let default_seed = 20260915

let () =
  print_endline "\nthe randomised differential tester (M1-T16)";
  let seed = getenv_int "BAGUETTE_RANDOM_SEED" default_seed in
  let cases = getenv_int "BAGUETTE_RANDOM_CASES" 50 in
  Printf.printf "  seed %d (BAGUETTE_RANDOM_SEED), %d cases (BAGUETTE_RANDOM_CASES)\n"
    seed cases;
  (match veripb with
  | None ->
      print_endline
        "  (veripb is not on PATH and not at ~/.local/bin/veripb -- every case below \
         will FAIL, which is the intended behaviour: see docs/INVARIANTS.md.)"
  | Some _ -> ());
  let r = Random.State.make [| seed |] in
  let dir = tmpdir () in
  let ran = ref 0
  and sat = ref 0
  and unsat = ref 0
  and known_ne_trace = ref 0
  and known_ne_root = ref 0
  and known_ne_in_pol = ref 0
  and branch_failed = ref 0
  and deep = ref 0
  and root_conflict = ref 0
  and cross = ref 0
  and div = ref 0
  and rem = ref 0
  and ne_bound = ref 0
  and offset_dom = ref 0 in
  let broken = ref [] in
  (try
     while !ran < cases do
       let m = gen_model r in
       (* Keep the box small enough that brute force is exact and cheap; an instance
          whose oracle is expensive is an instance whose budget bought nothing. *)
       let box = Array.fold_left (fun acc (_, lo, hi) -> acc * (hi - lo + 1)) 1 m.vars in
       if box <= 2000 then (
         incr ran;
         let verdict, obs = run_case ~dir ~n:!ran m in
         if obs.branch_failed then incr branch_failed;
         if obs.deep_decisions then incr deep;
         if obs.root_conflict then incr root_conflict;
         if obs.cross_conflict then incr cross;
         if obs.div_nontrivial then incr div;
         if obs.div_remainder then incr rem;
         if obs.ne_moved_bound then incr ne_bound;
         if Array.exists (fun (_, lo, _) -> lo <> 0) m.vars then incr offset_dom;
         (match brute_force m with Some _ -> incr sat | None -> incr unsat);
         match verdict with
         | Verified -> ()
         | Known_ne_trace -> incr known_ne_trace
         | Known_ne_root -> incr known_ne_root
         | Known_ne_in_pol -> incr known_ne_in_pol
         | Broken why -> broken := (!ran, m, why) :: !broken)
     done
   with e ->
     fail "the generator itself raised %s -- the run is incomplete" (Printexc.to_string e));
  (try Sys.rmdir dir with _ -> ());
  let pct k = if !ran = 0 then 0.0 else 100.0 *. float_of_int k /. float_of_int !ran in
  Printf.printf "\n  %d cases -- %d SAT, %d UNSAT\n" !ran !sat !unsat;
  print_endline "\n  what the generated instances actually reached:";
  List.iter
    (fun (k, what) -> Printf.printf "    %5.1f%%  (%d/%d)  %s\n" (pct k) k !ran what)
    [
      (!branch_failed, "a branch failed, so a D-0018 trace was written");
      (!deep, "the search went at least two decisions deep");
      (!root_conflict, "a conflict with no decision on the stack");
      (!div, "a push whose Combine divisor is greater than one");
      (!rem, "a push whose division has a remainder");
      (!ne_bound, "a disequality pruning that moved a bound");
      (!offset_dom, "at least one domain that does not start at zero");
      (!cross, "a cross-row conflict (Linear's Store-returned-Conflict path)");
    ];
  (* A number nobody reads is a number that lies. Each of these is asserted, so that a
     generator change that stops reaching a state turns the suite red instead of
     silently reporting a smaller percentage next to a passing count. *)
  (* Not "> 0": a rate this low would mean the branch-level mechanism is tested by
     accident. The bias exists to make this number large, so the number is what is
     asserted. Measured at 41% over a 1000-case soak and 56% at the default size; the
     floor is set well under both so that ordinary drift does not turn the gate red for
     no reason, while a bias that stops working does. *)
  check
    "at least a quarter of the generated instances fail a branch (without which D-0018 \
     is untested, and a rate near zero is how D-0017 survived a green suite)"
    (pct !branch_failed >= 25.0);
  (* Same discipline for the other claim this file's header makes about its generator. *)
  check
    "at least half the generated instances have a domain that does not start at zero \
     (the D-0010 / D-0021 shape)"
    (pct !offset_dom >= 50.0);
  check "the generator reaches a search at least two decisions deep" (!deep > 0);
  check "the generator reaches a root conflict" (!root_conflict > 0);
  check "the generator reaches a division by more than one" (!div > 0);
  check "the generator reaches a division with a remainder" (!rem > 0);
  check "the generator reaches a disequality pruning that moves a bound" (!ne_bound > 0);
  (* Reported rather than asserted, and said out loud rather than left as a 0% that
     reads like bad luck: test_matrix.ml's [cross_row_cell] shows this state cannot be
     reached from two instances at all, because a push can only land outside a
     variable's interval when the row's own slack is already negative, and that is
     tested first. The generator is not at fault and a bigger budget will not change
     it. *)
  Printf.printf
    "\n\
    \  note: the cross-row-conflict state is at %.1f%%, and that is not a budget problem.\n\
    \        test_matrix.ml's [cross_row_cell] measures and argues why two instances can\n\
    \        never reach it: a push lands outside a variable's interval only when the \
     row's\n\
    \        own slack is already negative, which is detected first. Do not read the 0%%\n\
    \        as coverage, and do not spend a soak run trying to raise it.\n"
    (pct !cross);
  (* The known failure, in one bucket with one assertion -- test_mutation.ml's
     [known_slack] shape. It goes green by itself when the bug is fixed. *)
  if !known_ne_trace > 0 then
    Printf.printf
      "\n\
      \  %d case(s) rejected with the int_ne FACTLESS-TRACE-LINE signature (a disequality\n\
      \  moved a bound, then a branch failed). Pinned minimally by test_matrix.ml's\n\
      \  [known_bug_ne_trace_facts]; counted here rather than printed one by one.\n"
      !known_ne_trace;
  check
    "no case is rejected through the known int_ne factless-trace-line bug (this goes \
     green by itself once a disequality pruning carries its bound facts)"
    (!known_ne_trace = 0);
  if !known_ne_root > 0 then
    Printf.printf
      "\n\
      \  %d case(s) rejected with the int_ne ROOT-CONFLICT signature (a disequality \
       conflicted\n\
      \  with no decision on the stack, and its clause was cited as the contradiction). \
       Pinned\n\
      \  minimally by test_matrix.ml's [known_bug_ne_root_conflict].\n"
      !known_ne_root;
  check
    "no case is rejected through the known int_ne root-conflict bug (this goes green by \
     itself once search.ml's root arm writes the trace a clausal reason needs)"
    (!known_ne_root = 0);
  if !known_ne_in_pol > 0 then
    Printf.printf
      "\n\
      \  %d case(s) rejected with the int_ne CLAUSE-IN-A-POL signature (int_lin_le's \
       Snap_cite\n\
      \  path folded a disequality's clause into a cutting-planes sum). That is D-0019's \
       last\n\
      \  consequence, pinned minimally by test_matrix.ml's [known_bug_ne_snap_cite].\n"
      !known_ne_in_pol;
  check
    "no case is rejected through the known int_ne clause-in-a-pol bug (D-0019; this goes \
     green by itself once Snap_cite stops citing a clausal reason)"
    (!known_ne_in_pol = 0);
  List.iter
    (fun (n, m, why) ->
      fail "random case %d (seed %d): %s" n seed why;
      Printf.printf "     paste this into test_matrix.ml's [instances]:\n%s\n"
        (show_model m))
    (List.rev !broken);
  check "every generated case agrees with brute force and its proof is accepted"
    (!broken = []);
  Printf.printf "\n%d random checks" !checks;
  if !failures > 0 then (
    Printf.printf ", %d failure(s)\n" !failures;
    exit 1)
  else print_endline ", all passed"
