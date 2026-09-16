(* M1-T16, part 1: the case matrix.

   ---------------------------------------------------------------------------
   Why this file exists
   ---------------------------------------------------------------------------

   Five findings in this project (D-0009, D-0010, D-0012, D-0017, D-0021) have the
   same shape: the instance chosen to test a feature could not see that feature break.
   The failing case needed one more step of something than the test instance had -- one
   more restatement, one further bound, one wider domain, one wrong turn, one offset
   domain. Every one of them shipped behind a green suite.

   The answer this file implements is not "more green tests". It is an enumeration:
   the situations the solver can actually be in are named as *cells*, every cell is
   given an instance, and -- the part that makes the enumeration worth anything -- the
   harness MEASURES which cells each instance actually reached and fails if an instance
   claims a cell it does not reach. A cell nobody reaches is reported as a hole, not
   quietly absorbed into a passing count.

   Three axes are crossed (see [propagator], [situation], [shape] below):

     - which propagator is doing the work,
     - what situation it is in (root pruning, pruning under nested decisions, a root
       conflict from a row's own slack, a cross-row conflict, both branches of a
       decision failing, a solution found only after a branch failed, ...),
     - and the shape of the data, which is where all five findings actually lived:
       negative coefficients, |a| > 1 so the Combine division is non-trivial,
       coefficients sharing a common factor, domains offset away from 0, domains that
       are entirely negative, a variable at its declared bound (the Weaken path) versus
       at a derived bound (the Snap_cite path) in the same row, and a bound derived by
       a different propagator instance than the one citing it.

   ---------------------------------------------------------------------------
   What is asserted per instance, and which of those checks can tell right from wrong
   ---------------------------------------------------------------------------

   1. The answer agrees with brute force, and a solution is re-checked against the
      model independently of the propagators (I-S1, I-P1).

   2. veripb accepts the emitted proof (I-X1). Necessary, and the weakest of the four:
      D-0009, D-0010 and D-0020 are all cases where the checker accepted something that
      did not assert what we believed.

   3. Every trace line verifies STANDALONE against the .opb as a one-rule proof
      (`f N`, the line, `conclusion NONE`), while a nogood must NOT. This is
      test_trace.ml's strong check, applied to every cell rather than to five models.
      A trace line is a decision-free consequence of one model row; if one ever
      verifies *with* a decision folded into it, that is a bug check 2 cannot see.

   4. Blanking every trace line into a same-shaped tautology (which keeps every later
      constraint id exactly in place) must make veripb reject. Without this, "the proof
      verifies" does not distinguish "because of the trace" from "despite it".
      D-0021 is explicit that blanking *half* a trace proves nothing on chain_sat:
      either half rebuilds enough of the fixpoint on its own. So this blanks all of it.

   ---------------------------------------------------------------------------
   The probe, and why it forces conflict explanations early
   ---------------------------------------------------------------------------

   Several cells are about things that leave no trace in the emitted text: whether a
   conflict came from a row's own slack or from a bound another instance held, whether
   a push divided by more than one, whether a division had a remainder, whether one row
   mixed a declared bound (Weaken) with a derived one (Snap_cite). [Probe_linear] and
   [Probe_ne] wrap the real propagators, run them unchanged, and look at what came back.

   Forcing a conflict's [Explanation.t] in the probe is not a perturbation: search
   forces it immediately anyway ([Justify.emit] is the next thing that happens), the
   thunks close over snapshots by I-X6, and [Explanation.force] memoises, so the value
   the proof is later built from is the same value. The deep scan of *pruning*
   explanations does force earlier than the solver would, so it is behind [~deep], off
   for the randomised tester in test_random.ml and on here. *)

module Encoding = Baguette_proof.Encoding
module Writer = Baguette_proof.Writer
module Lit = Baguette_proof.Lit
module Var = Baguette_core.Var
module Domain = Baguette_core.Domain
module Store = Baguette_core.Store
module Checked = Baguette_core.Checked
module Flatzinc = Baguette_flatzinc
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

(* ===================================================================== axes *)

type propagator = P_lin_le | P_lin_eq | P_le | P_lt | P_eq | P_ne | P_lin_ne

let all_propagators = [ P_lin_le; P_lin_eq; P_le; P_lt; P_eq; P_ne; P_lin_ne ]

let propagator_name = function
  | P_lin_le -> "int_lin_le"
  | P_lin_eq -> "int_lin_eq"
  | P_le -> "int_le"
  | P_lt -> "int_lt"
  | P_eq -> "int_eq"
  | P_ne -> "int_ne"
  | P_lin_ne -> "int_lin_ne"

type situation =
  | S_root_prune
  | S_prune_one_decision
  | S_prune_nested
  | S_root_slack_conflict
  | S_conflict_under_decisions
  | S_cross_row_conflict
  | S_both_branches_fail
  | S_sat_after_failure

let all_situations =
  [
    S_root_prune;
    S_prune_one_decision;
    S_prune_nested;
    S_root_slack_conflict;
    S_conflict_under_decisions;
    S_cross_row_conflict;
    S_both_branches_fail;
    S_sat_after_failure;
  ]

let situation_name = function
  | S_root_prune -> "pruning at root"
  | S_prune_one_decision -> "pruning under one decision"
  | S_prune_nested -> "pruning under nested decisions"
  | S_root_slack_conflict -> "conflict at root from a row's own slack"
  | S_conflict_under_decisions -> "conflict under decisions"
  | S_cross_row_conflict -> "cross-row conflict"
  | S_both_branches_fail -> "both branches fail, the nogoods resolve"
  | S_sat_after_failure -> "a solution found only after a branch failed"

type shape =
  | D_neg_coeff
  | D_big_coeff
  | D_common_factor
  | D_offset_domain
  | D_negative_domain
  | D_weaken_and_cite
  | D_cross_instance_cite
  | D_division_remainder

let all_shapes =
  [
    D_neg_coeff;
    D_big_coeff;
    D_common_factor;
    D_offset_domain;
    D_negative_domain;
    D_weaken_and_cite;
    D_cross_instance_cite;
    D_division_remainder;
  ]

let shape_name = function
  | D_neg_coeff -> "negative coefficients"
  | D_big_coeff -> "|a| > 1, so the Combine division is non-trivial"
  | D_common_factor -> "coefficients sharing a common factor"
  | D_offset_domain -> "domains offset away from 0"
  | D_negative_domain -> "domains entirely negative"
  | D_weaken_and_cite ->
      "a declared bound (Weaken) and a derived one (Snap_cite), same row"
  | D_cross_instance_cite -> "a bound derived by a different instance than the citer"
  | D_division_remainder -> "a push whose division has a remainder"

(* The fourth axis, added by M1-T23. It is about the SIZE of the numbers rather than
   their shape, which is why it is its own axis and not another [shape]: D_big_coeff
   asks whether a coefficient is past |1|, this asks whether a coefficient times a
   bound is past what a 63-bit int can hold. The two are independent -- every instance
   in this file before M1-T23 has small coefficients AND small numbers, and the
   demonstrating model has a single coefficient and no shape at all.

   [O_far] and [O_near_limit] are read off the model like the other static shapes
   ([static_overflow] below); the other three are not properties a runnable instance
   can have, and live in [overflow_cells]. *)
type overflow = O_far | O_near_limit | O_product | O_sum | O_compile_rejected

let all_overflows = [ O_far; O_near_limit; O_product; O_sum; O_compile_rejected ]

let overflow_name = function
  | O_far -> "every row's magnitude is far below the cap"
  | O_near_limit -> "a row within a factor of 4 of Checked.limit"
  | O_product -> "one coefficient * bound leaves the 63-bit range"
  | O_sum -> "every product fits, the weighted sum does not"
  | O_compile_rejected -> "Compile refuses the model, naming the limit"

(* ================================================================== models *)

type cstr =
  | Lin_le of (int * int) list * int
  | Lin_eq of (int * int) list * int
  | Lin_ne of (int * int) list * int
  | Le of int * int (* x_i <= x_j *)
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

(* The independent oracle. Enumerates the whole declared box; these instances are
   deliberately tiny so that this is cheap and exact rather than a sampling. *)
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

(* Shapes that are properties of the model text itself, so they are read off it
   rather than measured at run time. *)
let rec gcd a b = if b = 0 then abs a else gcd b (a mod b)

let static_shapes m =
  let coeffs =
    List.concat_map
      (function
        | Lin_le (t, _) | Lin_eq (t, _) | Lin_ne (t, _) -> List.map fst t
        | Le _ | Lt _ | Eq _ | Ne _ -> [ 1; -1 ])
      m.cstrs
  in
  let rows =
    List.filter_map
      (function
        | Lin_le (t, _) | Lin_eq (t, _) | Lin_ne (t, _) -> Some (List.map fst t)
        | _ -> None)
      m.cstrs
  in
  let has p l = List.exists p l in
  let s = ref [] in
  let add c = if not (List.mem c !s) then s := c :: !s in
  if has (fun a -> a < 0) coeffs then add D_neg_coeff;
  if has (fun a -> abs a > 1) coeffs then add D_big_coeff;
  if has (fun r -> List.length r > 1 && List.fold_left gcd 0 r > 1) rows then
    add D_common_factor;
  Array.iter
    (fun (_, lo, hi) ->
      if lo > 0 || hi < 0 then add D_offset_domain;
      if hi < 0 then add D_negative_domain)
    m.vars;
  !s

(* The magnitude lib/flatzinc/compile.ml caps, computed here from the model text the
   same way [Compile.check_row] computes it from [Model.t] -- deliberately recomputed
   rather than called, so that "this instance is near the cap" is an observation this
   file makes and not a report the code under test makes. [max_int] stands in for a
   magnitude that does not itself fit, which no instance in [instances] can have (it
   would not compile) but which the classification must not silently call small. *)
let row_terms_of = function
  | Lin_le (t, r) -> (t, r)
  | Lin_eq (t, r) -> (t, r)
  | Lin_ne (t, r) -> (t, r)
  | Le (i, j) -> ([ (1, i); (-1, j) ], 0)
  | Lt (i, j) -> ([ (1, i); (-1, j) ], -1)
  | Eq (i, j) -> ([ (1, i); (-1, j) ], 0)
  | Ne (i, j) -> ([ (1, i); (-1, j) ], 0)

let max_row_magnitude m =
  List.fold_left
    (fun acc c ->
      let t, r = row_terms_of c in
      let bounded =
        List.map
          (fun (a, i) ->
            let _, lo, hi = m.vars.(i) in
            (a, lo, hi))
          t
      in
      match Checked.row_magnitude bounded r with Some v -> max acc v | None -> max_int)
    0 m.cstrs

let static_overflow m =
  if max_row_magnitude m > Checked.limit / 4 then [ O_near_limit ] else [ O_far ]

(* =============================================================== the probe *)

type obs = {
  mutable conflict_levels : int list; (* decision level at each conflict *)
  mutable root_slack : bool;
  mutable slack_conflict : bool;
  mutable cross_conflict : bool;
  mutable ne_conflict : bool;
  mutable div_nontrivial : bool;
  mutable div_remainder : bool;
  mutable weaken_and_cite : bool;
  mutable cross_instance_cite : bool;
  (* A Clause folded into a `pol` as though it were a chain-sum. This is the D-0019
     gap between int_ne and int_lin_le's Snap_cite path; see [known_bug_ne_snap_cite]
     at the bottom of the file. *)
  mutable clause_in_pol : bool;
  mutable forcing_raised : string option;
}

let new_obs () =
  {
    conflict_levels = [];
    root_slack = false;
    slack_conflict = false;
    cross_conflict = false;
    ne_conflict = false;
    div_nontrivial = false;
    div_remainder = false;
    weaken_and_cite = false;
    cross_instance_cite = false;
    clause_in_pol = false;
    forcing_raised = None;
  }

(* Every [Model_row] id an explanation cites, and whether a [Clause] ever appears as a
   summand of a [Combine] -- i.e. is folded into a `pol` rather than emitted as a
   standalone `rup`. Forces as it walks; see the header. *)
let walk_explanation e =
  let rows = ref [] and clause_in_pol = ref false in
  let rec go ~in_pol e =
    match Explanation.force e with
    | Explanation.Trivial -> ()
    | Explanation.Model_row id -> if not (List.mem id !rows) then rows := id :: !rows
    | Explanation.Clause _ -> if in_pol then clause_in_pol := true
    | Explanation.Linear _ -> ()
    | Explanation.Cut (a, b, _, _) ->
        go ~in_pol:true a;
        go ~in_pol:true b
    | Explanation.Combine (summands, _) ->
        List.iter
          (function
            | Explanation.Term (_, e) -> go ~in_pol:true e | Explanation.Weaken _ -> ())
          summands
    | Explanation.Deferred _ -> ()
  in
  go ~in_pol:false e;
  (!rows, !clause_in_pol)

(* [Linear]'s own rounding, replicated here rather than called, so that "this push
   divided by more than one" and "this division had a remainder" are observations made
   by the test rather than reports made by the code under test. *)
let floordiv a b =
  let q = a / b and r = a mod b in
  if r <> 0 && r < 0 <> (b < 0) then q - 1 else q

let ceildiv a b = -(floordiv (-a) b)

let term_min store (tm : Linear.term) =
  let d = Store.get store tm.Linear.x in
  if tm.Linear.coeff >= 0 then tm.Linear.coeff * Domain.lo d
  else tm.Linear.coeff * Domain.hi d

(* What this row is about to do, looked at before [Linear.propagate] does it. *)
let scan_linear obs (lin : Linear.t) store =
  let terms = lin.Linear.terms in
  let mins = List.map (fun tm -> term_min store tm) terms in
  let slack = lin.Linear.rhs - List.fold_left ( + ) 0 mins in
  if slack >= 0 then
    List.iteri
      (fun idx (tm, m) ->
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
            if max_term mod coeff <> 0 then obs.div_remainder <- true;
            let others = Linear.others_except terms idx in
            let snaps = List.filter_map (Linear.snapshot_source store) others in
            let weakens =
              List.exists (function Linear.Snap_weaken _ -> true | _ -> false) snaps
            in
            let cites =
              List.exists (function Linear.Snap_cite _ -> true | _ -> false) snaps
            in
            if weakens && cites then obs.weaken_and_cite <- true;
            List.iter
              (function
                | Linear.Snap_cite { expl; _ } ->
                    let rows, clause = walk_explanation expl in
                    if clause then obs.clause_in_pol <- true;
                    let mine =
                      match lin.Linear.row_id with Some i -> [ i ] | None -> []
                    in
                    if List.exists (fun r -> not (List.mem r mine)) rows then
                      obs.cross_instance_cite <- true
                | Linear.Snap_weaken _ -> ())
              snaps))
      (List.combine terms mins)

(* Which kind of conflict this is, from the shape D-0013 gives each one:
     - a row's own slack:  Combine (Term (1, Model_row _) :: _, 1)
     - a cross-row clash:  Combine ([Term (1, _); Term (1, _)], 1) with neither a row
   The classification is structural rather than a flag set by the code under test. *)
let classify_conflict obs store e =
  obs.conflict_levels <- Store.level store :: obs.conflict_levels;
  let rows, clause_in_pol = walk_explanation e in
  if clause_in_pol then obs.clause_in_pol <- true;
  if List.length rows > 1 then obs.cross_instance_cite <- true;
  match Explanation.force e with
  | Explanation.Clause _ -> obs.ne_conflict <- true
  | Explanation.Combine (Explanation.Term (1, Explanation.Model_row _) :: _, 1) ->
      obs.slack_conflict <- true;
      if Store.level store = 0 then obs.root_slack <- true
  | Explanation.Combine ([ Explanation.Term (1, _); Explanation.Term (1, _) ], 1) ->
      obs.cross_conflict <- true
  | _ -> ()

module Probe_linear = struct
  type t = { lin : Linear.t; obs : obs; deep : bool }

  let name = "int_lin_le"
  let consistency = Propagator.Bounds
  let vars t = Linear.vars t.lin

  let propagate t store =
    (if t.deep then
       try scan_linear t.obs t.lin store
       with e -> t.obs.forcing_raised <- Some (Printexc.to_string e));
    match Linear.propagate t.lin store with
    | Propagator.Conflict e ->
        (try classify_conflict t.obs store e
         with exn -> t.obs.forcing_raised <- Some (Printexc.to_string exn));
        Propagator.Conflict e
    | Propagator.Fixpoint -> Propagator.Fixpoint
end

module Probe_ne = struct
  type t = { ne : Ne.t; obs : obs }

  let name = "int_lin_ne"
  let consistency = Propagator.Value
  let vars t = Ne.vars t.ne

  let propagate t store =
    match Ne.propagate t.ne store with
    | Propagator.Conflict e ->
        (try classify_conflict t.obs store e
         with exn -> t.obs.forcing_raised <- Some (Printexc.to_string exn));
        Propagator.Conflict e
    | Propagator.Fixpoint -> Propagator.Fixpoint
end

let pack_linear ~id obs ~deep lin =
  Propagator.pack ~id
    (module Probe_linear : Propagator.S with type t = Probe_linear.t)
    { Probe_linear.lin; obs; deep }

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

(* Rows into the .opb and instances into the engine, in lockstep: every instance is
   handed the id of the row it will justify against (D-0011), and an equality is two
   rows and two instances (D-0011 again, and the `=`-counts-as-two trap of
   PROOF-FORMAT section 2 is avoided because both halves go through add_int_lin_le). *)
let build m store obs ~deep =
  let e = Encoding.create () in
  Array.iter (fun (n, lo, hi) -> Encoding.declare_int e n ~lo ~hi) m.vars;
  let nm i =
    let n, _, _ = m.vars.(i) in
    n
  in
  let named t = List.map (fun (a, i) -> (a, nm i)) t in
  let vars_of t = List.map (fun (a, i) -> (a, Var.of_int i)) t in
  let next = ref 0 in
  let instances =
    List.concat_map
      (fun c ->
        let id () =
          let i = !next in
          incr next;
          i
        in
        match c with
        | Lin_le (t, r) ->
            let row = Encoding.add_int_lin_le e (named t) r in
            [
              pack_linear ~id:(id ()) obs ~deep
                (Linear.make ~row_id:row store (vars_of t) r);
            ]
        | Le (i, j) ->
            let t = [ (1, i); (-1, j) ] in
            let row = Encoding.add_int_lin_le e (named t) 0 in
            [
              pack_linear ~id:(id ()) obs ~deep
                (Int_le.make ~row_id:row store (Var.of_int i) (Var.of_int j));
            ]
        | Lt (i, j) ->
            let t = [ (1, i); (-1, j) ] in
            let row = Encoding.add_int_lin_le e (named t) (-1) in
            [
              pack_linear ~id:(id ()) obs ~deep
                (Int_lt.make ~row_id:row store (Var.of_int i) (Var.of_int j));
            ]
        | Lin_eq (t, r) ->
            let le_id = Encoding.add_int_lin_le e (named t) r in
            let ge_id = Encoding.add_int_lin_le e (named (negate_terms t)) (-r) in
            let le, ge = Lin_eq.make ~le_id ~ge_id store (vars_of t) r in
            [ pack_linear ~id:(id ()) obs ~deep le; pack_linear ~id:(id ()) obs ~deep ge ]
        | Eq (i, j) ->
            let t = [ (1, i); (-1, j) ] in
            let le_id = Encoding.add_int_lin_le e (named t) 0 in
            let ge_id = Encoding.add_int_lin_le e (named (negate_terms t)) 0 in
            let le, ge = Int_eq.make ~le_id ~ge_id store (Var.of_int i) (Var.of_int j) in
            [ pack_linear ~id:(id ()) obs ~deep le; pack_linear ~id:(id ()) obs ~deep ge ]
        | Lin_ne (t, r) ->
            let _ = Encoding.add_int_lin_ne e (named t) r in
            [ pack_ne ~id:(id ()) obs (Ne.make store (vars_of t) r) ]
        | Ne (i, j) ->
            let t = [ (1, i); (-1, j) ] in
            let _ = Encoding.add_int_lin_ne e (named t) 0 in
            [
              pack_ne ~id:(id ()) obs (Ne.Int_ne.make store (Var.of_int i) (Var.of_int j));
            ])
      m.cstrs
  in
  (e, Engine.create instances)

(* ================================================================== veripb *)

(* Which veripb: [Baguette_proof.Checker] decides, for this file as for every other.
   This used to be a private copy of the search that preferred ~/.local/bin, which is
   the Python 2.2.2 -- so this file alone went on checking against 2.2.2 after D-0023
   made 3.0.2 the checker of record, and could not have checked a 3.0 proof at all.
   It was also the suite's wall-clock pole for exactly that reason. *)
let veripb = Baguette_proof.Checker.find ()

(* The format the writer is actually emitting this run. Everything below that reads or
   writes proof text has to agree with it: 3.0 is not a dialect of 2.0 (D-0023), so a
   helper that knows only one spelling does not merely miss -- it goes quietly true.
   See [level_of_line] for the case where that bit us. *)
let proof_format = Writer.default_format ()
let v3 = proof_format = Writer.V3_0

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

let write_file path s =
  let oc = open_out_bin path in
  output_string oc s;
  close_out oc

let last_veripb_log = ref ""

let run_veripb ~dir ~opb proof_text =
  match veripb with
  | None -> None
  | Some exe ->
      let pbp = Filename.concat dir "check.pbp" in
      let log = Filename.concat dir "check.log" in
      write_file pbp proof_text;
      let rc =
        Sys.command
          (Printf.sprintf "%s %s %s > %s 2>&1" (Filename.quote exe) (Filename.quote opb)
             (Filename.quote pbp) (Filename.quote log))
      in
      (last_veripb_log := try read_file log with _ -> "");
      Some (rc = 0)

(* A one-rule proof: load the model, state this constraint, conclude nothing. veripb
   accepts `conclusion NONE` as VERIFIED NO CONCLUSION, which asks exactly the question
   that matters -- is this line derivable from the model alone, with no search, no
   decision and no other derived constraint in the database? *)
let standalone ~dir ~opb ~n_model rule_line =
  let term body = if v3 then body ^ " ;" else body in
  run_veripb ~dir ~opb
    (String.concat "\n"
       [
         Printf.sprintf "pseudo-Boolean proof version %s"
           (Writer.format_to_string proof_format);
         term (Printf.sprintf "f %d" n_model);
         (* [rule_line] is copied verbatim out of the emitted proof, so it already
            carries its own label and terminator in whichever format wrote it. *)
         rule_line;
         term "output NONE";
         term "conclusion NONE";
         term "end pseudo-Boolean proof";
         "";
       ])

(* =========================================================== reading a proof *)

let lines_of s = String.split_on_char '\n' s

let starts_with pre s =
  String.length s >= String.length pre && String.sub s 0 (String.length pre) = pre

let contains needle s =
  let n = String.length needle and m = String.length s in
  let rec go i = i + n <= m && (String.sub s i n = needle || go (i + 1)) in
  n = 0 || go 0

(* Which rules mint a constraint id, in [Writer]'s own order. Everything else -- `#`,
   `w`, `del`, `*`, `output`, `conclusion` -- mints nothing, so walking the file with
   this counter reproduces the checker's numbering. *)
(* In 3.0 every derived constraint is introduced with a label, `@c17 rup ... ;`, so
   the rule name is no longer the first token. [Writer] owns the stripping, for the
   same reason it owns the level marker: it is the thing that wrote the label. A
   matcher that knew only the 2.0 spelling would find no rules at all, and every
   id-walking check below would pass over an empty list -- green, and testing nothing. *)
let strip_label = Writer.strip_label

let mints_id line =
  let body = strip_label line in
  List.exists
    (fun p -> starts_with p body)
    [ "pol "; "rup "; "red "; "solx "; "soli "; "obju " ]

(* Where a decision level was opened. [Writer] owns both spellings -- `# l` in 2.0,
   the `% level l` comment in 3.0 (D-0024) -- because [Writer.set_level] is what wrote
   them. Reading them back through it is what stops this file from being the one that
   still knows only 2.0. *)
let level_of_line = Writer.level_of_line
let opens_level = Writer.opens_level

(* Every rule line as (id, proof level it was filed at, text). The level comes from the
   marker [Writer.set_level] emits whether or not comments are on -- `# l` in 2.0, the
   `% level l` comment in 3.0 (D-0024 took the rule away, not the information). *)
let numbered_rules ~n_model proof =
  let id = ref n_model and level = ref 0 in
  List.filter_map
    (fun line ->
      match level_of_line line with
      | Some l ->
          level := l;
          None
      | None ->
          if mints_id line then (
            incr id;
            Some (!id, !level, line))
          else None)
    (lines_of proof)

(* Replace the rules [victim] selects with a tautology over an existing variable. The
   replacement still mints an id, so every later `pol`, `del` and `conclusion`
   reference stays correct and the checker's complaint is about the nogood rather than
   about a dangling id. *)
let blank_rules ~n_model ~victim ~taut proof =
  let id = ref n_model in
  String.concat "\n"
    (List.map
       (fun line ->
         if mints_id line then (
           incr id;
           if victim !id then taut !id else line)
         else line)
       (lines_of proof))

(* ============================================================ one instance *)

(* [claims], [shape_claims] and [depth] are the instance's own description of what it
   does, and all three are CHECKED against the run rather than believed. The rule this
   file works to is that a sentence in [note] may explain a claim but may never BE one:
   test/models/guess_wrong_sat.fzn shipped with a header asserting that its search had
   to guess wrong, and the search fixed every variable at the root instead -- the model
   was green, the comment was false, and nothing could tell. Anything a note says about
   what the search or the data does belongs in one of these three fields. *)
type instance = {
  title : string;
  m : model;
  props : propagator list;
  claims : situation list; (* situations this instance must actually reach *)
  shape_claims : shape list; (* data shapes it must actually exercise *)
  depth : int; (* 0: must NOT branch. n > 0: must reach decision level n *)
  note : string;
}

type result = { reached : situation list; shapes : shape list }

let run_instance inst =
  let m = inst.m in
  let tag = inst.title in
  let expected = brute_force m in
  let expect_sat = expected <> None in
  let dir = Filename.temp_file "baguette_matrix" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  let opb = Filename.concat dir "model.opb" in
  let pbp = Filename.concat dir "model.pbp" in
  let store = build_store m in
  let obs = new_obs () in
  let encoding, engine = build m store obs ~deep:true in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ tag ] encoding oc;
  close_out oc;
  let n_model = Encoding.n_constraints encoding in
  let oc = open_out pbp in
  (* audit:true puts I-X2 under test: the level-0 trace lines are the one class of rule
     no `w` retires, so a leak raises at [conclusion] rather than shipping quietly. *)
  let writer = Writer.create ~audit:true oc in
  Encoding.start_proof encoding writer;
  let ctx =
    Justify.create ~writer ~encoding ~model_id:(fun () ->
        failwith (tag ^ ": search demanded Explanation.Trivial (D-0011)"))
  in
  let trace = Trace.create () in
  let entry_level = Store.level store in
  let outcome =
    try Search.solve ~engine ~store ~ctx ~check:(independent_check m) ~trace ()
    with Search.Unsound_solution a ->
      fail "%s: I-P1/I-S1 -- the search returned an assignment the model rejects" tag;
      ignore a;
      Search.Unsat
  in
  close_out oc;
  check
    (tag ^ ": decision level restored on return (I-S3)")
    (entry_level = Store.level store);
  let proof = read_file pbp in
  let rules = numbered_rules ~n_model proof in
  let trace_ids = Trace.emitted_ids trace in
  let is_trace id = List.mem id trace_ids in
  let branched = opens_level 1 proof in

  (* ---- the answer, from brute force, never hand-written *)
  (match outcome with
  | Search.Sat assignment ->
      check (tag ^ ": agrees with brute force (SAT)") expect_sat;
      check
        (tag ^ ": the solution independently satisfies the model (I-S1)")
        (independent_check m assignment)
  | Search.Unsat -> check (tag ^ ": agrees with brute force (UNSAT)") (not expect_sat));

  (* ---- what the run actually reached *)
  let trace_levels =
    List.filter_map (fun (id, lvl, _) -> if is_trace id then Some lvl else None) rules
  in
  let nogood_levels =
    List.filter_map
      (fun (id, lvl, line) ->
        if (not (is_trace id)) && starts_with "rup " line then Some lvl else None)
      rules
  in
  let reached =
    List.filter
      (fun s ->
        match s with
        | S_root_prune -> List.exists (fun l -> l = 0) trace_levels
        | S_prune_one_decision -> List.exists (fun l -> l >= 1) trace_levels
        | S_prune_nested -> List.exists (fun l -> l >= 2) trace_levels
        | S_root_slack_conflict -> obs.root_slack
        | S_conflict_under_decisions ->
            List.exists (fun l -> l >= 1) obs.conflict_levels
            || List.exists (fun l -> l >= 1) nogood_levels
        | S_cross_row_conflict -> obs.cross_conflict
        | S_both_branches_fail -> branched && outcome = Search.Unsat
        | S_sat_after_failure ->
            (match outcome with Search.Sat _ -> true | _ -> false) && trace_ids <> [])
      all_situations
  in
  let shapes =
    static_shapes m
    @ List.filter
        (fun s ->
          match s with
          | D_weaken_and_cite -> obs.weaken_and_cite
          | D_cross_instance_cite -> obs.cross_instance_cite
          | D_division_remainder -> obs.div_remainder
          | D_big_coeff -> obs.div_nontrivial
          | _ -> false)
        all_shapes
  in
  let shapes = List.sort_uniq compare shapes in
  Printf.printf "  observed: %s%s%s%s%s conflicts at level(s) %s\n"
    (if obs.slack_conflict then "row-slack " else "")
    (if obs.cross_conflict then "cross-row " else "")
    (if obs.ne_conflict then "disequality-clause " else "")
    (if obs.div_nontrivial then "divisor>1 " else "")
    (if obs.div_remainder then "rounded-division " else "")
    (match obs.conflict_levels with
    | [] -> "(none)"
    | l -> String.concat "," (List.map string_of_int (List.sort_uniq compare l)));

  (* An instance that does not do what it says is a decoration, not a test. *)
  List.iter
    (fun s ->
      check
        (Printf.sprintf "%s: reaches the case it is here for -- %s" tag (situation_name s))
        (List.mem s reached))
    inst.claims;
  List.iter
    (fun d ->
      check
        (Printf.sprintf "%s: exercises the data shape it is here for -- %s" tag
           (shape_name d))
        (List.mem d shapes))
    inst.shape_claims;
  (* The search shape, read off the level markers the writer emits whatever the comment
     flag says -- not inferred from first-fail and indomain_min. [opens_level] knows
     both spellings; spelling one of them here is how this check would go quietly true
     under the other. *)
  if inst.depth = 0 then
    check
      (tag ^ ": the search does not branch at all, so there is no trace and no nogood")
      ((not branched) && trace_ids = [])
  else
    check
      (Printf.sprintf "%s: the search reaches decision level %d" tag inst.depth)
      (opens_level inst.depth proof);
  (match obs.forcing_raised with
  | None -> ()
  | Some e -> fail "%s: forcing an explanation raised %s" tag e);

  (* ---- the whole proof. Never an xfail. *)
  (match run_veripb ~dir ~opb proof with
  | None ->
      fail "%s: veripb not found -- I-X1 was NOT checked. Do not read this as a pass" tag
  | Some ok ->
      check (tag ^ ": veripb accepts the proof (I-X1)") ok;
      if not ok then
        Printf.printf "  veripb said:\n%s\n  model:\n%s\n  proof:\n%s\n" !last_veripb_log
          (read_file opb) proof);

  (* ---- the discriminating check: each trace line on its own against the .opb, and
     each nogood NOT on its own. See the header, check 3. *)
  let bad_trace = ref [] and bad_nogood = ref [] in
  List.iter
    (fun (id, _, line) ->
      match standalone ~dir ~opb ~n_model line with
      | None -> ()
      | Some ok ->
          if is_trace id then (if not ok then bad_trace := (id, line) :: !bad_trace)
          else if ok then bad_nogood := (id, line) :: !bad_nogood)
    rules;
  if trace_ids <> [] then (
    check
      (Printf.sprintf "%s: all %d trace lines verify standalone against the .opb" tag
         (List.length trace_ids))
      (!bad_trace = []);
    List.iter
      (fun (id, line) -> Printf.printf "  not standalone-valid: id %d  %s\n" id line)
      !bad_trace);
  (* Only meaningful on a satisfiable model: in an UNSAT one the model rows are jointly
     contradictory, so every clause is entailed and whether veripb reaches one by unit
     propagation measures the checker's luck, not our proof. *)
  if expect_sat && trace_ids <> [] then (
    check
      (tag ^ ": every nogood needs the trace -- none is standalone-RUP")
      (!bad_nogood = []);
    List.iter
      (fun (id, line) ->
        Printf.printf "  unexpectedly standalone-valid nogood: id %d  %s\n" id line)
      !bad_nogood);

  (* ---- the negative control: blank the whole trace, keep every id, and the checker
     must refuse. D-0021 measured that blanking half of chain_sat's trace changes
     nothing, so this blanks all of it. *)
  (if trace_ids <> [] then
     let name0, lo0, _ = m.vars.(0) in
     (* Under 3.0 the replacement must keep the *label* of the line it replaces, not
        just its id: later `pol`, `del` and `conclusion` lines cite `@cN`, and an
        unlabelled stand-in would make those a parse error -- the checker would then
        reject for a dangling name rather than for the blanked reasoning, and this
        control would be green for the wrong reason. *)
     let taut id =
       let body =
         Printf.sprintf "rup +1 %s_ge_%d +1 ~%s_ge_%d >= 1 ;" name0 (lo0 + 1) name0
           (lo0 + 1)
       in
       if v3 then Printf.sprintf "@c%d %s" id body else body
     in
     let blanked = blank_rules ~n_model ~victim:is_trace ~taut proof in
     match run_veripb ~dir ~opb blanked with
     | None -> ()
     | Some ok ->
         check (tag ^ ": with the trace blanked out, veripb rejects") (not ok);
         if ok then Printf.printf "  blanked proof still verified:\n%s\n" blanked);

  List.iter
    (fun f -> try Sys.remove f with _ -> ())
    [ opb; pbp; Filename.concat dir "check.pbp"; Filename.concat dir "check.log" ];
  (try Sys.rmdir dir with _ -> ());
  { reached; shapes }

(* ============================================================== the instances *)

(* Every instance below is one step past the smallest thing that exercises its cell,
   which is the lesson of D-0009/D-0010/D-0012/D-0017/D-0021: the failing case always
   needed one more step than the test had. *)
let instances =
  [
    {
      title = "lin_le/root-slack";
      m =
        {
          vars = [| ("x", 0, 5); ("y", 0, 5) |];
          cstrs = [ Lin_le ([ (1, 0); (1, 1) ], 3); Lin_le ([ (-1, 0); (-1, 1) ], -8) ];
        };
      props = [ P_lin_le ];
      claims = [ S_root_slack_conflict ];
      shape_claims = [ D_neg_coeff ];
      depth = 0;
      note =
        "the refutation is decided at the root by one row's own slack, with no decision \
         on the stack -- the only situation in which no trace exists at all";
    };
    {
      title = "lin_le/parity-branching";
      m =
        {
          vars = [| ("x1", 0, 3); ("x2", 0, 3); ("x3", 0, 3) |];
          cstrs =
            [
              Lin_le ([ (2, 0); (2, 1); (2, 2) ], 5);
              Lin_le ([ (-2, 0); (-2, 1); (-2, 2) ], -5);
            ];
        };
      props = [ P_lin_le ];
      claims =
        [
          S_prune_one_decision;
          S_prune_nested;
          S_conflict_under_decisions;
          S_both_branches_fail;
        ];
      shape_claims = [ D_neg_coeff; D_big_coeff; D_common_factor; D_division_remainder ];
      depth = 2;
      note =
        "2(x1+x2+x3) = 5 written as two <= rows: UNSAT by parity, which bounds reasoning \
         cannot see at the root, so the search must branch and keep branching. Every |a| \
         > 1 and the coefficients share a factor of 2, so the Combine division is \
         non-trivial and rounds";
    };
    {
      (* This is also test/models/offset_unsat.fzn, mirrored so that "the search has to
         branch and refute both children at every level" is an asserted check rather
         than a sentence in that file's header. *)
      title = "lin_eq/offset-negative (mirrors test/models/offset_unsat.fzn)";
      m =
        {
          vars = [| ("a", -4, -1); ("b", -4, -1); ("c", -4, -1) |];
          cstrs = [ Lin_eq ([ (2, 0); (-2, 1); (2, 2) ], -5) ];
        };
      props = [ P_lin_eq; P_lin_le ];
      claims = [ S_prune_one_decision; S_both_branches_fail ];
      shape_claims =
        [
          D_neg_coeff;
          D_big_coeff;
          D_common_factor;
          D_offset_domain;
          D_negative_domain;
          D_division_remainder;
        ];
      depth = 2;
      note =
        "2a - 2b + 2c = -5 over three entirely negative domains: the left-hand side is \
         always even and the right-hand side is odd, and -5 sits inside the row's own \
         [-14, 4] span, so no bound can refute it and the search has to branch. Every \
         domain is offset away from zero and entirely negative, one coefficient is \
         negative, all share a factor of 2 and all are past |1| -- the data shapes \
         D-0010 hid behind, at once";
    };
    {
      title = "lin_eq/sat-after-failure";
      m =
        {
          vars = [| ("x1", 1, 5); ("x2", 1, 5); ("x3", 1, 5) |];
          cstrs =
            [
              Lin_eq ([ (1, 0); (1, 1); (1, 2) ], 10);
              Lin_eq ([ (1, 1); (-1, 0) ], 2);
              Lin_le ([ (1, 2); (-1, 1) ], 0);
            ];
        };
      props = [ P_lin_eq; P_lin_le ];
      claims = [ S_root_prune; S_sat_after_failure ];
      shape_claims = [ D_neg_coeff; D_offset_domain ];
      depth = 1;
      note =
        "satisfiable, but only after the search guesses wrong once -- the D-0017 shape \
         -- and over domains offset away from zero, so the order-encoding constant of \
         every root pruning is non-zero (D-0010). The SAT path then has to retire the \
         level-0 trace lines it wrote on the way, which no `w` covers, or the I-X2 audit \
         fires at conclusion";
    };
    {
      title = "int_le/chain-offset";
      m =
        {
          vars = [| ("p", 2, 6); ("q", 2, 6); ("r", 2, 6) |];
          cstrs =
            [ Le (0, 1); Le (1, 2); Lin_eq ([ (1, 0); (1, 1); (1, 2) ], 11); Le (2, 0) ];
        };
      props = [ P_le; P_lin_eq; P_lin_le ];
      claims = [ S_prune_one_decision; S_prune_nested; S_both_branches_fail ];
      shape_claims =
        [ D_neg_coeff; D_offset_domain; D_weaken_and_cite; D_cross_instance_cite ];
      depth = 2;
      note =
        "p <= q <= r <= p forces all three equal, and 3p = 11 has no integer solution: \
         UNSAT for a reason bounds propagation over the offset domain 2..6 reaches only \
         after branching. int_le carries the cycle, so the bound each of its rows cites \
         was derived by one of the other two instances";
    };
    {
      title = "int_lt/strict-cycle";
      m =
        {
          vars = [| ("u", -3, 1); ("v", -3, 1); ("w", -3, 1) |];
          cstrs = [ Lt (0, 1); Lt (1, 2); Lin_eq ([ (1, 0); (1, 2) ], -1); Lt (2, 0) ];
        };
      props = [ P_lt; P_lin_eq; P_lin_le ];
      claims = [ S_root_slack_conflict ];
      shape_claims = [ D_neg_coeff; D_cross_instance_cite ];
      depth = 0;
      note =
        "u < v < w < u over a domain that straddles zero. The strict cycle is refuted at \
         the root by one int_lt row's own slack, once the other two rows have pushed -- \
         so this is int_lt in the citing position, reading a bound a different instance \
         established";
    };
    {
      title = "int_eq/aliased-parity";
      m =
        {
          vars = [| ("m", -2, 3); ("n", -2, 3); ("k", -2, 3) |];
          cstrs = [ Eq (0, 1); Lin_eq ([ (2, 0); (2, 1) ], 3); Eq (1, 2) ];
        };
      props = [ P_eq; P_lin_eq; P_lin_le ];
      claims = [ S_root_slack_conflict ];
      shape_claims = [ D_neg_coeff; D_big_coeff; D_common_factor; D_division_remainder ];
      depth = 0;
      note =
        "m = n = k with 2m + 2n = 3: even equals odd. The domain straddles zero so the \
         order-encoding constant is non-zero, which is the D-0010 shape, and the divisor \
         is 2 with a remainder";
    };
    {
      title = "int_eq/branching-parity";
      m =
        {
          vars = [| ("m", 1, 4); ("n", 1, 4); ("k", 1, 4) |];
          cstrs = [ Eq (0, 1); Lin_eq ([ (1, 0); (1, 1); (1, 2) ], 7); Eq (1, 2) ];
        };
      props = [ P_eq; P_lin_eq; P_lin_le ];
      claims = [ S_prune_one_decision; S_both_branches_fail ];
      shape_claims = [ D_neg_coeff; D_offset_domain ];
      depth = 2;
      note =
        "m = n = k with m + n + k = 7 over the offset domain 1..4: 3m = 7, UNSAT, and \
         unlike the aliased parity case above the root fixpoint does not close it, so a \
         decision has to be made and its trace written";
    };
    {
      title = "int_ne/equality-cycle";
      m =
        {
          vars = [| ("x", 0, 4); ("y", 0, 4); ("z", 0, 4) |];
          cstrs =
            [
              Lin_eq ([ (1, 0); (-1, 2) ], 0);
              Lin_eq ([ (1, 1); (-1, 2) ], 0);
              Lin_le ([ (-1, 2) ], -1);
              Ne (0, 1);
            ];
        };
      props = [ P_ne; P_lin_eq; P_lin_le ];
      claims =
        [
          S_root_prune;
          S_prune_one_decision;
          S_prune_nested;
          S_conflict_under_decisions;
          S_both_branches_fail;
        ];
      shape_claims = [ D_neg_coeff ];
      depth = 3;
      note =
        "x = z, y = z, z >= 1, x <> y. The two equalities fix x and y to each other only \
         once a decision has been made, so int_ne is reached with both variables already \
         fixed and its own clause is the contradiction -- the one int_ne situation the \
         D-0018 trace covers today (see [known_bug_ne_trace_facts] for the one it does \
         not). Five levels deep, and at each one the second branch is entered at the \
         same trail positions the first used";
    };
    {
      (* Mirrors test/models/guess_wrong_sat.fzn. The .fzn header claims the search has
         to guess wrong before it can succeed; the model runner cannot check that (it
         compares stdout and runs veripb, both of which a root-fixed model passes), so
         the claim is asserted HERE, where [S_sat_after_failure] and [depth = 1] are
         checked against the emitted proof. An earlier version of that .fzn asserted the
         same thing in prose and was simply wrong. *)
      title = "guess_wrong (mirrors test/models/guess_wrong_sat.fzn)";
      m =
        {
          vars = [| ("p", 1, 4); ("q", 1, 4); ("r", 1, 4) |];
          cstrs =
            [
              Lin_eq ([ (1, 0); (1, 1); (1, 2) ], 6);
              Lin_eq ([ (2, 0); (3, 1); (4, 2) ], 20);
              Le (0, 1);
              Le (1, 2);
            ];
        };
      props = [ P_lin_eq; P_le; P_lin_le ];
      claims = [ S_root_prune; S_prune_one_decision; S_sat_after_failure ];
      shape_claims = [ D_neg_coeff; D_big_coeff; D_offset_domain ];
      depth = 1;
      note =
        "p + q + r = 6, 2p + 3q + 4r = 20, p <= q <= r over 1..4 -- one solution, (1, 2, \
         3), and the search reaches it only after refuting r <= 2. The D-0017 shape with \
         an offset domain: a SAT run whose proof contains a real trace and a real \
         nogood, both checked by veripb before `conclusion SAT` is reached";
    };
    {
      title = "int_lin_ne/sat-after-failure";
      m =
        {
          vars = [| ("e", 0, 4); ("f", 0, 4); ("g", 0, 4) |];
          cstrs =
            [
              Lin_eq ([ (1, 1); (-1, 0) ], 1);
              Lin_eq ([ (1, 2); (-1, 1) ], 1);
              Lin_le ([ (-1, 0) ], -1);
              Lin_ne ([ (1, 0); (1, 1); (1, 2) ], 6);
            ];
        };
      props = [ P_lin_ne; P_lin_eq; P_lin_le ];
      claims = [ S_root_prune; S_prune_one_decision; S_sat_after_failure ];
      shape_claims = [ D_neg_coeff ];
      depth = 1;
      note =
        "f = e+1, g = f+1, e >= 1, and e+f+g <> 6 -- which forbids exactly e = 1. \
         indomain_min tries e = 1 first, so the disequality's conflict closes a branch \
         and the solution e = 2 is found only afterwards: int_lin_ne conflicting under a \
         decision, with a real linear trace in front of it";
    };
    (* The three instances below fill the int_ne / int_lin_ne shape cells M1-T16 had to
       leave empty. They were blocked on the M1-T17 bug, not on the data: a disequality
       pruning that moved a bound wrote a factless trace line, so each of these would
       have printed the same failure again. D-0022 / I-P5 closed that -- [Ne.propagate]
       prunes through [Store.remove_with_facts] now -- and each instance below puts a
       bound-moving disequality pruning inside a branch that then fails, so the line it
       writes is emitted, verified standalone against the .opb, and blanked as a
       negative control.

       All three are SAT, and in all three the disequality is LOAD-BEARING: delete it
       from the model and the search's first complete assignment is one it forbids
       (x = y = -5, p = q = 5, a = b = -5 respectively). That is what ne_sat.fzn lacked
       -- int_lt alone solved it, so int_ne could have been a no-op and the test stayed
       green. Here a no-op disequality does not merely weaken the proof: [Search.solve]'s
       own [check] rejects the assignment (I-S1) and the run disagrees with brute force.
       Measured by mutating lib/core/prop/ne.ml, not argued.

       All three also carry a third variable that the disequality does not mention, and
       DECLARED domains wider than the box the root fixpoint leaves. Both are forced by
       the "every nogood needs the trace" check above, and the first drafts of these
       three failed it: over two variables whose declared bounds the search reaches
       directly, veripb's own unit propagation replays the whole refutation from the
       .opb and the nogood is standalone-RUP, which means the trace it was supposed to
       rest on was never load-bearing. Widening the declared domain so the branch is
       taken strictly inside it leaves the checker with an "at least k of n order
       literals" row that forces no single literal -- the D-0012 wall -- so the nogood
       needs the trace, which is the property these instances exist to exercise. *)
    {
      title = "int_ne/negative-domain";
      m =
        {
          vars = [| ("x", -5, -1); ("y", -5, -1); ("m", -5, -1) |];
          cstrs =
            [
              Ne (0, 1);
              Lin_le ([ (-1, 0) ], 4);
              Lin_eq ([ (1, 2); (-1, 0) ], 1);
              Lin_le ([ (1, 1); (-1, 2) ], -1);
              Lin_le ([ (-1, 1) ], 4);
            ];
        };
      props = [ P_ne; P_lin_eq; P_lin_le ];
      claims =
        [
          S_root_prune;
          S_prune_one_decision;
          S_conflict_under_decisions;
          S_sat_after_failure;
        ];
      shape_claims = [ D_neg_coeff; D_offset_domain; D_negative_domain ];
      depth = 2;
      note =
        "x >= -4, m = x + 1, y <= m - 1, y >= -4, x <> y over three domains that are \
         entirely negative and offset away from zero, so every order-encoding constant \
         int_ne writes is non-zero and negative -- the D-0010 shape applied to a \
         disequality rather than to a linear row. indomain_min tries x = -4 first, where \
         y's own bounds pin it to -4 as well, so int_ne removes -4 from y, which is y's \
         lower bound; the branch then fails on y <= m - 1 and (-3, -4, -2) is reached \
         afterwards. Drop the disequality and the search returns x = y = -4";
    };
    {
      title = "int_lin_ne/common-factor-offset";
      m =
        {
          vars = [| ("e", 1, 5); ("f", 1, 5); ("g", 1, 5) |];
          cstrs =
            [
              Lin_ne ([ (2, 0); (4, 2) ], 16);
              Lin_le ([ (-1, 0) ], -2);
              Lin_eq ([ (1, 1); (-1, 0) ], 1);
              Lin_le ([ (-1, 2) ], -3);
              Lin_le ([ (1, 2); (-1, 1) ], 0);
            ];
        };
      props = [ P_lin_ne; P_lin_eq; P_lin_le ];
      claims =
        [
          S_root_prune;
          S_prune_one_decision;
          S_conflict_under_decisions;
          S_sat_after_failure;
        ];
      shape_claims = [ D_neg_coeff; D_big_coeff; D_common_factor; D_offset_domain ];
      depth = 3;
      note =
        "the same skeleton over domains offset away from zero on the positive side, with \
         the disequality's OWN coefficients past |1| and sharing a factor: 2e + 4g <> \
         16, e >= 2, f = e + 1, 3 <= g <= f. |a| > 1 means [Ne.propagate]'s division by \
         the unfixed term's coefficient is not the identity, and the common factor 2 \
         means divisibility is what decides between pruning and declining -- both \
         outcomes occur here. At e = 2 the missing amount is 12, which 4 divides \
         exactly, so g's lower bound 3 is removed and g <= f closes the branch; at e = 3 \
         the remainder is 2 and int_lin_ne declines, which is how (3, 4, 3) survives. A \
         no-op int_lin_ne returns (2, 3, 3) and I-S1 rejects it";
    };
    {
      title = "int_lin_ne/coprime-negative";
      m =
        {
          vars = [| ("a", -5, -1); ("b", -5, -1); ("c", -5, -1) |];
          cstrs =
            [
              Lin_ne ([ (2, 0); (3, 2) ], -17);
              Lin_le ([ (-1, 0) ], 4);
              Lin_eq ([ (1, 1); (-1, 0) ], 1);
              Lin_le ([ (-1, 2) ], 3);
              Lin_le ([ (1, 2); (-1, 1) ], 0);
            ];
        };
      props = [ P_lin_ne; P_lin_eq; P_lin_le ];
      claims =
        [
          S_root_prune;
          S_prune_one_decision;
          S_conflict_under_decisions;
          S_sat_after_failure;
        ];
      shape_claims = [ D_neg_coeff; D_big_coeff; D_offset_domain; D_negative_domain ];
      depth = 3;
      note =
        "the instance above with the two things easiest to conflate pulled apart: 2a + \
         3c <> -17 has |a| > 1 but the coefficients are COPRIME, and the domains are \
         entirely negative. So the quotient is negative and the divisibility test has no \
         common factor to lean on -- at a = -4 the missing amount is -9, which 3 \
         divides, so c's lower bound -3 is removed and c <= b closes the branch; at a = \
         -3 it is -11, which 3 does not divide, so int_lin_ne declines and (-3, -2, -3) \
         survives. Without the disequality the search returns (-4, -3, -3)";
    };
    (* ---------------------------------------------------------------- M1-T23

       The three instances below sit near lib/flatzinc/compile.ml's cap rather than
       near zero. They are here for the half of M1-T23 that is easy to skip: a cap
       that rejects everything awkward is not a fix, it is a smaller solver. Each of
       these compiles, solves, agrees with brute force and has a proof veripb accepts,
       with every product and constant in it two orders of magnitude past anything the
       rest of this file computes.

       They are deliberately EXISTING instances rescaled rather than new shapes, so
       that a difference in outcome is a difference the magnitude caused. *)
    {
      title = "lin_eq/near-limit-parity (lin_le/parity-branching scaled by 2^53)";
      m =
        {
          vars = [| ("x1", 0, 3); ("x2", 0, 3); ("x3", 0, 3) |];
          cstrs =
            [
              Lin_eq
                ( [
                    (18014398509481984, 0); (18014398509481984, 1); (18014398509481984, 2);
                  ],
                  45035996273704960 );
            ];
        };
      props = [ P_lin_eq; P_lin_le ];
      claims =
        [
          S_prune_one_decision;
          S_prune_nested;
          S_conflict_under_decisions;
          S_both_branches_fail;
        ];
      shape_claims = [ D_big_coeff; D_common_factor; D_division_remainder ];
      depth = 2;
      note =
        "2A(x1+x2+x3) = 5A with A = 2^53, i.e. lin_le/parity-branching multiplied \
         through by 9007199254740992. Still UNSAT by parity, still invisible to bounds \
         reasoning at the root, still refuted by branching -- and now the row's \
         magnitude is 207165582859042816, 71.9% of Checked.limit, so every slack, every \
         Combine divisor and every .opb constant in the proof is a 17-digit number. \
         Everything this instance asserts about the outcome is in [claims], \
         [shape_claims] and [depth] rather than here: UNSAT against brute force, the \
         same four situations and the same depth 2 as the unscaled instance";
    };
    {
      title = "int_le/near-limit-offset";
      m =
        {
          vars =
            [|
              ("p", 144115188075855870, 144115188075855871);
              ("q", 144115188075855870, 144115188075855871);
            |];
          cstrs = [ Le (0, 1); Lin_le ([ (-1, 0); (1, 1) ], -2) ];
        };
      props = [ P_le; P_lin_le ];
      claims = [ S_root_slack_conflict ];
      shape_claims = [ D_neg_coeff; D_offset_domain ];
      depth = 0;
      note =
        "p <= q and q <= p - 2 over two domains sitting at 1.44 * 10^17, which is the \
         largest offset a two-variable row with unit coefficients can have and still \
         pass the cap: the row's magnitude is 288230376151711742, one below \
         Checked.limit. Refuted at the root by the second row's own slack, so there is \
         no trace -- what it exercises is the ORDER-ENCODING CONSTANT, a_i * lo_i, at \
         the largest value the compiler will ever hand lib/proof/encoding.ml. That \
         product is the exact expression that wrapped in the gap M1-T23 closed";
    };
    {
      title = "int_lin_ne/near-limit (common-factor-offset scaled by 5 * 10^15)";
      m =
        {
          vars = [| ("e", 1, 5); ("f", 1, 5); ("g", 1, 5) |];
          cstrs =
            [
              Lin_ne
                ([ (10000000000000000, 0); (20000000000000000, 2) ], 80000000000000000);
              Lin_le ([ (-1, 0) ], -2);
              Lin_eq ([ (1, 1); (-1, 0) ], 1);
              Lin_le ([ (-1, 2) ], -3);
              Lin_le ([ (1, 2); (-1, 1) ], 0);
            ];
        };
      props = [ P_lin_ne; P_lin_eq; P_lin_le ];
      claims =
        [
          S_root_prune;
          S_prune_one_decision;
          S_conflict_under_decisions;
          S_sat_after_failure;
        ];
      shape_claims = [ D_neg_coeff; D_big_coeff; D_common_factor; D_offset_domain ];
      depth = 3;
      note =
        "int_lin_ne/common-factor-offset with its disequality multiplied through by K = \
         5 * 10^15: 2K e + 4K g <> 16K. Divisibility is scale-invariant, so the same \
         pruning happens at e = 2 and the same decline at e = 3, and the outcome is \
         asserted where it belongs -- brute-force agreement, I-S1 on the solution, and \
         depth 3 -- rather than here. The row's magnitude is 230000000000000000, 79.8% \
         of Checked.limit -- and a disequality is the worst case the cap is sized \
         against (lib/core/checked.ml, envelope path 4), because Encoding.add_int_lin_ne \
         puts the row's own attainable span into the A/B pair's big-M coefficients. So \
         this is the instance that measures the factor of 16 rather than assuming it";
    };
  ]

(* ============================================================ the matrix report *)

let covered_situations : (situation, unit) Hashtbl.t = Hashtbl.create 16
let covered_shapes : (shape, unit) Hashtbl.t = Hashtbl.create 16
let covered_props : (propagator, unit) Hashtbl.t = Hashtbl.create 16
let cells_ps : (propagator * situation, unit) Hashtbl.t = Hashtbl.create 64
let cells_pd : (propagator * shape, unit) Hashtbl.t = Hashtbl.create 64
let cells_sd : (situation * shape, unit) Hashtbl.t = Hashtbl.create 64
let covered_overflows : (overflow, unit) Hashtbl.t = Hashtbl.create 16
let cells_po : (propagator * overflow, unit) Hashtbl.t = Hashtbl.create 64

let record_coverage inst (r : result) =
  List.iter (fun p -> Hashtbl.replace covered_props p ()) inst.props;
  (* M1-T23. Measured off the model, like [static_shapes], because there is nothing for
     an instance to CLAIM here: "this row's magnitude is 72% of the cap" is arithmetic,
     not behaviour. What keeps it honest is the hole check below -- if the near-limit
     instances were not in fact near the limit, [O_near_limit] would be an uncovered
     axis value and the run would go red. *)
  let os = static_overflow inst.m in
  List.iter (fun o -> Hashtbl.replace covered_overflows o ()) os;
  List.iter
    (fun p -> List.iter (fun o -> Hashtbl.replace cells_po (p, o) ()) os)
    inst.props;
  List.iter (fun s -> Hashtbl.replace covered_situations s ()) r.reached;
  List.iter (fun d -> Hashtbl.replace covered_shapes d ()) r.shapes;
  List.iter
    (fun p ->
      List.iter (fun s -> Hashtbl.replace cells_ps (p, s) ()) r.reached;
      List.iter (fun d -> Hashtbl.replace cells_pd (p, d) ()) r.shapes)
    inst.props;
  List.iter
    (fun s -> List.iter (fun d -> Hashtbl.replace cells_sd (s, d) ()) r.shapes)
    r.reached

let grid title rows cols row_name mem =
  Printf.printf "\n--- %s ---\n" title;
  List.iteri (fun i c -> Printf.printf "  %2d = %s\n" (i + 1) c) cols;
  List.iter
    (fun r ->
      Printf.printf "  %-46s" (row_name r);
      List.iteri (fun i _ -> Printf.printf " %s" (if mem r i then "X" else ".")) cols;
      print_newline ())
    rows

let report_matrix () =
  grid "propagator x situation" all_propagators (List.map situation_name all_situations)
    propagator_name (fun p i -> Hashtbl.mem cells_ps (p, List.nth all_situations i));
  grid "propagator x data shape" all_propagators (List.map shape_name all_shapes)
    propagator_name (fun p i -> Hashtbl.mem cells_pd (p, List.nth all_shapes i));
  grid "situation x data shape" all_situations (List.map shape_name all_shapes)
    situation_name (fun s i -> Hashtbl.mem cells_sd (s, List.nth all_shapes i));
  grid "propagator x overflow (M1-T23)" all_propagators
    (List.map overflow_name all_overflows) propagator_name (fun p i ->
      Hashtbl.mem cells_po (p, List.nth all_overflows i));
  print_endline "\n--- axis coverage ---";
  let holes = ref [] in
  List.iter
    (fun p ->
      Printf.printf "  %s  propagator %s\n"
        (if Hashtbl.mem covered_props p then "X" else ".")
        (propagator_name p);
      if not (Hashtbl.mem covered_props p) then
        holes := ("propagator " ^ propagator_name p) :: !holes)
    all_propagators;
  List.iter
    (fun s ->
      Printf.printf "  %s  situation %s\n"
        (if Hashtbl.mem covered_situations s then "X" else ".")
        (situation_name s);
      if not (Hashtbl.mem covered_situations s) then
        holes := ("situation " ^ situation_name s) :: !holes)
    all_situations;
  List.iter
    (fun d ->
      Printf.printf "  %s  shape %s\n"
        (if Hashtbl.mem covered_shapes d then "X" else ".")
        (shape_name d);
      if not (Hashtbl.mem covered_shapes d) then
        holes := ("shape " ^ shape_name d) :: !holes)
    all_shapes;
  List.iter
    (fun o ->
      Printf.printf "  %s  overflow %s\n"
        (if Hashtbl.mem covered_overflows o then "X" else ".")
        (overflow_name o);
      if not (Hashtbl.mem covered_overflows o) then
        holes := ("overflow " ^ overflow_name o) :: !holes)
    all_overflows;
  (* A hole is reported, never absorbed. An axis value no instance reaches means the
     matrix is not testing it, whatever the pass count says. *)
  check "every axis value has at least one instance that reaches it" (!holes = []);
  List.iter (fun h -> Printf.printf "  UNCOVERED: %s\n" h) (List.rev !holes);
  print_endline "\n--- empty cells, and why (read this before adding an instance) ---";
  List.iter
    (fun l -> Printf.printf "  %s\n" l)
    [
      "cross-row conflict x everything but int_lin_le: the situation is a property of \
       Linear.propagate, and int_le/int_lt/int_eq/int_lin_eq ARE Linear instances, so \
       the row would be identical. int_ne/int_lin_ne cannot reach it at all -- they \
       never compute a slack. See [cross_row_cell] for why even int_lin_le reaches it \
       only through a row that names one variable twice.";
      "int_lt x anything but a root slack conflict: int_lt is int_le with rhs - 1 and \
       shares every line of Linear, so a second branching instance would re-run \
       int_le/chain-offset with a different constant. The cell is left empty \
       deliberately rather than filled with a duplicate.";
      "int_ne / int_lin_ne x the offset and negative-domain shapes: FILLED as of M1-T20. \
       M1-T16 left them empty because every disequality pruning that moved a bound then \
       emitted a factless trace line, so an instance would only have reprinted that \
       failure; M1-T17 fixed it (D-0022, I-P5, Store.remove_with_facts) and the cells \
       opened as predicted. int_ne/negative-domain and int_lin_ne/coprime-negative fill \
       them, and each was confirmed to fail with the fix reverted -- the factless line \
       comes back and is not standalone-valid.";
      "int_lin_ne x |a| > 1 and x the common factor: FILLED, by \
       int_lin_ne/common-factor-offset (2e + 4g <> 16) and int_lin_ne/coprime-negative \
       (2a + 3c <> -17, the same shape with the factor removed, because \"non-unit\" and \
       \"shares a factor\" are easy to conflate and only one of them is what \
       [Ne.propagate]'s divisibility test turns on).";
      "int_ne x |a| > 1 and x the common factor: NOT filled, and NOT because of the \
       M1-T17 bug -- these two cells are unreachable by construction. int_ne IS 1*x + \
       (-1)*y <> 0 ([Ne.Int_ne.make]), so its coefficients are 1 and -1 in every \
       instance there can ever be; neither |a| > 1 nor a shared factor is a shape its \
       data can have. A shape is credited to every propagator in the instance's [props], \
       so these cells COULD be turned X by putting a big coefficient on some other row \
       of an int_ne model -- which would record something int_ne did not do. Left empty \
       deliberately, like the int_lt row above.";
      "int_ne / int_lin_ne x a push whose division has a remainder: not reachable as \
       that column is defined. The column means a push whose division rounded; for a \
       disequality a non-zero remainder is exactly the case where nothing is pruned \
       ([Ne.propagate]'s `rest mod tm.coeff <> 0 -> Fixpoint`), so there is no push to \
       round. Both int_lin_ne instances take that branch -- at e = 3 and at a = -3 -- \
       and their notes say so; it is the absence of a push that is being exercised.";
      "int_ne x conflict at root from a row's own slack: a disequality has no slack. Its \
       root conflict is its own clause, which is [known_bug_ne_snap_cite]'s territory \
       when another row cites it.";
      "OVERFLOW AXIS (M1-T23). Compile refuses the model x every propagator: EMPTY for \
       all seven, by construction. The cap is enforced in lib/flatzinc/compile.ml before \
       a single propagator instance exists, so there is no propagator to credit; putting \
       the model's builtins in the column would record something no propagator did, \
       which is the rule the int_lt and int_ne rows above already apply. The axis value \
       is covered by [overflow_compile_cell] directly, which is why the coverage line \
       for it is X while the whole column is empty.";
      "overflow: a product / a sum that leaves the range x int_lin_eq, int_le, int_lt, \
       int_eq: EMPTY, and for the reason the int_lt row gives. All four ARE Linear \
       instances -- int_le.ml, int_lt.ml and lin_eq.ml hand their terms to Linear.make \
       and re-export Linear.propagate unchanged -- so the overflowing product is the \
       same line of the same function, reached with a different row id. Filling them \
       would be the int_lin_le cell four more times.";
      "overflow: a sum that leaves the range x int_ne: EMPTY, and unreachable by \
       construction rather than merely unfilled. int_ne IS 1*x + (-1)*y <> 0, so when \
       one term is unfixed [Ne.propagate]'s sum_of runs over exactly ONE other term: \
       there is no sum, only a product, and the product cell IS filled (the negation of \
       a fixed min_int). A three-term disequality is int_lin_ne, which fills the sum \
       cell. Same shape of argument as int_ne x |a| > 1 above.";
      "overflow: near the cap x int_lt, int_eq: EMPTY, duplicates again. int_lt is \
       int_le with rhs - 1 and int_eq is Lin_eq over unit coefficients, so a near-limit \
       instance for either is int_le/near-limit-offset or lin_eq/near-limit-parity with \
       a different constant.";
      "overflow: near the cap x int_ne: EMPTY, deliberately, and this one is worth the \
       sentence. int_ne's coefficients are 1 and -1 in every instance there can ever be, \
       so 'near the cap' for it is entirely a property of the DECLARED DOMAINS -- which \
       int_le/near-limit-offset already drives to 1.44 * 10^17, the largest a \
       two-variable unit-coefficient row can have and still pass, over the same [Linear] \
       arithmetic and the same order-encoding constants. The path that is specific to a \
       disequality, and that the cap's factor of 16 is actually sized against \
       (lib/core/checked.ml, envelope path 4: Encoding.add_int_lin_ne folds the row's \
       attainable span into the A/B pair's big-M coefficients), is driven to 79.8% of \
       the cap by int_lin_ne/near-limit. Between the two, nothing about a disequality at \
       scale is untested, and a third instance would fill a cell without adding a path.";
      "pruning at root x entirely negative domains: FILLED as of M1-T20, as a side \
       effect rather than on purpose. M1-T16 left it empty because \
       lin_eq/offset-negative branches before it prunes anything at the root, and asked \
       for a negative-domain model whose root fixpoint moves a bound AND whose search \
       still has to guess. int_ne/negative-domain and int_lin_ne/coprime-negative are \
       both that model: the `x >= -4` and `y >= -4` rows move a bound at level 0 and the \
       disequality still forces a wrong guess afterwards.";
    ]

(* ================================================= the D-0019 / M1-T9 gap *)

(* agent-ne's finding, reported in D-0019's last consequence and not fixed:
   [linear.ml]'s Snap_cite path cites whatever trail entry last moved a bound and folds
   it into a `pol` as though it were a unit-coefficient chain-sum over that variable's
   declared range. [int_ne] can also move a bound -- removing a value at lo or hi
   shrinks the interval -- and its explanation is a [Clause], not a chain-sum.

   The instance: x declared 0..1 and pinned to 0 by its own row, int_ne(x, y) then
   pushes lo(y) to 1 by removing 0, and the row y <= 0 conflicts on its own slack and
   cites that pruning. Reachable only at a ROOT conflict, because under a decision the
   nogood is a plain rup over the trace and the `pol` is never built.

   This is written as a test, not a workaround. If it fails, that is the correct
   outcome and the finding is live. *)
let known_bug_ne_snap_cite () =
  let dir = Filename.temp_file "baguette_nebug" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  let opb = Filename.concat dir "b.opb" and pbp = Filename.concat dir "b.pbp" in
  let m =
    {
      vars = [| ("x", 0, 1); ("y", 0, 2) |];
      cstrs = [ Lin_le ([ (1, 0) ], 0); Ne (0, 1); Lin_le ([ (1, 1) ], 0) ];
    }
  in
  check "ne/snap_cite: brute force agrees the instance is UNSAT" (brute_force m = None);
  let store = build_store m in
  let obs = new_obs () in
  let encoding, engine = build m store obs ~deep:true in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "ne/snap_cite (D-0019)" ] encoding oc;
  close_out oc;
  let oc = open_out pbp in
  let writer = Writer.create ~audit:true oc in
  Encoding.start_proof encoding writer;
  let ctx =
    Justify.create ~writer ~encoding ~model_id:(fun () -> failwith "ne/snap_cite")
  in
  let outcome = Search.solve ~engine ~store ~ctx ~check:(fun _ -> true) () in
  close_out oc;
  check "ne/snap_cite: the solver refutes it at the root, with no decision made"
    (outcome = Search.Unsat && not (opens_level 1 (read_file pbp)));
  (* The instance is only the instance we think it is if an int_ne Clause really did
     end up inside a `pol`. Asserting that separately means a change that stopped
     reaching the bug cannot make the test below pass for the wrong reason. *)
  check
    "ne/snap_cite: an int_ne Clause really is folded into a pol (the instance reaches \
     the bug)"
    obs.clause_in_pol;
  let proof = read_file pbp in
  (match run_veripb ~dir ~opb proof with
  | None -> fail "ne/snap_cite: veripb not found -- nothing was checked"
  | Some ok ->
      if ok then
        check "ne/snap_cite: veripb accepts the proof (the D-0019 gap is closed)" true
      else (
        incr checks;
        incr failures;
        print_endline
          "FAIL ne/snap_cite: KNOWN BUG, not fixed. int_lin_le's Snap_cite path folds an \
           int_ne Clause into a `pol` as if it were a chain-sum over the declared range, \
           and the resulting constraint is not a contradiction, so veripb rejects the \
           refutation. Reported by agent-ne, recorded in D-0019's last consequence, \
           reachable only at a root conflict. This is a finding about \
           lib/core/prop/linear.ml, not about this test: do not weaken it.";
        print_endline "     the model:";
        List.iter (fun l -> print_endline ("       " ^ l)) (lines_of (read_file opb));
        print_endline "     the proof:";
        List.iter (fun l -> print_endline ("       " ^ l)) (lines_of proof)));
  List.iter (fun f -> try Sys.remove f with _ -> ()) [ opb; pbp ];
  try Sys.rmdir dir with _ -> ()

(* ====================================== the int_ne root-conflict gap *)

(* A THIRD finding, also new, found by test_random.ml rather than by reasoning -- two
   independent seeds hit it inside fifty cases.

   search.ml's root arm says, and D-0013 agrees:

     "with no decision active there is nothing to negate, and the propagator's own
      derivation *is* the contradiction"

   and [Search.solve] then emits `conclusion UNSAT` citing the id it got back. That is
   true for [int_lin_le], whose slack < 0 derivation is a `pol` closing at `0 >= k`. It
   is false for a disequality: [Ne]'s conflict explanation is a [Clause] saying "not all
   of these variables take these values at once", which is a perfectly good constraint
   and is NOT a contradiction. veripb says so in as many words -- "Constraint is not a
   contradiction".

   What is missing is the same thing D-0018 supplies everywhere else: the bound facts
   that fix each variable to the value the clause forbids. Under a decision they are
   there, because [Trace.emit] runs before the nogood; at the root [Search.dfs] takes
   the `decisions = []` arm, which writes no trace at all, so the clause stands alone.

   The instance: x and y both declared 1..2 and both pinned to 1 by their own rows, then
   x <> y. Two rows, one disequality, no decision. *)
let known_bug_ne_root_conflict () =
  let dir = Filename.temp_file "baguette_neroot" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  let opb = Filename.concat dir "r.opb" and pbp = Filename.concat dir "r.pbp" in
  let m =
    {
      vars = [| ("x", 1, 2); ("y", 1, 2) |];
      cstrs = [ Ne (0, 1); Lin_le ([ (1, 0) ], 1); Lin_le ([ (1, 1) ], 1) ];
    }
  in
  check "ne/root-conflict: brute force agrees the instance is UNSAT" (brute_force m = None);
  let store = build_store m in
  let obs = new_obs () in
  let encoding, engine = build m store obs ~deep:true in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "ne/root-conflict" ] encoding oc;
  close_out oc;
  let oc = open_out pbp in
  let writer = Writer.create ~audit:true oc in
  Encoding.start_proof encoding writer;
  let ctx =
    Justify.create ~writer ~encoding ~model_id:(fun () -> failwith "ne/root-conflict")
  in
  let outcome = Search.solve ~engine ~store ~ctx ~check:(fun _ -> true) () in
  close_out oc;
  let proof = read_file pbp in
  check "ne/root-conflict: the solver refutes it with no decision made"
    (outcome = Search.Unsat && not (opens_level 1 proof));
  check
    "ne/root-conflict: the contradiction the conclusion cites is int_ne's own clause \
     (the instance reaches the gap)"
    (obs.ne_conflict && contains "rup +1 x_ge_2 +1 y_ge_2 >= 1 ;" proof);
  (match run_veripb ~dir ~opb proof with
  | None -> fail "ne/root-conflict: veripb not found -- nothing was checked"
  | Some true ->
      check "ne/root-conflict: veripb accepts the proof (the gap is closed)" true
  | Some false ->
      incr checks;
      incr failures;
      print_endline
        "FAIL ne/root-conflict: NEW BUG, not previously reported. A disequality that \
         conflicts with NO decision on the stack has its Clause emitted and then cited \
         by `conclusion UNSAT` as if it were a contradiction. It is not: a clause saying \
         \"not all of these values at once\" needs the bound facts that fix each \
         variable to that value, and search.ml's decisions = [] arm writes no trace, so \
         they are absent. Under a decision the same conflict verifies, because \
         Trace.emit runs first. This is a finding about lib/core/search.ml's root arm \
         (and D-0013's \"the propagator's own derivation IS the contradiction\", which \
         holds for int_lin_le and not for int_ne), not about this test: do not weaken \
         it.";
      Printf.printf "     veripb said: %s\n     the proof:\n%s\n"
        (String.trim !last_veripb_log)
        (String.concat "\n" (List.map (fun l -> "       " ^ l) (lines_of proof))));
  List.iter (fun f -> try Sys.remove f with _ -> ()) [ opb; pbp ];
  try Sys.rmdir dir with _ -> ()

(* ============================================ the int_ne trace-facts gap *)

(* A SECOND finding, not previously reported, in the same family as the one above and
   found by this matrix rather than by reasoning.

   D-0018/D-0021 require every pruning to get a trace line stating the order literal it
   established disjoined with the negation of the bound facts its propagator read.
   [Store] carries those facts on the trail entry, and the only functions that accept
   them are [set_lo_with_facts] and [set_hi_with_facts]. [Store]'s own comment says
   why there is no [remove] variant:

     "There is no [remove]/[fix] variant yet because M1 is bounds-only (docs/SPEC.md
      3.2) and nothing punches a hole"

   That premise stopped being true when M1-T9 landed [int_ne] in the same round, and
   [Ne.propagate] prunes with [Store.remove], which records [no_facts]. Removing a value
   at [lo] or [hi] shrinks the interval (D-0019's own last consequence says so), so such
   a pruning DOES move a bound, [Trace] does give it a line -- and the line comes out
   with an empty reason:

       rup +1 y_ge_2 >= 1 ;

   which claims the bound unconditionally. It is false, and veripb rejects it.

   Why nothing caught it. [Trace.emit] only ever runs when a branch FAILS, so the line
   is written only if a disequality prunes a bound inside a branch that then fails.
   test_prop.ml's [build_ne_search] is the nearest existing test and its search never
   fails a branch -- the same "the instance could not see the thing break" shape as
   D-0009, D-0010, D-0012, D-0017 and D-0021, and the sixth time in this project.

   The instance: y <= x, x + y >= 3, x <> y over 0..2. Root propagation gives x >= 1 and
   y >= 1; the search decides x <= 1, int_ne then removes 1 from y and pushes lo(y) to 2,
   and y <= x refutes the branch. The solution x = 2, y = 1 is found on the second
   branch, so the model is satisfiable and the factless line is not merely unprovable in
   this proof -- it is false in the model. *)
let known_bug_ne_trace_facts () =
  let dir = Filename.temp_file "baguette_nefacts" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  let opb = Filename.concat dir "b.opb" and pbp = Filename.concat dir "b.pbp" in
  let m =
    {
      vars = [| ("x", 0, 2); ("y", 0, 2) |];
      cstrs = [ Ne (0, 1); Le (1, 0); Lin_le ([ (-1, 0); (-1, 1) ], -3) ];
    }
  in
  check "ne/trace-facts: brute force says the model is satisfiable (x = 2, y = 1)"
    (brute_force m = Some [| 2; 1 |]);
  let store = build_store m in
  let obs = new_obs () in
  let encoding, engine = build m store obs ~deep:true in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "ne/trace-facts (D-0018 + M1-T9)" ] encoding oc;
  close_out oc;
  let n_model = Encoding.n_constraints encoding in
  let oc = open_out pbp in
  let writer = Writer.create ~audit:true oc in
  Encoding.start_proof encoding writer;
  let ctx =
    Justify.create ~writer ~encoding ~model_id:(fun () -> failwith "ne/trace-facts")
  in
  let trace = Trace.create () in
  let outcome = Search.solve ~engine ~store ~ctx ~check:(independent_check m) ~trace () in
  close_out oc;
  let proof = read_file pbp in
  check
    "ne/trace-facts: the solver answers SAT, so every trace line it wrote is a \
     claim          about a model that HAS solutions"
    (match outcome with Search.Sat _ -> true | Search.Unsat -> false);
  (* The instance is only the instance we think it is if a branch really failed after
     int_ne moved a bound. Asserted separately, so that a change which stops reaching
     the bug cannot make the check below pass for the wrong reason. *)
  check
    "ne/trace-facts: a branch failed, so the trace was written (this is what      \
     test_prop.ml's ne_search cannot reach)"
    (Trace.emitted_ids trace <> []);
  (* M1-T17 inverted this check. It used to assert the BUG's bytes -- that the
     factless line `rup +1 y_ge_2 >= 1 ;` was present -- which pinned the symptom
     rather than the situation, so fixing the bug turned it red. The instance has
     exactly one solution, x = 2 and y = 1, so `y >= 2` is false in the model: that
     line can never be both present and correct.

     What replaces it is strictly stronger, and still byte-for-byte. It names the
     line the same pruning must now write, which asserts the situation (int_ne moved
     y's lower bound, citing x fixed to 1) and the content (the facts are there and
     are the right ones) in one check, with no probe flag needed. The absence of the
     old form is asserted alongside it, so a regression to a factless line is caught
     even if some other line happens to satisfy the positive check. *)
  check
    "ne/trace-facts: the bound-moving disequality line carries its facts, byte for byte"
    (contains "rup +1 y_ge_2 +1 ~y_ge_1 +1 ~x_ge_1 +1 x_ge_2 >= 1 ;" proof);
  check "ne/trace-facts: and the factless form is gone (it was false in this model)"
    (not (contains "rup +1 y_ge_2 >= 1 ;" proof));
  let trace_ids = Trace.emitted_ids trace in
  let bad =
    List.filter
      (fun (id, _, line) ->
        List.mem id trace_ids && standalone ~dir ~opb ~n_model line = Some false)
      (numbered_rules ~n_model proof)
  in
  (match bad with
  | [] ->
      check "ne/trace-facts: every trace line verifies standalone -- the gap is closed"
        true
  | _ ->
      incr checks;
      incr failures;
      print_endline
        "FAIL ne/trace-facts: NEW BUG, not previously reported. int_ne prunes through \
         Store.remove, which records no_facts, so the D-0018 trace line for a \
         disequality pruning that moves a bound states the bound with an EMPTY reason -- \
         an unconditional claim that is simply false. Store has set_lo_with_facts and \
         set_hi_with_facts and no remove_with_facts; store.ml's comment justifies that \
         with \"M1 is bounds-only ... nothing punches a hole\", which M1-T9's int_ne \
         made untrue in the same round. This is a finding about lib/core/prop/ne.ml + \
         lib/core/store.ml, not about this test: do not weaken it.";
      List.iter
        (fun (id, lvl, line) ->
          Printf.printf "     id %d at level %d does not follow from the model: %s\n" id
            lvl line)
        bad);
  (match run_veripb ~dir ~opb proof with
  | None -> fail "ne/trace-facts: veripb not found -- nothing was checked"
  | Some ok ->
      if ok then check "ne/trace-facts: veripb accepts the proof (the gap is closed)" true
      else (
        incr checks;
        incr failures;
        Printf.printf
          "FAIL ne/trace-facts: veripb rejects the proof, as it must -- %s\n\
          \     the model:\n\
           %s\n\
          \     the proof:\n\
           %s\n"
          (String.trim !last_veripb_log)
          (String.concat "\n"
             (List.map (fun l -> "       " ^ l) (lines_of (read_file opb))))
          (String.concat "\n" (List.map (fun l -> "       " ^ l) (lines_of proof)))));
  List.iter (fun f -> try Sys.remove f with _ -> ()) [ opb; pbp ];
  try Sys.rmdir dir with _ -> ()

(* ====================================================== white-box cells *)

(* Two cells leave no mark on the emitted text and are asserted against the propagator
   directly: one row mixing a declared bound (Weaken) with a derived one (Snap_cite),
   and the cross-row conflict's own derivation shape (D-0013 step 5).

   The second of those turned out not to be reachable the way linear.ml's header
   describes it. See [cross_row_is_unreachable_across_instances] for the measurement
   and the argument. *)

(* One row that has to weaken one term and cite another in the same snapshot: [v] has
   been moved off its declared lo by a different instance, [u] is still at its declared
   lo, and the push is on [w]. A two-term row cannot produce this -- there is only one
   "other" term and it is one thing or the other -- which is why the instance has
   three. *)
let weaken_and_cite_cell () =
  let store =
    Store.create ~names:[| "v"; "w"; "u" |]
      ~domains:[| Domain.make 0 9; Domain.make 0 9; Domain.make 0 9 |]
  in
  let v = Var.of_int 0 and w = Var.of_int 1 and u = Var.of_int 2 in
  let obs = new_obs () in
  let mover = Linear.make ~row_id:1 store [ (-1, v) ] (-3) in
  let row = Linear.make ~row_id:2 store [ (2, v); (3, w); (4, u) ] 20 in
  let engine =
    Engine.create
      [ pack_linear ~id:0 obs ~deep:true mover; pack_linear ~id:1 obs ~deep:true row ]
  in
  ignore (Engine.propagate engine store);
  check
    "white-box/weaken+cite: one row weakens a declared bound and cites a derived one in \
     the same snapshot"
    obs.weaken_and_cite;
  check "white-box/weaken+cite: the push divides by more than one (|a| > 1)"
    obs.div_nontrivial;
  check "white-box/weaken+cite: the division has a remainder, so the rounding matters"
    obs.div_remainder;
  check "white-box/weaken+cite: the bound cited was derived by a different instance"
    obs.cross_instance_cite;
  [ D_weaken_and_cite; D_cross_instance_cite; D_big_coeff; D_division_remainder ]

(* The cell the task asks for is "this row's new bound contradicts a bound another
   instance established". It cannot happen, and the reason is arithmetic rather than a
   gap in the instances tried.

   [Linear.propagate] computes [slack = rhs - sum_i min(a_i x_i)] ONCE, from the bounds
   as they stand when the call begins, and the engine runs one propagator at a time, so
   no other instance can move a bound between that computation and the pushes that
   follow. For a term with [a > 0] the push is
       new_hi = floor((a * lo + slack) / a) = lo + floor(slack / a)
   which is [>= lo] for every [slack >= 0], and symmetrically [new_lo <= hi] for
   [a < 0]. So a push can only land outside the variable's current interval when
   [slack < 0] -- and that is tested first and reported as the row's own slack conflict.

   This is measured below as well as argued: the instance is the one that looks most
   like a cross-row clash (t >= 4 and z >= 1 established by two other instances, then
   z + t <= 3), and it produces a plain slack conflict.

   What *does* reach [Linear]'s cross-conflict path is a row that mentions the same
   variable twice with opposite signs: the first push moves that variable, which makes
   the second term's cached [min] stale, and the second push can then contradict it.
   That is a legitimate row -- [Ne] and [Linear] both document that a variable may
   appear more than once, and lib/flatzinc/compile.ml only merges duplicates for rows
   it posts itself -- so the code is not dead, but it is reached from inside one
   instance rather than across two, which is not what linear.ml's header says. *)
let cross_row_cell () =
  (* First: the shape that looks like a cross-row clash really is a slack conflict. *)
  let store =
    Store.create ~names:[| "z"; "t" |] ~domains:[| Domain.make 0 6; Domain.make 0 6 |]
  in
  let z = Var.of_int 0 and t = Var.of_int 1 in
  let obs = new_obs () in
  let engine =
    Engine.create
      [
        pack_linear ~id:0 obs ~deep:true (Linear.make ~row_id:1 store [ (-1, t) ] (-4));
        pack_linear ~id:1 obs ~deep:true (Linear.make ~row_id:2 store [ (-1, z) ] (-1));
        pack_linear ~id:2 obs ~deep:true
          (Linear.make ~row_id:3 store [ (1, z); (1, t) ] 3);
      ]
  in
  (match Engine.propagate engine store with
  | Engine.Conflict _ -> ()
  | Engine.Fixpoint -> fail "white-box/cross-row: the instance does not conflict at all");
  check
    "white-box/cross-row: two instances' bounds meeting in a third row is reported as \
     that row's own slack, never as a cross-row conflict -- the cell as stated is \
     unreachable, see the comment above"
    (obs.slack_conflict && not obs.cross_conflict);
  (* Second: the route that does reach the path, and its proof. *)
  let dir = Filename.temp_file "baguette_cross" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  let opb = Filename.concat dir "c.opb" and pbp = Filename.concat dir "c.pbp" in
  let e = Encoding.create () in
  Encoding.declare_int e "d" ~lo:0 ~hi:6;
  let row = Encoding.add_int_lin_le e [ (2, "d"); (-1, "d") ] (-4) in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "white-box/cross-row: 2d - d <= -4" ] e oc;
  close_out oc;
  let store = Store.create ~names:[| "d" |] ~domains:[| Domain.make 0 6 |] in
  let d = Var.of_int 0 in
  let obs2 = new_obs () in
  let engine =
    Engine.create
      [
        pack_linear ~id:0 obs2 ~deep:true
          (Linear.make ~row_id:row store [ (2, d); (-1, d) ] (-4));
      ]
  in
  let oc = open_out pbp in
  let w = Writer.create ~audit:true oc in
  Encoding.start_proof e w;
  let ctx = Justify.create ~writer:w ~encoding:e ~model_id:(fun () -> row) in
  let outcome = Search.solve ~engine ~store ~ctx ~check:(fun _ -> true) () in
  close_out oc;
  check "white-box/cross-row: the duplicate-variable row is refuted"
    (outcome = Search.Unsat);
  check
    "white-box/cross-row: and it is refuted through D-0013 step 5, the two-summand \
     divisor-1 Combine -- the only route that reaches Linear's cross-conflict path"
    obs2.cross_conflict;
  (match run_veripb ~dir ~opb (read_file pbp) with
  | None -> fail "white-box/cross-row: veripb not found -- nothing was checked"
  | Some ok ->
      check "white-box/cross-row: veripb accepts the cross-conflict derivation (I-X1)" ok;
      if not ok then
        Printf.printf "  veripb said:\n%s\n  model:\n%s\n  proof:\n%s\n" !last_veripb_log
          (read_file opb) (read_file pbp));
  List.iter (fun f -> try Sys.remove f with _ -> ()) [ opb; pbp ];
  (try Sys.rmdir dir with _ -> ());
  [ D_neg_coeff; D_big_coeff ]

let white_box_cells () =
  let s1 = weaken_and_cite_cell () in
  let s2 = cross_row_cell () in
  List.iter (fun d -> Hashtbl.replace covered_shapes d ()) (s1 @ s2);
  List.iter
    (fun d ->
      Hashtbl.replace cells_pd (P_lin_le, d) ();
      Hashtbl.replace cells_sd (S_cross_row_conflict, d) ())
    s2;
  List.iter (fun d -> Hashtbl.replace cells_pd (P_lin_le, d) ()) s1;
  Hashtbl.replace covered_situations S_cross_row_conflict ();
  Hashtbl.replace cells_ps (P_lin_le, S_cross_row_conflict) ()

(* ========================================== the overflow axis's own cells (M1-T23)

   Three of the five [overflow] values cannot be an instance in [instances], and the
   reason is the point of the task rather than an inconvenience:

   - [O_product] and [O_sum] are what a propagator does when the arithmetic leaves the
     63-bit range, and the policy (lib/core/checked.ml) is that it RAISES. A raising
     propagator has no answer to compare against brute force and no proof to hand
     veripb, so [run_instance] cannot host it. It is asserted directly instead.

   - [O_compile_rejected] is a model that never reaches a propagator at all. Its
     column in the propagator grid is therefore empty for every propagator, on purpose:
     crediting a propagator for a model that was refused before any instance was built
     would record something no propagator did, which is the rule the empty-cell note
     below already applies to the int_lt and int_ne rows.

   **A ceiling, and why it is a rule rather than a preference.** No instance and no
   cell in this file declares a domain more than a few values wide -- the three
   near-limit instances above sit at 1.44 * 10^17 with a declared WIDTH of one, and
   the cells below reach overflow through coefficients and through a bound fixed at
   min_int (width zero). docs/DECISIONS.md **D-0028** measures why: a justification is
   Theta(declared width) per other term per pruning, so two variables declared
   0..999999 produce a 156 MB .opb and one 29.8 MB `pol` line having pruned nothing.
   Overflow is the area where "declare a domain near max_int" is the tempting test,
   and that test cannot be run in this project today. Drive it through the
   coefficient, which is where the wrapped product comes from anyway.

   Each cell below also pins WHAT WOULD HAVE HAPPENED, not merely that something
   raised. Before M1-T23 the first cell's [Linear.propagate] returned a [Conflict] on a
   row that is satisfied by every value in the domain, because -2^61 * 4 wraps to 0 and
   -2^61 * 3 wraps to +2^61; the checks below state those two products, so the cell
   says why it exists and not only that the guard is present. *)

let raises_overflow f =
  try
    ignore (f ());
    false
  with Checked.Overflow _ -> true

let overflow_product_cells () =
  (* The demonstrating row, built directly -- which is the one caller the compile-time
     cap does not cover, and the reason the runtime policy is to raise. *)
  let store = build_store { vars = [| ("x", 3, 4) |]; cstrs = [] } in
  let lin = Linear.make ~row_id:1 store [ (-2305843009213693952, Var.of_int 0) ] 0 in
  check
    "overflow/product: -2^61 * 3 really does wrap to a POSITIVE number, which is what \
     made the old slack argue for a conflict"
    (-2305843009213693952 * 3 = 2305843009213693952);
  check
    "overflow/product: int_lin_le raises rather than conflicting on a row every value \
     satisfies"
    (raises_overflow (fun () -> Linear.propagate lin store));
  (* int_ne's coefficients are 1 and -1 by construction, so its one overflowing product
     is the negation of a fixed value at min_int -- which is also the one input
     Stdlib.mod is not guaranteed to survive, further down the same function. *)
  let s2 =
    build_store { vars = [| ("u", 0, 2); ("v", min_int, min_int) |]; cstrs = [] }
  in
  let ne = Ne.Int_ne.make s2 (Var.of_int 0) (Var.of_int 1) in
  check "overflow/product: int_ne raises on the negation of a fixed min_int"
    (raises_overflow (fun () -> Ne.propagate ne s2));
  (* int_lin_ne reaches the same cell the ordinary way, through a coefficient. *)
  let s3 = build_store { vars = [| ("a", 4, 4); ("b", 0, 3) |]; cstrs = [] } in
  let lne = Ne.make s3 [ (-2305843009213693952, Var.of_int 0); (1, Var.of_int 1) ] 0 in
  check "overflow/product: int_lin_ne raises on a coefficient times a fixed value"
    (raises_overflow (fun () -> Ne.propagate lne s3));
  [ (P_lin_le, O_product); (P_ne, O_product); (P_lin_ne, O_product) ]

let overflow_sum_cells () =
  (* Every product fits; the running total does not. A per-product check alone would
     miss this, and a per-product check is the obvious thing to write. *)
  let big = (max_int / 2) + 1 in
  let m = { vars = [| ("a", big, big); ("b", big, big); ("c", 0, 1) |]; cstrs = [] } in
  let store = build_store m in
  let lin =
    Linear.make ~row_id:1 store
      [ (1, Var.of_int 0); (1, Var.of_int 1); (1, Var.of_int 2) ]
      0
  in
  check "overflow/sum: each product fits -- it is their total that does not"
    (Checked.mul 1 big = big && raises_overflow (fun () -> Checked.add big big));
  check "overflow/sum: int_lin_le raises on the fold of the minima"
    (raises_overflow (fun () -> Linear.propagate lin store));
  let s2 = build_store m in
  let lne = Ne.make s2 [ (1, Var.of_int 0); (1, Var.of_int 1); (1, Var.of_int 2) ] 0 in
  check "overflow/sum: int_lin_ne raises on the fixed terms' sum"
    (raises_overflow (fun () -> Ne.propagate lne s2));
  [ (P_lin_le, O_sum); (P_lin_ne, O_sum) ]

(* The model that demonstrated the gap, end to end through the front end. Before
   M1-T23 this model printed =====UNSATISFIABLE===== and emitted a .pbp that veripb
   accepted, on a model x = 3 satisfies. It is refused now, and the refusal is checked
   on its CONTENT: a rejection that does not say what the limit is, is not the
   diagnostic SPEC 2.1's standard for a rejection asks for. *)
let overflow_compile_cell () =
  let src =
    "array [1..1] of int: c = [-2305843009213693952];\n\
     var 3..4: x;\n\
     constraint int_lin_le(c, [x], 0);\n\
     constraint int_le(x, 3);\n\
     solve satisfy;\n"
  in
  (match Flatzinc.Compile.compile (Flatzinc.Builder.of_string ~file:"overflow" src) with
  | exception Flatzinc.Error.Error e ->
      let msg = Flatzinc.Error.to_string e in
      check "overflow/compile: the demonstrating model is refused" true;
      check "overflow/compile: the refusal states the limit and why it exists"
        (contains "arithmetic limit" msg
        && contains "288230376151711743" msg
        && contains "wraps silently" msg);
      if not (contains "arithmetic limit" msg) then Printf.printf "  message: %s\n" msg
  | exception exn ->
      fail "overflow/compile: raised the wrong exception: %s" (Printexc.to_string exn)
  | _ ->
      fail
        "overflow/compile: the model COMPILED. This is the M1-T23 gap: x = 3 satisfies \
         it, and the solver used to answer UNSAT with a proof veripb accepted");
  [ O_compile_rejected ]

let overflow_cells () =
  let cells = overflow_product_cells () @ overflow_sum_cells () in
  List.iter
    (fun (p, o) ->
      Hashtbl.replace cells_po (p, o) ();
      Hashtbl.replace covered_overflows o ())
    cells;
  List.iter (fun o -> Hashtbl.replace covered_overflows o ()) (overflow_compile_cell ())

(* ================================================================= main *)

let () =
  print_endline "\nthe case matrix (M1-T16)";
  (match veripb with
  | None ->
      print_endline
        "  (veripb is not on PATH and not at ~/.local/bin/veripb -- every I-X1 check \
         below will FAIL, which is the intended behaviour: see docs/INVARIANTS.md.)"
  | Some _ -> ());
  List.iter
    (fun inst ->
      Printf.printf "\n* %s\n  %s\n" inst.title inst.note;
      let r = run_instance inst in
      record_coverage inst r)
    instances;
  print_endline "";
  white_box_cells ();
  print_endline "";
  overflow_cells ();
  print_endline "";
  known_bug_ne_snap_cite ();
  print_endline "";
  known_bug_ne_trace_facts ();
  print_endline "";
  known_bug_ne_root_conflict ();
  report_matrix ();
  Printf.printf "\n%d matrix checks" !checks;
  if !failures > 0 then (
    Printf.printf ", %d failure(s)\n" !failures;
    exit 1)
  else print_endline ", all passed"
