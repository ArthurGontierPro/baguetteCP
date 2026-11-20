(* activity.ml: the ACTIVITY heuristic over integer variables -- conflict-driven variable
   selection in the VSIDS family (M10-search-strategy-T3, docs/DECISIONS.md D-0137
   section 4).

   Consistency level: none -- this is not a propagator. Governing records: D-0137 section
   4 (what is scored, what is bumped, the decay, the tie-break), section 1.1 (the trail
   reuse rule it answers for partial restarts); docs/SPEC.md 3.4 (opt-in:
   `--search activity` / `--search alternate`).

   ---------------------------------------------------------------------------
   What is scored, and why the variable and not the literal
   ---------------------------------------------------------------------------

   One float per store VARIABLE (Boolean or integer). A decision in this solver picks a
   variable, then a value, and the order literal follows from the pair (lib/core/search.ml,
   [type decision]); scoring literals would score something the search never chooses
   directly. Chuffed scores the Boolean variables of its order encoding, which is the
   other reading and is recorded in D-0137 as the alternative.

   ---------------------------------------------------------------------------
   Bump, decay, select
   ---------------------------------------------------------------------------

   - BUMP ([bump_lits]): every variable named by the learned 1UIP clause, after
     minimisation, gets the current increment -- Chaff's VSIDS (Moskewicz et al., DAC
     2001). A conflict that learned nothing bumps the variables of its own reason facts
     instead ([bump_facts]), dom/wdeg's signal in its simplest form (Boussemart et al.,
     ECAI 2004), so a run with learning off still moves the scores.
   - DECAY ([decay]): after every conflict the increment grows by 1/[decay_factor]
     (EVSIDS, Een and Sorensson, SAT 2003), which ages every older bump at once; when a
     score passes [rescale_at] every score and the increment are divided by it. Division
     by one positive constant is monotone under IEEE rounding, so a rescale never
     reverses a comparison [select] makes; it can only merge two scores that were within
     rounding of each other, or round a tiny one to 0.
   - SELECT ([select]): the candidate with the highest score; ties broken by SPEC 3.4's
     first-fail rule (smallest live domain, then the earliest candidate). At the start of
     a solve every score is 0, so the activity order's first decisions ARE the default
     order's, and the two part company only as conflicts accumulate.

   The scan in [select] is linear in the candidates, as [Search.unfixed] already is per
   node. A binary heap keyed on the score is the optimisation if a profile ever shows
   the scan; it would have to be told about every fix and unfix, which the store does
   not report, and that is why it is not here. M16-file-review-T3 (D-0191) measured it:
   under `--search activity` it is 0.2 % of the median lane instance's samples and 13 %
   of 2011_roster's, whose thousands of candidates are tied at score 0 for most of the
   run, so every one is also asked its [Domain.size]. The heap is the lever there and it
   needs the store's events, so it stays a proposal (D-0191 section 5).

   ---------------------------------------------------------------------------
   Determinism
   ---------------------------------------------------------------------------

   Floats, but no hashing and no clock: the same conflicts bump the same variables in the
   same order, every operation is IEEE-deterministic on one machine, and two runs of one
   binary make the same decisions (scripts/check_determinism.sh). *)

module Lit = Baguette_proof.Lit

let decay_factor = 0.95
let rescale_at = 1e100

type t = {
  score : float array;
  mutable inc : float;
  mutable n_bumps : int; (* variable bumps over the run: read by --stats *)
  mutable n_rescales : int;
}

let create n_vars =
  { score = Array.make n_vars 0.0; inc = 1.0; n_bumps = 0; n_rescales = 0 }

let score t v = t.score.(Var.to_int v)

let rescale t =
  Array.iteri (fun i s -> t.score.(i) <- s /. rescale_at) t.score;
  t.inc <- t.inc /. rescale_at;
  t.n_rescales <- t.n_rescales + 1

let bump_index t i =
  if i >= 0 && i < Array.length t.score then (
    t.score.(i) <- t.score.(i) +. t.inc;
    t.n_bumps <- t.n_bumps + 1;
    if t.score.(i) > rescale_at then rescale t)

(* The variable an order literal is about, if the store knows it. A [Bit] literal never
   reaches here (lib/proof/lit.ml: nothing in core builds one), and a name the store does
   not know is skipped rather than guessed. *)
let var_of_lit store (l : Lit.t) =
  match l.Lit.v with
  | Lit.Ge (x, _) | Lit.Eq (x, _) | Lit.Bit (x, _) -> Store.var_named store x

(* Bump each variable ONCE per clause, however many of its literals the clause carries
   (minimisation leaves at most one per direction, so a variable can appear twice). *)
let bump_lits t store (lits : Lit.t list) =
  let seen = Hashtbl.create 8 in
  List.iter
    (fun l ->
      match var_of_lit store l with
      | Some v ->
          let i = Var.to_int v in
          if not (Hashtbl.mem seen i) then (
            Hashtbl.replace seen i ();
            bump_index t i)
      | None -> ())
    lits

let bump_facts t store (facts : Reason.fact list) =
  let seen = Hashtbl.create 8 in
  List.iter
    (fun f ->
      let name =
        match f with Reason.At_least { name; _ } | Reason.At_most { name; _ } -> name
      in
      match Store.var_named store name with
      | Some v ->
          let i = Var.to_int v in
          if not (Hashtbl.mem seen i) then (
            Hashtbl.replace seen i ();
            bump_index t i)
      | None -> ())
    facts

let decay t =
  t.inc <- t.inc /. decay_factor;
  if t.inc > rescale_at then rescale t

(* The candidate with the highest score, ties to the smallest live domain, then to the
   earliest. [cands] is non-empty (Search's contract for an order). *)
let select t store (cands : Var.t array) =
  let best = ref cands.(0) in
  let bs = ref (score t cands.(0)) in
  let bsize = ref (Domain.size (Store.get store cands.(0))) in
  for i = 1 to Array.length cands - 1 do
    let v = cands.(i) in
    let s = score t v in
    if s > !bs then (
      best := v;
      bs := s;
      bsize := Domain.size (Store.get store v))
    else if s = !bs then
      let size = Domain.size (Store.get store v) in
      if size < !bsize then (
        best := v;
        bsize := size)
  done;
  !best

(* The highest score among [cands], for the trail-reuse rule (D-0137 section 1.1);
   [neg_infinity] when there is none. *)
let best_score t (cands : Var.t array) =
  Array.fold_left (fun acc v -> Float.max acc (score t v)) Float.neg_infinity cands

let n_bumps t = t.n_bumps
let n_rescales t = t.n_rescales
