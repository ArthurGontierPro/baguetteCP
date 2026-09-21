(* The reification dispatcher (roadmap M3-T4).

   A reified constraint is  b <-> C  for a Boolean [b] (the *reifier*, an ordinary
   order-encoded bool -- D-0007, and docs/DECISIONS.md D-0053 says reification
   introduces no new naming scheme) and a condition [C] over integer variables. Written
   out as propagation rules it is five cases:

     1. [b] is true                  -> enforce C
     2. [b] is false                 -> enforce ~C
     3. C is entailed by the domains -> [b] is true
     4. C is refuted by the domains  -> [b] is false
     5. none of the above            -> nothing

   M3-T2 has to do this for a linear inequality *and* for a linear equality, and
   M3-T4 exists so that is two authors and not ten cases. **An author supplies three
   pieces** -- enforce-hold, enforce-not-hold, entailment -- **and this module supplies
   the collapse and the contrapositive**:

     - the COLLAPSE is [propagate] below: it reads the reifier once and runs *at most
       one* of the three. Cases 1 and 2 are the two enforcement pieces; cases 3, 4 and
       5 are the entailment piece, which is the only one that may move the reifier.
     - the CONTRAPOSITIVE is the pairing: case 3 is the contrapositive of case 2 (if
       [b] were false we would be enforcing ~C, which the domains already refute) and
       case 4 of case 1. An author never writes either contrapositive; it writes the
       forward form and gets the reverse one from the position its piece sits in here.

   [r_positive] carries the one further collapse M3-T2 needs. `int_ne_reif` is
   `int_eq_reif` with the reifier's meaning inverted, so rather than a second author
   the dispatcher holds the POLARITY of the reification literal: [true] means the
   condition holds when [b] = 1, [false] that it holds when [b] = 0. Nothing else in
   this file, and nothing in either author, mentions the difference.

   ---------------------------------------------------------------------------
   What the three pieces are allowed to be, and why they are closures
   ---------------------------------------------------------------------------

   An author's three pieces are [Store.t -> Propagator.result], which is the signature
   of [Propagator.propagate] itself. That is deliberate and it is the whole economy of
   this design: **the overwhelmingly common author piece is an existing propagator over
   an existing row**, not new code. lib/core/prop/reif_lin_le.ml's enforce-hold is
   [Linear.propagate] over the big-M row `sum a x + K b <= rhs + K`; its
   enforce-not-hold is [Linear.propagate] over the other one. Neither re-implements
   bounds propagation and neither hand-builds a [pol]: they inherit [Linear]'s D-0013
   [Combine], which is the justification this reification needs, because the big-M row
   IS the reification row the .opb carries (lib/proof/encoding.ml,
   [add_int_lin_le_reif_rows]).

   The dispatch is therefore not redundant with the rows, and it is worth being precise
   about why, since "just register both rows as two ordinary propagators" is the obvious
   alternative. It would be *correct*: at b unfixed neither big-M row can prune a
   condition variable, so running them unconditionally prunes exactly the same values.
   What it would lose is the five cases as a THING IN THE CODE -- there would be no
   place where case 3 and case 2 are visibly the same fact read in two directions, no
   place for an author that is not two rows, and no [r_positive]. The equality author
   (lib/core/prop/reif_lin_eq.ml) is exactly such an author: its enforce-not-hold is a
   value-consistent disequality pass whose explanation is a [Clause], not a [pol] over a
   cited row, and its entailment piece pushes the reifier from a nogood. A dispatcher
   that only knew how to run rows could not hold it.

   ---------------------------------------------------------------------------
   Consistency, attribution, and the PB row
   ---------------------------------------------------------------------------

   This module declares NO consistency level, because it has no propagation of its own
   to declare one for: the level is the author's, stated in the author's own header, and
   each named face below the authors export carries it (SPEC 3.2 requires the level to
   be documented per propagator, and a dispatcher that declared one would be declaring
   something about code it does not contain).

   ATTRIBUTION. A sub-propagator called from here changes domains through the ordinary
   [Store] mutators, which stamp whoever [Engine] said was running -- that is this
   dispatcher's instance, not the inner [Linear]'s, because the inner one was never
   registered with the engine and has no id. That is the right answer and not an
   accident of the mechanism: the model wrote `int_le_reif`, so a trace line or an
   attribution failure should say `int_le_reif` (the [Ne] / [Ne.Int_ne] rule, and
   lib/core/prop/clause.ml's five faces of one propagator). Nothing here calls
   [Store.with_running].

   NO PB ROW. [Propagator.pb_row] is left at its default [None] (D-0054): an instance
   here stands for TWO rows at least, and a [pb_row] is a promise to reproduce exactly
   one. lib/flatzinc/compile.ml therefore packs these without [~row:], and M2-L6 falls
   back to the clause path for a conflict this instance reports -- which is what
   [Search]'s fallback rate counts, and is the same answer [Ne] gives for the same
   reason. The rows are not thereby uncitable: each inner [Linear.t] names its own with
   [Explanation.Model_row], so every [pol] this instance's prunings emit is still
   anchored to a row the .opb actually contains.

   IDEMPOTENCE AT THE INTERFACE (I-P3). [propagate] re-dispatches once if the
   entailment piece has just fixed the reifier -- and only then. That is bounded by
   construction: the reifier is a bool, so it can be fixed at most once, and the second
   pass takes an enforcement branch which cannot move it again.

   For BOTH authors shipped today the second pass provably prunes nothing, and it is
   worth saying so rather than leaving the re-dispatch looking load-bearing. Case 3
   fires because the current domains already entail the condition, so enforce-hold has
   nothing left to take away from them; case 4 fires because they already refute it, so
   enforce-not-hold has nothing either -- and the equality author's case 3 is stronger
   still, firing only with every condition variable fixed. The re-dispatch is a guard
   for a future author whose entailment test is cheaper than its enforcement, not a
   path this suite exercises; even without it nothing would be lost but a queue
   round-trip, since the reifier is in [vars] and the engine re-wakes on it. *)

module Domain = Domain
module Store = Store

type t = {
  r_b : Var.t;
      (* The reifier. [Compile] has already checked it is a `var bool`; [make] checks
         again, for the hand-built callers every unit test is. *)
  r_positive : bool;
  r_vars : Var.t list; (* the condition's variables, without the reifier *)
  r_hold : Store.t -> Propagator.result;
  r_not_hold : Store.t -> Propagator.result;
  r_entail : Store.t -> Propagator.result;
}

let make ~reifier ~positive ~vars ~hold ~not_hold ~entail store =
  let d = Store.get store reifier in
  if Domain.lo d <> 0 || Domain.hi d <> 1 then
    invalid_arg
      (Printf.sprintf
         "Reif.make: `%s` is declared over %s, but a reifier must be a `var bool`, i.e. \
          the order encoding on [0, 1] (docs/DECISIONS.md D-0007)."
         (Store.name store reifier)
         (Domain.to_string d));
  {
    r_b = reifier;
    r_positive = positive;
    r_vars = vars;
    r_hold = hold;
    r_not_hold = not_hold;
    r_entail = entail;
  }

(* The reifier first: it is the variable the engine will most often have just moved. *)
let vars t = t.r_b :: t.r_vars

let propagate t store =
  (* [Some true] / [Some false] once the reification literal is decided, [None] while
     it is open. This is the only place [r_positive] is read. *)
  let decided () =
    match Domain.value (Store.get store t.r_b) with
    | None -> None
    | Some v -> Some (v = 1 = t.r_positive)
  in
  let rec go again =
    match decided () with
    | Some true -> t.r_hold store
    | Some false -> t.r_not_hold store
    | None -> (
        match t.r_entail store with
        | Propagator.Conflict c -> Propagator.Conflict c
        | Propagator.Fixpoint ->
            (* The contrapositive just landed: the entailment piece decided the
               reifier, so the matching enforcement piece has not run yet. *)
            if again && Option.is_some (decided ()) then go false
            else Propagator.Fixpoint)
  in
  go true
