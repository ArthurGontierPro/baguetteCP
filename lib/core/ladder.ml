(* ladder.ml: THE ORDER-ENCODING LADDER CHAIN, AS A ROW (M2-L11).

   Consistency level: none -- this is not a propagator. Governing records:
   docs/DECISIONS.md D-0010 (a bound fact is stated in the order encoding's own
   currency), D-0028 (the ladder is eager and its implications are SEPARATE .opb rows),
   docs/INVARIANTS.md I-X6 (the falsified predicate is frozen at the propagation, and
   this module never reads a store) and I-X8 / D-0029 (coefficient growth must raise).

   ---------------------------------------------------------------------------
   The finding this module exists to answer -- M2-L6, measured
   ---------------------------------------------------------------------------

   OUR INTEGER PROPAGATOR IS STRONGER THAN PB PROPAGATION ON THE SAME ROW. That is
   lib/core/pb_analysis.ml's dominant non-[No_row] fallback and it is not a defect
   anywhere; it is a statement about where the strength lives. The worked case is
   [int_lin_le] doing its ordinary job:

     3a + 2b <= 14,  a, b declared 0..4,  and lo(b) = 4 already established.

   [Linear] deduces a <= 2. The row's PB form is

     3~[a>=1] + 3~[a>=2] + 3~[a>=3] + 3~[a>=4] + 2~[b>=1] + ... + 2~[b>=4] >= 6

   and with b at 4 every b term is falsified, leaving slack (3+3+3+3) - 6 = 6. The pivot
   ~[a>=3] has coefficient 3, and 3 > 6 is false: THE ROW ALONE DOES NOT PB-PROPAGATE
   IT. It cannot. The fact that ~[a>=1] entails ~[a>=3] is not in the row -- it is in the
   LADDER implications, which [Encoding.declare_int] writes as separate .opb rows
   (PROOF-FORMAT section 3):

     for lo < v < hi:   1 ~x_ge_(v+1)  1 x_ge_v  >= 1        i.e.  x >= v+1 -> x >= v

   So the true reason for the pruning is MODEL ROW + A LADDER CHAIN. [Order_reason]
   (lib/core/prop/order_reason.ml, D-0010) already builds exactly that chain as an
   [Explanation], which is why [Linear]'s own justification checks; what has never
   existed is the same chain AS A ROW, which is what PB conflict analysis resolves
   against. This module is that row, and nothing else.

   ---------------------------------------------------------------------------
   The step: one ladder row moves one term one rung, and the degree does not move
   ---------------------------------------------------------------------------

   Write the ladder row at value [w] as  L_w  =  [x>=w] + ~[x>=w+1] >= 1.

   Add [c * L_w] to a row carrying [c * ~[x>=w]]. The complementary pair
   [c ~[x>=w] + c [x>=w]] is the constant [c] (D-0044's [Learned.combine] stage 3 does
   this cancellation, and must: the checker normalises complements away when it reads a
   constraint, so a copy that did not would disagree with the checker's from the next
   line on). The constant moves across, so the degree goes [d + c - c = d], and what is
   left in its place is [c * ~[x>=w+1]]. That is a SUBSTITUTION of one rung for the next
   one up, at no cost in degree -- and it is sound for the obvious reason, which is that
   every step is the addition of a positive multiple of a row the .opb already contains.

   Iterating it from [v] up to [k] replaces [c * ~[x>=v]] by [c * ~[x>=k]] using the
   rows [L_v .. L_(k-1)]. The mirror case is a positive pivot: [c * [x>=v]] with [v > k]
   is lowered onto [c * [x>=k]] by [L_(v-1) .. L_k], because [L_w] carries [~[x>=w+1]]
   and cancels a positive [[x>=w+1]] the same way.

   On the worked case, with pivot ~[a>=3], the two liftable terms are ~[a>=1] and
   ~[a>=2] at coefficient 3 each, so the multipliers are 3 on L_1 and 3+3 = 6 on L_2:

     3a+2b<=14's row  +  3 L_1  +  6 L_2   =   9~[a>=3] + 3~[a>=4] + 2~[b>=*] >= 6

   whose slack under the same frozen assignment is (9 + 3) - 6 = 6 and whose pivot
   coefficient is now 9 > 6. It propagates, [Reduce] accepts it, and its reduction is
   the clause "a <= 2 or b <= 0 or b <= 1 or b <= 2 or b <= 3" -- which is the reason
   [Linear] actually used, now available to PB analysis as arithmetic.

   ---------------------------------------------------------------------------
   Only NON-FALSIFIED terms are lifted, and that is the whole of the heuristic
   ---------------------------------------------------------------------------

   Slack is the sum of the coefficients of the NOT-falsified terms, minus the degree, and
   what a reduction needs is [pivot coefficient > slack].

     - Lifting a NOT-falsified term of coefficient [c] onto the pivot leaves the slack
       exactly where it was (the [c] was already in the sum and still is, now under the
       pivot's literal) and raises the pivot's coefficient by [c]. Strictly better, every
       time.
     - Lifting a FALSIFIED term would add [c] to BOTH the slack and the pivot's
       coefficient. The difference the criterion reads is unchanged, and the absolute
       slack is larger, which is worse after the division rounds up. So a falsified term
       is left where it is, and the reduction keeps it as the ordinary falsified literal
       it is.

   This is a heuristic about which sound step to take, not a soundness argument; the
   soundness argument is one line and is above. A lift that turns out not to help is
   caught by [Reduce]'s own postcondition and falls back, exactly as before.

   ---------------------------------------------------------------------------
   What this module does NOT do
   ---------------------------------------------------------------------------

   It does not read a [Store]. The falsified predicate is passed in, already frozen at
   the propagation by lib/core/pb_analysis.ml's [bounds_before] -- I-X6, and
   lib/core/reduce.ml draws the same line for the same reason.

   It does not mint a row. Every id it cites comes from [Encoding.consistency_id], i.e.
   from a row the .opb already contains, introduced before the proof's first decision and
   retired by nothing. That is what keeps pb_analysis.ml's I-S4 discharge true after this
   module joins the derivation: the cited set still holds model-row ids and nothing else.
   A missing id (the caller's [ladder_id] answering [None], which is what the ladder's
   ENDS do) is not an error -- the term is simply not liftable and is left alone.

   It does not double-count [Order_reason]. The chain [Order_reason.weaken_declared]
   builds is a list of LITERAL AXIOMS inside a propagator's own [Explanation]; it names
   no constraint id and appears on a [pol] as [Weaken] summands. The chain here is a list
   of CONSTRAINT IDS of the ladder rows. They are different objects on different lines of
   the proof, appearing in different derivations -- [Linear]'s justification of its
   pruning, and PB analysis's derivation of a learned row -- and neither is a copy of the
   other. test/unit/test_pb_analysis.ml pins that they cannot collide. *)

module Lit = Baguette_proof.Lit

(* The ladder row at value [w] for variable [name], as the .opb literally holds it:

     1 ~x_ge_(w+1)  1 x_ge_w  >= 1

   [Encoding.declare_int] writes exactly this, for [lo < w < hi], and hands its id to
   [Encoding.consistency_id]. Rebuilt here rather than fetched because [Propagator.pb_row]
   is the only channel core has for a row's terms and a ladder row has no propagator
   instance to hang one on; the ONE thing that must agree with the encoding is the shape,
   and test/unit/test_pb_analysis.ml asserts it against [Encoding]'s own output rather
   than against this comment. *)
let ladder_row ~name w : Learned.t =
  Learned.make [ (1, Lit.ge name w); (1, Lit.negate (Lit.ge name (w + 1))) ] 1

(* A lift, as data. [steps] is [(value, multiplier, cid)] in the order the additions are
   performed -- increasing value for a negative pivot, decreasing for a positive one --
   which is the order [derive] writes them on the [pol] line. Determinism: the list is
   built by folding a sorted list of terms, never a [Hashtbl]; see
   lib/core/learned.ml's note on why that matters to the gate. *)
type t = {
  lifted : Learned.t;  (** the reason row with the chain added *)
  steps : (int * int * int) list;  (** (ladder value, multiplier, constraint id) *)
  rows : (int * Learned.t) list;
      (** the same ladder rows as (id, data), in the same order. Carried for the reason
          [Pb_analysis.antecedent_rows] is: a lift adds PREMISES to the derivation, and an
          entailment oracle handed the model rows alone would be checking a claim nobody
          made. *)
  rungs : int;  (** [List.length steps]: how many ladder rows this cites *)
}

(* The derivation of [lifted] from the model row's own explanation: one [pol] adding the
   ladder rows at their multipliers, divisor 1. Returns [e] untouched when there is
   nothing to add, so a lift that found no rung writes no line.

   [~break:true] is THE BREAK LANE for this module and is wrong on purpose: it writes the
   first rung at one more than its multiplier, so the [pol] derives a row that is not
   [lifted]. It stays SOUND -- adding a larger positive multiple of a real .opb row is
   still cutting planes -- which is exactly why it is worth having: the proof is
   well-formed, every id it names is live, and the only thing wrong with it is the
   ARITHMETIC. A checker that accepted it would be telling us that
   [Pb_analysis.introduce]'s claim is not being compared against anything, and M1-T42,
   M1-T51 and M2-T9's "Break A" are three occasions on which a well-formed but wrong
   derivation went through. Reached only through [Search.config], never from the CLI. *)
let derive ?(break = false) (t : t) (e : Explanation.t) : Explanation.t =
  match t.steps with
  | [] -> e
  | steps ->
      let bump = ref break in
      Explanation.combine
        (Explanation.term 1 e
        :: List.map
             (fun (_, m, cid) ->
               let m =
                 if !bump then (
                   bump := false;
                   m + 1)
                 else m
               in
               Explanation.term m (Explanation.model_row cid))
             steps)
        1

(* Every constraint id the lift cites, in order. Carried for the same reason
   [Pb_analysis.cited_ids] is: a test asserts the I-S4 property rather than a reader
   taking a paragraph's word for it. *)
let cited_ids (t : t) = List.map (fun (_, _, cid) -> cid) t.steps

(* The thresholds of the ladder rows that carry a term at rung [v] onto rung [k], and
   nothing else decides the direction:

     - [positive = false] (the pivot is ~[x>=k], an UPPER-bound pruning): [v < k] and the
       rows are [v, v+1, ..., k-1], ascending.
     - [positive = true] (the pivot is [x>=k], a LOWER-bound pruning): [v > k] and the
       rows are [v-1, v-2, ..., k], descending.

   Empty when [v] is on the wrong side of [k] or equal to it -- a term that does not
   entail the pivot is not liftable onto it at any price. *)
let path ~positive ~v ~k =
  if positive then if v <= k then [] else List.init (v - k) (fun i -> v - 1 - i)
  else if v >= k then []
  else List.init (k - v) (fun i -> v + i)

(* [lift ~row ~pivot ~falsified ~ladder_id] strengthens [row] by the ladder chain that
   carries every NOT-falsified term entailing [pivot] onto [pivot] itself.

   [ladder_id name w] is [Encoding.consistency_id], i.e. the id of the ladder row at
   value [w] or [None] when there is none (the ladder's ends, and any variable whose
   declared width is 1). A term whose whole path is not available is skipped; a partial
   lift is not attempted, because half a chain leaves an intermediate rung standing and
   the arithmetic no longer lands on the pivot.

   [None] means "no rung applies", which is the honest answer at a ladder end and on a
   Boolean, and the caller then proceeds with the bare row exactly as it did before this
   module existed. [Some t] always has [t.rungs > 0].

   Raises nothing: [Learned.combine] multiplies through [Checked] and may raise
   [Checked.Overflow], which is I-X8 / D-0029 and is the caller's to catch -- it is the
   same raise the caller already catches around its own [combine], and the answer to it
   is to learn a clause instead, never to wrap. *)
let lift ~(row : Learned.t) ~(pivot : Lit.t) ~(falsified : Lit.t -> bool)
    ~(ladder_id : string -> int -> int option) : t option =
  match pivot.Lit.v with
  | Lit.Eq _ -> None (* the direct encoding has no ladder: D-0019/D-0040 *)
  | Lit.Ge (name, k) ->
      let positive = pivot.Lit.positive in
      (* Multipliers accumulated per ladder value. An association list keyed by the value,
         so the result is a function of the SET of liftable terms and not of the order
         [Learned.terms] happened to return them in. *)
      let bump acc w m =
        match List.assoc_opt w acc with
        | Some m0 -> (w, m0 + m) :: List.remove_assoc w acc
        | None -> (w, m) :: acc
      in
      let mults =
        List.fold_left
          (fun acc (tm : Learned.term) ->
            let l = tm.Learned.lit in
            match l.Lit.v with
            | Lit.Ge (n, v)
              when String.equal n name && l.Lit.positive = positive
                   && (not (Lit.equal l pivot))
                   && not (falsified l) -> (
                match path ~positive ~v ~k with
                | [] -> acc
                | ws ->
                    (* Either the whole chain is available or the term is not lifted. *)
                    if List.for_all (fun w -> ladder_id name w <> None) ws then
                      List.fold_left (fun acc w -> bump acc w tm.Learned.coeff) acc ws
                    else acc)
            | _ -> acc)
          [] (Learned.terms row)
      in
      if mults = [] then None
      else
        (* Ascending for a negative pivot, descending for a positive one: the order in
           which each rung's coefficient is exactly the one the previous addition put
           there. Addition is commutative, so this is legibility of the [pol] rather than
           correctness -- but a reader following the line wants the substitutions in the
           order the argument makes them. *)
        let ordered =
          List.sort
            (fun (a, _) (b, _) -> if positive then compare b a else compare a b)
            mults
        in
        let steps =
          List.filter_map
            (fun (w, m) ->
              match ladder_id name w with Some cid -> Some (w, m, cid) | None -> None)
            ordered
        in
        if steps = [] then None
        else
          let lifted =
            List.fold_left
              (fun acc (w, m, _) -> Learned.combine acc 1 (ladder_row ~name w) m)
              row steps
          in
          let rows = List.map (fun (w, _, cid) -> (cid, ladder_row ~name w)) steps in
          Some { lifted; steps; rows; rungs = List.length steps }
