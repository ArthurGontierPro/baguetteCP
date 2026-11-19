(* ladder.ml: THE ORDER-ENCODING LADDER CHAIN, AS A ROW (M2-L11), and the BITS ARM: a
   bits block instantiated through its bridges (M8-bits-encoding, D-0153, at the foot).

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

   It does not mint a row ([lift] does not; the bits arm at the foot of this file does,
   and says why that is safe). Every id it cites comes from [Encoding.consistency_id], i.e.
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
   other. test/unit/test_ladder.ml pins that they cannot collide.

   ---------------------------------------------------------------------------
   It stays a `pol` (M8-bits-encoding-T5, D-0131)
   ---------------------------------------------------------------------------

   D-0131 writes the order arm's ladder walks as `rup` wherever the checker's unit
   propagation closes them. This derivation is the one ladder walk that is NOT such a
   case, and it was measured rather than argued: on the worked case above, `rup` of the
   lifted row `9 ~[a>=3] + 3 ~[a>=4] + 2 ~[b>=1..4] >= 6` against the .opb (the row and
   the ladder) is REFUSED by VeriPB 3.0.2 ("not implied by reverse unit propagation"),
   while the `pol` of the two rung additions is accepted and `e` confirms it equals the
   row. Reverse unit propagation negates the claim and propagates; the lifted row's
   negation forces nothing that the model row then contradicts, because the row's
   strength was never in the row -- it is in the rungs, which is the whole point of this
   module. So [Pb_analysis.introduce] keeps `pol` + `ia`, the `ia` stating the row our
   arithmetic produced against the checker's, and its token count is Theta(rungs) ids
   added into a Theta(w)-term accumulator, which is the shape D-0127 measured as
   quadratic in the checker. `--stats` reports it (`pol-widest`) so a wide one is seen. *)

module Lit = Baguette_proof.Lit

(* The ladder row at value [w] for variable [name], as the .opb literally holds it:

     1 ~x_ge_(w+1)  1 x_ge_w  >= 1

   [Encoding.declare_int] writes exactly this, for [lo < w < hi], and hands its id to
   [Encoding.consistency_id]. Rebuilt here rather than fetched because [Propagator.pb_row]
   is the only channel core has for a row's terms and a ladder row has no propagator
   instance to hang one on; the ONE thing that must agree with the encoding is the shape,
   and test/unit/test_ladder.ml asserts it against the constraint [Encoding] actually
   appended, rather than against this comment. *)
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

module Int_tbl = Hashtbl.Make (Int)

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
   is to learn a clause instead, never to wrap.

   M6-T23 (D-0149): [stop] is asked before every rung's [combine], and [Stopped] is
   raised when it says yes. One lift on 2017_cargo_challenge01 folds thousands of rungs
   into a row of thousands of terms, minutes of [combine] and its GC with nothing polling
   the time limit, so the stop fired only after the analysis ended, long past the limit.
   The default never says yes, so nothing changes without a limit, and a limit that fires
   here abandons a lift whose row nothing has used yet. *)
exception Stopped

let lift ?(stop = fun () -> false) ~(row : Learned.t) ~(pivot : Lit.t)
    ~(falsified : Lit.t -> bool) ~(ladder_id : string -> int -> int option) () : t option
    =
  match pivot.Lit.v with
  | Lit.Eq _ -> None (* the direct encoding has no ladder: D-0019/D-0040 *)
  | Lit.Bit _ -> None (* a bits variable has no ladder either: D-0130 section 7.5 *)
  | Lit.Ge (name, k) ->
      let positive = pivot.Lit.positive in
      (* Multipliers accumulated per ladder value, keyed by the value, so the result is a
         function of the SET of liftable terms and not of the order [Learned.terms]
         happened to return them in. M11-complexity-T4 (D-0140 P2, D-0144): a table keyed
         by the value, where it was an association list with an [assoc] and a
         [remove_assoc] per rung per term. The table is iterated once, into a list that
         is then SORTED by the value, which is unique per entry, so its iteration order
         reaches nothing: the same [(value, multiplier)] pairs come out in the same order
         as before. *)
      let tbl = Int_tbl.create 16 in
      let bump w m =
        match Int_tbl.find_opt tbl w with
        | Some m0 -> Int_tbl.replace tbl w (m0 + m)
        | None -> Int_tbl.add tbl w m
      in
      List.iter
        (fun (tm : Learned.term) ->
          let l = tm.Learned.lit in
          match l.Lit.v with
          | Lit.Ge (n, v)
            when String.equal n name
                 && Bool.equal l.Lit.positive positive
                 && (not (Lit.equal l pivot))
                 && not (falsified l) -> (
              match path ~positive ~v ~k with
              | [] -> ()
              | ws ->
                  (* Either the whole chain is available or the term is not lifted. *)
                  if List.for_all (fun w -> Option.is_some (ladder_id name w)) ws then
                    List.iter (fun w -> bump w tm.Learned.coeff) ws)
          | _ -> ())
        (Learned.terms row);
      let mults = Int_tbl.fold (fun w m acc -> (w, m) :: acc) tbl [] in
      if mults = [] then None
      else
        (* Ascending for a negative pivot, descending for a positive one: the order in
           which each rung's coefficient is exactly the one the previous addition put
           there. Addition is commutative, so this is legibility of the [pol] rather than
           correctness -- but a reader following the line wants the substitutions in the
           order the argument makes them. *)
        let ordered =
          List.sort
            (fun (a, _) (b, _) -> if positive then Int.compare b a else Int.compare a b)
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
              (fun acc (w, m, _) ->
                if stop () then raise Stopped;
                Learned.combine acc 1 (ladder_row ~name w) m)
              row steps
          in
          let rows = List.map (fun (w, _, cid) -> (cid, ladder_row ~name w)) steps in
          Some { lifted; steps; rows; rungs = List.length steps }

(* ===========================================================================
   THE BITS ARM: a bits block INSTANTIATED through its bridges (M8-bits-encoding, D-0153)
   ===========================================================================

   What the ladder lift above does for an order variable, this does for a variable on
   the BITS encoding (D-0130, D-0132): it turns the reason row the .opb holds into a row
   that PB-propagates the pivot, by adding rows the proof already has. The difference is
   in what a bits term IS. An order term of a model row is a run of literals each of
   which the trail can falsify, so the analysis resolves on them as they stand. A bits
   term [a * X'] (X' = sum 2^i x_bit_i, the offset of x from its declared low) is not:
   no bit is a bound, the trail never falsifies one, and a pivot cannot be one. So no
   row this arm hands back contains a [Bit] literal, and the learned rows, the
   criterion, the levels and lib/core/prop/pb.ml never see one.

   ---------------------------------------------------------------------------
   The step: a bridge cancels a whole block, and leaves ONE atom
   ---------------------------------------------------------------------------

   [Encoding.ensure_atom] gives the atom [x >= v] two rows (D-0130 section 5.1), with
   k = v - lo and K = 2^n - k:

     B1_v   X' + k ~x_ge_v >= k        (x_ge_v  -> X' >= k)
     B2_v  ~X' + K  x_ge_v >= K        (~x_ge_v -> X' <= k - 1)

   and every bits variable has its two declared-bound rows, [@lb: X' >= 0] and
   [@ub: ~X' >= 2^n - 1 - (hi - lo)]. A row carrying [a * X'] (a POSITIVE block, every
   bit at [a * 2^i]) is helped by a large x, so what the assignment says about it is
   x's UPPER bound u: adding [a * B2_(u+1)] cancels every bit ([a 2^i x_bit_i +
   a 2^i ~x_bit_i] is the constant [a 2^i], D-0044's complement cancellation) and leaves
   [a K x_ge_(u+1)] with the degree lowered by [a (u - lo)] -- the block, worth at most
   [a (u - lo)] while the atom is false, replaced by exactly that. At the declared high
   it is [a * @ub], which leaves nothing. A NEGATIVE block ([a * ~X'], a row helped by a
   small x) reads the LOWER bound l the same way: [a * B1_l] leaves [a k_l ~x_ge_l], and
   [a * @lb] at the declared low leaves nothing. Every step is the addition of a positive
   multiple of a line on the page, so the result is sound whatever bound is chosen; the
   choice decides only whether it is strong enough to propagate.

   ---------------------------------------------------------------------------
   Which bound: the one in force at the propagation, or the PIVOT's own atom
   ---------------------------------------------------------------------------

   For every block but the pruned one the bound is the one in force just before the
   propagation, read off the same frozen predicate the reduction uses (I-X6): the
   tightest [u] whose atom [x_ge_(u+1)] the predicate reports falsified, by binary search
   over the declared range. Its atom is then falsified under that predicate, so the
   block contributes to the slack exactly what the integer propagator read, nothing more.

   The pruned block is instantiated at the PIVOT: when the pivot is [~x_ge_v] (an upper
   push, x <= v - 1) the block is negative and [a * B1_v] leaves [a k_v ~x_ge_v], the
   pivot itself at coefficient [a k_v]; a lower push mirrors it through B2_v. The pivot's
   value and not the propagator's claim, because the learned row names the pivot, and
   the claim may be tighter than the pivot (the entry that falsified [x_ge_v] may have
   pushed x lower still). It still propagates: [Linear] deduced [a X' <= K] with
   [K / a < k_v], and the instantiated row's slack is K against a pivot coefficient of
   [a k_v] -- D-0153 section 2 has the arithmetic. A pruning that settled past a hole
   can fall short of it, and [Reduce]'s postcondition then says so: a fallback, never a
   wrong row.

   The conflict row is instantiated the same way at the conflict, with no pivot: every
   atom is then falsified, and the row's slack is the integer slack [Linear] found
   negative.

   ---------------------------------------------------------------------------
   Why not the alternatives (measured, D-0153 section 1)
   ---------------------------------------------------------------------------

     - THE SPARSE CHAIN AS THE LADDER of a bits term (replace [a X'] by its order
       expansion over the minted atoms, then reuse [lift]): that row is not one
       cutting-planes step from the pairs (D-0134 section 11's convex-combination
       argument), and as a `rup` it is refused at 8 bits (probe p7w) -- accepted at 3
       only, D-0127's caveat.
     - THE BITS ROW ITSELF AS AN ANTECEDENT (add conflict and reason so the pivot
       variable's whole block cancels, no atom): accepted, and STRONGER where the reason
       is tight (probe p6 learns z <= 1 where this arm learns z <= 2), but the row it
       leaves keeps every other variable's block, and a [Bit] in a learned row is a
       literal the criterion, the levels and [Pb] cannot read; where the reason is not
       tight it also loses the conflict to rounding, which the reduction here exists to
       repair. Recorded as the next step, not taken.

   ---------------------------------------------------------------------------
   It MINTS, unlike [lift]
   ---------------------------------------------------------------------------

   [lift] cites only ladder rows of the .opb. An atom is a proof line: [bits.bridge] is
   [Encoding.ensure_atom], which writes the `red` pair (and its sparse-chain links) at
   level 0 the first time the atom is named, and memoises it after. Almost every atom
   this arm asks for is already on the page -- the trace names the same bounds as facts
   and claims -- and one minted here is a level-0 line like any other, never deleted
   before the conclusion (D-0132 section 2.8), which is what keeps pb_analysis.ml's I-S4
   discharge true: the derivation still cites only lines no `w` retires. The
   precondition [ensure_atom] states (no root contradiction on the page) holds because
   PB analysis runs at a conflict below the root. *)

(* What the analysis is told about the bits encoding: the declared range and bit count of
   a bits variable, the ids of an atom's two rows, and the ids of the two bound rows.
   lib/core/pb_analysis.ml builds it from the encoding ([bits_of_ctx]); [no_bits] is the
   answer for a caller with no encoding, under which a row with a bits term is refused. *)
type bits = {
  bits_var : string -> (int * int * int) option;
      (** [Some (lo, hi, n)] iff the variable is on the bits encoding *)
  bridge : string -> int -> int * int;
      (** the ids (B1, B2) of [x >= v], minted on first ask ([Encoding.ensure_atom]) *)
  bound_rows : string -> int * int;  (** the ids (@lb, @ub) *)
}

let no_bits =
  {
    bits_var = (fun _ -> None);
    bridge = (fun x _ -> invalid_arg ("Ladder.no_bits: no bridge for " ^ x));
    bound_rows = (fun x -> invalid_arg ("Ladder.no_bits: no bound rows for " ^ x));
  }

(* The four rows, as [Encoding] writes them ([declare_int_bits], [mint_bits_atom]). The
   one thing that must agree with the encoding is the shape, and test_pb.ml asserts it
   against the lines the encoding actually wrote. *)
let bit_block name n ~negated =
  List.init n (fun i ->
      let b = Lit.bit name i in
      (1 lsl i, if negated then Lit.negate b else b))

let b1_row name ~lo ~n v =
  let k = v - lo in
  Learned.make (bit_block name n ~negated:false @ [ (k, Lit.negate (Lit.ge name v)) ]) k

let b2_row name ~lo ~n v =
  let big_k = (1 lsl n) - (v - lo) in
  Learned.make (bit_block name n ~negated:true @ [ (big_k, Lit.ge name v) ]) big_k

let lb_row name ~n = Learned.make (bit_block name n ~negated:false) 0

let ub_row name ~lo ~hi ~n =
  Learned.make (bit_block name n ~negated:true) ((1 lsl n) - 1 - (hi - lo))

(* An instantiation, as data: the row with every bits block replaced, and the rows added,
   [(multiplier, constraint id, row)] in the order they were added. *)
type instantiated = { inst : Learned.t; added : (int * int * Learned.t) list }

(* The derivation of [inst] from the model row's own explanation: one `pol` adding the
   bridges and bound rows at their multipliers, divisor 1. *)
let derive_instantiated (i : instantiated) (e : Explanation.t) : Explanation.t =
  match i.added with
  | [] -> e
  | added ->
      Explanation.combine
        (Explanation.term 1 e
        :: List.map
             (fun (m, cid, _) -> Explanation.term m (Explanation.model_row cid))
             added)
        1

let has_bits (row : Learned.t) =
  List.exists
    (fun (tm : Learned.term) -> Lit.is_bit tm.Learned.lit.Lit.v)
    (Learned.terms row)

(* The upper bound of [name] the frozen predicate reports: the smallest [u] in [lo, hi]
   with [x_ge_(u+1)] falsified, [hi] when none is. Binary search: "x <= u held" only
   grows with [u]. *)
let frozen_hi ~falsified name ~lo ~hi =
  let holds u = u >= hi || falsified (Lit.ge name (u + 1)) in
  let rec go a b =
    if a >= b then a
    else
      let mid = a + ((b - a) / 2) in
      if holds mid then go a mid else go (mid + 1) b
  in
  go lo hi

(* The lower bound, mirrored: the largest [l] in [lo, hi] with [~x_ge_l] falsified. *)
let frozen_lo ~falsified name ~lo ~hi =
  let holds l = l <= lo || falsified (Lit.negate (Lit.ge name l)) in
  let rec go a b =
    if a >= b then a
    else
      let mid = a + ((b - a + 1) / 2) in
      if holds mid then go mid b else go a (mid - 1)
  in
  go lo hi

exception Unreadable of string

(* [instantiate ~bits ~row ~pivot ~falsified] replaces every bits block of [row] as the
   section above says: at the pivot's own atom for the block of the pivot's variable when
   the block's direction matches the pivot's, at the frozen bound otherwise. [Error] names
   what could not be read: a variable [bits] does not know, a block without its bit 0, a
   pivot outside the declared range, or a block that is not [a * 2^i] (a bit left over).
   The blocks are taken in the order their variables first occur in [row]'s terms, which
   [Learned.make] sorted, so the result is a function of the row.

   Raises [Checked.Overflow] from [Learned.combine], the caller's to catch as for [lift]. *)
let instantiate ~(bits : bits) ~(row : Learned.t) ~(pivot : Lit.t option)
    ~(falsified : Lit.t -> bool) : (instantiated, string) result =
  let names =
    List.rev
      (List.fold_left
         (fun acc (tm : Learned.term) ->
           match tm.Learned.lit.Lit.v with
           | Lit.Bit (x, _) when not (List.mem x acc) -> x :: acc
           | _ -> acc)
         [] (Learned.terms row))
  in
  let block (row, added) x =
    let lo, hi, n =
      match bits.bits_var x with
      | Some r -> r
      | None -> raise (Unreadable (x ^ " is not on the bits encoding"))
    in
    let a, positive =
      match
        List.find_opt
          (fun (tm : Learned.term) ->
            match tm.Learned.lit.Lit.v with
            | Lit.Bit (y, 0) -> String.equal x y
            | _ -> false)
          (Learned.terms row)
      with
      | Some tm -> (tm.Learned.coeff, tm.Learned.lit.Lit.positive)
      | None -> raise (Unreadable (x ^ "'s block has no bit 0"))
    in
    let at_pivot =
      match pivot with
      | Some ({ Lit.v = Lit.Ge (y, v); _ } as p)
        when String.equal x y && Bool.equal p.Lit.positive positive ->
          if v <= lo || v > hi then
            raise
              (Unreadable
                 (Printf.sprintf "the pivot %s is outside %s's range" (Lit.to_string p) x));
          Some v
      | _ -> None
    in
    let cid, r =
      if positive then
        let atom =
          match at_pivot with
          | Some _ -> at_pivot
          | None ->
              let u = frozen_hi ~falsified x ~lo ~hi in
              if u >= hi then None else Some (u + 1)
        in
        match atom with
        | None -> (snd (bits.bound_rows x), ub_row x ~lo ~hi ~n)
        | Some v -> (snd (bits.bridge x v), b2_row x ~lo ~n v)
      else
        let atom =
          match at_pivot with
          | Some _ -> at_pivot
          | None ->
              let l = frozen_lo ~falsified x ~lo ~hi in
              if l <= lo then None else Some l
        in
        match atom with
        | None -> (fst (bits.bound_rows x), lb_row x ~n)
        | Some v -> (fst (bits.bridge x v), b1_row x ~lo ~n v)
    in
    (Learned.combine row 1 r a, (a, cid, r) :: added)
  in
  try
    let row, added_rev = List.fold_left block (row, []) names in
    if has_bits row then raise (Unreadable "a bits block that is not a * 2^i");
    Ok { inst = row; added = List.rev added_rev }
  with Unreadable m -> Error m
