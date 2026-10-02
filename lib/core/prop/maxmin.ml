(* array_int_maximum(m, [x_1..x_n]) and array_int_minimum(m, [x_1..x_n]): the
   DISJUNCTIVE half of m = max_i x_i (resp. min), as one propagator. M4-T9, D-0095.
   Governed by docs/SPEC.md 3.2 (consistency) and 3.3 (explanations), and by
   docs/PROOF-FORMAT.md section 4's `array_int_maximum` row.

   ---------------------------------------------------------------------------
   The split: m = max x is TWO constraints, and only one of them is this module
   ---------------------------------------------------------------------------

       m = max_i x_i   <=>   (/\_i  m >= x_i)   /\   m <= max_i x_i

   The CONJUNCTIVE half is n ordinary linear rows `x_i - m <= 0`, and
   lib/flatzinc/compile.ml posts them as exactly that: n [Linear] instances over n
   `int_lin_le` rows of the .opb. Those rows ARE the model rows, and they carry two of
   the four bounds rules with [Linear]'s own pol justification (D-0013) and nothing new:

     (R1)  lo(m)   >= lo(x_i)      -- row i, read from x_i's lower bound
     (R2)  hi(x_i) <= hi(m)        -- row i, read from m's upper bound

   This module is the DISJUNCTIVE half, `m <= max_i x_i`, and its two rules:

     (R3)  hi(m)   <= max_i hi(x_i)
     (R4)  lo(x_j) >= lo(m)        when j is the ONLY position with hi(x_j) >= lo(m)

   plus the conflict both rules degenerate to, max_i hi(x_i) < lo(m).

   ---------------------------------------------------------------------------
   What the .opb holds for the disjunction, and why it is per VALUE
   ---------------------------------------------------------------------------

   In the order encoding the disjunction is a family of clauses, one per threshold v:

     C_v :   ~[m >= v]  \/  [x_1 >= v]  \/ ... \/  [x_n >= v]

   "if m reaches v, some x reaches v" -- which, over every v, is exactly m <= max x.
   [rows] lists them and compile.ml posts each as one `>= 1` row. Literals the declared
   bounds settle are folded at construction (a constant-false literal is dropped, a
   constant-true one makes the clause vacuous and it is not posted), so only the
   thresholds

     v  in  [ max(dlo m, Lx + 1) ,  min(dhi m, max(Hx + 1, dlo m)) ]

   are rows, where Lx / Hx are the largest declared lower / upper bound of any x. Below
   Lx + 1 some x is >= v by declaration; above dhi m the antecedent is false; above
   Hx + 1 the clause is the unit ~[m >= v], which the ladder already gets from
   C_(Hx+1). The single row at dlo m when dlo m > Hx is the EMPTY clause, and that model
   is refuted by it at the root.

   The alternative was a selector per position (b_i -> m <= x_i, big-M, plus one
   clause over the b_i), the shape int_lin_ne's `_neN` has. It was not taken, for three
   reasons: it needs n auxiliary 0-1 variables the solver would have to either search
   on or keep in step; each big-M row expands both m and x_i over their full ladders, so
   it is not smaller (2n rows of width ~w against <= w rows of width n + 1); and its
   prunings would be RUP only through two rows and the ladder, where the per-value form
   makes every one of them ONE row, restated.

   ---------------------------------------------------------------------------
   Justification: one clause, which IS a row of the .opb
   ---------------------------------------------------------------------------

   Every explanation this module builds is [Explanation.clause C_v] for one v, and
   C_v is the posted row verbatim -- the lib/core/prop/clause.ml situation exactly
   (M2-L12: a clause over ORDER literals; Justify renders it `rup C_v`, reverse unit
   propagation in one step against the row that states it). No new [Explanation]
   constructor, no row id to carry, nothing [Deferred]: the clause for each v is built
   once, in [make], and shared, so lib/core/justify.ml's memoisation on physical
   identity fires across prunings at the same threshold.

     (R3)  at v = H + 1, H = max hi(x_i) and lo(m) <= H < hi(m):
           facts  x_i <= H  for every i                 claim  m <= H
     (R4)  at v = L = lo(m), j the only position that can reach L:
           facts  m >= L,  x_i <= L - 1 for every i <> j   claim  x_j >= L
     (conflict) at v = max(H + 1, dlo m), H < lo(m):
           facts  m >= v,  x_i <= v - 1 for every i

   Each v above lies in the posted range -- the arithmetic is in D-0095 and is checked
   by [expl_at]'s bounds test, which raises rather than invent a clause the .opb does
   not hold. The facts are the bound facts read (I-X10's "the facts on the line's own
   tail"), and each is the negation of one literal of C_v, so a trace line's tail and
   the clause agree literal for literal (D-0026's agreement check under
   BAGUETTE_DEBUG; test_prop.ml asserts it on a hand-built store).

   I-X10 class: [Single_row], on the clause.ml precedent. One threshold, one row.

   ---------------------------------------------------------------------------
   Consistency level: BOUNDS, for the constraint THIS INSTANCE is
   ---------------------------------------------------------------------------

   The instance's constraint is `m <= max_i x_i` (the linear rows are other instances),
   and for that constraint R3 and R4 are bounds(Z) consistency: hi(m) is supported by
   the x attaining H; lo(x_j) by m = lo(m) exactly when another x can reach lo(m), and
   R4 is precisely the case where none can; every other bound is supported by setting
   the x that attains H to H. Engine fixpoint with R1/R2 gives the textbook bounds
   rules for max. It never reads or punches an interior hole (the [Domain] settle is
   [Store]'s, I-X9).

   ---------------------------------------------------------------------------
   minimum: the SAME propagator over negated views (D-0058)
   ---------------------------------------------------------------------------

       m = min_i x_i   <=>   -m = max_i (-x_i)

   [make ~dir:Min] negates every view at construction and from then on there is one
   code path. A negated view's `>= v` literal IS the base's `<= -v` literal
   ([Lit.view_ge]), so the rows posted for a minimum are C_v in the mirror
   (`~[m <= -v] \/ [x_1 <= -v] \/ ...`) with no second encoding, and its facts are the
   base's upper bounds where a maximum's are lower ones. A constant operand is a
   [View.Const], whose literals all fold, so `int_max(x, 3, m)` needs no special case. *)

module Lit = Baguette_proof.Lit

type dir = Max | Min

(* One operand, frozen at [make] in MAX coordinates: [view] is already negated for a
   minimum, and [dlo]/[dhi] are the VIEW's declared bounds, [bdlo]/[bdhi] the base's
   (what a [Reason.fact] carries as [decl]). *)
type slot = {
  view : View.t;
  name : string;
  map : Lit.affine;
  dlo : int;
  dhi : int;
  bdlo : int;
  bdhi : int;
}

type t = {
  m : slot;
  xs : slot array;
  vlo : int;
  expls : Explanation.t option array;
      (* [expls.(v - vlo)] is C_v, [None] where C_v is vacuous. Same list [rows] posts. *)
  vars : Var.t list;
}

let slot_of store (v : View.t) =
  match v with
  | View.Const c ->
      { view = v; name = ""; map = Lit.identity; dlo = c; dhi = c; bdlo = c; bdhi = c }
  | View.Affine { base; map } ->
      let d = Store.get store base in
      let bdlo = Domain.lo d and bdhi = Domain.hi d in
      let a = Lit.apply map bdlo and b = Lit.apply map bdhi in
      {
        view = v;
        name = Store.name store base;
        map;
        dlo = min a b;
        dhi = max a b;
        bdlo;
        bdhi;
      }

(* [view >= v] against the declared bounds: [`Holds], [`Fails], or the literal. *)
let lit_ge s v =
  if v <= s.dlo then `Holds
  else if v > s.dhi then `Fails
  else `Lit (Lit.view_ge s.name s.map v)

(* The bound fact "view >= v" / "view <= v", stated on the base. [None] for a constant,
   which has no fact to state. A fact at or beyond the base's declared bound
   materialises to no literal ([Reason.lit_of_fact]); that is the same fold [lit_ge]
   makes, so the reason and the clause cannot disagree about it. *)
let fact_ge s v =
  match s.view with
  | View.Const _ -> None
  | View.Affine _ ->
      let d = v - s.map.Lit.offset in
      Some
        (if s.map.Lit.negated then Reason.at_most ~name:s.name ~decl:s.bdhi (-d)
         else Reason.at_least ~name:s.name ~decl:s.bdlo d)

let fact_le s v =
  match s.view with
  | View.Const _ -> None
  | View.Affine _ ->
      let d = v - s.map.Lit.offset in
      Some
        (if s.map.Lit.negated then Reason.at_least ~name:s.name ~decl:s.bdlo (-d)
         else Reason.at_most ~name:s.name ~decl:s.bdhi d)

(* C_v, folded, or [None] when a constant-true literal makes it vacuous. Duplicate
   literals (the same x twice) are merged, so the row stays a clause. *)
let clause_lits m xs v =
  let add l acc = if List.exists (Lit.equal l) acc then acc else l :: acc in
  let head =
    match lit_ge m v with
    | `Holds -> Some []
    | `Fails -> None
    | `Lit l -> Some [ Lit.negate l ]
  in
  Array.fold_left
    (fun acc x ->
      match (acc, lit_ge x v) with
      | None, _ | _, `Holds -> None
      | Some ls, `Fails -> Some ls
      | Some ls, `Lit l -> Some (add l ls))
    head xs
  |> Option.map List.rev

let threshold_range m xs =
  let lx = Array.fold_left (fun a s -> max a s.dlo) min_int xs in
  let hx = Array.fold_left (fun a s -> max a s.dhi) min_int xs in
  (max m.dlo (lx + 1), min m.dhi (max (hx + 1) m.dlo))

let make store ~dir (m : View.t) (xs : View.t list) : t =
  if xs = [] then
    invalid_arg "Maxmin.make: the maximum/minimum of an empty array is undefined";
  let orient v = match dir with Max -> v | Min -> View.negate v in
  let m = slot_of store (orient m) in
  let xs = Array.of_list (List.map (fun v -> slot_of store (orient v)) xs) in
  let vlo, vhi = threshold_range m xs in
  let expls =
    Array.init
      (max 0 (vhi - vlo + 1))
      (fun k -> Option.map Explanation.clause (clause_lits m xs (vlo + k)))
  in
  let vars =
    List.sort_uniq Var.compare
      (List.concat_map (fun s -> View.vars s.view) (m :: Array.to_list xs))
  in
  { m; xs; vlo; expls; vars }

(* The rows compile.ml posts, one clause per threshold, in increasing v. *)
let rows t =
  Array.to_list t.expls
  |> List.filter_map (function
       | None -> None
       | Some e -> (
           match Explanation.force e with Explanation.Clause ls -> Some ls | _ -> None))

let n_rows t =
  Array.fold_left (fun n e -> if Option.is_some e then n + 1 else n) 0 t.expls

(* C_v as an explanation. A threshold outside the posted range, or a vacuous one, is a
   bug in the rule that chose it (the header argues each rule's v is in range), and it is
   raised rather than rendered: a `rup` over a clause the .opb does not hold would verify
   only by luck. *)
let expl_at t v =
  let k = v - t.vlo in
  if k < 0 || k >= Array.length t.expls then
    invalid_arg (Printf.sprintf "Maxmin: threshold %d is outside the posted rows" v)
  else
    match t.expls.(k) with
    | Some e -> e
    | None -> invalid_arg (Printf.sprintf "Maxmin: C_%d is vacuous and was not posted" v)

let vars t = t.vars
let name = "array_int_maximum"
let consistency = Propagator.Bounds
let opt f = Option.to_list f

let propagate t store =
  let lm = View.lo store t.m.view and um = View.hi store t.m.view in
  let h = Array.fold_left (fun a s -> max a (View.hi store s.view)) min_int t.xs in
  if h < lm then
    let v = max (h + 1) t.m.dlo in
    let facts =
      opt (fact_ge t.m v)
      @ List.concat_map (fun s -> opt (fact_le s (v - 1))) (Array.to_list t.xs)
    in
    Propagator.Conflict
      (Store.conflict store (Reason.because ~concludes:None facts (expl_at t v)))
  else
    (* R3: hi(m) <= H. *)
    let r3 =
      if h < um then
        let facts = List.concat_map (fun s -> opt (fact_le s h)) (Array.to_list t.xs) in
        View.set_hi store t.m.view h
          (Reason.because ~concludes:(fact_le t.m h) facts (expl_at t (h + 1)))
      else Store.Unchanged
    in
    match r3 with
    | Store.Conflict e -> Propagator.Conflict e
    | Store.Changed | Store.Unchanged -> (
        (* R4: the unique position that can still reach lo(m) must. R3 moved neither
           lo(m) nor any hi(x_i), so [lm] and the reachers are still current. *)
        let reach = ref [] in
        Array.iteri
          (fun i s -> if View.hi store s.view >= lm then reach := i :: !reach)
          t.xs;
        match !reach with
        | [ j ] when View.lo store t.xs.(j).view < lm -> (
            let facts =
              opt (fact_ge t.m lm)
              @ List.concat
                  (List.mapi
                     (fun i s -> if i = j then [] else opt (fact_le s (lm - 1)))
                     (Array.to_list t.xs))
            in
            let xj = t.xs.(j) in
            match
              View.set_lo store xj.view lm
                (Reason.because ~concludes:(fact_ge xj lm) facts (expl_at t lm))
            with
            | Store.Conflict e -> Propagator.Conflict e
            | Store.Changed | Store.Unchanged -> Propagator.Fixpoint)
        | _ -> Propagator.Fixpoint)

(* The packed names. One implementation; an instance reports the builtin it came from,
   the [Ne] / [Ne.Int_ne] pattern. *)
module Maximum = struct
  type nonrec t = t

  let name = name
  let consistency = consistency
  let vars = vars
  let propagate = propagate
end

module Minimum = struct
  type nonrec t = t

  let name = "array_int_minimum"
  let consistency = consistency
  let vars = vars
  let propagate = propagate
end
