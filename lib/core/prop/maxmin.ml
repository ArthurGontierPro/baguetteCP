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

   That is the PER-VALUE shape, and it is what every scope with no bits variable posts,
   byte for byte as before. Over a bits variable it cannot be posted at all: the order
   atoms of a bits variable do not exist when the .opb is closed (D-0130 section 3.4),
   and Theta(w) rows of them would be the ladder the bits encoding exists to avoid.

   ---------------------------------------------------------------------------
   The SELECTOR shape: a scope with a bits variable (M8-bits-encoding-T3, D-0134)
   ---------------------------------------------------------------------------

   D-0095 rejected one selector per position (b_i -> m <= x_i, big-M, plus one clause
   over the b_i), the shape int_lin_ne's `_neN` has, for three reasons that were the
   LADDER's: n auxiliaries to keep in step, big-M rows expanding m and x_i over their
   full ladders, and prunings RUP only through two rows. Over bits each objection is
   gone: a big-M row is O(bits); the selectors are proof-only, fixed by the `sol`/`soli`
   listing (Encoding's choice groups, D-0134 section 2.4) and never searched on; and a
   bits pruning is one `pol` either way. So when [make] is asked for [`Selector], the
   disjunction is posted as, in MAX coordinates,

     S_i :   m - x_i + M_i b_i <= M_i        M_i = dhi(m) - dlo(x_i)   (one per operand)
     S   :   b_1 + ... + b_n >= 1

   ([selector_rows] spells them on the bases; a minimum is the same rows over the negated
   views, so `x_i - m + M_i b_i <= M_i` with M_i = dhi(x_i) - dlo(m)). M_i >= 1 whenever
   the threshold range is non-empty, and when it is empty -- or m is itself one of the
   operands -- the disjunction holds by declaration, nothing is posted and no rule
   fires. Every C_v is then DERIVED instead of restated, as ONE `pol`
   ([Explanation.Resolve], D-0134 section 2.2): for each operand, S_i plus m's bridge
   at m >= v plus x_i's at x_i <= v - 1 (or the declared bound line where that is the
   bound), divided by D_i = v - min(v - 1, dhi x_i) and saturated -- the clause
   `~b_i \/ ~[m >= v] \/ [x_i >= v]` -- then the n clauses summed with S and
   saturated, which resolves the b_i away and leaves C_v with every literal. The
   arithmetic is D-0134 section 1's probes a1/c1/e1, measured before this was written.

   ---------------------------------------------------------------------------
   Justification: C_v, as a row restated (per-value) or as one Resolve (selector)
   ---------------------------------------------------------------------------

   Per-value: every explanation this module builds is [Explanation.clause C_v] for one
   v, and C_v is the posted row verbatim -- the lib/core/prop/clause.ml situation
   exactly (M2-L12: a clause over ORDER literals; Justify renders it `rup C_v`, reverse
   unit propagation in one step against the row that states it). No row id to carry,
   nothing [Deferred]: the clause for each v is built once, in [make], and shared, so
   lib/core/justify.ml's memoisation on physical identity fires across prunings at the
   same threshold.

   Selector: the explanation at v is a [Deferred] [Resolve] built on first demand and
   cached per v (the threshold range is Theta(w) on bits, so nothing is built per value
   in [make]). It derives exactly the same C_v, which is why the reason half below is
   one code path for both shapes (D-0026's split: the facts are the propagator's, the
   justification the shape's). The [Linear_term] of the CLAIM variable carries the
   negation of the claim as the bound it assumed -- R3's m >= H + 1, R4's x_j <= L - 1
   -- so the derived clause is the trace clause with the claim among its literals and
   lib/core/justify.ml's [emit_bits_pruning] pins it by `ia` with no atom added.

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

   I-X10 class: [Single_row], on the clause.ml precedent. One threshold, one row --
   restated, or derived in one line from the n + 1 rows of its own choice group.

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

(* M8-bits-encoding-T3 (D-0134): the selector shape's proof-side state. The ids are
   attached by lib/flatzinc/compile.ml once it has posted [selector_rows] (they do not
   exist when [make] runs); [cache] holds the [Resolve] of each threshold already asked
   for, so prunings at the same v share one physical explanation, as the per-value
   array lets them. *)
type selector = {
  mutable sel_rows : int array; (* S_i's id, operand order; [||] until attached *)
  mutable sel_clause : int; (* S's id *)
  cache : (int, Explanation.t) Hashtbl.t;
}

type shape =
  | Per_value of Explanation.t option array
    (* [expls.(v - vlo)] is C_v, [None] where C_v is vacuous. Same list [rows] posts. *)
  | Selector of selector

type t = {
  m : slot;
  xs : slot array;
  vlo : int;
  vhi : int;
  shape : shape;
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

(* [~shape] is the caller's: lib/flatzinc/compile.ml asks for [`Selector] exactly when
   a variable of the scope is on the bits encoding (D-0134 section 2.5), and the
   default is the per-value shape every pre-T3 caller built. *)
let make ?(shape = `Per_value) store ~dir (m : View.t) (xs : View.t list) : t =
  if xs = [] then
    invalid_arg "Maxmin.make: the maximum/minimum of an empty array is undefined";
  let orient v = match dir with Max -> v | Min -> View.negate v in
  let m = slot_of store (orient m) in
  let xs = Array.of_list (List.map (fun v -> slot_of store (orient v)) xs) in
  let vlo, vhi = threshold_range m xs in
  let shape =
    match shape with
    | `Per_value ->
        Per_value
          (Array.init
             (max 0 (vhi - vlo + 1))
             (fun k -> Option.map Explanation.clause (clause_lits m xs (vlo + k))))
    | `Selector ->
        Selector { sel_rows = [||]; sel_clause = -1; cache = Hashtbl.create 16 }
  in
  let vars =
    List.sort_uniq Var.compare
      (List.concat_map (fun s -> View.vars s.view) (m :: Array.to_list xs))
  in
  { m; xs; vlo; vhi; shape; vars }

let is_selector t = match t.shape with Selector _ -> true | Per_value _ -> false

(* The rows compile.ml posts for the per-value shape, one clause per threshold, in
   increasing v. The selector shape posts [selector_rows] instead and has none. *)
let rows t =
  match t.shape with
  | Selector _ -> []
  | Per_value expls ->
      Array.to_list expls
      |> List.filter_map (function
           | None -> None
           | Some e -> (
               match Explanation.force e with
               | Explanation.Clause ls -> Some ls
               | _ -> None))

let n_rows t =
  match t.shape with
  | Selector _ -> 0
  | Per_value expls ->
      Array.fold_left (fun n e -> if Option.is_some e then n + 1 else n) 0 expls

(* ---------------------------------------------------------------- the selector shape *)

(* A slot's view as (sign, offset): the view's value is [sign * base + offset], and a
   constant is sign 0. Only +-1 occurs ([Lit.affine]). *)
let sign s =
  match s.view with
  | View.Const _ -> 0
  | View.Affine _ -> if s.map.Lit.negated then -1 else 1

let offset s = match s.view with View.Const c -> c | View.Affine _ -> s.map.Lit.offset

let same_view a b =
  sign a <> 0 && sign a = sign b && a.name = b.name && offset a = offset b

(* The disjunction holds by declaration: the threshold range is empty (D-0095), or m is
   itself one of the operands. Nothing is posted and no rule can fire (R3 needs
   max hi(x) < hi(m), R4 a reacher other than m, the conflict max hi(x) < lo(m)). *)
let selector_vacuous t = t.vlo > t.vhi || Array.exists (same_view t.m) t.xs

type selector_row = {
  sr_terms : (int * string) list; (* base coefficients on the FlatZinc names *)
  sr_big_m : int; (* the selector's coefficient, M_i >= 1 *)
  sr_rhs : int; (* terms + M_i b_i <= rhs *)
}

(* S_i on the bases, operand order: [view_m - view_x_i + M_i b_i <= M_i] with each view
   [sign * base + offset], so the terms are [(sign m, m)] and [(-sign x_i, x_i)] and the
   offsets move to the right-hand side. [] when [selector_vacuous]. A base shared by m
   and an operand under DIFFERENT views would merge two terms into one and break the
   unit coefficients every derivation below relies on; compile.ml cannot build one
   (its views are identity, or all negated for a minimum), so it is refused. *)
let selector_rows t =
  if selector_vacuous t then []
  else
    Array.to_list
      (Array.map
         (fun x ->
           if sign x <> 0 && sign t.m <> 0 && x.name = t.m.name then
             invalid_arg "Maxmin.selector_rows: m and an operand share a base";
           let term s c = if sign s = 0 then [] else [ (c * sign s, s.name) ] in
           let big_m = t.m.dhi - x.dlo in
           {
             sr_terms = term t.m 1 @ term x (-1);
             sr_big_m = big_m;
             sr_rhs = big_m - offset t.m + offset x;
           })
         t.xs)

let attach_selectors t ~rows ~clause =
  match t.shape with
  | Per_value _ -> invalid_arg "Maxmin.attach_selectors: a per-value instance"
  | Selector sel ->
      if List.length rows <> Array.length t.xs then
        invalid_arg "Maxmin.attach_selectors: one row per operand";
      sel.sel_rows <- Array.of_list rows;
      sel.sel_clause <- clause

(* The operand a solution selects: the first whose S_i holds with b_i = 1, i.e. the
   first attaining m (in max coordinates, view_m <= view_x_i). Read by
   lib/proof/encoding.ml's choice group, through a closure compile.ml builds, to list
   b_j and ~b_i in `sol`/`soli` (D-0134 section 2.4, probes a6-a8: with a tie neither
   selector is propagated and the checker refuses the solution). A wrong solution picks
   the largest operand; its `sol` is refused on the rows anyway (a10). *)
let chosen t (value_of : string -> int) =
  let value s =
    match s.view with
    | View.Const c -> c
    | View.Affine _ -> Lit.apply s.map (value_of s.name)
  in
  let vm = value t.m in
  let best = ref 0 in
  let found = ref None in
  Array.iteri
    (fun i x ->
      let vx = value x in
      if !found = None && vm <= vx then found := Some i;
      if vx > value t.xs.(!best) then best := i)
    t.xs;
  match !found with Some i -> i | None -> !best

(* One operand's part of C_v (D-0134 section 2.3): S_i, m's bound at m >= m_bound and
   x_i's at x_i <= x_bound, each a [Linear_term] with S_i's own base coefficient, so
   lib/core/justify.ml renders the bridge (or the declared bound line) of each and
   divides by D_i = m_bound - x_bound >= 1. A constant contributes no term. *)
let selector_part t row x ~v =
  let m_bound = max v t.m.dlo and x_bound = min (v - 1) x.dhi in
  let term s ~coeff ~bound =
    if sign s = 0 then []
    else
      [
        Explanation.linear_term ~coeff ~name:s.name ~decl_lo:s.bdlo ~decl_hi:s.bdhi
          ~value:(sign s * (bound - offset s))
          [];
      ]
  in
  Explanation.combine
    (Explanation.term 1 (Explanation.model_row row)
     :: term t.m ~coeff:(sign t.m) ~bound:m_bound
    @ term x ~coeff:(-sign x) ~bound:x_bound)
    (m_bound - x_bound)

let selector_expl t sel v =
  match Hashtbl.find_opt sel.cache v with
  | Some e -> e
  | None ->
      if Array.length sel.sel_rows <> Array.length t.xs then
        invalid_arg "Maxmin: the selector rows were never attached (compile.ml's job)";
      let e =
        Explanation.deferred (fun () ->
            Explanation.resolve
              (Array.to_list
                 (Array.mapi (fun i x -> selector_part t sel.sel_rows.(i) x ~v) t.xs)
              @ [ Explanation.model_row sel.sel_clause ]))
      in
      Hashtbl.add sel.cache v e;
      e

(* C_v as an explanation. A threshold outside the posted range, or a vacuous one, is a
   bug in the rule that chose it (the header argues each rule's v is in range), and it is
   raised rather than rendered: a `rup` over a clause the .opb does not hold would verify
   only by luck, and a selector derivation outside the range would divide by a D_i the
   rows do not support. *)
let expl_at t v =
  if v < t.vlo || v > t.vhi then
    invalid_arg (Printf.sprintf "Maxmin: threshold %d is outside the posted rows" v)
  else
    match t.shape with
    | Selector sel ->
        if selector_vacuous t then
          invalid_arg
            (Printf.sprintf "Maxmin: the disjunction is vacuous, yet C_%d was asked" v)
        else selector_expl t sel v
    | Per_value expls -> (
        match expls.(v - t.vlo) with
        | Some e -> e
        | None ->
            invalid_arg (Printf.sprintf "Maxmin: C_%d is vacuous and was not posted" v))

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
