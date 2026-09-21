(* int_times, int_div and int_abs: the M4 arithmetic family (roadmap M4-T4b).

   Consistency level: BOUNDS for every instance this family posts, and the level is
   [Linear]'s because every instance IS a [Linear] (or, for the guard definitions, a
   [Reif_lin_le] whose two halves are [Linear]s). See "What each one achieves" below
   for what that level does and does not buy here -- the short answer is that
   [int_abs] is bounds consistent, [int_times] is bounds consistent once the sign of
   its first operand is settled, and [int_div] is bounds consistent once its divisor
   is fixed. None of the three is claimed to be exact before that point, and
   [test_prop.ml]'s brute-force oracle asserts CONTAINMENT for them rather than
   equality, exactly as lib/core/interval.ml's own test file distinguishes its exact
   functions from [quotient_filter].

   ---------------------------------------------------------------------------
   The shape: a case split posted as ordinary rows, not a new proof rule
   ---------------------------------------------------------------------------

   x * y = z is not linear, so it has no single .opb row, and a bounds pruning that
   reads all of x, y and z at once is not the consequence of any one linear
   inequality. The classical answer is a CASE SPLIT, and the question M4-T4b has to
   answer is where that case split lives: in the proof (a derivation that resolves the
   cases, which needs a cutting-planes rule this tree does not have and an
   [Explanation] constructor that does not exist), or in the MODEL (rows that are each
   individually linear, each individually on the page, each individually cited).

   **It lives in the model.** For each value v of the case variable the .opb carries
   ordinary linear rows, guarded by big-M terms over Boolean variables that are
   themselves defined by the M3 reification machinery. That is the same device
   D-0057 chose for `b <-> C` one wave earlier, used once more:

     - the guard `b_v <-> y >= v` is an [int_lin_le_reif] over `-y <= -v`, which
       lib/proof/encoding.ml already posts as a pair of big-M rows and
       lib/core/prop/reif_lin_le.ml already propagates;
     - a guarded row `G_1 /\ ... /\ G_n  ->  (linear expression <= rhs)` is the single
       row `expr + sum_i M I_i <= rhs + (#positive guards) M`, where I_i is the guard's
       indicator (b for a positive guard, 1 - b for a negative one) and M is the
       largest value `expr - rhs` can take over the DECLARED box. Satisfy every guard
       and the cushion cancels exactly; violate one and the row degenerates to a bound
       the declared box already guarantees. [guarded_row] below is the whole of it.

   The consequence for the proof is the point of the design: **there is no new proof
   shape at all.** Every pruning is [Linear]'s, justified by [Linear]'s D-0013
   [Combine] over [Explanation.Model_row], citing a row the .opb really contains. No
   [Explanation] constructor was added and none is needed; no `pol` is written here;
   nothing in lib/core/justify.ml changed. docs/PROOF-FORMAT.md section 4's row for
   this family is therefore "as int_lin_le", and that is a claim about where the work
   went, not a gap.

   What it costs is size. A case split on a variable of declared width w posts O(w)
   rows and O(w) auxiliary Booleans per constraint, and each of those rows is expanded
   over the order encoding, which is itself width-proportional (D-0028). That is the
   reason the test models in this family keep their domains in the single digits, and
   it is a real cost, not a rounding error: `int_times` over two 0..9 variables is
   about forty rows and ten extra Booleans.

   ---------------------------------------------------------------------------
   The rows, per builtin (NORMATIVE -- these are what compile.ml posts)
   ---------------------------------------------------------------------------

   Write A(v) for the guard `y >= v`, B(v) for `y <= v`, S for `x >= 0` and ~S for
   `x <= -1`. A(lo_y) and B(hi_y) are constants and are dropped rather than posted;
   so is S when the declared domain of x does not straddle zero, in which case one of
   the two sign families disappears entirely.

   int_times(x, y, z), one group per v in [lo_y, hi_y]:

     T1  [A(v), S ]   z - v x >= 0        y >= v and x >= 0  =>  xy >= vx
     T2  [B(v), S ]   z - v x <= 0        y <= v and x >= 0  =>  xy <= vx
     T3  [A(v), ~S]   z - v x <= 0        y >= v and x <= 0  =>  xy <= vx
     T4  [B(v), ~S]   z - v x >= 0        y <= v and x <= 0  =>  xy >= vx

   At y = v both A(v) and B(v) hold, so whichever sign x has, z = v x is forced from
   two sides. The family is therefore CHECKING (propagator.ml's I-P2), which a
   relaxation such as a bare McCormick envelope over the declared box would NOT be --
   that was the first design tried and it is why the guards are there.

   int_div(x, y, q), one group per v in [lo_y, hi_y], writing d for x - v q:

     R1  [A(v), B(v), S ]    d >= 0
     R2  [A(v), B(v), S ]    d <= |v| - 1
     R3  [A(v), B(v), ~S]    d <= 0
     R4  [A(v), B(v), ~S]    d >= -(|v| - 1)
     R5  [A(v), B(v)    ]    d <= |v| - 1
     R6  [A(v), B(v)    ]    d >= -(|v| - 1)

   R5/R6 are the union of the two signed windows and add nothing once the sign of x is
   settled. They are there because until it is, R1..R4 are all cushioned and the group
   would otherwise say nothing at all about q.

   With y fixed to v <> 0, R1/R2 say 0 <= x - v q <= |v| - 1 and R3/R4 say
   -(|v| - 1) <= x - v q <= 0. As q moves, v q steps by |v|, so exactly one q lands in
   the window, and the remainder x - v q it leaves takes the sign of x. That is
   D-0033's rounding, spelled as two inequalities rather than as a call to any
   division function: see "Rounding" below.

   **Division by zero needs no special case and gets none.** At v = 0 the bound
   |v| - 1 is -1, so R2 reads `x <= -1` under the guard `x >= 0` and R4 reads
   `x >= 1` under `x <= -1`. Whichever sign x has, one of them is violated, so y = 0
   has no support and is pruned like any other value -- which is exactly what
   docs/SPEC.md section 2.1 and D-0033 require, and it falls out of the arithmetic
   rather than being arranged.

   int_abs(x, z):

     A1  []      z - x >= 0
     A2  []      z + x >= 0
     A3  [S ]    z - x <= 0
     A4  [~S]    z + x <= 0

   plus the two HULL rows `L <= z <= U` over the declared box, with U = max |x| and
   L = 0 when the box straddles zero and min |x| when it does not.

   ---------------------------------------------------------------------------
   Rounding: the relation truncates toward zero, the BOUNDS do not (D-0033)
   ---------------------------------------------------------------------------

   lib/core/interval.ml's header warns that these are two different roundings living a
   few functions apart, and this module is the place the warning was aimed at. The
   discipline followed here is to never let them meet:

     - the RELATION is [is_in_relation] below, and its division case is
       [Stdlib.(/)], which truncates toward zero, with [Stdlib.(mod)] taking the
       dividend's sign. test_prop.ml pins that sign behaviour against an independent
       reference rather than assuming OCaml's. It is the SOLVER's statement of the
       relation; lib/flatzinc/model.ml's [check_assignment] deliberately does not call
       it but restates it over its own exact arithmetic, and test_prop.ml asserts the
       two agree over small boxes -- see that function's own note for why sharing the
       predicate, which the roadmap row proposed, would have cost the oracle its
       independence;
     - the BOUNDS are never computed by dividing at all. R1..R4 above are
       MULTIPLICATIVE: `x - v q` compared against 0 and |v| - 1. Nothing in the rows
       divides, so there is no rounding decision in them to get backwards, and the
       outward-rounding [Interval.div_floor]/[div_ceil] are exactly what [Linear]
       already applies when it turns such a row into a bound on q.

   That is the strongest form of the guarantee available: not "we were careful to use
   the right division", but "the pruning path contains no division".

   ---------------------------------------------------------------------------
   Where M4-T4a's [Interval] is used, and one place it must NOT be
   ---------------------------------------------------------------------------

   [Interval] computes the HULL ROWS: the unguarded rows that bound z (and x) over the
   declared box, which is what gives them a bound at the root rather than only once the
   case variable is fixed. [product_bounds] is exact there, [square_bounds] is what
   `x * x = z` gets (interval.ml's header: "using the general one for a square is sound
   and weak"), and [quotient_filter] gives x's row and is sound but not exact.

   It is **not** used for the guarded rows, which do no multiplication and no division
   of bounds at all -- they compare `x - v q` against constants -- and it is not used
   to size a cushion, which is an affine extreme and not a product.

   **[quotient_filter] is wrong for [int_div] and is not called there.** It filters the
   EXACT relation `x * y = z`. Truncated division is not that relation: with x in
   [1, 1] and y in [2, 2] it returns an EMPTY interval, while `1 div 2 = 0` is a
   solution. Using it would prune a supported value -- D-0033's trap reached from the
   direction the decision record does not warn about, since nothing here rounded
   anything. [div_rows] uses the one bound that survives, |q| <= max |x|.

   ---------------------------------------------------------------------------
   What each one achieves, honestly
   ---------------------------------------------------------------------------

   **Every one of these three sentences was measured, and two of them are weaker than
   the first draft of this header claimed.** test_prop.ml's [test_arith_propagation]
   compares a root fixpoint with the enumerated hull, and it asserted equality where
   this header promised it; int_abs and int_div both failed, for the reason each line
   now names. The rule the failures illustrate is one rule: **a cushioned row says
   nothing, so a group whose guards are open contributes nothing but its hull row.**

   int_abs   BOUNDS CONSISTENT at the declared box, and whenever the sign of x is
             settled. A1/A2 give z >= x and z >= -x, and note what they do NOT give:
             over a box straddling zero they yield z >= lo(x), not z >= 0, because
             [Linear] reasons over one row at a time and neither row alone says it.
             The two hull rows say it. While x straddles zero AND has been narrowed
             below its declaration, hi(z) is the DECLARED box's bound -- sound, not
             exact. test_prop.ml asserts EQUALITY on the root scenes.

   int_times SOUND, and exact once the sign of x is settled -- at which point T1/T2 (or
             T3/T4) at v = lo(y) and v = hi(y) are exactly the two corner products, and
             [Linear] takes each to its bound over the live box. While x still straddles
             zero, both sign families are cushioned and only the hull rows speak.
             test_prop.ml asserts CONTAINMENT in general and EQUALITY on the
             sign-settled scenes.

   int_div   SOUND, and exact once y is fixed AND the sign of x is settled. Fixing y
             alone is NOT enough, and that is the second measured correction: with y
             fixed at -2 and x in -7..7, R1..R4 are all cushioned on the sign, so only
             R5/R6 -- the sign-free window |x - v q| <= |v| - 1 -- fire, and they give
             q in -4..4 where the hull is -3..3. The gap is exactly truncation's
             asymmetry: the window that has no sign in it is one wider than either
             signed window. While y is not fixed at all, the family prunes what the
             guard definitions force (a value of y whose group is infeasible pushes its
             own Boolean, and the reification channels that back to y), which is real
             but is not domain-consistent filtering. test_prop.ml asserts CONTAINMENT.

   **On [Interval.quotient_filter]'s inexactness (the roadmap asks M4-T4b to decide).**
   It is not used on the pruning path at all -- see "Rounding" above -- so the ~1% gap
   M4-T4a measured (40 of 4095 small cases) neither helps nor hurts this family, and
   the answer to "does M4-T4b want a tighter algorithm?" is NO, not because the gap is
   small but because nothing here reads it. If a future row makes [int_div] filter
   through the quotient hull directly, that decision comes back open.

   ---------------------------------------------------------------------------
   The faces
   ---------------------------------------------------------------------------

   Every instance is a [Linear.t] or a [Reif_lin_le.t]; the modules below exist so that
   an instance reports THE BUILTIN THE MODEL WROTE rather than "int_lin_le", which is
   what lib/core/engine.ml's attribution check and every `--stats` line read. Same
   device, for the same reason, as [Ne.Int_ne] and [Reif_lin_le.Int_le_reif]. *)

module Lin = Linear

(* ------------------------------------------------------------------ the relation *)

type family = Times | Div | Abs

let family_name = function Times -> "int_times" | Div -> "int_div" | Abs -> "int_abs"

(* THE predicate. [is_in_relation] is the single total statement of what these three
   builtins mean on the SOLVER side: what the tests here judge a triple against, and
   what anything else in lib/ should ask rather than restating the arithmetic.

   Total: it answers for every triple of machine integers. The multiplication is
   [Checked.mul], so an overflowing product RAISES rather than wrapping (I-X8, D-0029)
   -- and a raise here would mean a wrong answer had been accepted, which is precisely
   D-0029's failure, so it is caught and reported as "not in the relation" rather than
   escaping. It cannot be a false NEGATIVE: |z| is bounded by the declared box, so a
   product too large to compute is a product too large to equal z.

   Division truncates toward zero because [Stdlib.(/)] does (docs/SPEC.md 2.1,
   D-0033), and y = 0 is simply not in the relation -- not an error, per the same
   section. *)
let is_in_relation ~(family : family) ~(args : int list) : bool =
  match (family, args) with
  | Times, [ x; y; z ] -> ( try Checked.mul x y = z with Checked.Overflow _ -> false)
  | Div, [ x; y; q ] -> y <> 0 && x / y = q
  | Abs, [ x; z ] -> z = Stdlib.abs x
  | _ ->
      invalid_arg
        (Printf.sprintf "Arith.is_in_relation: %s takes %d arguments, given %d"
           (family_name family)
           (match family with Abs -> 2 | _ -> 3)
           (List.length args))

(* The quotient and the remainder D-0033 pins, exposed by name so that a test can
   assert the rounding against an independent reference instead of against
   [Stdlib.(/)] restating itself. [None] at y = 0: there is no answer, and returning
   one would be the "relational, not an error" rule broken in the other direction. *)
let trunc_div x y = if y = 0 then None else Some (x / y)
let trunc_rem x y = if y = 0 then None else Some (x mod y)

(* ---------------------------------------------------------------- affine pieces *)

(* An operand as it reaches the row builders: a term list over variable ids plus a
   constant. A FlatZinc operand may be a literal, and folding it here rather than
   demanding a variable is what lets `int_times(x, y, 6)` post the same rows as
   `int_times(x, y, z)` with no second path to keep right. *)
type aff = { a_terms : (int * int) list; a_const : int }

let aff_var i = { a_terms = [ (1, i) ]; a_const = 0 }
let aff_const n = { a_terms = []; a_const = n }

let aff_scale k a =
  {
    a_terms = List.map (fun (c, i) -> (Checked.mul k c, i)) a.a_terms;
    a_const = Checked.mul k a.a_const;
  }

let aff_add a b =
  { a_terms = a.a_terms @ b.a_terms; a_const = Checked.add a.a_const b.a_const }

let aff_neg a = aff_scale (-1) a

(* ------------------------------------------------------------------- the guards *)

(* A guard as it survives resolution: a constant one has already been folded away by
   the caller, so what is left is a Boolean variable at a polarity. [g_pos = false]
   means the guard holds when the Boolean is 0. *)
type guard = { g_var : int; g_pos : bool }

(* A row ready for lib/flatzinc/compile.ml: `sum r_terms <= r_rhs`, over variable ids,
   in exactly the shape [Encoding.add_int_lin_le] and [Linear.make] both take. *)
type row = { r_terms : (int * int) list; r_rhs : int }

(* The largest value a term list can take over the declared box. [Checked] throughout:
   this is the product the big-M cushion is sized from and D-0029's rule is that it
   raises rather than wrapping. *)
let terms_max ~bound terms =
  List.fold_left
    (fun acc (c, i) ->
      let lo, hi = bound i in
      Checked.add acc (if c >= 0 then Checked.mul c hi else Checked.mul c lo))
    0 terms

(* `guards -> (expr <= rhs)` as one linear row. See the module header for the
   algebra; the only subtlety in the code is that a negative guard contributes
   M (1 - b), whose constant half moves to the right-hand side and cancels that
   guard's share of the cushion there -- which is why the right-hand side counts only
   the POSITIVE guards.

   M is the smallest cushion that makes a violated guard vacuous, and never less
   than 1 (a cushion of 0 would make the row unconditional). *)
let guarded_row ~bound ~(guards : guard list) (e : aff) rhs : row =
  let rhs = Checked.sub rhs e.a_const in
  match guards with
  | [] -> { r_terms = e.a_terms; r_rhs = rhs }
  | _ ->
      let m = Stdlib.max 1 (Checked.sub (terms_max ~bound e.a_terms) rhs) in
      let npos = List.length (List.filter (fun g -> g.g_pos) guards) in
      let gterms =
        List.map (fun g -> ((if g.g_pos then m else Checked.neg m), g.g_var)) guards
      in
      { r_terms = e.a_terms @ gterms; r_rhs = Checked.add rhs (Checked.mul npos m) }

(* A guard the caller resolved: statically true (drop it), statically false (drop the
   whole row), or a literal. *)
type resolved = Always | Never | Lit of guard

let resolve gs =
  let rec go acc = function
    | [] -> Some (List.rev acc)
    | Never :: _ -> None
    | Always :: rest -> go acc rest
    | Lit g :: rest -> go (g :: acc) rest
  in
  go [] gs

let emit ~bound ~guards e rhs acc =
  match resolve guards with
  | None -> acc
  | Some guards -> guarded_row ~bound ~guards e rhs :: acc

(* ------------------------------------------------------------------- the ladders *)

(* `y >= v` and `y <= v` as guards, given the declared bounds of y and the Booleans
   the front end created for it. [ge] maps a value v in [lo_y + 1, hi_y] to the index
   of the Boolean defined as `b_v <-> y >= v`; the two ends need no Boolean, since
   `y >= lo_y` and `y <= hi_y` are true of every assignment the declaration allows. *)
let at_least ~ylo ~ge v =
  if v <= ylo then Always
  else
    match List.assoc_opt v ge with
    | Some b -> Lit { g_var = b; g_pos = true }
    | None -> Never

let at_most ~yhi ~ge v =
  if v >= yhi then Always
  else
    match List.assoc_opt (v + 1) ge with
    | Some b -> Lit { g_var = b; g_pos = false }
    | None -> Never

(* The variable the case split runs over. A FlatZinc model may write `int_div(x, 3, q)`,
   and then there is exactly one case and no ladder: [Case_const] is that, spelled as
   the degenerate one-value interval rather than as a second code path, so that the
   rows posted for a constant divisor are the rows the loop below already builds and
   there is no second shape for the .opb and the propagator to disagree about. *)
type case = Case_var of int | Case_const of int

let case_bounds ~bound = function Case_var i -> bound i | Case_const c -> (c, c)

(* The sign of the dividend / first factor. [Nonneg] and [Neg] are the cases where the
   declared domain settles it and no Boolean was created. *)
type sign = Nonneg | Neg | Bit of int

let is_nonneg = function
  | Nonneg -> Always
  | Neg -> Never
  | Bit b -> Lit { g_var = b; g_pos = true }

let is_neg = function
  | Nonneg -> Never
  | Neg -> Always
  | Bit b -> Lit { g_var = b; g_pos = false }

(* ---------------------------------------------------------------------- the rows *)

(* int_times(x, y, z): T1..T4 of the header, one group per value of y.

   [x] and [z] are affine so that a constant operand folds; [y] must be a variable,
   because the case split IS its ladder. lib/flatzinc/compile.ml takes the linear path
   when y is a constant, where x * c = z is one equality and none of this is needed. *)
let times_rows ~bound ~(x : aff) ~(y : case) ~(z : aff) ~(sign : sign) ~ge : row list =
  let ylo, yhi = case_bounds ~bound y in
  let s = is_nonneg sign and ns = is_neg sign in
  let acc = ref [] in
  (* The HULL rows, and the one place [Interval] is on this path. They are unguarded
     and hold of every assignment the declaration allows, so they need no cushion, and
     they are what gives z a bound at the root instead of only once y is fixed.

     [square_bounds] and not [product_bounds] when the two factors are THE SAME
     variable: over x in [-3, 2] a product of two independent values spans [-6, 9] and
     a square spans [0, 9]. interval.ml's header makes exactly this point ("using the
     general one for a square is sound and weak"), and x * x = z is a FlatZinc model
     anyone may write. *)
  (match (x.a_terms, z.a_terms) with
  | [ (1, xi) ], _ ->
      let xb =
        let l, h = bound xi in
        Interval.make l h
      in
      let yb =
        let l, h = case_bounds ~bound y in
        Interval.make l h
      in
      let p =
        if y = Case_var xi then Interval.square_bounds xb
        else Interval.product_bounds xb yb
      in
      acc := emit ~bound ~guards:[] z p.Interval.hi !acc;
      acc := emit ~bound ~guards:[] (aff_neg z) (Checked.neg p.Interval.lo) !acc
  | _ -> ());
  (* And the other direction: what z and y say about x. [quotient_filter] is SOUND but
     not exact (interval.ml measured the gap at 40 of 4095 small cases), which is fine
     for a row -- a row only has to be true. *)
  (match x.a_terms with
  | [ (1, xi) ] when y <> Case_var xi -> (
      let yb =
        let l, h = case_bounds ~bound y in
        Interval.make l h
      in
      let zb =
        match z.a_terms with
        | [ (1, zi) ] ->
            let l, h = bound zi in
            Interval.make l h
        | [] -> Interval.make z.a_const z.a_const
        | _ -> Interval.make min_int max_int
      in
      if zb.Interval.lo <> min_int then
        match Interval.quotient_filter ~y:yb ~z:zb with
        | Interval.No_filter | Interval.Empty_because_y_zero -> ()
        | Interval.Bounds b when Interval.is_empty b -> ()
        | Interval.Bounds b ->
            acc := emit ~bound ~guards:[] x b.Interval.hi !acc;
            acc := emit ~bound ~guards:[] (aff_neg x) (Checked.neg b.Interval.lo) !acc)
  | _ -> ());
  for v = ylo to yhi do
    let d = aff_add z (aff_scale (Checked.neg v) x) in
    let a = at_least ~ylo ~ge v and b = at_most ~yhi ~ge v in
    (* z - v x >= 0, i.e. -(z - v x) <= 0 *)
    acc := emit ~bound ~guards:[ a; s ] (aff_neg d) 0 !acc;
    acc := emit ~bound ~guards:[ b; ns ] (aff_neg d) 0 !acc;
    (* z - v x <= 0 *)
    acc := emit ~bound ~guards:[ b; s ] d 0 !acc;
    acc := emit ~bound ~guards:[ a; ns ] d 0 !acc
  done;
  List.rev !acc

(* int_div(x, y, q): R1..R4 of the header. [y] must be a variable for the same reason.
   Note there is no arm for v = 0: it is in the loop like any other value, and the
   window |v| - 1 = -1 is what makes it unsatisfiable. *)
let div_rows ~bound ~(x : aff) ~(y : case) ~(q : aff) ~(sign : sign) ~ge : row list =
  let ylo, yhi = case_bounds ~bound y in
  let s = is_nonneg sign and ns = is_neg sign in
  let acc = ref [] in
  (* The hull row, and a place [Interval.quotient_filter] must NOT be used. It is the
     filter for the EXACT relation x * y = z, and truncated division is not that
     relation: for x in [1, 1] and y in [2, 2] it returns [ceil(1/2), floor(1/2)],
     which is EMPTY, while `1 div 2 = 0` is a perfectly good solution of int_div. It
     would prune a supported value -- D-0033's trap, arrived at from the direction the
     decision record does not warn about.

     What is true, and is all that is claimed here, is |q| <= max |x|: y = 0 has no
     support (see the header), so |y| >= 1, so |x / y| <= |x| whichever way it rounds.
     Sound; not exact. *)
  (match q.a_terms with
  | [ (1, _) ] ->
      let w =
        match x.a_terms with
        | [ (1, xi) ] ->
            let l, h = bound xi in
            Stdlib.max (Checked.abs l) (Checked.abs h)
        | [] -> Checked.abs x.a_const
        | _ -> -1
      in
      if w >= 0 then (
        acc := emit ~bound ~guards:[] q w !acc;
        acc := emit ~bound ~guards:[] (aff_neg q) w !acc)
  | _ -> ());
  for v = ylo to yhi do
    let d = aff_add x (aff_scale (Checked.neg v) q) in
    let w = Stdlib.abs v - 1 in
    let a = at_least ~ylo ~ge v and b = at_most ~yhi ~ge v in
    (* x >= 0:  0 <= d <= |v| - 1 *)
    acc := emit ~bound ~guards:[ a; b; s ] (aff_neg d) 0 !acc;
    acc := emit ~bound ~guards:[ a; b; s ] d w !acc;
    (* x <= -1:  -(|v| - 1) <= d <= 0 *)
    acc := emit ~bound ~guards:[ a; b; ns ] d 0 !acc;
    acc := emit ~bound ~guards:[ a; b; ns ] (aff_neg d) w !acc;
    (* R5/R6: the union of the two windows, which needs no sign at all. They are
       implied by R1..R4 in each sign case and so add no strength once the sign is
       settled -- but until it is, R1..R4 are all cushioned and these are the only
       rows in the group that say anything. Without them `int_div(x, -2, q)` with x
       straddling zero prunes q not at all. *)
    acc := emit ~bound ~guards:[ a; b ] d w !acc;
    acc := emit ~bound ~guards:[ a; b ] (aff_neg d) w !acc
  done;
  List.rev !acc

(* int_abs(x, z): A1..A4 of the header. No ladder, so no [ge] and no loop. *)
let abs_rows ~bound ~(x : aff) ~(z : aff) ~(sign : sign) : row list =
  let s = is_nonneg sign and ns = is_neg sign in
  let d = aff_add z (aff_neg x) and p = aff_add z x in
  let acc = ref [] in
  (* The hull rows. A1/A2 give z >= x and z >= -x, which over a declared box
     straddling zero is only z >= lo(x) -- NOT z >= 0, because [Linear] reasons over
     one row at a time and neither row alone says it. A3/A4 are cushioned until the
     sign settles, so without these two z keeps its declared bounds at the root. *)
  (match x.a_terms with
  | [ (1, xi) ] ->
      let xl, xh = bound xi in
      let u = Stdlib.max (Checked.abs xl) (Checked.abs xh) in
      let l =
        if xl <= 0 && 0 <= xh then 0 else Stdlib.min (Checked.abs xl) (Checked.abs xh)
      in
      acc := emit ~bound ~guards:[] z u !acc;
      acc := emit ~bound ~guards:[] (aff_neg z) (Checked.neg l) !acc
  | [] ->
      let u = Checked.abs x.a_const in
      acc := emit ~bound ~guards:[] z u !acc;
      acc := emit ~bound ~guards:[] (aff_neg z) (Checked.neg u) !acc
  | _ -> ());
  acc := emit ~bound ~guards:[] (aff_neg d) 0 !acc;
  acc := emit ~bound ~guards:[] (aff_neg p) 0 !acc;
  acc := emit ~bound ~guards:[ s ] d 0 !acc;
  acc := emit ~bound ~guards:[ ns ] p 0 !acc;
  List.rev !acc

(* ---------------------------------------------------------------------- the faces

   Six modules, three implementations, one line of real content each: an instance's
   [name] is the builtin the model wrote. A guard definition reports the same builtin
   as the rows it guards, because it is part of that constraint's decomposition and
   an attribution naming `int_lin_le_reif` there would send a reader looking for a
   reification the model does not contain. *)

module type ROW = Propagator.S with type t = Lin.t
module type GUARD = Propagator.S with type t = Reif_lin_le.t

module Times_row : ROW = struct
  type t = Lin.t

  let name = "int_times"
  let consistency = Propagator.Bounds
  let vars = Lin.vars
  let propagate = Lin.propagate
end

module Div_row : ROW = struct
  type t = Lin.t

  let name = "int_div"
  let consistency = Propagator.Bounds
  let vars = Lin.vars
  let propagate = Lin.propagate
end

module Abs_row : ROW = struct
  type t = Lin.t

  let name = "int_abs"
  let consistency = Propagator.Bounds
  let vars = Lin.vars
  let propagate = Lin.propagate
end

module Times_guard : GUARD = struct
  type t = Reif_lin_le.t

  let name = "int_times"
  let consistency = Propagator.Bounds
  let vars = Reif_lin_le.vars
  let propagate = Reif_lin_le.propagate
end

module Div_guard : GUARD = struct
  type t = Reif_lin_le.t

  let name = "int_div"
  let consistency = Propagator.Bounds
  let vars = Reif_lin_le.vars
  let propagate = Reif_lin_le.propagate
end

module Abs_guard : GUARD = struct
  type t = Reif_lin_le.t

  let name = "int_abs"
  let consistency = Propagator.Bounds
  let vars = Reif_lin_le.vars
  let propagate = Reif_lin_le.propagate
end
