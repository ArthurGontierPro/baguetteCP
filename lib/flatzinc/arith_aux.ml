(* The auxiliary Booleans of the arithmetic family (int_times, int_div and int_abs, added
   in M4-T4b): a SIGN Boolean `b <-> x >= 0` and a LADDER of Booleans `b_v <-> y >= v`
   over the second operand. lib/core/prop/arith.ml splits each constraint into cases over
   these Booleans, so every case is a linear row. This module is the one helper shared by
   the two readers that build a [Model.t]: lib/flatzinc/builder.ml and lib/scp/reader.ml,
   the reader of cake_pb_cp's .scp format (D-0230, task M23-inputs-T4).

   It was extracted from builder.ml VERBATIM, expressions included, because OCaml leaves
   the evaluation order of a record's fields and of a function's arguments unspecified:
   [div] below evaluates [ladder_bools y] and [sign_bool x] in whatever order the
   compiler gave the builder's text, and the variable numbering, so the proof, depends on
   it. The FlatZinc artefacts are byte-identical across the extraction (D-0230 section 5
   measures it).

   Why the auxiliaries exist, and why only the ones a row will use are created, is
   builder.ml's comment above [var_bounds] and lib/core/prop/arith.ml's header. The
   caller supplies the two things that differ between readers: how a variable's declared
   bounds are read ([bounds]) and how a fresh Boolean is made and named ([fresh]). *)

type ctx = { bounds : int -> int * int; fresh : unit -> int }

(* `b <-> x >= 0`, and only when the declared domain of x leaves the sign open. *)
let sign_bool ctx (x : Model.operand) =
  match x with
  | Model.Const _ -> None
  | Model.Var i ->
      let lo, hi = ctx.bounds i in
      if lo >= 0 || hi < 0 then None else Some (ctx.fresh ())

(* `b_v <-> y >= v` for every v strictly inside y's declared domain, smallest first.
   Written as a loop and not [List.init], because [List.init]'s evaluation order is
   unspecified and [fresh] has a side effect: a proof whose variable numbering
   changes between runs is a proof nobody can diff. *)
let ladder_bools ctx (y : Model.operand) =
  match y with
  | Model.Const _ -> []
  | Model.Var j ->
      let lo, hi = ctx.bounds j in
      let acc = ref [] in
      for v = lo + 1 to hi do
        Baguette_proof.Deadline.tick 64 (* --time-limit in the parse, D-0263 *);
        acc := (v, ctx.fresh ()) :: !acc
      done;
      List.rev !acc

(* `int_times(x, y, z)`. With a constant second factor it is c*x = z, an ordinary linear
   equality, so it needs neither ladder nor sign and gets neither (as since M4).

   Otherwise the NARROWER operand goes second. The case split runs over the second
   operand, with one guard Boolean and two to four rows per value of its declared domain
   (lib/core/prop/arith.ml), and x * y = z is symmetric, so the split may pick the
   operand with fewer values. On the Challenge the shape that matters is
   `int_times(b, y, z)` with b in 0..1 and y up to 0..10000 (mapping, carpet-cutting):
   split over y it is 10 001 groups, split over b it is two. A tie keeps the order the
   model wrote, so a model whose operands are equally wide, or whose first is the wider,
   is posted exactly as before. Not done for int_div, which is not symmetric. This was
   the fix for the mapping instances in D-0134 section 10 (M8-bits-encoding-T3
   continuation). *)
let times ctx x y z =
  let width = function
    | Model.Const _ -> 0
    | Model.Var i ->
        let lo, hi = ctx.bounds i in
        hi - lo
  in
  let x, y = if width x < width y then (y, x) else (x, y) in
  let aux =
    match y with
    | Model.Const _ -> { Model.x_sign = None; y_ge = [] }
    | Model.Var _ ->
        let x_sign = sign_bool ctx x in
        { Model.x_sign; y_ge = ladder_bools ctx y }
  in
  Model.Int_times (x, y, z, aux)

(* `int_div(x, y, q)` keeps its sign split whatever the divisor is, because division
   rounds toward zero (D-0033, after SPEC 2.1), so the sign of x decides which way the
   quotient is truncated. It drops both auxiliaries only when both operands are constants
   and the quotient is a number. *)
let div ctx x y q =
  let aux =
    match (x, y) with
    | Model.Const _, Model.Const _ -> { Model.x_sign = None; y_ge = [] }
    | _ -> { Model.x_sign = sign_bool ctx x; y_ge = ladder_bools ctx y }
  in
  Model.Int_div (x, y, q, aux)

(* `int_abs(x, z)`: z = |x|, with the sign of x split when its domain leaves it open. *)
let abs ctx x z = Model.Int_abs (x, z, { Model.x_sign = sign_bool ctx x; y_ge = [] })
