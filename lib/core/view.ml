(* Views: [+/-x + k] over a store variable, and constants as first-class views.
   M4-T0. Consistency level: none of its own -- a view is not a constraint, it is a
   lens. Governed by docs/SPEC.md section 2.1 (what the front end may present) and
   docs/PROOF-FORMAT.md section 3 (how it reaches the proof).

   WHY THIS EXISTS, and why the obvious alternative is worse.

   A 1-based [array_int_element] index, a [c - x] term, a reversed objective: each is
   an affine image of a variable. The alternative is an AUXILIARY VARIABLE plus a
   channelling constraint [y = x + 1]. It looks equivalent and is not. The auxiliary
   variable has its own domain, so every value-consistent propagator downstream of it
   reasons about [y] and then has to get its pruning back to [x] through the
   channelling row -- which is a bounds-consistent step. The consistency is lost at
   the channel, silently, and the symptom is a slower search rather than a wrong
   answer. docs/ROADMAP.md's M4-T0 row records what that cost GCS on one family; the
   figure there is theirs and is not re-measured here, so it is cited as the reason
   for the shape and not as a number this project has confirmed.

   A view has no domain of its own. It has no store slot, no trail slot, and no PB
   variable. Everything it does is a translation of one integer:

       value  v = s*x + k         (s = +/-1, carried as [Lit.affine])
       read   view.lo = apply(x.lo) or apply(x.hi), whichever the sign puts lower
       write  view >= b           IS   x >= b-k    (s=+1)
                                  IS   x <= k-b    (s=-1)
       proof  [view >= b]         IS   the literal [x_ge_(b-k)] (or its negation)

   THE THREE CONSEQUENCES THAT MATTER, because each is an invariant it would be easy
   to break by adding state here.

   1. Pruning through a view moves the BASE, through [Store]'s ordinary mutators, so
      it pushes exactly one ordinary trail entry against the base variable. A view
      cannot smuggle a second trail past I-T1/I-X4, because there is nothing here to
      put one in.

   2. Reading a view reads the base's LIVE domain. The two directions are the same
      array cell, not two cells kept in step, so there is no link to fall out of
      step -- which is the failure a channelling constraint has and this does not.

   3. The proof side agrees with the solver side BY SHARING THE TRANSFORM. The
      [Lit.affine] in a view here is the very record [Lit.view_ge] and
      [Encoding.view_ge] render from. A propagator that prunes [view >= b] and the
      checker that reads [x_ge_(b-k)] are computing from one value, not from two
      copies of a rule. See lib/proof/lit.ml's "Views" section for why the base's
      literals are reused rather than fresh ones minted.

   CONSTANTS. [Const c] is a view with no base. It is here rather than in [Store]
   because a constant needs none of what a store slot provides: no domain to narrow,
   no trail entry to undo, no order ladder in the .opb. Every operation below has a
   [Const] arm that is the SAME operation on a one-value domain -- [lo = hi = c],
   [mem c v] is [v = c], a narrowing that keeps [c] is [Unchanged] and one that
   excludes it is a [Conflict] reported through [Store.conflict], the same call a
   propagator makes. The rule the arms are written to: a constant is a special case
   of the ARITHMETIC and of nothing else. If a caller has to ask [is_const] before it
   can do something, that something has been written wrong. *)

module Lit = Baguette_proof.Lit
module Encoding = Baguette_proof.Encoding

type t = Const of int | Affine of { base : Var.t; map : Lit.affine }

(* -------------------------------------------------------------- construction *)

let of_var v = Affine { base = v; map = Lit.identity }
let const c = Const c

(* [view + k] and [-view], FLATTENED: a view of a view is a view. That is what keeps
   the representation one constructor deep, so nothing downstream ever recurses. *)
let shift v k =
  match v with
  | Const c -> Const (c + k)
  | Affine { base; map } -> Affine { base; map = Lit.shift map k }

let negate = function
  | Const c -> Const (-c)
  | Affine { base; map } -> Affine { base; map = Lit.flip map }

(* [k - view], the common spelling of a reversed term. *)
let sub_from k v = shift (negate v) k
let is_const = function Const _ -> true | Affine _ -> false
let base_var = function Const _ -> None | Affine { base; _ } -> Some base
let map_of = function Const _ -> None | Affine { map; _ } -> Some map

(* True when the view is its base unchanged, so a caller may treat it as the variable
   itself. Purely an optimisation hook: every function below is already correct on
   the identity view. *)
let is_plain_var = function
  | Const _ -> false
  | Affine { map; _ } -> Lit.is_identity map

let equal a b =
  match (a, b) with
  | Const x, Const y -> Int.equal x y
  | Affine a, Affine b -> Var.equal a.base b.base && Lit.affine_equal a.map b.map
  | Const _, Affine _ | Affine _, Const _ -> false

let compare a b =
  match (a, b) with
  | Const x, Const y -> Int.compare x y
  | Const _, Affine _ -> -1
  | Affine _, Const _ -> 1
  | Affine a, Affine b ->
      let c = Var.compare a.base b.base in
      if c <> 0 then c else Lit.affine_compare a.map b.map

(* The variables a view actually reads, for a propagator's [vars] declaration. A
   constant reads none -- which is the point of I-T4's "the naming instance must also
   watch the variable the entry changed": a propagator over constants changes
   nothing, so it declares nothing. *)
let vars v = match v with Const _ -> [] | Affine { base; _ } -> [ base ]

(* ---------------------------------------------------------------------- reads *)

(* All O(1) and allocation-free: a scalar through [Lit.apply], never a domain. *)

let lo store = function
  | Const c -> c
  | Affine { base; map } ->
      let d = Store.get store base in
      if map.Lit.negated then Lit.apply map (Domain.hi d) else Lit.apply map (Domain.lo d)

let hi store = function
  | Const c -> c
  | Affine { base; map } ->
      let d = Store.get store base in
      if map.Lit.negated then Lit.apply map (Domain.lo d) else Lit.apply map (Domain.hi d)

let mem store v value =
  match v with
  | Const c -> Int.equal c value
  | Affine { base; map } -> Domain.mem (Store.get store base) (Lit.unapply map value)

let is_fixed store = function
  | Const _ -> true
  | Affine { base; _ } -> Domain.is_fixed (Store.get store base)

let value store v =
  match v with
  | Const c -> Some c
  | Affine { base; map } ->
      Option.map (Lit.apply map) (Domain.value (Store.get store base))

let size store = function
  | Const _ -> 1
  | Affine { base; _ } -> Domain.size (Store.get store base)

(* The materialising read. Off the hot path by construction -- see [Domain.affine]. *)
let domain store = function
  | Const c -> Domain.singleton c
  | Affine { base; map } ->
      Domain.affine (Store.get store base)
        ~negated:map.Lit.negated ~offset:map.Lit.offset

(* --------------------------------------------------------------------- writes *)

(* Each of these is the base's mutator at the translated bound, so the entry pushed,
   the reason recorded and the support updated are all the base's ordinary ones.
   A [Const] arm never touches the store: it decides the same question arithmetically
   and reports the same [Store.outcome]. *)

(* The [Const] failure arm goes through [Store.unattributed_conflict], which is what
   [Store.apply] itself returns when a variable's narrowing empties its domain -- NOT
   [Store.conflict]. The distinction is load-bearing and is the whole of test (d): the
   conflict a constant reports must be the same VALUE a variable reports in the same
   situation, reason included ([Reason.none], for the documented reason at
   [Store.apply]'s [Failed] arm). Reaching for [Store.conflict] here, which is the one
   that carries the pruning's own reason, would give a constant a conflict line over
   too few facts -- a claim the checker refuses -- and would do it only for constants,
   which is precisely the special case this module exists not to have. *)
let fail store (j : Reason.justified) =
  Store.Conflict (Store.unattributed_conflict store j.Reason.justification)

let set_lo store v bound j =
  match v with
  | Const c -> if bound <= c then Store.Unchanged else fail store j
  | Affine { base; map } ->
      let d = bound - map.Lit.offset in
      if map.Lit.negated then Store.set_hi store base (-d) j
      else Store.set_lo store base d j

let set_hi store v bound j =
  match v with
  | Const c -> if bound >= c then Store.Unchanged else fail store j
  | Affine { base; map } ->
      let d = bound - map.Lit.offset in
      if map.Lit.negated then Store.set_lo store base (-d) j
      else Store.set_hi store base d j

let remove store v value j =
  match v with
  | Const c -> if value <> c then Store.Unchanged else fail store j
  | Affine { base; map } -> Store.remove store base (Lit.unapply map value) j

let fix store v value j =
  match v with
  | Const c -> if value = c then Store.Unchanged else fail store j
  | Affine { base; map } -> Store.fix store base (Lit.unapply map value) j

(* ---------------------------------------------------------------------- proof *)

(* The view as the encoding sees it. The base's FlatZinc identifier comes from the
   store -- the SAME string [Encoding.declare_int] was given, which is what D-0010's
   "Store's initial domains and Encoding's declared domains must agree" requires of
   the other half of this pair.

   Note what is not here: no name is minted, no table is consulted, and nothing is
   keyed on a rendered OPB name. [Lit.sanitize] is non-injective (M2-T9); the reason
   that cannot bite a view is that a view never has a name to sanitise. *)
let to_encoding store = function
  | Const c -> Encoding.view_const c
  | Affine { base; map } -> Encoding.View (Store.name store base, map)

(* The literal for [view >= n] / [view <= n], untrimmed -- the pure form. A caller
   that needs the declared bounds taken into account wants [Encoding.view_ge], which
   returns [Holds]/[Fails] where there is no literal to name. *)
let lit_ge store v n =
  match v with
  | Const _ -> None
  | Affine { base; map } -> Some (Lit.view_ge (Store.name store base) map n)

let lit_le store v n =
  match v with
  | Const _ -> None
  | Affine { base; map } -> Some (Lit.view_le (Store.name store base) map n)

let to_string store v =
  match v with
  | Const c -> Printf.sprintf "%d" c
  | Affine { base; map } ->
      let x = Store.name store base in
      let body = if map.Lit.negated then "-" ^ x else x in
      if map.Lit.offset = 0 then body
      else if map.Lit.offset > 0 then Printf.sprintf "%s+%d" body map.Lit.offset
      else Printf.sprintf "%s-%d" body (-map.Lit.offset)
