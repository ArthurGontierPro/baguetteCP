(* member(x, y): y equals some x_i. Reaches the solver as `baguette_member(x, y, b)`
   through mznlib/fzn_member_int.mzn (and fzn_member_bool.mzn, over 0..1), where [b] is
   one SELECTOR Boolean per position the library introduces.

   Consistency level: DOMAIN ([consistency] below) while no variable occurs twice among x
   and y, and CHECKING for the [Aliased] packing compile.ml uses otherwise (section
   "Consistency level" below). Governed by docs/SPEC.md 3.2 (consistency levels) and 3.3
   (explanations). Proof shape: every line is ONE `rup`, and a line whose argument walks
   a hole has threshold lemmas, or a case split per selector, written ahead of it under
   [Store.deriving_ahead]. That makes the family [Needs_derivation] in the I-X10
   classification table of test/unit/test_trace.ml (a family some of whose prunings rest
   on more than one constraint and put their derivation on the page before their trace
   line).

   The records: docs/DECISIONS.md D-0151 section 3 is the design (selectors as store
   variables, reasons on the letters). D-0159 is the implementation, with the one place it
   departs from the design (the bound form of the rows, below). D-0170 (task M7-T34)
   replaced the width-proportional rows by four bound clauses and two big-M rows per
   position, the threshold clauses becoming lemmas written only where a line needs one.

   ---------------------------------------------------------------------------
   The selectors are STORE VARIABLES, as regular.ml's state flags are
   ---------------------------------------------------------------------------

   b_i means "y is matched at position i". A selector that dies is a trail entry with a
   reason like any other, lib/core/trace.ml writes its line, and every later reason that
   would have cited it cites the tail of that line instead. That is the rule D-0151
   section 1 set for regular's state flags, so that a learned clause names cells and not
   auxiliaries, and section 3 carries it over: a selector is to member what a state flag
   is to regular.

   ---------------------------------------------------------------------------
   The .opb rows (lib/flatzinc/compile.ml's [post_member]): TWO per position (M7-T34)
   ---------------------------------------------------------------------------

     OR            b_1 \/ ... \/ b_n
     B_k           ~b_k \/ [x_k >= a]    ~b_k \/ ~[x_k >= b+1]
                   ~b_k \/ [y >= a]      ~b_k \/ ~[y >= b+1]
     F_k           sum_{v=a+1..b} ([x_k >= v] + ~[y >= v]) + (b - a) ~b_k >= b - a
     G_k           the same with x_k and y swapped

   where [a, b] is the OVERLAP of the two DECLARED hulls. Under b_k both variables are in
   it (B_k), and there x_k = a + (its rungs a+1..b that hold), y the same, so F_k and G_k
   are x_k - y >= 0 and y - x_k >= 0 over the overlap's rungs only; without b_k every row
   is true. Constant literals fold (a bound clause at a declared bound is not written);
   disjoint hulls leave the one row `~b_k`; a single common value leaves B_k alone. A
   position whose x_k IS y has no rows. Six rows per position at most, whatever the
   width; the big-M rows cost 4 (b - a) + 2 literals, the threshold clauses below cost
   about 6 (b - a) -- a rung of an order-encoded variable is a literal of any linear row
   over it, so the literal mass cannot be width-free on this encoding, only smaller.
   (A row over the whole hulls, `x_k - y + M ~b_k >= 0` with M = hi y - lo x_k, was built
   first and measured: 47 M literals over the 35 Challenge instances of D-0159 section 5
   against the clauses' 22 M, D-0170.)

   Until M7-T34 the rows were the BOUND form per threshold v of the two hulls,

     R+(k, v)      ~b_k \/ ~[y >= v] \/ [x_k >= v]
     R-(k, v)      ~b_k \/ ~[x_k >= v] \/ [y >= v]

   two per threshold per position, which is the order encoding's width-proportionality
   (a justification costs in proportion to the declared width, D-0028) paid per position:
   1.39 M rows on hexagon_gcc.reload1.gen_reload, 3.77 M on gl_Map1f (D-0159 section 5).
   They are now LEMMAS, written into the proof only where a line needs one (see "The
   proof"). Each is RUP from the rows and the ladders: assume b_k, [y >= v] and ~[x_k >=
   v]. For v in a+1..b the ladders set y's rungs up to v and clear x_k's from v, so F_k's
   left side is at most (v - 1 - a) + (b - v) + 0 < b - a. For v <= a, [x_k >= v] follows
   from B_k; for v > b, ~[y >= v] does. Folded the same way: a constant literal at a
   declared bound, and a lemma a constant makes true not written.

   D-0151 section 3.1 wrote the VALUE form, `~b_i \/ y <> v \/ x_i >= v`. D-0159 measured
   that a selector death across TWO holes of x_i inside y's range is not RUP over it, and
   is over the bound form, which chases both lower bounds upward, each hole pushing its
   own variable past it. The lemmas keep the bound form for that reason.

   ---------------------------------------------------------------------------
   Consistency level: DOMAIN, and [Aliased] when it is not
   ---------------------------------------------------------------------------

   One call, at its fixpoint:

     K  b_i dies when dom(x_i) and dom(y) share no value;
     C  no live selector is a conflict (OR); one left, not yet set, is set to 1;
     E  for every selector set to 1, y and x_k are made EQUAL domain-wise (after K, so a
        set selector with no common value is a conflict, not an emptied domain);
     S  with no selector set, a value v of y with no live position holding v is removed.

   E can kill more selectors (it narrows y), so K, C, E repeat until E changes nothing;
   S cannot (a live position's common value is supported by that position). Afterwards
   every remaining value of every variable of the scope extends to a solution: v in y
   through a live position holding it (or, with selectors set, through those, which hold
   all of y); a value of x_k with b_k not set through another live position (b_k = 0);
   b_i = 1 through a common value; b_i = 0 through another live position. With two live
   positions or more nothing about the x can be pruned, and nothing is. That is domain
   consistency over (x, y, b) while no variable occurs twice among x and y; compile.ml
   packs an instance where one does as [Aliased], the same code declared [Checking]
   (x_i and x_j one variable with b_i and b_j the last two live selectors: a value of it
   outside y is unsupported and stays). Checking is unconditional: with x and y fixed
   every mismatched selector dies, and none left is the OR row's conflict.

   ---------------------------------------------------------------------------
   The proof: every line ONE `rup`, some behind threshold lemmas written ahead
   ---------------------------------------------------------------------------

   The rows propagate the SELECTOR (F_k's coefficient on ~b_k exceeds its slack once the
   x/y part is violated; B_k are clauses) and refute two bounds that cross under b_k --
   "x_k <= p and y >= q > p" violates B_k when p < a or q > b and F_k otherwise -- but
   they propagate no rung of a ladder: every rung has coefficient 1, and the slack is the
   width left. So a line whose argument walks a hole needs the threshold lemma that
   carries a bound across to the other variable, on the page before it; a line that only
   compares bounds does not. [a, b] below is the DECLARED overlap.

     K  ~b_i. Disjoint by bounds: two crossing bounds, no lemma. Otherwise assume b_i:
        between the larger lower bound fact and the smaller upper one, each value v is a
        hole of x_i or of y (its remover's facts on the tail), its OWNER. A run of one
        owner's holes walks on their lines alone; where the owner SWITCHES at v, the lemma
        at v carries the previous owner's bound to the new one (R- at v from x_i, R+ from
        y); the walk ends on two crossing bounds. It may start at either end: from the
        bottom when the owner of the first value is the variable whose lower bound the
        reason cites, or the declared overlap starts there (B_i), else with one more lemma
        there; from the top the same. Both ends free: the two walks meet at the last
        switch, whose lemma is dropped. Lemmas: one per switch, at most one more.
     C  b_k := 1: the other selectors' tails, so their lines fire, and OR. No lemma.
        A conflict: every selector's tail.
     E  y >= lo(x_k), y <= hi(x_k) (and the same for x_k against y): b_k's tail and the
        bound fact, two crossing bounds, no lemma. tgt <> v for a hole v of src: one
        lemma carries tgt >= v to src (R+ at v when tgt is y, R- when it is x_k), src's
        hole line pushes it past v, and the rows refute src >= v + 1 > tgt -- none when v
        is an end of [a, b], where B_k already bounds src.
     S  y <> v: per position, its death's tail if it is dead, else the fact excluding v
        from x_i -- the WEAKEST bound, or the hole's remover. Assume y = v: each dead
        selector's line fires, each live one bound-excluded dies on two crossing bounds,
        OR forces what is left; a hole-excluded one needs R+(i, v) (none at an end of
        [a, b]), after which its hole and the rows refute it.

   The counts are minimal for holes the reason cites; a hole whose line holds with no
   fact (declared, or punched at the root) can make one redundant -- 57 of 111 lemmas on
   satisfiable random models, test_mutation's chase lanes pin three that are not
   (bench/member_spike/fuzz_member.py, D-0170).

   The derivation ahead. A line with lemmas is made under [Store.deriving_ahead], so
   lib/core/trace.ml writes its explanation's `pol` before it: each lemma (a [Clause], so
   a `rup`) weakened back out to a constant by its literals' axioms, then the line's own
   [Clause] scaled by k = 1 + the degree the weakening cost, all divided by k. A [Combine]
   emits its terms left to right, so every lemma is on the page before the line's clause.
   The result is exactly that clause (the line's coefficients are k / k, and its degree k
   less the k - 1 the weakening cost is 1, which divides to 1), which is what a CITATION
   of the entry reads. The pruning's trace line is then RUP in sequence. No new
   [Explanation] constructor: Term, Weaken and Combine as D-0013 set them for a linear
   pruning (weaken, add, divide). The lemmas are measured load-bearing on a SATISFIABLE
   model (test/unit/test_mutation.ml's chase-start, chase-last and transfer lanes: one
   lemma deleted, the line refused at the RUP wording). A satisfiable model is required
   because over a contradictory database the checker accepts any `rup` line.

   S is still not one line when two or more LIVE positions exclude v by a HOLE only: OR
   then forces neither, and each b_i needs its own case split (D-0159, probe q2). That
   removal is the derivation D-0159 wrote ahead:

       one lemma A_i = ~b_i \/ y <> v \/ ~F_i per position (a `rup`: assume b_i and
       y = v; R+(i, v), the hole and the big-M row for a hole-excluded position, F_i or
       G_i for a bound-excluded one), the death's own line for a dead position, nothing
       for a selector a decision killed; then OR + sum A_i, divided by their count:
       exactly the clause y <> v \/ ~F -- with the hole-excluded positions' R+(i, v)
       weakened in front of it, the same way.

   The lines that only compare bounds are single-row shapes, but the lemma lines and the
   gap shape are not, so test/unit/test_trace.ml's table classifies the whole family as
   [Needs_derivation]; its derive-ahead lane drives the gap shape and test_mutation.ml's
   member-chase lanes the lemmas.

   ORDER ON THE TAIL: pinning bound facts first, then the dead selectors' tails, the
   excluding facts LAST, so test/unit/test_mutation.ml's lane that drops a line's last
   literal drops a fact the argument rests on.

   The reasons are kept on the LETTERS (x and y) by regular.ml's machinery, copied rather
   than shared (regular.ml was left as it was): one slot per distinct variable of x and
   y, a reason under construction as stamped scratch arrays indexed by (slot, direction)
   -- the STRONGEST fact per letter and direction -- and each selector's tail cached with
   the trail entry it belongs to, read back through the entry that moved the selector now
   ([Store.hi_support] / [lo_support]), so a selector revived by a backtrack and moved
   again by a decision is cited as itself.

   A call is O(n * w) for K and O(|dom y| * live) for S, w the overlap of two hulls; the
   lemmas a K line writes are as many as the holes its reason already cites.

   Cost as measured: no more than 0.32 % of the search's samples on the five Challenge
   instances profiled (elitserien_handball 7 and 11 at 20 000 nodes, three code-generator
   instances), with the proof and without, so nothing here was changed by the file-by-file
   review of M16-file-review-T3 (D-0191). Two costs are stated for whoever finds one hot.
   [support] builds a [dom] triple and closure per live position per value of y.
   [add_fact] keeps a reason's foreign facts unique by [List.mem], quadratic in their
   number, which a hole punched by a wide row makes one per other term of that row;
   element.ml's [Fact_tbl], a hashed deduplication that keeps the first-read order
   (D-0155), is the shape to copy. *)

module Lit = Baguette_proof.Lit

(* One operand: a variable with its DECLARED hull, or a constant the flattener left. *)
type cell = Fixed of int | Cell of { var : Var.t; name : string; dlo : int; dhi : int }

(* A selector's tail as this instance wrote it: [keys] packs (key, value) pairs, a key
   being [2 * slot] for a letter's lower bound and [2 * slot + 1] for its upper one;
   [others] is what is not a bound of a letter (a hole remover's facts elsewhere);
   [facts] the line's whole tail as written, for a lemma that restates the line. *)
type tail = {
  entry : Store.entry;
  keys : int array;
  others : Reason.fact list;
  facts : Reason.fact list;
}

type t = {
  xs : cell array;
  y : cell;
  sels : Var.t array;
  snames : string array;
  or_row : int; (* the id of OR in the .opb *)
  vars : Var.t list;
  slot_x : int array; (* position -> slot, -1 for a [Fixed] cell *)
  slot_y : int;
  slot_name : string array;
  slot_dlo : int array;
  slot_dhi : int array;
  slot_of_name : (string, int) Hashtbl.t;
  tails : tail option array; (* per selector *)
  live : int array; (* scratch: the live positions of one S pass *)
  (* The reason under construction, as in regular.ml. *)
  best : int array;
  seen : int array;
  keys_in : int array;
  mutable nkeys : int;
  mutable others_rev : Reason.fact list;
  mutable stamp : int;
  (* The threshold lemmas the line under construction needs on the page ahead of it,
     newest first (see the header, "The proof"). *)
  mutable lemmas_rev : Lit.t list list;
}

let make store ~xs ~y ~sels ~or_row : t =
  let n = Array.length xs in
  if Array.length sels <> n then invalid_arg "Member.make: one selector per position";
  let slot_of_name = Hashtbl.create 16 in
  let names = ref [] in
  let slot_of = function
    | Fixed _ -> -1
    | Cell { name; dlo; dhi; _ } -> (
        match Hashtbl.find_opt slot_of_name name with
        | Some s -> s
        | None ->
            let s = Hashtbl.length slot_of_name in
            Hashtbl.replace slot_of_name name s;
            names := (name, dlo, dhi) :: !names;
            s)
  in
  let slot_x = Array.map slot_of xs in
  let slot_y = slot_of y in
  let slots = Array.of_list (List.rev !names) in
  let ns = Array.length slots in
  let letters =
    List.sort_uniq Var.compare
      (List.filter_map
         (function Cell { var; _ } -> Some var | Fixed _ -> None)
         (y :: Array.to_list xs))
  in
  {
    xs;
    y;
    sels;
    snames = Array.map (Store.name store) sels;
    or_row;
    vars = letters @ Array.to_list sels;
    slot_x;
    slot_y;
    slot_name = Array.map (fun (nm, _, _) -> nm) slots;
    slot_dlo = Array.map (fun (_, lo, _) -> lo) slots;
    slot_dhi = Array.map (fun (_, _, hi) -> hi) slots;
    slot_of_name;
    tails = Array.make n None;
    live = Array.make n 0;
    best = Array.make (max (2 * ns) 1) 0;
    seen = Array.make (max (2 * ns) 1) 0;
    keys_in = Array.make (max (2 * ns) 1) 0;
    nkeys = 0;
    others_rev = [];
    stamp = 0;
    lemmas_rev = [];
  }

let vars t = t.vars
let size t = Array.length t.xs
let dead store t i = Domain.hi (Store.get store t.sels.(i)) = 0
let is_set store t i = Domain.lo (Store.get store t.sels.(i)) = 1
let dead_fact t i = Reason.at_most ~name:t.snames.(i) ~decl:1 0
let set_fact t i = Reason.at_least ~name:t.snames.(i) ~decl:0 1

(* The live domain of a cell, as lo, hi and a membership test. *)
let dom store = function
  | Fixed c -> (c, c, fun v -> v = c)
  | Cell { var; _ } ->
      let d = Store.get store var in
      (Domain.lo d, Domain.hi d, Domain.mem d)

(* The declared hull of a cell. *)
let decl = function Fixed c -> (c, c) | Cell { dlo; dhi; _ } -> (dlo, dhi)

(* The declared overlap of x_k and y, [a, b]: under b_k both are in it (the bound
   clauses, see the header), so a lemma at its ends is never needed. *)
let overlap t k =
  let (dlx, dhx), (dly, dhy) = (decl t.xs.(k), decl t.y) in
  (max dlx dly, min dhx dhy)

exception Found of Store.conflict

(* ------------------------------------------------------------- the reason under way *)

let start t =
  t.stamp <- t.stamp + 1;
  t.nkeys <- 0;
  t.others_rev <- [];
  t.lemmas_rev <- []

let is_lower_key key = key land 1 = 0

let add_key t key v =
  if t.seen.(key) <> t.stamp then (
    t.seen.(key) <- t.stamp;
    t.best.(key) <- v;
    t.keys_in.(t.nkeys) <- key;
    t.nkeys <- t.nkeys + 1)
  else if is_lower_key key then (if v > t.best.(key) then t.best.(key) <- v)
  else if v < t.best.(key) then t.best.(key) <- v

(* A bound of slot [s] ([-1]: a constant, nothing to cite), skipped at its declared
   bound, where it is no literal. *)
let add_lo t s v = if s >= 0 && v > t.slot_dlo.(s) then add_key t (2 * s) v
let add_hi t s v = if s >= 0 && v < t.slot_dhi.(s) then add_key t ((2 * s) + 1) v

(* A fact read elsewhere (a remover's, a foreign selector's): onto its letter's key when
   it names a letter of this instance, else kept once as it is. *)
let add_fact t (f : Reason.fact) =
  if Option.is_some (Reason.lit_of_fact f) then
    match Hashtbl.find_opt t.slot_of_name (Reason.fact_owner f) with
    | Some s ->
        let key = (2 * s) + if Reason.fact_is_lower f then 0 else 1 in
        add_key t key (Reason.fact_value f)
    | None -> if not (List.mem f t.others_rev) then t.others_rev <- f :: t.others_rev

let add_tail t (tl : tail) =
  let k = tl.keys in
  for j = 0 to (Array.length k / 2) - 1 do
    add_key t k.(2 * j) k.((2 * j) + 1)
  done;
  List.iter (add_fact t) tl.others

let fact_of_key t key v =
  let s = key / 2 in
  if is_lower_key key then Reason.at_least ~name:t.slot_name.(s) ~decl:t.slot_dlo.(s) v
  else Reason.at_most ~name:t.slot_name.(s) ~decl:t.slot_dhi.(s) v

(* The reason as facts (letters first, in the order first read, then the others) and as
   the packed pairs a tail caches. *)
let finish t =
  let packed = Array.make (2 * t.nkeys) 0 in
  let facts = ref (List.rev t.others_rev) in
  for j = t.nkeys - 1 downto 0 do
    let key = t.keys_in.(j) in
    let v = t.best.(key) in
    packed.(2 * j) <- key;
    packed.((2 * j) + 1) <- v;
    facts := fact_of_key t key v :: !facts
  done;
  (!facts, packed, List.rev t.others_rev)

(* ------------------------------------------------------------- the selectors' tails *)

let own t ~set i =
  let f = if set then set_fact t i else dead_fact t i in
  { entry = Store.dummy_entry; keys = [||]; others = [ f ]; facts = [ f ] }

let is_own (tl : tail) = tl.entry == Store.dummy_entry

(* The tail of the line that killed (set, if [~set]) selector i, as THIS instance wrote
   it; or the selector's own fact when anything else moved it. *)
let sel_tail store t ~set i : tail =
  let v = t.sels.(i) in
  let pos = if set then Store.lo_support store v else Store.hi_support store v in
  if pos = Store.no_support then own t ~set i
  else
    let e = Store.trail_entry store pos in
    match t.tails.(i) with Some tl when tl.entry == e -> tl | _ -> own t ~set i

let add_sel store t ~set i = add_tail t (sel_tail store t ~set i)

(* The facts behind the hole [v] of a cell: those of the entry that punched it. [None]
   from [Store.remover] is a declared hole with no entry, which lib/ does not produce;
   citing nothing there is what element.ml, regular.ml and trace.ml do. *)
let hole_facts store c v =
  match c with
  | Fixed _ -> []
  | Cell { var; _ } -> (
      match Store.remover store ~before:(Store.trail_length store) ~var v with
      | None -> []
      | Some e -> Reason.facts e.Store.reason)

let add_hole store t c v = List.iter (add_fact t) (hole_facts store c v)

(* The facts that exclude [v] (known not in the live domain) from cell [c]: the WEAKEST
   bound, or the hole's remover; nothing for a constant, whose rows fold. The second
   component says it was a hole: the shape S cannot discharge in one line twice. *)
let excl_facts store c v =
  match c with
  | Fixed _ -> ([], false)
  | Cell { var; name; dlo; dhi } ->
      let d = Store.get store var in
      if v < Domain.lo d then
        ((if v + 1 > dlo then [ Reason.at_least ~name ~decl:dlo (v + 1) ] else []), false)
      else if v > Domain.hi d then
        ((if v - 1 < dhi then [ Reason.at_most ~name ~decl:dhi (v - 1) ] else []), false)
      else (hole_facts store c v, true)

let clause_expl claim fs =
  Explanation.deferred (fun () ->
      Explanation.clause (claim @ List.map Lit.negate (Reason.lits_of_facts fs)))

(* ------------------------------------------------------- the threshold lemmas *)

(* [c >= v] over a cell's DECLARED hull: the constant true, the constant false, or a
   literal -- the folding compile.ml applied to the rows these lemmas used to be. *)
type glit = Tt | Ff | L of Lit.t

let ge_decl c v =
  match c with
  | Fixed k -> if k >= v then Tt else Ff
  | Cell { name; dlo; dhi; _ } ->
      if v <= dlo then Tt else if v > dhi then Ff else L (Lit.ge name v)

let neg = function Tt -> Ff | Ff -> Tt | L l -> L (Lit.negate l)
let not_b t k = Option.get (Reason.lit_of_fact (dead_fact t k))

(* A lemma's clause, or [None] when a constant literal makes it true. *)
let lemma parts =
  if List.mem Tt parts then None
  else Some (List.filter_map (function L l -> Some l | Tt | Ff -> None) parts)

(* R+(k, v)   ~b_k \/ ~[y >= v] \/ [x_k >= v]
   R-(k, v)   ~b_k \/ ~[x_k >= v] \/ [y >= v] *)
let need t = function Some l -> t.lemmas_rev <- l :: t.lemmas_rev | None -> ()

let need_plus t k v =
  need t (lemma [ L (not_b t k); neg (ge_decl t.y v); ge_decl t.xs.(k) v ])

let need_minus t k v =
  need t (lemma [ L (not_b t k); neg (ge_decl t.xs.(k) v); ge_decl t.y v ])

(* The derivation written AHEAD of a line that needs threshold lemmas: each lemma (a
   `rup`, RUP from its position's big-M row and the ladders) weakened back out to a
   constant, then the original summands scaled by [k] = 1 + the degree the weakening
   costs, the whole divided by [k * divisor]. The lemmas are on the page before the
   summands' own lines (a [Combine] emits its terms left to right), and the result is
   exactly what the summands alone derive: every coefficient is the old one times [k]
   over [k * divisor], and the degree loses less than [k] before the division (the header
   argues it). [lemmas = []] is the old [Combine] byte for byte. *)
let ahead_combine lemmas summands divisor =
  let s = List.fold_left (fun a l -> a + List.length l - 1) 0 lemmas in
  let k = s + 1 in
  let pre =
    List.concat_map
      (fun l ->
        [
          Explanation.term 1 (Explanation.clause l);
          Explanation.weaken (List.map (fun x -> (1, Lit.negate x)) l);
        ])
      lemmas
  in
  Explanation.combine
    (pre @ List.map (fun (c, e) -> Explanation.term (k * c) e) summands)
    (k * divisor)

(* A line's explanation: the bare [Clause] (one `rup`, RUP against the rows) when it needs
   no lemma, else that clause behind its lemmas. The thunk closes over lists, never over
   the live store (I-X6: an explanation reads a snapshot, never live domains). *)
let line_expl lemmas claim fs =
  match lemmas with
  | [] -> clause_expl claim fs
  | _ ->
      Explanation.deferred (fun () ->
          ahead_combine lemmas
            [
              ( 1,
                Explanation.clause (claim @ List.map Lit.negate (Reason.lits_of_facts fs))
              );
            ]
            1)

let lemmas t = List.rev t.lemmas_rev

(* Make a change (or a conflict) whose line needs lemmas under [Store.deriving_ahead], so
   lib/core/trace.ml writes the derivation before the line. *)
let ahead store lemmas f =
  match lemmas with [] -> f () | _ -> Store.deriving_ahead store f

let conflict store t fs =
  let ls = lemmas t in
  ahead store ls (fun () ->
      Store.conflict store (Reason.because ~concludes:None fs (line_expl ls [] fs)))

let conflict_now store t =
  let fs, _, _ = finish t in
  conflict store t fs

(* "c <> v" over the order literals of a variable declared on [dlo, dhi]. *)
let ne_lits ~name ~dlo ~dhi v =
  (if v > dlo then [ Lit.negate (Lit.ge name v) ] else [])
  @ if v < dhi then [ Lit.ge name (v + 1) ] else []

(* What removing [v] from [d] concludes: the settled bound when [v] is a bound
   (lib/core/prop/ne.ml's [removal_conclusion], the same walk), nothing for a hole. *)
let removal_conclusion ~name ~dlo ~dhi d v =
  if v = Domain.lo d then (
    let u = ref (v + 1) in
    while !u <= Domain.hi d && Domain.is_hole d !u do
      incr u
    done;
    Some (Reason.at_least ~name ~decl:dlo !u))
  else if v = Domain.hi d then (
    let u = ref (v - 1) in
    while !u >= Domain.lo d && Domain.is_hole d !u do
      decr u
    done;
    Some (Reason.at_most ~name ~decl:dhi !u))
  else None

let push = function
  | Store.Conflict c -> raise (Found c)
  | Store.Changed -> true
  | Store.Unchanged -> false

(* ------------------------------------------------------------- K: selector deaths *)

let intersects store cx cy =
  let lx, hx, mx = dom store cx and ly, hy, my = dom store cy in
  let b = min hx hy in
  let rec go v = v <= b && ((mx v && my v) || go (v + 1)) in
  go (max lx ly)

(* K's reason for b_i: the bounds that separate two disjoint hulls, or the larger lower
   bound, the smaller upper bound and one hole per value of the overlap. *)
let kill_reason store t i =
  start t;
  let cx = t.xs.(i) and sx = t.slot_x.(i) and cy = t.y and sy = t.slot_y in
  let lx, hx, mx = dom store cx and ly, hy, my = dom store cy in
  if lx > hy then (
    add_hi t sy hy;
    add_lo t sx (hy + 1))
  else if hx < ly then (
    add_hi t sx hx;
    add_lo t sy (hx + 1))
  else
    let a = max lx ly and b = min hx hy in
    let low_x = lx >= ly and high_x = hx <= hy in
    if low_x then add_lo t sx a else add_lo t sy a;
    if high_x then add_hi t sx b else add_hi t sy b;
    (* [owner v]: true when v is a hole of x_i (the one the reason cites), false when it
       is a hole of y *)
    let owner v =
      if not (mx v) then true
      else if not (my v) then false
      else invalid_arg "Member: a selector death with a value in common"
    in
    for v = a to b do
      if owner v then add_hole store t cx v else add_hole store t cy v
    done;
    (* The lemmas: one per SWITCH of owner, the lemma at v carrying the bound of v's
       predecessor's owner to v's. A run of one owner's holes walks on its hole lines
       alone, and the walk ends on a big-M row or a bound clause refuting two crossing
       bounds, which needs no lemma. It may start at either end: from the bottom it
       needs the owner of a to be at a already (the lower bound fact is its, or the
       declared overlap starts at a), else one more lemma at a; from the top the same
       with b. Both ends free: the two walks meet at the last switch, whose lemma is
       not needed. *)
    let ad, bd =
      let (dlx, dhx), (dly, dhy) = (decl cx, decl cy) in
      (max dlx dly, min dhx dhy)
    in
    let carry v ~from_x = if from_x then need_minus t i v else need_plus t i v in
    let su = not (a <= ad || owner a = low_x)
    and sd = not (b >= bd || owner b = high_x) in
    let switches =
      List.filter
        (fun v -> owner v <> owner (v - 1))
        (List.init (b - a) (fun j -> a + 1 + j))
    in
    let switches =
      if (not su) && not sd then
        match List.rev switches with [] -> [] | _ :: r -> List.rev r
      else switches
    in
    if su && sd then carry a ~from_x:low_x;
    List.iter (fun v -> carry v ~from_x:(owner (v - 1))) switches

(* Kill b_i on the reason under way, and cache its tail. A selector set to 1 cannot die:
   that is a conflict on the same facts plus its own tail. *)
let kill store t i =
  if is_set store t i then (
    add_sel store t ~set:true i;
    raise (Found (conflict_now store t)))
  else
    let fs, packed, others = finish t in
    let concl = dead_fact t i in
    let claim = Option.to_list (Reason.lit_of_fact concl) in
    let v = t.sels.(i) in
    let ls = lemmas t in
    match
      ahead store ls (fun () ->
          Store.set_hi store v 0
            (Reason.because ~concludes:(Some concl) fs (line_expl ls claim fs)))
    with
    | Store.Conflict c -> raise (Found c)
    | Store.Changed ->
        let e = Store.trail_entry store (Store.hi_support store v) in
        t.tails.(i) <- Some { entry = e; keys = packed; others; facts = fs }
    | Store.Unchanged -> ()

let kill_all store t =
  for i = 0 to size t - 1 do
    if (not (dead store t i)) && not (intersects store t.xs.(i) t.y) then (
      kill_reason store t i;
      kill store t i)
  done

(* ------------------------------------------------------------- C: the last selector *)

let single store t =
  let count = ref 0 and last = ref (-1) in
  for i = 0 to size t - 1 do
    if not (dead store t i) then (
      incr count;
      last := i)
  done;
  if !count = 0 then (
    start t;
    for i = 0 to size t - 1 do
      add_sel store t ~set:false i
    done;
    raise (Found (conflict_now store t)))
  else if !count = 1 && not (is_set store t !last) then (
    let k = !last in
    start t;
    for i = 0 to size t - 1 do
      if i <> k then add_sel store t ~set:false i
    done;
    let fs, packed, others = finish t in
    let concl = set_fact t k in
    let v = t.sels.(k) in
    match
      Store.set_lo store v 1
        (Reason.because ~concludes:(Some concl) fs
           (clause_expl (Option.to_list (Reason.lit_of_fact concl)) fs))
    with
    | Store.Conflict c -> raise (Found c)
    | Store.Changed ->
        let e = Store.trail_entry store (Store.lo_support store v) in
        t.tails.(k) <- Some { entry = e; keys = packed; others; facts = fs }
    | Store.Unchanged -> ())

(* ------------------------------------------------------------- E: a set selector *)

(* Narrow [tgt] (slot [st]) to [src] (slot [ss]) under b_k: its bounds to src's, then
   every value src lacks inside them, each on b_k's tail and the fact on src. *)
let narrow store t k ~tgt_is_y ~tgt ~st ~src ~ss =
  match tgt with
  | Fixed _ -> false
  | Cell { var; name; dlo; dhi } ->
      let changed = ref false in
      let ls, hs, ms = dom store src in
      let under () =
        start t;
        add_sel store t ~set:true k
      in
      let bound concl move =
        let fs, _, _ = finish t in
        let j =
          Reason.because ~concludes:(Some concl) fs
            (clause_expl (Option.to_list (Reason.lit_of_fact concl)) fs)
        in
        if push (move j) then changed := true
      in
      if Domain.lo (Store.get store var) < ls then (
        under ();
        add_lo t ss ls;
        bound (Reason.at_least ~name ~decl:dlo ls) (Store.set_lo store var ls));
      if Domain.hi (Store.get store var) > hs then (
        under ();
        add_hi t ss hs;
        bound (Reason.at_most ~name ~decl:dhi hs) (Store.set_hi store var hs));
      let d0 = Store.get store var in
      Domain.iter
        (fun v ->
          let d = Store.get store var in
          if (not (ms v)) && Domain.mem d v then (
            under ();
            if v = Domain.lo d then add_lo t st v;
            if v = Domain.hi d then add_hi t st v;
            add_hole store t src v;
            (* tgt = v under b_k: one lemma carries tgt >= v to src, src's hole line
               pushes src past v, and the big-M row refutes src >= v + 1 > tgt. *)
            (let ad, bd = overlap t k in
             if ad < v && v < bd then
               if tgt_is_y then need_plus t k v else need_minus t k v);
            if Domain.is_fixed d then raise (Found (conflict_now store t));
            let fs, _, _ = finish t in
            let ls = lemmas t in
            if
              push
                (ahead store ls (fun () ->
                     Store.remove store var v
                       (Reason.because
                          ~concludes:(removal_conclusion ~name ~dlo ~dhi d v)
                          fs
                          (line_expl ls (ne_lits ~name ~dlo ~dhi v) fs))))
            then changed := true))
        d0;
      !changed

(* Every set selector: a set one with no common value is K's conflict; then y is
   narrowed to each such x_k, and each such x_k to y (after all of them, so y is
   final). *)
let equalise store t =
  let changed = ref false in
  for k = 0 to size t - 1 do
    if is_set store t k then (
      if not (intersects store t.xs.(k) t.y) then (
        kill_reason store t k;
        kill store t k);
      if
        narrow store t k ~tgt_is_y:true ~tgt:t.y ~st:t.slot_y ~src:t.xs.(k)
          ~ss:t.slot_x.(k)
      then changed := true)
  done;
  for k = 0 to size t - 1 do
    if is_set store t k then
      if
        narrow store t k ~tgt_is_y:false ~tgt:t.xs.(k) ~st:t.slot_x.(k) ~src:t.y
          ~ss:t.slot_y
      then changed := true
  done;
  !changed

(* ------------------------------------------------------------- S: y's support *)

(* The derivation written ahead when two or more live positions exclude [v] by a hole
   only (see the header): one lemma per position, the OR row, the sum divided by the
   lemmas' count. Every literal list is computed now, at the push, from the facts as they
   stand; the thunk closes over lists and the row id, nothing live (I-X6). *)
let gap_expl t ~pre lemmas =
  let or_row = t.or_row in
  Explanation.deferred (fun () ->
      ahead_combine pre
        ((1, Explanation.model_row or_row)
        :: List.map (fun lits -> (1, Explanation.clause lits)) lemmas)
        (List.length lemmas))

let remove_y store t ~var ~name ~dlo ~dhi v =
  let d = Store.get store var in
  if Domain.mem d v then (
    start t;
    if v = Domain.lo d then add_lo t t.slot_y v;
    if v = Domain.hi d then add_hi t t.slot_y v;
    for i = 0 to size t - 1 do
      if dead store t i then add_sel store t ~set:false i
    done;
    let holes = ref 0 in
    let excl = Array.make (size t) [] in
    for i = 0 to size t - 1 do
      if not (dead store t i) then (
        let fs, hole = excl_facts store t.xs.(i) v in
        if hole then (
          incr holes;
          let ad, bd = overlap t i in
          if ad < v && v < bd then need_plus t i v);
        excl.(i) <- fs;
        List.iter (add_fact t) fs)
    done;
    (* Unreachable: a live position shares a value with y, which supports it. Kept as a
       conflict rather than an emptied domain, element.ml's rule. *)
    if Domain.is_fixed d then raise (Found (conflict_now store t));
    let fs, _, _ = finish t in
    let claim = ne_lits ~name ~dlo ~dhi v in
    let concludes = removal_conclusion ~name ~dlo ~dhi d v in
    let pre = lemmas t in
    if !holes < 2 then
      ignore
        (push
           (ahead store pre (fun () ->
                Store.remove store var v
                  (Reason.because ~concludes fs (line_expl pre claim fs))))
          : bool)
    else
      let lemmas =
        List.filter_map
          (fun i ->
            let not_b = Option.get (Reason.lit_of_fact (dead_fact t i)) in
            if dead store t i then
              let tl = sel_tail store t ~set:false i in
              if is_own tl then None
              else Some (not_b :: List.map Lit.negate (Reason.lits_of_facts tl.facts))
            else
              Some ((not_b :: claim) @ List.map Lit.negate (Reason.lits_of_facts excl.(i))))
          (List.init (size t) Fun.id)
      in
      let j = Reason.because ~concludes fs (gap_expl t ~pre lemmas) in
      ignore
        (push (Store.deriving_ahead store (fun () -> Store.remove store var v j)) : bool))

let support store t =
  match t.y with
  | Fixed _ -> ()
  | Cell { var; name; dlo; dhi } ->
      let nl = ref 0 in
      for i = 0 to size t - 1 do
        if not (dead store t i) then (
          t.live.(!nl) <- i;
          incr nl)
      done;
      let supported v =
        let rec go j =
          j < !nl
          &&
          let _, _, m = dom store t.xs.(t.live.(j)) in
          m v || go (j + 1)
        in
        go 0
      in
      Domain.iter
        (fun v -> if not (supported v) then remove_y store t ~var ~name ~dlo ~dhi v)
        (Store.get store var)

let any_set store t =
  let rec go i = i < size t && (is_set store t i || go (i + 1)) in
  go 0

let propagate t store =
  try
    let again = ref true in
    while !again do
      kill_all store t;
      single store t;
      again := equalise store t
    done;
    if not (any_set store t) then support store t;
    Propagator.Fixpoint
  with Found c -> Propagator.Conflict c

let name = "member"
let consistency = Propagator.Domain

(* The same code over an instance that names one variable twice among x and y: the
   filtering is no longer complete, so the claim drops to [Checking] (see the header). *)
module Aliased = struct
  type nonrec t = t

  let name = name
  let consistency = Propagator.Checking
  let vars = vars
  let propagate = propagate
end
