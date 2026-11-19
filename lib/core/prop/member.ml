(* member(x, y): y equals some x_i. Reaches the solver as `baguette_member(x, y, b)`
   through mznlib/fzn_member_int.mzn (and fzn_member_bool.mzn, over 0..1), where [b] is
   one SELECTOR Boolean per position the library introduces; docs/DECISIONS.md D-0151
   section 3 is its design record and D-0159 its implementation, including the one place
   the implementation departs from the design (the rows, below). Governed by
   docs/SPEC.md 3.2 (consistency) and 3.3 (explanations).

   ---------------------------------------------------------------------------
   The selectors are STORE VARIABLES, as regular.ml's state flags are
   ---------------------------------------------------------------------------

   b_i means "y is matched at position i". A selector that dies is a trail entry with a
   reason like any other, lib/core/trace.ml writes its line, and every later reason that
   would have cited it cites the tail of that line instead (D-0151 section 1's rule, which
   section 3 carries over: a selector is to member what a state flag is to regular).

   ---------------------------------------------------------------------------
   The .opb rows (lib/flatzinc/compile.ml's [post_member])
   ---------------------------------------------------------------------------

     OR            b_1 \/ ... \/ b_n
     R+(i, v)      ~b_i \/ ~[y >= v] \/ [x_i >= v]
     R-(i, v)      ~b_i \/ ~[x_i >= v] \/ [y >= v]

   for every threshold v of the union of the two declared hulls, a constant literal
   folded at a declared bound, and a row a ladder clause implies (beyond the first one past
   a hull) not written. With b_i, R+ and R- are y = x_i in the order encoding: every
   threshold agrees.

   D-0151 section 3.1 wrote the VALUE form instead, `~b_i \/ y <> v \/ x_i >= v` and
   `... \/ x_i <= v` per value v of y. D-0159 measured the case its probes did not hold
   (bench/member_spike/gen_rows_probe.py): a selector death across TWO holes of x_i inside
   y's range is not RUP over the value form -- y = v forces x_i = v, and the hole
   `x_i <> v` is a two-literal clause, so unit propagation can push y past neither the
   lowest nor the highest such hole -- and it is RUP over the bound form, which chases
   both lower bounds upward, each hole of either side pushing its own variable past it.
   Same row count to within the folding, three literals instead of four.

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
   The proof: every pruning ONE `rup`, except one shape, written ahead
   ---------------------------------------------------------------------------

     K  ~b_i. Assume b_i: R+/R- give x_i and y the same bounds; from the larger of the two
        lower bound facts, each value of the overlap is a hole of x_i or of y (its
        remover's facts on the tail), whose line pushes that variable past it and R+/R-
        the other, until the smaller upper bound fact is crossed. Disjoint hulls: the
        two bounds that separate them.
     C  b_k := 1: the other selectors' tails, so their lines fire, and OR.
        A conflict: every selector's tail.
     E  y >= lo(x_k), y <= hi(x_k), y <> v for a hole of x_k (and the same for x_k
        against y): b_k's tail, the bound fact or the hole's remover facts; R+/R- at
        one threshold, or both and the hole's line.
     S  y <> v: per position, its death's tail if it is dead, else the fact excluding v
        from x_i -- the WEAKEST bound, or the hole's remover. Assume y = v: each dead
        selector's line fires, each live one bound-excluded dies by R+/R- at v, OR forces
        what is left.

   S is one `rup` while at most ONE live position excludes v by a HOLE only: OR then
   forces that position, and its hole refutes it. Two or more cannot be done by unit
   propagation (each b_i needs its own case split: b_i /\ y = v gives x_i >= v and
   x_i <= v, and `x_i <> v` is two literals). Measured: q2 refused, q2a/q2p accepted
   (bench/member_spike/gen_rows_probe.py, D-0159). That pruning is made under
   [Store.deriving_ahead], and its justification is the derivation lib/core/trace.ml
   writes ahead of the line:

       one lemma A_i = ~b_i \/ y <> v \/ ~F_i per position (a `rup`: assume b_i and
       y = v, R+/R- pin x_i to v, F_i excludes it -- through the hole's own line), the
       death's own line for a dead position, nothing for a selector a decision killed;
       then OR + sum A_i, divided by their count: exactly the clause y <> v \/ ~F.

   So this family is [Needs_derivation] under I-X10 for that one shape and [Single_row]
   for every other (test/unit/test_trace.ml's table says so, and its derive-ahead lane
   drives the shape).

   ORDER ON THE TAIL: pinning bound facts first, then the dead selectors' tails, the
   excluding facts LAST, so test/unit/test_mutation.ml's lane that drops a line's last
   literal drops a fact the argument rests on.

   The reasons are kept on the LETTERS (x and y) by regular.ml's machinery, copied rather
   than shared (that module is not this task's to refactor): one slot per distinct
   variable of x and y, a reason under construction as stamped scratch arrays indexed by
   (slot, direction) -- the STRONGEST fact per letter and direction -- and each selector's
   tail cached with the trail entry it belongs to, read back through the entry that
   moved the selector now ([Store.hi_support] / [lo_support]), so a selector revived by a
   backtrack and moved again by a decision is cited as itself.

   A call is O(n * w) for K and O(|dom y| * live) for S, w the overlap of two hulls. *)

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

exception Found of Store.conflict

(* ------------------------------------------------------------- the reason under way *)

let start t =
  t.stamp <- t.stamp + 1;
  t.nkeys <- 0;
  t.others_rev <- []

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

let conflict store fs =
  Store.conflict store (Reason.because ~concludes:None fs (clause_expl [] fs))

let conflict_now store t =
  let fs, _, _ = finish t in
  conflict store fs

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
    if lx >= ly then add_lo t sx a else add_lo t sy a;
    if hx <= hy then add_hi t sx b else add_hi t sy b;
    for v = a to b do
      if not (mx v) then add_hole store t cx v
      else if not (my v) then add_hole store t cy v
      else invalid_arg "Member: a selector death with a value in common"
    done

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
    match
      Store.set_hi store v 0
        (Reason.because ~concludes:(Some concl) fs (clause_expl claim fs))
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
let narrow store t k ~tgt ~st ~src ~ss =
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
            if Domain.is_fixed d then raise (Found (conflict_now store t));
            let fs, _, _ = finish t in
            if
              push
                (Store.remove store var v
                   (Reason.because
                      ~concludes:(removal_conclusion ~name ~dlo ~dhi d v)
                      fs
                      (clause_expl (ne_lits ~name ~dlo ~dhi v) fs)))
            then changed := true))
        d0;
      !changed

(* Every set selector: a set one with no common value is K's conflict; then y is
   narrowed to each such x_k, and each such x_k to y (after all of them, so y is final). *)
let equalise store t =
  let changed = ref false in
  for k = 0 to size t - 1 do
    if is_set store t k then (
      if not (intersects store t.xs.(k) t.y) then (
        kill_reason store t k;
        kill store t k);
      if narrow store t k ~tgt:t.y ~st:t.slot_y ~src:t.xs.(k) ~ss:t.slot_x.(k) then
        changed := true)
  done;
  for k = 0 to size t - 1 do
    if is_set store t k then
      if narrow store t k ~tgt:t.xs.(k) ~st:t.slot_x.(k) ~src:t.y ~ss:t.slot_y then
        changed := true
  done;
  !changed

(* ------------------------------------------------------------- S: y's support *)

(* The derivation written ahead when two or more live positions exclude [v] by a hole
   only (see the header): one lemma per position, the OR row, the sum divided by the
   lemmas' count. Every literal list is computed now, at the push, from the facts as they
   stand; the thunk closes over lists and the row id, nothing live (I-X6). *)
let gap_expl t lemmas =
  Explanation.deferred (fun () ->
      Explanation.combine
        (Explanation.term 1 (Explanation.model_row t.or_row)
        :: List.map (fun lits -> Explanation.term 1 (Explanation.clause lits)) lemmas)
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
        if hole then incr holes;
        excl.(i) <- fs;
        List.iter (add_fact t) fs)
    done;
    (* Unreachable: a live position shares a value with y, which supports it. Kept as a
       conflict rather than an emptied domain, element.ml's rule. *)
    if Domain.is_fixed d then raise (Found (conflict_now store t));
    let fs, _, _ = finish t in
    let claim = ne_lits ~name ~dlo ~dhi v in
    let concludes = removal_conclusion ~name ~dlo ~dhi d v in
    if !holes < 2 then
      ignore
        (push
           (Store.remove store var v
              (Reason.because ~concludes fs (clause_expl claim fs)))
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
      let j = Reason.because ~concludes fs (gap_expl t lemmas) in
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
