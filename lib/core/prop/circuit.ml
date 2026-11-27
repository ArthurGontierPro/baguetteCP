(* circuit(succ): the successors succ_u of the nodes root, root + 1, ..., root + n - 1
   form ONE cycle through every node. Reaches the solver as
   `baguette_circuit(succ, pos, root)` through mznlib/fzn_circuit.mzn, which also posts
   all_different(succ) (lib/core/prop/alldiff.ml, its own instance) and the domain
   restrictions succ_u in S, succ_u <> u.

   Consistency level: CHECKING ([consistency] below), plus Chuffed's subtour `prevent`
   rule. Governed by docs/SPEC.md 3.2 (consistency levels) and 3.3 (explanations). Proof
   shape: a position pinned along a fixed arc is one `rup` against one MTZ row, and a
   subtour cut is ONE `pol` written ahead of its trace line. The cut sums several rows, so
   the family is [Needs_derivation] in the I-X10 classification table of
   test/unit/test_trace.ml (a pruning that rests on several model constraints and must
   put its cutting-planes derivation on the page before its trace line).

   docs/DECISIONS.md D-0217 is this module's record: circuit as a native propagator over
   Miller-Tucker-Zemlin position variables, built by M18-coverage-T3.

   ---------------------------------------------------------------------------
   The .opb rows: Miller-Tucker-Zemlin positions, the DEFINITION of the constraint
   ---------------------------------------------------------------------------

   [pos] holds one POSITION variable per node other than the root, declared 1..n-1 by the
   library (store variables, as table's selectors are); the root's position is the
   constant 0. With G(u, v) = `n ~[succ_u >= v] + n [succ_u >= v+1]` the GUARD of the arc
   u -> v over succ_u's ORDER literals (a literal a declared bound makes constant dropped,
   no guard at all for a constant successor), lib/flatzinc/compile.ml's [post_circuit]
   writes, for every v of succ_u's declared domain with v <> u and v in S:

     GE(u, v)   G(u, v) + pos_v - pos_u >= 1        u, v <> root
     LE(u, v)   G(u, v) + pos_u - pos_v >= -1       u, v <> root
     LE(r, v)   G(r, v) - pos_v >= -1               u = root
     END(u)     G(u, r) + pos_u >= n - 1            v = root

   pos expanded by [Encoding.linear_terms_int_lin_le], so on the bits encoding by default
   and on the order encoding under `--bits-above none`. GE alone makes a permutation one
   cycle (summed around a cycle that avoids the root, the positions cancel and 0 >= k);
   LE and END hold of every circuit (pos = the distance from the root) and give a cycle
   THROUGH the root its own one-line cut. So the .opb's solutions projected on succ are
   exactly the circuits, and nothing posted is a consequence the solver computed.

   ---------------------------------------------------------------------------
   The cut: ONE `pol`, the rows around the cycle divided by n
   ---------------------------------------------------------------------------

   For a cycle C of k < n arcs: if C avoids the root, GE over its arcs sums to
   `n * sum(guards) >= k`; if C = r -> c_1 -> ... -> c_(k-1) -> r, LE(r, c_1), ...,
   LE(c_(k-2), c_(k-1)) and END(c_(k-1)) sum to `n * sum(guards) >= n - k`. Every position
   cancels (the two rows of a node expand it identically). Divided by n, either is
   `sum(guards) >= 1`: some arc of C is not taken. [cut] builds it as one [Combine] of
   [Model_row] terms with divisor n, the "add the rows, then divide" shape D-0013 set for
   a linear pruning; no new constructor. Its literals are the
   NEGATED bound facts of the fixed arcs plus the claim `succ_e <> s`, so for an interior
   value it is literally the pruning's trace clause, and for a bound value with no hole
   next to it too.

   ---------------------------------------------------------------------------
   Consistency level: CHECKING, plus Chuffed's `prevent`
   ---------------------------------------------------------------------------

   One call, repeated until it fixes no new successor:

     R  succ_u loses the values outside S and u itself (compile.ml posts the unit rows
        when the declared domain holds them; mznlib's restrictions usually leave none).
     H  along a FIXED arc, a PINNED position pins the other: succ_r = v gives pos_v <= 1
        (LE), succ_u = r gives pos_u >= n - 1 (END), succ_u = v with pos_u fixed at a
        gives pos_v = a + 1 (GE and LE), and with pos_v fixed at b gives pos_u = b - 1.
     P  for every maximal chain s -> ... -> e of fixed arcs over k < n nodes, e unfixed,
        succ_e loses s. A closed cycle of fixed arcs shorter than n is a conflict. When
        the fixed arcs put two arcs into one node (all_different's to refute), P waits.

   With every variable fixed each row is one arc between two pinned positions, and H
   refutes a violated one: that is [Checking]. P is the reasoning Chuffed's circuit runs
   without its SCC check; the matching's strength on succ is all_different's instance.
   When the whole circuit is fixed H fixes every position from the root, so the positions
   need no search there. The advisor wakes the instance on a FIXED variable only, because
   R ran at the first call and H and P read fixed arcs and pinned positions only (I-P7: an
   advisor may drop a wake only when a run then would change nothing).

   ---------------------------------------------------------------------------
   The proof
   ---------------------------------------------------------------------------

     R  `rup` of the claim against its unit row, no facts (a bound value carries the bound
        fact that pins it, as inverse.ml's [remove]).
     H  `rup claim \/ ~facts` against ONE row, the facts the arc's two bound facts and the
        premise's two. Only PINNED premises, on purpose: over bits, unit propagation turns
        `x >= c` and `x <= c` into every bit of x (top bit down, one of the two forces
        it) and `x >= c`, `x <= c - 1` into a conflict, so the line is RUP; a premise that
        is only a bound is not RUP over bits in general. This part alone would be
        [Single_row].
     P  the facts are the chain's arcs (two bound facts each), the derivation the cut over
        the chain plus e -> s, made under [Store.deriving_ahead]: Trace writes the `pol`
        ahead and `rup claim \/ ~facts` follows from it by unit propagation. A closed
        short cycle is a conflict on its arcs with the same derivation ahead. This part
        is what makes the family [Needs_derivation], as alldiff and gcc are.

   A value that would empty a position is reported as a conflict on the premise plus the
   facts excluding the value (its weakest bound or its hole's remover), never through
   [Store.apply]'s failing arm (element.ml's rule). The scan is O(n) per call plus the
   prunings; it allocates the reasons of the prunings it makes. *)

module Lit = Baguette_proof.Lit

(* A successor or a position: a variable with its DECLARED bounds, or a constant the
   flattener left. *)
type cell = Fixed of int | Cell of { var : Var.t; name : string; dlo : int; dhi : int }

type t = {
  n : int;
  root : int;
  succ : cell array; (* succ.(k) is the successor of node root + k *)
  pos : cell array; (* pos.(k - 1) is the position of node root + k, k >= 1 *)
  ge : int array; (* ge.(k * n + j): GE(root+k, root+j)'s id, or -1 *)
  le : int array; (* le.(k * n + j): LE, or for j = 0 the END row; -1 when none *)
  vars : Var.t list;
  (* Scratch, reused by every call. *)
  next : int array; (* the fixed successor's node offset, -1 when unfixed *)
  pred : int array;
  seen : int array;
  mutable stamp : int;
}

let make ~root ~succ ~pos ~ge ~le =
  let n = Array.length succ in
  if n < 2 then invalid_arg "Circuit.make: fewer than two nodes";
  if Array.length pos <> n - 1 then invalid_arg "Circuit.make: not n - 1 positions";
  if Array.length ge <> n * n || Array.length le <> n * n then
    invalid_arg "Circuit.make: the row tables are not n * n";
  let vars =
    List.sort_uniq Var.compare
      (List.filter_map
         (function Cell { var; _ } -> Some var | Fixed _ -> None)
         (Array.to_list succ @ Array.to_list pos))
  in
  {
    n;
    root;
    succ;
    pos;
    ge;
    le;
    vars;
    next = Array.make n (-1);
    pred = Array.make n (-1);
    seen = Array.make n 0;
    stamp = 0;
  }

let vars t = t.vars
let name = "circuit"
let consistency = Propagator.Checking

exception Found of Store.conflict

(* The GUARD of the arc from a successor cell to [v]: the literals of the negated bound
   facts of `succ = v`, as compile.ml writes them with coefficient n. *)
let guard c v =
  match c with
  | Fixed _ -> []
  | Cell { name; dlo; dhi; _ } ->
      (if v > dlo then [ Lit.negate (Lit.ge name v) ] else [])
      @ if v < dhi then [ Lit.ge name (v + 1) ] else []

let fixed_value store = function
  | Fixed c -> Some c
  | Cell { var; _ } ->
      let d = Store.get store var in
      if Domain.is_fixed d then Some (Domain.lo d) else None

(* The facts of a fixed cell: its two bound facts (a declared one drops out when it is
   read as a literal), nothing for a constant. *)
let pin_facts c v =
  match c with
  | Fixed _ -> []
  | Cell { name; dlo; dhi; _ } -> Reason.fixed_at ~name ~decl_lo:dlo ~decl_hi:dhi v

(* The facts that exclude [v] from [c]'s live domain: the weakest bound, or the remover
   of a hole (inverse.ml's [excl]). *)
let excl store c v =
  match c with
  | Fixed _ -> []
  | Cell { var; name; dlo; dhi } -> (
      let d = Store.get store var in
      if v < Domain.lo d then [ Reason.at_least ~name ~decl:dlo (v + 1) ]
      else if v > Domain.hi d then [ Reason.at_most ~name ~decl:dhi (v - 1) ]
      else
        match Store.remover store ~before:(Store.trail_length store) ~var v with
        | None -> []
        | Some e -> Reason.facts e.Store.reason)

let clause_expl claim fs =
  Explanation.deferred (fun () ->
      Explanation.clause (claim @ List.map Lit.negate (Reason.lits_of_facts fs)))

let conflict store fs =
  Store.conflict store (Reason.because ~concludes:None fs (clause_expl [] fs))

let move = function
  | Store.Conflict c -> raise (Found c)
  | Store.Changed -> true
  | Store.Unchanged -> false

(* ---------------------------------------------------------------- the cut *)

(* The cut over the cycle [nodes] (offsets, in cycle order, every arc c_i -> c_(i+1) and
   the last back to the first): one [Combine] of the rows around it, divided by n. *)
let cut t nodes =
  let k = List.length nodes in
  let rows =
    if List.mem 0 nodes then
      (* Rotate to start at the root: LE along the path, END at its last node. *)
      let arr = Array.of_list nodes in
      let i0 =
        let rec find i = if arr.(i) = 0 then i else find (i + 1) in
        find 0
      in
      let at i = arr.((i0 + i) mod k) in
      List.init (k - 1) (fun i -> t.le.((at i * t.n) + at (i + 1)))
      @ [ t.le.(at (k - 1) * t.n) ]
    else
      let arr = Array.of_list nodes in
      List.init k (fun i -> t.ge.((arr.(i) * t.n) + arr.((i + 1) mod k)))
  in
  List.iter
    (fun cid ->
      if cid < 0 then
        invalid_arg
          "Circuit.cut: an arc of the cycle has no row; compile.ml posts one per \
           declared arc, so the cycle uses a value outside a declared domain")
    rows;
  Explanation.combine
    (List.map (fun cid -> Explanation.term 1 (Explanation.model_row cid)) rows)
    t.n

let arc_facts t nodes =
  List.concat_map (fun k -> pin_facts t.succ.(k) (t.root + t.next.(k))) nodes

(* ---------------------------------------------------------------- R *)

(* What removing [v] from [d] concludes: the settled bound when [v] is a bound, nothing
   for a hole (inverse.ml's, the same walk). *)
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

(* Remove [v] from cell [c] on the facts [why], with the derivation [expl claim fs] (fs
   the facts with the pinning bound first). Answers whether the cell became fixed. *)
let remove store c v why ~expl ~ahead =
  match c with
  | Fixed k ->
      if k = v then raise (Found (conflict store why));
      false
  | Cell { var; name; dlo; dhi } ->
      let d = Store.get store var in
      if not (Domain.mem d v) then false
      else
        let pin =
          (if v = Domain.lo d && v > dlo then [ Reason.at_least ~name ~decl:dlo v ]
           else [])
          @
          if v = Domain.hi d && v < dhi then [ Reason.at_most ~name ~decl:dhi v ] else []
        in
        let fs = pin @ why in
        if Domain.is_fixed d then raise (Found (conflict store fs));
        let claim =
          (if v > dlo then [ Lit.negate (Lit.ge name v) ] else [])
          @ if v < dhi then [ Lit.ge name (v + 1) ] else []
        in
        let j =
          Reason.because
            ~concludes:(removal_conclusion ~name ~dlo ~dhi d v)
            fs (expl claim fs)
        in
        let r =
          if ahead then Store.deriving_ahead store (fun () -> Store.remove store var v j)
          else Store.remove store var v j
        in
        ignore (move r : bool);
        Domain.is_fixed (Store.get store var)

let restrict t store k =
  let first = t.root and last = t.root + t.n - 1 and self = t.root + k in
  match t.succ.(k) with
  | Fixed c -> if c < first || c > last || c = self then raise (Found (conflict store []))
  | Cell { var; name; dlo; dhi } as c ->
      let d = Store.get store var in
      if Domain.hi d < first then
        raise (Found (conflict store [ Reason.at_most ~name ~decl:dhi (Domain.hi d) ]));
      if Domain.lo d > last then
        raise (Found (conflict store [ Reason.at_least ~name ~decl:dlo (Domain.lo d) ]));
      (if Domain.lo d < first then
         let concl = Reason.at_least ~name ~decl:dlo first in
         ignore
           (move
              (Store.set_lo store var first
                 (Reason.because ~concludes:(Some concl) []
                    (clause_expl (Option.to_list (Reason.lit_of_fact concl)) [])))
             : bool));
      (let d = Store.get store var in
       if Domain.hi d > last then
         let concl = Reason.at_most ~name ~decl:dhi last in
         ignore
           (move
              (Store.set_hi store var last
                 (Reason.because ~concludes:(Some concl) []
                    (clause_expl (Option.to_list (Reason.lit_of_fact concl)) [])))
             : bool));
      ignore (remove store c self [] ~expl:clause_expl ~ahead:false : bool)

(* ---------------------------------------------------------------- H *)

(* Pin position cell [c] to [v] on the premise facts [pf]. Answers whether it moved. *)
let pin_pos store c v pf =
  match c with
  | Fixed k ->
      if k <> v then raise (Found (conflict store pf));
      false
  | Cell { var; name; dlo; dhi } as cell ->
      let d = Store.get store var in
      if not (Domain.mem d v) then raise (Found (conflict store (pf @ excl store cell v)));
      let lo_moved =
        if Domain.lo d < v then
          let concl = Reason.at_least ~name ~decl:dlo v in
          move
            (Store.set_lo store var v
               (Reason.because ~concludes:(Some concl) pf
                  (clause_expl (Option.to_list (Reason.lit_of_fact concl)) pf)))
        else false
      in
      let d = Store.get store var in
      let hi_moved =
        if Domain.hi d > v then
          let concl = Reason.at_most ~name ~decl:dhi v in
          move
            (Store.set_hi store var v
               (Reason.because ~concludes:(Some concl) pf
                  (clause_expl (Option.to_list (Reason.lit_of_fact concl)) pf)))
        else false
      in
      lo_moved || hi_moved

(* The position of node offset [k] when it is pinned, the root's being the constant 0. *)
let pos_value t store k = if k = 0 then Some 0 else fixed_value store t.pos.(k - 1)
let pos_facts t k v = if k = 0 then [] else pin_facts t.pos.(k - 1) v

(* Every fixed arc, against its two ends, until nothing moves. The root's out-arc and the
   arcs into the root need no pinned premise (LE(r, v) and END hold the bound alone). *)
let positions t store =
  let n = t.n in
  let changed = ref true in
  while !changed do
    changed := false;
    for k = 0 to n - 1 do
      let j = t.next.(k) in
      if j >= 0 then
        let af = pin_facts t.succ.(k) (t.root + j) in
        if j = 0 then (
          if
            (* END: pos_k >= n - 1, the declared top *)
            k <> 0 && pin_pos store t.pos.(k - 1) (n - 1) af
          then changed := true)
        else if k = 0 then (
          if
            (* LE(r, j): pos_j <= 1, the declared bottom *)
            pin_pos store t.pos.(j - 1) 1 af
          then changed := true)
        else (
          (match pos_value t store k with
          | Some a ->
              if pin_pos store t.pos.(j - 1) (a + 1) (af @ pos_facts t k a) then
                changed := true
          | None -> ());
          match pos_value t store j with
          | Some b ->
              if pin_pos store t.pos.(k - 1) (b - 1) (af @ pos_facts t j b) then
                changed := true
          | None -> ())
    done
  done

(* ---------------------------------------------------------------- P *)

(* Read the fixed arcs into [next] and [pred]; [false] when two fixed arcs enter one
   node (or a value is outside S or a self-loop, which R refutes first). *)
let read_arcs t store =
  let n = t.n in
  Array.fill t.next 0 n (-1);
  Array.fill t.pred 0 n (-1);
  let ok = ref true in
  for k = 0 to n - 1 do
    match fixed_value store t.succ.(k) with
    | Some v ->
        let j = v - t.root in
        if j < 0 || j >= n || j = k then ok := false
        else (
          t.next.(k) <- j;
          if t.pred.(j) >= 0 then ok := false else t.pred.(j) <- k)
    | None -> ()
  done;
  !ok

(* Answers whether a successor became fixed. *)
let prevent t store =
  let n = t.n in
  t.stamp <- t.stamp + 1;
  let st = t.stamp in
  let fixed_some = ref false in
  for s = 0 to n - 1 do
    if t.pred.(s) < 0 && t.next.(s) >= 0 then (
      (* A chain starts at s. *)
      let nodes_rev = ref [ s ] and e = ref s and len = ref 1 in
      t.seen.(s) <- st;
      while t.next.(!e) >= 0 do
        e := t.next.(!e);
        t.seen.(!e) <- st;
        nodes_rev := !e :: !nodes_rev;
        incr len
      done;
      if !len < n then
        let chain = List.rev !nodes_rev in
        let arcs = List.filter (fun k -> k <> !e) chain in
        let why = arc_facts t arcs in
        let expl _claim _fs = Explanation.deferred (fun () -> cut t chain) in
        if remove store t.succ.(!e) (t.root + s) why ~expl ~ahead:true then
          fixed_some := true)
  done;
  (* The nodes left with a fixed successor lie on closed cycles. *)
  for s = 0 to n - 1 do
    if t.seen.(s) <> st && t.next.(s) >= 0 then (
      let nodes_rev = ref [ s ] and x = ref t.next.(s) and len = ref 1 in
      t.seen.(s) <- st;
      while !x <> s do
        t.seen.(!x) <- st;
        nodes_rev := !x :: !nodes_rev;
        incr len;
        x := t.next.(!x)
      done;
      if !len < n then
        let nodes = List.rev !nodes_rev in
        let fs = arc_facts t nodes in
        raise
          (Found
             (Store.deriving_ahead store (fun () ->
                  Store.conflict store
                    (Reason.because ~concludes:None fs
                       (Explanation.deferred (fun () -> cut t nodes)))))))
  done;
  !fixed_some

let propagate t store =
  try
    for k = 0 to t.n - 1 do
      restrict t store k
    done;
    let again = ref true in
    while !again do
      again := false;
      let ok = read_arcs t store in
      positions t store;
      if ok && prevent t store then again := true
    done;
    Propagator.Fixpoint
  with Found c -> Propagator.Conflict c

(* The advisor (I-P7): a change wakes the instance only when it FIXES a variable. R has
   done its whole work at the first call, and H and P read fixed arcs and pinned
   positions only, so a change that fixes nothing changes no run. *)
let advisor =
  {
    Propagator.ask = (fun store v -> Domain.is_fixed (Store.get store v));
    watched = None;
  }
