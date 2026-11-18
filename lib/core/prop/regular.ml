(* regular(x, Q, S, d, q0, F): the word x_0 .. x_(n-1) drives the DFA with states 1..Q,
   transition d (0 = fail) and start q0 to an accepting state in F. Reaches the solver as
   `baguette_regular(x, Q, smin, d, q0, F, s)` through mznlib/fzn_regular.mzn and
   mznlib/fzn_regular_set.mzn; docs/DECISIONS.md D-0146 is this module's record (section 3
   the design, section 4 the checker probes that settled it before a line of it existed).
   Governed by docs/SPEC.md 3.2 (consistency) and 3.3 (explanations).

   ---------------------------------------------------------------------------
   The layered graph, and the STATE FLAGS that make it a store object
   ---------------------------------------------------------------------------

   Layer i (0..n) holds the automaton's state after i letters. [s] is (n + 1) * Q
   Booleans the library introduces, s(i, q) meaning "after i letters the automaton is in
   q", and they are ORDINARY STORE VARIABLES in this propagator's scope. That is the
   design decision everything else follows from: a state that dies is a flag whose upper
   bound drops to 0, which is a trail entry with a reason like any other, and
   lib/core/trace.ml writes its line. GCS writes a cache-gated `~state[i][q]` line from
   inside the propagator for the same death (its dev_docs/regular.md); here the
   propagator writes no line at all, as every propagator in prop/ does not.

   The .opb rows (lib/flatzinc/compile.ml's [post_regular]) are the DFA's semantics and
   nothing else, over the flags' literals and the ORDER literals of x:

     ALO_i  sum_q s(i,q) >= 1          AMO_i  sum_q ~s(i,q) >= Q - 1     (i = 0..n)
     START  s(0,q0) >= 1               ACCEPT sum_{f in F} s(n,f) >= 1
     FWD(i, q, R)   ~s(i,q) \/ x_i notin R \/ s(i+1, d[q,R])      (i < n, every q, R)

   where R is a SYMBOL RUN of x_i's declared hull -- a maximal stretch of consecutive
   values whose columns of d are identical -- and the last literal is absent when
   d[q,R] = 0. `x_i notin R` is ~x_i_ge_a \/ x_i_ge_(b+1), constant halves dropped.

   And, derived as `rup` at the start of the proof ([Encoding.add_root_lemma]), the
   BACKWARD CHAINS the forward rows cannot carry:

     B(i, q', R)    ~s(i+1,q') \/ x_i notin R \/ OR_{q : d[q,R] = q'} s(i,q)

   ---------------------------------------------------------------------------
   Consistency level: DOMAIN (Pesant's filtering), and [Aliased] when it is not
   ---------------------------------------------------------------------------

   One call kills every flag off an accepting path through the current domains (forward
   reachability, then backward), removes every letter value no live edge carries, and
   fixes a flag to 1 when its layer has no other live state. Afterwards every remaining
   value of every variable of the scope -- letters AND flags -- extends to a solution of
   the constraint: a letter value lies on a live edge, which lies on an accepting path;
   a flag's 1 is its state on such a path, and its 0 is another live state of its layer
   (or the flag is fixed). That is domain consistency over the joint scope, so the tag
   is [Domain] and the M2-T10 oracle holds the module to it.

   It holds only while the layers are INDEPENDENT. A variable twice in the word couples
   two layers the graph treats separately, the filtering is no longer complete, and
   lib/flatzinc/compile.ml packs that instance as [Aliased], the same code declared
   [Checking]. Checking is unconditional: with every letter fixed the run is one path,
   every flag off it dies, and a word the automaton rejects empties a layer.

   The call is idempotent at its own fixpoint (forward kills never orphan a state the
   backward pass keeps, and a value removal only drops an edge already dead), and
   compile.ml says so at the packing site for the non-aliased instance only.

   ---------------------------------------------------------------------------
   The proof: every pruning is ONE `rup`, its facts on its tail
   ---------------------------------------------------------------------------

   Every reason is BOUND facts (lib/core/reason.ml): a dead flag is `s <= 0`, a fixed one
   `s >= 1`, a letter's bound `x >= lo` / `x <= hi`, and a hole in a letter's domain is
   cited through the facts of the entry that punched it (D-0075's technique, as
   lib/core/prop/element.ml does), because a hole is not a literal and its own trace line
   only fires once its tail is assumed. The trace line is then RUP against the rows, the
   root lemmas and the earlier lines -- the shapes, each measured in D-0146 section 4:

     P1  s(i+1,q') dies FORWARD. Assume it: AMO clears its layer; per run R of x_i the
         lemma B(i,q',R) (its predecessors dead) or the run's holes push x_i past R, from
         x_i >= lo upward, until x_i <= hi is contradicted.
     P2  s(i,q) dies BACKWARD. Assume it: FWD(i,q,R) with its successor dead (or no
         successor) pushes x_i past R, the same sweep.
     P3  x_i <> v. Assume x_i = v: every FWD(i,q,R) with v in R kills s(i,q) (its successor
         is dead) unless s(i,q) is already dead, and ALO_i is empty. At a bound the claim is
         the settled bound, so the reason carries the bound fact that pins x_i to v.
     P4  s(i,q) := 1: the rest of its layer is dead, ALO_i.
     P5  a flag fixed to 1 kills the rest of its layer: AMO_i. START and ACCEPT kill layer
         0 outside q0 and layer n outside F with no facts.

   A layer left with no live flag is a CONFLICT whose facts are its dead flags (ALO_i);
   killing a flag fixed to 1 is a conflict on the pruning's facts plus that flag's; two
   flags fixed to 1 in one layer, on the pair (AMO_i).

   The justification is [Explanation.clause] of the claim and the negated facts, the
   trace line itself, deferred. No new constructor, no [Store.deriving_ahead]: under
   I-X10 this is a [Single_row] family in the sense test/unit/test_trace.ml's table gives
   element.ml -- one constraint, several rows -- with the root lemmas being "lines already
   on the page", which is I-X10's own wording. A bound move is explained by the HOLE
   clause `x_i <> v`, which is RUP without the facts a settle adds; the trace line, which
   Trace builds from the entry, carries those.

   The scan is O(n * E) per call, E the automaton's non-failing edges: [out] lists each
   state's edges once, at [make]. *)

module Lit = Baguette_proof.Lit

(* One letter of the word: a variable with its DECLARED hull (what a fact's [decl] is and
   what decides whether a literal exists), or a constant the flattener left in the array. *)
type cell =
  | Fixed of int
  | Letter of { var : Var.t; name : string; dlo : int; dhi : int }

type t = {
  n : int; (* letters; layers 0..n *)
  nq : int; (* states 1..nq *)
  smin : int;
  w : int; (* the symbol range is smin .. smin + w - 1 *)
  delta : int array; (* nq * w, row-major by state; 0 = fail *)
  q0 : int;
  final : bool array; (* final.(q - 1) *)
  xs : cell array;
  flags : Var.t array; (* (n + 1) * nq, layer-major: flags.(i * nq + q - 1) *)
  fnames : string array;
  out : (int * int) array array; (* out.(q - 1): (v, t) with t > 0 *)
  vars : Var.t list;
  reach : bool array; (* scratch, (n + 1) * nq *)
}

let step t q v =
  let k = v - t.smin in
  if k < 0 || k >= t.w then 0 else t.delta.(((q - 1) * t.w) + k)

let make store ~xs ~nq ~smin ~delta ~q0 ~final ~flags : t =
  let n = Array.length xs in
  if nq < 1 then invalid_arg "Regular.make: no state";
  if Array.length delta mod nq <> 0 then
    invalid_arg "Regular.make: the table is not Q rows of equal length";
  if Array.length flags <> (n + 1) * nq then
    invalid_arg "Regular.make: (n + 1) * Q state flags are needed";
  let w = Array.length delta / nq in
  let t0 =
    {
      n;
      nq;
      smin;
      w;
      delta;
      q0;
      final = Array.init nq (fun q -> List.mem (q + 1) final);
      xs;
      flags;
      fnames = Array.map (Store.name store) flags;
      out = [||];
      vars = [];
      reach = Array.make ((n + 1) * nq) false;
    }
  in
  let out =
    Array.init nq (fun qi ->
        Array.of_list
          (List.filter_map
             (fun k ->
               let v = smin + k in
               let tq = step t0 (qi + 1) v in
               if tq > 0 then Some (v, tq) else None)
             (List.init w Fun.id)))
  in
  let letters =
    Array.fold_right
      (fun c acc ->
        match c with
        | Letter { var; _ } when not (List.exists (Var.equal var) acc) -> var :: acc
        | _ -> acc)
      xs []
  in
  { t0 with out; vars = letters @ Array.to_list flags }

let vars t = t.vars
let fid t i q = (i * t.nq) + q - 1
let flag t i q = t.flags.(fid t i q)
let dead store t i q = Domain.hi (Store.get store (flag t i q)) = 0
let is_set store t i q = Domain.lo (Store.get store (flag t i q)) = 1
let dead_fact t i q = Reason.at_most ~name:t.fnames.(fid t i q) ~decl:1 0
let set_fact t i q = Reason.at_least ~name:t.fnames.(fid t i q) ~decl:0 1

(* The live domain of letter i, as lo, hi and a membership test. *)
let letter_dom store t i =
  match t.xs.(i) with
  | Fixed c -> (c, c, fun v -> v = c)
  | Letter { var; _ } ->
      let d = Store.get store var in
      (Domain.lo d, Domain.hi d, Domain.mem d)

exception Found of Store.conflict

(* A reason under construction: facts in the order they were read, each once. *)
type acc = { mutable facts_rev : Reason.fact list; seen : (Reason.fact, unit) Hashtbl.t }

let new_acc () = { facts_rev = []; seen = Hashtbl.create 8 }

let add a f =
  if not (Hashtbl.mem a.seen f) then (
    Hashtbl.replace a.seen f ();
    a.facts_rev <- f :: a.facts_rev)

let facts a = List.rev a.facts_rev

(* The bound facts of letter i that are not its declared bounds. *)
let add_bounds a t i lo hi =
  match t.xs.(i) with
  | Fixed _ -> ()
  | Letter { name; dlo; dhi; _ } ->
      if lo > dlo then add a (Reason.at_least ~name ~decl:dlo lo);
      if hi < dhi then add a (Reason.at_most ~name ~decl:dhi hi)

(* The facts behind the hole [v] of letter i: those of the entry that punched it. [None]
   from [Store.remover] is a declared hole with no entry, which lib/ does not produce
   (Store.remover's header); citing nothing there is what element.ml and trace.ml do. *)
let add_hole a store t i v =
  match t.xs.(i) with
  | Fixed _ -> ()
  | Letter { var; _ } -> (
      match Store.remover store ~before:(Store.trail_length store) ~var v with
      | None -> ()
      | Some e -> List.iter (add a) (Reason.facts e.Store.reason))

let clause_expl claim fs =
  Explanation.deferred (fun () ->
      Explanation.clause (claim @ List.map Lit.negate (Reason.lits_of_facts fs)))

let conflict store fs =
  Store.conflict store (Reason.because ~concludes:None fs (clause_expl [] fs))

(* Kill s(i,q) on [fs]. A flag fixed to 1 cannot die: that is a conflict on the same facts
   plus the flag's own, which the same `rup` refutes (it assumed the flag anyway). *)
let kill store t i q fs =
  if is_set store t i q then raise (Found (conflict store (fs @ [ set_fact t i q ])))
  else
    let concl = dead_fact t i q in
    let claim = Option.to_list (Reason.lit_of_fact concl) in
    match
      Store.set_hi store (flag t i q) 0
        (Reason.because ~concludes:(Some concl) fs (clause_expl claim fs))
    with
    | Store.Conflict c -> raise (Found c)
    | Store.Changed | Store.Unchanged -> ()

let layer_wiped store t i =
  let rec go q = q > t.nq || (dead store t i q && go (q + 1)) in
  go 1

let check_layer store t i =
  if layer_wiped store t i then
    raise (Found (conflict store (List.init t.nq (fun k -> dead_fact t i (k + 1)))))

(* Step 1: a flag fixed to 1 clears its layer (AMO_i); START and ACCEPT clear layers 0
   and n. *)
let fixed_flags store t =
  for i = 0 to t.n do
    let set = List.filter (is_set store t i) (List.init t.nq (fun k -> k + 1)) in
    match set with
    | a :: b :: _ -> raise (Found (conflict store [ set_fact t i a; set_fact t i b ]))
    | [ a ] ->
        for r = 1 to t.nq do
          if r <> a && not (dead store t i r) then kill store t i r [ set_fact t i a ]
        done
    | [] -> ()
  done;
  for q = 1 to t.nq do
    if q <> t.q0 && not (dead store t 0 q) then kill store t 0 q []
  done;
  for q = 1 to t.nq do
    if (not t.final.(q - 1)) && not (dead store t t.n q) then kill store t t.n q []
  done

(* P1's reason for s(i+1,q'): per value of [lo, hi] of letter i, its predecessors on q'
   dead, or else the value is a hole. *)
let forward_reason store t i q' =
  let a = new_acc () in
  let lo, hi, mem = letter_dom store t i in
  add_bounds a t i lo hi;
  for v = lo to hi do
    let preds =
      List.filter (fun q -> step t q v = q') (List.init t.nq (fun k -> k + 1))
    in
    if List.for_all (fun q -> dead store t i q) preds then
      List.iter (fun q -> add a (dead_fact t i q)) preds
    else if not (mem v) then add_hole a store t i v
    else invalid_arg "Regular: a forward death with a live predecessor edge"
  done;
  facts a

(* Step 2. *)
let forward store t =
  check_layer store t 0;
  for i = 0 to t.n - 1 do
    let _, _, mem = letter_dom store t i in
    let base = (i + 1) * t.nq in
    Array.fill t.reach base t.nq false;
    for q = 1 to t.nq do
      if not (dead store t i q) then
        Array.iter
          (fun (v, tq) -> if mem v then t.reach.(base + tq - 1) <- true)
          t.out.(q - 1)
    done;
    for q' = 1 to t.nq do
      if (not t.reach.(base + q' - 1)) && not (dead store t (i + 1) q') then
        kill store t (i + 1) q' (forward_reason store t i q')
    done;
    check_layer store t (i + 1)
  done

(* P2's reason for s(i,q): per value of [lo, hi] of letter i, its successor dead (or no
   successor), or else the value is a hole. *)
let backward_reason store t i q =
  let a = new_acc () in
  let lo, hi, mem = letter_dom store t i in
  add_bounds a t i lo hi;
  for v = lo to hi do
    let tq = step t q v in
    if tq = 0 then ()
    else if dead store t (i + 1) tq then add a (dead_fact t (i + 1) tq)
    else if not (mem v) then add_hole a store t i v
    else invalid_arg "Regular: a backward death with a live successor edge"
  done;
  facts a

(* Step 3. *)
let backward store t =
  for i = t.n - 1 downto 0 do
    let _, _, mem = letter_dom store t i in
    for q = 1 to t.nq do
      if not (dead store t i q) then
        let live =
          Array.exists
            (fun (v, tq) -> mem v && not (dead store t (i + 1) tq))
            t.out.(q - 1)
        in
        if not live then kill store t i q (backward_reason store t i q)
    done;
    check_layer store t i
  done

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

(* Step 4: remove every value of letter i no live edge carries, one value at a time. *)
let values store t i =
  match t.xs.(i) with
  | Fixed _ -> ()
  | Letter { var; name; dlo; dhi } ->
      let d0 = Store.get store var in
      let supported = Hashtbl.create 16 in
      for q = 1 to t.nq do
        if not (dead store t i q) then
          Array.iter
            (fun (v, tq) ->
              if Domain.mem d0 v && not (dead store t (i + 1) tq) then
                Hashtbl.replace supported v ())
            t.out.(q - 1)
      done;
      Domain.iter
        (fun v ->
          if not (Hashtbl.mem supported v) then (
            let d = Store.get store var in
            let a = new_acc () in
            if v = Domain.lo d then add a (Reason.at_least ~name ~decl:dlo v);
            if v = Domain.hi d then add a (Reason.at_most ~name ~decl:dhi v);
            for q = 1 to t.nq do
              let tq = step t q v in
              if tq > 0 then
                if dead store t i q then add a (dead_fact t i q)
                else add a (dead_fact t (i + 1) tq)
            done;
            let fs = facts a in
            if Domain.is_fixed d then raise (Found (conflict store fs));
            let claim =
              (if v > dlo then [ Lit.negate (Lit.ge name v) ] else [])
              @ if v < dhi then [ Lit.ge name (v + 1) ] else []
            in
            match
              Store.remove store var v
                (Reason.because
                   ~concludes:(removal_conclusion ~name ~dlo ~dhi d v)
                   fs (clause_expl claim fs))
            with
            | Store.Conflict c -> raise (Found c)
            | Store.Changed | Store.Unchanged -> ()))
        d0

(* Step 5: a layer with one live state fixes its flag (ALO_i). *)
let fix_singletons store t =
  for i = 0 to t.n do
    let live =
      List.filter (fun q -> not (dead store t i q)) (List.init t.nq (fun k -> k + 1))
    in
    match live with
    | [ q ] when not (is_set store t i q) -> (
        let fs =
          List.filter_map
            (fun r -> if r = q then None else Some (dead_fact t i r))
            (List.init t.nq (fun k -> k + 1))
        in
        let concl = set_fact t i q in
        match
          Store.set_lo store (flag t i q) 1
            (Reason.because ~concludes:(Some concl) fs
               (clause_expl (Option.to_list (Reason.lit_of_fact concl)) fs))
        with
        | Store.Conflict c -> raise (Found c)
        | Store.Changed | Store.Unchanged -> ())
    | _ -> ()
  done

let propagate t store =
  try
    fixed_flags store t;
    forward store t;
    backward store t;
    for i = 0 to t.n - 1 do
      values store t i
    done;
    fix_singletons store t;
    Propagator.Fixpoint
  with Found c -> Propagator.Conflict c

let name = "regular"
let consistency = Propagator.Domain

(* The same code over a word that names one variable twice: the layers are coupled and
   the filtering is no longer complete, so the claim drops to [Checking] (see the
   header). One implementation; the packed name says which. *)
module Aliased = struct
  type nonrec t = t

  let name = name
  let consistency = Propagator.Checking
  let vars = vars
  let propagate = propagate
end
