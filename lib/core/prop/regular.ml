(* regular(x, Q, S, d, q0, F): the word x_0 .. x_(n-1) drives the DFA with states 1..Q,
   transition d (0 = fail) and start q0 to an accepting state in F. Reaches the solver as
   `baguette_regular(x, Q, smin, d, q0, F, s)` through mznlib/fzn_regular.mzn and
   mznlib/fzn_regular_set.mzn.

   Consistency level: DOMAIN ([consistency] below, Pesant's layered-graph filtering) over
   the letters and the state flags, and CHECKING for the [Aliased] packing compile.ml
   uses when a variable occurs twice in the word (section "Consistency level" below).
   Governed by docs/SPEC.md 3.2 (consistency levels) and 3.3 (explanations). Proof
   shape: every pruning is ONE `rup` against one row or root lemma of the automaton, with
   the flags' own earlier trace lines on the page and nothing derived ahead, so the
   family is [Single_row] in the I-X10 classification table of test/unit/test_trace.ml
   (a pruning that follows from one model constraint, whose trace line is RUP with
   nothing derived ahead of it).

   The records: docs/DECISIONS.md D-0146 (section 3 the design, section 4 the checker
   probes that settled it before a line of it existed), D-0151 section 1 for the reasons
   on the letters, and D-0232 for the incremental call.

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
   is [Domain] and the per-node consistency harness of M2-T10 (a brute-force oracle)
   holds the module to it.

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

   The shapes, each measured in D-0146 section 4, are the arguments a line's `rup` makes
   once its tail is assumed:

     P1  s(i+1,q') dies FORWARD. Assume it: AMO clears its layer; per run R of x_i the
         lemma B(i,q',R) (its predecessors dead) or the run's exclusion from x_i's
         domain pushes x_i past R, from the declared bound upward, until x_i has no value.
     P2  s(i,q) dies BACKWARD. Assume it: FWD(i,q,R) with its successor dead (or no
         successor) pushes x_i past R, the same sweep.
     P3  x_i <> v. Assume x_i = v: every FWD(i,q,R) with v in R kills s(i,q) (its
         successor is dead) unless s(i,q) is already dead, and ALO_i is empty. At a bound
         the claim is the settled bound, so the reason carries the bound fact that pins
         x_i to v.
     P4  s(i,q) := 1: the rest of its layer is dead, ALO_i.
     P5  a flag fixed to 1 kills the rest of its layer: AMO_i. START and ACCEPT kill layer
         0 outside q0 and layer n outside F with no facts.

   A layer left with no live flag is a CONFLICT (ALO_i); killing a flag fixed to 1 is a
   conflict on the pruning's facts plus that flag's; two flags fixed to 1 in one layer, on
   the pair (AMO_i).

   ---------------------------------------------------------------------------
   The reasons are ON THE LETTERS (D-0151): no tail names a flag this instance moved
   ---------------------------------------------------------------------------

   The reasons name only the WORD's bounds (and, for a hole, the facts of its remover,
   and a flag only if something other than this instance fixed it: a decision). The rule
   that makes that one `rup` per pruning, with no line added, is RECURSION THROUGH THE
   FLAGS' OWN LINES: where a reason would cite "s(i,q) <= 0", it cites the TAIL of the
   line that killed s(i,q), which is letter facts by the same rule, one level down.
   Assume the new tail and the dead flag's line fires (its tail is a subset), so the
   argument above goes through unchanged, against the same rows, the same lemmas and the
   earlier trace lines. The tails are kept as the STRONGEST fact per letter and direction
   (x >= 3 subsumes x >= 2 through the ladder), so a tail has at most two facts per
   letter however deep the recursion goes.

   Why the letters: the first design (D-0146) put the dead flags themselves on the tails
   (`s <= 0`), and 1UIP learning then cut on flags, so a learned clause named states of a
   row, which only that row's propagator can read back.

   Which values cite what -- Pesant's layered graph explained the way Gange, Stuckey and
   Szymanek explain an MDD ("MDD propagators with explanation", Constraints 2011): an
   edge is cut ABOVE (its source is dead), BELOW (its target is dead) or by its LETTER
   (the value is out of the domain), and the letter is cited only where it must be:

     P1  per value v of x_i's alphabet: every predecessor of q' on v dead -> recurse into
         their tails; else (a live predecessor) v is out of x_i's domain -> cited, as the
         WEAKEST bound that excludes every such v below lo (x_i >= v+1 for the largest)
         and above hi, or, inside [lo, hi], the hole's remover.
     P2  per value v: no successor -> nothing; the successor dead -> its tail; else v is
         out of the domain -> the weakest bound / the hole, as P1.
     P3  per state q with d[q,v] = t > 0: s(i,q) dead or s(i+1,t) dead, whichever tail
         adds fewer facts the reason does not already hold (the source on a tie); plus the
         letter's own bound fact when v is a bound.
     P4  the tails of the rest of the layer.  P5  the tail of the flag fixed to 1.
     Conflicts: the union of the tails the argument reads.

   "Recurse rather than cite the letter" is the choice that keeps the letters cited at the
   FRONTIER, where an edge leaves a live state: a death several layers past a decision
   cites the decision, not the letters the decision forced on the way. A flag killed by
   anything other than this instance (a decision, a learned clause) has no tail of ours
   to recurse into and is cited as itself; under the engine that is a decision on a flag.

   A flag's tail is kept per flag, packed as (slot, direction, value) triples, with the
   trail entry it belongs to, and read back through the entry that moved the flag NOW
   ([Store.hi_support] / [lo_support]): a hit is that same entry by physical equality, so
   a flag revived by a backtrack and moved again by anything else -- a decision -- is
   never read through a stale tail, and is cited as itself.

   The justification is [Explanation.clause] of the claim and the negated facts, the
   trace line itself, deferred. No new constructor, no [Store.deriving_ahead]: this is a
   [Single_row] family in the sense test/unit/test_trace.ml's table gives element.ml (one
   constraint, several rows), with the root lemmas and the flags' own earlier trace lines
   being "lines already on the page", which is I-X10's own wording.
   A bound move is explained by the HOLE clause `x_i <> v`, which is RUP without the
   facts a settle adds; the trace line, which Trace builds from the entry, carries those.

   The scan is O(n * E) per call, E the automaton's non-failing edges: [out] lists each
   state's edges and [preds] each state's predecessors per symbol, once, at [make]. A
   reason costs the sum of the tails it recurses into (each at most two facts per letter)
   and allocates only what it hands the store: the dedup is stamps on per-instance scratch
   arrays indexed by (slot, direction), never a hash of a fact (D-0146 section 5 measured
   that hashing at a quarter of the run).

   ---------------------------------------------------------------------------
   The call is INCREMENTAL (D-0232): a pass skips what cannot have changed
   ---------------------------------------------------------------------------

   Every condition the five steps test is LOCAL. Step 1 and step 5 read one layer's
   flags; steps 2 to 4 read the edges of letter i, that is layer i's flags, letter i's
   domain and layer i + 1's flags. When a call returns [Fixpoint], every such condition
   holds in the state it leaves (the idempotence argument above). So a later call need
   only test the conditions whose inputs differ from that state: a layer whose flags all
   have the state the fixpoint left is CLEAN, a letter whose domain is physically the one
   it left is clean, and step 1/5 skip a clean layer, steps 2 to 4 the edges of a clean
   letter between two clean layers. Everything the call itself writes marks its layer or
   letter dirty, so the passes see their own deaths exactly as the full scan did: the
   prunings, their order, their reasons and therefore the trace are the full scan's,
   byte for byte. That is the soundness argument and the test (D-0232 measures proof
   identity at a node limit on the Challenge sample): the skip changes WHICH conditions
   are tested, never what a tested one concludes.

   What it costs: one state byte per flag ([st], also the read the passes make instead of
   a [Store.get] per test), one domain reference per letter, and one comparison per flag
   per call. After a conflict the layers the call wrote are marked [stale] (their bytes
   hold writes the backtrack undoes) and read afresh. An ALIASED word scans everything,
   always: a removal at one layer moves a letter another layer reads, after that layer's
   pass. Under BAGUETTE_DEBUG every call first checks that the bytes are the store's and
   that every condition it is about to skip holds ([skipped_hold]). *)

module Lit = Baguette_proof.Lit

(* One letter of the word: a variable with its DECLARED hull (what a fact's [decl] is
   and what decides whether a literal exists), or a constant the flattener left in the
   array. *)
type cell =
  | Fixed of int
  | Letter of { var : Var.t; name : string; dlo : int; dhi : int }

(* A flag's tail as this instance wrote it: [keys] packs (key, value) pairs, a key being
   [2 * slot] for a letter's lower bound and [2 * slot + 1] for its upper one; [others] is
   what is not a bound of a letter of this word (a hole remover's facts elsewhere, a flag
   a decision fixed). [entry] is the trail entry the tail belongs to. *)
type tail = { entry : Store.entry; keys : int array; others : Reason.fact list }

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
  preds : int array array; (* preds.((t - 1) * w + k): the q with d[q, smin + k] = t *)
  vars : Var.t list;
  (* The letters as SLOTS, one per distinct variable of the word (an aliased word names a
     variable at two layers and gets one slot). *)
  slot : int array; (* layer i -> slot, -1 for a [Fixed] cell *)
  slot_name : string array;
  slot_dlo : int array;
  slot_dhi : int array;
  slot_of_name : (string, int) Hashtbl.t; (* for a remover's facts, named by string *)
  tails : tail option array; (* per flag: the tail of the last line this instance wrote *)
  (* The incremental call (D-0232): what the last call that reached its fixpoint LEFT --
     each flag's state, each letter's domain (compared by physical equality) -- and what
     this call found or made dirty. *)
  incremental : bool; (* false for an aliased word: every call scans every layer *)
  mutable valid : bool; (* [st]/[xsnap] hold a fixpoint's state *)
  st : Bytes.t; (* (n + 1) * nq, as [flags]: the fixpoint's states, then this call's *)
  stale : bool array; (* n + 1: [st] of layer i holds a call that ended in a conflict *)
  xsnap : Domain.t array; (* n, letter i's domain; unused for a [Fixed] cell *)
  ldirty : bool array; (* n + 1: a flag of layer i moved *)
  xdirty : bool array; (* n: letter i moved *)
  (* [out] flattened for the edge loops: state q's edges are oi.(q - 1) .. oi.(q) - 1,
     symbol ok.(e) (v - smin) to state ot.(e). *)
  oi : int array;
  ok : int array;
  ot : int array;
  inx : bool array; (* w: the symbols in the current letter's domain *)
  (* Scratch, reused by every call: nothing in it survives a call. *)
  reach : bool array; (* (n + 1) * nq *)
  sup : bool array; (* w: a symbol some live edge of the current layer carries *)
  (* The reason under construction: [best]/[seen] by key, [keys_in] the keys in the order
     first read, [others_rev] the rest. *)
  best : int array;
  seen : int array;
  keys_in : int array;
  mutable nkeys : int;
  mutable others_rev : Reason.fact list;
  mutable stamp : int;
}

let free = '\001'

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
  let get q k = delta.(((q - 1) * w) + k) in
  let out =
    Array.init nq (fun qi ->
        Array.of_list
          (List.filter_map
             (fun k ->
               if get (qi + 1) k > 0 then Some (smin + k, get (qi + 1) k) else None)
             (List.init w Fun.id)))
  in
  let preds =
    Array.init (nq * w) (fun j ->
        let tq = (j / w) + 1 and k = j mod w in
        Array.of_list
          (List.filter (fun q -> get q k = tq) (List.init nq (fun q -> q + 1))))
  in
  let fnames = Array.map (Store.name store) flags in
  let letters =
    Array.fold_right
      (fun c acc ->
        match c with
        | Letter { var; _ } when not (List.exists (Var.equal var) acc) -> var :: acc
        | _ -> acc)
      xs []
  in
  let slot_of_name = Hashtbl.create 16 in
  let names = ref [] in
  let slot =
    Array.map
      (function
        | Fixed _ -> -1
        | Letter { name; dlo; dhi; _ } -> (
            match Hashtbl.find_opt slot_of_name name with
            | Some s -> s
            | None ->
                let s = Hashtbl.length slot_of_name in
                Hashtbl.replace slot_of_name name s;
                names := (name, dlo, dhi) :: !names;
                s))
      xs
  in
  let slots = Array.of_list (List.rev !names) in
  let ns = Array.length slots in
  let nletters =
    Array.fold_left (fun c x -> match x with Letter _ -> c + 1 | Fixed _ -> c) 0 xs
  in
  let any = Store.get store flags.(0) in
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
    fnames;
    out;
    preds;
    vars = letters @ Array.to_list flags;
    slot;
    slot_name = Array.map (fun (nm, _, _) -> nm) slots;
    slot_dlo = Array.map (fun (_, lo, _) -> lo) slots;
    slot_dhi = Array.map (fun (_, _, hi) -> hi) slots;
    slot_of_name;
    tails = Array.make ((n + 1) * nq) None;
    incremental = nletters = ns;
    valid = false;
    stale = Array.make (n + 1) false;
    xsnap = Array.make n any;
    ldirty = Array.make (n + 1) true;
    xdirty = Array.make n true;
    st = Bytes.make ((n + 1) * nq) free;
    oi =
      (let a = Array.make (nq + 1) 0 in
       Array.iteri (fun q es -> a.(q + 1) <- a.(q) + Array.length es) out;
       a);
    ok = Array.concat (Array.to_list (Array.map (Array.map (fun (v, _) -> v - smin)) out));
    ot = Array.concat (Array.to_list (Array.map (Array.map snd) out));
    inx = Array.make (Int.max w 1) false;
    reach = Array.make ((n + 1) * nq) false;
    sup = Array.make (Int.max w 1) false;
    best = Array.make (Int.max (2 * ns) 1) 0;
    seen = Array.make (Int.max (2 * ns) 1) 0;
    keys_in = Array.make (Int.max (2 * ns) 1) 0;
    nkeys = 0;
    others_rev = [];
    stamp = 0;
  }

let vars t = t.vars
let fid t i q = (i * t.nq) + q - 1
let flag t i q = t.flags.(fid t i q)

(* A flag's state, as [st] caches it for the call ([detect] fills it from the store, and
   every write of this instance updates it). *)
let dead_c = '\000'
let set_c = '\002'

let state_of d =
  if Domain.hi d = 0 then dead_c else if Domain.lo d = 1 then set_c else free

let dead _store t i q = Bytes.unsafe_get t.st (fid t i q) = dead_c
let is_set _store t i q = Bytes.unsafe_get t.st (fid t i q) = set_c
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

(* ------------------------------------------------------------- the reason under way *)

let start t =
  t.stamp <- t.stamp + 1;
  t.nkeys <- 0;
  t.others_rev <- []

let is_lower_key key = key land 1 = 0

(* Would (key, v) tell the reason something it does not already hold? *)
let key_new t key v =
  t.seen.(key) <> t.stamp
  || if is_lower_key key then v > t.best.(key) else v < t.best.(key)

let add_key t key v =
  if t.seen.(key) <> t.stamp then (
    t.seen.(key) <- t.stamp;
    t.best.(key) <- v;
    t.keys_in.(t.nkeys) <- key;
    t.nkeys <- t.nkeys + 1)
  else if is_lower_key key then (if v > t.best.(key) then t.best.(key) <- v)
  else if v < t.best.(key) then t.best.(key) <- v

(* A fact read elsewhere (a remover's, a foreign flag's): onto its letter's key when it
   names a letter of this word, else kept once as it is. The equality is structural, on
   a list that is empty in every model without holes or flag decisions. *)
let add_fact t (f : Reason.fact) =
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

(* How many facts a tail would add, for P3's choice of side. *)
let tail_new t (tl : tail) =
  let k = tl.keys and c = ref 0 in
  for j = 0 to (Array.length k / 2) - 1 do
    if key_new t k.(2 * j) k.((2 * j) + 1) then incr c
  done;
  List.iter (fun f -> if not (List.mem f t.others_rev) then incr c) tl.others;
  !c

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

(* ------------------------------------------------------------- the flags' tails *)

(* The tail of the line that killed (fixed, if [~set]) flag (i, q), as THIS instance wrote
   it; or the flag's own fact when anything else moved it (see the header), or when the
   bound has no support entry ([Store.no_support]: it is still the bound the flag was
   created with). The entry is the one [Store.hi_support]/[lo_support] names, and the
   cached tail is used only when it belongs to that very entry. *)
let flag_tail store t ~set i q : tail =
  let k = fid t i q in
  let v = t.flags.(k) in
  let own () =
    {
      entry = Store.dummy_entry;
      keys = [||];
      others = [ (if set then set_fact t i q else dead_fact t i q) ];
    }
  in
  let pos = if set then Store.lo_support store v else Store.hi_support store v in
  if pos = Store.no_support then own ()
  else
    let e = Store.trail_entry store pos in
    match t.tails.(k) with Some tl when tl.entry == e -> tl | _ -> own ()

let add_flag store t ~set i q = add_tail t (flag_tail store t ~set i q)

(* The facts behind the hole [v] of letter i: those of the entry that punched it. [None]
   from [Store.remover] is a declared hole with no entry, which lib/ does not produce
   (Store.remover's header); citing nothing there is what element.ml and trace.ml do. *)
let add_hole store t i v =
  match t.xs.(i) with
  | Fixed _ -> ()
  | Letter { var; _ } -> (
      match Store.remover store ~before:(Store.trail_length store) ~var v with
      | None -> ()
      | Some e -> List.iter (add_fact t) (Reason.facts e.Store.reason))

(* Letter i's values in [need] (none in its domain) cited as the WEAKEST bounds that
   exclude them -- x_i >= (largest below lo) + 1, x_i <= (smallest above hi) - 1 -- and
   the ones inside [lo, hi] through their removers. [nlo]/[nhi] are the largest value
   needed below lo and the smallest above hi, or [min_int]/[max_int] for none. *)
let add_exclusion t i ~nlo ~nhi =
  let s = t.slot.(i) in
  if s >= 0 then (
    if nlo <> min_int then add_key t (2 * s) (nlo + 1);
    if nhi <> max_int then add_key t ((2 * s) + 1) (nhi - 1))

let clause_expl claim fs =
  Explanation.deferred (fun () ->
      Explanation.clause (claim @ List.map Lit.negate (Reason.lits_of_facts fs)))

let conflict store fs =
  Store.conflict store (Reason.because ~concludes:None fs (clause_expl [] fs))

(* The conflict on the reason under way. *)
let conflict_now store t =
  let fs, _, _ = finish t in
  conflict store fs

(* Kill s(i,q) on the reason under way, and cache its tail against the entry. A flag fixed
   to 1 cannot die: that is a conflict on the same facts plus the flag's own tail, which
   the same `rup` refutes (it assumed the flag anyway). *)
let kill store t i q =
  if is_set store t i q then (
    add_flag store t ~set:true i q;
    raise (Found (conflict_now store t)))
  else
    let fs, packed, others = finish t in
    let concl = dead_fact t i q in
    let claim = Option.to_list (Reason.lit_of_fact concl) in
    let v = flag t i q in
    t.ldirty.(i) <- true;
    match
      Store.set_hi store v 0
        (Reason.because ~concludes:(Some concl) fs (clause_expl claim fs))
    with
    | Store.Conflict c -> raise (Found c)
    | Store.Changed ->
        Bytes.unsafe_set t.st (fid t i q) dead_c;
        let e = Store.trail_entry store (Store.hi_support store v) in
        t.tails.(fid t i q) <- Some { entry = e; keys = packed; others }
    | Store.Unchanged -> ()

let layer_wiped store t i =
  let rec go q = q > t.nq || (dead store t i q && go (q + 1)) in
  go 1

let check_layer store t i =
  if layer_wiped store t i then (
    start t;
    for q = 1 to t.nq do
      add_flag store t ~set:false i q
    done;
    raise (Found (conflict_now store t)))

(* Step 1: a flag fixed to 1 clears its layer (AMO_i); START and ACCEPT clear layers 0
   and n. *)
let fixed_flags store t =
  for i = 0 to t.n do
    if t.ldirty.(i) then (
      let first = ref 0 in
      for q = 1 to t.nq do
        if is_set store t i q then
          if !first = 0 then first := q
          else (
            start t;
            add_flag store t ~set:true i !first;
            add_flag store t ~set:true i q;
            raise (Found (conflict_now store t)))
      done;
      if !first > 0 then
        for r = 1 to t.nq do
          if r <> !first && not (dead store t i r) then (
            start t;
            add_flag store t ~set:true i !first;
            kill store t i r)
        done)
  done;
  for q = 1 to t.nq do
    if t.ldirty.(0) && q <> t.q0 && not (dead store t 0 q) then (
      start t;
      kill store t 0 q)
  done;
  for q = 1 to t.nq do
    if t.ldirty.(t.n) && (not t.final.(q - 1)) && not (dead store t t.n q) then (
      start t;
      kill store t t.n q)
  done

(* The alphabet's values within letter i's declared hull: the only values whose edges a
   reason has to account for (a value outside the alphabet fails from every state). The
   range is EMPTY (lo > hi) when the hull misses the alphabet, a constant letter outside
   it included: such a letter labels no edge, every state of layer i + 1 dies forward
   with nothing to cite, and its line is `rup` against FWD(i, q, {c}) = ~s(i,q) for every
   q and ALO_i. (A constant letter outside the alphabet once crashed here: [Fixed c]
   returned (c, c) and [forward_reason] indexed [preds] out of bounds with it, fixed by
   D-0231.) *)
let alphabet_hull t i =
  let a = t.smin and b = t.smin + t.w - 1 in
  match t.xs.(i) with
  | Fixed c -> (Int.max a c, Int.min b c)
  | Letter { dlo; dhi; _ } -> (Int.max a dlo, Int.min b dhi)

(* P1's reason for s(i+1,q'): per value of letter i, its predecessors on q' all dead ->
   their tails; else the value is out of the domain -> the weakest bound, or the hole. *)
let forward_reason store t i q' =
  start t;
  let lo, hi, mem = letter_dom store t i in
  let nlo = ref min_int and nhi = ref max_int in
  let a, b = alphabet_hull t i in
  for v = a to b do
    let ps = t.preds.(((q' - 1) * t.w) + v - t.smin) in
    if Array.for_all (fun q -> dead store t i q) ps then
      Array.iter (fun q -> add_flag store t ~set:false i q) ps
    else if mem v then invalid_arg "Regular: a forward death with a live predecessor edge"
    else if v < lo then nlo := max !nlo v
    else if v > hi then nhi := min !nhi v
    else add_hole store t i v
  done;
  add_exclusion t i ~nlo:!nlo ~nhi:!nhi

(* Step 2, [forward] below: a state of layer i + 1 that no live edge from a live state
   of layer i reaches dies (P1). *)

(* Letter i's domain over the symbols, into [inx], read by the edge loops below. *)
let load_letter t mem =
  for k = 0 to t.w - 1 do
    Array.unsafe_set t.inx k (mem (t.smin + k))
  done

(* Layers i and i + 1 and letter i: what every pass over the edges of layer i reads. *)
let touched t i = t.ldirty.(i) || t.xdirty.(i) || t.ldirty.(i + 1)

let forward store t =
  if t.ldirty.(0) then check_layer store t 0;
  for i = 0 to t.n - 1 do
    if touched t i then (
      let _, _, mem = letter_dom store t i in
      load_letter t mem;
      let base = (i + 1) * t.nq in
      Array.fill t.reach base t.nq false;
      for q = 1 to t.nq do
        if not (dead store t i q) then
          for e = t.oi.(q - 1) to t.oi.(q) - 1 do
            if Array.unsafe_get t.inx t.ok.(e) then t.reach.(base + t.ot.(e) - 1) <- true
          done
      done;
      for q' = 1 to t.nq do
        if (not t.reach.(base + q' - 1)) && not (dead store t (i + 1) q') then (
          forward_reason store t i q';
          kill store t (i + 1) q')
      done;
      check_layer store t (i + 1))
  done

(* P2's reason for s(i,q): per value of letter i, no successor -> nothing; the successor
   dead -> its tail; else the value is out of the domain -> the weakest bound, or the
   hole. *)
let backward_reason store t i q =
  start t;
  let lo, hi, mem = letter_dom store t i in
  let nlo = ref min_int and nhi = ref max_int in
  let a, b = alphabet_hull t i in
  for v = a to b do
    let tq = step t q v in
    if tq = 0 then ()
    else if dead store t (i + 1) tq then add_flag store t ~set:false (i + 1) tq
    else if mem v then invalid_arg "Regular: a backward death with a live successor edge"
    else if v < lo then nlo := max !nlo v
    else if v > hi then nhi := min !nhi v
    else add_hole store t i v
  done;
  add_exclusion t i ~nlo:!nlo ~nhi:!nhi

(* Step 3: a live state of layer i with no live edge to a live state of layer i + 1
   dies (P2). *)
let backward store t =
  for i = t.n - 1 downto 0 do
    if touched t i then (
      let _, _, mem = letter_dom store t i in
      load_letter t mem;
      for q = 1 to t.nq do
        if not (dead store t i q) then
          let live =
            let e = ref t.oi.(q - 1) and stop = t.oi.(q) in
            while
              !e < stop
              && not
                   (Array.unsafe_get t.inx t.ok.(!e)
                   && not (dead store t (i + 1) t.ot.(!e)))
            do
              incr e
            done;
            !e < stop
          in
          if not live then (
            backward_reason store t i q;
            kill store t i q)
      done;
      check_layer store t i)
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

(* P3's reason for x_i <> v: per state q with an edge on v, the dead side whose tail adds
   less (the source on a tie). *)
let value_reason store t i v =
  start t;
  for q = 1 to t.nq do
    let tq = step t q v in
    if tq > 0 then
      let src = if dead store t i q then Some (flag_tail store t ~set:false i q) else None
      and dst =
        if dead store t (i + 1) tq then Some (flag_tail store t ~set:false (i + 1) tq)
        else None
      in
      match (src, dst) with
      | Some s, Some d -> add_tail t (if tail_new t s <= tail_new t d then s else d)
      | Some s, None -> add_tail t s
      | None, Some d -> add_tail t d
      | None, None -> invalid_arg "Regular: a value removal with a live edge"
  done

(* Step 4: remove every value of letter i no live edge carries, one value at a time. *)
let values store t i =
  match t.xs.(i) with
  | Fixed _ -> ()
  | Letter { var; name; dlo; dhi } ->
      let d0 = Store.get store var in
      load_letter t (Domain.mem d0);
      Array.fill t.sup 0 (Array.length t.sup) false;
      for q = 1 to t.nq do
        if not (dead store t i q) then
          for e = t.oi.(q - 1) to t.oi.(q) - 1 do
            let k = t.ok.(e) in
            if Array.unsafe_get t.inx k && not (dead store t (i + 1) t.ot.(e)) then
              t.sup.(k) <- true
          done
      done;
      let supported v =
        let k = v - t.smin in
        k >= 0 && k < t.w && t.sup.(k)
      in
      let s = t.slot.(i) in
      Domain.iter
        (fun v ->
          if not (supported v) then (
            let d = Store.get store var in
            value_reason store t i v;
            if v = Domain.lo d && v > dlo then add_key t (2 * s) v;
            if v = Domain.hi d && v < dhi then add_key t ((2 * s) + 1) v;
            if Domain.is_fixed d then raise (Found (conflict_now store t));
            let fs, _, _ = finish t in
            let claim =
              (if v > dlo then [ Lit.negate (Lit.ge name v) ] else [])
              @ if v < dhi then [ Lit.ge name (v + 1) ] else []
            in
            t.xdirty.(i) <- true;
            match
              Store.remove store var v
                (Reason.because
                   ~concludes:(removal_conclusion ~name ~dlo ~dhi d v)
                   fs (clause_expl claim fs))
            with
            | Store.Conflict c -> raise (Found c)
            | Store.Changed | Store.Unchanged -> ()))
        d0

(* Step 5: a layer with one live state fixes its flag (ALO_i), on the rest's tails. *)
let fix_singletons store t =
  for i = 0 to t.n do
    if t.ldirty.(i) then (
      let live = ref 0 and count = ref 0 in
      for q = 1 to t.nq do
        if not (dead store t i q) then (
          incr count;
          live := q)
      done;
      if !count = 1 && not (is_set store t i !live) then (
        let q = !live in
        start t;
        for r = 1 to t.nq do
          if r <> q then add_flag store t ~set:false i r
        done;
        let fs, packed, others = finish t in
        let concl = set_fact t i q in
        let v = flag t i q in
        match
          Store.set_lo store v 1
            (Reason.because ~concludes:(Some concl) fs
               (clause_expl (Option.to_list (Reason.lit_of_fact concl)) fs))
        with
        | Store.Conflict c -> raise (Found c)
        | Store.Changed ->
            Bytes.unsafe_set t.st (fid t i q) set_c;
            let e = Store.trail_entry store (Store.lo_support store v) in
            t.tails.(fid t i q) <- Some { entry = e; keys = packed; others }
        | Store.Unchanged -> ()))
  done

(* ------------------------------------------------------ the incremental call (D-0232) *)

(* Which layers and letters moved since the last call that reached its fixpoint. A flag
   is compared by its state, which is the whole of a 0..1 domain; a letter by PHYSICAL
   equality with the domain that call left ([Domain.t] is immutable, so the same value is
   the same set, and a different value with the same set, after a backtrack and a redo,
   only costs a rescan; nothing is read through [xsnap], so a version a backtrack
   truncated is compared, never asked: Domain's header, [Stale_version]). Before the
   first fixpoint, and always for an aliased word, everything is dirty. A dirty layer's
   [st] is read afresh from the store. *)
let detect store t =
  let fill i =
    t.stale.(i) <- false;
    for k = i * t.nq to (i * t.nq) + t.nq - 1 do
      Bytes.unsafe_set t.st k (state_of (Store.get store t.flags.(k)))
    done
  in
  if not (t.incremental && t.valid) then (
    Array.fill t.ldirty 0 (t.n + 1) true;
    Array.fill t.xdirty 0 t.n true;
    for i = 0 to t.n do
      fill i
    done)
  else (
    for i = 0 to t.n do
      let base = i * t.nq in
      let q = ref 0 in
      if not t.stale.(i) then
        while
          !q < t.nq
          && state_of (Store.get store t.flags.(base + !q))
             = Bytes.unsafe_get t.st (base + !q)
        do
          incr q
        done;
      t.ldirty.(i) <- !q < t.nq;
      if !q < t.nq then fill i
    done;
    for i = 0 to t.n - 1 do
      t.xdirty.(i) <-
        (match t.xs.(i) with
        | Fixed _ -> false
        | Letter { var; _ } -> Store.get store var != t.xsnap.(i))
    done)

(* The fixpoint just reached becomes the reference: [st] already holds it (every write of
   this call updated it), and the letters this call found or made dirty are re-read. *)
let refresh store t =
  for i = 0 to t.n - 1 do
    if t.xdirty.(i) then
      match t.xs.(i) with
      | Fixed _ -> ()
      | Letter { var; _ } -> t.xsnap.(i) <- Store.get store var
  done;
  t.valid <- true

(* BAGUETTE_DEBUG's audit of the skip: every condition a pass would test on a layer it
   skips holds now, read-only. Steps 1 and 5 on a clean layer, steps 2 to 4 on the edges
   of a clean letter between clean layers. *)
let skipped_hold store t =
  let dead store t i q = Domain.hi (Store.get store (flag t i q)) = 0 in
  let is_set store t i q = Domain.lo (Store.get store (flag t i q)) = 1 in
  let live i =
    List.filter (fun q -> not (dead store t i q)) (List.init t.nq (fun q -> q + 1))
  in
  let layer_ok i =
    t.ldirty.(i)
    ||
    let l = live i in
    let set = List.filter (is_set store t i) l in
    l <> []
    && (match set with [] -> true | [ q ] -> l = [ q ] | _ -> false)
    && (List.length l <> 1 || set <> [])
    && (i <> 0 || List.for_all (fun q -> q = t.q0) l)
    && (i <> t.n || List.for_all (fun q -> t.final.(q - 1)) l)
  in
  let edges_ok i =
    touched t i
    ||
    let _, _, mem = letter_dom store t i in
    let into = Array.make t.nq false and sup = Array.make t.w false in
    let src_ok =
      List.for_all
        (fun q ->
          Array.fold_left
            (fun ok (v, tq) ->
              if mem v && not (dead store t (i + 1) tq) then (
                into.(tq - 1) <- true;
                sup.(v - t.smin) <- true;
                true)
              else ok)
            false
            t.out.(q - 1))
        (live i)
    in
    let lo, hi, _ = letter_dom store t i in
    src_ok
    && List.for_all (fun q' -> into.(q' - 1)) (live (i + 1))
    && List.for_all
         (fun v -> (not (mem v)) || (v >= t.smin && v < t.smin + t.w && sup.(v - t.smin)))
         (List.init (hi - lo + 1) (fun k -> lo + k))
  in
  let cached k = Bytes.get t.st k = state_of (Store.get store t.flags.(k)) in
  List.for_all cached (List.init (Bytes.length t.st) Fun.id)
  && List.for_all layer_ok (List.init (t.n + 1) Fun.id)
  && List.for_all edges_ok (List.init t.n Fun.id)

let propagate t store =
  detect store t;
  if Debug.enabled then
    Debug.check
      "regular (D-0232): the cached flag states are the store's, and a layer the \
       incremental call skips is at its fixpoint" (fun () -> skipped_hold store t);
  try
    fixed_flags store t;
    forward store t;
    backward store t;
    for i = 0 to t.n - 1 do
      if touched t i then values store t i
    done;
    fix_singletons store t;
    refresh store t;
    Propagator.Fixpoint
  with Found c ->
    (* [st] holds this call's writes on its dirty layers, which the backtrack will undo
       and the next call must not compare against: those layers are read afresh. *)
    for i = 0 to t.n do
      if t.ldirty.(i) then t.stale.(i) <- true
    done;
    Propagator.Conflict c

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
