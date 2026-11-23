(* table(x, T): the tuple x_1 .. x_n is one of the T tuples of a constant table. Reaches
   the solver as `baguette_table(x, t, s)` (and `baguette_table_bool`, over 0..1) through
   mznlib/fzn_table_int.mzn and fzn_table_bool.mzn, [t] the tuples flattened row-major and
   [s] one SELECTOR Boolean per tuple the library introduces. docs/DECISIONS.md D-0206 is
   this module's record (M18-coverage-T1). Governed by docs/SPEC.md 3.2 (consistency) and
   3.3 (explanations).

   ---------------------------------------------------------------------------
   The selectors are STORE VARIABLES, as regular.ml's state flags and member.ml's
   selectors are
   ---------------------------------------------------------------------------

   s_t means "x is tuple t". A tuple that dies is a selector whose upper bound drops to 0:
   a trail entry with a reason like any other, whose line lib/core/trace.ml writes. The
   store is therefore the reversible state compact-table keeps in a bitset of its own,
   and this module keeps nothing across calls but the tails below.

   The .opb rows (lib/flatzinc/compile.ml's [post_table]), over the selectors and the
   ORDER literals of x:

     ALO      s_1 + ... + s_T >= 1
     DEF_t    k ~s_t + sum_i ([x_i >= t_i] + ~[x_i >= t_i + 1]) >= k

   a literal a declared bound makes true dropped, k the number left ([def_lits]); a
   literal that is constant false (t_i outside x_i's declared hull, or a constant cell
   that differs) makes DEF_t the unit `~s_t`. DEF_t is D-0184's DEF1 shape, s_t -> x = t
   as ONE row: it propagates both ways by unit propagation, since any literal false leaves
   the rest below k and forces ~s_t, and s_t true forces every literal.

   ---------------------------------------------------------------------------
   Consistency level: DOMAIN on (x, s), and [Aliased] when it is not
   ---------------------------------------------------------------------------

   One call, at its fixpoint:

     K  s_t dies when some t_i is not in dom(x_i);
     C  no live tuple is a conflict (ALO); one live and not set is set to 1 (ALO);
     E  a selector set to 1 fixes every x_i to t_i (DEF_t);
     S  x_i <> v when no live tuple has t_i = v.

   K, C, E repeat until E changes nothing; S kills no tuple (a value it removes is carried
   by dead tuples only). Afterwards every remaining value of the scope extends to a
   solution: v in x_i through a live tuple with t_i = v, s_t = 1 through t, s_t = 0
   through another live tuple (or C has fixed s_t). That is GAC on x, and std's element
   decomposition over a shared index was GAC too (a star around the index): what this
   module changes is the SIZE, T + 1 rows against about (2n + 3) T, and no index ladder
   (D-0206 section 1). With one variable twice in x, a live tuple can disagree with itself
   on it and the filtering is no longer complete: compile.ml packs that instance as
   [Aliased], the same code declared [Checking]. Checking is unconditional: with x fixed,
   K kills every tuple but x's own, and none left is ALO's conflict.

   The call is idempotent at its fixpoint when x names distinct variables, and compile.ml
   says so at the packing site for that instance only.

   ---------------------------------------------------------------------------
   The proof: every pruning is ONE `rup`, its facts on its tail
   ---------------------------------------------------------------------------

     K  ~s_t \/ ~F. F is the WEAKEST bound excluding t_i (x_i >= t_i + 1 or
        x_i <= t_i - 1), or for an interior hole the facts of its remover, or nothing when
        t_i is outside the declared hull. Assume s_t and F: DEF_t forces x_i = t_i against
        the bound, or against the hole's own trace line.
     C  s_t := 1: the other tuples' tails, so their lines fire, and ALO. A conflict: every
        tuple's tail.
     E  x_i >= t_i, x_i <= t_i: s_t's tail, so s_t, and DEF_t.
     S  x_i <> v: the tails of the dead tuples with t_i = v, plus the bound fact pinning v
        when v is a bound (regular.ml's P3). Assume x_i = v: every tuple with t_i <> v
        dies on DEF_t through x_i's ladder, every tuple with t_i = v on its own line, and
        ALO is empty.

   The reasons are ON THE LETTERS (D-0151): where a line would cite "s_t <= 0", it cites
   the TAIL of the line that killed s_t, which is letter facts by the same rule. A
   selector moved by anything other than this instance (a decision, a learned clause) has
   no tail of ours and is cited as itself. The tails are kept as the STRONGEST fact per
   letter and direction, so a tail has at most two facts per letter; a K tail has at most
   one. The machinery (slots, stamped scratch arrays, tails cached with the trail entry
   they belong to and read back through [Store.hi_support] / [lo_support]) is regular.ml's,
   copied rather than shared, as member.ml copied it.

   The justification is [Explanation.clause] of the claim and the negated facts, deferred:
   no new constructor, no line written ahead, a [Single_row] family in test_trace.ml's
   sense (one constraint, several rows, the earlier trace lines on the page).

   ---------------------------------------------------------------------------
   The scan: compact-table's two devices, without its reversible bitset
   ---------------------------------------------------------------------------

   Per (position, value) the static list of the tuples carrying it ([sup]), and per call
   a bitset of the live tuples read off the selectors ([live]). K builds, per position,
   the mask of the tuples some value of dom(x_i) supports, by OR-ing in those lists, and
   kills live AND NOT mask. S asks each value for a live tuple in its list, starting from
   its RESIDUE, the last tuple found supporting it (Lecoutre's residues, which compact-
   table also keeps). A call costs O(T) to read the selectors, plus per position the
   number of tuples its domain supports, plus one probe per value while its residue
   lives. The cost of a dead tuple is its trail entry and its trace line, as a dead
   regular flag's is. *)

module Lit = Baguette_proof.Lit

(* One position: a variable with its DECLARED hull, or a constant the flattener left. *)
type cell = Fixed of int | Cell of { var : Var.t; name : string; dlo : int; dhi : int }

(* DEF_t's literals for the tuple [tup] (one value per cell), as [post_table] writes them:
   [None] when one is constant false (the row is then the unit ~s_t), [Some []] when
   every literal is constant true (no row). *)
let def_lits (cells : cell array) (tup : int array) : Lit.t list option =
  let exception False in
  try
    Some
      (List.concat
         (List.mapi
            (fun i c ->
              let v = tup.(i) in
              match c with
              | Fixed k -> if k = v then [] else raise False
              | Cell { name; dlo; dhi; _ } ->
                  if v < dlo || v > dhi then raise False
                  else
                    (if v > dlo then [ Lit.ge name v ] else [])
                    @ if v < dhi then [ Lit.negate (Lit.ge name (v + 1)) ] else [])
            (Array.to_list cells)))
  with False -> None

(* A selector's tail as this instance wrote it: [keys] packs (key, value) pairs, a key
   being [2 * slot] for a letter's lower bound and [2 * slot + 1] for its upper one;
   [others] is what is not a bound of a letter (a hole remover's facts elsewhere, a
   selector a decision moved). [entry] is the trail entry the tail belongs to. *)
type tail = { entry : Store.entry; keys : int array; others : Reason.fact list }

type t = {
  n : int; (* positions *)
  nt : int; (* tuples *)
  xs : cell array;
  tup : int array; (* nt * n, row-major *)
  sels : Var.t array;
  snames : string array;
  vars : Var.t list;
  (* The letters as SLOTS, one per distinct variable of x. *)
  slot : int array; (* position -> slot, -1 for a [Fixed] cell *)
  slot_name : string array;
  slot_dlo : int array;
  slot_dhi : int array;
  slot_of_name : (string, int) Hashtbl.t;
  tails : tail option array; (* per tuple *)
  aliased : bool; (* x names a variable twice: S can kill a tuple, so the call loops *)
  (* Supports: position i's column spans cmin.(i) .. cmin.(i) + Array.length sup.(i) - 1;
     sup.(i).(v - cmin.(i)) lists the tuples with t_i = v, increasing. *)
  cmin : int array;
  sup : int array array array;
  residue : int array array; (* same shape as [sup]: an index into the list *)
  (* Scratch, reused by every call. *)
  live : int array; (* bitset of the live tuples, words of [wbits] *)
  mask : int array;
  best : int array;
  seen : int array;
  keys_in : int array;
  mutable nkeys : int;
  mutable others_rev : Reason.fact list;
  mutable stamp : int;
}

let wbits = Sys.int_size
let nwords nt = (nt + wbits - 1) / wbits
let bit_set a k = a.(k / wbits) <- a.(k / wbits) lor (1 lsl (k mod wbits))
let bit_clear a k = a.(k / wbits) <- a.(k / wbits) land lnot (1 lsl (k mod wbits))
let bit_mem a k = a.(k / wbits) land (1 lsl (k mod wbits)) <> 0

(* The index of the single bit set in [b]. *)
let bit_index b =
  let i = ref 0 and b = ref b in
  if !b land 0xFFFFFFFF = 0 then (
    b := !b lsr 32;
    i := !i + 32);
  if !b land 0xFFFF = 0 then (
    b := !b lsr 16;
    i := !i + 16);
  if !b land 0xFF = 0 then (
    b := !b lsr 8;
    i := !i + 8);
  if !b land 0xF = 0 then (
    b := !b lsr 4;
    i := !i + 4);
  if !b land 0x3 = 0 then (
    b := !b lsr 2;
    i := !i + 2);
  if !b land 0x1 = 0 then incr i;
  !i

let make store ~xs ~tuples ~sels : t =
  let n = Array.length xs and nt = Array.length sels in
  if Array.length tuples <> n * nt then
    invalid_arg "Table.make: the tuples are not T rows of n values";
  let value k i = tuples.((k * n) + i) in
  let cmin = Array.make n 0 in
  let sup =
    Array.init n (fun i ->
        if nt = 0 then [||]
        else
          let lo = ref max_int and hi = ref min_int in
          for k = 0 to nt - 1 do
            lo := Int.min !lo (value k i);
            hi := Int.max !hi (value k i)
          done;
          cmin.(i) <- !lo;
          let counts = Array.make (!hi - !lo + 1) 0 in
          for k = 0 to nt - 1 do
            let j = value k i - !lo in
            counts.(j) <- counts.(j) + 1
          done;
          let lists = Array.map (fun c -> Array.make c 0) counts in
          Array.fill counts 0 (Array.length counts) 0;
          for k = 0 to nt - 1 do
            let j = value k i - !lo in
            lists.(j).(counts.(j)) <- k;
            counts.(j) <- counts.(j) + 1
          done;
          lists)
  in
  let letters =
    Array.fold_right
      (fun c acc ->
        match c with
        | Cell { var; _ } when not (List.exists (Var.equal var) acc) -> var :: acc
        | _ -> acc)
      xs []
  in
  let slot_of_name = Hashtbl.create 16 in
  let names = ref [] in
  let slot =
    Array.map
      (function
        | Fixed _ -> -1
        | Cell { name; dlo; dhi; _ } -> (
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
  {
    n;
    nt;
    xs;
    tup = tuples;
    sels;
    snames = Array.map (Store.name store) sels;
    vars = letters @ Array.to_list sels;
    slot;
    slot_name = Array.map (fun (nm, _, _) -> nm) slots;
    slot_dlo = Array.map (fun (_, lo, _) -> lo) slots;
    slot_dhi = Array.map (fun (_, _, hi) -> hi) slots;
    slot_of_name;
    tails = Array.make nt None;
    aliased =
      ns
      < Array.length
          (Array.of_list
             (List.filter
                (function Cell _ -> true | Fixed _ -> false)
                (Array.to_list xs)));
    cmin;
    sup;
    residue = Array.map (Array.map (fun _ -> 0)) sup;
    live = Array.make (Int.max (nwords nt) 1) 0;
    mask = Array.make (Int.max (nwords nt) 1) 0;
    best = Array.make (Int.max (2 * ns) 1) 0;
    seen = Array.make (Int.max (2 * ns) 1) 0;
    keys_in = Array.make (Int.max (2 * ns) 1) 0;
    nkeys = 0;
    others_rev = [];
    stamp = 0;
  }

let vars t = t.vars
let dead store t k = Domain.hi (Store.get store t.sels.(k)) = 0
let is_set store t k = Domain.lo (Store.get store t.sels.(k)) = 1
let dead_fact t k = Reason.at_most ~name:t.snames.(k) ~decl:1 0
let set_fact t k = Reason.at_least ~name:t.snames.(k) ~decl:0 1

(* The live domain of position i, as lo, hi and a membership test. *)
let cell_dom store t i =
  match t.xs.(i) with
  | Fixed c -> (c, c, fun v -> v = c)
  | Cell { var; _ } ->
      let d = Store.get store var in
      (Domain.lo d, Domain.hi d, Domain.mem d)

(* The tuples carrying value [v] at position i (empty outside the column). *)
let supports t i v =
  let j = v - t.cmin.(i) in
  if t.nt = 0 || j < 0 || j >= Array.length t.sup.(i) then [||] else t.sup.(i).(j)

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

(* A fact read elsewhere (a remover's, a foreign selector's): onto its letter's key when
   it names a letter of x, else kept once as it is. *)
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

(* ---------------------------------------------------------- the selectors' tails *)

(* The tail of the line that killed (set, if [~set]) selector k, as THIS instance wrote
   it; or the selector's own fact when anything else moved it. *)
let sel_tail store t ~set k : tail =
  let v = t.sels.(k) in
  let own () =
    {
      entry = Store.dummy_entry;
      keys = [||];
      others = [ (if set then set_fact t k else dead_fact t k) ];
    }
  in
  let pos = if set then Store.lo_support store v else Store.hi_support store v in
  if pos = Store.no_support then own ()
  else
    let e = Store.trail_entry store pos in
    match t.tails.(k) with Some tl when tl.entry == e -> tl | _ -> own ()

let add_sel store t ~set k = add_tail t (sel_tail store t ~set k)

(* The facts behind the hole [v] of position i: those of the entry that punched it; a
   declared hole ([None]) is a row of the .opb and needs none. *)
let add_hole store t i v =
  match t.xs.(i) with
  | Fixed _ -> ()
  | Cell { var; _ } -> (
      match Store.remover store ~before:(Store.trail_length store) ~var v with
      | None -> ()
      | Some e -> List.iter (add_fact t) (Reason.facts e.Store.reason))

let clause_expl claim fs =
  Explanation.deferred (fun () ->
      Explanation.clause (claim @ List.map Lit.negate (Reason.lits_of_facts fs)))

let conflict_now store t =
  let fs, _, _ = finish t in
  Store.conflict store (Reason.because ~concludes:None fs (clause_expl [] fs))

(* Move selector k (kill it, or set it with [~set]) on the reason under way, and cache
   its tail against the entry. Killing a set selector is a conflict on the same facts
   plus the selector's own tail. *)
let move_sel store t ~set k =
  if (not set) && is_set store t k then (
    add_sel store t ~set:true k;
    raise (Found (conflict_now store t)))
  else
    let fs, packed, others = finish t in
    let concl = if set then set_fact t k else dead_fact t k in
    let claim = Option.to_list (Reason.lit_of_fact concl) in
    let v = t.sels.(k) in
    let why = Reason.because ~concludes:(Some concl) fs (clause_expl claim fs) in
    match if set then Store.set_lo store v 1 why else Store.set_hi store v 0 why with
    | Store.Conflict c -> raise (Found c)
    | Store.Changed ->
        let e =
          Store.trail_entry store
            (if set then Store.lo_support store v else Store.hi_support store v)
        in
        t.tails.(k) <- Some { entry = e; keys = packed; others }
    | Store.Unchanged -> ()

(* ------------------------------------------------------------------ the steps *)

(* The live tuples, read off the selectors; the set ones, returned. *)
let read_live store t =
  Array.fill t.live 0 (Array.length t.live) 0;
  let set = ref [] in
  for k = t.nt - 1 downto 0 do
    let d = Store.get store t.sels.(k) in
    if Domain.hi d = 1 then (
      bit_set t.live k;
      if Domain.lo d = 1 then set := k :: !set)
  done;
  !set

(* K's reason for tuple k, excluded at position i: the weakest bound past t_i, or the
   hole's remover, or nothing outside the declared hull (DEF_t is then the unit). *)
let exclusion store t k i =
  start t;
  let v = t.tup.((k * t.n) + i) in
  match t.xs.(i) with
  | Fixed _ -> ()
  | Cell { dlo; dhi; _ } ->
      let lo, hi, _ = cell_dom store t i in
      let s = t.slot.(i) in
      if v < lo then (if v >= dlo then add_key t (2 * s) (v + 1))
      else if v > hi then (if v <= dhi then add_key t ((2 * s) + 1) (v - 1))
      else add_hole store t i v

(* Step K over every position: kill live AND NOT (tuples dom(x_i) supports). Returns the
   set selectors, read with the live ones (a set selector K would kill is a conflict). *)
let kill_pass store t =
  let set = read_live store t in
  for i = 0 to t.n - 1 do
    let lo, hi, mem = cell_dom store t i in
    Array.fill t.mask 0 (Array.length t.mask) 0;
    let a = Int.max lo t.cmin.(i)
    and b = Int.min hi (t.cmin.(i) + Array.length t.sup.(i) - 1) in
    for v = a to b do
      if mem v then Array.iter (fun k -> bit_set t.mask k) (supports t i v)
    done;
    for w = 0 to Array.length t.live - 1 do
      let gone = ref (t.live.(w) land lnot t.mask.(w)) in
      while !gone <> 0 do
        let b = !gone land - !gone in
        gone := !gone lxor b;
        let k = (w * wbits) + bit_index b in
        exclusion store t k i;
        move_sel store t ~set:false k;
        bit_clear t.live k
      done
    done
  done;
  set

(* Step C on the live bitset K left. Returns the selector it set, if it set one. *)
let count_pass store t =
  (* 0, 1 or "2 or more" live tuples, and the one when it is one: a word with two bits
     set, or a second non-zero word, ends the scan. *)
  let count = ref 0 and last = ref (-1) and w = ref 0 in
  let nw = Array.length t.live in
  while !count < 2 && !w < nw do
    let word = t.live.(!w) in
    if word <> 0 then
      if word land (word - 1) <> 0 then count := 2
      else (
        incr count;
        last := (!w * wbits) + bit_index word);
    incr w
  done;
  if !count = 0 then (
    start t;
    for k = 0 to t.nt - 1 do
      add_sel store t ~set:false k
    done;
    raise (Found (conflict_now store t)))
  else if !count = 1 && not (is_set store t !last) then (
    start t;
    for k = 0 to t.nt - 1 do
      if k <> !last then add_sel store t ~set:false k
    done;
    move_sel store t ~set:true !last;
    [ !last ])
  else []

(* Step E: a set selector fixes x to its tuple. Over distinct variables every t_i is in
   dom(x_i) (K has run), so no push can fail; with x naming a variable twice, an earlier
   push of the same tuple can have moved it past t_i, and that conflict is built here, on
   the selector's tail and the bound it crossed, rather than left to [Store.apply]'s
   [Failed] arm, whose reason is empty (Store.unattributed_conflict). *)
let enforce_pass store t set =
  let changed = ref false in
  List.iter
    (fun k ->
      Array.iteri
        (fun i c ->
          match c with
          | Fixed _ -> ()
          | Cell { var; name; dlo; dhi } ->
              let v = t.tup.((k * t.n) + i) in
              let s = t.slot.(i) in
              let push concl apply =
                start t;
                add_sel store t ~set:true k;
                let fs, _, _ = finish t in
                let claim = Option.to_list (Reason.lit_of_fact concl) in
                match
                  apply (Reason.because ~concludes:(Some concl) fs (clause_expl claim fs))
                with
                | Store.Conflict c -> raise (Found c)
                | Store.Changed -> changed := true
                | Store.Unchanged -> ()
              in
              let crossed key bound =
                start t;
                add_sel store t ~set:true k;
                add_key t key bound;
                raise (Found (conflict_now store t))
              in
              let d = Store.get store var in
              if Domain.hi d < v then crossed ((2 * s) + 1) (v - 1);
              if Domain.lo d > v then crossed (2 * s) (v + 1);
              if Domain.lo d < v then
                push (Reason.at_least ~name ~decl:dlo v) (Store.set_lo store var v);
              let d = Store.get store var in
              if Domain.hi d > v then
                push (Reason.at_most ~name ~decl:dhi v) (Store.set_hi store var v))
        t.xs)
    set;
  !changed

(* What removing [v] from [d] concludes: the settled bound when [v] is a bound, nothing
   for a hole (regular.ml's, the same walk). *)
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

(* Is value v of position i carried by a live tuple? From its residue first. *)
let supported t i v =
  let l = supports t i v in
  let m = Array.length l in
  if m = 0 then false
  else
    let j = v - t.cmin.(i) in
    let r = t.residue.(i).(j) in
    if bit_mem t.live l.(r) then true
    else
      let rec scan q =
        q < m
        && (bit_mem t.live l.(q)
            &&
            (t.residue.(i).(j) <- q;
             true)
           || scan (q + 1))
      in
      scan 0

(* Step S: remove every value of position i no live tuple carries. *)
let values store t i =
  match t.xs.(i) with
  | Fixed _ -> ()
  | Cell { var; name; dlo; dhi } ->
      let s = t.slot.(i) in
      Domain.iter
        (fun v ->
          if not (supported t i v) then (
            let d = Store.get store var in
            start t;
            Array.iter (fun k -> add_sel store t ~set:false k) (supports t i v);
            if v = Domain.lo d && v > dlo then add_key t (2 * s) v;
            if v = Domain.hi d && v < dhi then add_key t ((2 * s) + 1) v;
            if Domain.is_fixed d then raise (Found (conflict_now store t));
            let fs, _, _ = finish t in
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
        (Store.get store var)

(* With x naming a variable twice, S at one position can remove a value another position's
   live tuple carries, so the call goes round again until S changes nothing; over distinct
   variables it cannot, and one round is the fixpoint. *)
let propagate t store =
  try
    let rec round () =
      (* [t.live] is exact after the last K: C sets but kills nothing, and the last E
         changed nothing. *)
      let rec settle () =
        let set = kill_pass store t in
        let fixed = count_pass store t in
        if enforce_pass store t (fixed @ set) then settle ()
      in
      settle ();
      let mark = Store.trail_length store in
      for i = 0 to t.n - 1 do
        values store t i
      done;
      if t.aliased && Store.trail_length store > mark then round ()
    in
    round ();
    Propagator.Fixpoint
  with Found c -> Propagator.Conflict c

let name = "table"
let consistency = Propagator.Domain

(* The same code over an x that names one variable twice: the positions are coupled and
   the filtering is no longer complete, so the claim drops to [Checking] (see the header).
   One implementation; the packed name says which. *)
module Aliased = struct
  type nonrec t = t

  let name = name
  let consistency = Propagator.Checking
  let vars = vars
  let propagate = propagate
end
