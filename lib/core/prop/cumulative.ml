(* cumulative(s, d, r, cap): at every time point t, the tasks running at t -- task i runs
   over [s_i, s_i + d_i - 1] -- use at most [cap] of the resource, task i using [r_i].
   Durations, resources and the capacity are CONSTANTS; the starts are variables or
   constants.  disjunctive(s, d) is the case cap = 1, r_i = 1 and reaches this module
   through mznlib/fzn_disjunctive*.mzn; there is one propagator, not two.

   Governed by D-0096 (the design record, its census and its worked proof), SPEC 3.2 for
   the tag, and shaped on lib/core/prop/gcc.ml, whose rule A this module's derivation IS
   with a coefficient per task.  Read gcc.ml's header first: what is not restated here is
   the same there, deliberately -- the helpers below are gcc's with [r_i] threaded
   through, not a second design.

   ---------------------------------------------------------------------------
   Consistency level: [Checking]
   ---------------------------------------------------------------------------

   The filtering is TIME-TABLE: the compulsory part of task i is
   [hi(s_i), lo(s_i) + d_i - 1], the profile at t is the resource of the tasks whose
   compulsory part contains t, and a task j that would overload the profile at t is
   pushed off t.  That is not bounds consistency (which is NP-hard for cumulative), it is
   not edge-finding, energetic reasoning or not-first/not-last (each a later row, D-0096
   section 5), and it is all this module does.  What [Checking] obliges it delivers: with
   every start fixed, every task's compulsory part is its whole run, so an overloaded
   time point is a profile of fixed tasks and the push it causes empties a domain.

   ---------------------------------------------------------------------------
   The model rows: one per time point, over ORDER literals, and no auxiliary
   ---------------------------------------------------------------------------

   "task i runs at t" is "s_i in [t - d_i + 1, t]", and over the order encoding that is
   the indicator

     I_i(t)  =  s_i_ge_(a_i')  -  s_i_ge_(b_i' + 1),   a_i' = max(t - d_i + 1, dlo_i)
                                                       b_i' = min(t, dhi_i)

   -- gcc's identity (D-0078) over an interval instead of a value.  [s_ge_dlo] is the
   constant 1 and [s_ge_(dhi+1)] the constant 0, so a clipped end contributes a
   constant, folded into the right-hand side.  [make] posts, for every t at which the
   tasks that MAY run (by declared windows) carry more than [cap],

     sum_i r_i I_i(t)  <=  cap - (fixed-start load at t) - (folded constants)

   and nothing else: no `o_it` Boolean, no reification, no direct encoding.  A t at which
   the may-load is within [cap] gets no row because no assignment can violate it and no
   derivation would cite it.

   ---------------------------------------------------------------------------
   The derivation of a push (D-0096 section 3, with the checker's verdicts)
   ---------------------------------------------------------------------------

   j is pushed off t when C + r_j > avail(t), where C is the resource of the OTHER tasks
   compulsory at t and avail(t) = cap - fixed load.  In `>=` form the row is
   `- sum_i r_i I_i >= - avail(t) + folded`.  Add

     1. r_i x the at-least-one `I_i >= 1` of every compulsory i -- its two bound facts
        walked onto a_i' and b_i' + 1 by ladder chains ([alo_summands]); a ROOT bound is
        then cancelled with [Defining] and a decision's is left in the row and carried
        by the Reason (D-0064, gcc's [bound_cancels]);
     2. r_k x the free `I_k >= 0` of every other task in the row: the rung chain from
        a_k' to b_k' + 1, or one literal axiom at a clipped end ([drop_summands]);

   which leaves `r_j ~s_j_ge_(a_j') + r_j s_j_ge_(t+1) >= C - avail + r_j` (plus the
   non-root leftovers).  ONE division by r_j rounds the degree to 1 exactly when
   C + r_j > avail -- the test the propagator made.  j's own bound, walked onto a_j',
   then cancels the first literal and what is left is `s_j >= t + 1` (the upper push is
   the mirror, `s_j <= t - d_j`), lifted into D-0010's currency by [ladder_lift].

   OVERLOAD is the same derivation: a task compulsory at an overloaded t is pushed off t,
   past its own upper bound, and its residue is closed by that upper bound (gcc's "one
   more line"), so [Store.apply]'s [Failed] arm carries a real derivation and no `rup`
   conflict line claims a counting argument.

   NO NEW [Explanation] CONSTRUCTOR: [Combine]/[Weaken]/[Model_row]/[Defining]/[Clause].

   ---------------------------------------------------------------------------
   I-X10: [Needs_derivation], so every push is made under [Store.deriving_ahead]
   ---------------------------------------------------------------------------

   Measured in D-0096 on a satisfiable four-task scene: the bare trace line of a push is
   REFUSED by 3.0.2 ("not implied by reverse unit propagation") as soon as two tasks in
   the row are neither compulsory nor the target -- "an indicator is never negative" is
   the ladder, a second constraint, and unit propagation cannot sum it.  With ONE such
   task it propagates, which is how gcc's rule C lower push hid (D-0084).  So the push
   always runs under [deriving_ahead] and [Trace.derive_ahead] writes the [pol] first.

   ---------------------------------------------------------------------------
   Snapshots and I-X6
   ---------------------------------------------------------------------------

   As in gcc: every number a derivation reads is frozen into a [snap] at the moment of the
   push, and the thunk reads nothing from the store afterwards.  The row ids and the
   ladder ids are written once, before the first decision, and never move. *)

module Lit = Baguette_proof.Lit
module Encoding = Baguette_proof.Encoding
module Opb = Baguette_proof.Opb

(* ---------------------------------------------------------------------- the instance *)

(* How a caller names a task's start: a variable of the store, or a constant. *)
type start = Start of Var.t | Fixed of int

(* A MOVABLE task: its start is a variable declared over more than one value.  A fixed
   start -- a constant, or a one-value variable -- is folded into the rows' right-hand
   sides as load and is not a task of the propagator. *)
type task = { x : Var.t; name : string; dlo : int; dhi : int; dur : int; res : int }

(* One posted capacity row: at time [rt], the movable tasks may use at most [avail]
   (the capacity less the fixed-start load at [rt]).  [cid] is the row's id. *)
type row = { rt : int; avail : int; cid : int }

type t = {
  tasks : task array;
  rows : row option array; (* indexed by [rt - t0] *)
  t0 : int;
  enc : Encoding.t;
  ground : int option;
      (* the id of a row with NO literal that is false -- fixed-start load alone exceeds
         the capacity -- which nothing can be pushed against; reported as the conflict
         `pol <cid>` on the first run, [Linear]'s ground-contradiction route. *)
}

let name = "cumulative"
let consistency = Propagator.Checking
let vars t = Array.to_list (Array.map (fun tk -> tk.x) t.tasks)
let range a b = List.init (Stdlib.max 0 (b - a + 1)) (fun i -> a + i)

(* Merge repeated literals (the same start in two tasks) so the .opb row names each once.
   The row is the same linear form either way; the per-task derivation sums to it. *)
let merge_terms terms =
  let tbl = Hashtbl.create 16 in
  let order = ref [] in
  List.iter
    (fun (c, l) ->
      match Hashtbl.find_opt tbl l with
      | Some c0 -> Hashtbl.replace tbl l (c0 + c)
      | None ->
          Hashtbl.add tbl l c;
          order := l :: !order)
    terms;
  List.filter_map
    (fun l ->
      let c = Hashtbl.find tbl l in
      if c = 0 then None else Some (c, l))
    (List.rev !order)

(* Builds the instance AND posts its capacity rows into [enc].  Called at compile time,
   before [Encoding.start_proof], like every other model row.  [specs] is
   (start, duration, resource); a task with a zero duration or a zero resource uses
   nothing and is dropped, which is std's own `Tasks` filter.  A negative duration,
   resource or capacity is the caller's to refuse with a source position; here it is an
   [Invalid_argument]. *)
let make store enc ~cap (specs : (start * int * int) list) =
  if cap < 0 then invalid_arg "Cumulative.make: the capacity must be >= 0";
  List.iter
    (fun (_, d, r) ->
      if d < 0 || r < 0 then
        invalid_arg "Cumulative.make: durations and resources must be >= 0")
    specs;
  let live = List.filter (fun (_, d, r) -> d > 0 && r > 0) specs in
  let fixed = ref [] and movable = ref [] in
  List.iter
    (fun (s, d, r) ->
      match s with
      | Fixed n -> fixed := (n, d, r) :: !fixed
      | Start x ->
          let dm = Store.get store x in
          let lo = Domain.lo dm and hi = Domain.hi dm in
          if lo = hi then fixed := (lo, d, r) :: !fixed
          else
            movable :=
              { x; name = Store.name store x; dlo = lo; dhi = hi; dur = d; res = r }
              :: !movable)
    live;
  let fixed = List.rev !fixed and tasks = Array.of_list (List.rev !movable) in
  let starts =
    List.map (fun (n, _, _) -> n) fixed
    @ Array.to_list (Array.map (fun tk -> tk.dlo) tasks)
  in
  let ends =
    List.map (fun (n, d, _) -> n + d) fixed
    @ Array.to_list (Array.map (fun tk -> tk.dhi + tk.dur) tasks)
  in
  match starts with
  | [] -> { tasks; rows = [||]; t0 = 0; enc; ground = None }
  | _ ->
      let t0 = List.fold_left Stdlib.min max_int starts in
      let t1 = List.fold_left Stdlib.max min_int ends in
      let rows = Array.make (Stdlib.max 0 (t1 - t0)) None in
      let ground = ref None in
      for t = t0 to t1 - 1 do
        let fixed_load =
          List.fold_left
            (fun acc (n, d, r) -> if n <= t && t < n + d then acc + r else acc)
            0 fixed
        in
        let may = ref fixed_load and folded = ref 0 and terms = ref [] in
        Array.iter
          (fun tk ->
            let a' = Stdlib.max (t - tk.dur + 1) tk.dlo and b' = Stdlib.min t tk.dhi in
            if a' <= b' then (
              may := !may + tk.res;
              if a' > tk.dlo then terms := (tk.res, Lit.ge tk.name a') :: !terms
              else folded := !folded + tk.res;
              if b' < tk.dhi then terms := (-tk.res, Lit.ge tk.name (b' + 1)) :: !terms))
          tasks;
        if !may > cap then (
          let avail = cap - fixed_load in
          let terms = merge_terms (List.rev !terms) in
          let cid = Encoding.add_constraint enc (Opb.le terms (avail - !folded)) in
          rows.(t - t0) <- Some { rt = t; avail; cid };
          if terms = [] && !folded > avail && !ground = None then ground := Some cid)
      done;
      { tasks; rows; t0; enc; ground = !ground }

let row_at t time =
  let i = time - t.t0 in
  if i < 0 || i >= Array.length t.rows then None else t.rows.(i)

(* ------------------------------------------------------------------------ snapshots *)

type snap = {
  s_task : task;
  s_name : string;
  s_dlo : int;
  s_dhi : int;
  s_lo : int;
  s_hi : int;
  s_lo_root : bool;
  s_hi_root : bool;
}

let established_at_root store v ~lower =
  let sup = if lower then Store.lo_support store v else Store.hi_support store v in
  sup = Store.no_support || Store.level_of_index store sup = 0

let snap_of store tk =
  let d = Store.get store tk.x in
  {
    s_task = tk;
    s_name = tk.name;
    s_dlo = tk.dlo;
    s_dhi = tk.dhi;
    s_lo = Domain.lo d;
    s_hi = Domain.hi d;
    s_lo_root = established_at_root store tk.x ~lower:true;
    s_hi_root = established_at_root store tk.x ~lower:false;
  }

(* The task's window at t, clipped to its declared range: [a', b'], empty when a' > b'. *)
let window s ~time =
  (Stdlib.max (time - s.s_task.dur + 1) s.s_dlo, Stdlib.min time s.s_dhi)

let in_row s ~time =
  let a', b' = window s ~time in
  a' <= b'

let compulsory_at s ~time = s.s_hi <= time && time <= s.s_lo + s.s_task.dur - 1

(* ---------------------------------------------------------------------- explanations *)

let cid_of what = function
  | Some id -> id
  | None ->
      invalid_arg
        (Printf.sprintf
           "Cumulative: %s has no constraint id. Every line this module names is a \
            ladder rung or a capacity row [make] posted; a [None] here means the \
            propagator and the .opb have drifted apart."
           what)

let cite c id = Explanation.term c (Explanation.model_row id)

(* [c] x the ladder chain `x_ge_j - x_ge_m >= 0`, j < m (gcc's [rung_summands]). *)
let rung_summands t ~c x ~from_ ~to_ =
  List.map
    (fun u -> cite c (cid_of "ladder rung" (Encoding.consistency_id t.enc x u)))
    (range from_ (to_ - 1))

(* [c] x `I_i >= 1` for a compulsory task, as far as the ladder takes it; its two
   leftovers are its own bounds, which [cancels] removes where they are root ones. *)
let alo_summands t s ~time =
  let c = s.s_task.res and a', b' = window s ~time in
  (if a' > s.s_dlo then rung_summands t ~c s.s_name ~from_:a' ~to_:s.s_lo else [])
  @
  if b' < s.s_dhi then rung_summands t ~c s.s_name ~from_:(s.s_hi + 1) ~to_:(b' + 1)
  else []

let alo_cancels s ~time =
  let c = s.s_task.res and a', b' = window s ~time in
  (if a' > s.s_dlo && s.s_lo > s.s_dlo && s.s_lo_root then
     [ Explanation.defining c (Lit.ge s.s_name s.s_lo) ]
   else [])
  @
  if b' < s.s_dhi && s.s_hi < s.s_dhi && s.s_hi_root then
    [ Explanation.defining c (Lit.le s.s_name s.s_hi) ]
  else []

(* [c] x the free `I_k >= 0` for a task the push does not lean on (gcc's
   [drop_summands]). *)
let drop_summands t s ~time =
  let c = s.s_task.res and a', b' = window s ~time in
  if a' > s.s_dlo && b' < s.s_dhi then rung_summands t ~c s.s_name ~from_:a' ~to_:(b' + 1)
  else if a' <= s.s_dlo && b' < s.s_dhi then
    [ Explanation.weaken [ (c, Lit.le s.s_name b') ] ]
  else if a' > s.s_dlo && b' >= s.s_dhi then
    [ Explanation.weaken [ (c, Lit.ge s.s_name a') ] ]
  else []

(* D-0010's currency: gcc's [ladder_lift] restated in LINEAR size.

   The lift turns the single literal a push concludes into the ladder statement another
   propagator sums against: for a lower push to b, `sum_{k = dlo+1}^{b} y_ge_k >= w`
   with w = b - dlo (the leftover fact literals scaled alongside).  gcc builds it as w
   copies of the base plus, for every rung k beneath b, the whole chain k -> b: that is
   sum_k (b - k) = O(w^2) rung citations in ONE line.  MEASURED on 2008_rcpsp (starts of
   width ~160): 553 750 pol lines averaging 5.7 KB, 3.17 GB of the 3.37 GB proof.

   Here the units are walked down one rung at a time instead -- u_b = base,
   u_k = u_(k+1) + rung_k, which is `y_ge_k \/ leftovers >= 1` -- and summed once.  The
   statement is the same, and it is w short lines plus one of w terms: O(w).  [Justify]
   memoises by physical identity, so each u_k is written once although it is cited
   twice.  The upper lift is the mirror: u_(b+1) = base, u_(k+1) = u_k + rung_k is
   `~y_ge_(k+1) \/ leftovers >= 1`. *)
let rung_cite t x u = cite 1 (cid_of "ladder rung" (Encoding.consistency_id t.enc x u))

let ladder_lift t ~y ~lower ~bound base =
  let sum us = Explanation.combine (List.map (Explanation.term 1) us) 1 in
  let step prev u =
    Explanation.combine [ Explanation.term 1 prev; rung_cite t y.s_name u ] 1
  in
  if lower then
    let w = bound - y.s_dlo in
    if w < 2 then base
    else
      (* k = bound - 1 down to dlo + 1; u_k uses rung k (y_ge_(k+1) -> y_ge_k). *)
      let rec walk k prev acc =
        if k <= y.s_dlo then acc
        else
          let u = step prev k in
          walk (k - 1) u (u :: acc)
      in
      sum (base :: walk (bound - 1) base [])
  else
    let w = y.s_dhi - bound in
    if w < 2 then base
    else
      (* k = bound + 2 up to dhi; u_k uses rung k - 1 (y_ge_k -> y_ge_(k-1)). *)
      let rec walk k prev acc =
        if k > y.s_dhi then acc
        else
          let u = step prev (k - 1) in
          walk (k + 1) u (u :: acc)
      in
      sum (base :: walk (bound + 2) base [])

(* The push of [y] off [time]: [lower] is `y >= time + 1`, otherwise
   `y <= time - d_y`.  [halls] are the OTHER tasks compulsory at [time], [others] every
   remaining task of the row but [y]. *)
let prune_expl t ~row ~halls ~others ~y ~lower ~bound =
  let time = row.rt in
  let moves = if lower then bound <= y.s_hi else bound >= y.s_lo in
  Explanation.deferred (fun () ->
      let a', b' = window y ~time in
      let a = time - y.s_task.dur + 1 in
      let low_side = a' > y.s_dlo and high_side = b' < y.s_dhi in
      let want_low = lower || a - 1 < y.s_lo in
      let want_high = (not lower) || time + 1 > y.s_hi in
      let counted =
        Explanation.combine
          (cite 1 row.cid
           :: List.concat_map
                (fun s -> alo_summands t s ~time @ alo_cancels s ~time)
                halls
          @ List.concat_map (fun s -> drop_summands t s ~time) others)
          y.s_task.res
      in
      let y_low =
        if low_side && want_low then rung_summands t ~c:1 y.s_name ~from_:a' ~to_:y.s_lo
        else []
      in
      let y_high =
        if high_side && want_high then
          rung_summands t ~c:1 y.s_name ~from_:(y.s_hi + 1) ~to_:(b' + 1)
        else []
      in
      let y_cancel =
        (if low_side && want_low && y.s_lo > y.s_dlo && y.s_lo_root then
           [ Explanation.defining 1 (Lit.ge y.s_name y.s_lo) ]
         else [])
        @
        if high_side && want_high && y.s_hi < y.s_dhi && y.s_hi_root then
          [ Explanation.defining 1 (Lit.le y.s_name y.s_hi) ]
        else []
      in
      let e =
        match y_low @ y_high @ y_cancel with
        | [] -> counted
        | rest -> Explanation.combine (Explanation.term 1 counted :: rest) 1
      in
      if moves then ladder_lift t ~y ~lower ~bound e else e)

(* Every task of the row is named, at both bounds, for gcc's reason: the derivation
   weakens the indicator of every task that is neither compulsory nor the target, and
   D-0026's reverse agreement check requires the reason to name them all.  A fact the
   derivation did not need weakens the trace line, which is sound.

   UNLIKE gcc, the facts of a bound's SUPPORT are not appended.  gcc needs them for its
   [fact_summand] clause `l \/ ~facts(support)`; nothing here cites a non-root bound by
   anything but its own literal, which stays in the row and is the fact named below.
   Appending them is also what made the first draft EXPONENTIAL: a time-table push
   rests on earlier pushes of the same instance, each reason copied its supports'
   reasons, and on a six-task unit-capacity scene (horizon 8) eleven search nodes took
   over five seconds before the copies were removed. *)
let scope_facts snaps =
  List.concat_map
    (fun s ->
      [
        Reason.at_least ~name:s.s_name ~decl:s.s_dlo s.s_lo;
        Reason.at_most ~name:s.s_name ~decl:s.s_dhi s.s_hi;
      ])
    snaps

(* --------------------------------------------------------------------- the sweep *)

exception Moved
exception Found of Store.conflict

(* One pass: the compulsory profile from a fresh snapshot, then for each task the first
   overloaded point of its earliest run (a lower push) or of its latest run (an upper
   push).  A pass that pushed anything restarts, so every push reads a CURRENT snapshot
   (gcc's and alldiff's rule). *)
let pass t store =
  let snaps = Array.map (snap_of store) t.tasks in
  let n_rows = Array.length t.rows in
  let profile = Array.make n_rows 0 in
  Array.iter
    (fun s ->
      for time = s.s_hi to s.s_lo + s.s_task.dur - 1 do
        let i = time - t.t0 in
        if i >= 0 && i < n_rows then profile.(i) <- profile.(i) + s.s_task.res
      done)
    snaps;
  let overloaded j time =
    match row_at t time with
    | None -> None
    | Some row ->
        let own = if compulsory_at j ~time then j.s_task.res else 0 in
        if profile.(time - t.t0) - own + j.s_task.res > row.avail then Some row else None
  in
  let push j row ~lower bound =
    let time = row.rt in
    let in_scope = List.filter (fun s -> in_row s ~time) (Array.to_list snaps) in
    let others_of = List.filter (fun s -> s != j) in_scope in
    let halls, others = List.partition (fun s -> compulsory_at s ~time) others_of in
    let why =
      Reason.because
        ~concludes:
          (Some
             (if lower then Reason.at_least ~name:j.s_name ~decl:j.s_dlo bound
              else Reason.at_most ~name:j.s_name ~decl:j.s_dhi bound))
        (scope_facts in_scope)
        (prune_expl t ~row ~halls ~others ~y:j ~lower ~bound)
    in
    let prune () =
      if lower then Store.set_lo store j.s_task.x bound why
      else Store.set_hi store j.s_task.x bound why
    in
    match Store.deriving_ahead store prune with
    | Store.Conflict c -> raise (Found c)
    | Store.Changed -> raise Moved
    | Store.Unchanged -> ()
  in
  Array.iter
    (fun j ->
      let d = j.s_task.dur in
      (* The LATEST overloaded point of the earliest run gives the strongest lower push,
         the EARLIEST of the latest run the strongest upper one; any other is valid and
         merely slower, since the pass restarts on every change. *)
      for time = j.s_lo + d - 1 downto j.s_lo do
        match overloaded j time with
        | Some row -> push j row ~lower:true (time + 1)
        | None -> ()
      done;
      for time = j.s_hi to j.s_hi + d - 1 do
        match overloaded j time with
        | Some row -> push j row ~lower:false (time - d)
        | None -> ()
      done)
    snaps

let rec loop t store =
  if
    try
      pass t store;
      false
    with Moved -> true
  then loop t store

let propagate t store =
  match t.ground with
  | Some cid ->
      Propagator.Conflict
        (Store.conflict store
           (Reason.because ~concludes:None Reason.none
              (Explanation.combine [ cite 1 cid ] 1)))
  | None -> (
      try
        loop t store;
        Propagator.Fixpoint
      with Found c -> Propagator.Conflict c)
