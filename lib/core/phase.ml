(* phase.ml: PHASE SAVING over order literals -- the value a variable was last fixed at
   (M10-search-strategy-T2, docs/DECISIONS.md D-0137 section 3; Pipatsrisawat and
   Darwiche, SAT 2007).

   Consistency level: none -- this is not a propagator. Governing records: D-0137 section 3
   (what is saved, what it changes), docs/SPEC.md 3.4 (it is opt-in: `--phase-saving`).

   ---------------------------------------------------------------------------
   What is saved, and when
   ---------------------------------------------------------------------------

   One value per variable: the value it was FIXED at, read when the decision level that
   fixed it is UNDONE. lib/core/search.ml calls [save_level] immediately before each
   [Store.backtrack], and this walks the entries of the level about to be popped. An entry
   whose [now] domain is a single value saves that value for its variable; an entry that
   only narrowed saves nothing. Within one level a domain only shrinks (I-D3), so once a
   variable is fixed in a level its value cannot change in that level and the walk's order
   does not matter. That is SAT's "save on unassignment", and for a Boolean it is exactly
   the saved polarity.

   The cost is one look at each popped entry, once, which is what popping it already
   costs. Nothing is saved on a path that never backtracks, and nothing needs to be. To
   FIND the level's first entry it pays O(depth) more per backtrack: [Store.level_marks]
   lists every mark and [List.nth] walks to the level's (M16-file-review-T3, D-0191). That
   is linear in the depth per node, quadratic only in a run whose every node backtracks
   from the bottom of a deep stack; measured 0.2 % median and 1.0 % at most of the lane's
   samples under `--restarts luby:1 --phase-saving`, so it stays until the store offers
   one mark by its level.

   ---------------------------------------------------------------------------
   What it changes: the value choice, never the variable choice
   ---------------------------------------------------------------------------

   [saved] answers "is there a saved value still in [v]'s domain?". Turning that into a
   decision -- always a one-literal split, see [Search.value_decision] and D-0137 section
   3's addendum on why not D-0077's assignment -- is Search's, because the decision type
   is Search's and this module must not depend on it.
   No decision shape and no proof line is added (D-0137 section 3).

   This module never reads the live store except through [save_level]'s walk of the
   level being popped and [saved]'s membership test, and holds no state that a backtrack
   could make stale: a saved value is a HINT, checked against the live domain each time it
   is used, so a value that has since been pruned away simply is not offered. *)

type t = {
  value : int array;
  has : Bytes.t; (* '\001' where [value] holds a saved value *)
  mutable n_saves : int;
      (* values written, over the run: a measurement, read by --stats *)
  mutable n_used : int; (* decisions whose value a saved phase chose *)
}

let create n_vars =
  { value = Array.make n_vars 0; has = Bytes.make n_vars '\000'; n_saves = 0; n_used = 0 }

(* Before [Store.backtrack store]: record every variable the current level fixed. *)
let save_level t store =
  let lvl = Store.level store in
  if lvl > 0 then
    let marks = Store.level_marks store in
    let from = List.nth marks (lvl - 1) in
    let upto = Store.trail_length store in
    for i = from to upto - 1 do
      let e = Store.trail_entry store i in
      let d = e.Store.now in
      if Domain.is_fixed d then
        let v = Var.to_int e.Store.var in
        if v >= 0 && v < Array.length t.value then (
          t.value.(v) <- Domain.lo d;
          Bytes.set t.has v '\001';
          t.n_saves <- t.n_saves + 1)
    done

(* The saved value of [v], if there is one and it is still in [v]'s live domain. *)
let saved t store v =
  let i = Var.to_int v in
  if i < 0 || i >= Array.length t.value || Bytes.get t.has i = '\000' then None
  else
    let s = t.value.(i) in
    if Domain.mem (Store.get store v) s then Some s else None

let note_used t = t.n_used <- t.n_used + 1
let n_saves t = t.n_saves
let n_used t = t.n_used
