(* engine.ml: the propagation fixpoint (M1-T10, Part 1).

   docs/ARCHITECTURE.md section 5: "A priority queue of propagator ids ... pops, runs,
   applies the resulting changes to the trail, and re-queues the propagators watching
   the changed variables." This is that queue, minus the cost-class ordering
   (docs/ARCHITECTURE.md's "cheap bounds propagators before all_different" -- M1 has no
   propagator above [Bounds] consistency yet, so a plain FIFO is honest; a priority
   ordering is a scheduling refinement for when that stops being true, not a
   correctness requirement, and adding one now would be sorting a list of one).

   Waking is by watched variable, not "run everyone again" (the task's explicit
   requirement, and the only way I-P2 -- fixpoint means propagating again changes
   nothing -- can be cheap to hold). [Store] does not track "who changed since I last
   looked" itself, so this module keeps its own trail cursor and, after each
   propagator call, diffs the trail against it to find the newly-touched variables
   (docs/ARCHITECTURE.md section 3: the trail is exactly the log of domain changes,
   most-recent-first). That is O(new entries) per propagator call, not O(n_vars); for
   the domain sizes and propagator counts M1 deals with, simplicity here is worth more
   than a smarter incremental cursor would be.

   This module never touches the proof (the task's Part 1 instruction, and
   docs/ARCHITECTURE.md's "Deferred explanations"): a [Conflict] hands back whatever
   [Explanation.t] the failing propagator built, unrendered, and it is search's job
   (search.ml) to decide whether and how a reason is ever turned into proof rules. *)

type outcome = Fixpoint | Conflict of Explanation.t

type t = {
  instances : Propagator.instance array;
  (* var -> ids of the propagator instances that read it. Built once at [create] time
     from each instance's [inst_vars]; instances never change their variable set after
     that, so the table does not need to be rebuilt per call. *)
  watchers : (Var.t, int list) Hashtbl.t;
}

let create (instances : Propagator.instance list) : t =
  let watchers = Hashtbl.create 64 in
  List.iter
    (fun (inst : Propagator.instance) ->
      List.iter
        (fun v ->
          let cur = try Hashtbl.find watchers v with Not_found -> [] in
          if not (List.mem inst.Propagator.id cur) then
            Hashtbl.replace watchers v (inst.Propagator.id :: cur))
        inst.Propagator.inst_vars)
    instances;
  { instances = Array.of_list instances; watchers }

let n_instances t = Array.length t.instances

(* Every newly-touched variable's watchers, for the trail entries pushed since
   [since] -- the positions [since .. trail_length - 1].

   This walks the trail by index ([Store.trail_entry] is O(1) and says so in its own
   comment). It used to call [Store.trail_entries], which materialises the *whole*
   trail as a fresh most-recent-first list and then kept only its first
   [trail_length - since] elements: O(|trail|) allocation on every propagator call in
   the fixpoint loop, to look at the handful of entries that call had just pushed.
   The module header above already claimed "O(new entries) per propagator call"; that
   is now true of the code as well as of the comment. M1-T24.

   The walk runs *downwards*, newest position first, and that is not cosmetic. The
   old code iterated a newest-first list prepending each entry's watchers with
   [List.rev_append], so the returned list came out oldest-entry-first with each
   entry's watcher list reversed, and [propagate] enqueues in exactly that order.
   Counting down from [trail_length - 1] to [since] performs the identical sequence
   of [rev_append]s on the identical entries, so the wake order -- and hence the
   propagation order, the search tree and the emitted proof -- is unchanged, not
   merely equal as a set. An upward walk would reverse it. *)
let watchers_of_new_entries t store ~since =
  let acc = ref [] in
  for i = Store.trail_length store - 1 downto since do
    let e : Store.entry = Store.trail_entry store i in
    match Hashtbl.find_opt t.watchers e.var with
    | None -> ()
    | Some ids -> acc := List.rev_append ids !acc
  done;
  !acc

(* Run every propagator to a joint fixpoint (invariant I-P2): a FIFO queue seeded with
   every instance, so nothing is skipped on the first pass, and thereafter re-fed only
   by the watchers of variables a run actually changed. *)
let propagate (t : t) (store : Store.t) : outcome =
  let n = n_instances t in
  if n = 0 then Fixpoint
  else
    let in_queue = Array.make n false in
    let queue = Queue.create () in
    let enqueue id =
      if (not in_queue.(id)) && id >= 0 && id < n then (
        in_queue.(id) <- true;
        Queue.push id queue)
    in
    Array.iter
      (fun (inst : Propagator.instance) -> enqueue inst.Propagator.id)
      t.instances;
    let conflict = ref None in
    while Option.is_none !conflict && not (Queue.is_empty queue) do
      let id = Queue.pop queue in
      in_queue.(id) <- false;
      let inst = t.instances.(id) in
      let before = Store.trail_length store in
      match inst.Propagator.run store with
      | Propagator.Conflict e -> conflict := Some e
      | Propagator.Fixpoint ->
          let woken = watchers_of_new_entries t store ~since:before in
          List.iter enqueue woken
    done;
    match !conflict with Some e -> Conflict e | None -> Fixpoint
