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
   [since]. [Store.trail_entries] returns the whole trail, most-recent-first; the
   entries pushed since [since] are exactly its first [trail_length store - since]
   elements. *)
let watchers_of_new_entries t store ~since =
  let len = Store.trail_length store in
  let n_new = len - since in
  if n_new <= 0 then []
  else
    let entries = Store.trail_entries store in
    let acc = ref [] in
    List.iteri
      (fun i (e : Store.entry) ->
        if i < n_new then
          match Hashtbl.find_opt t.watchers e.var with
          | None -> ()
          | Some ids -> acc := List.rev_append ids !acc)
      entries;
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
