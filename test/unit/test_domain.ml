(* Unit tests for [Domain.change] and [Domain.classify] -- M2-T5.

   test_core.ml already covers the narrowing operations themselves (I-D1 to I-D3). What
   is new here is the *change vocabulary* docs/ARCHITECTURE.md section 2 promised and the
   code did not have: what an operation reports having moved.

   This file exists because lib/core/engine.ml's wake mask rests on one property of
   [classify] and would be silently unsound without it:

     a change is a [Bound] or a [Holes], NEVER both, and a [Holes] change leaves [lo]
     and [hi] exactly where they were.

   If that ever stopped holding -- if some operation could punch an interior hole *and*
   move a bound in one trail entry, reported as [Holes] -- then a bounds-only propagator
   would be denied a bound move it needed, and the only symptom would be a solver that
   prunes less. Nothing would crash and the proof would still verify. So the property is
   brute-forced over every domain on a small universe rather than sampled: [exhaustive]
   below is the test that matters, and the hand-written cases above it are there to keep
   the failure readable when it goes red. Domains are kept to a six-value universe on
   purpose (the suite shares a 15 GB machine with other sessions). *)

module Domain = Baguette_core.Domain

(* M1-T53: the inner heap guard. test_prop.exe is the binary that reached 14.9 GB RSS on
   2026-09-16 and had to be killed by hand, so a guard that covered only test_output and
   test_compile would have missed the one incident it exists to prevent. `ulimit -v` stays
   the outer backstop -- see mem_guard.ml's header for what this cannot see. *)
let () = Mem_guard.install ()
let failures = ref 0

let check name cond =
  if cond then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s\n" name)

let changed = function
  | Domain.Changed d -> d
  | Domain.Unchanged -> failwith "expected Changed, got Unchanged"
  | Domain.Failed -> failwith "expected Changed, got Failed"

let classify_op d r = Domain.classify ~old:d ~now:(changed r)

(* ------------------------------------------------------------ hand-written *)

let test_bound_moves () =
  let d = Domain.make 0 9 in
  check "classify: set_lo reports the lower bound it established"
    (classify_op d (Domain.set_lo d 3) = Domain.Bound { lo = Some 3; hi = None });
  check "classify: set_hi reports the upper bound it established"
    (classify_op d (Domain.set_hi d 6) = Domain.Bound { lo = None; hi = Some 6 });
  check "classify: fix reports both bounds, because fix moves both"
    (classify_op d (Domain.fix d 4) = Domain.Bound { lo = Some 4; hi = Some 4 });
  (* [fix] onto a value that is already one of the bounds moves only the other one. *)
  check "classify: fixing to lo moves only hi"
    (classify_op d (Domain.fix d 0) = Domain.Bound { lo = None; hi = Some 0 })

let test_interior_hole () =
  let d = Domain.make 0 9 in
  check "classify: an interior removal is Holes, with the value that went"
    (classify_op d (Domain.remove d 4) = Domain.Holes [ 4 ]);
  let d4 = changed (Domain.remove d 4) in
  check "classify: a second interior removal names only the NEW hole"
    (classify_op d4 (Domain.remove d4 7) = Domain.Holes [ 7 ]);
  check "classify: an interior removal leaves the bounds alone"
    (Domain.lo d4 = 0 && Domain.hi d4 = 9)

(* The case the engine's mask depends on, and the one that would be easy to get wrong:
   removing the value sitting AT a bound is not a hole, it is a bound move, because
   [settle] restores I-D2. A bounds-only propagator must still be woken by it. *)
let test_removal_at_a_bound_is_a_bound_change () =
  let d = Domain.make 0 9 in
  check "classify: removing lo is a Bound change, not a Holes change"
    (classify_op d (Domain.remove d 0) = Domain.Bound { lo = Some 1; hi = None });
  check "classify: removing hi is a Bound change, not a Holes change"
    (classify_op d (Domain.remove d 9) = Domain.Bound { lo = None; hi = Some 8 });
  (* And when the bound has to walk over a run of holes already punched inside, the
     reported bound is where it ended up, not where the removal started. *)
  let holed = List.fold_left (fun acc v -> changed (Domain.remove acc v)) d [ 1; 2; 3 ] in
  check "classify: a bound walking over a run of holes reports where it landed"
    (classify_op holed (Domain.remove holed 0) = Domain.Bound { lo = Some 4; hi = None })

let test_no_change_and_change_of () =
  let d = Domain.make 0 9 in
  check "classify: identical domains are NoChange"
    (Domain.classify ~old:d ~now:d = Domain.NoChange);
  check "change_of: Unchanged is NoChange"
    (Domain.change_of d (Domain.set_lo d 0) = Domain.NoChange);
  check "change_of: Failed is NoChange -- an empty domain is never stored (I-D1)"
    (Domain.change_of d (Domain.set_lo d 20) = Domain.NoChange);
  check "change_of: Changed agrees with classify"
    (Domain.change_of d (Domain.set_lo d 5) = Domain.Bound { lo = Some 5; hi = None })

(* ---------------------------------------------------------------- exhaustive *)

(* Every non-empty subset of 0..5 as a domain, every operation, every argument in a
   window either side of it: 63 domains x 4 operations x 14 arguments. Small on purpose;
   the point is total coverage of a tiny universe, not a big random sample. *)
let universe_hi = 5
let args = List.init 14 (fun i -> i - 4)

let all_domains () =
  let acc = ref [] in
  for mask = 1 to (1 lsl (universe_hi + 1)) - 1 do
    let vs =
      List.filter (fun v -> mask land (1 lsl v) <> 0) (List.init (universe_hi + 1) Fun.id)
    in
    acc := Domain.of_list vs :: !acc
  done;
  !acc

let ops d =
  List.concat_map
    (fun v ->
      [
        (Printf.sprintf "set_lo %d" v, Domain.set_lo d v);
        (Printf.sprintf "set_hi %d" v, Domain.set_hi d v);
        (Printf.sprintf "remove %d" v, Domain.remove d v);
        (Printf.sprintf "fix %d" v, Domain.fix d v);
      ])
    args

let test_exhaustive () =
  let bad_shape = ref None in
  let bad_values = ref None in
  let saw_bound = ref 0 and saw_holes = ref 0 in
  let note r what = if Option.is_none !r then r := Some what in
  List.iter
    (fun d ->
      List.iter
        (fun (label, r) ->
          match r with
          | Domain.Unchanged | Domain.Failed -> ()
          | Domain.Changed now -> (
              let where = Printf.sprintf "%s on %s" label (Domain.to_string d) in
              let removed =
                List.filter (fun v -> not (Domain.mem now v)) (Domain.to_list d)
              in
              match Domain.classify ~old:d ~now with
              | Domain.NoChange ->
                  (* A stored change is a real change: [Store.apply] asserts the size
                     strictly drops, so [NoChange] here would be a classification bug. *)
                  note bad_shape (where ^ ": classified NoChange but the set changed")
              | Domain.Bound { lo; hi } ->
                  incr saw_bound;
                  (* The bound reported is the bound that moved, and it is the new one. *)
                  let lo_ok =
                    match lo with
                    | None -> Domain.lo now = Domain.lo d
                    | Some v -> v = Domain.lo now && v > Domain.lo d
                  in
                  let hi_ok =
                    match hi with
                    | None -> Domain.hi now = Domain.hi d
                    | Some v -> v = Domain.hi now && v < Domain.hi d
                  in
                  if not (lo_ok && hi_ok) then
                    note bad_values (where ^ ": Bound payload does not match the bounds");
                  if lo = None && hi = None then
                    note bad_shape (where ^ ": Bound but neither bound moved")
              | Domain.Holes vs ->
                  incr saw_holes;
                  (* THE property the engine's mask rests on. *)
                  if Domain.lo now <> Domain.lo d || Domain.hi now <> Domain.hi d then
                    note bad_shape (where ^ ": Holes but a bound moved");
                  if vs <> removed then
                    note bad_values (where ^ ": Holes payload is not the removed set")))
        (ops d))
    (all_domains ());
  check "exhaustive: every change is shaped as Bound-xor-Holes, bounds untouched by Holes"
    (match !bad_shape with
    | None -> true
    | Some w ->
        Printf.printf "     first offender: %s\n" w;
        false);
  check "exhaustive: every payload matches the values that actually moved"
    (match !bad_values with
    | None -> true
    | Some w ->
        Printf.printf "     first offender: %s\n" w;
        false);
  (* Guard against the two checks above passing because nothing was classified. This
     project's recurring failure is a test that cannot see the thing it checks. *)
  check "exhaustive: the sweep actually produced Bound changes" (!saw_bound > 0);
  check "exhaustive: the sweep actually produced Holes changes" (!saw_holes > 0);
  Printf.printf "     (classified %d Bound and %d Holes changes)\n" !saw_bound !saw_holes

let () =
  test_bound_moves ();
  test_interior_hole ();
  test_removal_at_a_bound_is_a_bound_change ();
  test_no_change_and_change_of ();
  test_exhaustive ();
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "\ndomain change-granularity tests passed"
