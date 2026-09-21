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

(* ------------------------------------------------------------------ *)
(* Domain.affine -- the materialising half of a view (M4-T0).          *)
(*                                                                     *)
(* A view's READ path does not come through here: [View.lo] and        *)
(* friends translate one integer. This is the form that builds the      *)
(* image domain, and the property that makes it usable at all is that   *)
(* the map is a BIJECTION on values, so I-D2 (a bound is never a hole)  *)
(* transports without settling. The reversal of the hole bitset under a *)
(* negated view is the part that can silently be off by one, so it is   *)
(* checked against the value set rather than against the bitset.        *)
(* ------------------------------------------------------------------ *)

let test_affine () =
  let hole d v = changed (Domain.remove d v) in
  (* 0..7 with interior holes at 2 and 5. *)
  let d = hole (hole (Domain.make 0 7) 2) 5 in
  check "affine: the source has the holes the rest of this test assumes"
    (Domain.to_list d = [ 0; 1; 3; 4; 6; 7 ]);

  (* A shift moves every value and nothing else. *)
  let up = Domain.affine d ~negated:false ~offset:3 in
  check "affine: a shift moves the bounds" (Domain.lo up = 3 && Domain.hi up = 10);
  check "affine: a shift moves the holes with them"
    (Domain.to_list up = List.map (fun v -> v + 3) (Domain.to_list d));
  check "affine: a shift of 0 on an unnegated view is the identity"
    (Domain.equal (Domain.affine d ~negated:false ~offset:0) d);

  (* A negation reverses the value set, so the hole bitset is reversed too. This is
     the off-by-one trap: the image of bit [i] is not at index [i]. *)
  let mirror = Domain.affine d ~negated:true ~offset:10 in
  check "affine: a negated view swaps the bounds"
    (Domain.lo mirror = 3 && Domain.hi mirror = 10);
  check "affine: a negated view reverses the value set"
    (Domain.to_list mirror
    = List.sort compare (List.map (fun v -> 10 - v) (Domain.to_list d)));
  check "affine: a negated view's holes are where 10-v says they are"
    (Domain.holes_list mirror = [ 5; 8 ]);

  (* [x |-> -x + k] is an involution, so applying it twice must return the original
     domain EXACTLY -- holes, bounds and all. A reversal that is off by one in the
     bitset survives a bounds check and dies here. *)
  check "affine: -(-x+k)+k is the identity, holes included"
    (Domain.equal (Domain.affine mirror ~negated:true ~offset:10) d);

  (* I-D2 transports: a bound of the image is never a hole of the image. Swept over
     every subset of a six-value universe, both signs, a few offsets. Small on
     purpose -- the suite shares a 15 GB machine. *)
  let bad = ref None in
  let rec subsets = function
    | [] -> [ [] ]
    | v :: rest ->
        let r = subsets rest in
        List.map (fun s -> v :: s) r @ r
  in
  let universe = [ 0; 1; 2; 3; 4; 5 ] in
  let n_checked = ref 0 in
  List.iter
    (fun keep ->
      match keep with
      | [] | [ _ ] -> ()
      | _ ->
          let d0 =
            List.fold_left
              (fun acc v ->
                if List.mem v keep then acc
                else
                  match Domain.remove acc v with
                  | Domain.Changed d -> d
                  | Domain.Unchanged -> acc
                  | Domain.Failed -> acc)
              (Domain.make (List.hd keep) (List.nth keep (List.length keep - 1)))
              universe
          in
          List.iter
            (fun (negated, offset) ->
              let img = Domain.affine d0 ~negated ~offset in
              incr n_checked;
              let expect =
                List.sort compare
                  (List.map
                     (fun v -> (if negated then -v else v) + offset)
                     (Domain.to_list d0))
              in
              if Domain.to_list img <> expect then
                if !bad = None then
                  bad :=
                    Some
                      (Printf.sprintf
                         "%s under (negated=%b, offset=%d) -> %s, wanted [%s]"
                         (Domain.to_string d0) negated offset (Domain.to_string img)
                         (String.concat ";" (List.map string_of_int expect)));
              if Domain.is_hole img (Domain.lo img) || Domain.is_hole img (Domain.hi img)
              then
                if !bad = None then
                  bad :=
                    Some
                      (Printf.sprintf "I-D2 broken on the image of %s"
                         (Domain.to_string d0)))
            [ (false, 0); (false, 4); (false, -3); (true, 0); (true, 7); (true, -2) ])
    (subsets universe);
  check "affine: the image is exactly the image of the value set, and keeps I-D2"
    (match !bad with
    | None -> true
    | Some w ->
        Printf.printf "     first offender: %s\n" w;
        false);
  check "affine: the sweep actually ran" (!n_checked > 100);
  Printf.printf "     (swept %d affine images)\n" !n_checked

let () =
  test_bound_moves ();
  test_interior_hole ();
  test_removal_at_a_bound_is_a_bound_change ();
  test_no_change_and_change_of ();
  test_exhaustive ();
  test_affine ();
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "\ndomain change-granularity tests passed"
