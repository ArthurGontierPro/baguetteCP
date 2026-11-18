(* Unit tests for M12-parity-T1, the parity SPIKE (lib/core/prop/parity.ml, D-0147).

   The propagator has no proof, so these tests cannot put a proof in front of veripb;
   what stands in for the checker is BRUTE FORCE over every assignment of a small system:

     - every reason clause the propagator builds is IMPLIED by the gathered rows (no
       assignment satisfies the rows and the reason's facts and falsifies the inferred
       literal; for a conflict, none satisfies the rows and the facts);
     - every literal the rows and the current assignment imply is INFERRED (GAC on the
       system, the level the module declares), and a system with no solution under the
       assignment is a conflict.

   Plus the three shapes the brief names (an implied literal three rows deep, a conflict
   only the system sees, the unit-propagation closure missing both), the refusal of a
   proved run, and one end-to-end run of bin/main.exe. Domains are [0, 1] throughout. *)

module Store = Baguette_core.Store
module Domain = Baguette_core.Domain
module Var = Baguette_core.Var
module Parity = Baguette_core.Parity
module Propagator = Baguette_core.Propagator
module Reason = Baguette_core.Reason
module Explanation = Baguette_core.Explanation

let () = Mem_guard.install ()
let failures = ref 0

let check name cond =
  if cond then Printf.printf "ok   %s\n" name
  else (
    Printf.printf "FAIL %s\n" name;
    incr failures)

let bools names =
  Store.create ~names:(Array.of_list names)
    ~domains:(Array.of_list (List.map (fun _ -> Domain.make 0 1) names))

let var = Var.of_int
let placeholder = Reason.because ~concludes:None Reason.none (Explanation.model_row 1)

let decide store i value =
  Store.new_level store;
  ignore
    (if value = 1 then Store.set_lo store (var i) 1 placeholder
     else Store.set_hi store (var i) 0 placeholder)

(* Atom-indexed values of [t] from a store-variable-indexed array. *)
let atom_values (t : Parity.t) (g : int array) =
  Array.map (fun x -> g.(Var.to_int x)) t.Parity.vars

let atom_of (t : Parity.t) i =
  let r = ref (-1) in
  Array.iteri (fun a x -> if Var.to_int x = i then r := a) t.Parity.vars;
  !r

let sorted l = List.sort compare l
let rows_of l = List.map (fun (xs, rhs) -> (List.map var xs, rhs)) l

(* ------------------------------------------------------- the three named shapes *)

(* a+b+c = 0, b+d+e = 0, a+d+f = 0; their sum is c+e+f = 0. With c = 1 and e = 0 every
   row still has two open atoms, so no row is unit, and f = 1 is implied by all three. *)
let test_three_rows_deep () =
  let store = bools [ "a"; "b"; "c"; "d"; "e"; "f" ] in
  let t =
    Parity.make store (rows_of [ ([ 0; 1; 2 ], 0); ([ 1; 3; 4 ], 0); ([ 0; 3; 5 ], 0) ])
  in
  decide store 2 1;
  decide store 4 0;
  let v = Parity.snapshot t store in
  (match Parity.analyse t v with
  | Parity.Implied [ (a, 1, reason) ] ->
      check "three rows deep: f = 1 is the one inference" (a = atom_of t 5);
      check "three rows deep: its reason is {c, e}"
        (sorted reason = sorted [ atom_of t 2; atom_of t 4 ])
  | _ -> check "three rows deep: f = 1 is the one inference" false);
  let up_conflict, vu = Parity.up_closure t v in
  check "three rows deep: unit propagation does not reach f"
    ((not up_conflict) && vu.(atom_of t 5) = -1);
  (match Parity.propagate t store with
  | Propagator.Fixpoint -> ()
  | Propagator.Conflict _ -> check "three rows deep: no conflict" false);
  let d = Store.get store (var 5) in
  check "three rows deep: the store has f = 1" (Domain.lo d = 1 && Domain.hi d = 1)

(* a+b+c = 0 and a+b+d = 0 say c = d. With c = 0 and d = 1 each row has two open atoms
   and is satisfiable on its own; only their sum conflicts. *)
let test_conflict_only_the_system_sees () =
  let store = bools [ "a"; "b"; "c"; "d" ] in
  let t = Parity.make store (rows_of [ ([ 0; 1; 2 ], 0); ([ 0; 1; 3 ], 0) ]) in
  decide store 2 0;
  decide store 3 1;
  let v = Parity.snapshot t store in
  (match Parity.analyse t v with
  | Parity.Conflict_on atoms ->
      check "system conflict: reason {c, d}"
        (sorted atoms = sorted [ atom_of t 2; atom_of t 3 ])
  | Parity.Implied _ -> check "system conflict: reason {c, d}" false);
  let up_conflict, _ = Parity.up_closure t v in
  check "system conflict: unit propagation finds none" (not up_conflict);
  check "system conflict: propagate conflicts"
    (match Parity.propagate t store with
    | Propagator.Conflict _ -> true
    | Propagator.Fixpoint -> false)

(* An odd cycle, a+b = 1, b+c = 1, c+a = 1, sums to 0 = 1 with nothing assigned. *)
let test_root_contradiction () =
  let store = bools [ "a"; "b"; "c" ] in
  let t = Parity.make store (rows_of [ ([ 0; 1 ], 1); ([ 1; 2 ], 1); ([ 2; 0 ], 1) ]) in
  check "odd cycle: inconsistent at the root" t.Parity.inconsistent;
  check "odd cycle: conflict with the empty reason"
    (match Parity.analyse t (Parity.snapshot t store) with
    | Parity.Conflict_on [] -> true
    | _ -> false)

(* ------------------------------------------------------------- the brute force *)

let satisfies rows (g : int array) =
  List.for_all (fun (xs, rhs) -> List.fold_left (fun p x -> p lxor g.(x)) 0 xs = rhs) rows

(* Every total assignment over [n] variables. *)
let all n = List.init (1 lsl n) (fun bits -> Array.init n (fun i -> (bits lsr i) land 1))

let test_brute_force () =
  let rng = Random.State.make [| 2026; 11; 18 |] in
  let trials = 3000 in
  let bad_sound = ref 0 and bad_complete = ref 0 and bad_conflict = ref 0 in
  let inferences = ref 0 and conflicts = ref 0 and beyond = ref 0 in
  for _ = 1 to trials do
    (* Most systems are built consistent, from a hidden solution, so that inferences
       dominate; one in five has random parities, so that root contradictions occur. *)
    let n = 4 + Random.State.int rng 6 in
    let m = 2 + Random.State.int rng (n - 1) in
    let hidden = Array.init n (fun _ -> Random.State.int rng 2) in
    let random_rhs = Random.State.int rng 5 = 0 in
    let rows =
      List.init m (fun _ ->
          let k = 2 + Random.State.int rng 3 in
          let xs = List.init k (fun _ -> Random.State.int rng n) in
          let rhs =
            if random_rhs then Random.State.int rng 2
            else List.fold_left (fun p x -> p lxor hidden.(x)) 0 xs
          in
          (xs, rhs))
    in
    (* the rows the brute force reads: duplicates cancel, as in the propagator *)
    let rows =
      List.map
        (fun (xs, rhs) -> (List.map Var.to_int (Parity.normalise (List.map var xs)), rhs))
        rows
    in
    let store = bools (List.init n (Printf.sprintf "x%d")) in
    let t = Parity.make store (rows_of rows) in
    (* a random partial assignment over all n variables *)
    let g =
      Array.init n (fun i ->
          match Random.State.int rng 10 with
          | 0 | 1 | 2 -> hidden.(i)
          | 3 -> 1 - hidden.(i)
          | _ -> -1)
    in
    let v = atom_values t g in
    let consistent_with fixed (h : int array) =
      List.for_all (fun (i, value) -> h.(i) = value) fixed
    in
    let assigned = List.filter (fun i -> g.(i) >= 0) (List.init n Fun.id) in
    let models =
      List.filter
        (fun h ->
          satisfies rows h && consistent_with (List.map (fun i -> (i, g.(i))) assigned) h)
        (all n)
    in
    let var_of a = Var.to_int t.Parity.vars.(a) in
    match Parity.analyse t v with
    | Parity.Conflict_on atoms ->
        incr conflicts;
        let fixed = List.map (fun a -> (var_of a, v.(a))) atoms in
        if List.exists (fun a -> v.(a) < 0) atoms then incr bad_conflict;
        if List.exists (fun h -> satisfies rows h && consistent_with fixed h) (all n) then
          incr bad_conflict;
        if models <> [] then incr bad_conflict
    | Parity.Implied l ->
        if models = [] then incr bad_complete;
        List.iter
          (fun (a, value, reason) ->
            incr inferences;
            if v.(a) >= 0 || List.exists (fun b -> v.(b) < 0) reason then incr bad_sound;
            let fixed = List.map (fun b -> (var_of b, v.(b))) reason in
            if
              List.exists
                (fun h ->
                  satisfies rows h && consistent_with fixed h && h.(var_of a) <> value)
                (all n)
            then incr bad_sound)
          l;
        (* GAC: every open atom on which all models agree is inferred, with that value *)
        if models <> [] then
          Array.iteri
            (fun a x ->
              let i = Var.to_int x in
              if v.(a) < 0 then
                let vals = List.sort_uniq compare (List.map (fun h -> h.(i)) models) in
                match vals with
                | [ value ] ->
                    if not (List.exists (fun (b, w, _) -> b = a && w = value) l) then
                      incr bad_complete
                | _ -> if List.exists (fun (b, _, _) -> b = a) l then incr bad_complete)
            t.Parity.vars;
        let up_conflict, vu = Parity.up_closure t v in
        if not up_conflict then
          List.iter (fun (a, _, _) -> if vu.(a) < 0 then incr beyond) l
  done;
  Printf.printf
    "     brute force: %d systems, %d inferences (%d beyond unit propagation), %d \
     conflicts\n"
    trials !inferences !beyond !conflicts;
  check "brute force: every reason clause is implied by the rows" (!bad_sound = 0);
  check "brute force: every conflict reason contradicts the rows" (!bad_conflict = 0);
  check "brute force: every implied literal is inferred (GAC)" (!bad_complete = 0);
  check "brute force: the sample exercises both outcomes and the system's own strength"
    (!inferences > 0 && !conflicts > 0 && !beyond > 0)

(* Components: shared variables join, disjoint ones do not, empty rows go. *)
let test_components () =
  let rows = rows_of [ ([ 0; 1 ], 0); ([ 2; 3 ], 1); ([ 1; 4 ], 1); ([ 5; 5 ], 1) ] in
  let comps = Parity.components rows in
  check "components: {0,1,4} and {2,3}, the cancelled row dropped"
    (List.map List.length comps = [ 2; 1 ])

(* ---------------------------------------------------------------- the refusal *)

let test_licence () =
  check "licence: refused for a proved run"
    (match Parity.licence ~no_proof:false with _ -> false | exception Failure _ -> true);
  check "licence: granted for a --no-proof run"
    (match Parity.licence ~no_proof:true with _ -> true | exception Failure _ -> false)

let read_file f =
  let ic = open_in_bin f in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

let contains hay needle =
  let n = String.length needle and h = String.length hay in
  let rec go i = i + n <= h && (String.sub hay i n = needle || go (i + 1)) in
  go 0

let binary () =
  let exe = Filename.concat "bin" "main.exe" in
  let rec up d n =
    if n > 6 then None
    else
      let p = Filename.concat d exe in
      if Sys.file_exists p then Some p
      else up (Filename.concat d Filename.parent_dir_name) (n + 1)
  in
  up (Sys.getcwd ()) 0

(* c = a xor b = d and c <> d: UNSAT, and the XOR rows alone say so at the root. *)
let fzn =
  "var bool: a :: output_var;\n\
   var bool: b :: output_var;\n\
   var bool: c :: output_var;\n\
   var bool: d :: output_var;\n\
   constraint bool_xor(a, b, c);\n\
   constraint bool_xor(a, b, d);\n\
   constraint bool_not(c, d);\n\
   solve satisfy;\n"

let test_cli () =
  match binary () with
  | None -> check "cli: bin/main.exe found above the test's cwd" false
  | Some exe ->
      let dir = Filename.temp_dir "parity" "" in
      let model = Filename.concat dir "xor.fzn" in
      let oc = open_out model in
      output_string oc fzn;
      close_out oc;
      let run args =
        let out = Filename.concat dir "out" and err = Filename.concat dir "err" in
        let rc =
          Sys.command
            (Printf.sprintf "%s %s %s > %s 2> %s" (Filename.quote exe) args
               (Filename.quote model) (Filename.quote out) (Filename.quote err))
        in
        let o = read_file out and e = read_file err in
        (rc, o, e)
      in
      let rc, _, e = run "--parity" in
      check "cli: --parity without --no-proof exits 2" (rc = 2 && contains e "--no-proof");
      let rc, _, _ = run "--parity --proof x" in
      check "cli: --parity with --proof exits 2" (rc = 2);
      let rc, o, e = run "--parity --no-proof --stats" in
      check "cli: --parity --no-proof answers UNSAT"
        (rc = 0 && contains o "=====UNSATISFIABLE=====");
      check "cli: the parity line reports one instance and a conflict"
        (contains e "parity: instances=1 " && contains e " conflicts=1 ");
      let rc, o, _ = run "--no-proof" in
      check "cli: without --parity the same answer"
        (rc = 0 && contains o "=====UNSATISFIABLE=====")

let () =
  test_three_rows_deep ();
  test_conflict_only_the_system_sees ();
  test_root_contradiction ();
  test_brute_force ();
  test_components ();
  test_licence ();
  test_cli ();
  if !failures > 0 then (
    Printf.printf "%d FAIL\n" !failures;
    exit 1)
