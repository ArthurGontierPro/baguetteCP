(* restart.ml: WHEN the search restarts -- the restart policies, as data and a small state
   machine (M10-search-strategy-T2, docs/DECISIONS.md D-0137 sections 1 and 2).

   Consistency level: none -- this is not a propagator. Governing records: D-0137 (the
   policies, their parameters, the termination argument), D-0045 (the question it answers
   for the flags), docs/SPEC.md 3.4 (restarts are opt-in, the default is [No_restarts]).

   ---------------------------------------------------------------------------
   What this module decides, and what it does not
   ---------------------------------------------------------------------------

   It decides one bit per conflict: is a restart due now? It is told about each conflict
   ([on_conflict], with the learned clause's LBD when there is one), asked [due], and told
   when the search has restarted ([on_restart]). That is all. HOW a restart is performed --
   the frames unwound, the levels closed, the node re-entered -- is lib/core/search.ml's
   [NRestart], and D-0137 section 1 is the argument that it writes no new kind of proof
   line. Nothing here touches a store, a writer or a trail, so every policy is a pure
   function of the sequence of conflicts it was shown, and two runs of one binary restart
   at the same conflicts (scripts/check_determinism.sh).

   ---------------------------------------------------------------------------
   The policies
   ---------------------------------------------------------------------------

   Run [k] (0-based: the search before the first restart is run 0) may take a number of
   conflicts before a restart is due:

     - [Luby u]       u * luby(k+1)          Luby, Sinclair, Zuckerman, IPL 1993
     - [Geom (u, f)]  u * f^k, rounded up    Walsh, IJCAI 1999
     - [Lbd]          dynamic: the average LBD of the last [window] learned clauses times
                      [k] exceeds the run-wide average (Audemard and Simon, CP 2012), and
                      the run has taken at least max(window, luby(k+1)) conflicts
     - [Stable u]     alternate an [Lbd] phase ("focused") and a [Luby u] phase
                      ("stable"), each [phase_len] conflicts long, [phase_len] doubling at
                      every switch from [stable_first_phase] -- the alternation of Oh (SAT
                      2015) that CaDiCaL and Kissat run
     - [No_restarts]  never: SPEC 3.4's default

   ---------------------------------------------------------------------------
   Termination: every cutoff is UNBOUNDED over the run index
   ---------------------------------------------------------------------------

   D-0137 section 1 has the argument in full. A tree searched from the root has fewer than
   B conflicts, B depending only on the declared domains; a run whose cutoff exceeds B
   cannot be restarted and completes. So a policy terminates if, for every bound, some run
   has a cutoff above it. Luby and geometric do by construction. [Lbd] alone does not --
   its restarts are triggered by the LBD signal, not by a count -- which is why it carries
   the Luby FLOOR: run [k] may not restart before luby(k+1) conflicts, and luby is
   unbounded. [Stable] switches mode only AT a restart, never by cutting a run, so each of
   its runs is a run of one of the two policies above, with that policy's own index. The
   floor is not Glucose's, and it is the only respect in which [Lbd] departs from it;
   luby(k+1) <= k+1, so in practice it binds only after hundreds of restarts.

   The alternative termination argument -- every learned clause is new, so the database
   cannot stop growing -- is NOT relied on: it holds only while retention keeps everything
   and every learned clause has an instance, and M10-search-strategy-T4 (D-0139) may change
   the first. *)

type policy =
  | No_restarts
  | Luby of int (* the unit, in conflicts *)
  | Geom of int * float (* the first cutoff and the factor *)
  | Lbd of { window : int; k : float }
  | Stable of int (* the stable phase's Luby unit *)

(* D-0137 section 2's defaults. *)
let default_unit = 100
let default_factor = 1.5
let default_window = 50
let default_k = 0.8
let stable_first_phase = 1000

(* luby(i) for i >= 1: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8 ...

   If i = 2^m - 1 the value is 2^(m-1); otherwise it is luby(i - 2^(m-1) + 1) for the
   smallest m with i < 2^m - 1, i.e. the sequence repeats its own prefix. Iterative, and
   total on i >= 1. *)
let luby i =
  if i < 1 then invalid_arg "Restart.luby: the index is 1-based";
  let rec go i =
    (* the smallest m with 2^m - 1 >= i *)
    let m = ref 1 in
    while (1 lsl !m) - 1 < i do
      incr m
    done;
    if (1 lsl !m) - 1 = i then 1 lsl (!m - 1) else go (i - (1 lsl (!m - 1)) + 1)
  in
  go i

type t = {
  policy : policy;
  mutable runs : int; (* restarts so far = the index of the current run *)
  mutable in_run : int; (* conflicts in the current run *)
  mutable conflicts : int; (* conflicts in total *)
  (* [Lbd]: the last [window] learned LBDs, a ring, and the run-wide sum. *)
  ring : int array;
  mutable ring_len : int;
  mutable ring_pos : int;
  mutable ring_sum : int;
  mutable lbd_sum : int;
  mutable lbd_n : int;
  (* [Stable]: which mode the current run is in, the conflicts left in this phase, the
     phase's length, and each mode's own run index (the Luby floor and the stable
     schedule each count their own runs, which is what keeps both unbounded). *)
  mutable stable_mode : bool;
  mutable phase_left : int;
  mutable phase_len : int;
  mutable focused_runs : int;
  mutable stable_runs : int;
  mutable n_switches : int;
}

let create policy =
  let window =
    match policy with Lbd { window; _ } -> window | Stable _ -> default_window | _ -> 1
  in
  if window < 1 then invalid_arg "Restart.create: the LBD window must be >= 1";
  (match policy with
  | (Luby u | Stable u) when u < 1 -> invalid_arg "Restart.create: the unit must be >= 1"
  | Geom (u, f) when u < 1 || f < 1.0 ->
      invalid_arg
        "Restart.create: a geometric schedule needs a unit >= 1 and a factor >= 1"
  | Lbd { k; _ } when k <= 0.0 -> invalid_arg "Restart.create: K must be > 0"
  | _ -> ());
  {
    policy;
    runs = 0;
    in_run = 0;
    conflicts = 0;
    ring = Array.make window 0;
    ring_len = 0;
    ring_pos = 0;
    ring_sum = 0;
    lbd_sum = 0;
    lbd_n = 0;
    stable_mode = false;
    phase_left = stable_first_phase;
    phase_len = stable_first_phase;
    focused_runs = 0;
    stable_runs = 0;
    n_switches = 0;
  }

let enabled t = match t.policy with No_restarts -> false | _ -> true
let restarts t = t.runs
let run t = t.runs
let switches t = t.n_switches

(* One conflict. [lbd] is the learned clause's LBD ([Learn.lbd]), [None] when the
   conflict learned nothing -- it then counts toward the cutoffs but gives the LBD
   averages no sample. *)
let on_conflict t ~lbd =
  t.in_run <- t.in_run + 1;
  t.conflicts <- t.conflicts + 1;
  (match t.policy with Stable _ -> t.phase_left <- t.phase_left - 1 | _ -> ());
  match lbd with
  | None -> ()
  | Some b -> (
      match t.policy with
      | Lbd _ | Stable _ ->
          let w = Array.length t.ring in
          if t.ring_len = w then t.ring_sum <- t.ring_sum - t.ring.(t.ring_pos)
          else t.ring_len <- t.ring_len + 1;
          t.ring.(t.ring_pos) <- b;
          t.ring_sum <- t.ring_sum + b;
          t.ring_pos <- (t.ring_pos + 1) mod w;
          t.lbd_sum <- t.lbd_sum + b;
          t.lbd_n <- t.lbd_n + 1
      | No_restarts | Luby _ | Geom _ -> ())

(* Glucose's test, with D-0137's floor. [run_index] is the focused-mode run index, which
   is [t.runs] under [Lbd] and [t.focused_runs] under [Stable]. *)
let lbd_due t ~window ~k ~run_index =
  t.ring_len = window
  && t.in_run >= Stdlib.max window (luby (run_index + 1))
  && t.lbd_n > 0
  &&
  let recent = float_of_int t.ring_sum /. float_of_int window in
  let global = float_of_int t.lbd_sum /. float_of_int t.lbd_n in
  recent *. k > global

(* The cutoff of run [k] under [Geom (u, f)]: [u * f^k] rounded up, saturated so that a
   long run cannot overflow it into a negative number (which would restart at once). *)
let geom_cutoff u f k =
  let c = float_of_int u *. (f ** float_of_int k) in
  if c >= 1e15 then max_int else int_of_float (Float.ceil c)

let due t =
  match t.policy with
  | No_restarts -> false
  | Luby u -> t.in_run >= u * luby (t.runs + 1)
  | Geom (u, f) -> t.in_run >= geom_cutoff u f t.runs
  | Lbd { window; k } -> lbd_due t ~window ~k ~run_index:t.runs
  | Stable u ->
      if t.stable_mode then t.in_run >= u * luby (t.stable_runs + 1)
      else lbd_due t ~window:default_window ~k:default_k ~run_index:t.focused_runs

(* The search has restarted. The LBD ring is cleared (Glucose clears its queue at a
   restart, so the next decision compares the NEW run's clauses with the global average),
   and under [Stable] the mode switches here -- and only here -- once the phase's conflict
   budget is spent. *)
let on_restart t =
  t.runs <- t.runs + 1;
  t.in_run <- 0;
  t.ring_len <- 0;
  t.ring_pos <- 0;
  t.ring_sum <- 0;
  match t.policy with
  | Stable _ ->
      if t.stable_mode then t.stable_runs <- t.stable_runs + 1
      else t.focused_runs <- t.focused_runs + 1;
      if t.phase_left <= 0 then (
        t.stable_mode <- not t.stable_mode;
        t.n_switches <- t.n_switches + 1;
        t.phase_len <- 2 * t.phase_len;
        t.phase_left <- t.phase_len)
  | _ -> ()

(* --------------------------------------------------------------- the CLI's spelling *)

let to_string = function
  | No_restarts -> "none"
  | Luby u -> Printf.sprintf "luby:%d" u
  | Geom (u, f) -> Printf.sprintf "geom:%d:%g" u f
  | Lbd { window; k } -> Printf.sprintf "lbd:%d:%g" window k
  | Stable u -> Printf.sprintf "stable:%d" u

(* `none | luby[:U] | geom[:U[:F]] | lbd[:W[:K]] | stable[:U]`. A malformed spelling is an
   [Error] naming what was wrong rather than a silent default -- a mistyped policy that
   quietly meant "no restarts" would be the measurement whose flag was never in force. *)
let of_string s =
  let int_ what v =
    match int_of_string_opt v with
    | Some n when n >= 1 -> Ok n
    | _ -> Error (Printf.sprintf "%s %S is not an integer >= 1" what v)
  in
  let float_ what ~min v =
    match float_of_string_opt v with
    | Some f when Float.is_finite f && f >= min -> Ok f
    | _ -> Error (Printf.sprintf "%s %S is not a number >= %g" what v min)
  in
  let ( let* ) = Result.bind in
  match String.split_on_char ':' s with
  | [ "none" ] -> Ok No_restarts
  | [ "luby" ] -> Ok (Luby default_unit)
  | [ "luby"; u ] ->
      let* u = int_ "the Luby unit" u in
      Ok (Luby u)
  | [ "geom" ] -> Ok (Geom (default_unit, default_factor))
  | [ "geom"; u ] ->
      let* u = int_ "the first cutoff" u in
      Ok (Geom (u, default_factor))
  | [ "geom"; u; f ] ->
      let* u = int_ "the first cutoff" u in
      let* f = float_ "the factor" ~min:1.0 f in
      Ok (Geom (u, f))
  | [ "lbd" ] -> Ok (Lbd { window = default_window; k = default_k })
  | [ "lbd"; w ] ->
      let* w = int_ "the LBD window" w in
      Ok (Lbd { window = w; k = default_k })
  | [ "lbd"; w; k ] ->
      let* w = int_ "the LBD window" w in
      let* k = float_ "K" ~min:1e-9 k in
      Ok (Lbd { window = w; k })
  | [ "stable" ] -> Ok (Stable default_unit)
  | [ "stable"; u ] ->
      let* u = int_ "the stable unit" u in
      Ok (Stable u)
  | _ ->
      Error
        (Printf.sprintf
           "%S is not a restart policy: none | luby[:U] | geom[:U[:F]] | lbd[:W[:K]] | \
            stable[:U]"
           s)
