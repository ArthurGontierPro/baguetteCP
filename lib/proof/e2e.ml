(* The end-to-end prefix, written by the solver (M14-e2e-verification-T3, D-0187).

   Under `--e2e`, the proof baguette writes is checked against the .opb that CakeML's
   VERIFIED encoder `cake_pb_cp` wrote for the model's `.scp` (D-0174), not against
   baguette's own .opb. Baguette never reads that file. It knows what the file holds from
   a CONTRACT (docs/PROOF-FORMAT.md section 3b), and it knows where each of its own rows
   comes from because lib/flatzinc/compile.ml says which FlatZinc constraint it is posting
   ([begin_con]). From the two it writes, at the head of its proof, the derivation of each
   of its .opb rows under the row's own label `@cN`. The proof after the prefix is
   baguette's own, byte for byte, but for the `f` line (omitted: veripb 3.0.2 accepts a
   proof with none and elaborates it with the right count, D-0187 section 1) and the
   `soli` lines (renamed, see [soli_tail]).

   This replaces the external bridge (tools/e2e/bridge.py), which recovered each row's
   origin by matching two files and took up to 2 408 s on the Challenge (D-0182).

   ---------------------------------------------------------------------------
   Why a wrong line here cannot make a wrong answer verify
   ---------------------------------------------------------------------------

   Every line written here is CHECKED, against a file this module never sees. If the
   contract is stale (cake's encoder renamed a label, changed a big-M), or if a derivation
   below is wrong, the checker refuses the line, and the chain says FAIL. Nothing here is
   trusted. The cost of a stale contract is availability, never soundness.

   ---------------------------------------------------------------------------
   The prefix (D-0174 section 4), per integer x over [l, u]
   ---------------------------------------------------------------------------

   B is cake's two's-complement bit sum of x ([bit_width] below, cake's own rule), and
   S = sum_{l < v <= u} x_ge_v baguette's ladder:

     @A1[x_ge_v]  red  B + M ~x_ge_v >= v      : x_ge_v -> 0      (x_ge_v -> B >= v)
     @A2[x_ge_v]  red -B + K x_ge_v  >= 1 - v  : x_ge_v -> 1      (B >= v -> x_ge_v)
     @E1  B - S >= l, upwards from @i[X][lb], one pol per value (running row @T1, deleted)
     @E2  S - B >= -l, downwards from @i[X][ub], idem (@T2)
     @L[x_ge_(v+1)]  the ladder rung, A1(v+1) + A2(v), saturated, divided

   Then, per FlatZinc constraint, every row cake writes for it ([cake_rows]) is
   SUBSTITUTED, B -> l + S: k * @E2 added for a coefficient k > 0 on B, |k| * @E1 for
   k < 0 (@S[...]; written when a pin first cites it, or before a `rup` pin of the same
   constraint, D-0188 section 3.2). And each of baguette's rows posted for that constraint is pinned:

     - `ia` against the substituted row of its OWN constraint that implies it
       syntactically (the coefficient each literal loses, summed, at most the slack), after
       the flag swap and saturation below, through a `pol` line @W when either is needed;
     - a disequality selector `_neN` (int_ne, int_lin_ne, and the constant pairs of
       all_different) is DEFINED as cake's flag for the same two halves (`b[c][ne]`,
       `x[c][i_j]`) by a red pair, `~s + F >= 1` and `s + ~F >= 1` with witness `s -> F`
       (or the same with ~F), s being fresh. A candidate's c * F is then c * s, by adding
       c times the clause of the pair that has s positive or negative as needed;
     - cake's ATOMS (T4): a reify tuple `(b = 1)` is cake's `i[b][eq1]`, defined over
       `i[b][ge1]` and `i[b][ge2]`, themselves defined over b's bits (cp_to_ilpScript.sml,
       cencode_full_eq); a constant tuple is `n[K][eq<v>]`. An atom that equals ONE
       baguette literal or a constant is replaced by it in a candidate, through a clause:
       a ge atom's by one `pol` of its own definition row and the atom @A1/@A2 of the same
       value (`[r] + A2`, saturated, gives ~g + x_ge_v; `[f] + A1` gives g + ~x_ge_v; a
       ge atom outside [l, u] is a unit from its row and the bound row), an eq atom's by
       `rup` once its two ge atoms have their clauses (@Q[...]);
     - cake's FLAG CLAUSE `lt + gt + eq >= 1` (equals_iff, not_equals_iff) is resolved
       once against a candidate that has one of its flags, and the resolvent is a
       candidate too: that is where baguette's `_neN` of int_eq_reif/int_ne_reif stands;
     - `rup` otherwise (all_different's per-value clauses close by unit propagation over the
       substituted pair rows, as the bridge measured, D-0176; array_bool_or/and's binary
       clauses over cake's `or`/`and` rows and the atom clauses, D-0178).

   A ladder rung is `ia` against its @L.

   ---------------------------------------------------------------------------
   T5's globals (T3b, D-0188)
   ---------------------------------------------------------------------------

   element, global_cardinality, array_int_maximum/minimum (and int_max/min, cake's binary
   `max`/`min`), inverse and member, their cake rows transcribed in [cake_rows]. Three
   derivations, all `pol`:

     - an INTERIOR eq atom [x = v] is the order indicator x_ge_v - x_ge_(v+1), exactly,
       through @Ep/@Em ([indicator]); gcc's counting rows and inverse's channel rows are
       then `ia` against cake's;
     - a cake row LINEARISED at a clause ([linearise]): each B_z cancelled by @A1/@A2 at
       the clause's threshold, or by z's bound row, saturated, its atoms replaced. That is
       element's `[i = p] -> z >= w` (the bridge's 93 043 `rup` on black-hole_17, D-0182),
       written as ONE `pol` under the row's own label when it is the row exactly;
     - maxmin's `m >= v -> OR x_i >= v`: the operands' choice rows so linearised, summed
       with the at-least-one over the flags ([special]).

   A candidate that implies a row only after WEAKENING (and saturation), or after resolving
   a literal against one of member's or inverse's own binary clauses ([resolve]), is tried
   after every strict candidate failed. A gcc copy (D-0146) is defined as its original by
   red pairs ([declare_copy], [split_copies]).

   ---------------------------------------------------------------------------
   What is covered
   ---------------------------------------------------------------------------

   The families of T2 (D-0176): int_lin_le, int_lin_eq, int_lin_ne, int_le, int_lt,
   int_eq, int_ne, all_different_int; of T4 (D-0178): bool_clause, array_bool_or,
   array_bool_and, bool_eq, bool_not, bool2int, int_le_reif, int_eq_reif, int_ne_reif,
   int_lin_le_reif; and of T5 above; over `var lo..hi` (a set domain with holes is cake's
   `in` over interior eq atoms, D-0187) and `var bool`, with or without an objective.
   Everything else raises [Not_covered] with the construct's name, before the search: the
   caller refuses `--e2e` and says why. In particular int_times and int_div (T6 left them
   outside, D-0195 section 2.4), and any row baguette commits outside a covered constraint.
   A variable on the bits arm (`--bits-above`) is covered since T7 (D-0196, [declare_bits]):
   its bits are defined from cake's, a guarded row whose big-M is baguette's is derived by
   contradiction against the bits' ub rows ([tight]), a choice selector over bits is defined
   as its flag AND no earlier one ([conj_of]), an int_abs guard over bits as cake's atom.

   ---------------------------------------------------------------------------
   T6's families (D-0195)
   ---------------------------------------------------------------------------

   - regular: mznlib's state flags have no .scp counterpart. Each is DEFINED as cake's flag
     of the same position and (renumbered, [regular_state]) state by a red pair, and swapped
     in as a selector ([flag], [declare]); a forward clause over a symbol run that no
     candidate implies closes by `rup` once its letter's eq atoms have their clauses.
   - cumulative: one candidate per time point, ONE pol of cake's capacity row, contribution
     rows, activity clauses and flag clauses ([begin_con]).
   - int_abs: the sign guard is DEFINED as x_ge_0 ([guard]); a row true in both signs is
     derived by contradiction, `pbc` with the negation plus each candidate ([pin]). *)

exception Not_covered of string

let refuse fmt = Printf.ksprintf (fun s -> raise (Not_covered s)) fmt

(* ---------------------------------------------------------------------------
   The contract (docs/PROOF-FORMAT.md section 3b). cake_pb_cp sha256 ca92491e, CakePB
   438b8f83, built from CakeML 14856fcf; every rule below is that commit's HOL4 source,
   named where it is transcribed.
   --------------------------------------------------------------------------- *)

let cake_pb_cp_sha256 = "ca92491e"

(* tools/e2e/fzn2scp.py's [sanitise]: the .scp name of a FlatZinc variable. *)
let scp_name x =
  String.map
    (fun c -> match c with 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> c | _ -> '_')
    x

(* HOL4's LENGTH (bits_of_num n) and LENGTH (FST (bits_of_int i)). *)
let rec num_bits n = if n <= 0 then 0 else 1 + num_bits (n lsr 1)
let int_bits i = if i < 0 then num_bits (-i - 1) else num_bits i

(* int_bitwiseExtraScript.sml, bit_width: (signed?, h). *)
let bit_width ~lo ~hi =
  if lo < 0 then (true, max (int_bits lo) (int_bits hi)) else (false, int_bits hi)

(* Checked arithmetic: a contract value that does not fit is refused, not wrapped. *)
let cap = max_int / 4

let ck v =
  if v > cap || v < -cap then refuse "a coefficient of cake's encoding beyond 2^60";
  v

let mul a b =
  if a <> 0 && abs b > cap / abs a then
    refuse "a coefficient of cake's encoding beyond 2^60";
  a * b

let pow2 h = if h >= 60 then refuse "a variable of %d bits" h else 1 lsl h

(* ilpScript.sml, min_iterm: the least value of c * X over X's bit range. *)
let min_iterm ~comp ~h c =
  if c < 0 then mul c (pow2 h - 1) else if comp then mul c (-pow2 h) else 0

(* ilpScript.sml, max_iterm: the greatest value of c * X over X's bit range. *)
let max_iterm ~comp ~h c =
  if c < 0 then if comp then mul c (-pow2 h) else 0 else mul c (pow2 h - 1)

(* ---------------------------------------------------------------------------
   Rows as data: a map from a variable name to its coefficient (variable form), or from
   a literal ("x" or "~x") to its positive coefficient (literal form), and a degree.
   --------------------------------------------------------------------------- *)

module SM = Map.Make (String)

let neg_lit l =
  if String.length l > 0 && l.[0] = '~' then String.sub l 1 (String.length l - 1)
  else "~" ^ l

let var_of l =
  if String.length l > 0 && l.[0] = '~' then String.sub l 1 (String.length l - 1) else l

(* sum c * lit >= d -> variable form *)
let var_form terms d =
  List.fold_left
    (fun (m, d) (c, l) ->
      if l.[0] = '~' then
        let v = var_of l in
        (SM.update v (fun o -> Some (Option.value o ~default:0 - c)) m, d - c)
      else (SM.update l (fun o -> Some (Option.value o ~default:0 + c)) m, d))
    (SM.empty, d) terms
  |> fun (m, d) -> (SM.filter (fun _ c -> c <> 0) m, d)

let lit_form (m, d) =
  SM.fold
    (fun v c (acc, d) ->
      if c > 0 then (SM.add v c acc, d) else (SM.add ("~" ^ v) (-c) acc, d - c))
    m (SM.empty, d)

let vadd (m1, d1) k (m2, d2) =
  let m =
    SM.union (fun _ a b -> Some (a + b)) m1 (SM.map (fun c -> mul k c) m2)
    |> SM.filter (fun _ c -> c <> 0)
  in
  (m, d1 + mul k d2)

(* The candidate implies the target by weakening: what each literal loses, summed, is at
   most the candidate's slack over the target's degree. Both in literal form. *)
let implies (cl, cd) (bl, bd) =
  let loss =
    SM.fold
      (fun l a acc -> acc + max 0 (a - Option.value (SM.find_opt l bl) ~default:0))
      cl 0
  in
  cd - loss >= bd

(* T3b: [implies], or, failing it, after WEAKENING away every literal the target lacks and
   saturating again (member's big-M row over the two hulls' overlap, where the loss of the
   guard's big-M coefficient alone exceeds the slack; D-0180's bridge did the same). The
   rpn suffix of the weakening, "" when none is needed. *)
let rec implied_or_weakened (cl, cd) (bl, bd) =
  if implies (cl, cd) (bl, bd) then Some ""
  else if cd < 1 then None
  else
    let removed = SM.filter (fun l _ -> not (SM.mem l bl)) cl in
    if SM.is_empty removed then None
    else
      let d = cd - SM.fold (fun _ a acc -> acc + a) removed 0 in
      let _, w = saturate (SM.filter (fun l _ -> SM.mem l bl) cl, d) in
      if snd w >= 1 && implies w (bl, bd) then
        Some
          (String.concat ""
             (List.map (fun (l, _) -> " " ^ var_of l ^ " w") (SM.bindings removed))
          ^ " s")
      else None

and saturate (cl, cd) =
  if cd > 0 && SM.exists (fun _ a -> a > cd) cl then
    (true, (SM.map (fun a -> min a cd) cl, cd))
  else (false, (cl, cd))

let row_text lits d =
  let b = Buffer.create 64 in
  SM.iter (fun l c -> Printf.bprintf b "+%d %s " c l) lits;
  Printf.bprintf b ">= %d" d;
  Buffer.contents b

(* ---------------------------------------------------------------------------
   What compile.ml tells this module about a constraint: the cake constraint the
   translator writes for it, over baguette's variable names and constants.
   --------------------------------------------------------------------------- *)

type operand = Var of string | Const of int

type spec =
  | Lin_le of (int * operand) list * int (* lin_less_equal (a x ...) c *)
  | Lin_eq of (int * operand) list * int (* lin_equals *)
  | Lin_ne of (int * operand) list * int (* lin_not_equals *)
  | Le of operand * operand (* less_equal x y *)
  | Lt of operand * operand (* less_than x y *)
  | Eq of operand * operand (* equals x y *)
  | Ne of operand * operand (* not_equals x y *)
  | All_different of operand list (* all_different (x ...) *)
  (* T4. A reify tuple (Z = v) is [(Z, v)]: the translator writes `(b = 1)`, `(b = 0)`
     and the constants `(1 = 1)`, `(0 = 1)`, and nothing else. *)
  | Or of (operand * int) list * (operand * int) (* or (tuples) tuple *)
  | And of (operand * int) list * (operand * int) (* and (tuples) tuple *)
  | Le_iff of (operand * int) * operand * operand (* less_equal_iff tuple x y *)
  | Eq_iff of (operand * int) * operand * operand (* equals_iff tuple x y *)
  | Ne_iff of (operand * int) * operand * operand (* not_equals_iff tuple x y *)
  | Lin_le_iff of (operand * int) * (int * operand) list * int
  (* lin_less_equal_iff tuple (a x ...) c *)
  (* T5 (T3b, D-0188), the translator's keywords for the globals *)
  | Element of int list * operand * operand (* element (a1 ... an) (i 1) z *)
  | Gcc of operand list * int list * operand list
    (* gacglobalcardinality (x ...) (v ...) (c ...) *)
  | Array_max of operand list * operand (* array_max (x ...) y *)
  | Array_min of operand list * operand (* array_min (x ...) y *)
  | Max of operand * operand * operand (* max x y z, z = max(x, y) *)
  | Min of operand * operand * operand (* min x y z *)
  | Inverse of operand list * int * operand list * int
    (* inverse ((f ...) fmin) ((g ...) gmin) *)
  | Member of (operand * operand) list * operand
  (* (c_k equals_if (b_k = 1) x_k y) per position k, from 1, then (c or ((b_k = 1) ...)
     (1 = 1)): [(b_k, x_k)] and y *)
  | Copy of string * string
  (* (original, copy): the int_eq lib/flatzinc/builder.ml adds to tie a gcc copy, which no
     .scp constraint states (D-0146 section 2, D-0188 section 3.3) *)
  (* T6 (D-0195) *)
  | Abs of operand * operand (* abs x z *)
  | Cumulative of operand list * int list * int list * int
    (* cumulative (s ...) (d ...) (r ...) cap, d, r and cap constants *)
  | Regular of operand list * int * (int * int) list array * int list
(* regular (x ...) n ((edges of state 0) ...) (finals), in CAKE's state numbering: see
   [regular_spec] *)

(* tools/e2e/fzn2scp.py's renumbering of a baguette_regular's states (D-0195 2.1): cake's
   NFA starts in state 0, so q goes to (q - q0) mod Q. *)
let regular_state ~q0 ~nq q = (((q - q0) mod nq) + nq) mod nq

(* The translator's `regular` for baguette_regular(x, Q, smin, d, q0, F, s): an edge
   (smin + j, pi(d)) out of pi(q) for every non-zero entry d of row q, finals pi(F). *)
let regular_spec ~letters ~nq ~smin ~delta ~q0 ~finals =
  let n = Array.length delta in
  if nq < 1 || n mod nq <> 0 || q0 < 1 || q0 > nq then
    refuse "a regular with %d states and %d transitions" nq n;
  if
    Array.exists (fun d -> d < 0 || d > nq) delta
    || List.exists (fun f -> f < 1 || f > nq) finals
  then refuse "a regular with a state outside 1..%d" nq;
  let w = n / nq and pi = regular_state ~q0 ~nq in
  let edges = Array.make nq [] in
  for q = 1 to nq do
    edges.(pi q) <-
      List.filter_map
        (fun j ->
          let d = delta.(((q - 1) * w) + j) in
          if d = 0 then None else Some (smin + j, pi d))
        (List.init w Fun.id)
  done;
  Regular (letters, nq, edges, List.sort_uniq compare (List.map pi finals))

(* A model Boolean with no .scp counterpart, DEFINED in the prefix by a red pair (D-0195):
   a regular state flag as cake's own flag ([Flag]), an arith guard `b <-> x >= w` as
   baguette's literal x_ge_w, or `b <-> x <= w - 1` as its negation ([Guard]). *)
type def = Flag of string | Guard of string * int * bool

(* A cake row in cake's own form (ilp_to_pb's PGe): sum_e c_e * B_{X_e} over the integer
   entries (one per occurrence, as cake keeps them), plus flag terms, >= deg. *)
type crow = {
  label : string;
  ints : (int * string) list; (* coefficient on B, baguette's variable name *)
  flags : (int * string) list; (* coefficient, flag literal *)
  deg : int;
}

type ivar = {
  x : string; (* baguette's name, the FlatZinc name *)
  cx : string; (* cake's *)
  lo : int;
  hi : int;
  comp : bool;
  h : int;
  bsum : (int * string) list;
  bmin : int;
  bmax : int;
  lit : int -> string; (* x_ge_v's name *)
  mutable e1 : string;
  mutable e2 : string;
  bitw : (int * string) list;
      (* T7 (D-0196): a bits variable's (2^i, x_bit_i); [] on the ladder *)
}

(* cp_to_ilpScript.sml, mk_constraint_ge a X b Y c: a * X + b * Y >= c, constants folded. *)
let mk_constraint_ge a x b y c =
  match (x, y) with
  | Var vx, Var vy -> ([ (a, vx); (b, vy) ], c)
  | Var vx, Const cy -> ([ (a, vx) ], c - mul b cy)
  | Const cx, Var vy -> ([ (b, vy) ], c - mul a cx)
  | Const cx, Const cy -> ([], c - mul a cx - mul b cy)

(* mk_lin_constraint_ge: sum a X >= b, constants folded, variables in REVERSE order (the
   order does not matter to a row; kept to say it is transcribed). *)
let mk_lin_constraint_ge axs b =
  List.fold_left
    (fun (is, rhs) (a, x) ->
      match x with Var v -> ((a, v) :: is, rhs) | Const k -> (is, rhs - mul a k))
    ([], b) axs

let negs axs = List.map (fun (a, x) -> (-a, x)) axs

(* ---------------------------------------------------------------------------
   The state
   --------------------------------------------------------------------------- *)

(* A candidate: the rpn of the `pol` that derives it ([plain] when it is a bare citation),
   its literal form, and the baguette variables it names. *)
type cand = {
  rpn : string;
  plain : bool;
  cl : int SM.t;
  cd : int;
  key : string;
  needs : string list; (* the @S labels its rpn cites, written when first cited *)
}

(* How a family's rows are pinned beyond the generic candidates (D-0188 section 2): the
   cake rows to LINEARISE at a target clause, chosen from what the clause says. *)
type fam =
  | Generic
  | Element_fam of { idx : string; n : int } (* the index variable, the array's length *)
  | Choice_fam of { choices : string list; al1 : string }
    (* maxmin: each operand's choice row [r], and the at-least-one over the flags *)
  | By_var of (string, string list) Hashtbl.t
  (* member (a selector -> its two equals_if rows), inverse (a variable -> its range rows) *)
  | Abs_fam (* T6: a row no candidate implies is derived by contradiction ([pin]) *)
  | Regular_fam of string list (* T6: its letters, whose eq atoms a `rup` pin reads *)

type con = {
  cname : string;
  cands : (string, cand list) Hashtbl.t;
  by_min : (string, cand list) Hashtbl.t; (* its least variable (or "") -> candidates *)
  aux_seen : (string, unit) Hashtbl.t;
  sel_flags : string list;
      (* D-0262: cake's flag of each selector compile.ml mints for this constraint, in
         the order it mints them ([selector_flags]); [] where none is known by position *)
  rows : (string, crow) Hashtbl.t; (* cake's rows for it, by label *)
  mutable fam : fam;
  mutable pending : string list; (* its @S labels not written yet *)
  mutable ncands : int;
  binary : (string, int * string) Hashtbl.t;
      (* member's and inverse's binary clause rows pinned so far: a literal -> (id, the
         other literal), to resolve a candidate's extra literal away ([resolve]) *)
}

type t = {
  path : string;
  oc : out_channel;
  b : Buffer.t;
  vars : (string, ivar) Hashtbl.t;
  cake_names : (string, string) Hashtbl.t;
  owner : (string, string) Hashtbl.t; (* ladder literal name -> baguette variable *)
  aux : (string, unit) Hashtbl.t; (* selector literal names (positive) *)
  sel : (string, string * bool) Hashtbl.t; (* selector lit -> (flag var, s <-> flag?) *)
  sel_of_flag : (string, string * bool) Hashtbl.t;
      (* the same, from the flag: looked up per candidate literal, so it is indexed (a scan
         of [sel] made sudoku_p48's prefix cost 9.8 s over 4 068 selectors) *)
  q : (string, unit) Hashtbl.t; (* atom clauses already derived, by label *)
  value_of : (string, int) Hashtbl.t; (* ladder literal name -> its value *)
  holes : (string, string * int list) Hashtbl.t;
      (* a variable with a set domain -> its `in` constraint's name and allowed values *)
  copies : (string, string) Hashtbl.t; (* a gcc copy -> its original (D-0188 3.3) *)
  defs : (string, def) Hashtbl.t; (* T6 (D-0195): a Boolean defined, not declared *)
  pending_s : (string, string) Hashtbl.t;
      (* an @S label -> its line, until a pin cites it (D-0188 section 3.2) *)
  mutable n_holes_vars : int;
  mutable cur : con option;
  mutable objective : (string * int) option;
  mutable nw : int;
  (* tallies, for the record and the comment line at the end *)
  mutable n_ia_rung : int;
  mutable n_ia_exact : int;
  mutable n_ia_w : int;
  mutable n_ia_lin : int; (* of which through a linearised cake row (T3b) *)
  mutable n_pol_lin : int; (* rows that ARE one pol of a linearised cake row (T3b) *)
  mutable n_rup : int;
  mutable n_pbc : int; (* T6: rows derived by contradiction (int_abs) *)
  mutable n_k : int; (* T6: cumulative's flag clauses *)
  mutable n_subst : int;
  mutable n_sel : int;
  mutable n_q : int;
  mutable finished : bool;
  (* T7 (D-0196) *)
  bound_q : string Queue.t;
      (* a bits variable's @BL/@BU, for its next two committed rows *)
  conj : (string, string list) Hashtbl.t;
      (* a choice selector defined as its flag AND no earlier one -> those earlier flags *)
  pos_flag : (string, string) Hashtbl.t;
      (* D-0262: a selector -> cake's flag at its position ([selector_flags]) *)
  mutable n_bits : int;
  mutable n_tight : int; (* rows derived by contradiction against the bits' ub rows *)
}

let create path =
  {
    path;
    oc = open_out_bin path;
    b = Buffer.create (1 lsl 16);
    vars = Hashtbl.create 64;
    cake_names = Hashtbl.create 64;
    owner = Hashtbl.create 256;
    aux = Hashtbl.create 16;
    sel = Hashtbl.create 16;
    sel_of_flag = Hashtbl.create 16;
    q = Hashtbl.create 64;
    value_of = Hashtbl.create 256;
    holes = Hashtbl.create 8;
    copies = Hashtbl.create 4;
    defs = Hashtbl.create 16;
    pending_s = Hashtbl.create 64;
    n_holes_vars = 0;
    cur = None;
    objective = None;
    nw = 0;
    n_ia_rung = 0;
    n_ia_exact = 0;
    n_ia_w = 0;
    n_ia_lin = 0;
    n_pol_lin = 0;
    n_rup = 0;
    n_pbc = 0;
    n_k = 0;
    n_subst = 0;
    n_sel = 0;
    n_q = 0;
    finished = false;
    bound_q = Queue.create ();
    conj = Hashtbl.create 4;
    pos_flag = Hashtbl.create 4;
    n_bits = 0;
    n_tight = 0;
  }

let flush_if t =
  if Buffer.length t.b >= 1 lsl 16 then (
    Buffer.output_buffer t.oc t.b;
    Buffer.clear t.b)

let emit t fmt =
  Printf.ksprintf
    (fun s ->
      Buffer.add_string t.b s;
      Buffer.add_char t.b '\n';
      flush_if t)
    fmt

let terms_text terms =
  String.concat " " (List.map (fun (c, l) -> Printf.sprintf "%+d %s" c l) terms)

(* ---------------------------------------------------------------------------
   Variables: atoms, halves, ladder. Written when the variable is declared, so they
   precede every line that names them.
   --------------------------------------------------------------------------- *)

(* T3b (D-0188 section 3.3): a gcc copy y of x has no bits in cake's file. Each rung is
   DEFINED as the original's by a red pair (the bridge's @Y1/@Y2, D-0180), and its ladder
   follows: @L[y_ge_(w+1)] = @Y1[y_ge_(w+1)] + @L[x_ge_(w+1)] + @Y2[y_ge_w]. *)
let copy t ~copy ~orig = Hashtbl.replace t.copies copy orig

(* T6 (D-0195): told before the variable is declared, like a copy *)
let flag t ~var ~cake = Hashtbl.replace t.defs var (Flag cake)
let guard t ~var ~x ~at ~pos = Hashtbl.replace t.defs var (Guard (x, at, pos))

let declare_copy t y ~orig ~lo ~hi ~lit =
  let v =
    match Hashtbl.find_opt t.vars orig with
    | Some v -> v
    | None -> refuse "the gcc copy %s's original %s is not declared before it" y orig
  in
  if v.lo <> lo || v.hi <> hi then
    refuse "the gcc copy %s has another range than %s" y orig;
  Hashtbl.replace t.vars y
    {
      x = y;
      cx = "";
      lo;
      hi;
      comp = false;
      h = 0;
      bsum = [];
      bmin = 0;
      bmax = 0;
      lit;
      e1 = "";
      e2 = "";
      bitw = [];
    };
  for w = lo + 1 to hi do
    let a = lit w and b = v.lit w in
    Hashtbl.replace t.owner a y;
    Hashtbl.replace t.value_of a w;
    emit t "@Y1[%s] red +1 ~%s +1 %s >= 1 : %s -> %s ;" a a b a b;
    emit t "@Y2[%s] red +1 %s +1 ~%s >= 1 : %s -> %s ;" a a b a b
  done;
  for w = lo + 1 to hi - 1 do
    emit t "@L[%s] pol @Y1[%s] @L[%s] + @Y2[%s] + ;"
      (lit (w + 1))
      (lit (w + 1))
      (v.lit (w + 1))
      (lit w)
  done

let declare ?(holes = []) t x ~lo ~hi ~lit =
  match t.cur with
  | None when Hashtbl.mem t.copies x ->
      declare_copy t x ~orig:(Hashtbl.find t.copies x) ~lo ~hi ~lit
  | None when Hashtbl.mem t.defs x ->
      (* T6 (D-0195): no bits in cake's file. s_ge_1 is fresh, so a red pair with witness
         s -> F makes it F: cake's regular flag (then swapped for s in every candidate, as
         a selector), or the guard's ladder literal (never swapped: it is baguette's own) *)
      if lo <> 0 || hi <> 1 then refuse "the defined Boolean %s is not 0..1" x;
      let s = lit 1 in
      Hashtbl.replace t.aux s ();
      let fl =
        match Hashtbl.find t.defs x with
        | Flag f ->
            Hashtbl.replace t.sel_of_flag f (s, true);
            f
        | Guard (y, w, pos) ->
            let v =
              match Hashtbl.find_opt t.vars y with
              | Some v -> v
              | None -> refuse "the guard %s is declared before its variable %s" x y
            in
            if w <= v.lo || w > v.hi then
              refuse "the guard %s over %s at %d, outside its ladder" x y w;
            if v.bitw <> [] then (
              (* T7 (D-0196): over a bits variable, cake's own atom (the order atom is minted
                 later, by the solver's proof); swapped for s in candidates *)
              let g = Printf.sprintf "i[%s][ge%d]" v.cx w in
              Hashtbl.replace t.sel_of_flag g (s, pos);
              if pos then g else "~" ^ g)
            else if pos then v.lit w
            else "~" ^ v.lit w
      in
      Hashtbl.replace t.sel s (fl, true);
      t.n_sel <- t.n_sel + 1;
      emit t "@D1[%s] red +1 ~%s +1 %s >= 1 : %s -> %s ;" s s fl s fl;
      emit t "@D2[%s] red +1 %s +1 %s >= 1 : %s -> %s ;" s s (neg_lit fl) s fl
  | Some c ->
      (* an auxiliary declared while a constraint is posted: a disequality selector *)
      if lo <> 0 || hi <> 1 then
        refuse "an auxiliary integer %s in constraint %s" x c.cname;
      (* D-0262: the k-th selector of a constraint whose selectors compile.ml mints in a
         known order is cake's k-th flag ([selector_flags]); [pin] defines it before the
         first row that names it *)
      (if c.sel_flags <> [] then
         match List.nth_opt c.sel_flags (Hashtbl.length c.aux_seen) with
         | Some f -> Hashtbl.replace t.pos_flag (lit 1) f
         | None -> refuse "a selector %s past cake's flags in constraint %s" x c.cname);
      Hashtbl.replace t.aux (lit 1) ();
      Hashtbl.replace c.aux_seen (lit 1) ()
  | None ->
      let cx = scp_name x in
      (match Hashtbl.find_opt t.cake_names cx with
      | Some y -> refuse "variables %s and %s have the same .scp name %s" y x cx
      | None -> Hashtbl.replace t.cake_names cx x);
      (* a set domain with holes is the translator's `(d<k> in (v ...) X)`, k counted over
         such variables in declaration order (tools/e2e/fzn2scp.py), cake's eq atoms of the
         allowed values and `@c[d<k>][al1]` over them *)
      if holes <> [] then (
        t.n_holes_vars <- t.n_holes_vars + 1;
        let allowed =
          List.filter
            (fun v -> not (List.mem v holes))
            (List.init (hi - lo + 1) (fun i -> lo + i))
        in
        Hashtbl.replace t.holes x (Printf.sprintf "d%d" t.n_holes_vars, allowed));
      let comp, h = bit_width ~lo ~hi in
      let bits = List.init h (fun i -> (pow2 i, Printf.sprintf "i[%s][b%d]" cx i)) in
      let bsum =
        if comp then (-pow2 h, Printf.sprintf "i[%s][sign]" cx) :: bits else bits
      in
      let bmin = List.fold_left (fun a (c, _) -> if c < 0 then a + c else a) 0 bsum in
      let bmax = List.fold_left (fun a (c, _) -> if c > 0 then a + c else a) 0 bsum in
      let v =
        { x; cx; lo; hi; comp; h; bsum; bmin; bmax; lit; e1 = ""; e2 = ""; bitw = [] }
      in
      Hashtbl.replace t.vars x v;
      let pos_b = terms_text bsum
      and neg_b = terms_text (List.map (fun (c, n) -> (-c, n)) bsum) in
      for w = lo + 1 to hi do
        let a = lit w in
        Hashtbl.replace t.owner a x;
        Hashtbl.replace t.value_of a w;
        let m = ck (w - bmin) and k = ck (bmax - w + 1) in
        emit t "@A1[%s] red %s +%d ~%s >= %d : %s -> 0 ;" a pos_b m a w a;
        emit t "@A2[%s] red %s +%d %s >= %d : %s -> 1 ;" a neg_b k a (1 - w) a
      done;
      (* E1 = B - S >= l, upwards *)
      let prev = ref (Printf.sprintf "@i[%s][lb]" cx) in
      for w = lo + 1 to hi do
        let a = lit w in
        let m = w - bmin in
        if w = lo + 1 then emit t "@T1[%s] pol ~%s ;" a a
        else emit t "@T1[%s] pol @T1[%s] ~%s + ;" a (lit (w - 1)) a;
        emit t "@E1[%s] pol %s %d * @A1[%s] + @T1[%s] + %d d ;" a !prev m a a (m + 1);
        if w > lo + 1 then emit t "del id @T1[%s] @E1[%s] ;" (lit (w - 1)) (lit (w - 1));
        prev := Printf.sprintf "@E1[%s]" a
      done;
      if hi > lo then emit t "del id @T1[%s] ;" (lit hi);
      v.e1 <- !prev;
      (* E2 = S - B >= -l, downwards *)
      let prev = ref (Printf.sprintf "@i[%s][ub]" cx) in
      for w = hi downto lo + 1 do
        let a = lit w in
        let k = bmax - w + 1 in
        if w = hi then emit t "@T2[%s] pol %s ;" a a
        else emit t "@T2[%s] pol @T2[%s] %s + ;" a (lit (w + 1)) a;
        emit t "@E2[%s] pol %s %d * @A2[%s] + @T2[%s] + %d d ;" a !prev k a a (k + 1);
        if w < hi then emit t "del id @T2[%s] @E2[%s] ;" (lit (w + 1)) (lit (w + 1));
        prev := Printf.sprintf "@E2[%s]" a
      done;
      if hi > lo then emit t "del id @T2[%s] ;" (lit (lo + 1));
      v.e2 <- !prev;
      for w = lo + 1 to hi - 1 do
        emit t "@L[%s] pol @A1[%s] @A2[%s] + s %d d ;"
          (lit (w + 1))
          (lit (w + 1))
          (lit w)
          (ck (bmax - bmin + 2))
      done

(* ---------------------------------------------------------------------------
   T7 (D-0196): a variable on baguette's BITS arm. Its x_bit_i (i < n) are the bits of
   x - lo, unsigned (PROOF-FORMAT section 3); cake's are x's two's complement. Over cake's
   digits u_j (b_j for j < h, ~sign at j = h when lo < 0), U = B + 2^h [sign] is unsigned on
   m digits and x - lo = U - L', L' = lo + 2^h [sign] >= 0, so the digits of x - lo are those
   of U + c, c = (2^m - L') mod 2^m: a ripple-carry adder, whose relation at digit i is ONE
   linear row,

     d_i + 2 k_(i+1) = u_i + c_i + k_i        (k_0 = 0)

   While the carry is a constant the next one is 0, u_i or 1; once it is a literal, k_(i+1)
   is fresh (x_bitc_(i+1)), defined by a red pair whose goals are tautologies:

     @BK1[k]  T - 2k >= 0 : k -> 0        @BK2[k]  2k - T >= -1 : k -> 1     (T = u_i + c_i + k_i)

   and d_i (x_bit_i for i < n, x_bith_i above, where it is zero) by the relation's halves:

     @BP[d]   d + 2k - T >= 0 : d -> 1    (goal: @BK2)
     @BN[d]   T - 2k - d >= 0 : d -> 0    (goal: @BK1)

   With lo = 0 and no sign every carry is 0 and each pair renames d_i to b_i. Summed with
   weights 2^i (@BPs, @BNs) the relations telescope to S_all + 2^m k_m = U + c. The final
   carry is a unit by rup against @BPs + cake's lb row (@BPk, @BK), each high digit a unit
   ~d by rup against @BNs + cake's ub row (@BNk, @BZ), and the halves follow by one pol each:

     @BE1 = @BNs + 2^m @BK + sum_high 2^j d_j            B - S >= lo
     @BE2 = @BPs + 2^m ~k_m + sum_high 2^j @BZ[d_j]       S - B >= -lo

   (S = sum 2^i x_bit_i), the order arm's halves over the bits, so substitution is the same.
   baguette's two bound rows are `ia` against @BL = @BE2 + lb and @BU = @BE1 + ub.
   --------------------------------------------------------------------------- *)

let declare_bits t x ~lo ~hi ~n ~bit =
  (match t.cur with
  | Some c -> refuse "a bits variable %s declared inside constraint %s" x c.cname
  | None -> ());
  if Hashtbl.mem t.copies x || Hashtbl.mem t.defs x then
    refuse "%s is on the bits encoding and has no .scp counterpart" x;
  let cx = scp_name x in
  (match Hashtbl.find_opt t.cake_names cx with
  | Some y -> refuse "variables %s and %s have the same .scp name %s" y x cx
  | None -> Hashtbl.replace t.cake_names cx x);
  let comp, h = bit_width ~lo ~hi in
  let bits = List.init h (fun i -> (pow2 i, Printf.sprintf "i[%s][b%d]" cx i)) in
  let bsum = if comp then (-pow2 h, Printf.sprintf "i[%s][sign]" cx) :: bits else bits in
  let bmin = List.fold_left (fun a (c, _) -> if c < 0 then a + c else a) 0 bsum in
  let bmax = List.fold_left (fun a (c, _) -> if c > 0 then a + c else a) 0 bsum in
  let bitw = List.init n (fun i -> (pow2 i, bit i)) in
  let v =
    {
      x;
      cx;
      lo;
      hi;
      comp;
      h;
      bsum;
      bmin;
      bmax;
      lit = (fun _ -> refuse "an order atom of the bits variable %s in the prefix" x);
      e1 = "";
      e2 = "";
      bitw;
    }
  in
  Hashtbl.replace t.vars x v;
  List.iter (fun (_, b) -> Hashtbl.replace t.owner b x) bitw;
  t.n_bits <- t.n_bits + 1;
  let digits =
    Array.of_list
      (List.init h (fun j -> Printf.sprintf "i[%s][b%d]" cx j)
      @ if comp then [ Printf.sprintf "~i[%s][sign]" cx ] else [])
  in
  let m = Array.length digits in
  let lp = lo + if comp then pow2 h else 0 in
  if lp < 0 || lp >= pow2 m || n > m then
    refuse "%s over [%d, %d] does not fit its %d digits" x lo hi m;
  let c = (pow2 m - lp) mod pow2 m in
  let dig i = if i < n then bit i else Printf.sprintf "%s_bith_%d" (Lit.sanitize x) i in
  let row terms d =
    let vm, d = var_form terms d in
    let b = Buffer.create 64 in
    SM.iter (fun l k -> Printf.bprintf b "%+d %s " k l) vm;
    Printf.bprintf b ">= %d" d;
    Buffer.contents b
  in
  let lneg = List.map (fun (a, l) -> (-a, l)) in
  (* the carry: a constant, or a literal *)
  let k = ref (`C 0) in
  for i = 0 to m - 1 do
    let ui = digits.(i) and ci = (c lsr i) land 1 in
    let d = dig i in
    let kp, tt, tc =
      match !k with
      | `C k0 ->
          let sk = ci + k0 in
          ((if sk = 0 then `C 0 else if sk = 1 then `L ui else `C 1), [ (1, ui) ], sk)
      | `L kl ->
          let kp = Printf.sprintf "%s_bitc_%d" (Lit.sanitize x) (i + 1) in
          let tt = [ (1, ui); (1, kl) ] in
          emit t "@BK1[%s] red %s : %s -> 0 ;" kp (row (tt @ [ (-2, kp) ]) (-ci)) kp;
          emit t "@BK2[%s] red %s : %s -> 1 ;" kp (row ((2, kp) :: lneg tt) (ci - 1)) kp;
          (`L kp, tt, ci)
    in
    let kt, kc = match kp with `C k1 -> ([], 2 * k1) | `L l -> ([ (2, l) ], 0) in
    emit t "@BP[%s] red %s : %s -> 1 ;" d (row (((1, d) :: kt) @ lneg tt) (tc - kc)) d;
    emit t "@BN[%s] red %s : %s -> 0 ;" d (row (tt @ lneg kt @ [ (-1, d) ]) (kc - tc)) d;
    k := kp
  done;
  let wsum tag =
    String.concat " "
      (List.init m (fun i ->
           if i = 0 then Printf.sprintf "@%s[%s]" tag (dig 0)
           else Printf.sprintf "@%s[%s] %d * +" tag (dig i) (pow2 i)))
  in
  let sx = Lit.sanitize x in
  emit t "@BPs[%s] pol %s ;" sx (wsum "BP");
  emit t "@BNs[%s] pol %s ;" sx (wsum "BN");
  let km =
    match !k with
    | `L l -> Some l
    | `C 0 -> None
    | `C _ -> refuse "%s's final carry is a constant 1" x
  in
  let mm = pow2 m in
  (match km with
  | Some l ->
      emit t "@BPk[%s] pol @BPs[%s] @i[%s][lb] + ;" sx sx cx;
      emit t "@BK[%s] rup +1 %s >= 1 ;" sx l
  | None -> ());
  emit t "@BNk[%s] pol @BNs[%s] @i[%s][ub] +%s ;" sx sx cx
    (match km with Some _ -> Printf.sprintf " @BK[%s] %d * +" sx mm | None -> "");
  for j = n to m - 1 do
    emit t "@BZ[%s] rup +1 ~%s >= 1 ;" (dig j) (dig j)
  done;
  let high f =
    String.concat "" (List.init (m - n) (fun j -> f (dig (n + j)) (pow2 (n + j))))
  in
  emit t "@BE1[%s] pol @BNs[%s]%s%s ;" sx sx
    (match km with Some _ -> Printf.sprintf " @BK[%s] %d * +" sx mm | None -> "")
    (high (fun d w -> Printf.sprintf " %s %d * +" d w));
  emit t "@BE2[%s] pol @BPs[%s]%s%s ;" sx sx
    (match km with Some l -> Printf.sprintf " %s %d * +" (neg_lit l) mm | None -> "")
    (high (fun d w -> Printf.sprintf " @BZ[%s] %d * +" d w));
  v.e1 <- Printf.sprintf "@BE1[%s]" sx;
  v.e2 <- Printf.sprintf "@BE2[%s]" sx;
  emit t "@BL[%s] pol %s @i[%s][lb] + ;" sx v.e2 cx;
  emit t "@BU[%s] pol %s @i[%s][ub] + ;" sx v.e1 cx;
  Queue.push (Printf.sprintf "@BL[%s]" sx) t.bound_q;
  Queue.push (Printf.sprintf "@BU[%s]" sx) t.bound_q

let find_var t x =
  match Hashtbl.find_opt t.vars x with
  | Some v -> v
  | None -> refuse "a constraint names %s, which is not a declared model variable" x

(* ---------------------------------------------------------------------------
   cake's rows for one constraint (the contract, per keyword)
   --------------------------------------------------------------------------- *)

let rec cake_rows t name spec =
  let lab tag = Printf.sprintf "c[%s][%s]" name tag in
  let width x =
    let v = find_var t x in
    (v.comp, v.h)
  in
  (* ilpScript.sml, bits_imply bnd [lit] (is, [], c): the big-M on the negated literal *)
  let bits_imply flag (is, c) =
    let mn =
      List.fold_left
        (fun a (k, x) ->
          let comp, h = width x in
          a + min_iterm ~comp ~h k)
        0 is
    in
    let rr = max 0 (ck (c - mn)) in
    (is, [ (rr, flag) ], c)
  in
  (* ilpScript.sml, imply_bit bnd lit (is, [], c): the constraint implies the literal;
     its big-M is over the UNFLIPPED terms' maximum (imply_bit_aux) *)
  let imply_bit flag (is, c) =
    let mx =
      List.fold_left
        (fun a (k, x) ->
          let comp, h = width x in
          a + max_iterm ~comp ~h k)
        0 is
    in
    let nc = 1 - c in
    let rr = max 0 (ck (nc + mx)) in
    (List.map (fun (k, x) -> (-k, x)) is, [ (rr, flag) ], nc)
  in
  let row label (is, flags, c) = { label; ints = is; flags; deg = c } in
  let plain label (is, c) = row label (is, [], c) in
  let ne_flag = Printf.sprintf "b[%s][ne]" name in
  (* cp_to_ilpScript.sml, format_reif (Eq Z v): the atom of the reify tuple (Z = v) *)
  let eq_atom (z, v) =
    match z with
    | Var x -> Printf.sprintf "i[%s][eq%d]" (find_var t x).cx v
    | Const k -> Printf.sprintf "n[%d][eq%d]" k v
  in
  let gt = Printf.sprintf "b[%s][gt]" name and lt = Printf.sprintf "b[%s][lt]" name in
  let mk_le x y = mk_constraint_ge 1 y (-1) x 0
  and mk_ge x y = mk_constraint_ge 1 x (-1) y 0 in
  let mk_gt x y = mk_constraint_ge 1 x (-1) y 1
  and mk_lt x y = mk_constraint_ge 1 y (-1) x 1 in
  match spec with
  (* cp_to_ilp_logicalScript.sml, encode_or_aux / encode_and_aux, labelled pos and neg *)
  | Or (xs, y) ->
      let n = List.length xs in
      [
        row (lab "pos") ([], (-1, eq_atom y) :: List.map (fun x -> (1, eq_atom x)) xs, 0);
        row (lab "neg")
          ([], (-n, "~" ^ eq_atom y) :: List.map (fun x -> (1, "~" ^ eq_atom x)) xs, 0);
      ]
  | And (xs, y) ->
      let n = List.length xs in
      [
        row (lab "pos") ([], (-n, eq_atom y) :: List.map (fun x -> (1, eq_atom x)) xs, 0);
        row (lab "neg")
          ([], (-1, "~" ^ eq_atom y) :: List.map (fun x -> (1, "~" ^ eq_atom x)) xs, 0);
      ]
  (* cencode_order_cmpops / cencode_lin_order_cmpops with SOME (INR Zc):
     bimply_bits bnd [reif_gen Zc] constr, labelled r and f *)
  | Le_iff (z, x, y) ->
      let e = eq_atom z in
      [
        row (lab "r") (bits_imply ("~" ^ e) (mk_le x y));
        row (lab "f") (imply_bit e (mk_le x y));
      ]
  | Lin_le_iff (z, axs, c) ->
      let e = eq_atom z and constr = mk_lin_constraint_ge ((1, Const c) :: negs axs) 0 in
      [ row (lab "r") (bits_imply ("~" ^ e) constr); row (lab "f") (imply_bit e constr) ]
  (* cp_to_ilp_primScript.sml, cencode_equal_2 *)
  | Eq_iff (z, x, y) ->
      let e = eq_atom z in
      [
        row (lab "ge") (bits_imply ("~" ^ e) (mk_ge x y));
        row (lab "le") (bits_imply ("~" ^ e) (mk_le x y));
        row (gt ^ "[r]") (bits_imply ("~" ^ gt) (mk_gt x y));
        row (lt ^ "[r]") (bits_imply ("~" ^ lt) (mk_lt x y));
        row (lab "al1") ([], [ (1, lt); (1, gt); (1, e) ], 1);
      ]
  (* cencode_not_equal_3 *)
  | Ne_iff (z, x, y) ->
      let e = eq_atom z in
      [
        row (lab "ge") (bits_imply e (mk_ge x y));
        row (lab "le") (bits_imply e (mk_le x y));
        row (gt ^ "[f]") (imply_bit gt (mk_gt x y));
        row (gt ^ "[r]") (bits_imply ("~" ^ gt) (mk_gt x y));
        row (lt ^ "[f]") (imply_bit lt (mk_lt x y));
        row (lt ^ "[r]") (bits_imply ("~" ^ lt) (mk_lt x y));
        row (lab "al1") ([], [ (1, lt); (1, gt); (1, "~" ^ e) ], 1);
      ]
  | Le (x, y) -> [ plain (Printf.sprintf "c[%s]" name) (mk_constraint_ge 1 y (-1) x 0) ]
  | Lt (x, y) -> [ plain (Printf.sprintf "c[%s]" name) (mk_constraint_ge 1 y (-1) x 1) ]
  | Eq (x, y) ->
      [
        plain (lab "ge") (mk_constraint_ge 1 x (-1) y 0);
        plain (lab "le") (mk_constraint_ge 1 y (-1) x 0);
      ]
  | Ne (x, y) ->
      [
        row (lab "gt") (bits_imply ("~" ^ ne_flag) (mk_constraint_ge 1 x (-1) y 1));
        row (lab "lt") (bits_imply ne_flag (mk_constraint_ge 1 y (-1) x 1));
      ]
  | Lin_le (axs, c) ->
      (* mk_lin_le cXs Y = mk_lin_constraint_ge ((1, Y) :: -cXs) 0, Y the constant c *)
      [
        plain (Printf.sprintf "c[%s]" name)
          (mk_lin_constraint_ge ((1, Const c) :: negs axs) 0);
      ]
  | Lin_eq (axs, c) ->
      [
        plain (lab "ge") (mk_lin_constraint_ge ((-1, Const c) :: axs) 0);
        plain (lab "le") (mk_lin_constraint_ge ((1, Const c) :: negs axs) 0);
      ]
  | Lin_ne (axs, c) ->
      [
        row (lab "gt")
          (bits_imply ("~" ^ ne_flag) (mk_lin_constraint_ge ((-1, Const c) :: axs) 1));
        row (lab "lt")
          (bits_imply ne_flag (mk_lin_constraint_ge ((1, Const c) :: negs axs) 1));
      ]
  | All_different xs ->
      (* cp_to_ilp_countingScript.sml, cencode_all_different_except_aux with iS = [] *)
      let xa = Array.of_list xs in
      let n = Array.length xa in
      List.concat
        (List.init n (fun i ->
             List.concat
               (List.init n (fun j ->
                    if i < j then
                      let f = Printf.sprintf "x[%s][%d_%d]" name i j in
                      [
                        row
                          (lab (Printf.sprintf "%dgt%d" i j))
                          (bits_imply ("~" ^ f) (mk_constraint_ge 1 xa.(i) (-1) xa.(j) 1));
                        row
                          (lab (Printf.sprintf "%dlt%d" i j))
                          (bits_imply f (mk_constraint_ge 1 xa.(j) (-1) xa.(i) 1));
                      ]
                    else []))))
  (* cp_to_ilp_arrayScript.sml, cencode_element with offset 1 (the translator's `(i 1)`):
     the index's eq atoms (cencode_full_eq, not rows here), cencode_proper_index's
     `lb`/`ub` when the index's range leaves 1..n, and per position p from 0 the two
     halves of `z = a_p`, guarded by the index's eq atom of value 1 + p *)
  | Element (arr, i, z) ->
      let n = List.length arr in
      let lb, ub =
        match i with
        | Var x ->
            let v = find_var t x in
            (v.lo, v.hi)
        | Const k -> (k, k)
      in
      let one_ge a y b =
        match y with Var vy -> ([ (a, vy) ], b) | Const cy -> ([], b - mul a cy)
      in
      (if lb < 1 then [ plain (lab "lb") (one_ge 1 i 1) ] else [])
      @ (if ub > n then [ plain (lab "ub") (one_ge (-1) i (1 - n - 1)) ] else [])
      @ List.concat
          (List.mapi
             (fun p a ->
               let e = "~" ^ eq_atom (i, 1 + p) in
               [
                 row (lab (Printf.sprintf "%dge" p)) (bits_imply e (mk_ge (Const a) z));
                 row (lab (Printf.sprintf "%dle" p)) (bits_imply e (mk_le (Const a) z));
               ])
             arr)
  (* cp_to_ilp_countingScript.sml, cencode_global_cardinality with clsd = F: per cover
     value v_j (j from 0) cencode_bitsum of the eq atoms [x_i = v_j] against c_j
     (encode_bitsum, ilp_to_pb's >= form), labelled `<j>_ge` and `<j>_le` *)
  | Gcc (xs, cover, counts) ->
      (* the translator names a repeated variable once per occurrence; baguette's copies
         are moved back onto their originals here and split again by [split_copies] *)
      let xs =
        List.map
          (function
            | Var x -> Var (Option.value (Hashtbl.find_opt t.copies x) ~default:x)
            | c -> c)
          xs
      in
      if List.length cover <> List.length counts then
        refuse "global_cardinality with %d cover values and %d counts" (List.length cover)
          (List.length counts);
      List.concat
        (List.mapi
           (fun j (v, cnt) ->
             let pos = List.map (fun x -> (1, eq_atom (x, v))) xs
             and neg = List.map (fun x -> (-1, eq_atom (x, v))) xs in
             let ge = lab (Printf.sprintf "%d_ge" j)
             and le = lab (Printf.sprintf "%d_le" j) in
             match cnt with
             | Var y -> [ row ge ([ (-1, y) ], pos, 0); row le ([ (1, y) ], neg, 0) ]
             | Const k -> [ row ge ([], pos, k); row le ([], neg, -k) ])
           (List.combine cover counts))
  (* cencode_array_max / cencode_array_min: a choice flag x[N][i] per operand
     (cbimply_var: `[f]` and `[r]`), the other half as `<i>le` (resp. `<i>ge`), and the
     at-least-one over the flags *)
  | Array_max (xs, y) | Array_min (xs, y) ->
      let is_max = match spec with Array_max _ -> true | _ -> false in
      let flag i = Printf.sprintf "x[%s][%d]" name i in
      let choice x = if is_max then mk_ge x y else mk_le x y
      and other x = if is_max then mk_le x y else mk_ge x y in
      List.concat
        (List.mapi
           (fun i x ->
             [
               row (flag i ^ "[f]") (imply_bit (flag i) (choice x));
               row (flag i ^ "[r]") (bits_imply ("~" ^ flag i) (choice x));
             ])
           xs)
      @ List.mapi
          (fun i x ->
            plain
              (lab (Printf.sprintf "%d%s" i (if is_max then "le" else "ge")))
              (other x))
          xs
      @ [ row (lab "al1") ([], List.mapi (fun i _ -> (1, flag i)) xs, 1) ]
  (* cp_to_ilp_primScript.sml, cencode_max / cencode_min: two flags with `[r]` only
     (cvar_imply), the other half as `lle`/`rle` (resp. `lge`/`rge`), the at-least-one *)
  | Max (x, y, z) | Min (x, y, z) ->
      let is_max = match spec with Max _ -> true | _ -> false in
      let c, o = if is_max then ("ge", "le") else ("le", "ge") in
      let fl = Printf.sprintf "b[%s][l%s]" name c
      and fr = Printf.sprintf "b[%s][r%s]" name c in
      let choice a = if is_max then mk_ge a z else mk_le a z
      and other a = if is_max then mk_le a z else mk_ge a z in
      [
        row (fl ^ "[r]") (bits_imply ("~" ^ fl) (choice x));
        row (fr ^ "[r]") (bits_imply ("~" ^ fr) (choice y));
        plain (lab ("l" ^ o)) (other x);
        plain (lab ("r" ^ o)) (other y);
        row (lab "al1") ([], [ (1, fl); (1, fr) ], 1);
      ]
  (* cp_to_ilp_channelingScript.sml, cencode_inverse (X = f from fmin, Y = g from gmin):
     the eq atoms, mk_bounds of each f into g's indices and of each g into f's, labelled
     `X_<k>_lb|ub`, `Y_<k>_lb|ub` (k from 1), and per (i, j) from 0 encode_bvar_eq of
     [f_i = gmin + j] and [g_j = fmin + i], labelled `<i+1>_<j+1>ge|le` *)
  | Inverse (f, fmin, g, gmin) ->
      let n = List.length f in
      if n <> List.length g then
        refuse "inverse over arrays of lengths %d and %d" n (List.length g);
      let one_ge a y b =
        match y with Var vy -> ([ (a, vy) ], b) | Const cy -> ([], b - mul a cy)
      in
      let bounds side xs off =
        List.concat
          (List.mapi
             (fun k x ->
               [
                 plain (lab (Printf.sprintf "%s_%d_lb" side (k + 1))) (one_ge 1 x off);
                 plain
                   (lab (Printf.sprintf "%s_%d_ub" side (k + 1)))
                   (one_ge (-1) x (-(off + n - 1)));
               ])
             xs)
      in
      bounds "X" f gmin @ bounds "Y" g fmin
      @ List.concat
          (List.mapi
             (fun i x ->
               List.concat
                 (List.mapi
                    (fun j y ->
                      let a = eq_atom (x, gmin + j) and b = eq_atom (y, fmin + i) in
                      [
                        row
                          (lab (Printf.sprintf "%d_%dge" (i + 1) (j + 1)))
                          ([], [ (1, a); (-1, b) ], 0);
                        row
                          (lab (Printf.sprintf "%d_%dle" (i + 1) (j + 1)))
                          ([], [ (1, b); (-1, a) ], 0);
                      ])
                    g))
             f)
  (* the translator's member: cencode_equal with SOME (INL (b_k, Equal, 1)) per position,
     `ge` and `le` guarded by the eq atom, then T4's `or` over the selectors' tuples *)
  | Member (bxs, y) ->
      List.concat
        (List.mapi
           (fun k (b, x) ->
             let e = "~" ^ eq_atom (b, 1) and nk = Printf.sprintf "%s_%d" name (k + 1) in
             [
               row (Printf.sprintf "c[%s][ge]" nk) (bits_imply e (mk_ge x y));
               row (Printf.sprintf "c[%s][le]" nk) (bits_imply e (mk_le x y));
             ])
           bxs)
      @ cake_rows t name (Or (List.map (fun (b, _) -> (b, 1)) bxs, (Const 1, 1)))
  | Copy _ -> []
  (* cp_to_ilp_primScript.sml, cencode_abs (T6, D-0195): the atom i[X][ge0] and the four
     rows of encode_abs_body, the first two guarded by it, the last two by its negation *)
  | Abs (x, z) -> (
      let g =
        match x with
        | Var v -> Printf.sprintf "i[%s][ge0]" (find_var t v).cx
        | Const _ -> refuse "int_abs of a constant"
      in
      let mk_nle x y = mk_constraint_ge 1 y 1 x 0
      and mk_nge x y = mk_constraint_ge (-1) x (-1) y 0 in
      [
        row (lab "posge") (bits_imply ("~" ^ g) (mk_ge x z));
        row (lab "posle") (bits_imply ("~" ^ g) (mk_le x z));
        row (lab "negle") (bits_imply g (mk_nle x z));
        row (lab "negge") (bits_imply g (mk_nge x z));
      ]
      (* T7 (D-0196): over a bits x, the guard is the atom itself, and its two definition
         rows (cp_to_ilpScript.sml, cencode_ge: imply_bit and bits_imply over x >= 0) are
         the candidates of the guard's own rows *)
      @
      match x with
      | Var v when (find_var t v).bitw <> [] ->
          [
            row (g ^ "[f]") (imply_bit g ([ (1, v) ], 0));
            row (g ^ "[r]") (bits_imply ("~" ^ g) ([ (1, v) ], 0));
          ]
      | _ -> [])
  (* cp_to_ilp_extensionalScript.sml, cencode_regular (T6, D-0195): the state flags
     x[N][<idx>_<q>][st], exactly one per position (`pos<idx>al1`, `am1`), some final at the
     end (`st<n>al1`), the start (`st0`), and per position, state and value index vi of the
     letter's domain (bounds: holes are `in` constraints) the clause `<idx>_<q>_<vi>t`,
     st /\ [X = v] -> OR of the targets' flags *)
  | Regular (xs, nq, edges, finals) ->
      let n = List.length xs in
      let st i q = Printf.sprintf "x[%s][%d_%d][st]" name i q in
      let layer i = List.init nq (fun q -> st i q) in
      List.concat
        (List.init (n + 1) (fun i ->
             [
               row
                 (lab (Printf.sprintf "pos%dal1" i))
                 ([], List.map (fun f -> (1, f)) (layer i), 1);
               row
                 (lab (Printf.sprintf "pos%dam1" i))
                 ([], List.map (fun f -> (-1, f)) (layer i), -1);
             ]))
      @ [
          row
            (lab (Printf.sprintf "st%dal1" n))
            ( [],
              List.filter_map (fun f -> if f < nq then Some (1, st n f) else None) finals,
              1 );
          row (lab "st0") ([], [ (1, st 0 0) ], 1);
        ]
      @ List.concat
          (List.mapi
             (fun i x ->
               (* a constant letter is cake's constant: its one value, the atom n[K][eq<K>] *)
               let values, atom =
                 match x with
                 | Var x ->
                     let v = find_var t x in
                     ( List.init (v.hi - v.lo + 1) (fun k -> v.lo + k),
                       fun value -> Printf.sprintf "i[%s][eq%d]" v.cx value )
                 | Const k -> ([ k ], fun value -> Printf.sprintf "n[%d][eq%d]" k value)
               in
               List.concat
                 (List.mapi
                    (fun vi value ->
                      let e = atom value in
                      List.init nq (fun q ->
                          let tg =
                            List.filter_map
                              (fun (sym, q2) ->
                                if sym = value && q2 < nq then Some (1, st (i + 1) q2)
                                else None)
                              edges.(q)
                          in
                          row
                            (lab (Printf.sprintf "%d_%d_%dt" i q vi))
                            ([], (1, "~" ^ st i q) :: (1, "~" ^ e) :: tg, 1)))
                    values))
             xs)
  (* cumulative's rows are not offered as candidates: [begin_con] derives one row per time
     point from them ([cumulative_cands]) *)
  | Cumulative _ -> []

(* The substituted row's literal form and the label of the line that derives it. The line
   is NOT written here (D-0188 section 3.2): it waits in [pending_s] until a pin cites it
   ([ensure_s]), or a `rup` pin of the same constraint needs the whole database ([flush_s]).
   Returns the label it waits under, if any. *)
let substitute t (r : crow) =
  let per = Hashtbl.create 4 in
  List.iter
    (fun (k, x) ->
      Hashtbl.replace per x (Option.value (Hashtbl.find_opt per x) ~default:0 + k))
    r.ints;
  let xs = List.sort_uniq compare (List.map snd r.ints) in
  let vm, d =
    List.fold_left
      (fun (m, d) x ->
        let k = Hashtbl.find per x in
        if k = 0 then (m, d)
        else
          let v = find_var t x in
          let m = ref m in
          if v.bitw <> [] then
            (* T7: S = sum 2^i x_bit_i *)
            List.iter
              (fun (w, b) ->
                m := SM.update b (fun o -> Some (Option.value o ~default:0 + mul k w)) !m)
              v.bitw
          else
            for w = v.lo + 1 to v.hi do
              m := SM.update (v.lit w) (fun o -> Some (Option.value o ~default:0 + k)) !m
            done;
          (!m, d - mul k v.lo))
      (SM.empty, r.deg) xs
  in
  let vm, d =
    let fm, fd = var_form r.flags 0 in
    (SM.union (fun _ a b -> Some (a + b)) vm fm, d + fd)
  in
  let rpn =
    List.filter_map
      (fun x ->
        let k = Hashtbl.find per x in
        if k = 0 then None
        else
          let v = find_var t x in
          Some (Printf.sprintf "%s %d * +" (if k > 0 then v.e2 else v.e1) (abs k)))
      xs
  in
  let cite =
    if rpn = [] then "@" ^ r.label
    else
      let lab = Printf.sprintf "@S[%s]" r.label in
      Hashtbl.replace t.pending_s lab
        (Printf.sprintf "%s pol @%s %s ;" lab r.label (String.concat " " rpn));
      lab
  in
  (cite, lit_form (SM.filter (fun _ c -> c <> 0) vm, d))

let ensure_s t lab =
  match Hashtbl.find_opt t.pending_s lab with
  | None -> ()
  | Some line ->
      Hashtbl.remove t.pending_s lab;
      if String.length lab > 3 && String.sub lab 0 3 = "@K[" then t.n_k <- t.n_k + 1
      else t.n_subst <- t.n_subst + 1;
      emit t "%s" line

let flush_s t (c : con) =
  List.iter (ensure_s t) (List.rev c.pending);
  c.pending <- []

(* The baguette variables a literal form names (selectors and flags left out). *)
let key_of t lits =
  SM.fold
    (fun l _ acc ->
      match Hashtbl.find_opt t.owner (var_of l) with Some x -> x :: acc | None -> acc)
    lits []
  |> List.sort_uniq compare |> String.concat " "

(* cake's atoms: `i[X][ge<k>]`, `i[X][eq<k>]`, `n[K][ge<k>]`, `n[K][eq<k>]`. *)
let parse_atom v =
  let n = String.length v in
  if n < 7 || (v.[0] <> 'i' && v.[0] <> 'n') || v.[1] <> '[' || v.[n - 1] <> ']' then None
  else
    match String.index_from_opt v 2 ']' with
    | None -> None
    | Some j -> (
        let z = String.sub v 2 (j - 2) and rest = String.sub v (j + 1) (n - j - 1) in
        if String.length rest < 5 || rest.[0] <> '[' then None
        else
          let kind = String.sub rest 1 2 in
          match int_of_string_opt (String.sub rest 3 (String.length rest - 4)) with
          | Some k when kind = "ge" || kind = "eq" -> Some (v.[0] = 'i', z, kind, k)
          | _ -> None)

type aval =
  | T
  | F
  | L of string
  | Interior
  | Keep (* T7: a bits variable's: no literal *)

let atom_value t (isvar, z, kind, k) =
  if not isvar then
    let kk = int_of_string z in
    if (kind = "ge" && kk >= k) || (kind = "eq" && kk = k) then T else F
  else
    let x =
      match Hashtbl.find_opt t.cake_names z with
      | Some x -> x
      | None -> refuse "cake's atom over %s, which is no declared variable" z
    in
    let v = find_var t x in
    if v.bitw <> [] then
      if kind = "ge" then if k <= v.lo then T else if k > v.hi then F else Keep
      else if k < v.lo || k > v.hi then F
      else Keep
    else if kind = "ge" then if k <= v.lo then T else if k > v.hi then F else L (v.lit k)
    else if k < v.lo || k > v.hi then F
    else if v.lo = v.hi then T
    else if k = v.lo then L ("~" ^ v.lit (v.lo + 1))
    else if k = v.hi then L (v.lit v.hi)
    else Interior

(* Derive, once, the clause that states atom [g]'s value: "t" (g >= 1), "f" (~g >= 1),
   "p" (~g + M >= 1) or "n" (g + ~M >= 1), M its baguette literal. Returns its label. *)
let rec q_clause t g which =
  let lab = Printf.sprintf "@Q%s[%s]" which g in
  if not (Hashtbl.mem t.q lab) then (
    Hashtbl.replace t.q lab ();
    t.n_q <- t.n_q + 1;
    let ((isvar, z, kind, k) as a) =
      match parse_atom g with Some a -> a | None -> refuse "not an atom: %s" g
    in
    let value = atom_value t a in
    if kind = "ge" && isvar then
      let x = Hashtbl.find t.cake_names z in
      let v = find_var t x in
      match (which, value) with
      | "p", L m -> emit t "%s pol @%s[r] @A2[%s] + s ;" lab g m
      | "n", L m -> emit t "%s pol @%s[f] @A1[%s] + s ;" lab g m
      | "t", T ->
          let d = 1 - k + v.lo in
          emit t "%s pol @%s[f] @i[%s][lb] + s%s ;" lab g z
            (if d > 1 then Printf.sprintf " %d d" d else "")
      | "f", F ->
          let d = k - v.hi in
          emit t "%s pol @%s[r] @i[%s][ub] + s%s ;" lab g z
            (if d > 1 then Printf.sprintf " %d d" d else "")
      | _ -> refuse "atom %s has no clause %s" g which
    else if kind = "ge" then
      (* a constant's ge atom: its own rows are the units *)
      match (which, value) with
      | "t", T -> emit t "%s pol @%s[f] ;" lab g
      | "f", F -> emit t "%s pol @%s[r] ;" lab g
      | _ -> refuse "atom %s has no clause %s" g which
    else
      (* an eq atom e = [z = k] (T3b, D-0188): ONE pol of its own definition row and its
         two ge atoms' clauses, where D-0187 closed it by `rup` (on a Challenge instance of
         T4's Booleans, 75 302 of them). A clause with e positive ("t", "n") comes from
         [f], `e + ~ge_k + ge_(k+1) >= 1`, each ge atom replaced by its value or literal;
         one with ~e ("f", "p", and the interior "a", "b") from [r],
         `2 ~e + ge_k + ~ge_(k+1) >= 2`, a ge literal that is true or not wanted weakened
         away, then saturated. *)
      let ge kk = Printf.sprintf "%s[%s][ge%d]" (if isvar then "i" else "n") z kk in
      let gv kk = atom_value t (isvar, z, "ge", kk) in
      let b = Buffer.create 64 in
      let cite kk w = Printf.bprintf b " %s +" (q_clause t (ge kk) w)
      and weaken kk = Printf.bprintf b " %s w" (ge kk) in
      let bad () = refuse "atom %s has no clause %s" g which in
      (match (which, value) with
      | "t", T | "n", L _ -> (
          Printf.bprintf b "@%s[f]" g;
          (match gv k with T -> cite k "t" | L _ -> cite k "n" | _ -> bad ());
          match gv (k + 1) with
          | F -> cite (k + 1) "f"
          | L _ -> cite (k + 1) "p"
          | _ -> bad ())
      | "f", F | "p", L _ | "a", Interior | "b", Interior ->
          Printf.bprintf b "@%s[r]" g;
          (match gv k with
          | T -> weaken k
          | F -> cite k "f"
          | L _ when which = "b" -> weaken k
          | L _ -> cite k "p"
          | Interior | Keep -> bad ());
          (match gv (k + 1) with
          | F -> weaken (k + 1)
          | T -> cite (k + 1) "t"
          | L _ when which = "a" -> weaken (k + 1)
          | L _ -> cite (k + 1) "n"
          | Interior | Keep -> bad ());
          Buffer.add_string b " s"
      | _ -> bad ());
      emit t "%s pol %s ;" lab (Buffer.contents b));
  lab

(* T3b (D-0188 section 2): an INTERIOR eq atom e = [x = v], lo < v < hi, as the order
   indicator x_ge_v - x_ge_(v+1). Two clauses, each one `pol` of the atom's own definition
   row and its two ge atoms' clauses (the bridge's @Ep/@Em, D-0180, derived by `rup` there):

     @Ep[e]  e + ~x_ge_v + x_ge_(v+1) >= 1    = [f] + Qn(ge_v) + Qp(ge_(v+1))
     @Em[e]  ~e + x_ge_v + ~x_ge_(v+1) >= 2   = ([r] + Qp(ge_v) + Qn(ge_(v+1)) + @L) / 2

   In variable form they are e >= x_ge_v - x_ge_(v+1) and e <= x_ge_v - x_ge_(v+1), so a
   candidate's c * e is replaced exactly by adding c * @Em, and c * ~e by c * @Ep. *)
let indicator t g ~pos =
  let lab = Printf.sprintf "@E%s[%s]" (if pos then "p" else "m") g in
  if not (Hashtbl.mem t.q lab) then (
    Hashtbl.replace t.q lab ();
    t.n_q <- t.n_q + 1;
    let z, k =
      match parse_atom g with
      | Some (true, z, "eq", k) -> (z, k)
      | _ -> refuse "not an interior eq atom: %s" g
    in
    let v = find_var t (Hashtbl.find t.cake_names z) in
    let ge kk = Printf.sprintf "i[%s][ge%d]" z kk in
    if pos then
      emit t "%s pol @%s[f] %s + %s + ;" lab g
        (q_clause t (ge k) "n")
        (q_clause t (ge (k + 1)) "p")
    else
      emit t "%s pol @%s[r] %s + %s + @L[%s] + 2 d ;" lab g
        (q_clause t (ge k) "p")
        (q_clause t (ge (k + 1)) "n")
        (v.lit (k + 1)));
  lab

let to_var (cl, cd) =
  SM.fold
    (fun l c (m, d) ->
      if l.[0] = '~' then (SM.add (var_of l) (-c) m, d - c) else (SM.add l c m, d))
    cl (SM.empty, cd)

(* Replace every atom of a candidate that equals one baguette literal or a constant. *)
let swap_atoms t (rpn, (cl, cd)) =
  let b = Buffer.create 32 in
  Buffer.add_string b rpn;
  let row =
    SM.fold
      (fun l c row ->
        let g = var_of l and positive = var_of l = l in
        match parse_atom g with
        | None -> row
        | Some a -> (
            let clause cite lits d =
              Printf.bprintf b " %s %d * +" cite c;
              vadd row c (var_form lits d)
            in
            match (atom_value t a, positive) with
            | Keep, _ -> row
            | Interior, true ->
                let _, z, _, k = a in
                let v = find_var t (Hashtbl.find t.cake_names z) in
                clause (indicator t g ~pos:false)
                  [ (1, "~" ^ g); (1, v.lit k); (1, "~" ^ v.lit (k + 1)) ]
                  2
            | Interior, false ->
                let _, z, _, k = a in
                let v = find_var t (Hashtbl.find t.cake_names z) in
                clause (indicator t g ~pos:true)
                  [ (1, g); (1, "~" ^ v.lit k); (1, v.lit (k + 1)) ]
                  1
            | T, true -> clause ("~" ^ g) [ (1, "~" ^ g) ] 0
            | F, false -> clause g [ (1, g) ] 0
            | T, false -> clause (q_clause t g "t") [ (1, g) ] 1
            | F, true -> clause (q_clause t g "f") [ (1, "~" ^ g) ] 1
            | L m, true -> clause (q_clause t g "p") [ (1, "~" ^ g); (1, m) ] 1
            | L m, false -> clause (q_clause t g "n") [ (1, g); (1, neg_lit m) ] 1))
      cl
      (to_var (cl, cd))
  in
  (Buffer.contents b, lit_form row)

let is_flag t l =
  let v = var_of l in
  not (Hashtbl.mem t.owner v || Hashtbl.mem t.aux v || parse_atom v <> None)

(* ---------------------------------------------------------------------------
   T3b (D-0188 section 2): a cake row LINEARISED at a target clause [bl] (literal form).
   Each integer B_z of the row, net coefficient a, is cancelled by

     a > 0:  a * @A2[z_ge_w] when bl holds z_ge_w   (-B + K z_ge_w >= 1 - w), else
             a * @i[Z][ub]                           (-B >= -hi)
     a < 0: |a| * @A1[z_ge_w] when bl holds ~z_ge_w  (B + M ~z_ge_w >= w), else
            |a| * @i[Z][lb]                          (B >= lo)

   and what is left, the flags and those literals, is saturated, then cake's atoms are
   replaced by baguette's literals ([swap_atoms]). That is element's `[i = p] -> z >= w`:
   `@c[N][<p>le] + @A2[z_ge_w]`, saturated, is `~[i = 1 + p] + z_ge_w >= 1`, and the
   eq atom's @Ep turns `~[i = 1 + p]` into the index's two ladder literals. None when bl
   holds two literals of z of the polarity a needs, or when the result is trivial.
   --------------------------------------------------------------------------- *)
let linearise t (r : crow) bl =
  let per = Hashtbl.create 4 in
  List.iter
    (fun (k, x) ->
      Hashtbl.replace per x (Option.value (Hashtbl.find_opt per x) ~default:0 + k))
    r.ints;
  let lits_of x pos =
    SM.fold
      (fun l _ acc ->
        if Hashtbl.find_opt t.owner (var_of l) = Some x && l.[0] <> '~' = pos then
          l :: acc
        else acc)
      bl []
  in
  let step acc x =
    match acc with
    | None -> None
    | Some (rpn, terms, d) -> (
        let a = Hashtbl.find per x and v = find_var t x in
        if a = 0 then acc
        else if a > 0 then
          match lits_of x true with
          | [ l ] ->
              let w = Hashtbl.find t.value_of l in
              Some
                ( Printf.sprintf "%s @A2[%s] %d * +" rpn l a,
                  (mul a (ck (v.bmax - w + 1)), l) :: terms,
                  d + mul a (1 - w) )
          | [] ->
              Some
                (Printf.sprintf "%s @i[%s][ub] %d * +" rpn v.cx a, terms, d - mul a v.hi)
          | _ -> None
        else
          let a = -a in
          match lits_of x false with
          | [ l ] ->
              let p = var_of l in
              let w = Hashtbl.find t.value_of p in
              Some
                ( Printf.sprintf "%s @A1[%s] %d * +" rpn p a,
                  (mul a (ck (w - v.bmin)), l) :: terms,
                  d + mul a w )
          | [] ->
              Some
                (Printf.sprintf "%s @i[%s][lb] %d * +" rpn v.cx a, terms, d + mul a v.lo)
          | _ -> None)
  in
  match
    List.fold_left step
      (Some ("@" ^ r.label, [], r.deg))
      (List.sort_uniq compare (List.map snd r.ints))
  with
  | None -> None
  | Some (rpn, terms, d) ->
      let _, (cl, cd) = saturate (lit_form (var_form (r.flags @ terms) d)) in
      if cd < 1 then None
      else
        (* saturated at a degree d > 1 with every coefficient d, it is a clause divided by d *)
        let rpn, cl, cd =
          if cd > 1 && SM.for_all (fun _ a -> a = cd) cl then
            (Printf.sprintf "%s s %d d" rpn cd, SM.map (fun _ -> 1) cl, 1)
          else (rpn ^ " s", cl, cd)
        in
        let rpn, lf = swap_atoms t (rpn, (cl, cd)) in
        let sat, lf = saturate lf in
        Some ((if sat then rpn ^ " s" else rpn), lf)

(* The cake rows each family LINEARISES for a target clause, chosen from what the clause
   names; see [fam]. *)
let family name spec =
  let lab tag = Printf.sprintf "c[%s][%s]" name tag in
  let by_var pairs =
    let tbl = Hashtbl.create 16 in
    List.iter
      (fun (x, ls) ->
        match x with
        | Var x ->
            Hashtbl.replace tbl x (Option.value (Hashtbl.find_opt tbl x) ~default:[] @ ls)
        | Const _ -> ())
      pairs;
    By_var tbl
  in
  match spec with
  | Element (arr, Var x, z) ->
      if z = Var x then refuse "array_int_element whose result is its own index";
      Element_fam { idx = x; n = List.length arr }
  | Array_max (xs, _) | Array_min (xs, _) ->
      Choice_fam
        {
          choices = List.mapi (fun i _ -> Printf.sprintf "x[%s][%d][r]" name i) xs;
          al1 = lab "al1";
        }
  | Max _ | Min _ ->
      let c = match spec with Max _ -> "ge" | _ -> "le" in
      Choice_fam
        {
          choices =
            [
              Printf.sprintf "b[%s][l%s][r]" name c; Printf.sprintf "b[%s][r%s][r]" name c;
            ];
          al1 = lab "al1";
        }
  | Member (bxs, _) ->
      by_var
        (List.mapi
           (fun k (b, _) ->
             let nk = Printf.sprintf "%s_%d" name (k + 1) in
             (b, [ Printf.sprintf "c[%s][ge]" nk; Printf.sprintf "c[%s][le]" nk ]))
           bxs)
  | Inverse (f, _, g, _) ->
      let side s xs =
        List.mapi
          (fun k x ->
            ( x,
              [
                lab (Printf.sprintf "%s_%d_lb" s (k + 1));
                lab (Printf.sprintf "%s_%d_ub" s (k + 1));
              ] ))
          xs
      in
      by_var (side "X" f @ side "Y" g)
  | Abs _ -> Abs_fam
  | Regular (xs, _, _, _) ->
      Regular_fam (List.filter_map (function Var x -> Some x | Const _ -> None) xs)
  | _ -> Generic

(* T3b (D-0188 section 3.3): cake's gcc rows name a repeated variable x once per
   occurrence, so a candidate carries k times x's coefficient where baguette's row has x
   once and each of its k - 1 copies once. Each copy's share a / k of x_w's coefficient a
   is moved onto y_w by a / k times @Y2[y_w] (y_w - x_w >= 0), or |a / k| times @Y1[y_w]
   (x_w - y_w >= 0) for a negative share. *)
let split_copies t xs (rpn, lf) =
  let groups = Hashtbl.create 2 in
  List.iter
    (function
      | Var y when Hashtbl.mem t.copies y ->
          let o = Hashtbl.find t.copies y in
          Hashtbl.replace groups o
            (y :: Option.value (Hashtbl.find_opt groups o) ~default:[])
      | _ -> ())
    xs;
  if Hashtbl.length groups = 0 then (rpn, lf)
  else
    let b = Buffer.create 32 in
    Buffer.add_string b rpn;
    let row = ref (to_var lf) in
    Hashtbl.iter
      (fun o ys ->
        let k = 1 + List.length ys and v = find_var t o in
        for w = v.lo + 1 to v.hi do
          let xl = v.lit w in
          let a = Option.value (SM.find_opt xl (fst !row)) ~default:0 in
          if a <> 0 then (
            if a mod k <> 0 then
              refuse "a gcc candidate whose coefficient on %s is not split" xl;
            let share = a / k in
            List.iter
              (fun y ->
                let yl = (find_var t y).lit w in
                if share > 0 then (
                  Printf.bprintf b " @Y2[%s] %d * +" yl share;
                  row := vadd !row share (var_form [ (1, yl); (1, "~" ^ xl) ] 1))
                else (
                  Printf.bprintf b " @Y1[%s] %d * +" yl (-share);
                  row := vadd !row (-share) (var_form [ (1, "~" ^ yl); (1, xl) ] 1)))
              ys)
        done)
      groups;
    (Buffer.contents b, lit_form !row)

(* D-0262: cake's flag for each selector compile.ml mints for [spec], in minting order, so
   that a selector is defined by its POSITION and never guessed from the first candidate
   that happens to imply a row (a row a constant operand makes true, or weaker, implied by
   any candidate, used to define a selector as the wrong pair's flag). Each flag is the
   selector's value, positively:
   - array_int_maximum/minimum over a bits variable: one `$mxN` per operand in operand
     order (Maxmin.selector_rows, Encoding.add_choice); $mx_i = 1 picks operand i, cake's
     x[N][i] is x_i >= m (resp. <=); defined as F_i AND no earlier flag ([conj_of]);
   - int_max/int_min over bits: the same over cake's binary b[N][lge|rge] (b[N][lle|rle]);
   - all_different: one `$neN` per pair i < j that is not two distinct variables (a
     constant on either side, or a repeated variable), i then j (compile.ml's
     [post_all_different]); $ne = 1 iff x_i - x_j > 0 (Encoding.expand_int_lin_ne: the
     aux is 1 iff sum > rhs), and cake's x[N][i_j] is 1 iff x_i > x_j (its `gt`/`lt` rows) *)
let selector_flags name spec =
  match spec with
  | Array_max (xs, _) | Array_min (xs, _) ->
      List.mapi (fun i _ -> Printf.sprintf "x[%s][%d]" name i) xs
  | Max _ -> [ Printf.sprintf "b[%s][lge]" name; Printf.sprintf "b[%s][rge]" name ]
  | Min _ -> [ Printf.sprintf "b[%s][lle]" name; Printf.sprintf "b[%s][rle]" name ]
  | All_different xs ->
      let xa = Array.of_list xs in
      let n = Array.length xa in
      List.concat
        (List.init n (fun i ->
             List.filter_map
               (fun j ->
                 match (xa.(i), xa.(j)) with
                 | Var a, Var b when a <> b -> None
                 | _ -> Some (Printf.sprintf "x[%s][%d_%d]" name i j))
               (List.init (n - i - 1) (fun k -> i + 1 + k))))
  | _ -> []

let begin_con t ~name spec =
  let c =
    {
      cname = name;
      cands = Hashtbl.create 8;
      by_min = Hashtbl.create 8;
      aux_seen = Hashtbl.create 2;
      sel_flags = selector_flags name spec;
      rows = Hashtbl.create 16;
      fam = Generic;
      pending = [];
      ncands = 0;
      binary = Hashtbl.create 16;
    }
  in
  let crows = cake_rows t name spec in
  List.iter (fun (r : crow) -> Hashtbl.replace c.rows r.label r) crows;
  c.fam <- family name spec;
  (* the lists are kept NEWEST FIRST and reversed where read ([cands_of]): appending at the
     end was quadratic in a key's candidates, 7 000 per regular on 2021_pentominoes (T6) *)
  let push tbl k cand =
    Hashtbl.replace tbl k (cand :: Option.value (Hashtbl.find_opt tbl k) ~default:[])
  in
  let add ?(needs = []) rpn (cl, cd) =
    let cand =
      { rpn; plain = not (String.contains rpn ' '); cl; cd; key = key_of t cl; needs }
    in
    c.ncands <- c.ncands + 1;
    push c.cands cand.key cand;
    push c.by_min
      (match String.index_opt cand.key ' ' with
      | Some i -> String.sub cand.key 0 i
      | None -> cand.key)
      cand;
    cand
  in
  (* element's rows are all LINEARISED for the clause that cites them ([pin]); offering
     their substitutions too would cost a ladder-wide row each and is never cited *)
  let generic = match c.fam with Element_fam _ -> [] | _ -> crows in
  let base =
    List.map
      (fun r ->
        let cite, lf = substitute t r in
        let needs =
          if Hashtbl.mem t.pending_s cite then (
            c.pending <- cite :: c.pending;
            [ cite ])
          else []
        in
        let rl = swap_atoms t (cite, lf) in
        (needs, match spec with Gcc (xs, _, _) -> split_copies t xs rl | _ -> rl))
      generic
  in
  let cands = List.map (fun (needs, (rpn, lf)) -> add ~needs rpn lf) base in
  (* T6 (D-0195): cumulative. cake writes, per task i and time t of its window [lb s_i,
     ub s_i + d_i - 1] (cp_to_ilp_schedulingScript.sml, cencode_cumulative), flags cb
     (s_i <= t) and ca (s_i + d_i >= t + 1) by cbimply_var, act = cb /\ ca
     (`<i>_<t>_acta|b|cal1`), contribution bits equal to r_i under act (`<i>_<t>_cge`:
     r_i ~act + bits >= r_i), and `cap_<t>`: minus every covering task's bits >= -cap.
     baguette's row at t is ONE pol of them:
       cap_t + sum_i ( cge + r_i actc + r_i [cb's clause] + r_i [ca's clause] )
     cge cancels the bits (sum r_i ~act_i >= sum r_i - cap), actc turns ~act into
     ~cb + ~ca, and each flag's clause, one pol of its [f] row and the atom @A2 (cb) or @A1
     (ca) at its threshold, saturated, swaps it for baguette's literal, `cb \/ s_ge_(t+1)`
     and `ca \/ ~s_ge_(t+1-d)`; at a clipped end the bound row instead leaves the flag's
     unit. One candidate per time point; the generic pin finds it by its variables. *)
  (match spec with
  | Cumulative (ss, ds, rs, cap) ->
      if List.length ds <> List.length ss || List.length rs <> List.length ss then
        refuse "cumulative with %d starts, %d durations, %d resources" (List.length ss)
          (List.length ds) (List.length rs);
      let tasks = List.combine ss (List.combine ds rs) in
      let window (st, (d, _)) =
        match st with
        | Var x ->
            let v = find_var t x in
            (v.lo, v.hi + d - 1)
        | Const c0 -> (c0, c0 + d - 1)
      in
      let times =
        List.sort_uniq compare
          (List.concat_map
             (fun task ->
               let lo, hi = window task in
               if hi < lo then [] else List.init (hi - lo + 1) (fun k -> lo + k))
             tasks)
      in
      let pending lab line =
        if not (Hashtbl.mem t.pending_s lab || Hashtbl.mem t.q lab) then (
          Hashtbl.replace t.q lab ();
          Hashtbl.replace t.pending_s lab line;
          c.pending <- lab :: c.pending);
        lab
      in
      let div k = if k > 1 then Printf.sprintf " %d d" k else "" in
      List.iter
        (fun tm ->
          let acc = ref (SM.empty, -cap) and needs = ref [] and any = ref false in
          let rpn = Buffer.create 128 in
          Printf.bprintf rpn "@c[%s][cap_%d]" name tm;
          List.iteri
            (fun i ((st, (d, r)) as task) ->
              let lo, hi = window task in
              if r > 0 && lo <= tm && tm <= hi then (
                any := true;
                let pre = Printf.sprintf "%d_%d" i tm in
                let fl w = Printf.sprintf "v[%s][%s][%s]" name pre w in
                let act = fl "cact" and cb = fl "cb" and ca = fl "ca" in
                acc := vadd !acc 1 (var_form [ (r, "~" ^ act) ] r);
                Printf.bprintf rpn " @c[%s][%s_cge] +" name pre;
                acc := vadd !acc r (var_form [ (1, act); (1, "~" ^ cb); (1, "~" ^ ca) ] 1);
                Printf.bprintf rpn " @c[%s][%s_actcal1] %d * +" name pre r;
                let clause f line lits =
                  let lab =
                    pending ("@K[" ^ f ^ "]") (Printf.sprintf "@K[%s] pol %s ;" f line)
                  in
                  needs := lab :: !needs;
                  acc := vadd !acc r (var_form lits 1);
                  Printf.bprintf rpn " %s %d * +" lab r
                in
                match st with
                | Var x ->
                    let v = find_var t x in
                    if tm + 1 <= v.hi then
                      clause cb
                        (Printf.sprintf "@%s[f] @A2[%s] + s" cb (v.lit (tm + 1)))
                        [ (1, cb); (1, v.lit (tm + 1)) ]
                    else
                      clause cb
                        (Printf.sprintf "@%s[f] @i[%s][ub] + s%s" cb v.cx
                           (div (tm + 1 - v.hi)))
                        [ (1, cb) ];
                    let w = tm + 1 - d in
                    if w <= v.lo then
                      clause ca
                        (Printf.sprintf "@%s[f] @i[%s][lb] + s%s" ca v.cx
                           (div (v.lo - w + 1)))
                        [ (1, ca) ]
                    else if w > v.hi then refuse "cumulative's window beyond %s's range" x
                    else
                      clause ca
                        (Printf.sprintf "@%s[f] @A1[%s] + s" ca (v.lit w))
                        [ (1, ca); (1, "~" ^ v.lit w) ]
                | Const c0 ->
                    clause cb
                      (Printf.sprintf "@%s[f]%s" cb (div (1 + tm - c0)))
                      [ (1, cb) ];
                    clause ca
                      (Printf.sprintf "@%s[f]%s" ca (div (c0 + d - tm)))
                      [ (1, ca) ]))
            tasks;
          let cl, cd = lit_form !acc in
          if !any && SM.for_all (fun l _ -> Hashtbl.mem t.owner (var_of l)) cl then
            ignore (add ~needs:(List.rev !needs) (Buffer.contents rpn) (cl, cd)))
        times
  | _ -> ());
  (* a copy's int_eq: its two rows are the sums of the copy's @Y1, resp. @Y2 *)
  (match spec with
  | Copy (o, y) ->
      let v = find_var t o and vy = find_var t y in
      let ws = List.init (v.hi - v.lo) (fun i -> v.lo + 1 + i) in
      List.iter
        (fun (tag, terms) ->
          if ws <> [] then
            let rpn =
              String.concat " "
                (List.mapi
                   (fun i w ->
                     Printf.sprintf "@%s[%s]%s" tag (vy.lit w)
                       (if i > 0 then " +" else ""))
                   ws)
            in
            ignore
              (add rpn (lit_form (var_form (List.concat_map terms ws) (List.length ws)))))
        [
          ("Y1", fun w -> [ (1, "~" ^ vy.lit w); (1, v.lit w) ]);
          ("Y2", fun w -> [ (1, vy.lit w); (1, "~" ^ v.lit w) ]);
        ]
  | _ -> ());
  (* T4: resolve each candidate once against a FLAG CLAUSE of this constraint (a clause
     with a flag), on a flag the candidate has with the other polarity *)
  let clauses =
    List.filter
      (fun k ->
        k.cd = 1
        && SM.for_all (fun _ a -> a = 1) k.cl
        && SM.exists (fun l _ -> is_flag t l) k.cl)
      cands
  in
  List.iter
    (fun cand ->
      SM.iter
        (fun l a ->
          if is_flag t l then
            List.iter
              (fun k ->
                if k != cand && SM.mem (neg_lit l) k.cl then
                  ignore
                    (add ~needs:(cand.needs @ k.needs)
                       (Printf.sprintf "%s %s %d * +" cand.rpn k.rpn a)
                       (lit_form
                          (vadd (to_var (cand.cl, cand.cd)) a (to_var (k.cl, k.cd))))))
              clauses)
        cand.cl)
    cands;
  t.cur <- Some c

let end_con t =
  (match t.cur with
  | Some c -> List.iter (Hashtbl.remove t.pending_s) c.pending
  | None -> ());
  t.cur <- None

(* ---------------------------------------------------------------------------
   Pins
   --------------------------------------------------------------------------- *)

(* a candidate table's list for a key, in insertion order ([begin_con] keeps it reversed) *)
let cands_of tbl k = List.rev (Option.value (Hashtbl.find_opt tbl k) ~default:[])

let lits_of_row (c : Opb.constr) =
  lit_form
    (var_form (List.map (fun (a, l) -> (a, Lit.to_string l)) (Opb.terms c)) (Opb.rhs c))

(* Swap every flag of [cand] that is a defined selector's flag. [try_def] is a selector
   of this row not defined yet, and an orientation to try for it against the first
   undefined flag met. Returns the swapped literal form, the rpn of the swaps, and the
   definition made (if any). *)
let swap t (cl, cd) ~try_def =
  let made = ref None in
  let rpn = Buffer.create 32 in
  let cl =
    SM.fold
      (fun l c acc ->
        if not (is_flag t l || Hashtbl.mem t.sel_of_flag (var_of l)) then
          SM.update l (fun o -> Some (Option.value o ~default:0 + c)) acc
        else
          let f = var_of l and positive = var_of l = l in
          let def =
            match Hashtbl.find_opt t.sel_of_flag f with
            | Some d -> Some d
            | None -> (
                match (try_def, !made) with
                | Some (s, p), None ->
                    made := Some (s, f, p);
                    Some (s, p)
                | _ -> None)
          in
          match def with
          | None -> SM.update l (fun o -> Some (Option.value o ~default:0 + c)) acc
          | Some (s, _) when Hashtbl.mem t.conj s && positive ->
              (* T7: a choice selector defined as F_i AND no earlier flag: F_i -> s does
                 not hold, only ~F_i -> ~s (@D1) *)
              SM.update l (fun o -> Some (Option.value o ~default:0 + c)) acc
          | Some (s, p) ->
              (* s <-> f when p, s <-> ~f otherwise; the literal m equal to l *)
              let m = if positive = p then s else "~" ^ s in
              let cl_lab = if m = s then "@D2[" ^ s ^ "]" else "@D1[" ^ s ^ "]" in
              Printf.bprintf rpn " %s %d * +" cl_lab c;
              SM.update m (fun o -> Some (Option.value o ~default:0 + c)) acc)
      cl SM.empty
  in
  (* a literal and its negation both present: cancel (does not arise in the covered
     families, where s is fresh and f appears once; refused rather than mis-stated) *)
  SM.iter
    (fun l _ ->
      if SM.mem (neg_lit l) cl then refuse "a candidate with both %s and its negation" l)
    cl;
  ((cl, cd), Buffer.contents rpn, !made)

(* T7 (D-0196): a choice-group selector `_mxN` (array_int_maximum/minimum over a bits
   variable, D-0134) is set by `sol` to the FIRST operand attaining m and no other
   ([Maxmin.chosen]); cake's array_max flag i is x_i >= m both ways (`[f]`, `[r]`), so at a
   tie two flags hold, and s := F_i would contradict the `sol`. It is defined as F_i AND
   no earlier flag of the same constraint:

     @C1[s]  red (i+1) ~s + F_i + sum_{j<i} ~F_j >= i+1 : s -> 0
     @C2[s]  red s + ~F_i + sum_{j<i} F_j >= 1         : s -> 1
     @D1[s]  pol @C1[s], the earlier flags weakened, saturated:  ~s + F_i >= 1

   so ~F_i is still swapped for ~s ([swap]); the at-least-one over the selectors closes by
   rup through the @C2 and cake's al1. The earlier flags, or None for a renaming. *)
let conj_of t s f =
  let n = String.length s in
  let is_mx = n > 3 && String.sub s 0 3 = "_mx" in
  match t.cur with
  | Some ({ fam = Choice_fam { choices; _ }; _ } as con) when is_mx -> (
      let flag i = Printf.sprintf "x[%s][%d]" con.cname i in
      let flags = List.mapi (fun i _ -> flag i) choices in
      let rec earlier acc = function
        | [] -> None
        | g :: rest -> if g = f then Some (List.rev acc) else earlier (g :: acc) rest
      in
      match earlier [] flags with Some (_ :: _ as e) -> Some e | _ -> None)
  | _ -> None

let define t (s, f, p) =
  Hashtbl.replace t.sel s (f, p);
  Hashtbl.replace t.sel_of_flag f (s, p);
  t.n_sel <- t.n_sel + 1;
  let fl = if p then f else "~" ^ f in
  match if p then conj_of t s f else None with
  | Some e ->
      Hashtbl.replace t.conj s e;
      let k = List.length e in
      let terms pre =
        String.concat "" (List.map (fun g -> Printf.sprintf " +1 %s%s" pre g) e)
      in
      emit t "@C1[%s] red +%d ~%s +1 %s%s >= %d : %s -> 0 ;" s (k + 1) s f (terms "~")
        (k + 1) s;
      emit t "@C2[%s] red +1 %s +1 ~%s%s >= 1 : %s -> 1 ;" s s f (terms "") s;
      emit t "@D1[%s] pol @C1[%s]%s s ;" s s
        (String.concat "" (List.map (fun g -> " " ^ g ^ " w") e))
  | None ->
      emit t "@D1[%s] red +1 ~%s +1 %s >= 1 : %s -> %s ;" s s fl s fl;
      emit t "@D2[%s] red +1 %s +1 %s >= 1 : %s -> %s ;" s s (neg_lit fl) s fl

let is_clause (bl, bd) = bd = 1 && SM.for_all (fun _ a -> a = 1) bl

(* T3b: a candidate's literal l the target lacks, RESOLVED against a binary clause of the
   same constraint already pinned, `~l + m` with m in the target: adding it a times (a the
   candidate's coefficient on l) replaces l by m. member's big-M row over the overlap
   needs it where the candidate runs past the overlap, as D-0180's bridge found (its @R
   rows, a `rup` each; here they are baguette's own pinned rows, cited). *)
let resolve (con : con) (cl, cd) bl =
  let b = Buffer.create 16 in
  let row =
    SM.fold
      (fun l a row ->
        if SM.mem l bl then row
        else
          match
            List.find_opt
              (fun (_, m) -> SM.mem m bl)
              (Hashtbl.find_all con.binary (neg_lit l))
          with
          | Some (id, m) ->
              Printf.bprintf b " @c%d %d * +" id a;
              vadd row a (to_var (SM.add (neg_lit l) 1 (SM.singleton m 1), 1))
          | None -> row)
      cl
      (to_var (cl, cd))
  in
  if Buffer.length b = 0 then None
  else
    let sat, lf = saturate (lit_form row) in
    Some ((Buffer.contents b ^ if sat then " s" else ""), lf)

(* The family's own derivation of a clause row (D-0188 section 2), as the rpn of one `pol`
   whose result implies it syntactically, and whether that result IS the row (then the
   `pol` is the pin itself, with no `ia`), or None. *)
let special t (con : con) bl =
  let exact (cl, cd) = cd = 1 && SM.equal ( = ) cl bl in
  let lin labels =
    List.find_map
      (fun lab ->
        match Hashtbl.find_opt con.rows lab with
        | None -> None
        | Some r -> (
            match linearise t r bl with
            | Some (rpn, lf) -> (
                match implied_or_weakened lf (bl, 1) with
                | Some "" -> Some (rpn, exact lf)
                | Some wk -> Some (rpn ^ wk, false)
                | None -> None)
            | None -> None))
      labels
  in
  match con.fam with
  | Generic | Abs_fam | Regular_fam _ -> None
  | Element_fam { idx; n } -> (
      (* the guard is `x <> bp` over the index's ladder (Encoding.ne_clause): read bp *)
      let v = find_var t idx in
      let il =
        SM.fold
          (fun l _ acc ->
            if Hashtbl.find_opt t.owner (var_of l) = Some idx then l :: acc else acc)
          bl []
      in
      let value l = Hashtbl.find t.value_of (var_of l) in
      let bp =
        match il with
        | [] when v.lo = v.hi -> Some v.lo
        | [ l ] when l.[0] <> '~' && value l = v.lo + 1 -> Some v.lo
        | [ l ] when l.[0] = '~' && value l = v.hi -> Some v.hi
        | [ a; b ] ->
            let ng, ps = if a.[0] = '~' then (a, b) else (b, a) in
            if ng.[0] = '~' && ps.[0] <> '~' && value ps = value ng + 1 then
              Some (value ng)
            else None
        | _ -> None
      in
      match bp with
      | None -> None
      | Some bp ->
          let p = bp - 1 in
          let lab tag = Printf.sprintf "c[%s][%s]" con.cname tag in
          lin
            (if p >= 0 && p < n then
               [ lab (Printf.sprintf "%dle" p); lab (Printf.sprintf "%dge" p) ]
             else [ lab "lb"; lab "ub" ]))
  | By_var tbl ->
      lin
        (SM.fold
           (fun l _ acc ->
             match Hashtbl.find_opt t.owner (var_of l) with
             | Some x -> acc @ Option.value (Hashtbl.find_opt tbl x) ~default:[]
             | None -> acc)
           bl [])
  | Choice_fam { choices; al1 } -> (
      (* maxmin's `m >= v -> OR x_i >= v`: every operand's choice row linearised at the
         clause, each leaving `~f_i + ...`, summed with the at-least-one over the flags *)
      let parts =
        List.map
          (fun lab ->
            Option.bind (Hashtbl.find_opt con.rows lab) (fun r -> linearise t r bl))
          choices
      in
      if List.exists Option.is_none parts then None
      else
        let parts = List.map Option.get parts in
        let sum =
          List.fold_left (fun acc (_, lf) -> vadd acc 1 (to_var lf)) (SM.empty, 0) parts
        in
        match Hashtbl.find_opt con.rows al1 with
        | None -> None
        | Some a ->
            let sum = vadd sum 1 (var_form a.flags a.deg) in
            let _, lf = saturate (lit_form sum) in
            if not (implies lf (bl, 1)) then None
            else
              let rpns = List.map fst parts in
              Some
                ( Printf.sprintf "%s %s @%s + s" (List.hd rpns)
                    (String.concat " " (List.map (fun r -> r ^ " +") (List.tl rpns)))
                    al1,
                  exact lf ))

(* T7 (D-0196): a guarded row over a bits variable whose big-M is baguette's own, over the
   declared bounds, where cake's candidate's is over the bit range (`bits_imply`): on the
   ladder the two agree after saturation, on bits they do not (`x + 17 ~b >= 2` against
   `x + 11 ~s >= 17` in literal form for `var 0..9`), and no weakening reaches it. By
   contradiction, as int_abs's rows (D-0195 2.3): the negation plus the candidate,
   saturated, is a clause over the guards; the negation plus each NEGATED bits variable's
   ub row (@BU, `-S >= -(u - l)`, a times for a coefficient a 2^i on ~x_bit_i) leaves them
   no room; unit propagation closes. Simulated here (what one sum forces leaves the other no
   room), so that it is tried only where it closes. The rpn of the second sum, or None. *)
let tight t (cl, cd) (bl, bd) =
  let neg_t =
    ( SM.fold (fun l a acc -> SM.add (neg_lit l) a acc) bl SM.empty,
      SM.fold (fun _ a acc -> acc + a) bl 0 - bd + 1 )
  in
  let add rows =
    lit_form
      (List.fold_left (fun acc (k, lf) -> vadd acc k (to_var lf)) (SM.empty, 0) rows)
  in
  let r1l, r1d = add [ (1, neg_t); (1, (cl, cd)) ] in
  if r1d < 1 then None
  else
    let r1l = SM.map (fun a -> min a r1d) r1l in
    let ubs =
      Hashtbl.fold
        (fun x v acc ->
          match v.bitw with
          | (_, b0) :: _ -> (
              match SM.find_opt ("~" ^ b0) bl with
              | Some a ->
                  if
                    List.for_all
                      (fun (w, b) -> SM.find_opt ("~" ^ b) bl = Some (a * w))
                      v.bitw
                  then Some (x, v, a) :: acc
                  else None :: acc
              | None -> acc)
          | [] -> acc)
        t.vars []
    in
    if ubs = [] || List.mem None ubs then None
    else
      let ubs = List.sort compare (List.filter_map Fun.id ubs) in
      let r2l, r2d =
        add
          ((1, neg_t)
          :: List.map
               (fun (_, v, a) ->
                 ( a,
                   lit_form
                     ( List.fold_left (fun m (w, b) -> SM.add b (-w) m) SM.empty v.bitw,
                       v.lo - v.hi ) ))
               ubs)
      in
      let forced (ls, d) =
        let tot = SM.fold (fun _ a acc -> acc + a) ls 0 in
        SM.filter (fun _ a -> tot - a < d) ls
      in
      let room ls f =
        SM.fold (fun l a acc -> if SM.mem (neg_lit l) f then acc else acc + a) ls 0
      in
      if room r2l (forced (r1l, r1d)) < r2d || room r1l (forced (r2l, r2d)) < r1d then
        Some
          (String.concat " "
             (List.mapi
                (fun i (x, _, a) ->
                  Printf.sprintf "@BU[%s]%s%s" (Lit.sanitize x)
                    (if a > 1 then Printf.sprintf " %d *" a else "")
                    (if i > 0 then " +" else ""))
                ubs))
      else None

let pin t ~id (c : Opb.constr) =
  let body = Opb.constr_body c in
  let bl, bd = lits_of_row c in
  (* D-0262: a choice selector is defined by its position, before any derivation that may
     cite it; guessing it from a candidate's first undefined flag left a constant operand's
     selector undefined (its row is implied without it, by [special]) *)
  SM.iter
    (fun l _ ->
      let s = var_of l in
      if not (Hashtbl.mem t.sel s) then
        Option.iter (fun f -> define t (s, f, true)) (Hashtbl.find_opt t.pos_flag s))
    bl;
  let rung =
    if t.cur <> None then None
    else
      match SM.bindings bl with
      | [ (l1, 1); (l2, 1) ] when bd = 1 -> (
          (* ~x_ge_(v+1) + x_ge_v, a rung; ~x_ge_h + x_ge_(h+1), a hole *)
          let n, p = if l1.[0] = '~' then (var_of l1, l2) else (var_of l2, l1) in
          match (Hashtbl.find_opt t.owner n, Hashtbl.find_opt t.owner p) with
          | Some x, Some y when x = y && p.[0] <> '~' -> (
              match (Hashtbl.find_opt t.value_of n, Hashtbl.find_opt t.value_of p) with
              | Some a, Some b when a = b + 1 -> Some (`Rung n)
              | Some a, Some b when b = a + 1 -> Some (`Hole x)
              | _ -> None)
          | _ -> None)
      | _ -> None
  in
  let memo = ref None in
  let sp con =
    match !memo with
    | Some r -> r
    | None ->
        let r = special t con bl in
        memo := Some r;
        r
  in
  match (rung, t.cur) with
  | _ when not (Queue.is_empty t.bound_q) ->
      (* T7: a bits variable's bound row, against @BL / @BU *)
      t.n_ia_exact <- t.n_ia_exact + 1;
      emit t "@c%d ia %s : %s ;" id body (Queue.pop t.bound_q)
  | Some (`Rung hi), _ ->
      t.n_ia_rung <- t.n_ia_rung + 1;
      emit t "@c%d ia %s : @L[%s] ;" id body hi
  | Some (`Hole x), _ when Hashtbl.mem t.copies x ->
      (* a copy's hole: its original's hole clause and the two red pairs, by propagation *)
      t.n_rup <- t.n_rup + 1;
      emit t "@c%d rup %s ;" id body
  | Some (`Hole x), _ when Hashtbl.mem t.holes x ->
      (* the clause x <> h: every allowed value's eq atom implies its ladder literals, then
         cake's `@c[d<k>][al1]` has no true literal left under x = h *)
      let _, allowed = Hashtbl.find t.holes x in
      let v = find_var t x in
      List.iter
        (fun w ->
          let g = Printf.sprintf "i[%s][eq%d]" v.cx w in
          if w = v.lo || w = v.hi then ignore (q_clause t g "p")
          else (
            ignore (q_clause t g "a");
            ignore (q_clause t g "b")))
        allowed;
      t.n_rup <- t.n_rup + 1;
      emit t "@c%d rup %s ;" id body
  | _, None -> refuse "row @c%d (%s) belongs to no covered constraint" id body
  | _, Some con when is_clause (bl, bd) && sp con <> None -> (
      match Option.get (sp con) with
      | rpn, true ->
          (* the pol's result is the row itself: it is the pin, under the row's label *)
          t.n_pol_lin <- t.n_pol_lin + 1;
          emit t "@c%d pol %s ;" id rpn
      | rpn, false ->
          t.nw <- t.nw + 1;
          t.n_ia_w <- t.n_ia_w + 1;
          t.n_ia_lin <- t.n_ia_lin + 1;
          emit t "@W[%d] pol %s ;" t.nw rpn;
          emit t "@c%d ia %s : @W[%d] ;" id body t.nw;
          emit t "del id @W[%d] ;" t.nw)
  | _, Some con -> (
      let undefined =
        SM.fold
          (fun l _ acc ->
            let v = var_of l in
            if Hashtbl.mem t.aux v && not (Hashtbl.mem t.sel v) then v :: acc else acc)
          bl []
      in
      let tries =
        match undefined with
        | [] -> [ None ]
        | s :: _ -> [ Some (s, true); Some (s, false) ]
      in
      (* the candidates over exactly this row's variables, then, if none serves and the
         row has a selector or no such candidate exists, those over a SUBSET of them (a
         guard the candidate lacks is a literal the row may add: int_eq_reif's `gt` half,
         D-0178) *)
      let key = key_of t bl in
      let exact = cands_of con.cands key in
      let subset () =
        let vs = if key = "" then [] else String.split_on_char ' ' key in
        let inside k =
          k = "" || List.for_all (fun v -> List.mem v vs) (String.split_on_char ' ' k)
        in
        List.concat_map
          (fun v ->
            List.filter (fun cd -> cd.key <> key && inside cd.key) (cands_of con.by_min v))
          ("" :: vs)
      in
      (* [relaxed] (T3b): a candidate weakened, or resolved against the constraint's own
         binary clauses, then weakened; tried only after every candidate failed strictly,
         and only for a row with no selector to define (a weakening could drop the very
         literal a selector's orientation is chosen by) *)
      let tw = ref None in
      let rec go ~mode = function
        | [] -> None
        | cand :: rest ->
            let relaxed = mode = `Relaxed in
            let rec over = function
              | [] -> go ~mode rest
              | try_def :: more -> (
                  let (sl, sd), rpn, made = swap t (cand.cl, cand.cd) ~try_def in
                  let sat, (sl, sd) = saturate (sl, sd) in
                  if mode = `Tight then
                    match tight t (sl, sd) (bl, bd) with
                    | Some w ->
                        tw := Some w;
                        Some (cand, rpn, sat, made)
                    | None -> over more
                  else if not relaxed then
                    if implies (sl, sd) (bl, bd) then Some (cand, rpn, sat, made)
                    else over more
                  else
                    let rpn = rpn ^ if sat then " s" else "" in
                    match implied_or_weakened (sl, sd) (bl, bd) with
                    | Some wk -> Some (cand, rpn ^ wk, false, made)
                    | None -> (
                        match resolve con (sl, sd) bl with
                        | Some (rr, lf) -> (
                            match implied_or_weakened lf (bl, bd) with
                            | Some wk -> Some (cand, rpn ^ rr ^ wk, false, made)
                            | None -> over more)
                        | None -> over more))
            in
            over tries
      in
      (* relaxed, a constraint with few candidates: those over a SUPERSET of the row's
         variables, whose extra literals the weakening drops (array_bool_and's `~r \/ x_i`
         from cake's `pos` row: 155 554 such constraints and 327 836 `rup` pins on
         steiner_t3_k3_N11, D-0188 section 6) *)
      let superset () =
        if con.ncands > 8 then []
        else
          let vs = if key = "" then [] else String.split_on_char ' ' key in
          Hashtbl.fold
            (fun k l acc ->
              let ks = String.split_on_char ' ' k in
              if k <> key && List.for_all (fun v -> List.mem v ks) vs then
                List.rev_append l acc
              else acc)
            con.cands []
      in
      let search ~mode =
        match go ~mode exact with
        | Some r -> Some r
        | None -> (
            match
              if
                exact = []
                || SM.exists (fun l _ -> Hashtbl.mem t.aux (var_of l)) bl
                || mode = `Tight
              then go ~mode (subset ())
              else None
            with
            | Some r -> Some r
            | None when mode = `Relaxed -> go ~mode (superset ())
            | None -> None)
      in
      (* T7 (D-0196): a row over a bits variable no candidate implies: by contradiction
         against the bits' ub rows ([tight]), before `rup` *)
      let bits_row =
        SM.exists
          (fun l _ ->
            match Hashtbl.find_opt t.owner (var_of l) with
            | Some x -> (find_var t x).bitw <> []
            | None -> false)
          bl
      in
      (* T6 (D-0195): a regular row no candidate implies strictly is a forward clause over
         a symbol run, which weakening never reaches (its literals are the run's bounds,
         cake's are one value's eq atom): straight to `rup`. The relaxed search tried ~560
         candidates per such row on 2021_pentominoes (116 s of --e2e against 0.08 s) *)
      let relax_ok = match con.fam with Regular_fam _ -> false | _ -> true in
      let found =
        match search ~mode:`Strict with
        | Some r -> Some r
        | None -> (
            match if undefined = [] && relax_ok then search ~mode:`Relaxed else None with
            | Some r -> Some r
            | None -> if bits_row then search ~mode:`Tight else None)
      in
      Option.iter (fun (cand, _, _, _) -> List.iter (ensure_s t) cand.needs) found;
      match found with
      | Some (cand, rpn, sat, made) when !tw <> None ->
          Option.iter (define t) made;
          t.n_tight <- t.n_tight + 1;
          emit t "@c%d pbc %s : subproof" id body;
          emit t "    pol -1 %s%s%s + s ;" cand.rpn rpn (if sat then " s" else "");
          emit t "    pol -2 %s + ;" (Option.get !tw);
          emit t "    rup >= 1 ;";
          emit t "qed ;"
      | Some (cand, "", false, None) when cand.plain ->
          t.n_ia_exact <- t.n_ia_exact + 1;
          emit t "@c%d ia %s : %s ;" id body cand.rpn
      | Some (cand, rpn, sat, made) ->
          Option.iter (define t) made;
          t.nw <- t.nw + 1;
          t.n_ia_w <- t.n_ia_w + 1;
          emit t "@W[%d] pol %s%s%s ;" t.nw cand.rpn rpn (if sat then " s" else "");
          emit t "@c%d ia %s : @W[%d] ;" id body t.nw;
          emit t "del id @W[%d] ;" t.nw
      | None
        when (match con.fam with Abs_fam -> true | _ -> false)
             && not (is_clause (bl, bd)) ->
          (* T6 (D-0195 2.3): a row that holds in both signs of int_abs (z >= x, z >= -x,
             the hull, the guard's own rows) is implied by no single cake row, and cutting
             planes cannot resolve two big-M rows on their guard. By contradiction: the
             negation plus each candidate, saturated, is a unit on the guard (or nothing),
             and unit propagation closes. *)
          let all = Hashtbl.fold (fun _ l acc -> List.rev_append l acc) con.cands [] in
          let all = List.sort (fun a b -> compare a.rpn b.rpn) all in
          List.iter (fun cd -> List.iter (ensure_s t) cd.needs) all;
          t.n_pbc <- t.n_pbc + 1;
          emit t "@c%d pbc %s : subproof" id body;
          List.iteri (fun k cd -> emit t "    pol -%d %s + s ;" (k + 1) cd.rpn) all;
          emit t "    rup >= 1 ;";
          emit t "qed ;"
      | None ->
          (* T6 (D-0195): regular's forward clause over a symbol run is unit propagation
             through cake's transition clauses and the letter's eq atoms, read as ladder
             literals: each value's clause `[x = v] \/ ~x_ge_v \/ x_ge_(v+1)` first *)
          (match con.fam with
          | Regular_fam letters ->
              SM.iter
                (fun l _ ->
                  match Hashtbl.find_opt t.owner (var_of l) with
                  | Some x when List.mem x letters ->
                      let v = find_var t x in
                      if v.lo < v.hi then
                        for w = v.lo to v.hi do
                          let g = Printf.sprintf "i[%s][eq%d]" v.cx w in
                          if w = v.lo || w = v.hi then ignore (q_clause t g "n")
                          else ignore (indicator t g ~pos:true)
                        done
                  | _ -> ())
                bl
          | _ -> ());
          (* unit propagation may need any of this constraint's substitutions *)
          flush_s t con;
          t.n_rup <- t.n_rup + 1;
          emit t "@c%d rup %s ;" id body)

(* member's and inverse's binary clauses, recorded once pinned (for [resolve]) *)
let row t ~id c =
  pin t ~id c;
  match t.cur with
  | Some ({ fam = By_var _; _ } as con) -> (
      match lits_of_row c with
      | bl, 1 when SM.cardinal bl = 2 && SM.for_all (fun _ a -> a = 1) bl -> (
          match SM.bindings bl with
          | [ (a, _); (b, _) ] ->
              Hashtbl.add con.binary a (id, b);
              Hashtbl.add con.binary b (id, a)
          | _ -> ())
      | _ -> ())
  | _ -> ()

(* ---------------------------------------------------------------------------
   The objective (T8, D-0182): cake writes `min: k * B` (k = 1 minimise, -1 maximise),
   baguette `min: k * S + k * l`. VeriPB's `soli` adds `k * B <= v - 1` over cake's bits,
   and baguette's later lines want `k * S + k * l <= v - 1`: the improving line is
   labelled @O[cN] and @cN derived from it by the half, as the bridge did.
   --------------------------------------------------------------------------- *)

let objective t x ~sign =
  ignore (find_var t x);
  t.objective <- Some (x, sign)

let soli_tail t =
  match t.objective with
  | None -> None
  | Some (x, k) ->
      let v = find_var t x in
      let half = if k > 0 then v.e1 else v.e2 in
      Some (fun id -> Printf.sprintf "@c%d pol @O[c%d] %s 1 * + ;" id id half)

(* The prefix is complete: close the file and return its path. *)
let finish t =
  if not t.finished then (
    t.finished <- true;
    emit t
      "%% e2e prefix (D-0187, contract cake_pb_cp %s): %d substitutions, %d atom \
       clauses, %d selectors, pins: %d rungs ia, %d rows ia exact, %d rows ia through a \
       pol, %d rows rup; T3b (D-0188): %d rows by one pol of a linearised cake row, %d \
       rows ia through one; T6 (D-0195): %d rows by contradiction, %d cumulative flag \
       clauses; T7 (D-0196): %d bits variables, %d rows by contradiction against their \
       ub rows"
      cake_pb_cp_sha256 t.n_subst t.n_q t.n_sel t.n_ia_rung t.n_ia_exact t.n_ia_w t.n_rup
      t.n_pol_lin t.n_ia_lin t.n_pbc t.n_k t.n_bits t.n_tight;
    Buffer.output_buffer t.oc t.b;
    Buffer.clear t.b;
    close_out t.oc);
  t.path

let stats t = (t.n_subst, t.n_q, t.n_sel, t.n_ia_rung, t.n_ia_exact, t.n_ia_w, t.n_rup)
