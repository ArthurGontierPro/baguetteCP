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
   k < 0 (@S[...]). And each of baguette's rows posted for that constraint is pinned:

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
   What is covered
   ---------------------------------------------------------------------------

   The families of T2 (D-0176): int_lin_le, int_lin_eq, int_lin_ne, int_le, int_lt,
   int_eq, int_ne, all_different_int; and of T4 (D-0178): bool_clause, array_bool_or,
   array_bool_and, bool_eq, bool_not, bool2int, int_le_reif, int_eq_reif, int_ne_reif,
   int_lin_le_reif; over `var lo..hi` and `var bool`, with or without an objective.
   Everything else raises [Not_covered] with the construct's name, before the search:
   the caller refuses `--e2e` and says why. In particular a set domain with holes (cake
   writes it as an `in` constraint over INTERIOR eq atoms, which no single baguette
   literal equals, T5), a variable on the bits arm (T7), and any row baguette commits
   outside a covered constraint. *)

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

let saturate (cl, cd) =
  if SM.exists (fun _ a -> a > cd) cl then (true, (SM.map (fun a -> min a cd) cl, cd))
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
type cand = { rpn : string; plain : bool; cl : int SM.t; cd : int; key : string }

type con = {
  cname : string;
  cands : (string, cand list) Hashtbl.t;
  by_min : (string, cand list) Hashtbl.t; (* its least variable (or "") -> candidates *)
  aux_seen : (string, unit) Hashtbl.t;
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
  q : (string, unit) Hashtbl.t; (* atom clauses already derived, by label *)
  value_of : (string, int) Hashtbl.t; (* ladder literal name -> its value *)
  holes : (string, string * int list) Hashtbl.t;
      (* a variable with a set domain -> its `in` constraint's name and allowed values *)
  mutable n_holes_vars : int;
  mutable cur : con option;
  mutable objective : (string * int) option;
  mutable nw : int;
  (* tallies, for the record and the comment line at the end *)
  mutable n_ia_rung : int;
  mutable n_ia_exact : int;
  mutable n_ia_w : int;
  mutable n_rup : int;
  mutable n_subst : int;
  mutable n_sel : int;
  mutable n_q : int;
  mutable finished : bool;
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
    q = Hashtbl.create 64;
    value_of = Hashtbl.create 256;
    holes = Hashtbl.create 8;
    n_holes_vars = 0;
    cur = None;
    objective = None;
    nw = 0;
    n_ia_rung = 0;
    n_ia_exact = 0;
    n_ia_w = 0;
    n_rup = 0;
    n_subst = 0;
    n_sel = 0;
    n_q = 0;
    finished = false;
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

let declare ?(holes = []) t x ~lo ~hi ~lit =
  match t.cur with
  | Some c ->
      (* an auxiliary declared while a constraint is posted: a disequality selector *)
      if lo <> 0 || hi <> 1 then
        refuse "an auxiliary integer %s in constraint %s" x c.cname;
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
      let v = { x; cx; lo; hi; comp; h; bsum; bmin; bmax; lit; e1 = ""; e2 = "" } in
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

let refuse_bits x = refuse "%s is on the bits encoding (--bits-above; T7)" x

let find_var t x =
  match Hashtbl.find_opt t.vars x with
  | Some v -> v
  | None -> refuse "a constraint names %s, which is not a declared model variable" x

(* ---------------------------------------------------------------------------
   cake's rows for one constraint (the contract, per keyword)
   --------------------------------------------------------------------------- *)

let cake_rows t name spec =
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

(* The substituted row's literal form and the line that derives it. *)
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
    else (
      t.n_subst <- t.n_subst + 1;
      emit t "@S[%s] pol @%s %s ;" r.label r.label (String.concat " " rpn);
      Printf.sprintf "@S[%s]" r.label)
  in
  (cite, lit_form (SM.filter (fun _ c -> c <> 0) vm, d))

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

type aval = T | F | L of string | Interior

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
    if kind = "ge" then if k <= v.lo then T else if k > v.hi then F else L (v.lit k)
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
    else (
      (* an eq atom: its two ge atoms' clauses first, then unit propagation *)
      List.iter
        (fun kk ->
          let ge = Printf.sprintf "%s[%s][ge%d]" (if isvar then "i" else "n") z kk in
          match atom_value t (isvar, z, "ge", kk) with
          | L _ ->
              ignore (q_clause t ge "p");
              ignore (q_clause t ge "n")
          | T -> ignore (q_clause t ge "t")
          | F -> ignore (q_clause t ge "f")
          | Interior -> ())
        [ k; k + 1 ];
      match (which, value) with
      | "t", T -> emit t "%s rup +1 %s >= 1 ;" lab g
      | "f", F -> emit t "%s rup +1 ~%s >= 1 ;" lab g
      | "p", L m -> emit t "%s rup +1 ~%s +1 %s >= 1 ;" lab g m
      | "n", L m -> emit t "%s rup +1 %s +1 %s >= 1 ;" lab g (neg_lit m)
      (* an interior value: e -> x_ge_k and e -> ~x_ge_(k+1), each by unit propagation *)
      | "a", Interior ->
          let v = find_var t (Hashtbl.find t.cake_names z) in
          emit t "%s rup +1 ~%s +1 %s >= 1 ;" lab g (v.lit k)
      | "b", Interior ->
          let v = find_var t (Hashtbl.find t.cake_names z) in
          emit t "%s rup +1 ~%s +1 ~%s >= 1 ;" lab g (v.lit (k + 1))
      | _ -> refuse "atom %s has no clause %s" g which));
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
            | Interior, _ -> row
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

let begin_con t ~name spec =
  let c =
    {
      cname = name;
      cands = Hashtbl.create 8;
      by_min = Hashtbl.create 8;
      aux_seen = Hashtbl.create 2;
    }
  in
  let push tbl k cand =
    Hashtbl.replace tbl k (Option.value (Hashtbl.find_opt tbl k) ~default:[] @ [ cand ])
  in
  let add rpn (cl, cd) =
    let cand =
      { rpn; plain = not (String.contains rpn ' '); cl; cd; key = key_of t cl }
    in
    push c.cands cand.key cand;
    push c.by_min
      (match String.index_opt cand.key ' ' with
      | Some i -> String.sub cand.key 0 i
      | None -> cand.key)
      cand;
    cand
  in
  let base =
    List.map
      (fun r ->
        let cite, lf = substitute t r in
        swap_atoms t (cite, lf))
      (cake_rows t name spec)
  in
  let cands = List.map (fun (rpn, lf) -> add rpn lf) base in
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
                    (add
                       (Printf.sprintf "%s %s %d * +" cand.rpn k.rpn a)
                       (lit_form
                          (vadd (to_var (cand.cl, cand.cd)) a (to_var (k.cl, k.cd))))))
              clauses)
        cand.cl)
    cands;
  t.cur <- Some c

let end_con t = t.cur <- None

(* ---------------------------------------------------------------------------
   Pins
   --------------------------------------------------------------------------- *)

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
        if not (is_flag t l) then
          SM.update l (fun o -> Some (Option.value o ~default:0 + c)) acc
        else
          let f = var_of l and positive = var_of l = l in
          let def =
            match
              Hashtbl.fold
                (fun s (g, p) acc -> if g = f then Some (s, p) else acc)
                t.sel None
            with
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

let define t (s, f, p) =
  Hashtbl.replace t.sel s (f, p);
  t.n_sel <- t.n_sel + 1;
  let fl = if p then f else "~" ^ f in
  emit t "@D1[%s] red +1 ~%s +1 %s >= 1 : %s -> %s ;" s s fl s fl;
  emit t "@D2[%s] red +1 %s +1 %s >= 1 : %s -> %s ;" s s (neg_lit fl) s fl

let pin t ~id (c : Opb.constr) =
  let body = Opb.constr_body c in
  let bl, bd = lits_of_row c in
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
  match (rung, t.cur) with
  | Some (`Rung hi), _ ->
      t.n_ia_rung <- t.n_ia_rung + 1;
      emit t "@c%d ia %s : @L[%s] ;" id body hi
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
      let exact = Option.value (Hashtbl.find_opt con.cands key) ~default:[] in
      let subset () =
        let vs = if key = "" then [] else String.split_on_char ' ' key in
        let inside k =
          k = "" || List.for_all (fun v -> List.mem v vs) (String.split_on_char ' ' k)
        in
        List.concat_map
          (fun v ->
            List.filter
              (fun cd -> cd.key <> key && inside cd.key)
              (Option.value (Hashtbl.find_opt con.by_min v) ~default:[]))
          ("" :: vs)
      in
      let rec go = function
        | [] -> None
        | cand :: rest ->
            let rec over = function
              | [] -> go rest
              | try_def :: more ->
                  let (sl, sd), rpn, made = swap t (cand.cl, cand.cd) ~try_def in
                  let sat, (sl, sd) = saturate (sl, sd) in
                  if implies (sl, sd) (bl, bd) then Some (cand, rpn, sat, made)
                  else over more
            in
            over tries
      in
      let found =
        match go exact with
        | Some r -> Some r
        | None when exact = [] || SM.exists (fun l _ -> Hashtbl.mem t.aux (var_of l)) bl
          ->
            go (subset ())
        | None -> None
      in
      match found with
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
      | None ->
          t.n_rup <- t.n_rup + 1;
          emit t "@c%d rup %s ;" id body)

let row t ~id c = pin t ~id c

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
       pol, %d rows rup"
      cake_pb_cp_sha256 t.n_subst t.n_q t.n_sel t.n_ia_rung t.n_ia_exact t.n_ia_w t.n_rup;
    Buffer.output_buffer t.oc t.b;
    Buffer.clear t.b;
    close_out t.oc);
  t.path

let stats t = (t.n_subst, t.n_q, t.n_sel, t.n_ia_rung, t.n_ia_exact, t.n_ia_w, t.n_rup)
