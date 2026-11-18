(* parity: a SYSTEM of XOR rows over Boolean variables, propagated by Gauss-Jordan
   elimination over GF(2). M12-parity-T1, docs/DECISIONS.md D-0147.

   ===========================================================================
   THIS MODULE IS A SPIKE AND IT HAS NO PROOF
   ===========================================================================

   It exists to answer one question -- how many search nodes does system-level parity
   reasoning remove on the coding-theory models -- and it lives on a branch that is never
   merged. Every pruning it makes carries its reason AS DATA, exactly as every other
   propagator here does (CLAUDE.md: "a propagator that narrows a domain without producing
   an Explanation is a bug"): the facts are the current values of the assigned atoms of
   the derived row's support (D-0026's split), and the [Explanation.t] is the clause those
   facts imply, [Explanation.clause]. What it does NOT have is the VeriPB derivation of
   that clause. A parity-implied clause is in general NOT reverse-unit-propagation
   derivable from the clause encoding (that is the whole point of the module), so if
   lib/core/justify.ml rendered it as the `rup` a [Clause] normally becomes, the checker
   would reject the proof -- or, worse, accept it vacuously after an earlier conflict
   (CLAUDE.md, "rup is vacuous over a contradictory database"). GCS's scheme for the real
   derivation (dev_docs/parity-system.md sections 2-4: the slack rows derived by `red` from
   the encoding, one `pol` per elimination, one `pol` plus one `rup` per inference) is
   what M12-parity-T2 would build.

   So the module refuses to exist in a proved run, MECHANICALLY:

     - [licence] is the only way to obtain the [licence] value [Compile.compile ?parity]
       requires, and it raises unless the caller says the run is `--no-proof`;
     - bin/main.ml refuses `--parity` without `--no-proof` before anything is compiled
       (exit 2), and checks [posted] against [Writer.is_null] once the writer exists.

   ---------------------------------------------------------------------------
   Consistency: GAC on the PB relaxation of the system
   ---------------------------------------------------------------------------

   GCS's wording (parity-system.md, "The propagator"), and the honest one: every literal
   implied by the CONJUNCTION of the rows under the current assignment is inferred, and a
   conjunction with no solution is a conflict. Each variable here contributes exactly one
   atom (a `var bool`, [make] checks the declared [0, 1]), so this coincides with GAC on
   the conjunction of the XORs. It is strictly stronger than unit propagation over the
   rows (which is GAC per row and nothing across rows), and that difference is the thing
   D-0147 measures. Implied EQUIVALENCES between two unassigned atoms (a two-atom row of
   the reduced system) are real strength with nowhere to live, as in GCS, and are not
   used.

   ---------------------------------------------------------------------------
   The algorithm: one reduction at the root, a small one per wake
   ---------------------------------------------------------------------------

   GCS re-eliminates the whole system from scratch at every wake, on bitset rows. That is
   O(rows * rank * atoms / 64) per wake, which for aut order 7 (25 842 rows over 25 902
   atoms) is out of reach. This module does the expensive part ONCE, at [make]:

     ROOT. The rows are put in reduced row-echelon form over all atoms: every root row is
       `p + sum_{f in expr(p)} f = c (mod 2)` with a distinct PIVOT atom p, and every
       atom that is no row's pivot is FREE. The set F of free atoms is small on these
       models -- 24 on QR48, 36 on QR72, 108 on aut order 7 -- because MiniZinc's
       `bool_xor(a, b, r) :: defines_var(r)` chains define almost every atom from earlier
       ones. [make] exploits that: pass 1 picks, for each row, an atom never seen before
       as the one it DEFINES (the last such, which is the `defines_var` output); pass 2
       expresses each defined atom over the never-defined ones C; pass 3 runs
       Gauss-Jordan on the remaining (constraint) rows over C only, which pivots some of
       C and leaves F; pass 4 rewrites every expression over F.

     WAKE. Under the current assignment, a root row whose pivot is ASSIGNED is an
       equation over the unassigned free atoms; a root row whose pivot is UNASSIGNED
       contains a column (its pivot) no other row has. So:
         - a conflict, or an implied FREE atom, can only come from the assigned-pivot
           rows: Gauss-Jordan over the unassigned F columns (at most |F| pivots, rows of
           |F| bits) finds them -- an empty row with odd parity, or a unit row;
         - an UNASSIGNED pivot p is implied exactly when its row's unassigned part lies
           in the span of those reduced rows, which one pass of reduction decides.
       That is the whole of GAC on the system, and its cost is O(rows * |F|^2 / 62) per
       wake rather than O(rows^2 * atoms / 62).

   The reason for an inference is the assigned atoms in the support of the derived row
   BEFORE substitution, which is GCS's (and Gocht and Nordstrom's section 4.3) rho. A
   derived row is a sum of root rows; its support is the pivots of the root rows it sums
   plus the free atoms of the XOR of their expressions. The reduction tracks which root
   rows were summed as a bitset over the ORIGINS of the node basis (at most |F| + 1 of
   them), not over all root rows, which is what keeps that bookkeeping at two words.

   The root form is a set of LINEAR COMBINATIONS of the gathered rows, so every root row,
   every derived row and therefore every reason clause is implied by the gathered rows.
   test/unit/test_parity.ml checks exactly that by brute force, and checks GAC the same
   way (every literal the brute force says is implied is inferred).

   ---------------------------------------------------------------------------
   Measurement
   ---------------------------------------------------------------------------

   [stats] counts runs, inferences, conflicts and CPU time. Under
   BAGUETTE_PARITY_UP=1 every run also computes the closure of unit propagation over the
   gathered rows from the same assignment (what the clause encoding, which stays posted
   alongside, can derive) and counts the inferences and conflicts that closure does NOT
   reach: [beyond_inferred] and [beyond_conflicts]. That is the "what did the system find
   that the clauses did not" column of D-0147. bin/main.ml prints the line on stderr at
   exit when `--parity` is given.

   BAGUETTE_PARITY_MODE=beyond keeps only those: see [beyond_only] for why the default
   mode, which applies everything Gauss-Jordan finds, can hurt the search. *)

module Lit = Baguette_proof.Lit

(* ------------------------------------------------------------------- the licence *)

type licence = No_proof_run

let refusal =
  "the parity propagator (M12-parity-T1 spike, docs/DECISIONS.md D-0147) has NO proof \
   rendering: its reasons are clauses implied by GF(2) reasoning, which the checker \
   cannot derive by `rup`. It may only be posted in a run made with --no-proof."

let licence ~no_proof = if no_proof then No_proof_run else failwith ("parity: " ^ refusal)

(* How many instances [make] has built. bin/main.ml compares it with the writer it
   creates: a non-null writer with a parity instance posted is refused. *)
let posted = ref 0

(* ----------------------------------------------------------------------- bitsets *)

module Bits = struct
  let w = 62
  let words n = max 1 ((n + w - 1) / w)
  let create n = Array.make (words n) 0
  let get b i = (b.(i / w) lsr (i mod w)) land 1 = 1

  let flip b i =
    let k = i / w in
    b.(k) <- b.(k) lxor (1 lsl (i mod w))

  let set b i =
    let k = i / w in
    b.(k) <- b.(k) lor (1 lsl (i mod w))

  let xor_into dst src =
    for k = 0 to Array.length dst - 1 do
      Array.unsafe_set dst k (Array.unsafe_get dst k lxor Array.unsafe_get src k)
    done

  let parity_word x =
    let x = x lxor (x lsr 32) in
    let x = x lxor (x lsr 16) in
    let x = x lxor (x lsr 8) in
    let x = x lxor (x lsr 4) in
    let x = x lxor (x lsr 2) in
    let x = x lxor (x lsr 1) in
    x land 1

  let parity_and a b =
    let p = ref 0 in
    for k = 0 to Array.length a - 1 do
      p := !p lxor (a.(k) land b.(k))
    done;
    parity_word !p

  let is_zero_and a b =
    let r = ref true and k = ref 0 in
    while !r && !k < Array.length a do
      if a.(!k) land b.(!k) <> 0 then r := false;
      incr k
    done;
    !r

  let is_zero a =
    let r = ref true and k = ref 0 in
    while !r && !k < Array.length a do
      if a.(!k) <> 0 then r := false;
      incr k
    done;
    !r

  (* Index of the single set bit of a power of two. *)
  let ctz x =
    let n = ref 0 and x = ref x in
    if !x land 0xFFFFFFFF = 0 then (
      n := 32;
      x := !x lsr 32);
    if !x land 0xFFFF = 0 then (
      n := !n + 16;
      x := !x lsr 16);
    if !x land 0xFF = 0 then (
      n := !n + 8;
      x := !x lsr 8);
    if !x land 0xF = 0 then (
      n := !n + 4;
      x := !x lsr 4);
    if !x land 0x3 = 0 then (
      n := !n + 2;
      x := !x lsr 2);
    if !x land 0x1 = 0 then incr n;
    !n

  (* Every set bit of [a land b], lowest first. *)
  let iter_and a b f =
    for k = 0 to Array.length a - 1 do
      let x = ref (a.(k) land b.(k)) in
      while !x <> 0 do
        let low = !x land - !x in
        f ((k * w) + ctz low);
        x := !x lxor low
      done
    done

  let iter a f =
    for k = 0 to Array.length a - 1 do
      let x = ref a.(k) in
      while !x <> 0 do
        let low = !x land - !x in
        f ((k * w) + ctz low);
        x := !x lxor low
      done
    done

  (* The lowest set bit of [a land b], or -1. *)
  let first_and a b =
    let r = ref (-1) and k = ref 0 in
    while !r < 0 && !k < Array.length a do
      let x = a.(!k) land b.(!k) in
      if x <> 0 then r := (!k * w) + ctz (x land -x);
      incr k
    done;
    !r

  (* [a land b] has exactly one set bit. *)
  let single_and a b =
    let seen = ref 0 and k = ref 0 in
    while !seen < 2 && !k < Array.length a do
      let x = a.(!k) land b.(!k) in
      if x <> 0 then if x land (x - 1) = 0 then incr seen else seen := 2;
      incr k
    done;
    !seen = 1
end

(* ------------------------------------------------------------------------- types *)

type t = {
  vars : Var.t array; (* atom -> variable *)
  names : string array;
  n : int; (* atoms *)
  nf : int; (* |F|, the free atoms of the root form *)
  free_atom : int array; (* F column -> atom *)
  is_free : bool array; (* atom -> is it in F *)
  piv : int array; (* root row -> its pivot atom *)
  expr : int array array; (* root row -> its free atoms, as a bitset over F *)
  cst : int array; (* root row -> its right-hand side, 0 or 1 *)
  inconsistent : bool; (* the rows alone sum to 0 = 1 *)
  donors : (int array * int) array; (* the gathered rows: atoms and parity *)
  occ : int array array; (* atom -> the donors that mention it *)
}

let name = "parity"

(* DOMAIN: GAC on the PB relaxation of the system, which coincides with GAC on the
   conjunction because each `var bool` is one atom. The header is the argument. *)
let consistency = Propagator.Domain
let vars t = Array.to_list t.vars
let n_atoms t = t.n
let n_free t = t.nf
let rank t = Array.length t.piv
let n_rows t = Array.length t.donors

(* ------------------------------------------------------------------ measurement *)

type stats = {
  mutable instances : int;
  mutable s_rows : int;
  mutable s_atoms : int;
  mutable s_rank : int;
  mutable s_free : int;
  mutable runs : int;
  mutable inferred : int;
  mutable inferred_free : int;
  mutable conflicts : int;
  mutable reason_atoms : int;
  mutable up_runs : int;
  mutable beyond_inferred : int;
  mutable beyond_conflicts : int;
  mutable time : float;
}

let stats =
  {
    instances = 0;
    s_rows = 0;
    s_atoms = 0;
    s_rank = 0;
    s_free = 0;
    runs = 0;
    inferred = 0;
    inferred_free = 0;
    conflicts = 0;
    reason_atoms = 0;
    up_runs = 0;
    beyond_inferred = 0;
    beyond_conflicts = 0;
    time = 0.;
  }

let diagnose_up =
  match Sys.getenv_opt "BAGUETTE_PARITY_UP" with Some "1" -> true | _ -> false

(* BAGUETTE_PARITY_MODE=beyond: apply ONLY what the unit-propagation closure of the
   gathered rows does not reach (inferences it leaves open, conflicts it does not find),
   and leave everything else to the clause encoding. Measured in D-0147 section 4: in
   the default mode the instance, which the FIFO engine runs as soon as any atom moves,
   pre-empts the chain clauses and records the support of a derived row where a
   two-literal clause would have been the reason, and on aut order 7 that alone turned
   172 nodes into more than 60 000. In this mode a parity reason exists only where no
   clause reason could. *)
let beyond_only =
  match Sys.getenv_opt "BAGUETTE_PARITY_MODE" with Some "beyond" -> true | _ -> false

let report oc =
  Printf.fprintf oc
    "parity: instances=%d rows=%d atoms=%d rank=%d free=%d runs=%d inferred=%d \
     inferred_free=%d conflicts=%d reason_atoms=%d up_runs=%d beyond_inferred=%d \
     beyond_conflicts=%d cpu=%.2fs\n\
     %!"
    stats.instances stats.s_rows stats.s_atoms stats.s_rank stats.s_free stats.runs
    stats.inferred stats.inferred_free stats.conflicts stats.reason_atoms stats.up_runs
    stats.beyond_inferred stats.beyond_conflicts stats.time

(* ---------------------------------------------------------------- the gathering *)

(* A row as compile.ml hands it over: the variables, constants already folded into the
   parity [rhs] (the row says their XOR is [rhs]). [normalise] cancels a variable that
   occurs twice (x xor x = 0); the order of first occurrence is kept. *)
let normalise (xs : Var.t list) : Var.t list =
  let count = Hashtbl.create 8 in
  List.iter
    (fun x ->
      let k = Var.to_int x in
      Hashtbl.replace count k (1 + Option.value ~default:0 (Hashtbl.find_opt count k)))
    xs;
  let emitted = Hashtbl.create 8 in
  List.filter
    (fun x ->
      let k = Var.to_int x in
      if Hashtbl.mem emitted k || Hashtbl.find count k mod 2 = 0 then false
      else (
        Hashtbl.add emitted k ();
        true))
    xs

(* Partition rows into connected components by shared variable, in order of first row.
   An empty row is dropped: with parity 0 it says nothing, with parity 1 it says 0 = 1
   and the donor's own clauses refute it (GCS makes the same choice). *)
let components (rows : (Var.t list * int) list) : (Var.t list * int) list list =
  let rows = List.map (fun (xs, rhs) -> (normalise xs, rhs land 1)) rows in
  let rows = List.filter (fun (xs, _) -> xs <> []) rows in
  let parent = Hashtbl.create 64 in
  let rec find x =
    match Hashtbl.find_opt parent x with
    | None -> x
    | Some p when p = x -> x
    | Some p ->
        let r = find p in
        Hashtbl.replace parent x r;
        r
  in
  List.iter
    (fun (xs, _) ->
      match xs with
      | [] -> ()
      | x0 :: rest ->
          let r0 = find (Var.to_int x0) in
          List.iter
            (fun x ->
              let r = find (Var.to_int x) in
              if r <> find r0 then Hashtbl.replace parent r (find r0))
            rest)
    rows;
  let order = ref [] and groups = Hashtbl.create 16 in
  List.iter
    (fun ((xs, _) as row) ->
      let r = find (Var.to_int (List.hd xs)) in
      match Hashtbl.find_opt groups r with
      | None ->
          Hashtbl.add groups r (ref [ row ]);
          order := r :: !order
      | Some l -> l := row :: !l)
    rows;
  List.rev_map (fun r -> List.rev !(Hashtbl.find groups r)) !order

(* --------------------------------------------------------------- the root form *)

let make store (rows : (Var.t list * int) list) : t =
  let rows = List.map (fun (xs, rhs) -> (normalise xs, rhs land 1)) rows in
  let inconsistent0 = List.exists (fun (xs, rhs) -> xs = [] && rhs = 1) rows in
  let rows = List.filter (fun (xs, _) -> xs <> []) rows in
  (* Atoms, in order of first occurrence. *)
  let index = Hashtbl.create 64 and atoms_rev = ref [] and n = ref 0 in
  let atom x =
    let k = Var.to_int x in
    match Hashtbl.find_opt index k with
    | Some a -> a
    | None ->
        let d = Store.get store x in
        if Domain.lo d <> 0 || Domain.hi d <> 1 then
          invalid_arg
            (Printf.sprintf
               "Parity.make: `%s` is declared over %s, but a parity atom must be a `var \
                bool` (the order encoding on [0, 1])"
               (Store.name store x) (Domain.to_string d));
        let a = !n in
        Hashtbl.add index k a;
        atoms_rev := x :: !atoms_rev;
        incr n;
        a
  in
  let donors =
    Array.of_list
      (List.map (fun (xs, rhs) -> (Array.of_list (List.map atom xs), rhs)) rows)
  in
  let n = !n in
  let vars = Array.of_list (List.rev !atoms_rev) in
  let names = Array.map (Store.name store) vars in
  let m = Array.length donors in
  let occ =
    let l = Array.make n [] in
    for r = m - 1 downto 0 do
      Array.iter (fun a -> l.(a) <- r :: l.(a)) (fst donors.(r))
    done;
    Array.map Array.of_list l
  in
  (* Pass 1: which atom each row DEFINES -- the last atom of the row not seen in any
     earlier row -- or none (a constraint row). *)
  let seen = Array.make n false in
  let defines = Array.make m (-1) and defined = Array.make n false in
  for r = 0 to m - 1 do
    let ats = fst donors.(r) in
    let fresh = ref (-1) in
    Array.iter (fun a -> if not seen.(a) then fresh := a) ats;
    (* a row may name an atom twice only if [normalise] failed; it did not *)
    if !fresh >= 0 then (
      defines.(r) <- !fresh;
      defined.(!fresh) <- true);
    Array.iter (fun a -> seen.(a) <- true) ats
  done;
  (* C: the atoms no row defines, as columns. *)
  let ccol = Array.make n (-1) and catoms = ref [] and nc = ref 0 in
  for a = 0 to n - 1 do
    if not defined.(a) then (
      ccol.(a) <- !nc;
      catoms := a :: !catoms;
      incr nc)
  done;
  let nc = !nc in
  let catom = Array.of_list (List.rev !catoms) in
  (* Pass 2: every defined atom over C. A row's other atoms are in C or were defined by
     an earlier row, because an atom is defined by the first row that mentions it. *)
  let exprc = Array.make n [||] and constc = Array.make n 0 in
  let over_c ats rhs ~skip =
    let v = Bits.create nc and c = ref rhs in
    Array.iter
      (fun a ->
        if a <> skip then
          if ccol.(a) >= 0 then Bits.flip v ccol.(a)
          else (
            Bits.xor_into v exprc.(a);
            c := !c lxor constc.(a)))
      ats;
    (v, !c)
  in
  for r = 0 to m - 1 do
    let d = defines.(r) in
    if d >= 0 then (
      let ats, rhs = donors.(r) in
      let v, c = over_c ats rhs ~skip:d in
      exprc.(d) <- v;
      constc.(d) <- c)
  done;
  (* Pass 3: the constraint rows, as equations over C, in reduced row-echelon form. *)
  let bcol = Array.make (max nc 1) (-1) and colrow = Array.make (max nc 1) (-1) in
  let bvec = Array.make (max nc 1) [||] and bconst = Array.make (max nc 1) 0 in
  let nb = ref 0 and inconsistent = ref inconsistent0 in
  for r = 0 to m - 1 do
    if defines.(r) < 0 then (
      let ats, rhs = donors.(r) in
      let v, c = over_c ats rhs ~skip:(-1) in
      let c = ref c in
      for b = 0 to !nb - 1 do
        if Bits.get v bcol.(b) then (
          Bits.xor_into v bvec.(b);
          c := !c lxor bconst.(b))
      done;
      if Bits.is_zero v then (if !c = 1 then inconsistent := true)
      else
        let col = Bits.first_and v v in
        for b = 0 to !nb - 1 do
          if Bits.get bvec.(b) col then (
            Bits.xor_into bvec.(b) v;
            bconst.(b) <- bconst.(b) lxor !c)
        done;
        bvec.(!nb) <- v;
        bconst.(!nb) <- !c;
        colrow.(col) <- !nb;
        bcol.(!nb) <- col;
        incr nb)
  done;
  let nb = !nb in
  (* F: the columns of C that pass 3 did not pivot. *)
  let fcol = Array.make (max nc 1) (-1) and fatoms = ref [] and nf = ref 0 in
  for col = 0 to nc - 1 do
    if colrow.(col) < 0 then (
      fcol.(col) <- !nf;
      fatoms := catom.(col) :: !fatoms;
      incr nf)
  done;
  let nf = !nf in
  let free_atom = Array.of_list (List.rev !fatoms) in
  (* Pass 4: every pivot over F. A C-pivot x's row is x + rest = c with [rest] over
     unpivoted columns only (reduced form), so x = c + rest. *)
  let cpiv_f = Array.make (max nb 1) [||] in
  for b = 0 to nb - 1 do
    let f = Bits.create nf in
    Bits.iter bvec.(b) (fun col -> if fcol.(col) >= 0 then Bits.flip f fcol.(col));
    cpiv_f.(b) <- f
  done;
  let to_f v c =
    let f = Bits.create nf and c = ref c in
    Bits.iter v (fun col ->
        if fcol.(col) >= 0 then Bits.flip f fcol.(col)
        else
          let b = colrow.(col) in
          Bits.xor_into f cpiv_f.(b);
          c := !c lxor bconst.(b));
    (f, !c)
  in
  let piv = ref [] and expr = ref [] and cst = ref [] in
  for r = 0 to m - 1 do
    let d = defines.(r) in
    if d >= 0 then (
      let f, c = to_f exprc.(d) constc.(d) in
      piv := d :: !piv;
      expr := f :: !expr;
      cst := c :: !cst)
  done;
  for b = 0 to nb - 1 do
    piv := catom.(bcol.(b)) :: !piv;
    expr := cpiv_f.(b) :: !expr;
    cst := bconst.(b) :: !cst
  done;
  let t =
    {
      vars;
      names;
      n;
      nf;
      free_atom;
      is_free =
        (let a = Array.make n false in
         Array.iter (fun x -> a.(x) <- true) free_atom;
         a);
      piv = Array.of_list (List.rev !piv);
      expr = Array.of_list (List.rev !expr);
      cst = Array.of_list (List.rev !cst);
      inconsistent = !inconsistent;
      donors;
      occ;
    }
  in
  incr posted;
  stats.instances <- stats.instances + 1;
  stats.s_rows <- stats.s_rows + m;
  stats.s_atoms <- stats.s_atoms + n;
  stats.s_rank <- stats.s_rank + Array.length t.piv;
  stats.s_free <- stats.s_free + nf;
  t

(* ------------------------------------------------------------------- one wake *)

type outcome =
  | Conflict_on of int list
    (* the atoms whose CURRENT values, together, contradict the rows *)
  | Implied of (int * int * int list) list
(* (atom, the value it must take, the atoms whose current values imply it) *)

(* [v.(a)] is atom [a]'s value, or -1 while unassigned. Pure: reads [v], writes nothing
   outside its own arrays. The header's "WAKE" paragraph is the specification. *)
let analyse t (v : int array) : outcome =
  if t.inconsistent then Conflict_on []
  else
    let nf = t.nf in
    let u = Bits.create nf and tr = Bits.create nf in
    for k = 0 to nf - 1 do
      match v.(t.free_atom.(k)) with -1 -> Bits.set u k | 1 -> Bits.set tr k | _ -> ()
    done;
    let cap = max 1 nf in
    let wc = Bits.words cap in
    let bf = Array.make cap [||] and bval = Array.make cap 0 in
    let bcomb = Array.make cap [||] and bcol = Array.make cap (-1) in
    let origin = Array.make cap (-1) and colrow = Array.make cap (-1) in
    let nb = ref 0 in
    let free_of f ~except =
      let acc = ref [] in
      Bits.iter f (fun k -> if k <> except then acc := t.free_atom.(k) :: !acc);
      !acc
    in
    let pivots_of comb =
      let acc = ref [] in
      Bits.iter comb (fun k -> acc := t.piv.(origin.(k)) :: !acc);
      !acc
    in
    (* Reduce [f] (with value [vl] and combination [comb]) by the basis rows whose pivot
       column it has. Each basis row toggles only its own pivot among pivot columns, so
       the set read before the first XOR is the set to apply. *)
    let reduce f vl comb =
      let hits = ref [] in
      Bits.iter_and f u (fun c -> if colrow.(c) >= 0 then hits := colrow.(c) :: !hits);
      List.iter
        (fun b ->
          Bits.xor_into f bf.(b);
          vl := !vl lxor bval.(b);
          Bits.xor_into comb bcomb.(b))
        !hits;
      !hits <> []
    in
    let conflict = ref None in
    let nroot = Array.length t.piv in
    let j = ref 0 in
    while !conflict = None && !j < nroot do
      let r = !j in
      incr j;
      let p = t.piv.(r) in
      let vp = v.(p) in
      if vp >= 0 then (
        let e = t.expr.(r) in
        if Bits.is_zero_and e u then (
          if t.cst.(r) lxor vp lxor Bits.parity_and e tr = 1 then
            conflict := Some (p :: free_of e ~except:(-1)))
        else
          let f = Array.copy e in
          let vl = ref (t.cst.(r) lxor vp lxor Bits.parity_and e tr) in
          let comb = Array.make wc 0 in
          ignore (reduce f vl comb : bool);
          match Bits.first_and f u with
          | -1 ->
              if !vl = 1 then
                conflict := Some ((p :: pivots_of comb) @ free_of f ~except:(-1))
          | col ->
              let k = !nb in
              incr nb;
              Bits.flip comb k;
              origin.(k) <- r;
              for b = 0 to k - 1 do
                if Bits.get bf.(b) col then (
                  Bits.xor_into bf.(b) f;
                  bval.(b) <- bval.(b) lxor !vl;
                  Bits.xor_into bcomb.(b) comb)
              done;
              bf.(k) <- f;
              bval.(k) <- !vl;
              bcomb.(k) <- comb;
              bcol.(k) <- col;
              colrow.(col) <- k)
    done;
    match !conflict with
    | Some atoms -> Conflict_on atoms
    | None ->
        let acc = ref [] in
        for b = 0 to !nb - 1 do
          if Bits.single_and bf.(b) u then
            let col = bcol.(b) in
            acc :=
              ( t.free_atom.(col),
                bval.(b),
                pivots_of bcomb.(b) @ free_of bf.(b) ~except:col )
              :: !acc
        done;
        for r = 0 to nroot - 1 do
          let p = t.piv.(r) in
          if v.(p) < 0 then
            let e = t.expr.(r) in
            if Bits.is_zero_and e u then
              acc :=
                (p, t.cst.(r) lxor Bits.parity_and e tr, free_of e ~except:(-1)) :: !acc
            else if !nb > 0 then
              let f = Array.copy e in
              let vl = ref (t.cst.(r) lxor Bits.parity_and e tr) in
              let comb = Array.make wc 0 in
              if reduce f vl comb && Bits.is_zero_and f u then
                acc := (p, !vl, pivots_of comb @ free_of f ~except:(-1)) :: !acc
        done;
        Implied (List.rev !acc)

(* ----------------------------------------------- the diagnostic: unit propagation *)

(* The closure of unit propagation over the gathered rows from [v]: what the clause
   encoding of the same rows derives on its own. [true] in the first component if it
   reaches a conflict. *)
let up_closure t (v : int array) : bool * int array =
  let vu = Array.copy v in
  let m = Array.length t.donors in
  let inq = Array.make m true in
  let q = Queue.create () in
  for r = 0 to m - 1 do
    Queue.add r q
  done;
  let conflict = ref false in
  while (not !conflict) && not (Queue.is_empty q) do
    let r = Queue.pop q in
    inq.(r) <- false;
    let ats, rhs = t.donors.(r) in
    let open_ = ref (-1) and nopen = ref 0 and par = ref rhs in
    Array.iter
      (fun a ->
        if vu.(a) < 0 then (
          incr nopen;
          open_ := a)
        else par := !par lxor vu.(a))
      ats;
    if !nopen = 0 then (if !par = 1 then conflict := true)
    else if !nopen = 1 then (
      vu.(!open_) <- !par;
      Array.iter
        (fun r' ->
          if not inq.(r') then (
            inq.(r') <- true;
            Queue.add r' q))
        t.occ.(!open_))
  done;
  (!conflict, vu)

(* ------------------------------------------------------------------ propagation *)

(* The bound fact an atom's current value is, and the clause literal that negates it --
   the shapes lib/core/prop/pb.ml's [falsity_fact] and [pb_lit] use for a [0, 1] atom. *)
let fact t a value =
  let name = t.names.(a) in
  if value = 1 then Reason.at_least ~name ~decl:0 1 else Reason.at_most ~name ~decl:1 0

let negated t a value =
  let name = t.names.(a) in
  if value = 1 then Lit.le name 0 else Lit.ge name 1

let snapshot t store =
  Array.map
    (fun x ->
      let d = Store.get store x in
      if Domain.lo d = Domain.hi d then Domain.lo d else -1)
    t.vars

let propagate t store =
  stats.runs <- stats.runs + 1;
  let t0 = Sys.time () in
  let v = snapshot t store in
  let outcome = analyse t v in
  stats.time <- stats.time +. (Sys.time () -. t0);
  let outcome =
    if not (diagnose_up || beyond_only) then outcome
    else
      let up_conflict, vu = up_closure t v in
      stats.up_runs <- stats.up_runs + 1;
      (match outcome with
      | Conflict_on _ ->
          if not up_conflict then stats.beyond_conflicts <- stats.beyond_conflicts + 1
      | Implied l ->
          if not up_conflict then
            List.iter
              (fun (a, _, _) ->
                if vu.(a) < 0 then stats.beyond_inferred <- stats.beyond_inferred + 1)
              l);
      if not beyond_only then outcome
      else if up_conflict then Implied []
      else
        match outcome with
        | Conflict_on _ -> outcome
        | Implied l -> Implied (List.filter (fun (a, _, _) -> vu.(a) < 0) l)
  in
  match outcome with
  | Conflict_on atoms ->
      stats.conflicts <- stats.conflicts + 1;
      stats.reason_atoms <- stats.reason_atoms + List.length atoms;
      let facts = List.map (fun a -> fact t a v.(a)) atoms in
      let expl = Explanation.clause (List.map (fun a -> negated t a v.(a)) atoms) in
      Propagator.Conflict
        (Store.conflict store (Reason.because ~concludes:None facts expl))
  | Implied l ->
      let rec apply = function
        | [] -> Propagator.Fixpoint
        | (a, value, reason) :: rest -> (
            stats.inferred <- stats.inferred + 1;
            stats.reason_atoms <- stats.reason_atoms + List.length reason;
            let name = t.names.(a) in
            let facts = List.map (fun b -> fact t b v.(b)) reason in
            let claim = if value = 1 then Lit.ge name 1 else Lit.le name 0 in
            let expl =
              Explanation.clause (claim :: List.map (fun b -> negated t b v.(b)) reason)
            in
            let concludes =
              Some
                (if value = 1 then Reason.at_least ~name ~decl:0 1
                 else Reason.at_most ~name ~decl:1 0)
            in
            let j = Reason.because ~concludes facts expl in
            let x = t.vars.(a) in
            let r =
              if value = 1 then Store.set_lo store x 1 j else Store.set_hi store x 0 j
            in
            match r with
            | Store.Changed | Store.Unchanged -> apply rest
            | Store.Conflict e -> Propagator.Conflict e)
      in
      List.iter
        (fun (a, _, _) ->
          if t.is_free.(a) then stats.inferred_free <- stats.inferred_free + 1)
        l;
      apply l
