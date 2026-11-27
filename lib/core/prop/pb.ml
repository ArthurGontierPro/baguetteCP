(* pb: a pseudo-Boolean inequality over ORDER LITERALS, propagated by slack,

     a_1 l_1 + ... + a_n l_n  >=  b,     every a_i >= 1

   where each l_i is an order-encoding atom [x >= k] at a polarity (the order encoding's
   ladder of literals per variable, D-0028, docs/PROOF-FORMAT.md section 3), so
   `~[x >= k]` is `x <= k - 1`. Its instances are LEARNED rows ([Learned_pb], at the
   bottom) and, at degree 1, every clause of lib/core/prop/clause.ml.

   Consistency level: BOUNDS ([consistency] below). See "Consistency level" below: the
   declaration is honest and the section says exactly what is left on the table.
   Governed by docs/SPEC.md 3.2 (consistency levels) and 3.3 (explanations). Proof shape:
   every forcing and every conflict is one `rup` of a clause over the row's falsified
   literals, RUP in one step against the row already on the page. The family is
   [Single_row] in the I-X10 classification table of test/unit/test_trace.ml (a pruning
   that follows from one constraint, whose trace line is RUP with nothing derived ahead
   of it); the ladder rows the checker also uses are the variable's own encoding, not a
   second constraint.

   ---------------------------------------------------------------------------
   A SOLVING-side object (D-0054)
   ---------------------------------------------------------------------------

   The premise, from D-0054, is one sentence: **a PB line for proof logging and a PB
   explanation for solving are different objects.** The first must be sound, complete
   and CITABLE; the second must be USEFUL TO PROPAGATION. This module is the second, and
   it was the first of its kind in this tree (M2-L13).

   [Propagator.pb_row] is explicitly the proof object and its own comment says so: it
   requires [r_cid] because "a row nobody can cite is a row no [pol] can be built from",
   and it is "emphatically not a function of the store because it reads live domains" --
   it is frozen at DECLARED bounds, because "a row that moved with the search would
   break I-X6" (an explanation reads a snapshot, never live domains). Both properties are
   correct for proof logging and disqualifying for propagation, because propagation
   strength lives in the LIVE domain at the moment of the pruning.

   **This module reads live domains, and that is the entire point.** [status] below reads
   the live domain on every call. Nothing here is frozen except the DECLARED bounds each
   atom carries, which are the .opb's ladder width and not a search state -- exactly the
   freeze lib/core/learned.ml's "Why the [Linear.t] is built here" argues for, for the
   same reason. The proof row stays static and citable; this object moves.

   This module instantiates from [Learned.t] terms directly. Before it, a learned row
   reached propagation only if [Learned.to_linear_row] could read it back as an integer
   linear row for [Linear], an ALGEBRAIC IDENTITY OVER THE DECLARED BOX. D-0050 called
   that "the right predicate used as the wrong gate", and D-0054 named why: a proof-side
   test doing a solving-side job. M2-L13 removed it from the propagation path; the
   predicate survives only as the MEASURED counter [Search.n_pb_converts] that
   bin/main.ml labels "MEASURED ONLY".

   ---------------------------------------------------------------------------
   [Clause] is the degree-1 case, and it is the SAME CODE
   ---------------------------------------------------------------------------

   [Clause] has no propagator of its own: its [t] IS this [t], its [make] and [of_lits]
   build one with every coefficient 1 and degree 1, and its [propagate] is this
   [propagate]. D-0044 fixed the learned object as a PB inequality with the clause as its
   degree-1, unit-coefficient case, and sharing the code makes that relationship
   structural instead of asserted. lib/core/prop/clause.ml already refused "a second
   implementation to keep in step" for [Array_bool_or]; the refusal applies here with
   more force.

   The degree-1 arithmetic falls out rather than being special-cased, which is the check
   that the generalisation is the right one. With every a_i = 1 and b = 1, the four cases
   a clause propagator distinguishes (the arms of the clause module's former survey, in
   brackets) are:

     - some literal satisfied: slack = |sat| + |open| - 1 >= 0 and a forcing needs
       1 > slack, i.e. slack = 0 with an open literal, which cannot happen while a
       literal is satisfied. Nothing fires ([Satisfied]).
     - two or more open, none satisfied: slack = |open| - 1 >= 1, and 1 > 1 is false.
       Nothing fires ([Two_open]).
     - exactly one open: slack = 0 and 1 > 0, so that literal is forced: unit
       propagation ([Units [l]]).
     - none open, none satisfied: slack = -1 < 0, conflict ([Units []]), including the
       opposite-direction HOLE case its header describes (`x >= 3 \/ x <= 1` with x at
       [2,2]).

   The explanations coincide too, and byte-identically: see [reason_clause] below.

   ---------------------------------------------------------------------------
   The rule, and why each pruning is RUP against the row on the page
   ---------------------------------------------------------------------------

   Let F be the literals FALSIFIED by the live domains and

     slack  =  ( sum of a_i over i not in F )  -  b.

     - slack < 0: the constraint is violated. Conflict.
     - any OPEN l_i with a_i > slack is forced true.

   Both are the textbook counter/slack rule (Elffers & Nordstrom, IJCAI 2018, and
   RoundingSat as Koops et al. (CP 2025) describe it; the literature review is in
   docs/DECISIONS.md D-0044).
   lib/core/reduce.ml's header already states its solving-side half -- "reduce the reason
   so the resolvent stays CONFLICTING" -- and confines it to the analysis; this is the
   same criterion at the other end of the pipeline.

   The PROOF OBLIGATION IS UNCHANGED and was already discharged before this module
   existed: the learned row is on the page as a stated line with its [pol] derivation
   behind it (lib/core/learned.ml's [introduce], lib/core/pb_analysis.ml's). Nothing
   here writes a new proof shape. What it writes is the [rup] every pruning in this
   solver writes, and the one-step RUP argument is:

     a forcing of l_i emits the clause  l_i \/ ( \/_{j in F} l_j ).  Negate it: l_i and
     every l_j in F are false, so the largest the left-hand side can reach is
     (slack + b) - a_i, which is < b because a_i > slack. The row is violated outright,
     so the checker finds the contradiction with no search at all.

     a conflict emits  \/_{j in F} l_j.  Negate it: the left-hand side is at most
     slack + b < b. Violated outright, again in one step.

   That is the same shape lib/core/prop/clause.ml already relies on, which is what
   D-0044's "the clause is the degree-1 case" has to mean on the proof side as well.

   **F is a SNAPSHOT taken at the top of the pass**, and the explanation of every
   forcing in that pass names that same F. It stays valid even if an earlier forcing in
   the same pass falsifies a further literal, because the argument above only needs the
   negated clause to violate the row, and a smaller F makes the bound on the left-hand
   side larger, not smaller. I-X6's snapshot discipline, met by construction.

   ---------------------------------------------------------------------------
   Consistency level: BOUNDS
   ---------------------------------------------------------------------------

   Forcing `x >= v` true moves [lo]; forcing it false moves [hi]. Those are the only two
   mutators this module calls, so it can only ever move bounds. It cannot punch an
   interior hole: that would need [Store.remove], a hole the row's own trace line does
   not unit-propagate (I-X10), and D-0052 (a clause over order literals is a widening of
   bool_clause, at BOUNDS) decided that the clause row does not reach for it.

   BOUNDS is also the honest level for a second reason that is about PB and not about
   holes: **the slack rule is not domain consistent even over the literals it does
   mention.** A single row knows nothing about the LADDER constraints that tie
   `[x >= 4]` to `[x >= 3]` (they are separate rows of the .opb, D-0028), which is
   precisely the observation lib/core/pb_analysis.ml's [Postcondition_failed] section
   makes about the same arithmetic on the analysis side. So a row can fail to force a
   literal that the row PLUS the ladder would force. That is a weaker propagator, not an
   unsound one, and BOUNDS claims no more than it delivers.

   [Clause.Bool_clause] still declares DOMAIN, still correctly, on the same [0, 1]
   precondition its [make] checks -- see clause.ml. An instance built here gets BOUNDS.

   ---------------------------------------------------------------------------
   No state across calls, and no watched literals on a PB row
   ---------------------------------------------------------------------------

   [propagate] relies on nothing an earlier call computed: every pass recomputes the
   slack from the live domains. [t] has no [mutable] field; its [scan] is written by
   [quiet] and read in the same run by lib/core/prop/clause.ml's learned clause, to move
   its watches. A cached slack updated on the trail is refused, because a cached counter
   that the trail does not undo is the classic way a backtracking PB solver becomes
   unsound in a way no proof check catches: the wrong slack yields a pruning whose `rup`
   is still valid for the F it names.

   Watched literals exist only for the degree-1 case. D-0052 had refused them as the
   first search-dependent mutable propagator state outside [Store]'s undo trail; M6-T20
   (D-0104) gave the learned CLAUSE two watches ([Clause.Learned_clause]), because an
   advisor (I-P7) may answer for a wake it drops. For a learned PB row, M20-pernode-T4
   (D-0208) measured the watched alternative and did not take it. A WITNESS of quiet (a
   few non-false literals whose sum, minus its largest (variable, polarity) group, reaches
   the degree; re-read at every run, so a choice and not a cached number) is exact and
   keeps the run order, but on costas and mknap the learned rows sit so close to
   propagating that a witness needs 60 to 70 % of the row and exists after fewer than half
   of the passes, and building it cost more than it saved: +20 and +24 % instructions at 3
   000 nodes. What was taken instead is the exact early exit of [pass] ([snapshot]'s
   [max_open]): one walk instead of three for a run that forces nothing, which is almost
   every run of a learned row.

   ---------------------------------------------------------------------------
   The pass's working memory is not state
   ---------------------------------------------------------------------------

   A pass runs over a [layout] built once per row, on its first pass ([t.layout] is
   lazy, so a row [quiet] always answers never builds one): each term's (variable,
   polarity) GROUP, and each group's terms strongest threshold first. With it
   [effective] is one walk per group and the strongest forceable threshold one slot per
   group, so a pass is O(row) and allocates nothing unless it prunes or conflicts.
   Before it, a pass allocated its whole survey (a list of (term, status) pairs, from 12
   terms a hash table of groups, and a [List.exists] per forceable term to keep the
   strongest), quadratic in a group on a row lifted onto ladder rungs; the complexity
   inventory measured the learned PB rows at 73 % of a no-proof node on 2011
   cyclic-rcpsp (D-0140, item E3), and M11-complexity-T3 (D-0142) built the layout.

   A pass also needs three SCRATCH arrays (the statuses, the effective coefficients and
   the per-group strongest threshold). They are mutable memory, and module-level: one set,
   [scratch], shared by every row and grown to the longest (a set per row cost 15 % of the
   peak memory of a 40 000-node run, one learned clause per conflict). It is not state in
   the sense above, and the argument is short: every pass WRITES every cell it will read
   before it reads it (all statuses first, then every term's effective coefficient and
   every group's slot), so nothing one pass leaves there is ever read by another. A cached
   slack is refused because a later call relies on a number an earlier call computed under
   domains the trail has since undone; here no call relies on any number from an earlier
   call. And two passes never overlap, whatever rows they belong to: a pass calls nothing
   that runs a propagator ([assign] only moves the store, which wakes nobody until the
   engine walks the trail after the run), it recurses into [propagate] only once it is
   past its last read, and the solver runs one propagator at a time on one domain. *)

module Lit = Baguette_proof.Lit

(* One order-encoding atom at a polarity:

     [positive = true ] : the literal is  x >= k
     [positive = false] : the literal is  x <= k - 1

   [name] is frozen at construction -- nothing renames a variable and an explanation
   should not have to hold the store to spell itself out. [decl_lo] / [decl_hi] are the
   DECLARED bounds, which is what [Reason] needs to decide whether a fact materialises to
   a literal at all (a fact at its declared bound is the constant true and drops out;
   reasons as declarative facts are D-0026, built by M2-T8); they come from the ENCODING
   and not from the store, because an instance built mid-search would otherwise freeze a
   narrowed box as the declared one. lib/core/learned.ml says this at length for the same
   hazard. *)
type atom = {
  x : Var.t;
  name : string;
  positive : bool;
  k : int;
  decl_lo : int;
  decl_hi : int;
}

(* A strictly positive coefficient on an atom. [of_terms] establishes the sign; a
   [Learned.t] has already normalised to positive coefficients ([Learned.make] absorbs a
   negative one by negating its literal), so the invariant arrives rather than being
   imposed here. *)
type term = { coeff : int; a : atom }

(* The status of one literal under the live domains, as [status] below reads it. *)
type status = Sat_lit | Unsat_lit | Open

(* The pass's LAYOUT, built once per row on its first pass (item E3 (a) of the
   complexity inventory D-0140, built by M11-complexity-T3, D-0142). Since D-0226 the
   terms themselves are the row's flat arrays ([t] below), so the layout holds only what
   is derived from them:

     [groups]  [None] when no two terms share a (variable, polarity), which is every
               clause [Learn.minimise] produced: then term [i] is group [i] alone.
               Otherwise the GROUPS, the terms [effective] can add for one another:
       [gid]     each term's group, numbered by first occurrence;
       [dom]     every term index, group after group, each group in DOMINANCE order:
                 strongest threshold first (the largest [k] in a positive group, the
                 smallest in a negative one), ties by term index;
       [gfirst]  group [g] is [dom.(gfirst.(g))] .. [dom.(gfirst.(g + 1) - 1)].

   The working memory of a pass is not here but in [scratch] below, shared by every row:
   see the header's "The pass's working memory is not state". *)
type groups = { gid : int array; dom : int array; gfirst : int array }
type layout = { groups : groups option; plain : bool }

(* [plain] says that no partial sum of the slack can overflow ([-degree] plus any subset
   of the coefficients, all of which are >= 1), so [snapshot] adds with [+] where
   [Checked.add] could never have raised (M20-pernode-T4, D-0208). False when the whole
   coefficient sum, or that sum minus a negative degree, does not fit. *)
let plain_sums (coef : int array) degree =
  let total = ref 0 and fits = ref (degree > min_int) in
  Array.iter
    (fun c -> if !total > max_int - c then fits := false else total := !total + c)
    coef;
  !fits && (degree >= 0 || !total <= max_int + degree)

(* [xv], [kv] and [pv] are the row's variables, thresholds and polarities (the arrays of
   [t] below, which is not defined yet). *)
let layout_of ~coef ~(xv : Var.t array) ~kv ~pv degree : layout =
  let plain = plain_sums coef degree in
  let n = Array.length coef in
  let positive i = Bytes.unsafe_get pv i <> '\000' in
  let key i = (2 * Var.to_int xv.(i)) + if positive i then 1 else 0 in
  let ids = Hashtbl.create (Int.max 1 n) in
  let gid = Array.make n 0 and ng = ref 0 in
  for i = 0 to n - 1 do
    match Hashtbl.find_opt ids (key i) with
    | Some g -> gid.(i) <- g
    | None ->
        Hashtbl.add ids (key i) !ng;
        gid.(i) <- !ng;
        incr ng
  done;
  if !ng = n then { groups = None; plain }
  else
    let dominance i j =
      let c = Int.compare gid.(i) gid.(j) in
      if c <> 0 then c
      else
        let ki = kv.(i) and kj = kv.(j) in
        let c = if positive i then Int.compare kj ki else Int.compare ki kj in
        if c <> 0 then c else Int.compare i j
    in
    let dom = Array.init n Fun.id in
    Array.sort dominance dom;
    let gfirst = Array.make (!ng + 1) n in
    for p = n - 1 downto 0 do
      gfirst.(gid.(dom.(p))) <- p
    done;
    { groups = Some { gid; dom; gfirst }; plain }

(* A term's group: its index when every group is a single term. *)
let group w i = match w.groups with None -> i | Some g -> g.gid.(i)

(* The pass's working memory, one set for every row (the header's "The pass's working
   memory is not state"), grown to the longest row seen:

     [st]      the snapshot F: every term's status at the top of the pass;
     [eff]     every term's ladder-effective coefficient under that snapshot;
     [gbest]   per group, the strongest threshold among its forceable terms. *)
type scratch = {
  mutable st : status array;
  mutable eff : int array;
  mutable gbest : int array;
  mutable n_open : int;
      (* How many terms [snapshot] found open, written by every [snapshot]. *)
  mutable osum : int array;
      (* Per group, the sum of its OPEN coefficients, written by every [snapshot]. *)
  mutable max_open : int;
      (* The largest [osum] of the snapshot, or [max_int] when a group's open sum would
         not fit (then the fast exit of [pass] is not taken). *)
}

let scratch =
  { st = [||]; eff = [||]; gbest = [||]; n_open = 0; osum = [||]; max_open = 0 }

let ensure_scratch n =
  if Array.length scratch.st < n then (
    let m = Int.max n (2 * Array.length scratch.st) in
    scratch.st <- Array.make m Open;
    scratch.eff <- Array.make m 0;
    scratch.gbest <- Array.make m 0;
    scratch.osum <- Array.make m 0)

(* What [quiet]'s walk found, kept for the learned clause's watch move
   (lib/core/prop/clause.ml, [Learned_clause.propagate]; item E2 (a) of the complexity
   pass, D-0142). When [quiet] answers [true], [f1] and [f2] are the indices of the FIRST
   TWO non-false literals; when it answers [false] they mean nothing. [quiet] writes both
   before it can answer [true], so, like the layout's scratch, the record carries nothing
   from one call to the next. *)
type scan = { mutable f1 : int; mutable f2 : int }

(* THE ROW IS FLAT. One array per field, indexed by term, and no record per term
   (M21-memory-T3, D-0226, the learned-row layout): [coef] the coefficient, [xv] the
   variable, [kv] the threshold [k], [pv] the polarity (a byte, ['\001'] for `x >= k`,
   ['\000'] for `x <= k - 1`), [dlo] and [dhi] the declared bounds, [lits] the proof
   literal. Until D-0226 a term was a [term] record over an [atom] record, held in a list,
   again in an array, again in the layout, beside a list of its literals: about 230 bytes
   per term on the 64-bit heap (measured in D-0218 section 5, where the heap goes), for 49
   here. [atom] and [term] above stay as the CONSTRUCTION and test view of a term
   ([atom_at], [terms]); nothing in a pass reads one.

   [lits] holds the literal each term was BUILT FROM when it came as one ([of_terms]), so
   a learned row and its propagator share their literals rather than each holding a copy;
   a literal's name is read off it ([name_at]). [expl_all] is the clause over all of them
   -- built once at construction, as before. It is not "the explanation": for a general
   row the explanation of a pruning is the SUBSET clause [reason_clause] builds. It is
   kept because in the degree-1 case that subset is always the whole thing, and
   lib/core/justify.ml memoises on PHYSICAL identity, so handing back the same value lets
   one clause emit one [rup] per decision level instead of one per pruning. That is the
   property lib/core/prop/clause.ml's header claims and this module has to keep. It is
   also why it is not made lazy: [Explanation.clause] answers with the written node of the
   same content when there is one (hash-consing), so WHEN it is built decides which node
   it is, and building it later would change the proof. *)
type t = {
  degree : int;
  n_terms : int;
  coef : int array;
  xv : Var.t array;
  kv : int array;
  pv : Bytes.t;
  dlo : int array;
  dhi : int array;
  lits : Lit.t array;
  expl_all : Explanation.t;
  scan : scan;
      (* [quiet]'s finding; lib/core/prop/clause.ml's learned clause reads it to move its
         watches. *)
  layout : layout Lazy.t;
      (* The pass's layout, built on the first pass (the header's "The pass's working
         memory is not state"). *)
}

let name = "pb"

(* BOUNDS. The header's "Consistency level" section is the argument. *)
let consistency = Propagator.Bounds
let pb_lit a = if a.positive then Lit.ge a.name a.k else Lit.le a.name (a.k - 1)

(* Term [i]'s fields. [name_at] reads the name off the literal: an order literal is
   [Ge (name, k)] at either polarity (`x <= k - 1` is the negated [Ge (name, k)]), and
   only order literals are ever stored ([atom_of] declines the others). *)
let var_at t i = t.xv.(i)
let k_at t i = t.kv.(i)
let positive_at t i = Bytes.unsafe_get t.pv i <> '\000'

(* THE HOT READS (D-0226) skip the bounds check: every per-term array of a [t] has length
   [n_terms], built so by [finish] and never resized, and every index the walks below pass
   is a term index ([0 .. n_terms - 1] by its loop bound, by the layout's [dom], or by
   [quiet]'s [< n] tests). The flat layout made a term three array reads where it was one
   array read and three field loads, and the checks on them were measurable on QR48
   (+4 % instructions per node before this). They are written [Array.unsafe_get] at each
   site, never through a polymorphic helper: a helper's body is compiled for any array, so
   it would test for a float array on every read, which the typed site does not. *)
let coeff_at t i = t.coef.(i)

let name_at t i =
  match t.lits.(i).Lit.v with Lit.Ge (nm, _) | Lit.Eq (nm, _) | Lit.Bit (nm, _) -> nm

let atom_at t i =
  {
    x = t.xv.(i);
    name = name_at t i;
    positive = positive_at t i;
    k = t.kv.(i);
    decl_lo = t.dlo.(i);
    decl_hi = t.dhi.(i);
  }

(* The row as [term]s, for tests and for whoever wants to read it: built on each call. *)
let terms t = List.init t.n_terms (fun i -> { coeff = t.coef.(i); a = atom_at t i })

(* From parallel lists, in term order: the coefficients, the atoms, and the literal each
   atom renders to. *)
let finish (coefs : int list) (atoms : atom list) (lits : Lit.t list) degree =
  let coef = Array.of_list coefs in
  let n = Array.length coef in
  let av = Array.of_list atoms in
  let xv = Array.map (fun a -> a.x) av
  and kv = Array.map (fun a -> a.k) av
  and dlo = Array.map (fun a -> a.decl_lo) av
  and dhi = Array.map (fun a -> a.decl_hi) av in
  let pv = Bytes.init n (fun i -> if av.(i).positive then '\001' else '\000') in
  {
    degree;
    n_terms = n;
    coef;
    xv;
    kv;
    pv;
    dlo;
    dhi;
    lits = Array.of_list lits;
    expl_all = Explanation.clause lits;
    scan = { f1 = -1; f2 = -1 };
    layout = lazy (layout_of ~coef ~xv ~kv ~pv degree);
  }

(* ------------------------------------------------------------------ construction *)

(* An order literal as an atom of this store, or [None].

   [None] for a [Lit.Eq] literal: the direct encoding is a set of 0-1 variables with no
   order to read a bound off (D-0019, D-0040: the solver stays on the order encoding), so
   a positive [Eq] would have to FIX a variable and a negative one would have to punch an
   interior hole. Both are outside what BOUNDS may claim and the second needs
   [Store.remove] (I-X10). [None] too for a name this store or this encoding does not
   know: the honest answer is to decline the whole instance rather than to guess a box. A
   1UIP cut and a PB row can both contain such a literal, so this is a case that really
   arises and is counted by
   the caller, not a defensive arm. *)
let atom_of store ~(decl : string -> (int * int) option) (l : Lit.t) : atom option =
  match l.Lit.v with
  | Lit.Eq _ | Lit.Bit _ ->
      None (* a bit is not a bound: decline (D-0130 section 7.5, the bits encoding) *)
  | Lit.Ge (nm, k) -> (
      match (Store.var_named store nm, decl nm) with
      | Some x, Some (lo, hi) ->
          Some { x; name = nm; positive = l.Lit.positive; k; decl_lo = lo; decl_hi = hi }
      | _ -> None)

(* The general entry: a PB row over proof literals, as [Learned.terms] hands it over.

   Coefficients must be strictly positive, which [Learned.make] guarantees; a
   non-positive one is dropped rather than accepted, because a zero term contributes
   nothing and a negative one would mean the caller skipped the normalisation and the
   row this instance propagates would not be the row on the page.

   [None] if any literal declines. Partial instantiation is not available: dropping a
   literal from a PB row makes it a DIFFERENT, stronger constraint, which is the one
   thing a learned instance must not be. (Dropping a literal from a CLAUSE is also
   strengthening -- same argument, which is why [Clause.of_lits] declined wholesale
   too.) *)
let of_terms store ~decl ~degree (raw : (int * Lit.t) list) : t option =
  let rec go cs atoms lits = function
    | [] -> Some (finish (List.rev cs) (List.rev atoms) (List.rev lits) degree)
    | (c, l) :: rest -> (
        if c <= 0 then go cs atoms lits rest
        else
          match atom_of store ~decl l with
          | None -> None
          (* The literal handed over is the one kept, shared with the caller's row (the
             flat learned-row layout of D-0226). [pb_lit a] is equal to it ([atom_of]
             reads [k] and the polarity off it and nothing else), so the explanations
             built from either are the same. *)
          | Some a -> go (c :: cs) (a :: atoms) (l :: lits) rest)
  in
  go [] [] [] raw

(* The degree-1 entry, for [Clause]: atoms already resolved, every coefficient 1. Not a
   second constructor -- it is [finish] with D-0044's degenerate numbers, written out so
   that the one place the clause case is spelled is here. *)
let of_atoms (atoms : atom list) : t =
  finish (List.map (fun _ -> 1) atoms) atoms (List.map pb_lit atoms) 1

(* The DISTINCT variables, in first-occurrence order (D-0226: a row lifted onto a ladder
   names one variable once per rung, and [Propagator.inst_vars] is kept for the life of
   the instance; every reader of it treats it as a set). *)
let vars t =
  let n = t.n_terms in
  if n <= 1 then Array.to_list t.xv
  else
    let seen = Hashtbl.create n in
    let acc = ref [] in
    for i = n - 1 downto 0 do
      Hashtbl.replace seen (Var.to_int t.xv.(i)) i
    done;
    for i = n - 1 downto 0 do
      if Hashtbl.find seen (Var.to_int t.xv.(i)) = i then acc := t.xv.(i) :: !acc
    done;
    !acc

let literals t = Array.to_list t.lits
let width t = t.n_terms
let degree t = t.degree
let coeffs t = Array.to_list t.coef

(* The row as (coefficient, literal) pairs in term order, as [Propagator.pb_row] and
   [Learned.raw_terms] give it: the row this instance propagates, at its own degree. *)
let raw_terms t = List.init t.n_terms (fun i -> (t.coef.(i), t.lits.(i)))

(* ------------------------------------------------------------------- bound facts *)

(* The facts lib/core/trace.ml negates into the tail of a trace line, the other projection
   of D-0018's rule that a branch nogood is RUP over the branch's own trace. A literal
   that is FALSE is a bound fact -- `x <= k - 1` for a positive occurrence, `x >= k` for a
   negative one -- which is exactly [Lit.negate] of the literal, so the line [Trace]
   builds, [claim :: List.map Lit.negate facts], comes out as the clause [reason_clause]
   built.

   M2-T8 / D-0026: the declared bound is IN the fact, so whether it materialises to a
   literal at all is [Reason.lit_of_fact]'s test and not this module's. *)
let falsity_fact a =
  if a.positive then Reason.at_most ~name:a.name ~decl:a.decl_hi (a.k - 1)
  else Reason.at_least ~name:a.name ~decl:a.decl_lo a.k

(* [falsity_fact (atom_at t i)], without the atom. *)
let falsity_fact_at t i =
  if positive_at t i then Reason.at_most ~name:(name_at t i) ~decl:t.dhi.(i) (t.kv.(i) - 1)
  else Reason.at_least ~name:(name_at t i) ~decl:t.dlo.(i) t.kv.(i)

(* ------------------------------------------------------------------- propagation *)

(* LIVE domains, every call. See the header: this is the whole difference between this
   object and [Propagator.pb_row].

   M11-complexity-T14: the bounds are read off the domain record once ([d.Domain.lo],
   [d.Domain.hi]) rather than through [Domain.lo]/[Domain.hi]. The values are the same;
   the difference is that dune's default (dev) profile compiles with [-opaque], so a
   cross-module accessor is never inlined and each was a call, two or three per literal on
   the hottest loop of a clause-heavy model ([status] and [falsified] were 12 % of a QR48
   node with their callees). *)
let status store a =
  let d = Store.get store a.x in
  if a.positive then
    if d.Domain.lo >= a.k then Sat_lit else if d.Domain.hi < a.k then Unsat_lit else Open
  else if d.Domain.hi < a.k then Sat_lit
  else if d.Domain.lo >= a.k then Unsat_lit
  else Open

(* [status store a = Unsat_lit], in one test: `x >= k` is false iff [hi x < k],
   `x <= k - 1` iff [lo x >= k]. The [Sat_lit] arm [status] tries first cannot hold at the
   same time, since [lo <= hi] (I-D1). The walks of [quiet] and the learned clause's
   watches ask only this. *)
let falsified store a =
  let d = Store.get store a.x in
  if a.positive then d.Domain.hi < a.k else d.Domain.lo >= a.k

(* [status store a = Sat_lit], in one test: `x >= k` holds iff [lo x >= k], `x <= k - 1`
   iff [hi x < k]. The satisfied-watch rule of [Clause.Learned_clause] asks only this
   (M11-complexity-T17, D-0173). *)
let holds store a =
  let d = Store.get store a.x in
  if a.positive then d.Domain.lo >= a.k else d.Domain.hi < a.k

(* The three above on term [i] of [t], reading its arrays (D-0226). Same tests. *)
let status_at store t i =
  let d = Store.get store (Array.unsafe_get t.xv i) and k = Array.unsafe_get t.kv i in
  if positive_at t i then
    if d.Domain.lo >= k then Sat_lit else if d.Domain.hi < k then Unsat_lit else Open
  else if d.Domain.hi < k then Sat_lit
  else if d.Domain.lo >= k then Unsat_lit
  else Open

let falsified_at store t i =
  let d = Store.get store (Array.unsafe_get t.xv i) in
  if positive_at t i then d.Domain.hi < Array.unsafe_get t.kv i
  else d.Domain.lo >= Array.unsafe_get t.kv i

let holds_at store t i =
  let d = Store.get store (Array.unsafe_get t.xv i) in
  if positive_at t i then d.Domain.lo >= Array.unsafe_get t.kv i
  else d.Domain.hi < Array.unsafe_get t.kv i

let is_false = function Unsat_lit -> true | Sat_lit | Open -> false
let is_open = function Open -> true | Sat_lit | Unsat_lit -> false

(* The explanation of one step, and the reason facts that go with it, read off the
   pass's snapshot [scratch.st].

   The step names every FALSIFIED term and, for a forcing, the forced term [claim] (a
   conflict passes [-1]). Both are taken IN TERM ORDER, which is what makes the degree-1
   case byte-identical to the clause propagator this replaced -- there the selected set
   is always the whole constraint, in the same order [pb] has, so the value handed to
   [Explanation.clause] is the same list.

   When the set IS the whole constraint the shared [expl_all] is returned instead of an
   equal fresh one, so lib/core/justify.ml's memoisation on physical identity still
   fires. That is not an optimisation of this module's making: it is the property
   clause.ml's header claims for a clause, preserved. *)
let reason_clause t ~claim =
  let picked = ref [] and facts = ref [] and n_picked = ref 0 in
  for j = t.n_terms - 1 downto 0 do
    let falsified = is_false scratch.st.(j) in
    if falsified || j = claim then (
      incr n_picked;
      picked := t.lits.(j) :: !picked;
      (* The FALSIFIED members are the facts. The forced literal is not a fact --
         [assign] passes it as [concludes] instead (D-0043: the conclusion is a
         [Reason.fact] carried on the justification), which is what lets [Store.apply]
         check the claim against the bound. *)
      if falsified then facts := falsity_fact_at t j :: !facts)
  done;
  let expl = if !n_picked = t.n_terms then t.expl_all else Explanation.clause !picked in
  (expl, !facts)

(* Force term [i], which is open, true. A positive atom moves [lo] to [k], a negative one
   moves [hi] to [k - 1]; either way exactly ONE bound moves, so lib/core/trace.ml writes
   exactly one line for it. The reason is not optional and there is no factless mutator to
   reach for (I-P4: every change carries its explanation and its facts): without it the
   line would claim the new bound unconditionally, which is false.

   D-0043: [concludes] is the [Reason.fact] mirror of the bound handed to the mutator on
   the next line, against the same declared bounds [falsity_fact] uses, so [Store.apply]
   can check the two against each other. *)
let assign t store i =
  let expl, facts = reason_clause t ~claim:i in
  let x = t.xv.(i) and k = t.kv.(i) and positive = positive_at t i in
  let concludes =
    Some
      (if positive then Reason.at_least ~name:(name_at t i) ~decl:t.dlo.(i) k
       else Reason.at_most ~name:(name_at t i) ~decl:t.dhi.(i) (k - 1))
  in
  let j = Reason.because ~concludes facts expl in
  if positive then Store.set_lo store x k j else Store.set_hi store x (k - 1) j

let conflict_of t store =
  let expl, facts = reason_clause t ~claim:(-1) in
  Propagator.Conflict (Store.conflict store (Reason.because ~concludes:None facts expl))

(* ------------------------------------------------- the LADDER-EFFECTIVE coefficient

   The plain slack rule forces [l_i] when [a_i > slack], because falsifying [l_i] alone
   costs the left-hand side [a_i]. Over ORDER LITERALS that is an underestimate, and
   badly so, because the rungs of one variable are not independent: `[x >= 5]` entails
   `[x >= 3]`, so falsifying `[x >= 3]` falsifies `[x >= 5]` with it. The cost of
   falsifying a rung is therefore the whole suffix of that variable's rungs above it,
   not its own coefficient.

   MEASURED, and it is the difference between a propagator and an ornament. The plain
   rule prunes NOTHING on test/models/width_sat_depth.fzn, whose 24 learned rows have
   the shape `+2 a_ge_1 ... +2 a_ge_99 >= 98`: total coefficient 198, degree 98, slack
   100, and no single coefficient of 2 beats 100. Read with the ladder the same row says
   `a >= 49`, which is what it means. The Boolean models do not notice, because a
   `var bool` ladder has ONE rung (D-0007) and the two rules coincide -- which is why
   this is not visible at all on the php family.

   So:

     effective([x >= k])   =  sum of a_j over x's NON-FALSIFIED POSITIVE rungs with
                              threshold >= k
     effective(~[x >= k])  =  sum of a_j over x's NON-FALSIFIED NEGATIVE terms with
                              threshold <= k

   and a literal is forced when its EFFECTIVE coefficient exceeds the slack. Already
   falsified terms are excluded because the slack has already paid for them.

   The proof obligation is still discharged in one [rup], and the extra step is the
   checker's own unit propagation over rows that are already on the page. Negating the
   emitted clause sets `~[x >= k]`; the LADDER rows of the .opb (D-0028,
   docs/PROOF-FORMAT.md section 3) unit-propagate `~[x >= j]` for every j >= k; the row
   is then short by [effective] and violated, because [effective > slack]. Same argument
   mirrored for a negative claim. Nothing new is emitted and nothing new is cited -- the
   ladder rows are model rows, on the page before the first decision and retired by
   nothing, which is the same standing lib/core/ladder.ml's lift relies on.

   This is where the pre-M2-L13 clause propagator was already slightly weak and nobody
   had noticed: `[x >= 3] \/ [x >= 5]` with both literals open is the clause `[x >= 3]`,
   and the old [Two_open] arm declined to say so. It does not arise in practice --
   [Learn.minimise]'s [slot] keys on (variable, polarity) and subsumes same-direction
   pairs before a clause is built, and a `bool_clause` has one rung per variable -- and
   the suite's proofs are byte-identical across this change, which is what says so. *)
let effective t i =
  let xi = Var.to_int t.xv.(i) and pi = positive_at t i and ki = t.kv.(i) in
  let acc = ref 0 in
  for j = 0 to t.n_terms - 1 do
    if
      (not (is_false scratch.st.(j)))
      && Var.to_int t.xv.(j) = xi
      && positive_at t j = pi
      && if pi then t.kv.(j) >= ki else t.kv.(j) <= ki
    then acc := Checked.add !acc t.coef.(j)
  done;
  !acc

(* [effective] for every term of one pass, in O(row) (M11-complexity-T3, D-0142, E3 (a);
   before it, a hash table per pass grouped the terms and a group was walked per term,
   still quadratic in a group and allocating every pass, M6-T11 / D-0085).

   The terms [effective] adds for a term are the non-falsified ones of its group whose
   threshold is at least as strong as its own. The layout lists each group strongest
   first, so one walk that sums the non-falsified coefficients gives every term its value
   as the running sum at the end of its TIE RUN (the terms of the group with the same
   threshold, which count one another).

   Same number: the addends are [effective]'s and all of them are positive (the
   constructors keep only coefficients >= 1), so their order does not change the sum. The
   one thing an order can change is WHERE [Checked.add] overflows, and so the message it
   raises. That is kept exact rather than argued away: a running sum that would pass
   [max_int] is not taken, every term from there on in the group is marked [-1], and
   [mark_forceable] calls [effective] itself for such a term, which raises what it always
   raised, at the same query. Every other term gets its true sum, because the running sum
   only grows.

   The same walk resets each group's [gbest] for [mark_forceable]. *)
let effective_all t w =
  match w.groups with
  | None ->
      (* Every term its own group: [effective] adds the term's own coefficient while the
         term is non-false, and from 0 a single positive addend cannot overflow. *)
      for i = 0 to t.n_terms - 1 do
        scratch.gbest.(i) <- (if positive_at t i then min_int else max_int);
        scratch.eff.(i) <-
          (if is_false scratch.st.(i) then 0 else Array.unsafe_get t.coef i)
      done
  | Some g ->
      for gi = 0 to Array.length g.gfirst - 2 do
        let stop = g.gfirst.(gi + 1) in
        scratch.gbest.(gi) <-
          (if positive_at t g.dom.(g.gfirst.(gi)) then min_int else max_int);
        let sum = ref 0 and fits = ref true and p = ref g.gfirst.(gi) in
        while !p < stop do
          let k = Array.unsafe_get t.kv g.dom.(!p) in
          let q = ref !p in
          while !q < stop && Array.unsafe_get t.kv g.dom.(!q) = k do
            let j = g.dom.(!q) in
            (if not (is_false scratch.st.(j)) then
               let c = Array.unsafe_get t.coef j in
               if !sum > max_int - c then fits := false else sum := !sum + c);
            incr q
          done;
          let e = if !fits then !sum else -1 in
          for r = !p to !q - 1 do
            scratch.eff.(g.dom.(r)) <- e
          done;
          p := !q
        done
      done

(* The FORCEABLE terms are the open ones whose effective coefficient exceeds the slack.
   Of the forceable literals of one variable at one polarity only the STRONGEST claim is
   forced: the largest threshold among the positive ones, the smallest among the negative.
   The others are implied by it through the domain, so forcing them too would move no
   bound and would only risk a second trace line for one inference.

   [mark_forceable] records each group's strongest forceable threshold in [gbest] and
   says whether anything is forceable. It queries the terms in term order, as the list
   filter it replaced did, which is what keeps the [Checked] overflow of [effective_all]
   at the same query. [forced] is then "forceable and as strong as its group's best",
   which is "no forceable term of its group is strictly stronger", the old [strongest]. *)
let mark_forceable t w ~slack =
  let any = ref false in
  for i = 0 to t.n_terms - 1 do
    if is_open scratch.st.(i) then (
      if scratch.eff.(i) < 0 then scratch.eff.(i) <- effective t i;
      if scratch.eff.(i) > slack then (
        any := true;
        let k = Array.unsafe_get t.kv i and g = group w i in
        if positive_at t i then (if k > scratch.gbest.(g) then scratch.gbest.(g) <- k)
        else if k < scratch.gbest.(g) then scratch.gbest.(g) <- k))
  done;
  !any

let forced t w ~slack i =
  is_open scratch.st.(i)
  && scratch.eff.(i) > slack
  && Array.unsafe_get t.kv i = scratch.gbest.(group w i)

(* One pass, then repeat while the store moved.

   The loop is what a general PB row needs and a clause does not: forcing one literal
   can falsify a different literal on the SAME variable (`x >= 5` forced true falsifies
   `~[x >= 3]`), which shrinks the slack and can make a further term forceable. Each
   pass recomputes from live domains, so the fixpoint is reached without any cached
   counter -- see the header on why there is none.

   Termination: a pass only repeats when a [Store] mutator reported [Changed], and a
   change strictly narrows a domain over a finite box.

   Fixpoint (I-P2): on return there is nothing more to say about this constraint,
   because the last pass found no forceable term and a non-negative slack. *)

(* The pass, when it can be seen in advance to do nothing (M6-T22, D-0138). At degree 1
   with two non-false literals on DIFFERENT variables, the slack S - 1 (S the non-false
   coefficients' sum) is at least 1, so there is no conflict; and a literal is forced
   only when its LADDER-EFFECTIVE coefficient ([effective]) exceeds S - 1, i.e. reaches
   S, which needs ALL of the non-false coefficient sum to sit in that literal's own
   (variable, polarity) -- and a non-false literal on another variable, with its
   coefficient of at least 1, rules that out. So the pass would return [Fixpoint] having
   changed nothing, and [quiet] says so with one walk that stops at the second free
   variable, instead of the pass's walks over the whole row.

   Degree 1 is every clause ([Clause], learned or not) and only the clauses' rows here.
   On QR48 (D-0138) a learned clause runs 369 times per node and changes something 0.01
   times per node, and a `bool_clause` 270 times for 36: the runs this answers are the
   runs that change nothing, so every run that does change something happens in the same
   order on the same domains, and the trail and the proof are the same.

   M11-complexity-T3 (D-0142, E2 (a)): the walk is over the row's arrays with top-level
   functions, so it builds no closure per call, and it records the first two non-false
   literals in [t.scan], which is what lets a learned clause move its watches without a
   walk of its own. The predicate is the one above, split at the second non-false literal:
   "a non-false literal after the first one, on another variable" is "the second one is
   on another variable, or a non-false literal after the second one is". *)
let rec next_free store t i =
  if i >= t.n_terms then i
  else if falsified_at store t i then next_free store t (i + 1)
  else i

let rec free_off store t xi i =
  let j = next_free store t i in
  j < t.n_terms
  && (Var.to_int (Array.unsafe_get t.xv j) <> xi || free_off store t xi (j + 1))

let quiet store t =
  t.degree = 1
  &&
  let n = t.n_terms in
  let f1 = next_free store t 0 in
  f1 < n
  &&
  let f2 = next_free store t (f1 + 1) in
  t.scan.f1 <- f1;
  t.scan.f2 <- f2;
  f2 < n
  &&
  let xi = Var.to_int (Array.unsafe_get t.xv f1) in
  Var.to_int (Array.unsafe_get t.xv f2) <> xi || free_off store t xi (f2 + 1)

(* The top of a pass: the snapshot F into [scratch.st], the number of open terms into
   [scratch.n_open], each group's open sum into [scratch.osum] and their largest into
   [scratch.max_open], and the slack, summed in term order from [-degree] through
   [Checked.add], or through [+] when the layout's [plain] says no partial sum can
   overflow. Reads the store, writes only [scratch].

   [max_open] (M20-pernode-T4, D-0208) is the largest ladder-effective coefficient of an
   open term, exactly. A term i of group g counts the non-false terms of g at least as
   strong as itself; a satisfied term of g is strictly weaker than any open one (for
   `x >= k`, satisfied is [k <= lo] and open is [lo < k <= hi]; mirrored for
   `x <= k - 1`), so what i counts is open terms of g only, and the weakest open term of g
   counts all of them. So [mark_forceable] finds a forceable term iff [slack < max_open],
   and [pass] returns at once when [slack >= max_open], which is most runs of a learned
   row (D-0208 section 6). [max_int] means "do not exit early", never "nothing is
   forceable". *)
let snapshot store t w =
  let n = t.n_terms in
  ensure_scratch n;
  let slack = ref (-t.degree) and n_open = ref 0 and mx = ref 0 and fits = ref true in
  let osum = scratch.osum and plain = w.plain and coef = t.coef in
  (match w.groups with
  | None ->
      for i = 0 to n - 1 do
        let c = Array.unsafe_get coef i in
        let s = status_at store t i in
        scratch.st.(i) <- s;
        match s with
        | Unsat_lit -> ()
        | Open ->
            incr n_open;
            if c > !mx then mx := c;
            slack := if plain then !slack + c else Checked.add !slack c
        | Sat_lit -> slack := if plain then !slack + c else Checked.add !slack c
      done
  | Some g ->
      Array.fill osum 0 (Array.length g.gfirst - 1) 0;
      for i = 0 to n - 1 do
        let c = Array.unsafe_get coef i in
        let s = status_at store t i in
        scratch.st.(i) <- s;
        match s with
        | Unsat_lit -> ()
        | Open ->
            incr n_open;
            let gi = g.gid.(i) in
            let o = osum.(gi) in
            if o > max_int - c then fits := false
            else (
              osum.(gi) <- o + c;
              if o + c > !mx then mx := o + c);
            slack := if plain then !slack + c else Checked.add !slack c
        | Sat_lit -> slack := if plain then !slack + c else Checked.add !slack c
      done);
  scratch.n_open <- !n_open;
  scratch.max_open <- (if !fits then !mx else max_int);
  !slack

let rec propagate t store = if quiet store t then Propagator.Fixpoint else pass t store

(* The pass over the layout (M11-complexity-T3, D-0142): the snapshot F and the slack in
   one walk, then -- only when a term is open -- [effective_all], [mark_forceable], and
   the forcings in term order. It allocates nothing unless it prunes or conflicts, and
   then only the explanation. Every step reads the snapshot, never the store, from the
   first walk on, so computing [forced] term by term while assigning gives the list the
   old pass computed whole before its first assignment. *)
and pass t store =
  let w = Lazy.force t.layout in
  let n = t.n_terms in
  let slack = snapshot store t w in
  if slack < 0 then conflict_of t store
  else if scratch.n_open = 0 || (slack >= scratch.max_open && scratch.max_open < max_int)
  then Propagator.Fixpoint
  else (
    effective_all t w;
    if not (mark_forceable t w ~slack) then Propagator.Fixpoint
    else
      let rec apply moved i =
        if i = n then if moved then propagate t store else Propagator.Fixpoint
        else if not (forced t w ~slack i) then apply moved (i + 1)
        else
          match assign t store i with
          | Store.Changed -> apply true (i + 1)
          | Store.Unchanged -> apply moved (i + 1)
          | Store.Conflict e ->
              (* Reachable, unlike the clause case: two forced literals on one
                 variable can be jointly unsatisfiable, and then the row plus the
                 snapshot F really is a contradiction. Forwarded exactly as
                 [Store.apply] returns it, the way every other propagator does. *)
              Propagator.Conflict e
      in
      apply false 0)

(* --------------------------------------------------------------------------------
   The learned face: a PB row this search derived, registered mid-search by
   lib/core/search.ml. Named apart from [name] above so that a trace, a fallback reason
   or an attribution failure says WHICH row -- a model row's or one this search derived
   -- which is the distinction lib/core/retention.ml's citation guard is about.

   A learned instance is on the page only while [Retention] holds it, so a [rup] citing
   it is RUP only while that constraint is live: whoever registers one must
   [Retention.cite] its id. [Search.register_learned_pb] does. That is the same coupling
   M2-L12 created for the learned clause. It matters because learned rows are evicted:
   the default retention policy is [tiered] (D-0226), not the keep-everything policy
   D-0051 had chosen. *)
module Learned_pb = struct
  type nonrec t = t

  let name = "learned_pb"
  let consistency = consistency
  let vars = vars
  let propagate = propagate
end
