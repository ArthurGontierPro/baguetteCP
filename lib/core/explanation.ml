(* Explanations: HOW THE CHECKER IS CONVINCED that a value could be removed -- the
   derivation, in a form the proof layer can render.

   This is the design centre of the project. Read docs/SPEC.md section 3.3 and
   docs/ARCHITECTURE.md section 4 before changing it.

   D-0003 ("what does higher-order explanation mean here?") is RESOLVED, by D-0026, and
   the resolution split this type's job in two rather than reshaping it. *Which facts*
   justify a pruning is now declarative data in lib/core/reason.ml; *how the checker is
   convinced* is this type, unchanged, and it is the project's (a)-claim: [Combine] with
   a divisor, [Weaken], [Model_row], and [Term (coeff, t)] recursing into another
   justification -- an explanation taking explanations as arguments. Nothing about that
   was flattened by D-0026 and nothing about it should be.

   What changed here in M2-T8 is what this type is *not* asked to do any more. It no
   longer doubles as the reason: no propagator projects an [Explanation.t] to get the
   bound facts a trace line negates, and [Store.entry] no longer carries a second,
   closure-valued reason channel beside it. The one new function is [owners], which
   exists so the two halves can be *checked* against each other instead of kept in
   agreement by a comment.

   Do not add a constructor without a decision record -- D-0026 authorises the split, not
   a new constructor -- and when one is added, extend [force], [lits] and [to_string]
   rather than adding a catch-all case: the exhaustiveness warning is what will find
   every site that needs updating.

   [Deferred] exists because most prunings are never asked for a reason. Computing a full
   explanation eagerly for every pruning is the standard way to make a proof-logging
   solver an order of magnitude slower than its unlogged sibling. Forcing memoises: a
   reason can be demanded more than once during conflict analysis.

   -------------------------------------------------------------------------------
   M1-T12 / docs/DECISIONS.md D-0013: [Model_row], [Combine], [Weaken]
   -------------------------------------------------------------------------------

   D-0013 verified, against veripb 2.2.2, the actual derivation a bounds conflict at
   the root needs: weaken every *other* variable out of the model row with literal
   axioms (sound per D-0009 -- an axiom can never assert a bound, but it *can* weaken
   one away), or, where that variable sits at a bound some earlier step already
   derived, cite that derivation's id instead; then divide by the pushed variable's
   own coefficient. [Trivial]/[Linear]/[Cut] cannot say this:

     - [Linear] carries literals but no constraint id, so it cannot cite "the id that
       already established this bound" (D-0009).
     - [Cut] has two multipliers and no divisor, so it cannot express the division
       D-0010/D-0011 left out.
     - Nothing distinguishes "still at the declared bound, weaken it away" from
       "sitting at a bound some earlier step derived, cite that id" -- D-0013's whole
       point is that these are different operations with a different source.

   [Combine (summands, divisor)] is one [pol] step: every summand added, then (unless
   [divisor = 1]) divided. A [summand] is either [Term (c, e)] -- recursively emit
   [e], the way [Cut] already does, and cite its id scaled by [c] -- or [Weaken lits]
   -- a sum of individually-scaled *literal axioms*, which cancel a term whose
   variable is still sitting at its declared bound. [Weaken] is not a [t]: it is not
   a value anyone can point at and say "this holds", only a piece of arithmetic valid
   solely inside a [Combine]'s sum, which is exactly the D-0009 distinction made
   structural instead of a convention someone has to remember.

   [Model_row] exists because [Trivial] was not enough once a [Combine] cites an
   explanation another propagator *instance* built: [Trivial] meant "whatever
   [ctx.model_id] currently points at" (lib/core/justify.ml), a single ambient
   pointer good for exactly one row at a time. D-0011 already found this: two
   propagator instances justify against two different rows, and nothing on the trail
   says which one produced a given pruning. A [Combine] can legitimately hold, in one
   tree, an explanation this instance built (whose own base is its own row) *and* a
   cited explanation another instance built earlier (whose base is *that* instance's
   row) -- two different rows, resolved simultaneously, which one mutable ambient
   pointer cannot do. [Model_row id] names the row explicitly and renders to [id]
   directly, no lookup, so each instance's own base survives being embedded inside
   someone else's derivation.

   -------------------------------------------------------------------------------
   M1-T31 / M1-T50: [Trivial] is gone, and [Decision] is not its replacement
   -------------------------------------------------------------------------------

   [Trivial] had exactly two producers left: [Linear.make] without a [row_id], and
   search.ml's two decision pushes. The first is now impossible ([~row_id] is
   required), and the second was never what [Trivial] said. "The model constraint
   itself justifies this" is *false* of a decision: a decision is an assumption the
   search made, not a consequence of any row. Calling it [Trivial] is what let
   [Justify.emit] answer [ctx.model_id ()] and emit `pol <own row> <own row> +` --
   M1-T50, a proof step that does not say what the explanation says.

   So the constructor now carries what a decision actually is: [Decision lit], the
   order literal the search assumed. Two consequences follow, and both are the point:

   - **It has no constraint id, and never will.** Nothing in the proof establishes a
     decision. D-0009 is why: a [pol] cannot assert a literal (a bare literal in one
     is the trivial axiom [lit >= 0]) and a [rup] cannot derive one that is not a
     consequence. The decisions enter the proof in exactly one place, negated, in the
     branch's nogood -- D-0018 and lib/core/trace.ml's header say so already. A
     [Decision] is therefore not citable, and [term]/[cut] below refuse to build a
     summand out of one rather than leaving [Justify] to discover it.
   - **It is not silent.** [Trivial]'s [lits] was [[]], so a reason set that rested on
     a decision named nothing at all -- the omission D-0035 says becomes unsoundness
     once M2-T3 builds learned clauses from it. [Decision lit]'s [lits] is [[lit]].

   With [Trivial] gone, [Justify.ctx] has no [model_id] field at all: the ambient row
   is not "discouraged", it is unrepresentable. Every row a derivation names, it names
   with [Model_row]. *)

module Lit = Baguette_proof.Lit

type t =
  | Decision of Lit.t
    (* An assumption the search made: [lit] holds *because we said so*, on this
       branch only. Nothing derives it, so it has no constraint id and can never be
       a [pol] operand -- see the module header. *)
  | Clause of Lit.t list (* These literals together imply the pruning. Renders to rup. *)
  | Linear of (int * Lit.t) list * int
    (* sum a_i l_i >= b. Renders to pol over the model constraint. *)
  | Cut of t * t * int * int
    (* Linear combination: c1 * e1 + c2 * e2, the cutting-planes workhorse. Kept for
       existing single-row uses; D-0013's cross-row, divided combination is
       [Combine], below -- see the module header. *)
  | Model_row of int
    (* The id (a Baguette_proof.Writer.cid) of a model constraint already loaded by
       the checker's [f] rule, named explicitly rather than resolved through
       whatever [ctx.model_id] happens to point at right now. See the module
       header. *)
  | Combine of summand list * int
    (* sum of summands, then divide by the int (>= 1; 1 means "do not divide" --
       Justify skips emitting a division step rather than a no-op "1 d"). One
       [Combine] is one [pol] step (D-0013). *)
  | Deferred of thunk
(* Computed only if actually needed. *)

and summand =
  | Term of int * t
    (* coeff * (recursively emit this explanation and cite its resulting id). *)
  | Weaken of (int * Lit.t) list
(* sum of coeff_i * axiom(lit_i): weakens a variable's contribution out of the
   row it is added to. See the module header -- never meaningful outside a
   [Combine]'s summand list. *)

and thunk = { mutable forced : t option; mutable compute : unit -> t }

type expl = t

let decision lit = Decision lit
let clause lits = Clause lits
let linear terms rhs = Linear (terms, rhs)
let model_row id = Model_row id
let weaken lits = Weaken lits

(* The guard that keeps M1-T50 from coming back by a different route.

   A [Cut] operand and a [Combine]'s [Term] are both "emit this explanation and cite
   the id it produced" (lib/core/justify.ml's [emit_cut] and [emit_summand]). A
   [Decision] has no id to cite -- it is an assumption, not a derivation -- so there
   is no id for either of them to name, and the old code's answer was to fall through
   to whatever row was ambient. This refuses at the point the mistake is made, not
   several layers down inside [Justify] where the cited value is no longer in view.

   The caller's correct move is the one lib/core/prop/linear.ml makes: a term whose
   bound rests on a decision is *weakened* out of the row with declared-width axioms
   (D-0009 -- an axiom cannot assert a bound but it can weaken one away), and the
   decision's literal is carried by the D-0018 trace line instead. *)
let citable what e =
  match e with
  | Decision l ->
      invalid_arg
        (Printf.sprintf
           "Explanation.%s: a decision (%s) has no constraint id and cannot be cited. \
            Weaken the term out of the row instead -- see explanation.ml's header."
           what (Lit.to_string l))
  | e -> e

let cut e1 e2 c1 c2 = Cut (citable "cut" e1, citable "cut" e2, c1, c2)
let term coeff e = Term (coeff, citable "term" e)

let combine summands divisor =
  if divisor < 1 then invalid_arg "Explanation.combine: divisor must be >= 1";
  (match summands with
  | [] -> invalid_arg "Explanation.combine: summands must be non-empty"
  | _ -> ());
  Combine (summands, divisor)

let deferred compute = Deferred { forced = None; compute }

(* Force to a non-deferred head. Nested [Deferred] is allowed: a thunk may return another
   thunk, and memoisation records the fully forced result at each level. The closure is
   dropped once forced so that whatever it captured - propagator state, coefficient
   arrays - becomes collectable; a memoised thunk must never be re-run anyway. *)
let rec force = function
  | Deferred th -> (
      match th.forced with
      | Some e -> e
      | None ->
          let e = force (th.compute ()) in
          th.forced <- Some e;
          th.compute <- (fun () -> e);
          e)
  | e -> e

let is_forced = function Deferred { forced = None; _ } -> false | _ -> true

(* The forced value if it is already available, without running any thunk. Useful for
   debug printing, which must not have side effects on the memo table. *)
let peek = function Deferred th -> th.forced | e -> Some e

(* Literals mentioned by an explanation, after forcing, without duplicates. Conflict
   analysis walks this. *)
let lits e =
  let seen = Hashtbl.create 16 in
  let acc = ref [] in
  let add l =
    if not (Hashtbl.mem seen l) then (
      Hashtbl.add seen l ();
      acc := l :: !acc)
  in
  let rec go e =
    match force e with
    (* A decision's reason set is exactly the literal it assumed. [Trivial]'s was
       empty, which is the dependency D-0035 says becomes unsoundness in M2-T3. *)
    | Decision l -> add l
    | Model_row _ -> ()
    | Clause ls -> List.iter add ls
    | Linear (terms, _) -> List.iter (fun (_, l) -> add l) terms
    | Cut (a, b, _, _) ->
        go a;
        go b
    | Combine (summands, _) -> List.iter go_summand summands
    | Deferred _ -> assert false (* force returns a non-deferred head *)
  and go_summand = function
    | Term (_, e) -> go e
    | Weaken lits -> List.iter (fun (_, l) -> add l) lits
  in
  go e;
  List.rev !acc

(* The FlatZinc identifiers this derivation mentions, after forcing, without
   duplicates -- [lits] projected through [Lit.owner].

   D-0026 split the reason off this type, and the two halves then have to be checked
   against each other rather than kept in agreement by a comment. Literal-for-literal
   they do NOT agree and must not: the reason states where a bound currently *sits*,
   while a [Weaken] summand states the variable's whole *declared* range (D-0013), so
   the two projections of one pruning share no literal for a weakened term. What they do
   share is the variable scope, and that is what [Store.apply]'s D-0026 check compares:
   a reason naming a variable this derivation never mentions is a reason for a different
   pruning. See [Reason.owners] for the other side of the comparison. *)
let owners e = List.sort_uniq String.compare (List.map (fun l -> Lit.owner l.Lit.v) (lits e))

let rec to_string e =
  match e with
  | Decision l -> "decision(" ^ Lit.to_string l ^ ")"
  | Clause ls -> "clause(" ^ String.concat " " (List.map Lit.to_string ls) ^ ")"
  | Linear (terms, rhs) ->
      Printf.sprintf "linear(%s >= %d)"
        (String.concat " "
           (List.map (fun (a, l) -> Printf.sprintf "%+d %s" a (Lit.to_string l)) terms))
        rhs
  | Cut (a, b, c1, c2) ->
      Printf.sprintf "cut(%d*%s + %d*%s)" c1 (to_string a) c2 (to_string b)
  | Model_row id -> Printf.sprintf "model_row(%d)" id
  | Combine (summands, divisor) ->
      Printf.sprintf "combine(%s)%s"
        (String.concat " + " (List.map summand_to_string summands))
        (if divisor = 1 then "" else Printf.sprintf " / %d" divisor)
  | Deferred { forced = Some e; _ } -> "deferred[" ^ to_string e ^ "]"
  | Deferred { forced = None; _ } -> "deferred[?]"

and summand_to_string = function
  | Term (c, e) -> Printf.sprintf "%d*%s" c (to_string e)
  | Weaken lits ->
      "weaken("
      ^ String.concat " "
          (List.map (fun (c, l) -> Printf.sprintf "%d*%s" c (Lit.to_string l)) lits)
      ^ ")"

(* ------------------------------------------------------------------- arena *)

(* Explanations live in a side arena and the trail stores an index into it
   (docs/ARCHITECTURE.md section 3): trail records stay small and uniform, and
   invariant I-T3 - every trail entry's explanation index resolves - becomes something
   that can be checked with a bounds test.

   The arena is a stack. [truncate] is how backtracking discards the reasons for the
   prunings it is undoing; it is safe because nothing outside the trail holds an [id],
   and anything that wants to survive a backtrack (a learned clause) holds the forced
   [expl] value itself, which the GC keeps alive independently. *)
module Arena = struct
  type id = int
  type t = { mutable items : expl array; mutable len : int }

  (* Not a valid index; [get] on it raises. Lets containers hold a "no reason yet". *)
  let null : id = -1

  (* What an arena slot holds when nothing occupies it. [mem] bounds every [get], so
     it is never observable; it exists only so [truncate] can drop its references and
     let the GC collect what a discarded reason's thunk captured. [Trivial] played
     this role until M1-T31 deleted it, and the empty clause is a deliberate
     replacement rather than an arbitrary one: [Trivial] was a *plausible* reason, so
     a slot that leaked read as "the model row justifies this" and nothing complained,
     which is the failure mode this whole task is about. The empty clause renders as a
     claimed contradiction and fails at the checker on sight. *)
  let vacant : expl = Clause []

  let create ?(capacity = 256) () =
    { items = Array.make (Stdlib.max 1 capacity) vacant; len = 0 }

  let length a = a.len
  let mem a (i : id) = i >= 0 && i < a.len

  let grow a =
    let bigger = Array.make (Stdlib.max 1 (2 * Array.length a.items)) vacant in
    Array.blit a.items 0 bigger 0 a.len;
    a.items <- bigger

  let add a (e : expl) : id =
    if a.len = Array.length a.items then grow a;
    a.items.(a.len) <- e;
    a.len <- a.len + 1;
    a.len - 1

  let get a (i : id) : expl =
    if not (mem a i) then
      invalid_arg
        (Printf.sprintf "Explanation.Arena.get: %d out of range (len %d)" i a.len);
    a.items.(i)

  (* Force in place, so the memoised result is what the arena holds from now on. *)
  let force_at a (i : id) : expl =
    let e = force (get a i) in
    a.items.(i) <- e;
    e

  let truncate a n =
    if n < 0 then invalid_arg "Explanation.Arena.truncate: negative length";
    if n < a.len then (
      (* Drop the references so the explanations, and anything their thunks captured,
         become collectable. *)
      Array.fill a.items n (a.len - n) vacant;
      a.len <- n)

  let clear a = truncate a 0
end
