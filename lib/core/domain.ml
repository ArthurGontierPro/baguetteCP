(* Finite integer domains: a bounds pair plus a lazily allocated hole set.

   Rationale for the representation is in docs/ARCHITECTURE.md section 2 - most
   propagation in a linear-heavy workload is bounds reasoning, so the bounds are the fast
   path and holes are only populated by the propagators that actually punch them.

   The hole set is a bitset ([Bytes.t]) rather than a balanced set, because SPEC section
   3.1 requires membership in O(1) and permits hole removal to be O(size). It is used
   *immutably*: [remove] copies the bitset before setting a bit. That costs O(size) per
   interior removal, which the spec allows, and it is what makes the trail correct - the
   store restores a domain by writing back the old [t], so a [t] must never share mutable
   state with its successors (invariant I-T1).

   Invariants (docs/INVARIANTS.md):
     I-D1  lo <= hi; an empty domain is never constructed, it is reported as [Failed]
     I-D2  lo and hi are in the domain: holes never sit at a bound
     I-D3  a domain only ever shrinks - every operation here returns a subset *)

(* Bit [i] of [bits] stands for the value [base + i]. [span] is how many values the
   bitset covers; it is fixed when the bitset is first allocated, at which point it spans
   exactly the bounds then in force. Since domains only shrink (I-D3), every later value
   of the domain is inside [base, base + span). Bits outside the current bounds may be
   stale; [mem] tests the bounds first, so they are harmless. *)
type holes = { base : int; span : int; bits : Bytes.t }
type t = { lo : int; hi : int; holes : holes option }
type result = Unchanged | Changed of t | Failed

(* What a narrowing actually moved - docs/ARCHITECTURE.md section 2's promise, which the
   code did not keep until M2-T5: "Operations return a [change] describing what moved
   ([NoChange | Bound of ... | Holes of ...]) so the engine knows which propagators to
   re-queue and the proof layer knows which literals became true."

   The payloads are chosen for those two readers:

   - [Bound] carries the bound that MOVED, and only if it moved: [lo = Some v] means the
     lower bound is now [v] and was lower before. At least one of the two is [Some]
     (bounds only shrink, I-D3), and a single operation can move both -- [fix] does.
     [Some v] is exactly the order literal [x >= v] (resp. [x <= v]) the proof layer has
     to claim, which is why the new value and not the old one is what is recorded.
   - [Holes] carries the interior values removed, ascending. Only values strictly inside
     the new bounds can be here: a removal at a bound tightens that bound instead
     ([settle] restores I-D2), so a change is either a [Bound] or a [Holes] and never
     both. The engine relies on exactly that disjointness.

   NOTE (M2-T5, deviation to route): this is a *sibling* of [result], not a payload of
   [Changed]. Putting the change inside [Changed] is the shape ARCHITECTURE section 2
   reads as promising, and it is a two-line diff -- [Changed of t * change] here and the
   one match in [Store.apply] -- but lib/core/store.ml and test/unit/test_core.ml were
   not this round's to edit. [classify] below computes the same value from the [old] and
   [now] a trail entry already records, so nothing is lost today; the bridge is
   [change_of]. *)
type change =
  | NoChange
  | Bound of { lo : int option; hi : int option }
  | Holes of int list

exception Bad_domain of string

(* Above this many values we decline to allocate a hole bitset and simply do not record
   the hole. Declining to prune is sound (we only ever keep values, never remove ones we
   should have kept); it just makes the domain weaker. Bound moves never need the bitset,
   so this only affects interior holes in enormous domains, which the FlatZinc subset in
   SPEC section 2.1 does not produce in practice. *)
let max_hole_span = 1 lsl 20

(* ------------------------------------------------------------------ bitsets *)

let popcount8 =
  Array.init 256 (fun i ->
      let rec go i acc = if i = 0 then acc else go (i lsr 1) (acc + (i land 1)) in
      go i 0)

let get_bit bits i =
  Char.code (Bytes.unsafe_get bits (i lsr 3)) land (1 lsl (i land 7)) <> 0

let set_bit bits i =
  let byte = i lsr 3 in
  Bytes.unsafe_set bits byte
    (Char.unsafe_chr (Char.code (Bytes.unsafe_get bits byte) lor (1 lsl (i land 7))))

(* Number of set bits in the inclusive bit range [i0, i1]. *)
let count_bits bits i0 i1 =
  if i1 < i0 then 0
  else
    let b0 = i0 lsr 3 and b1 = i1 lsr 3 in
    let head_mask = (0xff lsl (i0 land 7)) land 0xff in
    let tail_mask = 0xff lsr (7 - (i1 land 7)) in
    if b0 = b1 then
      popcount8.(Char.code (Bytes.get bits b0) land head_mask land tail_mask)
    else
      let total = ref popcount8.(Char.code (Bytes.get bits b0) land head_mask) in
      for k = b0 + 1 to b1 - 1 do
        total := !total + popcount8.(Char.code (Bytes.get bits k))
      done;
      total := !total + popcount8.(Char.code (Bytes.get bits b1) land tail_mask);
      !total

(* ------------------------------------------------------------- construction *)

let make lo hi =
  if lo > hi then raise (Bad_domain (Printf.sprintf "empty initial domain %d..%d" lo hi));
  { lo; hi; holes = None }

let singleton v = { lo = v; hi = v; holes = None }

(* ----------------------------------------------------------------- querying *)

let lo d = d.lo
let hi d = d.hi
let is_fixed d = d.lo = d.hi

let is_hole d v =
  match d.holes with
  | None -> false
  | Some h ->
      let i = v - h.base in
      i >= 0 && i < h.span && get_bit h.bits i

let mem d v = v >= d.lo && v <= d.hi && not (is_hole d v)
let value d = if is_fixed d then Some d.lo else None

let size d =
  let width = d.hi - d.lo + 1 in
  match d.holes with
  | None -> width
  | Some h ->
      let i0 = max 0 (d.lo - h.base) in
      let i1 = min (h.span - 1) (d.hi - h.base) in
      width - count_bits h.bits i0 i1

let has_holes d = match d.holes with None -> false | Some _ -> size d < d.hi - d.lo + 1

let iter f d =
  for v = d.lo to d.hi do
    if not (is_hole d v) then f v
  done

let fold f acc d =
  let acc = ref acc in
  iter (fun v -> acc := f !acc v) d;
  !acc

let to_list d = List.rev (fold (fun acc v -> v :: acc) [] d)

let holes_list d =
  let acc = ref [] in
  for v = d.hi downto d.lo do
    if is_hole d v then acc := v :: !acc
  done;
  !acc

(* Structural equality of the *sets*, not of the representations: two domains with
   different stale bits but the same live values are equal. Used by the trail tests for
   I-T1, where "exactly the state at the level mark" means exactly this. *)
let equal a b =
  a.lo = b.lo && a.hi = b.hi
  &&
  match (a.holes, b.holes) with
  | None, None -> true
  | _ ->
      let ok = ref true in
      let v = ref a.lo in
      while !ok && !v <= a.hi do
        if is_hole a !v <> is_hole b !v then ok := false;
        incr v
      done;
      !ok

(* ------------------------------------------------------------ change kinds *)

(* What moved between [old] and the [now] that replaced it. This is the [change] of
   docs/ARCHITECTURE.md section 2, recovered from the pair of domains rather than
   returned alongside the new one - see the NOTE on [change] above for why.

   Cost matters here: [Engine] calls this once per trail entry, on the hot path of the
   fixpoint loop. The bound comparison is O(1) and returns first, so the common case (a
   bound move, which is every pruning M1's propagators make) costs four integer
   comparisons and no allocation beyond the result. Only the interior-hole case walks the
   interval, and it is bounded by the span of a domain that is already known to have a
   bitset. That is the right way round: the rare case pays.

   Precondition: [now] is a subset of [old] (I-D3), which is what [Store.apply] has
   already asserted by the time the engine gets here. If it is not - if a bound somehow
   widened - the widened side reports as "did not move" rather than lying about a
   literal that did not become true. *)
let classify ~old ~now =
  if old.lo <> now.lo || old.hi <> now.hi then
    Bound
      {
        lo = (if now.lo > old.lo then Some now.lo else None);
        hi = (if now.hi < old.hi then Some now.hi else None);
      }
  else
    (* Same bounds, so anything that went is strictly interior. Walk downwards and
       prepend, so the list comes out ascending without a reversal. *)
    let removed = ref [] in
    for v = now.hi downto now.lo do
      if is_hole now v && not (is_hole old v) then removed := v :: !removed
    done;
    match !removed with [] -> NoChange | vs -> Holes vs

(* The bridge between the two vocabularies: the [change] that applying [r] to [d] makes.
   [Failed] is not a change - the empty domain is never stored (I-D1), so there is no
   watcher for it to wake and no literal for the proof to claim; the caller handles the
   failure off the [result] itself, as [Store.apply] does. *)
let change_of d (r : result) =
  match r with Unchanged | Failed -> NoChange | Changed d' -> classify ~old:d ~now:d'

let change_to_string = function
  | NoChange -> "no change"
  | Bound { lo; hi } ->
      let part name = function
        | None -> []
        | Some v -> [ Printf.sprintf "%s=%d" name v ]
      in
      "bound " ^ String.concat "," (part "lo" lo @ part "hi" hi)
  | Holes vs -> "holes {" ^ String.concat "," (List.map string_of_int vs) ^ "}"

(* -------------------------------------------------------------- narrowing *)

(* Restore I-D2 on a candidate domain whose bounds may have landed on a hole, and report
   emptiness as [Failed] rather than storing a domain with lo > hi (I-D1). Stale bits
   outside the new bounds are left alone: they cost nothing and rewriting the bitset
   would cost a copy. *)
let settle d =
  let l = ref d.lo in
  while !l <= d.hi && is_hole d !l do
    incr l
  done;
  if !l > d.hi then Failed
  else
    (* terminates at or above [!l], which is known not to be a hole *)
    let h = ref d.hi in
    while is_hole d !h do
      decr h
    done;
    Changed { d with lo = !l; hi = !h }

(* Copy-on-write hole insertion. [None] means "declined" - see [max_hole_span]. *)
let with_hole d v =
  match d.holes with
  | Some h ->
      let i = v - h.base in
      if i < 0 || i >= h.span then None
      else
        let bits = Bytes.copy h.bits in
        set_bit bits i;
        Some { d with holes = Some { h with bits } }
  | None ->
      let span = d.hi - d.lo + 1 in
      if span > max_hole_span then None
      else
        let bits = Bytes.make ((span + 7) / 8) '\000' in
        set_bit bits (v - d.lo);
        Some { d with holes = Some { base = d.lo; span; bits } }

let set_lo d v =
  if v <= d.lo then Unchanged else if v > d.hi then Failed else settle { d with lo = v }

let set_hi d v =
  if v >= d.hi then Unchanged else if v < d.lo then Failed else settle { d with hi = v }

let remove d v =
  if not (mem d v) then Unchanged
  else if v = d.lo then settle { d with lo = d.lo + 1 }
  else if v = d.hi then settle { d with hi = d.hi - 1 }
  else match with_hole d v with None -> Unchanged | Some d' -> settle d'

let fix d v =
  if not (mem d v) then Failed
  else if is_fixed d then Unchanged
  else Changed { lo = v; hi = v; holes = None }

(* Build a domain from an explicit value list, for FlatZinc declarations of the form
   [var {1,3,5}: x]. Gaps become holes. *)
let of_list values =
  match List.sort_uniq Stdlib.compare values with
  | [] -> raise (Bad_domain "empty domain from an empty value list")
  | first :: _ as sorted ->
      let last = List.fold_left (fun _ v -> v) first sorted in
      let d = make first last in
      let rec go d v present =
        if v > last then d
        else
          match present with
          | p :: rest when p = v -> go d (v + 1) rest
          | _ -> (
              match remove d v with
              | Changed d' -> go d' (v + 1) present
              | Unchanged -> go d (v + 1) present
              | Failed -> raise (Bad_domain "of_list: domain became empty"))
      in
      go d first sorted

(* ------------------------------------------------------------------ display *)

let to_string d =
  if is_fixed d then string_of_int d.lo
  else
    match holes_list d with
    | [] -> Printf.sprintf "%d..%d" d.lo d.hi
    | hs ->
        Printf.sprintf "%d..%d \\ {%s}" d.lo d.hi
          (String.concat "," (List.map string_of_int hs))
