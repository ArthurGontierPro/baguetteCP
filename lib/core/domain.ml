(* Finite integer domains: a bounds pair plus a lazily allocated hole set.

   Rationale for the representation is in docs/ARCHITECTURE.md section 2 - most
   propagation in a linear-heavy workload is bounds reasoning, so the bounds are the fast
   path and holes are only populated by the propagators that actually punch them.

   The hole set is a bitset ([Bytes.t]) rather than a balanced set, because SPEC section
   3.1 requires membership in O(1). Since M21-memory-T3 (D-0222) it is NOT copied per
   removal: a domain's holes are a VERSION of a per-variable LOG that its successors
   share. The log is one mutable bitset (every hole any version of the lineage has) plus
   the removals in the order they were made; a version is "the log's base holes and its
   first [k] removals". Removing a value from the NEWEST version sets one bit and appends
   one entry (16 bytes), where the copy cost span / 8 bytes per pruning and the trail
   kept every copy: 98 % of wordpress's live heap at its refusal (D-0218). Removing from
   an older version forks a new log (one copy, what every removal used to pay), so the
   value semantics a caller sees are those of a persistent set.

   What that costs is I-T1's old guarantee that a [t] shares no mutable state with its
   successors. The new one (docs/INVARIANTS.md I-T1, D-0222 section 4): [undo] -- called
   by [Store.undo_to] for every entry it pops -- truncates the log back to the version the
   entry restores, so a [t] answers exactly the set it was made with for as long as no
   trail entry older than it has been undone, and a read after that raises
   [Stale_version] rather than answering. Each version carries the uid of its last log
   slot, which a truncation and a refill never reproduce, so the refusal is exact.

   Every read tests the bit first, with the loads the copying representation made (the
   version carries the log's base, span and bitset): a clear bit is a hole of no valid
   version, which answers every read of a value still in the domain. A set bit is a hole
   of the newest version (two compares), and of an older one (a trail entry's
   [old]/[now], a pass's snapshot, an Element frame, a D-0124 history) iff it was logged
   before [k]: a scan of at most [deep_scan] entries, else [pos], an int32 per value
   built on the first deep read of that log and kept up to date after. So every read is
   O(1) once [pos] exists, and [pos] exists only for a log something read deep in its
   past. What this costs in time is the set-bit reads of older versions, which Element's
   lazy reasons make by the thousand per node: +2 % of javarouting's instructions per
   node, +1 % of costas's, nothing elsewhere (D-0222 section 6).

   M16-file-review-T1 (D-0186), the costs that grow with the WIDTH, and why none of them
   is on a per-entry path of the engine: [remove] of an interior value copies the bitset
   (O(span / 8), so punching every hole of a domain along one branch is O(span^2 / 8);
   O(1) since D-0222, which appends to the log instead);
   [size] of a domain with holes counts the bits between the bounds (O(span / 8)), and
   [Search.first_fail] asks it per candidate per node; [classify] of a hole entry walks
   the bounds (O(width)) and is asked by the proof side ([Trace]) only, the engine reading
   an entry's kind without it. [span] is at most [max_hole_span] (2^20 values, a 128 KB
   bitset). The lane's domains are at most 10 000 values wide, and none of the three
   reaches 1.5 % of a lane profile (D-0186's table).

   Invariants (docs/INVARIANTS.md):
     I-D1  lo <= hi; an empty domain is never constructed, it is reported as [Failed]
     I-D2  lo and hi are in the domain: holes never sit at a bound
     I-D3  a domain only ever shrinks - every operation here returns a subset *)

(* Bit [i] of [bits] stands for the value [base + i]. [span] is how many values the
   bitset covers; it is fixed when the log is first allocated, at which point it spans
   exactly the bounds then in force. Since domains only shrink (I-D3), every later value
   of the domain is inside [base, base + span). Bits outside the current bounds may be
   stale; [mem] tests the bounds first, so they are harmless.

   THE LOG (D-0222). [bits] holds the BASE holes (those the log was created with, by a
   fork or [affine]; never cleared) and the values [vals.(0 .. len - 1)], each removed by
   one [push] in that order. [uids.(j)] is slot [j]'s stamp, drawn from [next_uid] and
   never reused within the log; [top_uid] is the newest slot's (0 when [len = 0]). [pos]
   is empty, or an int32 per value: the slot that logged it, -1 for a base hole, garbage
   where the bit is clear (never read there). The arrays grow by doubling and are never
   shrunk; [len] is at most [span], because a value is logged only while its bit is
   clear. *)
type log = {
  base : int;
  span : int;
  bits : Bytes.t;
  mutable vals : int array;
  mutable uids : int array;
  mutable len : int;
  mutable top_uid : int;
  mutable next_uid : int;
  mutable pos : Bytes.t;
}

(* A version of [log]: its base holes and the first [k] logged values. [uid] is the stamp
   of slot [k - 1] (0 for [k = 0]), which is how a version knows it has been truncated
   away: see [valid]. [hbase], [hspan] and [hbits] are the log's own (immutable) fields,
   copied so that [is_hole] -- the read every [mem] makes -- costs the loads it cost
   before D-0222 and not one more through [log] (3 words a version, measured on
   javarouting, D-0222 section 6). Immutable, seven words. *)
type holes = { log : log; k : int; uid : int; hbase : int; hspan : int; hbits : Bytes.t }
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

   [change] is a sibling of [result]: [classify] below recovers it from the [old] and
   [now] a trail entry records. Carrying it in [Changed] instead, as ARCHITECTURE section 2
   reads, would be a change here and in [Store.apply] (M22-review-T6). *)
type change =
  | NoChange
  | Bound of { lo : int option; hi : int option }
  | Holes of int list

exception Bad_domain of string

(* A read of a version whose log has been truncated below it (D-0222, I-T1): the domain
   belonged to a branch the trail has undone. Raised rather than answered, because the
   answer would be the present's, not the version's. *)
exception Stale_version of string

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

let[@inline] get_bit bits i =
  Char.code (Bytes.unsafe_get bits (i lsr 3)) land (1 lsl (i land 7)) <> 0

let set_bit bits i =
  let byte = i lsr 3 in
  Bytes.unsafe_set bits byte
    (Char.unsafe_chr (Char.code (Bytes.unsafe_get bits byte) lor (1 lsl (i land 7))))

let clear_bit bits i =
  let byte = i lsr 3 in
  Bytes.unsafe_set bits byte
    (Char.unsafe_chr
       (Char.code (Bytes.unsafe_get bits byte) land lnot (1 lsl (i land 7)) land 0xff))

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

(* --------------------------------------------------------------- the log (D-0222) *)

let fresh_log ~base ~span ~bits =
  {
    base;
    span;
    bits;
    vals = [||];
    uids = [||];
    len = 0;
    top_uid = 0;
    next_uid = 1;
    pos = Bytes.empty;
  }

(* The version the store holds after its last removal: every slot of the log is its. *)
let[@inline] is_newest h = h.k = h.log.len && h.uid = h.log.top_uid

(* Not truncated away: slot [k - 1] still holds the removal this version ended with. A
   version of [k = 0] is the base holes, which no truncation touches. *)
let[@inline] valid h =
  h.k <= h.log.len && (h.k = 0 || Array.unsafe_get h.log.uids (h.k - 1) = h.uid)

let stale h =
  raise
    (Stale_version
       (Printf.sprintf
          "I-T1 (D-0222): a domain version of %d removals was read after its log was \
           truncated to %d (its branch was undone)"
          h.k h.log.len))

(* Append [v] (bit index [i], clear) and return the version that ends with it. *)
let push lg i v =
  let j = lg.len in
  if j = Array.length lg.vals then (
    (* from empty: a log made by [affine] or a fork may never be appended to *)
    let cap = Stdlib.max (j + 1) (Stdlib.min lg.span (Stdlib.max 4 (2 * j))) in
    let grow a = Array.append a (Array.make (cap - j) 0) in
    lg.vals <- grow lg.vals;
    lg.uids <- grow lg.uids);
  let uid = lg.next_uid in
  lg.next_uid <- uid + 1;
  Array.unsafe_set lg.vals j v;
  Array.unsafe_set lg.uids j uid;
  lg.len <- j + 1;
  lg.top_uid <- uid;
  set_bit lg.bits i;
  if Bytes.length lg.pos > 0 then Bytes.set_int32_le lg.pos (4 * i) (Int32.of_int j);
  { log = lg; k = j + 1; uid; hbase = lg.base; hspan = lg.span; hbits = lg.bits }

(* Pop every slot at or above [k], clearing its bit. *)
let truncate lg k =
  if k < lg.len then (
    for j = lg.len - 1 downto k do
      clear_bit lg.bits (Array.unsafe_get lg.vals j - lg.base)
    done;
    lg.len <- k;
    lg.top_uid <- (if k = 0 then 0 else lg.uids.(k - 1)))

(* Above this many slots past a version, a deep read builds [pos] rather than scan. *)
let deep_scan = 8

let build_pos lg =
  let p = Bytes.make (4 * lg.span) '\255' in
  for j = 0 to lg.len - 1 do
    Bytes.set_int32_le p (4 * (lg.vals.(j) - lg.base)) (Int32.of_int j)
  done;
  lg.pos <- p

(* Bit [i] is set: was its value logged at or after slot [h.k]? (Then it is not a hole of
   [h].) *)
let logged_after h i =
  let lg = h.log in
  if lg.len - h.k <= deep_scan then (
    let v = lg.base + i in
    let found = ref false and j = ref h.k in
    while (not !found) && !j < lg.len do
      if Array.unsafe_get lg.vals !j = v then found := true;
      incr j
    done;
    !found)
  else (
    if Bytes.length lg.pos = 0 then build_pos lg;
    Int32.to_int (Bytes.get_int32_le lg.pos (4 * i)) >= h.k)

(* Bit [i] (in range) is set: is it a hole of version [h]? Of the newest version, yes;
   of an older one iff it was logged before [k]; a STALE version refuses. *)
let set_bit_is_hole h i =
  is_newest h || if valid h then not (logged_after h i) else stale h

(* A fresh bitset holding exactly [h]'s holes: the log's, minus what came after [k]. *)
let materialise h =
  if not (valid h) then stale h;
  let lg = h.log in
  let bits = Bytes.copy lg.bits in
  for j = h.k to lg.len - 1 do
    clear_bit bits (lg.vals.(j) - lg.base)
  done;
  bits

(* ------------------------------------------------------------- construction *)

let make lo hi =
  if lo > hi then raise (Bad_domain (Printf.sprintf "empty initial domain %d..%d" lo hi));
  { lo; hi; holes = None }

let singleton v = { lo = v; hi = v; holes = None }

(* ----------------------------------------------------------------- querying *)

let lo d = d.lo
let hi d = d.hi
let is_fixed d = d.lo = d.hi

let[@inline] is_hole d v =
  match d.holes with
  | None -> false
  | Some h ->
      (* The bit first: a clear bit is a hole of no valid version (bits only gain values
         along the log), which answers the common read -- a value still in the domain --
         with the loads the copying representation made. A stale version is refused on
         a set bit; on a clear one only [check_version] (which D-0222's test asks of
         every photograph from an undone branch) sees it, to keep this path as it was. *)
      let i = v - h.hbase in
      i >= 0 && i < h.hspan && get_bit h.hbits i && set_bit_is_hole h i

(* Raise [Stale_version] if [d]'s holes are a version its log has truncated away. A read
   refuses by itself on a set bit; this asks on any (the test of D-0222 asks it of every
   photograph from an undone branch). *)
let check_version d = match d.holes with Some h when not (valid h) -> stale h | _ -> ()
let mem d v = v >= d.lo && v <= d.hi && not (is_hole d v)
let value d = if is_fixed d then Some d.lo else None

let size d =
  let width = d.hi - d.lo + 1 in
  match d.holes with
  | None -> width
  | Some h ->
      let lg = h.log in
      let i0 = max 0 (d.lo - lg.base) in
      let i1 = min (lg.span - 1) (d.hi - lg.base) in
      let n = count_bits lg.bits i0 i1 in
      if is_newest h then width - n
      else (
        (* the log's count less the values logged after [k] within the bounds *)
        if not (valid h) then stale h;
        let later = ref 0 in
        for j = h.k to lg.len - 1 do
          let i = Array.unsafe_get lg.vals j - lg.base in
          if i >= i0 && i <= i1 then incr later
        done;
        width - (n - !later))

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

   Who asks: [Trace], once per trail entry it writes a line for, and the engine's debug
   messages. The propagation path reads an entry's bound moves directly ([Engine.lo_moved],
   [Engine.hi_moved]) and never calls it. The bound comparison is O(1) and returns first,
   so the common case (a bound move) costs four integer comparisons and no allocation
   beyond the result. Only the interior-hole case walks the
   interval, and it is bounded by the span of a domain that is already known to have a
   bitset. That is the right way round: the rare case pays.

   Precondition: [now] is a subset of [old] (I-D3), which is what [Store.apply] has
   already asserted by the time the engine gets here. If it is not - if a bound somehow
   widened - the widened side reports as "did not move" rather than lying about a
   literal that did not become true. *)
(* Same bounds, so anything that went is strictly interior. Walk downwards and prepend,
   so the list comes out ascending without a reversal. *)
let classify_walk ~old ~now =
  let removed = ref [] in
  for v = now.hi downto now.lo do
    if is_hole now v && not (is_hole old v) then removed := v :: !removed
  done;
  match !removed with [] -> NoChange | vs -> Holes vs

let classify ~old ~now =
  if old.lo <> now.lo || old.hi <> now.hi then
    Bound
      {
        lo = (if now.lo > old.lo then Some now.lo else None);
        hi = (if now.hi < old.hi then Some now.hi else None);
      }
  else
    match (old.holes, now.holes) with
    | Some ho, Some hn when ho.log == hn.log && ho.k <= hn.k && valid ho && valid hn ->
        (* D-0222: one log, so what [now] has and [old] has not is exactly the slots
           [ho.k .. hn.k - 1] (a logged value was clear in every version before it, and
           base holes are in both). Usually one slot. Same answer as the walk below,
           which BAGUETTE_DEBUG cross-checks, without walking the width. *)
        let lg = hn.log in
        let removed = ref [] in
        for j = ho.k to hn.k - 1 do
          let v = lg.vals.(j) in
          if v >= now.lo && v <= now.hi then removed := v :: !removed
        done;
        let r =
          match List.sort_uniq Int.compare !removed with [] -> NoChange | vs -> Holes vs
        in
        if Debug.enabled then
          Debug.check "D-0222: classify from the log agrees with the walk" (fun () ->
              r = classify_walk ~old ~now);
        r
    | _ -> classify_walk ~old ~now

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

(* Hole insertion, by appending to the log (D-0222). [None] means "declined" - see
   [max_hole_span]. A domain with no hole yet gets a fresh log spanning its bounds; one
   whose version is the newest of its log extends it in place; one whose version is OLDER
   (a caller removing twice from the same value, or a store sharing a log another store
   extended) forks: a fresh log whose base holes are that version's set, one copy of the
   bitset, which is what every removal paid before D-0222. *)
(* How many removals forked a log, for the test that a store never does (every removal
   it makes is from its own newest version, because [undo] truncates). *)
let forks = ref 0

let with_hole d v =
  match d.holes with
  | Some h ->
      let lg = h.log in
      let i = v - lg.base in
      if i < 0 || i >= lg.span then None
      else
        let lg =
          if is_newest h then lg
          else (
            incr forks;
            fresh_log ~base:lg.base ~span:lg.span ~bits:(materialise h))
        in
        Some { d with holes = Some (push lg i v) }
  | None ->
      let span = d.hi - d.lo + 1 in
      if span > max_hole_span then None
      else
        let lg = fresh_log ~base:d.lo ~span ~bits:(Bytes.make ((span + 7) / 8) '\000') in
        Some { d with holes = Some (push lg (v - d.lo) v) }

(* The trail's half of D-0222: [Store.undo_to] pops an entry that replaced [old] by [now]
   and calls this before writing [old] back. If [now]'s version is past [old]'s on the
   same log, the slots between are this entry's (or a later pop's leftovers) and go; if
   [now] holds a log [old] does not (the entry's removal created or forked it), that log
   dies with the entry and is emptied, so a version of it read later refuses. An entry
   that moved a bound shares its version with [old] and costs this one comparison. *)
let[@inline] undo ~old ~now =
  match now.holes with
  | None -> ()
  | Some hn -> (
      match old.holes with
      | Some ho when ho.log == hn.log -> if hn.k > ho.k then truncate hn.log ho.k
      | Some _ | None -> truncate hn.log 0)

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

(* ------------------------------------------------------------------ display *)

let to_string d =
  if is_fixed d then string_of_int d.lo
  else
    match holes_list d with
    | [] -> Printf.sprintf "%d..%d" d.lo d.hi
    | hs ->
        Printf.sprintf "%d..%d \\ {%s}" d.lo d.hi
          (String.concat "," (List.map string_of_int hs))

(* ---------------------------------------------------------------- views (M4-T0) *)

(* The image of a domain under [x |-> (if negated then -x else x) + offset].

   This is the materialising form, for printing, for tests and for a caller that
   genuinely wants a [Domain.t] of a view. It is NOT the read path: [View.lo],
   [View.hi] and [View.mem] translate a single integer in O(1) and allocate nothing,
   which is what a propagator uses. Building a domain per read would make a view
   cost more than the auxiliary variable it exists to avoid.

   It is not the test helper [Domain_helper.of_list] either, deliberately: that one
   builds holes no trail entry explains, which is why M22-review-T5 moved it out of
   [lib/] (docs/INVARIANTS.md I-X10), and it is O(size) in removals where this is one
   pass over the bitset. The map is a bijection on values, so I-D2 (bounds are not
   holes) transports with no settling: the image of a non-hole bound is a non-hole
   bound. *)
let affine d ~negated ~offset =
  if negated && (d.lo = min_int || d.hi = min_int) then
    raise (Bad_domain "affine: negating min_int");
  let l = (if negated then -d.hi else d.lo) + offset
  and h = (if negated then -d.lo else d.hi) + offset in
  let fresh base span bits =
    let lg = fresh_log ~base ~span ~bits in
    Some { log = lg; k = 0; uid = 0; hbase = base; hspan = span; hbits = bits }
  in
  match d.holes with
  | None -> { lo = l; hi = h; holes = None }
  | Some hs when not negated ->
      let lg = hs.log in
      { lo = l; hi = h; holes = fresh (lg.base + offset) lg.span (materialise hs) }
  | Some hs ->
      (* Old bit [i] stands for [base + i], whose image is [offset - base - i]. So the
         image's bitset is the old one reversed, over the mirrored base. *)
      let lg = hs.log in
      let old_bits = materialise hs in
      let base = offset - (lg.base + lg.span - 1) in
      let bits = Bytes.make (Bytes.length old_bits) '\000' in
      for j = 0 to lg.span - 1 do
        if get_bit old_bits (lg.span - 1 - j) then set_bit bits j
      done;
      { lo = l; hi = h; holes = fresh base lg.span bits }
