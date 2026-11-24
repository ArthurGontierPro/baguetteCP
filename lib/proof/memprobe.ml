(* M21-memory-T1 (D-0218). INSTRUMENTATION, KEPT AS A PATCH (memprobe.patch in
   /cluster/arthur/baguette-results/memory/), never merged.

   Under BAGUETTE_MEMPROBE=<file>, writes at a few points of a run the live heap split by
   KIND. A kind is a list of roots registered by name; the split is cumulative in
   registration order: kind k is charged with the words reachable from roots 1..k minus
   those reachable from roots 1..k-1, so a block shared by two kinds goes to the first one
   registered. [Gc.stat] gives the live words after a full major cycle, and what the roots
   do not reach is reported as [unattributed].

   Probe points: [probe] called by name (parse, compile, proofopen), the search's node
   count crossing 1 and 1000, the heap ([Gc.quick_stat]'s heap_words at the end of a
   major cycle, i.e. what --max-heap-mb reads) crossing 1, 2, 4, 8, 16 and 32 GiB, and the
   exit. A threshold crossing only arms a flag; the probe runs at the next [tick] (every
   [poll_runs] propagator runs, and every node), where the roots are consistent. *)

let path = Sys.getenv_opt "BAGUETTE_MEMPROBE"
let enabled = match path with None | Some "" -> false | Some _ -> true
let oc = lazy (match path with Some p -> open_out p | None -> stderr)

type root = { label : string; get : unit -> Obj.t list }

let roots : root list ref = ref []

(* Re-registering a label replaces its getter and keeps its position. *)
let register label get =
  if enabled then
    if List.exists (fun r -> r.label = label) !roots then
      roots := List.map (fun r -> if r.label = label then { label; get } else r) !roots
    else roots := !roots @ [ { label; get } ]

let counters : (string * (unit -> int)) list ref = ref []

let count label get =
  if enabled then
    counters := List.filter (fun (l, _) -> l <> label) !counters @ [ (label, get) ]

let nodes = ref 0

(* What the search was doing at the last marker (set in Search: conflict, learn_clause,
   pb_analysis; "propagate" at each node). Printed with every probe. *)
let phase = ref "front"
let t0 = Sys.time ()

(* ONE pass over the roots, in order, with a visited set outside the OCaml heap (a
   Bigarray, open addressing on the block's address), so that a block is charged to the
   first kind that reaches it and the probe does not grow the heap it measures. Must run
   right after [Gc.full_major]: the major heap of OCaml 5.1 does not move, and the
   minor heap is then empty, so an address is stable for the length of the walk.

   Per kind: words (headers included), blocks, string bytes, and a histogram of block
   shapes (tag, size) -- the evidence T2 needs to say what is header, what is a list
   cell, what is a boxed literal. *)
module Walk = struct
  type stats = {
    mutable words : int;
    mutable blocks : int;
    mutable str_words : int;
    mutable flat_words : int; (* no-scan blocks other than strings: floats, customs *)
    shapes : (int, int ref) Hashtbl.t; (* tag * 4096 + min size 4095 -> count *)
  }

  let new_stats () =
    { words = 0; blocks = 0; str_words = 0; flat_words = 0; shapes = Hashtbl.create 64 }

  let addr (o : Obj.t) : int = (Obj.magic o : int) lor 1

  type set = {
    mutable tbl : (int, Bigarray.int_elt, Bigarray.c_layout) Bigarray.Array1.t;
    mutable mask : int;
    mutable n : int;
  }

  let create_set cap =
    let rec pow2 k = if k >= cap then k else pow2 (2 * k) in
    let c = pow2 1024 in
    let tbl = Bigarray.Array1.create Bigarray.int Bigarray.c_layout c in
    Bigarray.Array1.fill tbl 0;
    { tbl; mask = c - 1; n = 0 }

  let hash a = (a * 0x9E3779B97F4A7C1) lsr 7

  let rec add s a =
    if 2 * (s.n + 1) > s.mask then grow s;
    let tbl = s.tbl and mask = s.mask in
    let rec go i =
      let v = Bigarray.Array1.unsafe_get tbl i in
      if v = 0 then (
        Bigarray.Array1.unsafe_set tbl i a;
        s.n <- s.n + 1;
        true)
      else if v = a then false
      else go ((i + 1) land mask)
    in
    go (hash a land mask)

  and grow s =
    let old = s.tbl in
    let c = 2 * (s.mask + 1) in
    let tbl = Bigarray.Array1.create Bigarray.int Bigarray.c_layout c in
    Bigarray.Array1.fill tbl 0;
    s.tbl <- tbl;
    s.mask <- c - 1;
    s.n <- 0;
    for i = 0 to Bigarray.Array1.dim old - 1 do
      let v = Bigarray.Array1.unsafe_get old i in
      if v <> 0 then ignore (add s v)
    done

  (* the explicit stack, a growable array of values *)
  let stack = ref (Array.make 4096 (Obj.repr 0))
  let sp = ref 0

  let push o =
    if !sp >= Array.length !stack then begin
      let a = Array.make (2 * !sp) (Obj.repr 0) in
      Array.blit !stack 0 a 0 !sp;
      stack := a
    end;
    Array.unsafe_set !stack !sp o;
    incr sp

  let closinfo_startenv o =
    let info = Obj.raw_field o 1 in
    Nativeint.to_int (Nativeint.shift_right_logical (Nativeint.shift_left info 8) 9)

  let walk set st root =
    let visit o =
      if Obj.is_block o then begin
        let o =
          if Obj.tag o = Obj.infix_tag then
            Obj.add_offset o (Int32.of_int (-(Obj.size o * (Sys.word_size / 8))))
          else o
        in
        if add set (addr o) then push o
      end
    in
    visit root;
    while !sp > 0 do
      decr sp;
      let o = Array.unsafe_get !stack !sp in
      Array.unsafe_set !stack !sp (Obj.repr 0);
      let tag = Obj.tag o and size = Obj.size o in
      st.words <- st.words + size + 1;
      st.blocks <- st.blocks + 1;
      let key = (tag * 4096) + min size 4095 in
      (match Hashtbl.find_opt st.shapes key with
      | Some r -> incr r
      | None -> Hashtbl.add st.shapes key (ref 1));
      if tag = Obj.closure_tag then
        for i = closinfo_startenv o to size - 1 do
          visit (Obj.field o i)
        done
      else if tag = Obj.string_tag then st.str_words <- st.str_words + size + 1
      else if tag >= Obj.no_scan_tag then st.flat_words <- st.flat_words + size + 1
      else if tag = Obj.cont_tag then ()
      else
        for i = 0 to size - 1 do
          visit (Obj.field o i)
        done
    done
end

let shape_name key =
  let tag = key / 4096 and size = key mod 4096 in
  let t =
    if tag = Obj.closure_tag then "closure"
    else if tag = Obj.string_tag then "string"
    else if tag = Obj.double_array_tag then "floatarray"
    else if tag = Obj.custom_tag then "custom"
    else if tag = Obj.lazy_tag then "lazy"
    else if tag = Obj.forward_tag then "forward"
    else string_of_int tag
  in
  Printf.sprintf "%s/%s" t (if size = 4095 then "big" else string_of_int size)

let in_probe = ref false

let probe tag =
  if enabled && not !in_probe then begin
    in_probe := true;
    let oc = Lazy.force oc in
    let t_start = Sys.time () in
    let hdr = Printf.sprintf "%s\t%.1f\t%d" tag (t_start -. t0) !nodes in
    Printf.fprintf oc "phase\t%s\t%s\n" hdr !phase;
    let q = Gc.quick_stat () in
    Printf.fprintf oc "gc\t%s\theap_words_quick\t%d\n" hdr q.Gc.heap_words;
    Printf.fprintf oc "gc\t%s\ttop_heap_words_quick\t%d\n" hdr q.Gc.top_heap_words;
    (try
       let ic = open_in "/proc/self/status" in
       (try
          while true do
            let l = input_line ic in
            if String.starts_with ~prefix:"VmRSS" l || String.starts_with ~prefix:"VmHWM" l
            then
              Printf.fprintf oc "gc\t%s\t%s\n" hdr
                (String.concat "" (String.split_on_char '\t' l))
          done
        with End_of_file -> ());
       close_in ic
     with Sys_error _ -> ());
    Gc.full_major ();
    let st = Gc.stat () in
    Printf.fprintf oc "gc\t%s\tlive_words\t%d\n" hdr st.Gc.live_words;
    Printf.fprintf oc "gc\t%s\theap_words\t%d\n" hdr st.Gc.heap_words;
    Printf.fprintf oc "gc\t%s\tfree_words\t%d\n" hdr st.Gc.free_words;
    Printf.fprintf oc "gc\t%s\tlive_blocks\t%d\n" hdr st.Gc.live_blocks;
    Printf.fprintf oc "gc\t%s\tfragments\t%d\n" hdr st.Gc.fragments;
    let set = Walk.create_set (2 * (st.Gc.live_blocks + 1024)) in
    let total = ref 0 in
    List.iter
      (fun r ->
        let objs = try r.get () with _ -> [] in
        let s = Walk.new_stats () in
        List.iter (fun o -> Walk.walk set s o) objs;
        total := !total + s.Walk.words;
        Printf.fprintf oc "kind\t%s\t%s\t%d\t%d\t%d\t%d\n" hdr r.label s.Walk.words
          s.Walk.blocks s.Walk.str_words s.Walk.flat_words;
        let l = Hashtbl.fold (fun k v a -> (k, !v) :: a) s.Walk.shapes [] in
        let l = List.sort (fun (_, a) (_, b) -> compare b a) l in
        List.iteri
          (fun i (k, n) ->
            if i < 12 then
              Printf.fprintf oc "shape\t%s\t%s\t%s\t%d\n" hdr r.label (shape_name k) n)
          l;
        (* and the 8 heaviest shapes by words (count * (size + 1)), "big" counted at 4096 *)
        let w (k, n) = n * ((k mod 4096) + 1) in
        let l = List.sort (fun a b -> compare (w b) (w a)) l in
        List.iteri
          (fun i (k, n) ->
            if i < 8 then
              Printf.fprintf oc "wshape\t%s\t%s\t%s\t%d\n" hdr r.label (shape_name k) n)
          l)
      !roots;
    Printf.fprintf oc "kind\t%s\tunattributed\t%d\n" hdr (st.Gc.live_words - !total);
    List.iter
      (fun (l, g) ->
        let v = try g () with _ -> -1 in
        Printf.fprintf oc "count\t%s\t%s\t%d\n" hdr l v)
      !counters;
    Printf.fprintf oc "probe_seconds\t%s\t%.1f\n%!" hdr (Sys.time () -. t_start);
    in_probe := false
  end

let gib = 1024 * 1024 * 1024 / 8
let thresholds = ref [ gib / 2; 1 * gib; 2 * gib; 4 * gib; 8 * gib; 16 * gib; 32 * gib ]

(* BAGUETTE_MEMPROBE_STOP_GIB=g: after the probe at the g GiB crossing, exit (rc 0, no exit
   probe). The refusal point is 16 GiB; walking a heap past it costs minutes per probe. *)
let stop_gib =
  match Sys.getenv_opt "BAGUETTE_MEMPROBE_STOP_GIB" with
  | Some s -> ( try int_of_string s with _ -> max_int)
  | None -> max_int

let stopped = ref false
let pending : string option ref = ref None

let tick () =
  if enabled then
    match !pending with
    | None -> ()
    | Some tag ->
        pending := None;
        probe tag;
        let g =
          try Scanf.sscanf tag "heap%dG" (fun g -> g) with _ -> 0
        in
        if g >= stop_gib then begin
          stopped := true;
          Printf.fprintf (Lazy.force oc) "stop\t%s\n%!" tag;
          exit 0
        end

let node n =
  if enabled then begin
    nodes := n;
    phase := "node";
    if n = 1 || n = 1000 || n = 10_000 || n = 100_000 || n = 1_000_000 || n = 10_000_000
    then probe (Printf.sprintf "node%d" n);
    tick ()
  end

let in_alarm = Sys.getenv_opt "BAGUETTE_MEMPROBE_IN_ALARM" = Some "1"

let () =
  if enabled then begin
    ignore
      (Gc.create_alarm (fun () ->
           let h = (Gc.quick_stat ()).Gc.heap_words in
           (match !thresholds with
           | t :: rest when h >= t ->
               let rec drop t = function t' :: r when h >= t' -> drop t' r | r -> (t, r) in
               let t, r = drop t rest in
               thresholds := r;
               pending :=
                 Some
                   (if t < gib then Printf.sprintf "heap%dM" (t * 8 / 1024 / 1024)
                    else Printf.sprintf "heap%dG" (t / gib))
           | _ -> ());
         (* BAGUETTE_MEMPROBE_IN_ALARM=1: probe here, at the end of the major cycle, rather
            than at the next tick. A heap that crosses a threshold inside ONE step (a
            conflict analysis) never reaches a tick before the budget refuses it. *)
         if in_alarm && !pending <> None && not !in_probe then tick ()));
    at_exit (fun () -> if not !stopped then probe "exit")
  end

