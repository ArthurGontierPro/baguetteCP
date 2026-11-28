(* --time-limit BEFORE THE SEARCH (M22-review-bugs, D-0263).

   The search polls its own stop (bin/main.ml's [config.stop]: every node, every 128
   propagator runs, inside a conflict's trace). Nothing before it did: the parse, the
   compile (declarations, the case split of int_times/int_div, the rows), the .opb's
   splice and [Encoding.start_proof] (the direct encodings, written into the .pbp) never
   looked at a clock, so a model whose encoding is long ignored --time-limit entirely. The
   fuzz lane's `wide` stream found 264 of 2 000 such runs (D-0258): `int_times` over a
   2^21-wide variable, no output at 100 s under `--time-limit 10`.

   THE RULE. The phases before the search call [tick] with a WEIGHT, roughly the bytes of
   work just done: a committed .opb row, a proof line (its length), a value of a direct
   encoding, a Boolean of an arithmetic ladder, a 64 KiB block of the .opb splice. Every
   [every] units of weight the clock is read once, through the closure bin/main.ml armed
   ([arm]); when it says the deadline is past, [tick] raises [Reached]. Disarmed (no
   --time-limit, and from the search on), [tick] is a subtraction and a comparison.

   WHERE [tick] IS CALLED, so that the exception never leaves a line half written: before a
   proof line enters the channel ([Writer.write_buf], before [enter]), before an .opb row
   is written ([Opb.output_row], once its buffer is built, and [Encoding.commit]), and
   between two iterations of a loop. A [Reached] therefore abandons at most a line that was
   never on the page.

   IN THE SEARCH the search's own poll stops the run at the limit; the deadline stays armed
   as a backstop, through [on_reached], and only proof lines tick there.

   WHAT A STOP HERE PRODUCES is bin/main.ml's (exit_time_limit): `=====UNKNOWN=====`, a
   `limit:` line with `at=<phase>`, exit 0, as a search cut by the limit. The proof: when
   the stop comes during [Encoding.start_proof], the .opb is complete and the .pbp is a
   valid prefix, so it is ENDED (`conclusion NONE`, [Writer.conclude_interrupted]) and the
   checker accepts it for what it claims, nothing. Before that the .opb itself is
   incomplete: there is no proof, and stderr says so (INCOMPLETE, as exit 5 and 6 do).

   THE GRACE. bin/main.ml arms the deadline at the limit PLUS [grace] seconds, so a stop
   before the search happens only when the encoding itself is long. Without it a short
   limit (the fuzz lane's `limit` stream runs `-t 1` to `-t 20` milliseconds, and process
   start-up alone is 4 ms) would stop most runs in the compile, before the .opb exists,
   and they would lose the proof a few milliseconds more would have given them; with it
   they reach the search, which stops them at its first node with an ended proof, exactly
   as before D-0263. The tolerance a user can count on is therefore: the limit plus
   [grace], plus the time between two clock reads (one per [every] units, a few
   milliseconds of work).

   GRANULARITY AND COST. [every] is 2^20 units: one clock read per MB of proof text or per
   16 K rows. A normal model's compile writes far less than that, so it reads the clock a
   handful of times; the cost on handball12 and costas13 is in D-0263 (instructions, not
   measurable). *)

exception Reached

(* bin/main.ml's test of the clock: true once the armed deadline is past. *)
let armed : (unit -> bool) option ref = ref None

(* The seconds a stop before the search waits past the limit (see THE GRACE). *)
let grace = 1.0

(* Units of weight between two clock reads. A ref only so that test_endtoend.ml can stop
   a small model's compile and proof at their first tick; nothing else sets it. *)
let every = ref (1 lsl 20)
let left = ref !every

let arm f =
  armed := Some f;
  left := !every

let disarm () = armed := None

(* What a past deadline does: raise [Reached] before the search. From the search on,
   bin/main.ml replaces it with the stop a second signal makes (end the proof where it
   stands, report, exit), the BACKSTOP for one search step too long for the search's own
   poll: an alldiff whose Hall derivations wrote 540 MB of proof in one propagator run
   overran `--time-limit 10` by 10 s and died against the memory cap (D-0263 section 4). *)
let on_reached : (unit -> unit) ref = ref (fun () -> raise Reached)

let check () =
  left := !every;
  match !armed with Some f when f () -> !on_reached () | _ -> ()

let tick n =
  left := !left - n;
  if !left < 0 then check ()
