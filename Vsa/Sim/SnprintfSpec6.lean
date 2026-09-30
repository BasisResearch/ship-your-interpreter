import Vsa.Sim.SnprintfSpec5
import Vsa.Sim.ObsAvoid

/-!
# M3 Layer-3 — `SnprintfSpec6` : sign block → digit buffer, composed (`_sn6`)

Glues the three verified segments end-to-end for the negative arm:

* `splitToEntry_spec` — the flag-guard hop `0x800080f8 bltz s4` (both arms) and
  the optional flag mask `0x800080fc andi t1,t1,-129`, joining at the fast/multi
  split `0x80008100`.  Memory untouched; the grouping bit of `t1` stays clear
  (`flagmask_sn6`).
* `signToDigits_neg_spec` — the composed theorem: from the sign-block entry
  `0x800080e4` with the loaded argument `v` negative and magnitude `> 9`, the
  machine emits `'-'` into `sp+167`, negates, threads the flag guard, runs the
  loop entry and the whole decimal loop, and exits at `0x80008358` with the
  complete decimal digit string of the magnitude in the descending buffer.
  The value bridge `((0#64) - v).toNat = (-v.toInt).toNat` (INT64_MIN-safe)
  ties the buffer content to `intToString v.toInt`'s magnitude digits
  (`intToString_signblock_sn4`, `SnprintfSpec4`).

The sign byte's survival across the loop's stores (it sits at `sp+167`,
disjoint from the spill area `sp+[32,128)` and the digit window
`sp+[328,348)`) is a memory-frame fact the flush segment will need; stating it
requires a frame conjunct on `decimalLoop_spec`'s postcondition and is the
next piece of plumbing, together with the single-digit fast path and the
flush itself.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

