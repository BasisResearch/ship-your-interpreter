import Vsa.Sim.SnprintfSitesFlush
import Vsa.Sim.SnprintfSpec6
import Vsa.Sim.ValueEqualSpec3
import Vsa.Sim.ObsAvoid

/-!
# M3 Layer-3 — `SnprintfSpec7` : the exit-restore + flush hops, composed (`_fl`)

From the digit-loop exit `0x80008358` (the state `signToDigits_neg_spec`
delivers), step the restore block — five spill reloads folding back to their
stored 64-bit values (`ve_sext_reassemble`), `len = top − cursor` (32-bit
`subw`), the width test (`width < len`, not taken for `%lld`), the **sign-byte
read-back** `lbu t5,167(sp)`, `t6 := 0` — and the three hops, landing at the
PRINT entry `0x8000782c` with `a6 = len+1` (sign included) and every restored
register pinned.  The spill-slot contents arrive as `sdData_val`-shaped
hypotheses — exactly what the entry block stored (`SnprintfSpec5`) and the
digit loop preserved (`DigitFrame`); wiring those through `loopEntry_spec`'s
postcondition is the remaining glue, together with the PRINT/iov segment and
`__ssprint_r` + memcpy.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

