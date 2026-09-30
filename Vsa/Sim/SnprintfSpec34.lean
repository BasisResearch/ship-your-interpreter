import Vsa.Sim.SnprintfProCommon
import Vsa.Sim.SnprintfSitesPro
import Vsa.Sim.SnprintfSitesPro4
import Vsa.Sim.SnprintfSites2

/-!
# M3 Layer-3 — `SnprintfSpec34` : svfprintf prologue segment H
## `0x80007798 → 0x80008534` — the first `%lld` dispatch, wide post

A self-contained twin of `SnprintfSpec14.parseDispatch_l_full_spec` whose
post carries **all** the registers `SnprintfSpec16.parseToPrintEntry_spec`
and `SnprintfSpec26`'s `hmidregs` need at the `'l'` handler entry
(`x2/x3/x6/x8/x9/x10/x12/x18/x19/x20/x21/x22/x23/x25/x26/x27`) plus
`c'.σ.mem = c.σ.mem`.  The table slot bytes are caller pins (`ParseSlotPinned
0x6c` unpacked; `parseSlot_l` in SnprintfSpec13 proves the same data).
Generated in the SnprintfSpec22 house style by /tmp/gen_spec34.py.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

