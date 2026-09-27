import Vsa.Sim.SnprintfProCommon
import Vsa.Sim.SnprintfSitesPro
import Vsa.Sim.SnprintfSitesPro3
import Vsa.Sim.SnprintfSitesPro4

/-!
# M3 Layer-3 — `SnprintfSpec29` : svfprintf prologue segment C
## `0x800076a0` (the `jal memset`) → `0x800076bc` (second spill block)

`memset(sp+200, 0, 8)` (mbstate init) fully inlined — small-size `bgeu`
dispatch, computed `jr 12(a3)` into the byte-store chain, 8 × `sb`, `ret` —
then the FILE `_flags` `lhu`/`andi 128`/`beqz`-taken check (the `__SCLE`
bit is clear for the `_svsnprintf_r` string sink).
Generated in the SnprintfSpec22 house style by /tmp/gen_spec29.py.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

