import Vsa.Sim.SnprintfProCommon
import Vsa.Sim.SnprintfSitesPro
import Vsa.Sim.StrlenSites
import Vsa.Sim.StrlenSpec

/-!
# M3 Layer-3 — `SnprintfSpec28` : svfprintf prologue segment B
## `0x8000768c` (the `jal strlen`) → `0x800076a0` (the `jal memset`)

`strlen(decimal_point)` for the concrete static string `"."` at `0x80019770`
(from `_localeconv_r`), fully inlined (22 `StrlenSites` steps: aligned entry,
one magic word probe, byte tail, exit `a0 = 1`), the result spill to `sp+72`,
and the `memset(sp+200, 0, 8)` argument setup.
Generated in the SnprintfSpec22 house style by /tmp/gen_spec28.py.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

