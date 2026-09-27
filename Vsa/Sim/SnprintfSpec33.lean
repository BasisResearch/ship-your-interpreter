import Vsa.Sim.SnprintfProCommon
import Vsa.Sim.SnprintfSitesPro
import Vsa.Sim.SnprintfSitesPro4

/-!
# M3 Layer-3 — `SnprintfSpec33` : svfprintf prologue segment G
## `0x8000775c → 0x80007798` — the `%`-directive entry + parse-state init

Establishes exactly the register block the `%lld` dispatch consumes: flags
`t1 = 0`, width `s4 = -1`, bound `s10 = 90`, table base `s6 = 0x8001a0fc`,
`s11 = 0`, cursor `s9 = vfmt+1` with `s8 = 'l'`; the sign-byte slot at
`sp+167` zeroed; the cursor slot at `sp+0` bumped to `vfmt+1`.
Generated in the SnprintfSpec22 house style by /tmp/gen_spec33.py.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

