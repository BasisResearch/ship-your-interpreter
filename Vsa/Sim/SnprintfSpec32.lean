import Vsa.Sim.SnprintfProCommon
import Vsa.Sim.SnprintfSitesPro
import Vsa.Sim.SnprintfSitesRet
import Vsa.Sim.SnprintfSitesRet3
import Vsa.Sim.SnprintfSitesRet4
import Vsa.Sim.SnprintfSitesRet5

/-!
# M3 Layer-3 — `SnprintfSpec32` : svfprintf prologue segment F
## `0x80007728 → 0x8000775c` — parse pass 1, the `'%'` recognition

Reuses the `SnprintfSitesRet*` batteries (the same instructions run on the
NUL exit path verified in `SnprintfSpec22`); here the mbtowc reads the
concrete `'%'` (`0x25`) — the first byte of the static `"%lld"` template —
returns 1, and the `beq a5,s3` dispatches into the `%`-directive block.
Generated in the SnprintfSpec22 house style by /tmp/gen_spec32.py.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

