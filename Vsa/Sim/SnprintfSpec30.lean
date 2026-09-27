import Vsa.Sim.SnprintfProCommon
import Vsa.Sim.SnprintfSitesPro

/-!
# M3 Layer-3 — `SnprintfSpec30` : svfprintf prologue segment D
## `0x800076bc` (second spill block) → `0x800076f4`

The nine `s2…s11` callee-save spills to `sp+0x1e8…0x230` (Spec26's
`hsv1e8…hsv230` residuals) and the uio/iov init (`resid := 0` at `sp+240`,
`count := 0` at `sp+232`, iov base `sp+352` at `sp+224`, `s5 = s7 := sp+352`).
Generated in the SnprintfSpec22 house style by /tmp/gen_spec30.py.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

