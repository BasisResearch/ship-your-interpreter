import Vsa.Sim.SnprintfProCommon
import Vsa.Sim.SnprintfSitesPro
import Vsa.Sim.SnprintfSitesPro2

/-!
# M3 Layer-3 — `SnprintfSpec27` : svfprintf prologue segment A
## `0x80007654` (entry) → `0x8000768c` (the `jal strlen`)

First segment of the svfprintf PROLOGUE + first-parse-pass chain (pctrace
`[0x80007654, 0x800077c0)`).  16 machine steps: `addi sp,sp,-592`, the six
early spills, the `mv` triple, `jal _localeconv_r` with the 2-instruction
callee body inlined (`addi a0,gp,904; ret` — gp is the concrete link-time
`0x8001b510`), the `ld` of the static `decimal_point` pointer
(`0x8001b898 → 0x80019770`), `mv a0,a4`, and the spill of the pointer to
`sp+80`.  Generated in the SnprintfSpec22 house style by /tmp/gen_spec27.py.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

