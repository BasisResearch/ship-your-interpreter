import Vsa.Sim.SnprintfSitesRet5
import Vsa.Sim.Code.Memset
import Vsa.Sim.DecodeTable.Batch05Part14
import Vsa.Sim.DecodeTable.Batch08Part30
import Vsa.Sim.DecodeTable.Batch01Part09
import Vsa.Sim.DecodeTable.Batch06Part25
import Vsa.Sim.DecodeTable.Batch06Part14
import Vsa.Sim.DecodeTable.Batch03Part02
import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch04Part10

/-!
# M3 Layer-3 — hand `StepObs` sites for the svfprintf PROLOGUE generator gaps

`scripts/gen_sites.py` has no `lhu`/`andi`/`auipc`/`slli`/`srli`/offset-`jr`
classes; the eight sites on the prologue + first-parse-pass path in those
classes are hand-written here on the validated templates
(`SnprintfSitesRet5.site_800079c0_rt5`/`site_800079c4_rt5` for `lhu`/`andi`,
`EvalExprSites.site_80003190_ee` for `auipc`, `StrlenSites.site_80006d04`
for `slli`, `SnprintfSpec14`'s inline `srli` block, and the generated
`jr`-class emission with a nonzero immediate for `jr 12(a3)`).

  0x800076a4  lhu  a5,16(s1)     FILE `_flags` halfword
  0x800076a8  andi a5,a5,128     `__SCLE` test (taken-zero on this path)
  0x80007788  auipc s6,0x13      parse jump-table base (hi part)
  0x800077a8  slli a4,a5,0x20    dispatch index scale (hi)
  0x800077ac  srli a5,a4,0x1e    dispatch index scale (lo) = 4*(ch-32)
  0x80006b2c  slli a3,a3,0x2     memset jump-table scale
  0x80006b30  auipc t0,0x0       memset jump-table base
  0x80006b38  jr   12(a3)        memset computed dispatch
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

