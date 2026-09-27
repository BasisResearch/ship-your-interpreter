import Vsa.Sim.AddTailSites
import Vsa.Sim.BlockMem
import Vsa.Sim.BlockTactics
import Vsa.Sim.BlockDecode

/-!
# `EvalGtBlk1Pilot` — P1 reflection pilot: EvalGtRow's opening block via ONE `block_mem_sound`

Measurement vehicle. EvalGtRow (226s) hand-threads its opening straight-line run
`0x8000351c … 0x80003530` (lw/li/lw/addiw/lw/ld) as 6 `site_*_ee` obtains + ~40
`obs_alu_*` register carries. Here the SAME run is one `block_mem_sound` application:
one kernel computation over the 6-instruction write-log model, all code-byte pins +
decodes auto-discharged by `block_facts`, only the four load MemFacts supplied. If this
elaborates in a few seconds, the reflection rewrite (P1) is the transformative lever for
the whole cohort. Follows `BlockMemDemo.ssputs_prologue_block` verbatim in shape.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

-- No heartbeat/recDepth overrides: block_mem_sound reflection elaborates within ALL defaults.

