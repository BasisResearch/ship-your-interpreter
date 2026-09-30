import Vsa.Sim.SnprintfSites
import Vsa.Sim.ValueSites
import Vsa.Sim.StrcpySites
import Vsa.Sim.Code.FlushPins
import Vsa.Sim.DecodeTable.Batch16Part20
import Vsa.Sim.DecodeTable.Batch15Part22
import Vsa.Sim.DecodeTable.Batch15Part21
import Vsa.Sim.DecodeTable.Batch14Part31
import Vsa.Sim.DecodeTable.Batch13Part04
import Vsa.Sim.DecodeTable.Batch11Part31
import Vsa.Sim.DecodeTable.Batch09Part10
import Vsa.Sim.DecodeTable.Batch08Part24
import Vsa.Sim.DecodeTable.Batch08Part22
import Vsa.Sim.DecodeTable.Batch08Part21
import Vsa.Sim.DecodeTable.Batch07Part18
import Vsa.Sim.DecodeTable.Batch07Part16
import Vsa.Sim.DecodeTable.Batch07Part08
import Vsa.Sim.DecodeTable.Batch06Part30
import Vsa.Sim.DecodeTable.Batch06Part18
import Vsa.Sim.DecodeTable.Batch06Part17
import Vsa.Sim.DecodeTable.Batch05Part31
import Vsa.Sim.DecodeTable.Batch02Part28
import Vsa.Sim.DecodeTable.Batch02Part20
import Vsa.Sim.DecodeTable.Batch02Part09
import Vsa.Sim.DecodeTable.Batch02Part05
import Vsa.Sim.DecodeTable.Batch01Part02

/-!
# M3 Layer-3 — `SnprintfSitesFlush` : exit-restore + flush-hop step battery (`_fl`)

Sites for the post-loop flush path (ordered PC trace, `experiments/pctrace.md`):
the exit-restore block `0x80008358 … 0x80008394` (spill reloads, `len = top −
cursor`, the sign-byte read-back `lbu t5,167(sp)`), and the hops
`0x8000812c/30/34 → 0x80008088/8c → 0x8000a830/34/38 → 0x8000782c`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

