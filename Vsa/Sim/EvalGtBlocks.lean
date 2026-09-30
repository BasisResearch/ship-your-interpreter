import Vsa.Sim.AddTailSites
import Vsa.Sim.BlockMem
import Vsa.Sim.BlockTactics
import Vsa.Sim.BlockDecode
import Vsa.Sim.DecodeTable.Batch09Part24
import Vsa.Sim.DecodeTable.Batch09Part25
import Vsa.Sim.DecodeTable.Batch09Part32
import Vsa.Sim.DecodeTable.Batch05Part26
import Vsa.Sim.DecodeTable.Batch05Part24
import Vsa.Sim.DecodeTable.Batch11Part25
import Vsa.Sim.DecodeTable.Batch05Part29

/-!
# `EvalGtBlocks` — three straight-line eval-expr blocks via ONE `block_mem_sound` each

Merged from three isolated pilots (Blk2, BlkLdSt, BlkCmp).  Each block is a
self-contained standalone lemma derived by ONE `block_mem_sound` application.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

-- No heartbeat/recDepth overrides: block_mem_sound reflection elaborates within ALL defaults.

