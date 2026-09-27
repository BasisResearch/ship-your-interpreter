import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable.Batch03Part21
import Vsa.Sim.DecodeTable.Batch03Part23
import Vsa.Sim.DecodeTable.Batch04Part09
import Vsa.Sim.DecodeTable.Batch04Part11
import Vsa.Sim.DecodeTable.Batch11Part23
import Vsa.Sim.DecodeTable.Batch16Part21
import Vsa.Sim.DecodeTable.Batch16Part27
import Vsa.Sim.Code.Memcpy
import Vsa.Sim.DivSites
import Vsa.Sim.MemcpySites
import Vsa.Sim.MemcpySites2

/-!
# Layer 3 — per-site observational step lemmas for `memcpy`'s word-loop epilogue

One observational-step (`StepObs`) lemma per instruction of the **word-loop
epilogue** `[0x80006c1c, 0x80006c34]` — the straight-line pointer recomputation
after the small word loop that repositions `a1`/`a4` past the copied `p` words and
falls into the byte tail (`c38`).

| pc  | word     | mnemonic       | AST | class |
|-----|----------|----------------|-----|-------|
| c1c | fff60613 | addi a2,a2,-1  | ITYPE(0xfff,x12,x12,ADDI) | ALU |
| c20 | 40e60633 | sub  a2,a2,a4  | RTYPE(x14,x12,x12,SUB)    | ALU |
| c24 | ff867613 | andi a2,a2,-8  | ITYPE(0xff8,x12,x12,ANDI) | ALU |
| c28 | 00858593 | addi a1,a1,8   | ITYPE(0x008,x11,x11,ADDI) | ALU |
| c2c | 00870713 | addi a4,a4,8   | ITYPE(0x008,x14,x14,ADDI) | ALU |
| c30 | 00c585b3 | add  a1,a1,a2  | RTYPE(x12,x11,x11,ADD)    | ALU |
| c34 | 00c70733 | add  a4,a4,a2  | RTYPE(x12,x14,x14,ADD)    | ALU |

All sites are the plain ALU recipe (`MemcpySites` byte-path style): one `exec_*`
assembly (decode + one/two `rX_bits` reads + one `wX_bits`) and one `stepObs_alu`.
The site at `c38` (`bltu a4,a7`) already exists in `MemcpySites2.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code (MemcpyLoaded memcpy_at_80006c1c memcpy_at_80006c20 memcpy_at_80006c24 memcpy_at_80006c28 memcpy_at_80006c2c memcpy_at_80006c30 memcpy_at_80006c34)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

