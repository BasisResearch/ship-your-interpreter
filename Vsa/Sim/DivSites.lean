import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part19
import Vsa.Sim.DecodeTable.Batch02Part20
import Vsa.Sim.DecodeTable.Batch02Part24
import Vsa.Sim.DecodeTable.Batch02Part25
import Vsa.Sim.DecodeTable.Batch04Part04
import Vsa.Sim.DecodeTable.Batch04Part08
import Vsa.Sim.DecodeTable.Batch04Part10
import Vsa.Sim.DecodeTable.Batch04Part15
import Vsa.Sim.DecodeTable.Batch06Part22
import Vsa.Sim.DecodeTable.Batch11Part22
import Vsa.Sim.DecodeTable.Batch16Part09
import Vsa.Sim.DecodeTable.Batch16Part13
import Vsa.Sim.DecodeTable.Batch16Part26
import Vsa.Sim.Code.«__hidden___udivdi3»

/-!
# Layer 3 — per-site observational step lemmas for `__hidden___udivdi3`

One observational-step (`StepObs`) lemma per instruction of the libgcc unsigned
64-bit division core `__hidden___udivdi3` (18 instructions at
`[0x800046ac, 0x800046f4)`), assembled in the `Muldi3Sites` style: decode
(`DecodeTable`) + `rX`/`wX` read-backs through the prelude frame + the relevant
`ExecuteAlu`/`ExecuteBranch` character → the abstract `hexec` the generic
`stepObs_*` wrapper wants.

The routine uses one comparison the shared `ExecuteBranch.lean` does not
characterize — `bgeu` (unsigned `≥`, `BGEU`) — so we prove its taken/not-taken
execute characters here (a verbatim clone of the `execute_btype_bge_taken`
proof, swapping the guard predicate `zopz0zKzJ_s` → `zopz0zKzJ_u` and the op).

The 18 sites and their kinds:
| pc | word | mnemonic | class |
|----|------|----------|-------|
| ac | 00058613 | mv a2,a1 (addi a2,a1,0)       | ALU ITYPE ADDI (rd x12, rs1 x11) |
| b0 | 00050593 | mv a1,a0 (addi a1,a0,0)       | ALU ITYPE ADDI (rd x11, rs1 x10) |
| b4 | fff00513 | li a0,-1 (addi a0,x0,-1)      | ALU ITYPE ADDI (rd x10, rs1 x0) |
| b8 | 02060c63 | beqz a2 (beq a2,x0)           | BRANCH BEQ (rs1 x12, rs2 x0) |
| bc | 00100693 | li a3,1 (addi a3,x0,1)        | ALU ITYPE ADDI (rd x13, rs1 x0) |
| c0 | 00b67a63 | bgeu a2,a1                    | BRANCH BGEU (rs1 x12, rs2 x11) |
| c4 | 00c05863 | blez a2 (bge x0,a2)           | BRANCH BGE (rs1 x0, rs2 x12) |
| c8 | 00161613 | slli a2,a2,1                  | ALU SHIFTIOP SLLI (rd x12, rs1 x12) |
| cc | 00169693 | slli a3,a3,1                  | ALU SHIFTIOP SLLI (rd x13, rs1 x13) |
| d0 | feb66ae3 | bltu a2,a1                    | BRANCH BLTU (rs1 x12, rs2 x11) |
| d4 | 00000513 | li a0,0 (addi a0,x0,0)        | ALU ITYPE ADDI (rd x10, rs1 x0) |
| d8 | 00c5e663 | bltu a1,a2                    | BRANCH BLTU (rs1 x11, rs2 x12) |
| dc | 40c585b3 | sub a1,a1,a2                  | ALU RTYPE SUB (rd x11, rs1 x11, rs2 x12) |
| e0 | 00d56533 | or a0,a0,a3                   | ALU RTYPE OR (rd x10, rs1 x10, rs2 x13) |
| e4 | 0016d693 | srli a3,a3,1                  | ALU SHIFTIOP SRLI (rd x13, rs1 x13) |
| e8 | 00165613 | srli a2,a2,1                  | ALU SHIFTIOP SRLI (rd x12, rs1 x12) |
| ec | fe0696e3 | bnez a3 (bne a3,x0)           | BRANCH BNE (rs1 x13, rs2 x0) |
| f0 | 00008067 | ret (jalr x0,ra,0)            | JUMP jr x0 (rs1 x1) |
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## BGEU execute character (absent from shared `ExecuteBranch.lean`)

A verbatim clone of `execute_btype_bge_taken`/`_nottaken`, guard predicate
`zopz0zKzJ_u` (unsigned `≥`), op `BGEU`. -/

/-! BGEU execute characters now live in `Vsa.Sim.StepBranch` (canonical home). -/

/-! ## ALU sites -/

/-! ### 0x800046ac — `mv a2,a1` = `addi a2,a1,0` (rd = x12, rs1 = x11) -/

/-! ### 0x800046b0 — `mv a1,a0` = `addi a1,a0,0` (rd = x11, rs1 = x10) -/

/-! ### 0x800046b4 — `li a0,-1` = `addi a0,x0,-1` (rd = x10, rs1 = x0) -/

/-! ### 0x800046bc — `li a3,1` = `addi a3,x0,1` (rd = x13, rs1 = x0) -/

/-! ### 0x800046c8 — `slli a2,a2,1` (rd = x12, rs1 = x12) -/

/-! ### 0x800046cc — `slli a3,a3,1` (rd = x13, rs1 = x13) -/

/-! ### 0x800046d4 — `li a0,0` = `addi a0,x0,0` (rd = x10, rs1 = x0) -/

theorem exec_li_a0_0 (σ : MState) (pc : BitVec 64) :
    (execute (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12))) :=
  execute_itype_addi_char (0x000#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5) (0#64)
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12)))
    (rX_bits_zero _) (wX_bits_x10 _ ((0#64) + sign_extend (m := 64) (0x000#12)))

/-! ### 0x800046dc — `sub a1,a1,a2` (rd = x11, rs1 = x11, rs2 = x12) -/

/-! ### 0x800046e0 — `or a0,a0,a3` (rd = x10, rs1 = x10, rs2 = x13) -/

/-! ### 0x800046e4 — `srli a3,a3,1` (rd = x13, rs1 = x13) -/

/-! ### 0x800046e8 — `srli a2,a2,1` (rd = x12, rs1 = x12) -/

/-! ## Branch sites -/

/-! ### 0x800046b8 — `beqz a2` = `beq a2,x0` (rs1 = x12, rs2 = x0), imm 0x0038 → 0x800046f0 -/

/-! ### 0x800046c0 — `bgeu a2,a1` (rs1 = x12, rs2 = x11), imm 0x0014 → 0x800046d4 -/

/-! ### 0x800046c4 — `blez a2` = `bge x0,a2` (rs1 = x0, rs2 = x12), imm 0x0010 → 0x800046d4 -/

/-! ### 0x800046d0 — `bltu a2,a1` (rs1 = x12, rs2 = x11), imm 0x1ff4 → 0x800046c4 (back-edge) -/

/-! ### 0x800046d8 — `bltu a1,a2` (rs1 = x11, rs2 = x12), imm 0x000c → 0x800046e4 -/

/-! ### 0x800046ec — `bnez a3` = `bne a3,x0` (rs1 = x13, rs2 = x0), imm 0x1fec → 0x800046d8 (back-edge) -/

/-! ### 0x800046f0 — `ret` = `jalr x0,ra,0` (rs1 = x1 = ra) -/

end Vsa.Sim

