import Vsa.Sim.RamReadPins
import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.ExecuteLoad
import Vsa.Sim.ExecuteStore
import Vsa.Sim.MemStore
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part10
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part20
import Vsa.Sim.DecodeTable.Batch01Part21
import Vsa.Sim.DecodeTable.Batch01Part22
import Vsa.Sim.DecodeTable.Batch01Part23
import Vsa.Sim.DecodeTable.Batch01Part29
import Vsa.Sim.DecodeTable.Batch01Part32
import Vsa.Sim.DecodeTable.Batch03Part03
import Vsa.Sim.DecodeTable.Batch03Part22
import Vsa.Sim.DecodeTable.Batch03Part30
import Vsa.Sim.DecodeTable.Batch04Part24
import Vsa.Sim.DecodeTable.Batch10Part12
import Vsa.Sim.DecodeTable.Batch12Part01
import Vsa.Sim.DecodeTable.Batch12Part02
import Vsa.Sim.DecodeTable.Batch12Part03
import Vsa.Sim.DecodeTable.Batch14Part09
import Vsa.Sim.DecodeTable.Batch14Part13
import Vsa.Sim.DecodeTable.Batch15Part01
import Vsa.Sim.DecodeTable.Batch16Part08
import Vsa.Sim.ValueSites
import Vsa.Sim.Code.Eval_expr

/-!
# Layer 3/4 — per-site observational step lemmas for the `EX_INT` path of `eval_expr`

The `EvalE.int` case walks `eval_expr` (@0x80003164) through:

* **prologue** — `lw a4,0(a2)` (kind), `addi sp,sp,-1088` (frame), 4 `sd` spills
  (`s0@1072`, `s2@1056`, `ra@1080`, `s1@1064`), `li a5,10`, `mv s0,a2`, `mv s2,a1`,
  `bltu a5,a4` (bounds; NOT taken for kind 0), `lwu a5,0(a2)` (kind again),
  `auipc a4,0x17; addi a4,a4,-568` (table base 0x80019f58), `mv s1,a0`,
  `slli a5,a5,2; add a5,a5,a4; lw a5,0(a5)` (jump-table read),
  `add a5,a5,a4; jr a5` (computed dispatch → 0x80003408);
* **arm** (@0x80003408) — `ld a1,8(a2)` (payload), `jal value_int` (@0x8000280c);
* **epilogue** (@0x800033ec) — `ld ra,1080(sp); ld s0,1072(sp); ld s2,1056(sp);
  mv a0,s1; ld s1,1064(sp); addi sp,sp,1088; ret`, reached via `j 0x800033ec`.

Each site follows the `ValueSites`/`ValueEqualSites` recipe: a `stepObs_*` wrapper
over a per-instruction `execute_*` characterization, discharging the fetch bytes
from `Eval_expr.lean`'s `eval_expr_at_*` and the decode from `DecodeTable`. All new
top-level names are suffixed `_ee` to avoid the generic-exec-helper collisions the
sites files have hit before.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Generic unsigned width-4 load `lwu rd,off(rs1)`

`lwu` is `LOAD (off, rs1, rd, true, 4)`. `extend_value true` zero-extends, so the
written value is `zero_extend (kind word)`. Mirrors `exec_lw` (signed) over
`execute_load_unsigned_char`. -/

/-! ## Prologue -/

/-! ### 0x80003164 — `lw a4,0(a2)` (kind of `e`). Writes `x14`. -/

/-! ### 0x80003168 — `addi sp,sp,-1088` (0xbc0). Writes `x2 := sp + sext 0xbc0`. -/

/-! ### The 4 `sd` spills (0x8000316c/70/74/78). Generic over (rs2, off). -/

/-! ### 0x8000317c — `li a5,10` (addi x15,x0,10). Writes `x15 := 10`. -/

/-! ### 0x80003180 — `mv s0,a2` (addi x8,x12,0). Writes `x8 := a2`. -/

/-! ### 0x80003184 — `mv s2,a1` (addi x18,x11,0). Writes `x18 := a1`. -/

/-! ### 0x80003188 — `bltu a5,a4` (rs1=x15, rs2=x14), imm 0x9a0 → 0x80003b28.
For the `.int` case (kind 0 ≤ 10), the branch is NOT taken. -/

/-! ### 0x8000318c — `lwu a5,0(a2)` (kind, unsigned). Writes `x15`. -/

/-! ### 0x80003190 — `auipc a4,0x17`. Writes `x14 := pc + sext(0x17 <<< 12)`. -/

/-! ### 0x80003194 — `addi a4,a4,-568` (0xdc8). Writes `x14 := v14 + sext 0xdc8`. -/

/-! ### 0x80003198 — `mv s1,a0` (addi x9,x10,0). Writes `x9 := a0` (the sret buffer). -/

/-! ### 0x8000319c — `slli a5,a5,0x2` (rd=x15, rs1=x15, shamt=2). -/
theorem exec_slli_a5_ee (σ : MState) (pc : BitVec 64) (v15 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15) :
    (execute (instruction.SHIFTIOP (0x02#6, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, sop.SLLI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x15 (shift_bits_left v15 (Sail.BitVec.extractLsb (0x02#6) 5 0))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_shiftiop_slli_char (0x02#6) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5) v15
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x15 (shift_bits_left v15 (Sail.BitVec.extractLsb (0x02#6) 5 0)))
    (rX_bits_x15 _ v15 h₂)
    (wX_bits_x15 _ (shift_bits_left v15 (Sail.BitVec.extractLsb (0x02#6) 5 0)))

/-! ### 0x800031a0 / 0x800031a8 — `add a5,a5,a4` (rd=x15, rs1=x15, rs2=x14). -/

/-! ### 0x800031a4 — `lw a5,0(a5)` : the JUMP-TABLE read (in `.rodata`).
Four table-slot bytes `t0..t3` are explicit hypotheses. Writes
`x15 := sign_extend (t3 ++ t2 ++ t1 ++ t0)`. -/

/-! ### 0x800031ac — `jr a5` : the computed dispatch (`jalr x0, 0(a5)`). -/

/-! ## The EX_INT arm (@0x80003408) -/

/-! ### 0x80003408 — `ld a1,8(a2)` (payload). Writes `x11`. -/

/-! ### 0x8000340c — `jal value_int` (imm 0x1ff400 → 0x8000280c, rd=x1=ra). -/

/-! ### 0x80003410 — `j 0x800033ec` (jal x0, imm 0x1fffdc → epilogue). -/

/-! ## The shared epilogue (@0x800033ec) -/

/-! ### The 4 `ld` restores (0x800033ec/f0/f4/fc). Generic over (rd, off). -/

/-! ### 0x800033f8 — `mv a0,s1` (addi x10,x9,0). Writes `x10 := s1` (the sret buffer). -/

/-! ### 0x80003400 — `addi sp,sp,1088` (0x440). Restores `x2 := vsp + sext 0x440`. -/

/-! ### 0x80003404 — `ret` (jalr x0, 0(ra)). PC → bit-0-cleared `ra`. -/

end Vsa.Sim
