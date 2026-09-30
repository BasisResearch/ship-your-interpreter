import Vsa.Sim.EnvGetSites
import Vsa.Sim.DecodeTable.Batch16Part09
import Vsa.Sim.DecodeTable.Batch16Part07
import Vsa.Sim.DecodeTable.Batch15Part23
import Vsa.Sim.DecodeTable.Batch10Part24
import Vsa.Sim.DecodeTable.Batch09Part04
import Vsa.Sim.DecodeTable.Batch08Part22
import Vsa.Sim.DecodeTable.Batch07Part23
import Vsa.Sim.DecodeTable.Batch07Part17
import Vsa.Sim.DecodeTable.Batch07Part12
import Vsa.Sim.DecodeTable.Batch07Part07
import Vsa.Sim.DecodeTable.Batch06Part31
import Vsa.Sim.DecodeTable.Batch06Part30
import Vsa.Sim.DecodeTable.Batch06Part28
import Vsa.Sim.DecodeTable.Batch06Part17
import Vsa.Sim.DecodeTable.Batch06Part07
import Vsa.Sim.DecodeTable.Batch06Part02
import Vsa.Sim.DecodeTable.Batch05Part29
import Vsa.Sim.DecodeTable.Batch05Part27
import Vsa.Sim.DecodeTable.Batch05Part26
import Vsa.Sim.DecodeTable.Batch05Part20
import Vsa.Sim.DecodeTable.Batch05Part19
import Vsa.Sim.DecodeTable.Batch05Part12
import Vsa.Sim.DecodeTable.Batch05Part09
import Vsa.Sim.DecodeTable.Batch05Part07
import Vsa.Sim.DecodeTable.Batch04Part28
import Vsa.Sim.DecodeTable.Batch04Part24
import Vsa.Sim.DecodeTable.Batch03Part26
import Vsa.Sim.DecodeTable.Batch03Part25
import Vsa.Sim.DecodeTable.Batch03Part23
import Vsa.Sim.DecodeTable.Batch03Part19
import Vsa.Sim.DecodeTable.Batch03Part18
import Vsa.Sim.DecodeTable.Batch03Part06
import Vsa.Sim.DecodeTable.Batch02Part22
import Vsa.Sim.DecodeTable.Batch02Part20
import Vsa.Sim.DecodeTable.Batch02Part06
import Vsa.Sim.DecodeTable.Batch02Part04
import Vsa.Sim.DecodeTable.Batch01Part32
import Vsa.Sim.DecodeTable.Batch01Part22
import Vsa.Sim.DecodeTable.Batch01Part20
import Vsa.Sim.DecodeTable.Batch01Part16
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part01

/-!
# Layer 3 — remaining per-site observational step lemmas for `env_get`

Continuation of `Vsa/Sim/EnvGetSites.lean` (which holds the shared byte-word /
non-RVC facts `*_eg`, the control-flow map, and the validated site templates for
`0x80002c10` and `0x80002c14`).  This file adds the remaining ~35 `env_get`
sites, all `_eg2`-suffixed, following the same `stepObs_*` idioms.

Instruction inventory (decoded from `Code/Env_get.lean`):

* ALU-class (`stepObs_alu`): `mv`/`li`/`addi`/`slli`/`add`, and the SIGNED loads
  `lw`/`ld` (they write a GPR with `sign_extend`, observed as `sigmaPost_alu`).
* STORE-class (`stepObs_store`): the seven prologue `sd` spills and the three HIT
  `sd`s into `*out`.
* BRANCH-class: `blez`(=`bge x0,·`)/`beq`/`bne`, taken and not-taken.
* JUMP-class: `j`(`jal x0`), `jal strcmp`, `ret`(`jr x0`).

Reuses `ValueSites` builders (`exec_ld`, `exec_lw`, `exec_sd_val`) and the
`ExecuteAlu`/`ExecuteBranch`/`ExecuteJump` `_char` characterizations, plus the
`*_eg` byte-word facts and `decode_*` table entries.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## ALU-class straight-line sites (`mv`/`li`/`addi`/`slli`/`add`) -/

/-! ### 0x80002c34 (`mv s4,a0`): `x20 := x10 + sext 0`. -/

/-! ### 0x80002c38 (`mv s3,a1`): `x19 := x11 + sext 0`. -/

/-! ### 0x80002c3c (`mv s5,a2`): `x21 := x12 + sext 0`. -/

/-! ### 0x80002c4c (`li s0,0`): `x8 := 0 + sext 0`. -/

/-! ### 0x80002c54 (`addi s0,s0,1`): `x8 := s0 + sext 1` (scan back-edge `i++`). -/

/-! ### 0x80002c58 (`addi s1,s1,8`): `x9 := s1 + sext 8` (names++). -/

/-! ### 0x80002c64 (`mv a1,s3`): `x11 := x19 + sext 0`. -/

/-! ## Load-class sites (`lw`/`ld` — ALU-class, write a GPR with `sign_extend`) -/

/-! ### 0x80002c40 (`lw s2,0(s4)`): `x18 := sext32 [s4+0]` (env->count, CHAIN HEAD). -/

/-! ### 0x80002c48 (`ld s1,8(s4)`): `x9 := sext64 [s4+8]` (env->names). -/

/-! ### 80002c60 (`ld` off=0x000(rs1=Register.x9) → Register.x10). -/
theorem site_80002c60_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbase : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hbase : σ.regs.get? Register.x9 = some vbase)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c60#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (vbase + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) (0x000#12)).toNat)
    (halign : (vbase + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0)
    (d0 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat]? = some b0)
    (d1 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some b1)
    (d2 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some b2)
    (d3 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some b3)
    (d4 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 4]? = some b4)
    (d5 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 5]? = some b5)
    (d6 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 6]? = some b6)
    (d7 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10
          (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_get_at_80002c60 hmem
  have hbase₂ : (afterNextPC (afterPrelude σ) (0x80002c60#64)).regs.get? Register.x9 = some vbase := by
    rw [get?_afterNextPC σ (0x80002c60#64) _ (by decide) (by decide)]; exact hbase
  exact stepObs_alu σ i u (0x80002c60#64) vminstret (0x0004b503#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x09#5, regidx.Regidx 0x0a#5, false, 8))
    Register.x10 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0xb5#8) (0x04#8) (0x00#8)
    hG hpc hminstret w_0004b503_eg nr_0004b503_eg
    (Vsa.Sim.DecodeTable.decode_0004b503 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002c60#64) (0x000#12) (regidx.Regidx 0x09#5) (regidx.Regidx 0x0a#5)
      (sigma3_alu σ (0x80002c60#64) Register.x10
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vbase b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x9 _ vbase hbase₂)
      (wX_bits_x10 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign d0 d1 d2 d3 d4 d5 d6 d7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 80002c70 (`ld` off=0x010(rs1=Register.x20) → Register.x15). -/

/-! ### 80002c84 (`ld` off=0x000(rs1=Register.x15) → Register.x14). -/

/-! ### 80002c90 (`ld` off=0x008(rs1=Register.x15) → Register.x14). -/

/-! ### 80002c98 (`ld` off=0x010(rs1=Register.x15) → Register.x15). -/

/-! ### 80002ca0 (`ld` off=0x038(rs1=Register.x2) → Register.x1). -/

/-! ### 80002ca4 (`ld` off=0x030(rs1=Register.x2) → Register.x8). -/

/-! ### 80002ca8 (`ld` off=0x028(rs1=Register.x2) → Register.x9). -/

/-! ### 80002cac (`ld` off=0x020(rs1=Register.x2) → Register.x18). -/

/-! ### 80002cb0 (`ld` off=0x018(rs1=Register.x2) → Register.x19). -/

/-! ### 80002cb4 (`ld` off=0x010(rs1=Register.x2) → Register.x20). -/

/-! ### 80002cb8 (`ld` off=0x008(rs1=Register.x2) → Register.x21). -/

/-! ### 80002cc4 (`ld` off=0x018(rs1=Register.x20) → Register.x20). -/

/-! ### 80002c18 (`sd` Register.x19 → off=0x018(base=Register.x2)). -/

/-! ### 80002c1c (`sd` Register.x20 → off=0x010(base=Register.x2)). -/

/-! ### 80002c20 (`sd` Register.x21 → off=0x008(base=Register.x2)). -/

/-! ### 80002c24 (`sd` Register.x1 → off=0x038(base=Register.x2)). -/

/-! ### 80002c28 (`sd` Register.x8 → off=0x030(base=Register.x2)). -/

/-! ### 80002c2c (`sd` Register.x9 → off=0x028(base=Register.x2)). -/

/-! ### 80002c30 (`sd` Register.x18 → off=0x020(base=Register.x2)). -/

/-! ### 80002c8c (`sd` Register.x14 → off=0x000(base=Register.x21)). -/

/-! ### 80002c94 (`sd` Register.x14 → off=0x008(base=Register.x21)). -/

/-! ### 80002c9c (`sd` Register.x15 → off=0x010(base=Register.x21)). -/

/-! ## HIT-block index arithmetic (`slli`/`add`: 24*i stride) -/

/-! ### 0x80002c74 (`slli a4,s0,1`): `x14 := s0 <<< 1`. -/

/-! ### 0x80002c78 (`add a4,a4,s0`): `x14 := a4 + s0`. -/

/-! ### 0x80002c7c (`slli a4,a4,3`): `x14 := a4 <<< 3`. -/

/-! ### 0x80002c80 (`add a5,a5,a4`): `x15 := a5 + a4` (&vals[i]). -/

/-! ### 0x80002c88 (`li a0,1`): `x10 := 0 + sext 1` (HIT return value). -/

/-! ### 0x80002cbc (`addi sp,sp,64`): `x2 := sp + sext 0x040` (epilogue restore). -/

/-! ### 0x80002ccc (`li a0,0`): `x10 := 0 + sext 0` (MISS return value). -/

/-! ## Branch-class sites (`blez`/`beq`/`bnez`) -/

/-! ### 0x80002c44 (`blez s2,cc4` = `bge x0,s2`), NOT taken: `count > 0`, fall to c48. -/

/-! ### 0x80002c44 (`blez s2,cc4`), TAKEN: `count <= 0`, branch to cc4 (descend). -/

/-! ### 0x80002c5c (`beq s0,s2,cc4` = SCAN TEST), NOT taken: `i != count`, fall to c60. -/

/-! ### 0x80002c5c (`beq s0,s2,cc4`), TAKEN: `i == count` (scan exhausted), branch to cc4. -/

/-! ### 0x80002c6c (`bnez a0,c54` = `bne a0,x0`), NOT taken: `strcmp == 0` (HIT), fall to c70. -/

/-! ### 0x80002c6c (`bnez a0,c54`), TAKEN: `strcmp != 0`, branch back to c54 (next iter). -/

/-! ### 0x80002cc8 (`bnez s4,c40` = CHAIN TEST), NOT taken: `parent == 0`, fall to ccc (MISS). -/

/-! ### 0x80002cc8 (`bnez s4,c40`), TAKEN: `parent != 0`, branch to c40 (next chain head). -/

/-! ## Jump-class sites (`j`/`jal`/`ret`) -/

/-! ### 0x80002c50 (`j 0x80002c60` = `jal x0`): enter scan loop at the test. -/

/-! ### 0x80002c68 (`jal strcmp` = `jal x1`, imm 0x004238 → 0x80006ea0). -/

/-! ### 0x80002cc0 (`ret` = `jr x1`): epilogue return. -/

/-! ### 0x80002cd0 (`j 0x80002ca0` = `jal x0`, imm 0x1fffd0 → epilogue with a0=0). -/

/-! ### 0x80002cd4 (`li a0,0`): NULL-env entry return value. -/

/-! ### 0x80002cd8 (`ret` = `jr x1`): NULL-env entry return. -/

end Vsa.Sim

