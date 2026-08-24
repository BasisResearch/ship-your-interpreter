import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part23
import Vsa.Sim.DecodeTable.Batch02Part23
import Vsa.Sim.DecodeTable.Batch02Part24
import Vsa.Sim.DecodeTable.Batch04Part09
import Vsa.Sim.DecodeTable.Batch16Part09
import Vsa.Sim.Code.«__muldi3»

/-!
# Layer 3 — per-site observational step lemmas for `__muldi3`

One observational-step (`StepObs`) lemma per instruction of `__muldi3`
(9 instructions at `[0x80004640, 0x80004664)`), each consuming the generated
`__muldi3Loaded` fetch facts (`Vsa/Sim/Code/__muldi3.lean`), the fully-qualified
`DecodeTable` decode lemma, and the relevant `ExecuteAlu`/`ExecuteBranch`
character, assembled in the `DemoStore` style (decode + `rX`/`wX` read-backs +
execute char → the abstract `hexec` the generic `stepObs_*` wrapper wants).

Every lemma is **parity-agnostic**: it takes `i < 2` and produces
`∃ σ' i', Step ⟨σ,i,u⟩ ⟨σ',i',u+1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
ReadsLikePost σ' (sigmaPost_… )`, folding the tick/notick split.

The nine sites and their kinds:
| pc | word | mnemonic | class |
|----|------|----------|-------|
| 40 | 00050613 | mv a2,a0  (addi a2,a0,0)  | ALU ITYPE ADDI (rd x12, rs1 x10) |
| 44 | 00000513 | li a0,0   (addi a0,x0,0)  | ALU ITYPE ADDI (rd x10, rs1 x0) |
| 48 | 0015f693 | andi a3,a1,1              | ALU ITYPE ANDI (rd x13, rs1 x11) |
| 4c | 00068463 | beqz a3,+8 (beq a3,x0)    | BRANCH BEQ (rs1 x13, rs2 x0) |
| 50 | 00c50533 | add a0,a0,a2              | ALU RTYPE ADD (rd x10, rs1 x10, rs2 x12) |
| 54 | 0015d593 | srli a1,a1,1              | ALU SHIFTIOP SRLI (rd x11, rs1 x11) |
| 58 | 00161613 | slli a2,a2,1              | ALU SHIFTIOP SLLI (rd x12, rs1 x12) |
| 5c | fe0596e3 | bnez a1,-20 (bne a1,x0)   | BRANCH BNE (rs1 x11, rs2 x0) |
| 60 | 00008067 | ret (jalr x0,ra,0)        | JUMP jr x0 (rs1 x1) |

Per-site cost: one `hexec` assembly (decode + one/two `rX` read-backs + one `wX`)
+ one `stepObs_*` application. The straight-line ALU sites are ~15 lines each;
the branch sites split taken/not-taken; `ret` is the `stepObs_jr` instantiation.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code (__muldi3Loaded __muldi3_at_80004640 __muldi3_at_80004644
  __muldi3_at_80004648 __muldi3_at_8000464c __muldi3_at_80004650 __muldi3_at_80004654
  __muldi3_at_80004658 __muldi3_at_8000465c __muldi3_at_80004660)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Common address constants and fetch-side bounds

`__muldi3` sits at `0x80004640`, well inside RAM and below `tohostAddr`
(`0x8001ad00`). The fetch-side bounds (`0x80000000 ≤ pc`, `pc+4 ≤ tohostAddr`,
`pc % 4 = 0`) are decidable at each concrete site pc. -/

/-- The base address of `__muldi3`. -/
abbrev muldi3Base : Nat := 0x80004640

/-! ## Site 0x80004640 — `mv a2,a0` = `addi a2,a0,0` (rd = x12, rs1 = x10) -/

/-- `execute (ITYPE addi x12,x10,0)` at `σ₂` in `sigma3_alu` shape (rd = x12,
value `v10 + sext 0`), from `execute_itype_addi_char` + `rX_bits_x10`/`wX_bits_x12`
read-backs through the prelude frame. -/
theorem exec_mv_a2_a0 (σ : MState) (pc : BitVec 64) (v10 : BitVec 64)
    (hx10 : σ.regs.get? Register.x10 = some v10) :
    (execute (instruction.ITYPE (0x000#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0c#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x12 (v10 + sign_extend (m := 64) (0x000#12))) := by
  have hx10₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  exact execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0c#5) v10
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x12 (v10 + sign_extend (m := 64) (0x000#12)))
    (rX_bits_x10 _ v10 hx10₂)
    (wX_bits_x12 _ (v10 + sign_extend (m := 64) (0x000#12)))

/-- Byte-word bridge for `0x00050613`. -/
theorem mv_a2_a0_word :
    (((0x00#8).append (0x05#8)).append (0x06#8)).append (0x13#8) = (0x00050613#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- Non-RVC fact for `0x00050613`. -/
theorem mv_a2_a0_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0x06#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80004640** (`mv a2,a0`). Writes `x12 := v10`
(the ADDI value `v10 + sext 0`); PC advances to `pc+4`. -/
theorem site_80004640
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : __muldi3Loaded σ.mem)
    (hpcv : pc = (0x80004640#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x12 (v10 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __muldi3_at_80004640 hmem
  exact stepObs_alu σ i u (0x80004640#64) vminstret (0x00050613#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0c#5, iop.ADDI))
    Register.x12 (v10 + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x06#8) (0x05#8) (0x00#8)
    hG hpc hminstret mv_a2_a0_word mv_a2_a0_notrvc
    (Vsa.Sim.DecodeTable.decode_00050613 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_mv_a2_a0 σ (0x80004640#64) v10 hx10)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80004644 — `li a0,0` = `addi a0,x0,0` (rd = x10, rs1 = x0) -/

/-- `execute (ITYPE addi x10,x0,0)` at `σ₂`: `rs1 = x0` reads `0` (`rX_bits_zero`),
so the value is `0 + sext 0`; writes `x10`. -/
theorem exec_li_a0_0 (σ : MState) (pc : BitVec 64) :
    (execute (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12))) :=
  execute_itype_addi_char (0x000#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5) (0#64)
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12)))
    (rX_bits_zero _)
    (wX_bits_x10 _ ((0#64) + sign_extend (m := 64) (0x000#12)))

theorem li_a0_0_word :
    (((0x00#8).append (0x00#8)).append (0x05#8)).append (0x13#8) = (0x00000513#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem li_a0_0_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x00#8)).append (0x05#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80004644** (`li a0,0`). Writes `x10 := 0`. -/
theorem site_80004644
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : __muldi3Loaded σ.mem)
    (hpcv : pc = (0x80004644#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __muldi3_at_80004644 hmem
  exact stepObs_alu σ i u (0x80004644#64) vminstret (0x00000513#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x05#8) (0x00#8) (0x00#8)
    hG hpc hminstret li_a0_0_word li_a0_0_notrvc
    (Vsa.Sim.DecodeTable.decode_00000513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_li_a0_0 σ (0x80004644#64))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80004648 — `andi a3,a1,1` (rd = x13, rs1 = x11) -/

/-- `execute (ITYPE andi x13,x11,1)` at `σ₂`: value `v11 &&& sext 1`; writes `x13`. -/
theorem exec_andi_a3_a1 (σ : MState) (pc : BitVec 64) (v11 : BitVec 64)
    (hx11 : σ.regs.get? Register.x11 = some v11) :
    (execute (instruction.ITYPE (0x001#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0d#5, iop.ANDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x13 (v11 &&& sign_extend (m := 64) (0x001#12))) := by
  have hx11₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  exact execute_itype_andi_char (0x001#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0d#5) v11
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x13 (v11 &&& sign_extend (m := 64) (0x001#12)))
    (rX_bits_x11 _ v11 hx11₂)
    (wX_bits_x13 _ (v11 &&& sign_extend (m := 64) (0x001#12)))

theorem andi_a3_a1_word :
    (((0x00#8).append (0x15#8)).append (0xf6#8)).append (0x93#8) = (0x0015f693#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem andi_a3_a1_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x15#8)).append (0xf6#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80004648** (`andi a3,a1,1`). Writes `x13 := a1 & 1`. -/
theorem site_80004648
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : __muldi3Loaded σ.mem)
    (hpcv : pc = (0x80004648#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x13 (v11 &&& sign_extend (m := 64) (0x001#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __muldi3_at_80004648 hmem
  exact stepObs_alu σ i u (0x80004648#64) vminstret (0x0015f693#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0d#5, iop.ANDI))
    Register.x13 (v11 &&& sign_extend (m := 64) (0x001#12)) (0x93#8) (0xf6#8) (0x15#8) (0x00#8)
    hG hpc hminstret andi_a3_a1_word andi_a3_a1_notrvc
    (Vsa.Sim.DecodeTable.decode_0015f693 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_andi_a3_a1 σ (0x80004648#64) v11 hx11)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80004650 — `add a0,a0,a2` (rd = x10, rs1 = x10, rs2 = x12) -/

/-- `execute (RTYPE add x10,x10,x12)` at `σ₂`: value `v10 + v12`; writes `x10`.
Decode gives `RTYPE (rs2=x12, rs1=x10, rd=x10, ADD)`. -/
theorem exec_add_a0_a0_a2 (σ : MState) (pc : BitVec 64) (v10 v12 : BitVec 64)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hx12 : σ.regs.get? Register.x12 = some v12) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0c#5, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, rop.ADD))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x10 (v10 + v12)) := by
  have hx10₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  have hx12₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  exact execute_rtype_add_char (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0a#5)
    v10 v12 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x10 (v10 + v12))
    (rX_bits_x10 _ v10 hx10₂) (rX_bits_x12 _ v12 hx12₂)
    (wX_bits_x10 _ (v10 + v12))

theorem add_a0_a0_a2_word :
    (((0x00#8).append (0xc5#8)).append (0x05#8)).append (0x33#8) = (0x00c50533#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem add_a0_a0_a2_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xc5#8)).append (0x05#8)).append (0x33#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80004650** (`add a0,a0,a2`). Writes `x10 := a0 + a2`. -/
theorem site_80004650
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : __muldi3Loaded σ.mem)
    (hpcv : pc = (0x80004650#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10 (v10 + v12)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __muldi3_at_80004650 hmem
  exact stepObs_alu σ i u (0x80004650#64) vminstret (0x00c50533#32)
    (instruction.RTYPE (regidx.Regidx 0x0c#5, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, rop.ADD))
    Register.x10 (v10 + v12) (0x33#8) (0x05#8) (0xc5#8) (0x00#8)
    hG hpc hminstret add_a0_a0_a2_word add_a0_a0_a2_notrvc
    (Vsa.Sim.DecodeTable.decode_00c50533 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_add_a0_a0_a2 σ (0x80004650#64) v10 v12 hx10 hx12)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80004654 — `srli a1,a1,1` (rd = x11, rs1 = x11) -/

/-- `execute (SHIFTIOP srli x11,x11,1)` at `σ₂`: value `shift_bits_right v11 (extractLsb 1 5 0)`;
writes `x11`. -/
theorem exec_srli_a1_a1 (σ : MState) (pc : BitVec 64) (v11 : BitVec 64)
    (hx11 : σ.regs.get? Register.x11 = some v11) :
    (execute (instruction.SHIFTIOP (0x01#6, regidx.Regidx 0x0b#5, regidx.Regidx 0x0b#5, sop.SRLI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x11 (shift_bits_right v11 (Sail.BitVec.extractLsb (0x01#6) 5 0))) := by
  have hx11₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  exact execute_shiftiop_srli_char (0x01#6) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0b#5) v11
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x11 (shift_bits_right v11 (Sail.BitVec.extractLsb (0x01#6) 5 0)))
    (rX_bits_x11 _ v11 hx11₂)
    (wX_bits_x11 _ (shift_bits_right v11 (Sail.BitVec.extractLsb (0x01#6) 5 0)))

theorem srli_a1_a1_word :
    (((0x00#8).append (0x15#8)).append (0xd5#8)).append (0x93#8) = (0x0015d593#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem srli_a1_a1_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x15#8)).append (0xd5#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80004654** (`srli a1,a1,1`). Writes `x11 := a1 >> 1`. -/
theorem site_80004654
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : __muldi3Loaded σ.mem)
    (hpcv : pc = (0x80004654#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x11 (shift_bits_right v11 (Sail.BitVec.extractLsb (0x01#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __muldi3_at_80004654 hmem
  exact stepObs_alu σ i u (0x80004654#64) vminstret (0x0015d593#32)
    (instruction.SHIFTIOP (0x01#6, regidx.Regidx 0x0b#5, regidx.Regidx 0x0b#5, sop.SRLI))
    Register.x11 (shift_bits_right v11 (Sail.BitVec.extractLsb (0x01#6) 5 0))
    (0x93#8) (0xd5#8) (0x15#8) (0x00#8)
    hG hpc hminstret srli_a1_a1_word srli_a1_a1_notrvc
    (Vsa.Sim.DecodeTable.decode_0015d593 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_srli_a1_a1 σ (0x80004654#64) v11 hx11)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80004658 — `slli a2,a2,1` (rd = x12, rs1 = x12) -/

/-- `execute (SHIFTIOP slli x12,x12,1)` at `σ₂`: value `shift_bits_left v12 (extractLsb 1 5 0)`;
writes `x12`. -/
theorem exec_slli_a2_a2 (σ : MState) (pc : BitVec 64) (v12 : BitVec 64)
    (hx12 : σ.regs.get? Register.x12 = some v12) :
    (execute (instruction.SHIFTIOP (0x01#6, regidx.Regidx 0x0c#5, regidx.Regidx 0x0c#5, sop.SLLI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x12 (shift_bits_left v12 (Sail.BitVec.extractLsb (0x01#6) 5 0))) := by
  have hx12₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  exact execute_shiftiop_slli_char (0x01#6) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0c#5) v12
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x12 (shift_bits_left v12 (Sail.BitVec.extractLsb (0x01#6) 5 0)))
    (rX_bits_x12 _ v12 hx12₂)
    (wX_bits_x12 _ (shift_bits_left v12 (Sail.BitVec.extractLsb (0x01#6) 5 0)))

theorem slli_a2_a2_word :
    (((0x00#8).append (0x16#8)).append (0x16#8)).append (0x13#8) = (0x00161613#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem slli_a2_a2_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x16#8)).append (0x16#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80004658** (`slli a2,a2,1`). Writes `x12 := a2 << 1`. -/
theorem site_80004658
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : __muldi3Loaded σ.mem)
    (hpcv : pc = (0x80004658#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x12 (shift_bits_left v12 (Sail.BitVec.extractLsb (0x01#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __muldi3_at_80004658 hmem
  exact stepObs_alu σ i u (0x80004658#64) vminstret (0x00161613#32)
    (instruction.SHIFTIOP (0x01#6, regidx.Regidx 0x0c#5, regidx.Regidx 0x0c#5, sop.SLLI))
    Register.x12 (shift_bits_left v12 (Sail.BitVec.extractLsb (0x01#6) 5 0))
    (0x13#8) (0x16#8) (0x16#8) (0x00#8)
    hG hpc hminstret slli_a2_a2_word slli_a2_a2_notrvc
    (Vsa.Sim.DecodeTable.decode_00161613 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_slli_a2_a2 σ (0x80004658#64) v12 hx12)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x8000464c — `beqz a3,+8` = `beq a3,x0` (rs1 = x13, rs2 = x0)

Decode: `BTYPE (0x0008#13, x0, x13, BEQ)`. Taken (a3 = 0) ⇒ branch to
`pc + sext 0x0008 = pc + 8` (skip the `add`). Not-taken (a3 ≠ 0) ⇒ fall through
to `pc + 4`. Both variants below; the loop proof picks by the value of a3. -/

theorem beqz_a3_word :
    (((0x00#8).append (0x06#8)).append (0x84#8)).append (0x63#8) = (0x00068463#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem beqz_a3_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x06#8)).append (0x84#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- Taken `beqz a3` execute char at `σ₂` (a3 = 0): `nextPC := pc + sext 0x0008`. -/
theorem exec_beqz_a3_taken (σ : MState) (pc : BitVec 64) (v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (htgt : (pc + sign_extend (m := 64) (0x0008#13)).toNat % 4 = 0)
    (hv : (v13 == (0#64)) = true) :
    (execute (instruction.BTYPE (0x0008#13, regidx.Regidx 0x00#5, regidx.Regidx 0x0d#5, bop.BEQ))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc (0x0008#13)) := by
  have hx13₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_beq_taken (0x0008#13) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x00#5)
    v13 (0#64) pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x13 _ v13 hx13₂) (rX_bits_zero _) hpc₂ hmisa₂ htgt hv

/-- Not-taken `beqz a3` execute char at `σ₂` (a3 ≠ 0): state unchanged. -/
theorem exec_beqz_a3_nottaken (σ : MState) (pc : BitVec 64) (v13 : BitVec 64)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hv : (v13 == (0#64)) = false) :
    (execute (instruction.BTYPE (0x0008#13, regidx.Regidx 0x00#5, regidx.Regidx 0x0d#5, bop.BEQ))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have hx13₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  exact execute_btype_beq_nottaken (0x0008#13) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x00#5)
    v13 (0#64) (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x13 _ v13 hx13₂) (rX_bits_zero _) hv

/-- **Observational step at 0x8000464c, taken** (`beqz a3`, a3 = 0): PC → pc+8. -/
theorem site_8000464c_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : __muldi3Loaded σ.mem)
    (hpcv : pc = (0x8000464c#64 : BitVec 64)) (hv : (v13 == (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0008#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __muldi3_at_8000464c hmem
  exact stepObs_branch_taken σ i u (0x8000464c#64) vminstret (0x0008#13)
    (regidx.Regidx 0x0d#5) (regidx.Regidx 0x00#5) bop.BEQ (0x00068463#32)
    (0x63#8) (0x84#8) (0x06#8) (0x00#8)
    hG hpc hminstret beqz_a3_word beqz_a3_notrvc
    (Vsa.Sim.DecodeTable.decode_00068463 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beqz_a3_taken σ (0x8000464c#64) v13 hG hpc hx13 (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Observational step at 0x8000464c, not taken** (`beqz a3`, a3 ≠ 0): PC → pc+4. -/
theorem site_8000464c_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : __muldi3Loaded σ.mem)
    (hpcv : pc = (0x8000464c#64 : BitVec 64)) (hv : (v13 == (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __muldi3_at_8000464c hmem
  exact stepObs_branch_nottaken σ i u (0x8000464c#64) vminstret (0x0008#13)
    (regidx.Regidx 0x0d#5) (regidx.Regidx 0x00#5) bop.BEQ (0x00068463#32)
    (0x63#8) (0x84#8) (0x06#8) (0x00#8)
    hG hpc hminstret beqz_a3_word beqz_a3_notrvc
    (Vsa.Sim.DecodeTable.decode_00068463 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beqz_a3_nottaken σ (0x8000464c#64) v13 hx13 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x8000465c — `bnez a1,-20` = `bne a1,x0` (rs1 = x11, rs2 = x0)

Decode: `BTYPE (0x1fec#13, x0, x11, BNE)`. Taken (a1 ≠ 0) ⇒ branch to
`pc + sext 0x1fec = pc - 20 = 0x80004648` (loop back-edge). Not-taken (a1 = 0) ⇒
fall through to `pc + 4 = 0x80004660` (ret). -/

theorem bnez_a1_word :
    (((0xfe#8).append (0x05#8)).append (0x96#8)).append (0xe3#8) = (0xfe0596e3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem bnez_a1_notrvc :
    Sail.BitVec.extractLsb ((((0xfe#8).append (0x05#8)).append (0x96#8)).append (0xe3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- Taken `bnez a1` execute char at `σ₂` (a1 ≠ 0): `nextPC := pc + sext 0x1fec`. -/
theorem exec_bnez_a1_taken (σ : MState) (pc : BitVec 64) (v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (htgt : (pc + sign_extend (m := 64) (0x1fec#13)).toNat % 4 = 0)
    (hv : (v11 != (0#64)) = true) :
    (execute (instruction.BTYPE (0x1fec#13, regidx.Regidx 0x00#5, regidx.Regidx 0x0b#5, bop.BNE))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc (0x1fec#13)) := by
  have hx11₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_bne_taken (0x1fec#13) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x00#5)
    v11 (0#64) pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x11 _ v11 hx11₂) (rX_bits_zero _) hpc₂ hmisa₂ htgt hv

/-- Not-taken `bnez a1` execute char at `σ₂` (a1 = 0): state unchanged. -/
theorem exec_bnez_a1_nottaken (σ : MState) (pc : BitVec 64) (v11 : BitVec 64)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hv : (v11 != (0#64)) = false) :
    (execute (instruction.BTYPE (0x1fec#13, regidx.Regidx 0x00#5, regidx.Regidx 0x0b#5, bop.BNE))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have hx11₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  exact execute_btype_bne_nottaken (0x1fec#13) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x00#5)
    v11 (0#64) (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x11 _ v11 hx11₂) (rX_bits_zero _) hv

/-- **Observational step at 0x8000465c, taken** (`bnez a1`, a1 ≠ 0): back-edge to 0x48. -/
theorem site_8000465c_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : __muldi3Loaded σ.mem)
    (hpcv : pc = (0x8000465c#64 : BitVec 64)) (hv : (v11 != (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x1fec#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __muldi3_at_8000465c hmem
  exact stepObs_branch_taken σ i u (0x8000465c#64) vminstret (0x1fec#13)
    (regidx.Regidx 0x0b#5) (regidx.Regidx 0x00#5) bop.BNE (0xfe0596e3#32)
    (0xe3#8) (0x96#8) (0x05#8) (0xfe#8)
    hG hpc hminstret bnez_a1_word bnez_a1_notrvc
    (Vsa.Sim.DecodeTable.decode_fe0596e3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bnez_a1_taken σ (0x8000465c#64) v11 hG hpc hx11 (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Observational step at 0x8000465c, not taken** (`bnez a1`, a1 = 0): fall to ret. -/
theorem site_8000465c_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : __muldi3Loaded σ.mem)
    (hpcv : pc = (0x8000465c#64 : BitVec 64)) (hv : (v11 != (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __muldi3_at_8000465c hmem
  exact stepObs_branch_nottaken σ i u (0x8000465c#64) vminstret (0x1fec#13)
    (regidx.Regidx 0x0b#5) (regidx.Regidx 0x00#5) bop.BNE (0xfe0596e3#32)
    (0xe3#8) (0x96#8) (0x05#8) (0xfe#8)
    hG hpc hminstret bnez_a1_word bnez_a1_notrvc
    (Vsa.Sim.DecodeTable.decode_fe0596e3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bnez_a1_nottaken σ (0x8000465c#64) v11 hx11 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80004660 — `ret` = `jalr x0,ra,0` (rs1 = x1 = ra)

Decode: `JALR (0x000#12, x1, x0)`. The `x0` write is a no-op; `nextPC`/`PC` are
set to the bit-0-cleared return address `ra + sext 0 = ra` (with bit 0 cleared). -/

theorem ret_word :
    (((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8) = (0x00008067#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem ret_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80004660** (`ret`): PC → bit-0-cleared `ra`. -/
theorem site_80004660
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : __muldi3Loaded σ.mem)
    (hpcv : pc = (0x80004660#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __muldi3_at_80004660 hmem
  have hx1₂ : (rX_bits (regidx.Regidx 0x01#5)).run (afterNextPC (afterPrelude σ) (0x80004660#64))
      = .ok vra (afterNextPC (afterPrelude σ) (0x80004660#64)) := by
    apply rX_bits_x1
    rw [get?_afterNextPC σ (0x80004660#64) _ (by decide) (by decide)]; exact hx1
  exact stepObs_jr σ i u (0x80004660#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    ret_notrvc ret_word
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    hx1₂ htgt hi

end Vsa.Sim
