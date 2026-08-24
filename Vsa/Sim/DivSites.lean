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
open Vsa.Sim.Code (__hidden___udivdi3Loaded
  __hidden___udivdi3_at_800046ac __hidden___udivdi3_at_800046b0
  __hidden___udivdi3_at_800046b4 __hidden___udivdi3_at_800046b8
  __hidden___udivdi3_at_800046bc __hidden___udivdi3_at_800046c0
  __hidden___udivdi3_at_800046c4 __hidden___udivdi3_at_800046c8
  __hidden___udivdi3_at_800046cc __hidden___udivdi3_at_800046d0
  __hidden___udivdi3_at_800046d4 __hidden___udivdi3_at_800046d8
  __hidden___udivdi3_at_800046dc __hidden___udivdi3_at_800046e0
  __hidden___udivdi3_at_800046e4 __hidden___udivdi3_at_800046e8
  __hidden___udivdi3_at_800046ec __hidden___udivdi3_at_800046f0)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## BGEU execute character (absent from shared `ExecuteBranch.lean`)

A verbatim clone of `execute_btype_bge_taken`/`_nottaken`, guard predicate
`zopz0zKzJ_u` (unsigned `≥`), op `BGEU`. -/

/-! BGEU execute characters now live in `Vsa.Sim.StepBranch` (canonical home). -/

/-! ## ALU sites -/

/-! ### 0x800046ac — `mv a2,a1` = `addi a2,a1,0` (rd = x12, rs1 = x11) -/

theorem exec_mv_a2_a1 (σ : MState) (pc : BitVec 64) (v11 : BitVec 64)
    (hx11 : σ.regs.get? Register.x11 = some v11) :
    (execute (instruction.ITYPE (0x000#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0c#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x12 (v11 + sign_extend (m := 64) (0x000#12))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  exact execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0c#5) v11
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x12 (v11 + sign_extend (m := 64) (0x000#12)))
    (rX_bits_x11 _ v11 h₂) (wX_bits_x12 _ (v11 + sign_extend (m := 64) (0x000#12)))

theorem site_800046ac
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : __hidden___udivdi3Loaded σ.mem)
    (hpcv : pc = (0x800046ac#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x12 (v11 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __hidden___udivdi3_at_800046ac hmem
  exact stepObs_alu σ i u (0x800046ac#64) vminstret (0x00058613#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0c#5, iop.ADDI))
    Register.x12 (v11 + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x86#8) (0x05#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00058613 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_mv_a2_a1 σ (0x800046ac#64) v11 hx11)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800046b0 — `mv a1,a0` = `addi a1,a0,0` (rd = x11, rs1 = x10) -/

theorem exec_mv_a1_a0 (σ : MState) (pc : BitVec 64) (v10 : BitVec 64)
    (hx10 : σ.regs.get? Register.x10 = some v10) :
    (execute (instruction.ITYPE (0x000#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0b#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x11 (v10 + sign_extend (m := 64) (0x000#12))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  exact execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0b#5) v10
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x11 (v10 + sign_extend (m := 64) (0x000#12)))
    (rX_bits_x10 _ v10 h₂) (wX_bits_x11 _ (v10 + sign_extend (m := 64) (0x000#12)))

theorem site_800046b0
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : __hidden___udivdi3Loaded σ.mem)
    (hpcv : pc = (0x800046b0#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x11 (v10 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __hidden___udivdi3_at_800046b0 hmem
  exact stepObs_alu σ i u (0x800046b0#64) vminstret (0x00050593#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0b#5, iop.ADDI))
    Register.x11 (v10 + sign_extend (m := 64) (0x000#12)) (0x93#8) (0x05#8) (0x05#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00050593 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_mv_a1_a0 σ (0x800046b0#64) v10 hx10)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800046b4 — `li a0,-1` = `addi a0,x0,-1` (rd = x10, rs1 = x0) -/

theorem exec_li_a0_m1 (σ : MState) (pc : BitVec 64) :
    (execute (instruction.ITYPE (0xfff#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x10 ((0#64) + sign_extend (m := 64) (0xfff#12))) :=
  execute_itype_addi_char (0xfff#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5) (0#64)
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x10 ((0#64) + sign_extend (m := 64) (0xfff#12)))
    (rX_bits_zero _) (wX_bits_x10 _ ((0#64) + sign_extend (m := 64) (0xfff#12)))

theorem site_800046b4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : __hidden___udivdi3Loaded σ.mem)
    (hpcv : pc = (0x800046b4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 ((0#64) + sign_extend (m := 64) (0xfff#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __hidden___udivdi3_at_800046b4 hmem
  exact stepObs_alu σ i u (0x800046b4#64) vminstret (0xfff00513#32)
    (instruction.ITYPE (0xfff#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 ((0#64) + sign_extend (m := 64) (0xfff#12)) (0x13#8) (0x05#8) (0xf0#8) (0xff#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_fff00513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_li_a0_m1 σ (0x800046b4#64))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800046bc — `li a3,1` = `addi a3,x0,1` (rd = x13, rs1 = x0) -/

theorem exec_li_a3_1 (σ : MState) (pc : BitVec 64) :
    (execute (instruction.ITYPE (0x001#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0d#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x13 ((0#64) + sign_extend (m := 64) (0x001#12))) :=
  execute_itype_addi_char (0x001#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0d#5) (0#64)
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x13 ((0#64) + sign_extend (m := 64) (0x001#12)))
    (rX_bits_zero _) (wX_bits_x13 _ ((0#64) + sign_extend (m := 64) (0x001#12)))

theorem site_800046bc
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : __hidden___udivdi3Loaded σ.mem)
    (hpcv : pc = (0x800046bc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x13 ((0#64) + sign_extend (m := 64) (0x001#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __hidden___udivdi3_at_800046bc hmem
  exact stepObs_alu σ i u (0x800046bc#64) vminstret (0x00100693#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0d#5, iop.ADDI))
    Register.x13 ((0#64) + sign_extend (m := 64) (0x001#12)) (0x93#8) (0x06#8) (0x10#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00100693 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_li_a3_1 σ (0x800046bc#64))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800046c8 — `slli a2,a2,1` (rd = x12, rs1 = x12) -/

theorem exec_slli_a2 (σ : MState) (pc : BitVec 64) (v12 : BitVec 64)
    (hx12 : σ.regs.get? Register.x12 = some v12) :
    (execute (instruction.SHIFTIOP (0x01#6, regidx.Regidx 0x0c#5, regidx.Regidx 0x0c#5, sop.SLLI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x12 (shift_bits_left v12 (Sail.BitVec.extractLsb (0x01#6) 5 0))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  exact execute_shiftiop_slli_char (0x01#6) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0c#5) v12
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x12 (shift_bits_left v12 (Sail.BitVec.extractLsb (0x01#6) 5 0)))
    (rX_bits_x12 _ v12 h₂)
    (wX_bits_x12 _ (shift_bits_left v12 (Sail.BitVec.extractLsb (0x01#6) 5 0)))

theorem site_800046c8
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : __hidden___udivdi3Loaded σ.mem)
    (hpcv : pc = (0x800046c8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x12 (shift_bits_left v12 (Sail.BitVec.extractLsb (0x01#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __hidden___udivdi3_at_800046c8 hmem
  exact stepObs_alu σ i u (0x800046c8#64) vminstret (0x00161613#32)
    (instruction.SHIFTIOP (0x01#6, regidx.Regidx 0x0c#5, regidx.Regidx 0x0c#5, sop.SLLI))
    Register.x12 (shift_bits_left v12 (Sail.BitVec.extractLsb (0x01#6) 5 0))
    (0x13#8) (0x16#8) (0x16#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00161613 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_slli_a2 σ (0x800046c8#64) v12 hx12)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800046cc — `slli a3,a3,1` (rd = x13, rs1 = x13) -/

theorem exec_slli_a3 (σ : MState) (pc : BitVec 64) (v13 : BitVec 64)
    (hx13 : σ.regs.get? Register.x13 = some v13) :
    (execute (instruction.SHIFTIOP (0x01#6, regidx.Regidx 0x0d#5, regidx.Regidx 0x0d#5, sop.SLLI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x13 (shift_bits_left v13 (Sail.BitVec.extractLsb (0x01#6) 5 0))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  exact execute_shiftiop_slli_char (0x01#6) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0d#5) v13
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x13 (shift_bits_left v13 (Sail.BitVec.extractLsb (0x01#6) 5 0)))
    (rX_bits_x13 _ v13 h₂)
    (wX_bits_x13 _ (shift_bits_left v13 (Sail.BitVec.extractLsb (0x01#6) 5 0)))

theorem site_800046cc
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : __hidden___udivdi3Loaded σ.mem)
    (hpcv : pc = (0x800046cc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x13 (shift_bits_left v13 (Sail.BitVec.extractLsb (0x01#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __hidden___udivdi3_at_800046cc hmem
  exact stepObs_alu σ i u (0x800046cc#64) vminstret (0x00169693#32)
    (instruction.SHIFTIOP (0x01#6, regidx.Regidx 0x0d#5, regidx.Regidx 0x0d#5, sop.SLLI))
    Register.x13 (shift_bits_left v13 (Sail.BitVec.extractLsb (0x01#6) 5 0))
    (0x93#8) (0x96#8) (0x16#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00169693 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_slli_a3 σ (0x800046cc#64) v13 hx13)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800046d4 — `li a0,0` = `addi a0,x0,0` (rd = x10, rs1 = x0) -/

theorem exec_li_a0_0 (σ : MState) (pc : BitVec 64) :
    (execute (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12))) :=
  execute_itype_addi_char (0x000#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5) (0#64)
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12)))
    (rX_bits_zero _) (wX_bits_x10 _ ((0#64) + sign_extend (m := 64) (0x000#12)))

theorem site_800046d4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : __hidden___udivdi3Loaded σ.mem)
    (hpcv : pc = (0x800046d4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __hidden___udivdi3_at_800046d4 hmem
  exact stepObs_alu σ i u (0x800046d4#64) vminstret (0x00000513#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x05#8) (0x00#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00000513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_li_a0_0 σ (0x800046d4#64))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800046dc — `sub a1,a1,a2` (rd = x11, rs1 = x11, rs2 = x12) -/

theorem exec_sub_a1 (σ : MState) (pc : BitVec 64) (v11 v12 : BitVec 64)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hx12 : σ.regs.get? Register.x12 = some v12) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0c#5, regidx.Regidx 0x0b#5, regidx.Regidx 0x0b#5, rop.SUB))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x11 (v11 - v12)) := by
  have h11 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  have h12 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  exact execute_rtype_sub_char (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0b#5)
    v11 v12 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x11 (v11 - v12))
    (rX_bits_x11 _ v11 h11) (rX_bits_x12 _ v12 h12)
    (wX_bits_x11 _ (v11 - v12))

theorem site_800046dc
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : __hidden___udivdi3Loaded σ.mem)
    (hpcv : pc = (0x800046dc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x11 (v11 - v12)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __hidden___udivdi3_at_800046dc hmem
  exact stepObs_alu σ i u (0x800046dc#64) vminstret (0x40c585b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0c#5, regidx.Regidx 0x0b#5, regidx.Regidx 0x0b#5, rop.SUB))
    Register.x11 (v11 - v12) (0xb3#8) (0x85#8) (0xc5#8) (0x40#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_40c585b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sub_a1 σ (0x800046dc#64) v11 v12 hx11 hx12)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800046e0 — `or a0,a0,a3` (rd = x10, rs1 = x10, rs2 = x13) -/

theorem exec_or_a0 (σ : MState) (pc : BitVec 64) (v10 v13 : BitVec 64)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hx13 : σ.regs.get? Register.x13 = some v13) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0d#5, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, rop.OR))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x10 (v10 ||| v13)) := by
  have h10 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  have h13 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  exact execute_rtype_or_char (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0a#5)
    v10 v13 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x10 (v10 ||| v13))
    (rX_bits_x10 _ v10 h10) (rX_bits_x13 _ v13 h13)
    (wX_bits_x10 _ (v10 ||| v13))

theorem site_800046e0
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : __hidden___udivdi3Loaded σ.mem)
    (hpcv : pc = (0x800046e0#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10 (v10 ||| v13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __hidden___udivdi3_at_800046e0 hmem
  exact stepObs_alu σ i u (0x800046e0#64) vminstret (0x00d56533#32)
    (instruction.RTYPE (regidx.Regidx 0x0d#5, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, rop.OR))
    Register.x10 (v10 ||| v13) (0x33#8) (0x65#8) (0xd5#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00d56533 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_or_a0 σ (0x800046e0#64) v10 v13 hx10 hx13)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800046e4 — `srli a3,a3,1` (rd = x13, rs1 = x13) -/

theorem exec_srli_a3 (σ : MState) (pc : BitVec 64) (v13 : BitVec 64)
    (hx13 : σ.regs.get? Register.x13 = some v13) :
    (execute (instruction.SHIFTIOP (0x01#6, regidx.Regidx 0x0d#5, regidx.Regidx 0x0d#5, sop.SRLI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x13 (shift_bits_right v13 (Sail.BitVec.extractLsb (0x01#6) 5 0))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  exact execute_shiftiop_srli_char (0x01#6) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0d#5) v13
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x13 (shift_bits_right v13 (Sail.BitVec.extractLsb (0x01#6) 5 0)))
    (rX_bits_x13 _ v13 h₂)
    (wX_bits_x13 _ (shift_bits_right v13 (Sail.BitVec.extractLsb (0x01#6) 5 0)))

theorem site_800046e4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : __hidden___udivdi3Loaded σ.mem)
    (hpcv : pc = (0x800046e4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x13 (shift_bits_right v13 (Sail.BitVec.extractLsb (0x01#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __hidden___udivdi3_at_800046e4 hmem
  exact stepObs_alu σ i u (0x800046e4#64) vminstret (0x0016d693#32)
    (instruction.SHIFTIOP (0x01#6, regidx.Regidx 0x0d#5, regidx.Regidx 0x0d#5, sop.SRLI))
    Register.x13 (shift_bits_right v13 (Sail.BitVec.extractLsb (0x01#6) 5 0))
    (0x93#8) (0xd6#8) (0x16#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0016d693 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_srli_a3 σ (0x800046e4#64) v13 hx13)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800046e8 — `srli a2,a2,1` (rd = x12, rs1 = x12) -/

theorem exec_srli_a2 (σ : MState) (pc : BitVec 64) (v12 : BitVec 64)
    (hx12 : σ.regs.get? Register.x12 = some v12) :
    (execute (instruction.SHIFTIOP (0x01#6, regidx.Regidx 0x0c#5, regidx.Regidx 0x0c#5, sop.SRLI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x12 (shift_bits_right v12 (Sail.BitVec.extractLsb (0x01#6) 5 0))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  exact execute_shiftiop_srli_char (0x01#6) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0c#5) v12
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x12 (shift_bits_right v12 (Sail.BitVec.extractLsb (0x01#6) 5 0)))
    (rX_bits_x12 _ v12 h₂)
    (wX_bits_x12 _ (shift_bits_right v12 (Sail.BitVec.extractLsb (0x01#6) 5 0)))

theorem site_800046e8
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : __hidden___udivdi3Loaded σ.mem)
    (hpcv : pc = (0x800046e8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x12 (shift_bits_right v12 (Sail.BitVec.extractLsb (0x01#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __hidden___udivdi3_at_800046e8 hmem
  exact stepObs_alu σ i u (0x800046e8#64) vminstret (0x00165613#32)
    (instruction.SHIFTIOP (0x01#6, regidx.Regidx 0x0c#5, regidx.Regidx 0x0c#5, sop.SRLI))
    Register.x12 (shift_bits_right v12 (Sail.BitVec.extractLsb (0x01#6) 5 0))
    (0x13#8) (0x56#8) (0x16#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00165613 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_srli_a2 σ (0x800046e8#64) v12 hx12)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Branch sites -/

/-! ### 0x800046b8 — `beqz a2` = `beq a2,x0` (rs1 = x12, rs2 = x0), imm 0x0038 → 0x800046f0 -/

theorem exec_beqz_a2_taken (σ : MState) (pc : BitVec 64) (v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (htgt : (pc + sign_extend (m := 64) (0x0038#13)).toNat % 4 = 0)
    (hv : (v12 == (0#64)) = true) :
    (execute (instruction.BTYPE (0x0038#13, regidx.Regidx 0x00#5, regidx.Regidx 0x0c#5, bop.BEQ))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc (0x0038#13)) := by
  have h12 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_beq_taken (0x0038#13) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x00#5)
    v12 (0#64) pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x12 _ v12 h12) (rX_bits_zero _) hpc₂ hmisa₂ htgt hv

theorem exec_beqz_a2_nottaken (σ : MState) (pc : BitVec 64) (v12 : BitVec 64)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hv : (v12 == (0#64)) = false) :
    (execute (instruction.BTYPE (0x0038#13, regidx.Regidx 0x00#5, regidx.Regidx 0x0c#5, bop.BEQ))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have h12 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  exact execute_btype_beq_nottaken (0x0038#13) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x00#5)
    v12 (0#64) (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x12 _ v12 h12) (rX_bits_zero _) hv

theorem site_800046b8_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : __hidden___udivdi3Loaded σ.mem)
    (hpcv : pc = (0x800046b8#64 : BitVec 64)) (hv : (v12 == (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0038#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __hidden___udivdi3_at_800046b8 hmem
  exact stepObs_branch_taken σ i u (0x800046b8#64) vminstret (0x0038#13)
    (regidx.Regidx 0x0c#5) (regidx.Regidx 0x00#5) bop.BEQ (0x02060c63#32)
    (0x63#8) (0x0c#8) (0x06#8) (0x02#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_02060c63 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beqz_a2_taken σ (0x800046b8#64) v12 hG hpc hx12 (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_800046b8_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : __hidden___udivdi3Loaded σ.mem)
    (hpcv : pc = (0x800046b8#64 : BitVec 64)) (hv : (v12 == (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __hidden___udivdi3_at_800046b8 hmem
  exact stepObs_branch_nottaken σ i u (0x800046b8#64) vminstret (0x0038#13)
    (regidx.Regidx 0x0c#5) (regidx.Regidx 0x00#5) bop.BEQ (0x02060c63#32)
    (0x63#8) (0x0c#8) (0x06#8) (0x02#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_02060c63 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beqz_a2_nottaken σ (0x800046b8#64) v12 hx12 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800046c0 — `bgeu a2,a1` (rs1 = x12, rs2 = x11), imm 0x0014 → 0x800046d4 -/

theorem exec_bgeu_a2_a1_taken (σ : MState) (pc : BitVec 64) (v12 v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx12 : σ.regs.get? Register.x12 = some v12) (hx11 : σ.regs.get? Register.x11 = some v11)
    (htgt : (pc + sign_extend (m := 64) (0x0014#13)).toNat % 4 = 0)
    (hv : zopz0zKzJ_u v12 v11 = true) :
    (execute (instruction.BTYPE (0x0014#13, regidx.Regidx 0x0b#5, regidx.Regidx 0x0c#5, bop.BGEU))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc (0x0014#13)) := by
  have h12 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  have h11 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_bgeu_taken (0x0014#13) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0b#5)
    v12 v11 pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x12 _ v12 h12) (rX_bits_x11 _ v11 h11) hpc₂ hmisa₂ htgt hv

theorem exec_bgeu_a2_a1_nottaken (σ : MState) (pc : BitVec 64) (v12 v11 : BitVec 64)
    (hx12 : σ.regs.get? Register.x12 = some v12) (hx11 : σ.regs.get? Register.x11 = some v11)
    (hv : zopz0zKzJ_u v12 v11 = false) :
    (execute (instruction.BTYPE (0x0014#13, regidx.Regidx 0x0b#5, regidx.Regidx 0x0c#5, bop.BGEU))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have h12 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  have h11 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  exact execute_btype_bgeu_nottaken (0x0014#13) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0b#5)
    v12 v11 (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x12 _ v12 h12) (rX_bits_x11 _ v11 h11) hv

theorem site_800046c0_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12) (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : __hidden___udivdi3Loaded σ.mem)
    (hpcv : pc = (0x800046c0#64 : BitVec 64)) (hv : zopz0zKzJ_u v12 v11 = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0014#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __hidden___udivdi3_at_800046c0 hmem
  exact stepObs_branch_taken σ i u (0x800046c0#64) vminstret (0x0014#13)
    (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0b#5) bop.BGEU (0x00b67a63#32)
    (0x63#8) (0x7a#8) (0xb6#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00b67a63 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bgeu_a2_a1_taken σ (0x800046c0#64) v12 v11 hG hpc hx12 hx11 (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_800046c0_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12) (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : __hidden___udivdi3Loaded σ.mem)
    (hpcv : pc = (0x800046c0#64 : BitVec 64)) (hv : zopz0zKzJ_u v12 v11 = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __hidden___udivdi3_at_800046c0 hmem
  exact stepObs_branch_nottaken σ i u (0x800046c0#64) vminstret (0x0014#13)
    (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0b#5) bop.BGEU (0x00b67a63#32)
    (0x63#8) (0x7a#8) (0xb6#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00b67a63 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bgeu_a2_a1_nottaken σ (0x800046c0#64) v12 v11 hx12 hx11 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800046c4 — `blez a2` = `bge x0,a2` (rs1 = x0, rs2 = x12), imm 0x0010 → 0x800046d4 -/

theorem exec_blez_a2_taken (σ : MState) (pc : BitVec 64) (v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (htgt : (pc + sign_extend (m := 64) (0x0010#13)).toNat % 4 = 0)
    (hv : zopz0zKzJ_s (0#64) v12 = true) :
    (execute (instruction.BTYPE (0x0010#13, regidx.Regidx 0x0c#5, regidx.Regidx 0x00#5, bop.BGE))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc (0x0010#13)) := by
  have h12 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_bge_taken (0x0010#13) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0c#5)
    (0#64) v12 pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_zero _) (rX_bits_x12 _ v12 h12) hpc₂ hmisa₂ htgt hv

theorem exec_blez_a2_nottaken (σ : MState) (pc : BitVec 64) (v12 : BitVec 64)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hv : zopz0zKzJ_s (0#64) v12 = false) :
    (execute (instruction.BTYPE (0x0010#13, regidx.Regidx 0x0c#5, regidx.Regidx 0x00#5, bop.BGE))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have h12 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  exact execute_btype_bge_nottaken (0x0010#13) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0c#5)
    (0#64) v12 (afterNextPC (afterPrelude σ) pc)
    (rX_bits_zero _) (rX_bits_x12 _ v12 h12) hv

theorem site_800046c4_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : __hidden___udivdi3Loaded σ.mem)
    (hpcv : pc = (0x800046c4#64 : BitVec 64)) (hv : zopz0zKzJ_s (0#64) v12 = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0010#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __hidden___udivdi3_at_800046c4 hmem
  exact stepObs_branch_taken σ i u (0x800046c4#64) vminstret (0x0010#13)
    (regidx.Regidx 0x00#5) (regidx.Regidx 0x0c#5) bop.BGE (0x00c05863#32)
    (0x63#8) (0x58#8) (0xc0#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00c05863 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_blez_a2_taken σ (0x800046c4#64) v12 hG hpc hx12 (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_800046c4_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : __hidden___udivdi3Loaded σ.mem)
    (hpcv : pc = (0x800046c4#64 : BitVec 64)) (hv : zopz0zKzJ_s (0#64) v12 = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __hidden___udivdi3_at_800046c4 hmem
  exact stepObs_branch_nottaken σ i u (0x800046c4#64) vminstret (0x0010#13)
    (regidx.Regidx 0x00#5) (regidx.Regidx 0x0c#5) bop.BGE (0x00c05863#32)
    (0x63#8) (0x58#8) (0xc0#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00c05863 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_blez_a2_nottaken σ (0x800046c4#64) v12 hx12 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800046d0 — `bltu a2,a1` (rs1 = x12, rs2 = x11), imm 0x1ff4 → 0x800046c4 (back-edge) -/

theorem exec_bltu_a2_a1_taken (σ : MState) (pc : BitVec 64) (v12 v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx12 : σ.regs.get? Register.x12 = some v12) (hx11 : σ.regs.get? Register.x11 = some v11)
    (htgt : (pc + sign_extend (m := 64) (0x1ff4#13)).toNat % 4 = 0)
    (hv : zopz0zI_u v12 v11 = true) :
    (execute (instruction.BTYPE (0x1ff4#13, regidx.Regidx 0x0b#5, regidx.Regidx 0x0c#5, bop.BLTU))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc (0x1ff4#13)) := by
  have h12 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  have h11 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_bltu_taken (0x1ff4#13) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0b#5)
    v12 v11 pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x12 _ v12 h12) (rX_bits_x11 _ v11 h11) hpc₂ hmisa₂ htgt hv

theorem exec_bltu_a2_a1_nottaken (σ : MState) (pc : BitVec 64) (v12 v11 : BitVec 64)
    (hx12 : σ.regs.get? Register.x12 = some v12) (hx11 : σ.regs.get? Register.x11 = some v11)
    (hv : zopz0zI_u v12 v11 = false) :
    (execute (instruction.BTYPE (0x1ff4#13, regidx.Regidx 0x0b#5, regidx.Regidx 0x0c#5, bop.BLTU))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have h12 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  have h11 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  exact execute_btype_bltu_nottaken (0x1ff4#13) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0b#5)
    v12 v11 (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x12 _ v12 h12) (rX_bits_x11 _ v11 h11) hv

theorem site_800046d0_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12) (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : __hidden___udivdi3Loaded σ.mem)
    (hpcv : pc = (0x800046d0#64 : BitVec 64)) (hv : zopz0zI_u v12 v11 = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x1ff4#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __hidden___udivdi3_at_800046d0 hmem
  exact stepObs_branch_taken σ i u (0x800046d0#64) vminstret (0x1ff4#13)
    (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0b#5) bop.BLTU (0xfeb66ae3#32)
    (0xe3#8) (0x6a#8) (0xb6#8) (0xfe#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_feb66ae3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bltu_a2_a1_taken σ (0x800046d0#64) v12 v11 hG hpc hx12 hx11 (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_800046d0_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12) (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : __hidden___udivdi3Loaded σ.mem)
    (hpcv : pc = (0x800046d0#64 : BitVec 64)) (hv : zopz0zI_u v12 v11 = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __hidden___udivdi3_at_800046d0 hmem
  exact stepObs_branch_nottaken σ i u (0x800046d0#64) vminstret (0x1ff4#13)
    (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0b#5) bop.BLTU (0xfeb66ae3#32)
    (0xe3#8) (0x6a#8) (0xb6#8) (0xfe#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_feb66ae3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bltu_a2_a1_nottaken σ (0x800046d0#64) v12 v11 hx12 hx11 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800046d8 — `bltu a1,a2` (rs1 = x11, rs2 = x12), imm 0x000c → 0x800046e4 -/

theorem exec_bltu_a1_a2_taken (σ : MState) (pc : BitVec 64) (v11 v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx11 : σ.regs.get? Register.x11 = some v11) (hx12 : σ.regs.get? Register.x12 = some v12)
    (htgt : (pc + sign_extend (m := 64) (0x000c#13)).toNat % 4 = 0)
    (hv : zopz0zI_u v11 v12 = true) :
    (execute (instruction.BTYPE (0x000c#13, regidx.Regidx 0x0c#5, regidx.Regidx 0x0b#5, bop.BLTU))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc (0x000c#13)) := by
  have h11 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  have h12 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_bltu_taken (0x000c#13) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0c#5)
    v11 v12 pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x11 _ v11 h11) (rX_bits_x12 _ v12 h12) hpc₂ hmisa₂ htgt hv

theorem exec_bltu_a1_a2_nottaken (σ : MState) (pc : BitVec 64) (v11 v12 : BitVec 64)
    (hx11 : σ.regs.get? Register.x11 = some v11) (hx12 : σ.regs.get? Register.x12 = some v12)
    (hv : zopz0zI_u v11 v12 = false) :
    (execute (instruction.BTYPE (0x000c#13, regidx.Regidx 0x0c#5, regidx.Regidx 0x0b#5, bop.BLTU))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have h11 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  have h12 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  exact execute_btype_bltu_nottaken (0x000c#13) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0c#5)
    v11 v12 (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x11 _ v11 h11) (rX_bits_x12 _ v12 h12) hv

theorem site_800046d8_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11) (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : __hidden___udivdi3Loaded σ.mem)
    (hpcv : pc = (0x800046d8#64 : BitVec 64)) (hv : zopz0zI_u v11 v12 = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x000c#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __hidden___udivdi3_at_800046d8 hmem
  exact stepObs_branch_taken σ i u (0x800046d8#64) vminstret (0x000c#13)
    (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0c#5) bop.BLTU (0x00c5e663#32)
    (0x63#8) (0xe6#8) (0xc5#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00c5e663 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bltu_a1_a2_taken σ (0x800046d8#64) v11 v12 hG hpc hx11 hx12 (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_800046d8_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11) (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : __hidden___udivdi3Loaded σ.mem)
    (hpcv : pc = (0x800046d8#64 : BitVec 64)) (hv : zopz0zI_u v11 v12 = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __hidden___udivdi3_at_800046d8 hmem
  exact stepObs_branch_nottaken σ i u (0x800046d8#64) vminstret (0x000c#13)
    (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0c#5) bop.BLTU (0x00c5e663#32)
    (0x63#8) (0xe6#8) (0xc5#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00c5e663 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bltu_a1_a2_nottaken σ (0x800046d8#64) v11 v12 hx11 hx12 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800046ec — `bnez a3` = `bne a3,x0` (rs1 = x13, rs2 = x0), imm 0x1fec → 0x800046d8 (back-edge) -/

theorem exec_bnez_a3_taken (σ : MState) (pc : BitVec 64) (v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (htgt : (pc + sign_extend (m := 64) (0x1fec#13)).toNat % 4 = 0)
    (hv : (v13 != (0#64)) = true) :
    (execute (instruction.BTYPE (0x1fec#13, regidx.Regidx 0x00#5, regidx.Regidx 0x0d#5, bop.BNE))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc (0x1fec#13)) := by
  have h13 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_bne_taken (0x1fec#13) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x00#5)
    v13 (0#64) pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x13 _ v13 h13) (rX_bits_zero _) hpc₂ hmisa₂ htgt hv

theorem exec_bnez_a3_nottaken (σ : MState) (pc : BitVec 64) (v13 : BitVec 64)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hv : (v13 != (0#64)) = false) :
    (execute (instruction.BTYPE (0x1fec#13, regidx.Regidx 0x00#5, regidx.Regidx 0x0d#5, bop.BNE))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have h13 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  exact execute_btype_bne_nottaken (0x1fec#13) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x00#5)
    v13 (0#64) (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x13 _ v13 h13) (rX_bits_zero _) hv

theorem site_800046ec_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : __hidden___udivdi3Loaded σ.mem)
    (hpcv : pc = (0x800046ec#64 : BitVec 64)) (hv : (v13 != (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x1fec#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __hidden___udivdi3_at_800046ec hmem
  exact stepObs_branch_taken σ i u (0x800046ec#64) vminstret (0x1fec#13)
    (regidx.Regidx 0x0d#5) (regidx.Regidx 0x00#5) bop.BNE (0xfe0696e3#32)
    (0xe3#8) (0x96#8) (0x06#8) (0xfe#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_fe0696e3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bnez_a3_taken σ (0x800046ec#64) v13 hG hpc hx13 (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_800046ec_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : __hidden___udivdi3Loaded σ.mem)
    (hpcv : pc = (0x800046ec#64 : BitVec 64)) (hv : (v13 != (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __hidden___udivdi3_at_800046ec hmem
  exact stepObs_branch_nottaken σ i u (0x800046ec#64) vminstret (0x1fec#13)
    (regidx.Regidx 0x0d#5) (regidx.Regidx 0x00#5) bop.BNE (0xfe0696e3#32)
    (0xe3#8) (0x96#8) (0x06#8) (0xfe#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_fe0696e3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bnez_a3_nottaken σ (0x800046ec#64) v13 hx13 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800046f0 — `ret` = `jalr x0,ra,0` (rs1 = x1 = ra) -/

theorem site_800046f0
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : __hidden___udivdi3Loaded σ.mem)
    (hpcv : pc = (0x800046f0#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := __hidden___udivdi3_at_800046f0 hmem
  have hx1₂ : (rX_bits (regidx.Regidx 0x01#5)).run (afterNextPC (afterPrelude σ) (0x800046f0#64))
      = .ok vra (afterNextPC (afterPrelude σ) (0x800046f0#64)) := by
    apply rX_bits_x1
    rw [get?_afterNextPC σ (0x800046f0#64) _ (by decide) (by decide)]; exact hx1
  exact stepObs_jr σ i u (0x800046f0#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    hx1₂ htgt hi

end Vsa.Sim

