import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeNF
import Vsa.Sim.Code.«__muldi3»

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code (__muldi3Loaded __muldi3_at_80004640 __muldi3_at_80004644 __muldi3_at_80004648 __muldi3_at_8000464c __muldi3_at_80004650 __muldi3_at_80004654 __muldi3_at_80004658 __muldi3_at_8000465c __muldi3_at_80004660)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

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

theorem mv_a2_a0_word :
    (((0x00#8).append (0x05#8)).append (0x06#8)).append (0x13#8) = (0x00050613#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem mv_a2_a0_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0x06#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

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
    (Vsa.Sim.decodeW (w := 0x00050613#32) (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_mv_a2_a0 σ (0x80004640#64) v10 hx10)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

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
    (Vsa.Sim.decodeW (w := 0x00000513#32) (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_li_a0_0 σ (0x80004644#64))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

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
    (Vsa.Sim.decodeW (w := 0x0015f693#32) (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_andi_a3_a1 σ (0x80004648#64) v11 hx11)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

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
    (Vsa.Sim.decodeW (w := 0x00c50533#32) (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_add_a0_a0_a2 σ (0x80004650#64) v10 v12 hx10 hx12)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

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
    (Vsa.Sim.decodeW (w := 0x0015d593#32) (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_srli_a1_a1 σ (0x80004654#64) v11 hx11)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

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
    (Vsa.Sim.decodeW (w := 0x00161613#32) (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_slli_a2_a2 σ (0x80004658#64) v12 hx12)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem beqz_a3_word :
    (((0x00#8).append (0x06#8)).append (0x84#8)).append (0x63#8) = (0x00068463#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem beqz_a3_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x06#8)).append (0x84#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

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
    (Vsa.Sim.decodeW (w := 0x00068463#32) (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beqz_a3_taken σ (0x8000464c#64) v13 hG hpc hx13 (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

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
    (Vsa.Sim.decodeW (w := 0x00068463#32) (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beqz_a3_nottaken σ (0x8000464c#64) v13 hx13 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem bnez_a1_word :
    (((0xfe#8).append (0x05#8)).append (0x96#8)).append (0xe3#8) = (0xfe0596e3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem bnez_a1_notrvc :
    Sail.BitVec.extractLsb ((((0xfe#8).append (0x05#8)).append (0x96#8)).append (0xe3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

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
    (Vsa.Sim.decodeW (w := 0xfe0596e3#32) (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bnez_a1_taken σ (0x8000465c#64) v11 hG hpc hx11 (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

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
    (Vsa.Sim.decodeW (w := 0xfe0596e3#32) (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bnez_a1_nottaken σ (0x8000465c#64) v11 hx11 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem ret_word :
    (((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8) = (0x00008067#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem ret_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

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
    (Vsa.Sim.decodeW (w := 0x00008067#32) (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    hx1₂ htgt hi

end Vsa.Sim
