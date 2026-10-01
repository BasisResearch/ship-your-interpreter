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
    (rX_bits_gpr _ 10 (by decide) (by decide) v10 hx10₂)
    (wX_bits_gpr _ (v10 + sign_extend (m := 64) (0x000#12)) 12 (by decide) (by decide))

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
  exact stepObs_exec _ vminstret (Fetched.of_word (0x00050613#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_mv_a2_a0 σ (0x80004640#64) v10 hx10)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

theorem exec_li_a0_0 (σ : MState) (pc : BitVec 64) :
    (execute (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12))) :=
  execute_itype_addi_char (0x000#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5) (0#64)
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12)))
    (rX_bits_zero _)
    (wX_bits_gpr _ ((0#64) + sign_extend (m := 64) (0x000#12)) 10 (by decide) (by decide))

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
  exact stepObs_exec _ vminstret (Fetched.of_word (0x00000513#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_li_a0_0 σ (0x80004644#64))
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

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
    (rX_bits_gpr _ 11 (by decide) (by decide) v11 hx11₂)
    (wX_bits_gpr _ (v11 &&& sign_extend (m := 64) (0x001#12)) 13 (by decide) (by decide))

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
  exact stepObs_exec _ vminstret (Fetched.of_word (0x0015f693#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_andi_a3_a1 σ (0x80004648#64) v11 hx11)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

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
    (rX_bits_gpr _ 10 (by decide) (by decide) v10 hx10₂) (rX_bits_gpr _ 12 (by decide) (by decide) v12 hx12₂)
    (wX_bits_gpr _ (v10 + v12) 10 (by decide) (by decide))

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
  exact stepObs_exec _ vminstret (Fetched.of_word (0x00c50533#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_add_a0_a0_a2 σ (0x80004650#64) v10 v12 hx10 hx12)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

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
    (rX_bits_gpr _ 11 (by decide) (by decide) v11 hx11₂)
    (wX_bits_gpr _ (shift_bits_right v11 (Sail.BitVec.extractLsb (0x01#6) 5 0)) 11 (by decide) (by decide))

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
  exact stepObs_exec _ vminstret (Fetched.of_word (0x0015d593#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_srli_a1_a1 σ (0x80004654#64) v11 hx11)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

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
    (rX_bits_gpr _ 12 (by decide) (by decide) v12 hx12₂)
    (wX_bits_gpr _ (shift_bits_left v12 (Sail.BitVec.extractLsb (0x01#6) 5 0)) 12 (by decide) (by decide))

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
  exact stepObs_exec _ vminstret (Fetched.of_word (0x00161613#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_slli_a2_a2 σ (0x80004658#64) v12 hx12)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

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
    (rX_bits_gpr _ 13 (by decide) (by decide) v13 hx13₂) (rX_bits_zero _) hpc₂ hmisa₂ htgt hv

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
    (rX_bits_gpr _ 13 (by decide) (by decide) v13 hx13₂) (rX_bits_zero _) hv

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
  exact stepObs_exec _ vminstret (Fetched.of_word (0x00068463#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_beqz_a3_taken σ (0x8000464c#64) v13 hG hpc hx13 (by decide) hv)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

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
  exact stepObs_exec _ vminstret (Fetched.of_word (0x00068463#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_beqz_a3_nottaken σ (0x8000464c#64) v13 hx13 hv)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    (hG.prelude _) hi

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
    (rX_bits_gpr _ 11 (by decide) (by decide) v11 hx11₂) (rX_bits_zero _) hpc₂ hmisa₂ htgt hv

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
    (rX_bits_gpr _ 11 (by decide) (by decide) v11 hx11₂) (rX_bits_zero _) hv

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
  exact stepObs_exec _ vminstret (Fetched.of_word (0xfe0596e3#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_bnez_a1_taken σ (0x8000465c#64) v11 hG hpc hx11 (by decide) hv)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

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
  exact stepObs_exec _ vminstret (Fetched.of_word (0xfe0596e3#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_bnez_a1_nottaken σ (0x8000465c#64) v11 hx11 hv)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    (hG.prelude _) hi

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
    apply rX_bits_gpr _ 1 (by decide) (by decide); simp only [gprGet]
    rw [get?_afterNextPC σ (0x80004660#64) _ (by decide) (by decide)]; exact hx1
  exact stepObs_exec _ vminstret (Fetched.of_word (0x00008067#32) hG hpc hb0 hb1 hb2 hb3)
    (execute_jalr_x0_char (0x000#12) (regidx.Regidx 0x01#5) _ vra _ (by reg_reads [hG.misa])
      (by reg_reads [hG.cur_privilege]) (by reg_reads [hG.mseccfg]) (by reg_reads []) hx1₂ htgt)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

end Vsa.Sim
