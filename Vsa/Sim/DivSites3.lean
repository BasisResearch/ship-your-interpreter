import Vsa.Sim.DivSites2
import Vsa.Sim.DecodeNF

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem exec_bltz_a1_taken (σ : MState) (pc : BitVec 64) (imm : BitVec 13) (v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hv : zopz0zI_s v11 (0#64) = true) :
    (execute (instruction.BTYPE (imm, regidx.Regidx 0x00#5, regidx.Regidx 0x0b#5, bop.BLT))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc imm) := by
  have h11 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_blt_taken imm (regidx.Regidx 0x0b#5) (regidx.Regidx 0x00#5)
    v11 (0#64) pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_gpr _ 11 (by decide) (by decide) v11 h11) (rX_bits_zero _) hpc₂ hmisa₂ htgt hv

theorem exec_bltz_a1_nottaken (σ : MState) (pc : BitVec 64) (imm : BitVec 13) (v11 : BitVec 64)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hv : zopz0zI_s v11 (0#64) = false) :
    (execute (instruction.BTYPE (imm, regidx.Regidx 0x00#5, regidx.Regidx 0x0b#5, bop.BLT))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have h11 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  exact execute_btype_blt_nottaken imm (regidx.Regidx 0x0b#5) (regidx.Regidx 0x00#5)
    v11 (0#64) (afterNextPC (afterPrelude σ) pc)
    (rX_bits_gpr _ 11 (by decide) (by decide) v11 h11) (rX_bits_zero _) hv

theorem exec_bltz_a0_taken' (σ : MState) (pc : BitVec 64) (imm : BitVec 13) (v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hv : zopz0zI_s v10 (0#64) = true) :
    (execute (instruction.BTYPE (imm, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, bop.BLT))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc imm) := by
  have h10 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_blt_taken imm (regidx.Regidx 0x0a#5) (regidx.Regidx 0x00#5)
    v10 (0#64) pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_gpr _ 10 (by decide) (by decide) v10 h10) (rX_bits_zero _) hpc₂ hmisa₂ htgt hv

theorem exec_bltz_a0_nottaken' (σ : MState) (pc : BitVec 64) (imm : BitVec 13) (v10 : BitVec 64)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hv : zopz0zI_s v10 (0#64) = false) :
    (execute (instruction.BTYPE (imm, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, bop.BLT))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have h10 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  exact execute_btype_blt_nottaken imm (regidx.Regidx 0x0a#5) (regidx.Regidx 0x00#5)
    v10 (0#64) (afterNextPC (afterPrelude σ) pc)
    (rX_bits_gpr _ 10 (by decide) (by decide) v10 h10) (rX_bits_zero _) hv

theorem exec_bgez_a0_taken (σ : MState) (pc : BitVec 64) (imm : BitVec 13) (v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hv : zopz0zKzJ_s v10 (0#64) = true) :
    (execute (instruction.BTYPE (imm, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, bop.BGE))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc imm) := by
  have h10 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_bge_taken imm (regidx.Regidx 0x0a#5) (regidx.Regidx 0x00#5)
    v10 (0#64) pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_gpr _ 10 (by decide) (by decide) v10 h10) (rX_bits_zero _) hpc₂ hmisa₂ htgt hv

theorem exec_bgez_a0_nottaken (σ : MState) (pc : BitVec 64) (imm : BitVec 13) (v10 : BitVec 64)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hv : zopz0zKzJ_s v10 (0#64) = false) :
    (execute (instruction.BTYPE (imm, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, bop.BGE))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have h10 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  exact execute_btype_bge_nottaken imm (regidx.Regidx 0x0a#5) (regidx.Regidx 0x00#5)
    v10 (0#64) (afterNextPC (afterPrelude σ) pc)
    (rX_bits_gpr _ 10 (by decide) (by decide) v10 h10) (rX_bits_zero _) hv

theorem site3_80004728
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v1 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some v1)
    (hmem : Vsa.Sim.Code.__moddi3Loaded σ.mem)
    (hpcv : pc = (0x80004728#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x5 (v1 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__moddi3_at_80004728 hmem
  exact stepObs_exec _ vminstret (Fetched.of_word (0x00008293#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_mv_t0_ra σ (0x80004728#64) v1 hx1)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

theorem site3_8000472c_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Vsa.Sim.Code.__moddi3Loaded σ.mem)
    (hpcv : pc = (0x8000472c#64 : BitVec 64)) (hv : zopz0zI_s v11 (0#64) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0014#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__moddi3_at_8000472c hmem
  exact stepObs_exec _ vminstret (Fetched.of_word (0x0005ca63#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_bltz_a1_taken σ (0x8000472c#64) (0x0014#13) v11 hG hpc hx11 (by decide) hv)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

theorem site3_8000472c_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Vsa.Sim.Code.__moddi3Loaded σ.mem)
    (hpcv : pc = (0x8000472c#64 : BitVec 64)) (hv : zopz0zI_s v11 (0#64) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__moddi3_at_8000472c hmem
  exact stepObs_exec _ vminstret (Fetched.of_word (0x0005ca63#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_bltz_a1_nottaken σ (0x8000472c#64) (0x0014#13) v11 hx11 hv)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    (hG.prelude _) hi

theorem site3_80004730_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Vsa.Sim.Code.__moddi3Loaded σ.mem)
    (hpcv : pc = (0x80004730#64 : BitVec 64)) (hv : zopz0zI_s v10 (0#64) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0018#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__moddi3_at_80004730 hmem
  exact stepObs_exec _ vminstret (Fetched.of_word (0x00054c63#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_bltz_a0_taken' σ (0x80004730#64) (0x0018#13) v10 hG hpc hx10 (by decide) hv)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

theorem site3_80004730_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Vsa.Sim.Code.__moddi3Loaded σ.mem)
    (hpcv : pc = (0x80004730#64 : BitVec 64)) (hv : zopz0zI_s v10 (0#64) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__moddi3_at_80004730 hmem
  exact stepObs_exec _ vminstret (Fetched.of_word (0x00054c63#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_bltz_a0_nottaken' σ (0x80004730#64) (0x0018#13) v10 hx10 hv)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    (hG.prelude _) hi

theorem site3_80004734
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Vsa.Sim.Code.__moddi3Loaded σ.mem)
    (hpcv : pc = (0x80004734#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jal σ pc vminstret (0x1fff78#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__moddi3_at_80004734 hmem
  refine stepObs_exec _ vminstret (Fetched.of_word (0xf79ff0ef#32) hG hpc hb0 hb1 hb2 hb3)
    (execute_jal_char (0x1fff78#21) (regidx.Regidx 0x01#5) _ (0x80004734#64) _ _ _ (by reg_reads []) (by reg_reads [hpc])
      (by reg_reads [hG.misa]) (by decide) ?_)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    (((hG.prelude _).insert_nonpinned (by decide) _).insert_nonpinned (by decide) _) hi
  exact wX_bits_gpr _ (BitVec.addInt (0x80004734#64) 4) 1 (by decide) (by decide)

theorem site3_80004738
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Vsa.Sim.Code.__moddi3Loaded σ.mem)
    (hpcv : pc = (0x80004738#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 (v11 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__moddi3_at_80004738 hmem
  exact stepObs_exec _ vminstret (Fetched.of_word (0x00058513#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_mv_a0_a1 σ (0x80004738#64) v11 hx11)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

theorem site3_8000473c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vt0 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx5 : σ.regs.get? Register.x5 = some vt0)
    (hmem : Vsa.Sim.Code.__moddi3Loaded σ.mem)
    (hpcv : pc = (0x8000473c#64 : BitVec 64))
    (htgt : (BitVec.update (vt0 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vt0 + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__moddi3_at_8000473c hmem
  have hx5₂ : (rX_bits (regidx.Regidx 0x05#5)).run (afterNextPC (afterPrelude σ) (0x8000473c#64))
      = .ok vt0 (afterNextPC (afterPrelude σ) (0x8000473c#64)) := by
    apply rX_bits_gpr _ 5 (by decide) (by decide); simp only [gprGet]
    rw [get?_afterNextPC σ (0x8000473c#64) _ (by decide) (by decide)]; exact hx5
  exact stepObs_exec _ vminstret (Fetched.of_word (0x00028067#32) hG hpc hb0 hb1 hb2 hb3)
    (execute_jalr_x0_char (0x000#12) (regidx.Regidx 0x05#5) _ vt0 _ (by reg_reads [hG.misa])
      (by reg_reads [hG.cur_privilege]) (by reg_reads [hG.mseccfg]) (by reg_reads []) hx5₂ htgt)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

theorem site3_80004740
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Vsa.Sim.Code.__moddi3Loaded σ.mem)
    (hpcv : pc = (0x80004740#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x11 ((0#64) - v11)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__moddi3_at_80004740 hmem
  exact stepObs_exec _ vminstret (Fetched.of_word (0x40b005b3#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_neg_a1 σ (0x80004740#64) v11 hx11)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

theorem site3_80004744_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Vsa.Sim.Code.__moddi3Loaded σ.mem)
    (hpcv : pc = (0x80004744#64 : BitVec 64)) (hv : zopz0zKzJ_s v10 (0#64) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x1ff0#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__moddi3_at_80004744 hmem
  exact stepObs_exec _ vminstret (Fetched.of_word (0xfe0558e3#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_bgez_a0_taken σ (0x80004744#64) (0x1ff0#13) v10 hG hpc hx10 (by decide) hv)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

theorem site3_80004744_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Vsa.Sim.Code.__moddi3Loaded σ.mem)
    (hpcv : pc = (0x80004744#64 : BitVec 64)) (hv : zopz0zKzJ_s v10 (0#64) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__moddi3_at_80004744 hmem
  exact stepObs_exec _ vminstret (Fetched.of_word (0xfe0558e3#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_bgez_a0_nottaken σ (0x80004744#64) (0x1ff0#13) v10 hx10 hv)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    (hG.prelude _) hi

theorem site3_80004748
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Vsa.Sim.Code.__moddi3Loaded σ.mem)
    (hpcv : pc = (0x80004748#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 ((0#64) - v10)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__moddi3_at_80004748 hmem
  exact stepObs_exec _ vminstret (Fetched.of_word (0x40a00533#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_neg_a0 σ (0x80004748#64) v10 hx10)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

theorem site3_8000474c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Vsa.Sim.Code.__moddi3Loaded σ.mem)
    (hpcv : pc = (0x8000474c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jal σ pc vminstret (0x1fff60#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__moddi3_at_8000474c hmem
  refine stepObs_exec _ vminstret (Fetched.of_word (0xf61ff0ef#32) hG hpc hb0 hb1 hb2 hb3)
    (execute_jal_char (0x1fff60#21) (regidx.Regidx 0x01#5) _ (0x8000474c#64) _ _ _ (by reg_reads []) (by reg_reads [hpc])
      (by reg_reads [hG.misa]) (by decide) ?_)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    (((hG.prelude _).insert_nonpinned (by decide) _).insert_nonpinned (by decide) _) hi
  exact wX_bits_gpr _ (BitVec.addInt (0x8000474c#64) 4) 1 (by decide) (by decide)

theorem site3_80004750
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Vsa.Sim.Code.__moddi3Loaded σ.mem)
    (hpcv : pc = (0x80004750#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 ((0#64) - v11)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__moddi3_at_80004750 hmem
  exact stepObs_exec _ vminstret (Fetched.of_word (0x40b00533#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_neg_a0_a1 σ (0x80004750#64) v11 hx11)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

theorem site3_80004754
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vt0 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx5 : σ.regs.get? Register.x5 = some vt0)
    (hmem : Vsa.Sim.Code.__moddi3Loaded σ.mem)
    (hpcv : pc = (0x80004754#64 : BitVec 64))
    (htgt : (BitVec.update (vt0 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vt0 + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__moddi3_at_80004754 hmem
  have hx5₂ : (rX_bits (regidx.Regidx 0x05#5)).run (afterNextPC (afterPrelude σ) (0x80004754#64))
      = .ok vt0 (afterNextPC (afterPrelude σ) (0x80004754#64)) := by
    apply rX_bits_gpr _ 5 (by decide) (by decide); simp only [gprGet]
    rw [get?_afterNextPC σ (0x80004754#64) _ (by decide) (by decide)]; exact hx5
  exact stepObs_exec _ vminstret (Fetched.of_word (0x00028067#32) hG hpc hb0 hb1 hb2 hb3)
    (execute_jalr_x0_char (0x000#12) (regidx.Regidx 0x05#5) _ vt0 _ (by reg_reads [hG.misa])
      (by reg_reads [hG.cur_privilege]) (by reg_reads [hG.mseccfg]) (by reg_reads []) hx5₂ htgt)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

theorem exec_bgtz_a1_taken (σ : MState) (pc : BitVec 64) (imm : BitVec 13) (v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hv : zopz0zI_s (0#64) v11 = true) :
    (execute (instruction.BTYPE (imm, regidx.Regidx 0x0b#5, regidx.Regidx 0x00#5, bop.BLT))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc imm) := by
  have h11 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_blt_taken imm (regidx.Regidx 0x00#5) (regidx.Regidx 0x0b#5)
    (0#64) v11 pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_zero _) (rX_bits_gpr _ 11 (by decide) (by decide) v11 h11) hpc₂ hmisa₂ htgt hv

theorem exec_bgtz_a1_nottaken (σ : MState) (pc : BitVec 64) (imm : BitVec 13) (v11 : BitVec 64)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hv : zopz0zI_s (0#64) v11 = false) :
    (execute (instruction.BTYPE (imm, regidx.Regidx 0x0b#5, regidx.Regidx 0x00#5, bop.BLT))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have h11 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  exact execute_btype_blt_nottaken imm (regidx.Regidx 0x00#5) (regidx.Regidx 0x0b#5)
    (0#64) v11 (afterNextPC (afterPrelude σ) pc)
    (rX_bits_zero _) (rX_bits_gpr _ 11 (by decide) (by decide) v11 h11) hv

theorem site3_800046a8_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Vsa.Sim.Code.__divdi3Loaded σ.mem)
    (hpcv : pc = (0x800046a8#64 : BitVec 64)) (hv : zopz0zI_s v11 (0#64) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x006c#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__divdi3_at_800046a8 hmem
  exact stepObs_exec _ vminstret (Fetched.of_word (0x0605c663#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_bltz_a1_taken σ (0x800046a8#64) (0x006c#13) v11 hG hpc hx11 (by decide) hv)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

theorem site3_800046a8_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Vsa.Sim.Code.__divdi3Loaded σ.mem)
    (hpcv : pc = (0x800046a8#64 : BitVec 64)) (hv : zopz0zI_s v11 (0#64) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__divdi3_at_800046a8 hmem
  exact stepObs_exec _ vminstret (Fetched.of_word (0x0605c663#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_bltz_a1_nottaken σ (0x800046a8#64) (0x006c#13) v11 hx11 hv)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    (hG.prelude _) hi

theorem site3_80004704
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Vsa.Sim.Code.__umoddi3Loaded σ.mem)
    (hpcv : pc = (0x80004704#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 ((0#64) - v10)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__umoddi3_at_80004704 hmem
  exact stepObs_exec _ vminstret (Fetched.of_word (0x40a00533#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_neg_a0 σ (0x80004704#64) v10 hx10)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

theorem site3_80004708_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Vsa.Sim.Code.__umoddi3Loaded σ.mem)
    (hpcv : pc = (0x80004708#64 : BitVec 64)) (hv : zopz0zI_s (0#64) v11 = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0010#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__umoddi3_at_80004708 hmem
  exact stepObs_exec _ vminstret (Fetched.of_word (0x00b04863#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_bgtz_a1_taken σ (0x80004708#64) (0x0010#13) v11 hG hpc hx11 (by decide) hv)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

theorem site3_80004708_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Vsa.Sim.Code.__umoddi3Loaded σ.mem)
    (hpcv : pc = (0x80004708#64 : BitVec 64)) (hv : zopz0zI_s (0#64) v11 = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__umoddi3_at_80004708 hmem
  exact stepObs_exec _ vminstret (Fetched.of_word (0x00b04863#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_bgtz_a1_nottaken σ (0x80004708#64) (0x0010#13) v11 hx11 hv)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    (hG.prelude _) hi

theorem site3_8000470c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Vsa.Sim.Code.__umoddi3Loaded σ.mem)
    (hpcv : pc = (0x8000470c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x11 ((0#64) - v11)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__umoddi3_at_8000470c hmem
  exact stepObs_exec _ vminstret (Fetched.of_word (0x40b005b3#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_neg_a1 σ (0x8000470c#64) v11 hx11)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

theorem site3_80004714
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Vsa.Sim.Code.__umoddi3Loaded σ.mem)
    (hpcv : pc = (0x80004714#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x11 ((0#64) - v11)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__umoddi3_at_80004714 hmem
  exact stepObs_exec _ vminstret (Fetched.of_word (0x40b005b3#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_neg_a1 σ (0x80004714#64) v11 hx11)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

theorem site3_80004718
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v1 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some v1)
    (hmem : Vsa.Sim.Code.__umoddi3Loaded σ.mem)
    (hpcv : pc = (0x80004718#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x5 (v1 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__umoddi3_at_80004718 hmem
  exact stepObs_exec _ vminstret (Fetched.of_word (0x00008293#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_mv_t0_ra σ (0x80004718#64) v1 hx1)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

theorem site3_8000471c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Vsa.Sim.Code.__umoddi3Loaded σ.mem)
    (hpcv : pc = (0x8000471c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jal σ pc vminstret (0x1fff90#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__umoddi3_at_8000471c hmem
  refine stepObs_exec _ vminstret (Fetched.of_word (0xf91ff0ef#32) hG hpc hb0 hb1 hb2 hb3)
    (execute_jal_char (0x1fff90#21) (regidx.Regidx 0x01#5) _ (0x8000471c#64) _ _ _ (by reg_reads []) (by reg_reads [hpc])
      (by reg_reads [hG.misa]) (by decide) ?_)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    (((hG.prelude _).insert_nonpinned (by decide) _).insert_nonpinned (by decide) _) hi
  exact wX_bits_gpr _ (BitVec.addInt (0x8000471c#64) 4) 1 (by decide) (by decide)

theorem site3_80004720
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Vsa.Sim.Code.__umoddi3Loaded σ.mem)
    (hpcv : pc = (0x80004720#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 ((0#64) - v10)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__umoddi3_at_80004720 hmem
  exact stepObs_exec _ vminstret (Fetched.of_word (0x40a00533#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_neg_a0 σ (0x80004720#64) v10 hx10)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

theorem site3_80004724
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vt0 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx5 : σ.regs.get? Register.x5 = some vt0)
    (hmem : Vsa.Sim.Code.__umoddi3Loaded σ.mem)
    (hpcv : pc = (0x80004724#64 : BitVec 64))
    (htgt : (BitVec.update (vt0 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vt0 + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__umoddi3_at_80004724 hmem
  have hx5₂ : (rX_bits (regidx.Regidx 0x05#5)).run (afterNextPC (afterPrelude σ) (0x80004724#64))
      = .ok vt0 (afterNextPC (afterPrelude σ) (0x80004724#64)) := by
    apply rX_bits_gpr _ 5 (by decide) (by decide); simp only [gprGet]
    rw [get?_afterNextPC σ (0x80004724#64) _ (by decide) (by decide)]; exact hx5
  exact stepObs_exec _ vminstret (Fetched.of_word (0x00028067#32) hG hpc hb0 hb1 hb2 hb3)
    (execute_jalr_x0_char (0x000#12) (regidx.Regidx 0x05#5) _ vt0 _ (by reg_reads [hG.misa])
      (by reg_reads [hG.cur_privilege]) (by reg_reads [hG.mseccfg]) (by reg_reads []) hx5₂ htgt)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

end Vsa.Sim
