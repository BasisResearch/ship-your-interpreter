import Vsa.Sim.DivLoops
import Vsa.Sim.Code.«__umoddi3»
import Vsa.Sim.Code.«__divdi3»
import Vsa.Sim.Code.«__moddi3»
import Vsa.Sim.DecodeNF

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem post_jal_pc (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 21)
    (rd_reg : Register) (link : RegisterType rd_reg) :
    (sigmaPost_jal σ pc vminstret imm rd_reg link).regs.get? Register.PC
      = some (pc + sign_extend (m := 64) imm) := by
  show ((((sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? Register.PC = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.PC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

theorem post_jal_rd (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 21)
    (rd_reg : Register) (link : RegisterType rd_reg)
    (h1 : (Register.minstret == rd_reg) = false) (h2 : (Register.PC == rd_reg) = false) :
    (sigmaPost_jal σ pc vminstret imm rd_reg link).regs.get? rd_reg = some link := by
  show ((((sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? rd_reg = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h1, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h2, dif_neg, reduceCtorEq, not_false_eq_true]
  show (((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
    (pc + sign_extend (m := 64) imm)).insert rd_reg link).get? rd_reg = _
  rw [Std.ExtDHashMap.get?_insert_self]

theorem obs_jal_pc {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) :
    σ'.regs.get? Register.PC = some (pc + sign_extend (m := 64) imm) :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide) (post_jal_pc σ pc vm imm rd_reg link)

theorem obs_jal_rd {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link))
    (hmc : (Register.mcycle == rd_reg) = false) (hmt : (Register.mtime == rd_reg) = false)
    (hmi : (Register.mip == rd_reg) = false)
    (h1 : (Register.minstret == rd_reg) = false) (h2 : (Register.PC == rd_reg) = false) :
    σ'.regs.get? rd_reg = some link :=
  readback σ' _ hobs rd_reg hmc hmt hmi (post_jal_rd σ pc vm imm rd_reg link h1 h2)

theorem obs_jal_minstret {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
    (by decide) (by decide) (by decide) ?_⟩
  show ((((sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

theorem exec_mv_t0_ra (σ : MState) (pc : BitVec 64) (v1 : BitVec 64)
    (hx1 : σ.regs.get? Register.x1 = some v1) :
    (execute (instruction.ITYPE (0x000#12, regidx.Regidx 0x01#5, regidx.Regidx 0x05#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x5 (v1 + sign_extend (m := 64) (0x000#12))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x1 = some v1 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx1
  exact execute_itype_addi_char (0x000#12) (regidx.Regidx 0x01#5) (regidx.Regidx 0x05#5) v1
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x5 (v1 + sign_extend (m := 64) (0x000#12)))
    (rX_bits_gpr _ 1 (by decide) (by decide) v1 h₂) (wX_bits_gpr _ (v1 + sign_extend (m := 64) (0x000#12)) 5 (by decide) (by decide))

theorem exec_mv_a0_a1 (σ : MState) (pc : BitVec 64) (v11 : BitVec 64)
    (hx11 : σ.regs.get? Register.x11 = some v11) :
    (execute (instruction.ITYPE (0x000#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0a#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x10 (v11 + sign_extend (m := 64) (0x000#12))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  exact execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0a#5) v11
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x10 (v11 + sign_extend (m := 64) (0x000#12)))
    (rX_bits_gpr _ 11 (by decide) (by decide) v11 h₂) (wX_bits_gpr _ (v11 + sign_extend (m := 64) (0x000#12)) 10 (by decide) (by decide))

theorem exec_neg_a0 (σ : MState) (pc : BitVec 64) (v10 : BitVec 64)
    (hx10 : σ.regs.get? Register.x10 = some v10) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0a#5, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, rop.SUB))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x10 ((0#64) - v10)) := by
  have h10 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  exact execute_rtype_sub_char (regidx.Regidx 0x0a#5) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5)
    (0#64) v10 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x10 ((0#64) - v10))
    (rX_bits_zero _) (rX_bits_gpr _ 10 (by decide) (by decide) v10 h10) (wX_bits_gpr _ ((0#64) - v10) 10 (by decide) (by decide))

theorem exec_neg_a1 (σ : MState) (pc : BitVec 64) (v11 : BitVec 64)
    (hx11 : σ.regs.get? Register.x11 = some v11) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0b#5, regidx.Regidx 0x00#5, regidx.Regidx 0x0b#5, rop.SUB))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x11 ((0#64) - v11)) := by
  have h11 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  exact execute_rtype_sub_char (regidx.Regidx 0x0b#5) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0b#5)
    (0#64) v11 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x11 ((0#64) - v11))
    (rX_bits_zero _) (rX_bits_gpr _ 11 (by decide) (by decide) v11 h11) (wX_bits_gpr _ ((0#64) - v11) 11 (by decide) (by decide))

theorem exec_neg_a0_a1 (σ : MState) (pc : BitVec 64) (v11 : BitVec 64)
    (hx11 : σ.regs.get? Register.x11 = some v11) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0b#5, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, rop.SUB))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x10 ((0#64) - v11)) := by
  have h11 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  exact execute_rtype_sub_char (regidx.Regidx 0x0b#5) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5)
    (0#64) v11 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x10 ((0#64) - v11))
    (rX_bits_zero _) (rX_bits_gpr _ 11 (by decide) (by decide) v11 h11) (wX_bits_gpr _ ((0#64) - v11) 10 (by decide) (by decide))

theorem exec_bltz_a0_taken (σ : MState) (pc : BitVec 64) (v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (htgt : (pc + sign_extend (m := 64) (0x0060#13)).toNat % 4 = 0)
    (hv : zopz0zI_s v10 (0#64) = true) :
    (execute (instruction.BTYPE (0x0060#13, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, bop.BLT))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc (0x0060#13)) := by
  have h10 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_blt_taken (0x0060#13) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x00#5)
    v10 (0#64) pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_gpr _ 10 (by decide) (by decide) v10 h10) (rX_bits_zero _) hpc₂ hmisa₂ htgt hv

theorem exec_bltz_a0_nottaken (σ : MState) (pc : BitVec 64) (v10 : BitVec 64)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hv : zopz0zI_s v10 (0#64) = false) :
    (execute (instruction.BTYPE (0x0060#13, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, bop.BLT))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have h10 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  exact execute_btype_blt_nottaken (0x0060#13) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x00#5)
    v10 (0#64) (afterNextPC (afterPrelude σ) pc)
    (rX_bits_gpr _ 10 (by decide) (by decide) v10 h10) (rX_bits_zero _) hv

theorem site2_800046a4_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Vsa.Sim.Code.__divdi3Loaded σ.mem)
    (hpcv : pc = (0x800046a4#64 : BitVec 64)) (hv : zopz0zI_s v10 (0#64) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0060#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__divdi3_at_800046a4 hmem
  exact stepObs_exec _ vminstret (Fetched.of_word (0x06054063#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_bltz_a0_taken σ (0x800046a4#64) v10 hG hpc hx10 (by decide) hv)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

theorem site2_800046a4_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Vsa.Sim.Code.__divdi3Loaded σ.mem)
    (hpcv : pc = (0x800046a4#64 : BitVec 64)) (hv : zopz0zI_s v10 (0#64) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__divdi3_at_800046a4 hmem
  exact stepObs_exec _ vminstret (Fetched.of_word (0x06054063#32) hG hpc hb0 hb1 hb2 hb3)
    (exec_bltz_a0_nottaken σ (0x800046a4#64) v10 hx10 hv)
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    (hG.prelude _) hi

theorem site2_80004710
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Vsa.Sim.Code.__umoddi3Loaded σ.mem)
    (hpcv : pc = (0x80004710#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) (0x1fff9c#21))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__umoddi3_at_80004710 hmem
  exact stepObs_exec _ vminstret (Fetched.of_word (0xf9dff06f#32) hG hpc hb0 hb1 hb2 hb3)
    (execute_jal_x0_char (0x1fff9c#21) _ (0x80004710#64) _ _ (by reg_reads []) (by reg_reads [hpc])
      (by reg_reads [hG.misa]) (by decide))
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩
    ((hG.prelude _).insert_nonpinned (by decide) _) hi

end Vsa.Sim
