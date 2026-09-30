import Vsa.Sim.StepAlu
import Vsa.Sim.StepBranch
import Vsa.Sim.StepJump
import Vsa.Sim.StepStore

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

def ReadsLikePost (σ' spost : MState) : Prop :=
  (∀ R : Register, (Register.mcycle == R) = false → (Register.mtime == R) = false →
    (Register.mip == R) = false → σ'.regs.get? R = spost.regs.get? R)
  ∧ σ'.sailOutput = spost.sailOutput

theorem ReadsLikePost.rfl (s : MState) : ReadsLikePost s s :=
  ⟨fun _ _ _ _ => Eq.refl _, Eq.refl _⟩

/-- **Commit (observational step).** Any retiring instruction, tick or not. -/
theorem stepObs_retire {σ s : MState} {i u : Nat}
    (hts : (try_step u true).run σ = .ok false s) (hG : GoodState σ) (hGs : GoodState s)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = s.mem ∧ ReadsLikePost σ' s := by
  by_cases htick : i + 1 = 2
  · obtain ⟨vmip, hmip⟩ := hGs.mip
    obtain ⟨vmtime, hmtime⟩ := hGs.mtime
    obtain ⟨vmtimecmp, hmtimecmp⟩ := hGs.mtimecmp
    obtain ⟨vmcycle, hmcycle⟩ := hGs.mcycle
    obtain ⟨hstep, hGt⟩ := step_retire_tick hts hG hGs hmip hmtime hmtimecmp hmcycle htick
    exact ⟨_, 0, hstep, by decide, hGt, rfl, fun R hmc hmt hmi => by reg_reads [hmc, hmt, hmi], rfl⟩
  · obtain ⟨hstep, hGt⟩ := step_retire_notick hts hG hGs htick
    exact ⟨_, i + 1, hstep, by omega, hGt, rfl, ReadsLikePost.rfl _⟩

theorem ReadsLikePost.out {σ' spost : MState} (h : ReadsLikePost σ' spost) :
    σ'.sailOutput = spost.sailOutput := h.2

theorem sailOutput_sigmaPost_alu (σ : MState) (pc vminstret : BitVec 64)
    (rd_reg : Register) (v : RegisterType rd_reg) :
    (sigmaPost_alu σ pc vminstret rd_reg v).sailOutput = σ.sailOutput := rfl

theorem sailOutput_sigmaPost_branch_taken (σ : MState) (pc vminstret : BitVec 64)
    (imm : BitVec 13) :
    (sigmaPost_branch_taken σ pc vminstret imm).sailOutput = σ.sailOutput := rfl

theorem sailOutput_sigmaPost_branch_nottaken (σ : MState) (pc vminstret : BitVec 64) :
    (sigmaPost_branch_nottaken σ pc vminstret).sailOutput = σ.sailOutput := rfl

theorem sailOutput_sigmaPost_jump_x0 (σ : MState) (pc vminstret tgt : BitVec 64) :
    (sigmaPost_jump_x0 σ pc vminstret tgt).sailOutput = σ.sailOutput := rfl

theorem sailOutput_sigmaPost_jal (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 21)
    (rd_reg : Register) (link : RegisterType rd_reg) :
    (sigmaPost_jal σ pc vminstret imm rd_reg link).sailOutput = σ.sailOutput := rfl

theorem sailOutput_sigmaPost_store (σ : MState) (pc vminstret : BitVec 64)
    (m' : Std.ExtHashMap Nat (BitVec 8)) :
    (sigmaPost_store σ pc vminstret m').sailOutput = σ.sailOutput := rfl

theorem stepObs_alu
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (ast : instruction) (rd_reg : Register) (v : RegisterType rd_reg)
    (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ) = .ok ast (afterPrelude σ))
    (hexec : (execute ast).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc rd_reg v))
    (hrd_npc : (rd_reg == Register.nextPC) = false)
    (hrd_mi : (rd_reg == Register.minstret_increment) = false)
    (hrd_ms : (rd_reg == Register.minstret) = false)
    (hrd_hart : (rd_reg == Register.hart_state) = false)
    (hrd : NonPinned rd_reg)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ' (sigmaPost_alu σ pc vminstret rd_reg v) :=
  stepObs_retire (try_step_alu σ u pc vminstret w ast rd_reg v b0 b1 b2 b3
    hG hpc hminstret hword hnotrvc hdec hexec hrd_npc hrd_mi hrd_ms hrd_hart hb0 hb1 hb2 hb3 hlo hhi halign)
    hG (goodstate_sigmaPost_alu σ pc vminstret rd_reg hrd v hG) hi

theorem stepObs_branch_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (imm : BitVec 13) (rs1 rs2 : regidx) (op : bop)
    (w : BitVec 32) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.BTYPE (imm, rs2, rs1, op)) (afterPrelude σ))
    (hexec : (execute (instruction.BTYPE (imm, rs2, rs1, op))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc imm))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret imm) := by
  exact stepObs_retire (try_step_branch_taken σ u pc vminstret imm rs1 rs2 op w b0 b1 b2 b3
    hG hpc hminstret hword hnotrvc hdec hexec hb0 hb1 hb2 hb3 hlo hhi halign)
    hG (goodstate_sigmaPost_branch_taken σ pc vminstret imm hG) hi

theorem stepObs_branch_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (imm : BitVec 13) (rs1 rs2 : regidx) (op : bop)
    (w : BitVec 32) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.BTYPE (imm, rs2, rs1, op)) (afterPrelude σ))
    (hexec : (execute (instruction.BTYPE (imm, rs2, rs1, op))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧ ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) :=
  stepObs_retire (try_step_branch_nottaken σ u pc vminstret imm rs1 rs2 op w b0 b1 b2 b3
    hG hpc hminstret hword hnotrvc hdec hexec hb0 hb1 hb2 hb3 hlo hhi halign)
    hG (goodstate_sigmaPost_branch_nottaken σ pc vminstret hG) hi

theorem stepObs_jr
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vrs1 : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs1 : regidx) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JALR (imm, rs1, regidx.Regidx 0x00#5)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vrs1 (afterNextPC (afterPrelude σ) pc))
    (htgt : (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)) :=
  stepObs_retire (try_step_jr σ u pc vminstret vrs1 w imm rs1 b0 b1 b2 b3
    hG hpc hminstret hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec hrs1 htgt)
    hG (goodstate_sigmaPost_jump_x0 σ pc vminstret _ hG) hi

theorem stepObs_j
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 21) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JAL (imm, regidx.Regidx 0x00#5)) (afterPrelude σ))
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) imm)) :=
  stepObs_retire (try_step_j σ u pc vminstret w imm b0 b1 b2 b3
    hG hpc hminstret hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec htgt)
    hG (goodstate_sigmaPost_jump_x0 σ pc vminstret _ hG) hi

theorem stepObs_jal
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 21) (rd : regidx) (rd_reg : Register)
    (link : RegisterType rd_reg) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JAL (imm, rd)) (afterPrelude σ))
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hrd_npc : (rd_reg == Register.nextPC) = false)
    (hrd_mi : (rd_reg == Register.minstret_increment) = false)
    (hrd_ms : (rd_reg == Register.minstret) = false)
    (hrd_hart : (rd_reg == Register.hart_state) = false)
    (hrd : NonPinned rd_reg)
    (hwr : (wX_bits rd (BitVec.addInt pc 4)).run
        {(afterNextPC (afterPrelude σ) pc) with
          regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
            (pc + sign_extend (m := 64) imm)}
        = .ok () (sigma3_jal σ pc imm rd_reg link))
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jal σ pc vminstret imm rd_reg link) := by
  exact stepObs_retire (try_step_jal σ u pc vminstret w imm rd rd_reg link b0 b1 b2 b3 hG hpc hminstret
    hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec htgt hrd_npc hrd_mi hrd_ms hrd_hart hwr)
    hG (goodstate_sigmaPost_jal σ pc vminstret imm rd_reg hrd link hG) hi

theorem stepObs_store
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (ast : instruction) (m' : Std.ExtHashMap Nat (BitVec 8))
    (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ) = .ok ast (afterPrelude σ))
    (hexec : (execute ast).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_store σ pc m'))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = m' ∧ ReadsLikePost σ' (sigmaPost_store σ pc vminstret m') :=
  stepObs_retire (try_step_store σ u pc vminstret w ast m' b0 b1 b2 b3
    hG hpc hminstret hword hnotrvc hdec hexec hb0 hb1 hb2 hb3 hlo hhi halign)
    hG (goodstate_sigmaPost_store σ pc vminstret m' hG) hi

end Vsa.Sim
