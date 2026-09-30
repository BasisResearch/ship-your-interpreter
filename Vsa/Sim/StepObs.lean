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

/-- **Commit (observational step from the fetched word).** Any retiring instruction: the
fetched word, its `execute` fact, the four retire reads and the pins of the post-execute state. -/
theorem stepObs_exec {σ σ3 : MState} {i u : Nat} {pc : BitVec 64} (npc vm : BitVec 64)
    {ast : instruction} (F : Fetched σ pc ast)
    (hexec : (execute ast).run (afterNextPC (afterPrelude σ) pc) = .ok RETIRE_SUCCESS σ3)
    (R : RetireReads σ3 npc vm) (hG3 : GoodState σ3) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ3.mem ∧ ReadsLikePost σ' (retirePost σ3 npc vm) :=
  stepObs_retire (try_step_retire F hexec R) F.good (hG3.retirePost npc vm) hi

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
      ReadsLikePost σ' (sigmaPost_jal σ pc vminstret imm rd_reg link) :=
  stepObs_exec _ vminstret (Fetched.of_bytes hG hpc hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec)
    (execute_jal_char imm rd _ pc _ _ _ (by reg_reads []) (by reg_reads [hpc]) (by reg_reads [hG.misa])
      htgt hwr)
    ⟨by reg_reads [hrd_hart, hG.hart_state], by reg_reads [hrd_npc], by reg_reads [hrd_mi],
     by reg_reads [hrd_ms, hminstret]⟩
    (((hG.prelude _).insert_nonpinned (by decide) _).insert_nonpinned (r := rd_reg) hrd link) hi

end Vsa.Sim
