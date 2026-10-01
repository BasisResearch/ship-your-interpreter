import Vsa.Sim.StepAlu
import Vsa.Sim.StepBranch
import Vsa.Sim.StepJump
import Vsa.Sim.StepStore
import Vsa.Sim.DecodeNF

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

/-- The fetched instruction from a concrete word: the four bytes at `pc`, the range, alignment,
compressed-bit and word facts by `decide`, and the decode by `rfl` along `decodeN`. -/
theorem Fetched.of_word {σ : MState} {pc : BitVec 64} {ast : instruction} (w : BitVec 32)
    {b0 b1 b2 b3 : BitVec 8} (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat := by decide) (hhi : pc.toNat + 4 ≤ tohostAddr := by decide)
    (halign : pc.toNat % 4 = 0 := by decide)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0
      = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide)
    (hword : (((b3.append b2).append b1).append b0) = w := by apply BitVec.eq_of_toNat_eq; decide)
    (hnf : decodeN w (afterPrelude σ) = .ok ast (afterPrelude σ) := by rfl) :
    Fetched σ pc ast :=
  Fetched.of_bytes hG hpc hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword
    (decodeW (afterPrelude σ) (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg) hnf)

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

end Vsa.Sim
