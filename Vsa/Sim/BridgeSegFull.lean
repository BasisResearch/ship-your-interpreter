import Vsa.Sim.BridgeSeg
import Vsa.Sim.StepFrameOut

namespace Vsa.Sim
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine

/-- One actual JAL endpoint, retaining its complete nonwritten register frame. -/
structure JalCallFacts (callee link : BitVec 64) (before after : Config) : Prop where
  step : Step before after
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some callee
  ra : after.σ.regs.get? Register.x1 = some link
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  mem : after.σ.mem = before.σ.mem
  nonra : ∀ n, 1 ≤ n → n ≤ 31 → n ≠ 1 → ∀ w,
    gprGet before.σ n = some w → gprGet after.σ n = some w
  frame : StepFrameOut (Register.x1 :: noiseRegs) before.σ after.σ

/-- Retain the frame on the same endpoint as the canonical JAL observation rule. -/
theorem jalCallFacts_of_obs {σ σ' : MState} {i u i' : Nat}
    {pc vm callee link : BitVec 64} {imm : BitVec 21}
    (hs : Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩) (hi : i' < 2)
    (hg : GoodState σ') (hm : σ'.mem = σ.mem)
    (ho : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm Register.x1 link))
    (hc : pc + sign_extend (m := 64) imm = callee) :
    JalCallFacts callee link ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ := by
  obtain ⟨sj, ij, hsj, hij, hgj, hmj, hpj, hraj, hmij, hnr, _⟩ :=
    jalStep_of_obs hs hi hg hm ho hc
  have heq : (⟨sj, ij, u + 1⟩ : Config) = ⟨σ', i', u + 1⟩ :=
    Step.deterministic hsj hs
  cases heq
  exact ⟨hs, hg, hi, hpj, hraj, hmij, hm, hnr, StepFrameOut.of_jal ho⟩

/-- The reflected body and call share one computed memory/register result. -/
structure SegCallFacts (bs : List BBlock) (L : GRegs)
    (lds : List (List (BitVec 8))) (callee link : BitVec 64)
    (before after : Config) : Prop where
  run : Steps before after
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some callee
  ra : after.σ.regs.get? Register.x1 = some link
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  registers : GHolds after.σ (evalBlocks bs (SegEvalState.init L lds)).regs
  mem : after.σ.mem = writeLog before.σ.mem (evalBlocks bs (SegEvalState.init L lds)).log
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, (∀ r ∈ noiseRegs, (r == R) = false) →
    (∀ n ∈ wrChain bs, (gprReg n == R) = false) →
    (Register.x1 == R) = false → after.σ.regs.get? R = before.σ.regs.get? R

/-- Compose any reflected body and observed JAL without discarding non-ABI state. -/
theorem bridgeOfSegFull (bs : List BBlock) (L : GRegs)
    (lds : List (List (BitVec 8))) (pc callee link : BitVec 64) (c : Config)
    (hg : GoodState c.σ) (hp : c.σ.regs.get? Register.PC = some pc)
    (hmi : ∃ w, c.σ.regs.get? Register.minstret = some w)
    (ht : c.tick < 2) (hl : GHolds c.σ L) (hk : KeysOK (keysG L))
    (hf : ChainFacts c.σ.mem c.σ.mem L lds bs) (hw : ChainOK pc (keysG L) bs)
    (hko : KeysOK (keysG (evalBlocks bs (SegEvalState.init L lds)).regs))
    (hra : KeysAvoidRa (evalBlocks bs (SegEvalState.init L lds)).regs)
    (hj : ∀ middle : Config, GoodState middle.σ → middle.tick < 2 →
      middle.σ.regs.get? Register.PC = some (evalBlocksPC pc (SegEvalState.init L lds) bs) →
      (∃ w, middle.σ.regs.get? Register.minstret = some w) →
      middle.σ.mem = writeLog c.σ.mem (evalBlocks bs (SegEvalState.init L lds)).log →
      GHolds middle.σ (evalBlocks bs (SegEvalState.init L lds)).regs →
      ∃ after, JalCallFacts callee link middle after) :
    ∃ after, SegCallFacts bs L lds callee link c after := by
  obtain ⟨vm, hvm⟩ := hmi
  obtain ⟨s1, i1, hs1, hi1, hg1, hm1, ho1, hp1, hmi1, hr1, hf1⟩ :=
    segEval_sound bs c.σ c.tick c.steps pc vm L lds hg hp hvm hl hk hf hw ht
  obtain ⟨after, J⟩ := hj ⟨s1, i1, c.steps + evalBlocksFuel bs⟩
    hg1 hi1 hp1 hmi1 hm1 hr1
  refine ⟨after, hs1.trans (Steps.single J.step), J.good, J.tick, J.pc, J.ra,
    J.minstret, gholds_of_jal J.nonra _ hko hra hr1, J.mem.trans hm1,
    J.frame.out.trans ho1, ?_⟩
  intro R hn hw hr
  have hjr : ∀ r ∈ Register.x1 :: noiseRegs, (r == R) = false := by
    intro r hh
    rcases List.mem_cons.mp hh with rfl | hh
    · exact hr
    · exact hn r hh
  exact (J.frame.frame R hjr).trans (hf1 R hn hw)

#print axioms jalCallFacts_of_obs
#print axioms bridgeOfSegFull
end Vsa.Sim
