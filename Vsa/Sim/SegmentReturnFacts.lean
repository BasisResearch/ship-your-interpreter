import Vsa.Sim.DeriveCaseRow

open LeanRV64DExecutable Vsa.Machine Vsa.MemRepr

namespace Vsa.Sim

/-- The common segment-return facts at one exact memory and register image. -/
structure SegmentReturnFacts (pc : BitVec 64) (mem : Mem) (regs : GRegs)
    (c : Config) : Prop where
  good : GoodState c.σ
  memory : c.σ.mem = mem
  programCounter : c.σ.regs.get? Register.PC = some pc
  registers : GHolds c.σ regs
  tick : c.tick < 2

/-- Destructure the existing segment-return conjunction once. -/
theorem SegmentReturnFacts.of_conjunction
    {pc : BitVec 64} {mem : Mem} {regs : GRegs} {c : Config}
    (h : GoodState c.σ ∧ c.σ.mem = mem ∧
      c.σ.regs.get? Register.PC = some pc ∧ GHolds c.σ regs ∧ c.tick < 2) :
    SegmentReturnFacts pc mem regs c := by
  obtain ⟨good, memory, programCounter, registers, tick⟩ := h
  exact ⟨good, memory, programCounter, registers, tick⟩

#print axioms SegmentReturnFacts.of_conjunction

end Vsa.Sim
