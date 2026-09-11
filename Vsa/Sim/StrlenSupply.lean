import Vsa.Sim.StrlenCompleteRun
import Vsa.Sim.AllocRuns

namespace Vsa.Sim

open LeanRV64DExecutable Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc Vsa.Logic

/-- The full strlen contract retains caller registers and console output. -/
theorem strlen_full_spec_kept (p r : BitVec 64) (s : String) (m0 : Mem)
    (g : (R : Register) → Option (RegisterType R)) (out : Array String) :
    Triple
      (fun c => strlen_full_pre p r s m0 c ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R) ∧ c.σ.sailOutput = out)
      (fun c => strlen_post r s m0 c ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R) ∧ c.tick < 2 ∧
        c.σ.sailOutput = out) := by
  intro before pre
  obtain ⟨input, frame, output⟩ := pre
  obtain ⟨good, code, mem, pc, a0, ra, mi, tick, regions, string, retAlign⟩ := input
  obtain ⟨after, steps, returned⟩ := StrlenRun.run
    (p := p) (r := r) (s := s) (m0 := m0) (before := before)
    ⟨good, code, mem, pc, a0, ra, mi, tick, regions.readRegions, string, retAlign⟩
  have result := returned.state
  exact ⟨after, steps, ⟨result.good, result.pc, result.a0, result.ra, result.mem⟩,
    fun R hR => (returned.frame R hR).trans (frame R hR), result.tick,
    returned.output.trans output⟩

/-- Supply the allocator ledger's existing strlen field from the actual execution. -/
theorem strlenRun_closed : StrlenRun := by
  intro p r s m0 g out before pre
  obtain ⟨input, frame, output⟩ := pre
  obtain ⟨good, code, mem, pc, a0, ra, mi, tick, regions, _, string, retAlign⟩ := input
  exact strlen_full_spec_kept p r s m0 g out before
    ⟨⟨good, code, mem, pc, a0, ra, mi, tick, regions, string, retAlign⟩, frame, output⟩

#print axioms strlen_full_spec_kept
#print axioms strlenRun_closed

end Vsa.Sim
