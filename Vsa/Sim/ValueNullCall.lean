import Vsa.Sim.BridgeSegFull
import Vsa.Sim.EvalNullSim
import Vsa.Sim.StepFrameOut

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

/-- The null helper's frame excludes every machine noise register. -/
theorem nullFrame_noise {R : Register} (h : NotWrittenV R) :
    ∀ r ∈ noiseRegs, (r == R) = false := by
  obtain ⟨_, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := h
  intro r hr
  simp only [noiseRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-- A null initializer retains the actual call's memory and complete register frame. -/
structure ValueNullCallPost (bs : List BBlock) (buf ret : BitVec 64)
    (N : NativeAddrs) (phiC : Vsa.While.Addr → Nat) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some ret
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  value : ValueRepr after.σ.mem N phiC buf.toNat .null
  outside : ∀ k, ¬ (buf.toNat ≤ k ∧ k < buf.toNat + 24) → before.σ.mem[k]? = after.σ.mem[k]?
  output : after.σ.sailOutput = before.σ.sailOutput
  presence : MemExtends before.σ.mem after.σ.mem
  frame : ∀ R, NotWrittenV R →
    (∀ n ∈ wrChain bs, (gprReg n == R) = false) → (Register.x1 == R) = false →
    after.σ.regs.get? R = before.σ.regs.get? R

/-- Finish a reflected null-helper call without repeating its prefix execution. -/
theorem SegCallFacts.valueNull
    {bs : List BBlock} {L : GRegs} {lds : List (List (BitVec 8))}
    {ret buf : BitVec 64} {before called : Config}
    (h : SegCallFacts bs L lds 0x800027ec#64 ret before called)
    (noWrites : (evalBlocks bs (SegEvalState.init L lds)).log = [])
    (argument : lookupG 10 (evalBlocks bs (SegEvalState.init L lds)).regs = some buf)
    (loaded : Code.Value_nullLoaded before.σ.mem) (region : NullRegion buf)
    (retClean : BitVec.update (ret + sign_extend (m := 64) (0#12)) 0 0#1 = ret)
    (retAlign : ret.toNat % 4 = 0) (N : NativeAddrs) (phiC : Vsa.While.Addr → Nat) :
    ∃ after, Steps before after ∧ ValueNullCallPost bs buf ret N phiC before after := by
  have memory : called.σ.mem = before.σ.mem := by rw [h.mem, noWrites]; rfl
  obtain ⟨after, steps, good, pc, _, _, minstret, tick, value, output, outside, frame, presence⟩ :=
    value_null_spec_full called.σ.regs.get? buf ret N phiC called.σ.mem called.σ.sailOutput called
      ⟨h.good, memory.symm ▸ loaded, rfl, h.pc, gholds_lookup _ h.registers argument,
        h.ra, h.minstret, h.tick, region, by rw [retClean]; exact retAlign,
        rfl, fun _ _ => rfl⟩
  refine ⟨after, h.run.trans steps,
    { good := good, tick := tick, pc := by rw [retClean] at pc; exact pc
      minstret := minstret, value := value
      outside := ?_, output := output.trans h.output
      presence := memory ▸ presence
      frame := fun R hR hw hra => (frame R hR).trans (h.frame R (nullFrame_noise hR) hw hra) }⟩
  intro k hk
  exact (congrArg (fun m : Mem => m[k]?) memory).symm.trans (outside k hk)

#print axioms nullFrame_noise
#print axioms SegCallFacts.valueNull

end Vsa.Sim
