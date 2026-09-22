import Vsa.Sim.BridgeSegFull
import Vsa.Sim.rows.InitialValueNullCall
import Vsa.Sim.InitialNullSites
import Vsa.Sim.InitialDispatch
import Vsa.Sim.EvalNullSim
import Vsa.Sim.StepFrameOut
import Vsa.Sim.ValueNullCall

namespace Vsa.Sim
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Machine Vsa.While Vsa.Alloc

/-- Actual staging, call, and return with the result-slot write frame. -/
structure InitialNullFacts (before after : Config) (N : NativeAddrs)
    (phiC : Addr → Nat) : Prop where
  run : Steps before after
  good : GoodState after.σ
  pc : after.σ.regs.get? Register.PC = some (0x80004460#64 : BitVec 64)
  tick : after.tick < 2
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  value : ValueRepr after.σ.mem N phiC 0x87fffca8 .null
  outside : ∀ k, ¬ (0x87fffca8 ≤ k ∧ k < 0x87fffcc0) →
    before.σ.mem[k]? = after.σ.mem[k]?
  output : after.σ.sailOutput = before.σ.sailOutput
  mem_extends : MemExtends before.σ.mem after.σ.mem
  frame : ∀ R, NotWrittenV R → (Register.x1 == R) = false →
    (Register.x10 == R) = false → after.σ.regs.get? R = before.σ.regs.get? R

/-- Result-slot initialization at an interpreter loop's current stack pointer. -/
structure InterpNullFacts (sp : BitVec 64) (before after : Config) (N : NativeAddrs)
    (phiC : Addr → Nat) : Prop where
  run : Steps before after
  good : GoodState after.σ
  pc : after.σ.regs.get? Register.PC = some (0x80004460#64 : BitVec 64)
  tick : after.tick < 2
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  value : ValueRepr after.σ.mem N phiC (sp + 88#64).toNat .null
  outside : ∀ k, ¬ ((sp + 88#64).toNat ≤ k ∧ k < (sp + 88#64).toNat + 24) →
    before.σ.mem[k]? = after.σ.mem[k]?
  output : after.σ.sailOutput = before.σ.sailOutput
  mem_extends : MemExtends before.σ.mem after.σ.mem
  frame : ∀ R, NotWrittenV R → (Register.x1 == R) = false →
    (Register.x10 == R) = false → after.σ.regs.get? R = before.σ.regs.get? R

/-- Execute the loop's result-slot initialization using the existing call span. -/
theorem interpValueNull_run (c : Config) (sp : BitVec 64) (N : NativeAddrs)
    (phiC : Addr → Nat)
    (hG : GoodState c.σ)
    (hpc : c.σ.regs.get? Register.PC = some (0x80004458#64 : BitVec 64))
    (hsp : c.σ.regs.get? Register.x2 = some sp)
    (hmi : ∃ w, c.σ.regs.get? Register.minstret = some w)
    (hi : c.tick < 2) (hcode : Code.Interp_runLoaded c.σ.mem)
    (hnull : Code.Value_nullLoaded c.σ.mem) (region : NullRegion (sp + 88#64)) :
    ∃ after, InterpNullFacts sp c after N phiC := by
  have hfacts : ChainFacts c.σ.mem c.σ.mem
      (initialValueNullCallL sp) [] initialValueNullCallSeg := by
    chain_facts hcode with "Vsa.Sim.Code.interp_run_at_"
  obtain ⟨c2, C⟩ := bridgeOfSegFull initialValueNullCallSeg
    (initialValueNullCallL sp) [] 0x80004458#64 0x800027ec#64 0x80004460#64
    c hG hpc hmi hi ⟨hsp, trivial⟩ (by change KeysOK [2]; decide) hfacts
    (by change ChainOK 0x80004458#64 [2] initialValueNullCallSeg; decide)
    (by change KeysOK [10, 2]; decide)
    (by change ∀ n ∈ ([10, 2] : List Nat), n ≠ 1; decide)
    (by
      intro middle hg ht hp hmi hm _
      have hm' : middle.σ.mem = c.σ.mem := hm.trans (by rfl)
      obtain ⟨vm, hvm⟩ := hmi
      obtain ⟨s2, i2, hs2, hi2, hg2, hm2, ho2⟩ :=
        site_8000445c_initialNull middle.σ middle.tick middle.steps 0x8000445c#64 vm
          hg hp hvm (hm'.symm ▸ hcode) rfl ht
      exact ⟨⟨s2, i2, middle.steps + 1⟩, jalCallFacts_of_obs hs2 hi2 hg2 hm2 ho2 (by decide)⟩)
  obtain ⟨after, steps, post⟩ := C.valueNull rfl rfl hnull region (by decide) (by decide) N phiC
  refine ⟨after, steps, post.good, post.pc, post.tick, post.minstret, post.value,
    post.outside, post.output, post.presence, ?_⟩
  intro R hR hra harg
  apply post.frame R hR ?_ hra
  change ∀ n ∈ ([10] : List Nat), (gprReg n == R) = false
  simpa only [List.mem_singleton, forall_eq, gprReg] using harg

/-- Execute the initial result-slot initialization from its actual code and registers. -/
theorem initialValueNull_run (c : Config) (N : NativeAddrs) (phiC : Addr → Nat)
    (hG : GoodState c.σ)
    (hpc : c.σ.regs.get? Register.PC = some (0x80004458#64 : BitVec 64))
    (hsp : c.σ.regs.get? Register.x2 = some (0x87fffc50#64 : BitVec 64))
    (hmi : ∃ w, c.σ.regs.get? Register.minstret = some w)
    (hi : c.tick < 2) (hcode : Code.Interp_runLoaded c.σ.mem)
    (hnull : Code.Value_nullLoaded c.σ.mem) :
    ∃ after, InitialNullFacts c after N phiC := by
  obtain ⟨after, h⟩ := interpValueNull_run c 0x87fffc50#64 N phiC hG hpc hsp hmi hi
    hcode hnull ⟨by decide, by decide, by decide, by decide, by decide⟩
  exact ⟨after, h.run, h.good, h.pc, h.tick, h.minstret, h.value, h.outside,
    h.output, h.mem_extends, h.frame⟩

#print axioms nullFrame_noise
#print axioms interpValueNull_run
#print axioms initialValueNull_run
end Vsa.Sim
