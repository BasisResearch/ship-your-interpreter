import Vsa.Sim.BridgeSegFull
import Vsa.Sim.rows.InitialValueNullCall
import Vsa.Sim.InitialNullSites
import Vsa.Sim.InitialDispatch
import Vsa.Sim.EvalNullSim
import Vsa.Sim.StepFrameOut

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

/-- The null helper's frame excludes every machine noise register. -/
theorem nullFrame_noise {R : Register} (h : NotWrittenV R) :
    ∀ r ∈ noiseRegs, (r == R) = false := by
  obtain ⟨_, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := h
  intro r hr
  simp only [noiseRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-- Execute the initial result-slot initialization from its actual code and registers. -/
theorem initialValueNull_run (c : Config) (N : NativeAddrs) (phiC : Addr → Nat)
    (hG : GoodState c.σ)
    (hpc : c.σ.regs.get? Register.PC = some (0x80004458#64 : BitVec 64))
    (hsp : c.σ.regs.get? Register.x2 = some (0x87fffc50#64 : BitVec 64))
    (hmi : ∃ w, c.σ.regs.get? Register.minstret = some w)
    (hi : c.tick < 2) (hcode : Code.Interp_runLoaded c.σ.mem)
    (hnull : Code.Value_nullLoaded c.σ.mem) :
    ∃ after, InitialNullFacts c after N phiC := by
  have hfacts : ChainFacts c.σ.mem c.σ.mem
      (initialValueNullCallL 0x87fffc50#64) [] initialValueNullCallSeg := by
    chain_facts hcode with "Vsa.Sim.Code.interp_run_at_"
  obtain ⟨c2, C⟩ := bridgeOfSegFull initialValueNullCallSeg
    (initialValueNullCallL 0x87fffc50#64) [] 0x80004458#64 0x800027ec#64 0x80004460#64
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
  have hm2 : c2.σ.mem = c.σ.mem := C.mem.trans (by rfl)
  have ha2 : c2.σ.regs.get? Register.x10 = some (0x87fffca8#64 : BitVec 64) :=
    gholds_lookup _ C.registers (show lookupG 10 _ = some (0x87fffca8#64 : BitVec 64) from rfl)
  obtain ⟨after, hs3, hG3, hp3, _ha3, _hra3, hmi3, hi3, hv3, ho3, hm3, hf3, he3⟩ :=
    value_null_spec_full (fun R => c2.σ.regs.get? R) 0x87fffca8#64 0x80004460#64
      N phiC c2.σ.mem c2.σ.sailOutput c2
      ⟨C.good, hm2.symm ▸ hnull, rfl, C.pc, ha2, C.ra, C.minstret, C.tick,
        ⟨by decide, by decide, by decide, by decide, by decide⟩,
        by decide, rfl, fun _ _ => rfl⟩
  refine ⟨after, ⟨C.run.trans hs3, hG3, hp3, hi3, hmi3,
    hv3, ?_, ho3.trans C.output, hm2 ▸ he3, ?_⟩⟩
  · intro k hk
    exact (congrArg (fun m : Mem => m[k]?) hm2).symm.trans (hm3 k hk)
  · intro R hR hra harg
    have hb : ∀ n ∈ wrChain initialValueNullCallSeg, (gprReg n == R) = false := by
      change ∀ n ∈ ([10] : List Nat), (gprReg n == R) = false
      simpa only [List.mem_singleton, forall_eq] using harg
    exact (hf3 R hR).trans (C.frame R (nullFrame_noise hR) hb hra)

#print axioms nullFrame_noise
#print axioms initialValueNull_run
end Vsa.Sim
