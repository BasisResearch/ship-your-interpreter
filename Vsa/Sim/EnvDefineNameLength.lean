import Vsa.Sim.StrlenSupply
import Vsa.Sim.rows.EnvDefineCallRuns
import Vsa.Sim.Code.FixedImage_Env_define

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.Alloc
open RuntimeOwnership Code

/-- The actual strlen call and size prefix reach malloc for the represented shared name. -/
theorem envDefineNameMallocParked_of {namePtr : BitVec 64} {name : String}
    {shared : Nat → Prop} {SL : StackLayout} {before : Config}
    (good : GoodState before.σ)
    (pc : before.σ.regs.get? Register.PC = some 0x80002b1c#64)
    (nameReg : before.σ.regs.get? Register.x18 = some namePtr)
    (text : FixedTextLoaded before.σ.mem) (tick : before.tick < 2)
    (geometry : SharedReadGeom shared SL)
    (owned : SharedCString before.σ.mem shared namePtr.toNat name) :
    ∃ after, EnvDefineMallocParked name.length before after := by
  obtain ⟨called, call⟩ := envDefineStrlenParked_of namePtr before good pc nameReg
    text.Env_defineLoaded tick
  have regions := geometry.strlenRegions owned
  have input : StrlenRun.Input namePtr 0x80002b24#64 name before.σ.mem called :=
    { good := call.good, loaded := by rw [call.mem]; exact text.StrlenLoaded
      mem := call.mem, pc := call.pc, a0 := call.a0, ra := call.ra
      minstret := call.minstret, tick := call.tick, regions := regions
      string := owned.repr, retAlign := by decide }
  obtain ⟨returned, lengthSteps, length⟩ := StrlenRun.run input
  obtain ⟨after, malloc⟩ := envDefineMallocParked_of name.length returned
    (by have := regions.nowrap; omega) length.state.good length.state.pc length.state.a0
    (by rw [length.state.mem]; exact text.Env_defineLoaded) length.state.tick
  exact ⟨after,
    { malloc with
      steps := call.steps.trans (lengthSteps.trans malloc.steps)
      mem := malloc.mem.trans length.state.mem
      out := malloc.out.trans (length.output.trans call.out)
      abi := fun R hR => (malloc.abi R hR).trans
        ((length.frame R (abiButS0_abi hR)).trans (call.abi R (abiButS0_abi hR))) }⟩

#print axioms envDefineNameMallocParked_of

end Vsa.Sim
