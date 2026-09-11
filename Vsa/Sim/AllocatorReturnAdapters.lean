import Vsa.Sim.AllocatorIH
import Vsa.Sim.RuntimeReturnAdapters

open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine

namespace Vsa.Sim

/-- Reuse the coherent exit adapter at the allocator producer's selected maps. -/
theorem ExecExitD.withAllocatorRepr
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC resultF resultC : Addr → Nat} {nf nc credits : Nat} {shared : Nat → Prop}
    {st : Vsa.While.St} {status : Status} {sp ret aRet : BitVec 64} {m0 : Mem} {c : Config}
    (h : ExecExitD g N A SL phiF phiC nf nc st status sp ret aRet m0 c)
    (hr : ReturnRepr N A phiF phiC resultF resultC nf nc st.store
      (statusResults aRet.toNat status)
      (AllocatorResult M N shared credits st.store (statusResults aRet.toNat status) m0)
      (fun k => SL.lo ≤ k ∧ k < SL.hi) c.σ.mem)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (gp : c.σ.regs.get? Register.x3 = some gpv) :
    ExecAllocatorReturn g N M phiF phiC nf nc shared credits st status sp ret aRet m0 c :=
  { exit := (h.withRuntimeRepr
      { frames := hr.frames, closures := hr.closures, values := hr.values
        owned := hr.owned.runtime L, survives := hr.survives }).exit
    selected := ⟨resultF, resultC, hr⟩
    gp := gp }

#print axioms ExecExitD.withAllocatorRepr

end Vsa.Sim
