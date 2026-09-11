import Vsa.Sim.DeriveMeta
import Vsa.Sim.EvalRecCommon

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.Logic Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim

#derive_destructurer SubEvalReturn fields
  good tick pc a0 ra sret spReg minstret out frame value store code
  slotRa slotS0 slotS1 slotS2 memFrame presence

/-- Recover the ordinary child exit at the same returned configuration. -/
theorem SubEvalReturn.toExit
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat} {nf nc : Nat}
    {st : Vsa.While.St} {v : Value} {sp ret dst childDst link r8 r9 r18 : BitVec 64}
    {mcall : Mem} {after : Config}
    (h : SubEvalReturn g N A SL phiF phiC nf nc st v
      sp ret dst childDst link r8 r9 r18 mcall after)
    (aligned : link.toNat % 4 = 0)
    (lowered : (sp - 1088#64).toNat = sp.toNat - 1088) :
    EvalExit g N A SL phiF phiC nf nc st v (sp - 1088#64) link childDst mcall after := by
  have p := SubEvalReturn.destruct g N A SL phiF phiC nf nc st v
    sp ret dst childDst link r8 r9 r18 mcall after h
  obtain ⟨valueC, valueExtends, value⟩ := p.value
  obtain ⟨storeF, storeC, frames, closures, store, _⟩ := p.store
  exact
    { good := p.good
      tick := p.tick
      pc := by rw [ret_tgt link aligned]; exact p.pc
      a0 := p.a0
      ra := p.ra
      spReg := p.spReg
      minstret := p.minstret
      result := ⟨valueC, valueExtends, value.repr⟩
      store := ⟨storeF, storeC, frames, closures, store⟩
      out := p.out
      frame := p.frame
      memFrame := by rw [lowered]; exact p.memFrame }

#print axioms SubEvalReturn.destruct
#print axioms SubEvalReturn.mk'
#print axioms SubEvalReturn.toExit

end Vsa.Sim
