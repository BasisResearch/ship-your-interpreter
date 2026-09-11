import Vsa.Sim.ExecSimCommon

namespace Vsa.Sim

open LeanRV64DExecutable Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

/-- Interpreter placement and saved registers supplied by loop setup and
preserved by each actual statement call and normal back edge. -/
structure ExecSeqInterpResources (A : Arena) (SL : StackLayout)
    (sp aRet interp : BitVec 64)
    (regs : (R : Register) → Option (RegisterType R)) : Prop where
  arenaBelow : A.hi ≤ SL.lo
  interpAbove : sp.toNat ≤ interp.toNat
  interpHi : interp.toNat + 8 ≤ 0x100000000
  interpOffRet : interp.toNat + 8 ≤ aRet.toNat ∨ aRet.toNat + 24 ≤ interp.toNat
  breakReg : regs .x19 = some 3#64
  continueReg : regs .x20 = some 1#64
  spill21 : ∃ v, regs .x21 = some v

/-- The resources belong to the interpreter pointer saved in this memory. -/
inductive ExecSeqInterpResources.At (A : Arena) (SL : StackLayout)
    (sp aRet : BitVec 64) (m : Mem)
    (regs : (R : Register) → Option (RegisterType R)) : Prop where
  | intro (interp : BitVec 64) (saved : read64 m sp.toNat = some interp.toNat)
      (resources : ExecSeqInterpResources A SL sp aRet interp regs) :
      ExecSeqInterpResources.At A SL sp aRet m regs

end Vsa.Sim
