import Vsa.Sim.ExecSimCommon
import Vsa.Sim.AstReadGeometryCore

namespace Vsa.Sim

open LeanRV64DExecutable Vsa.Machine Vsa.RuntimeRepr Vsa.MemRepr Vsa.Alloc

/-- Block header ownership and protected stack space retained across child calls. -/
structure ExecSeqBlockResources (A : Arena) (SL : StackLayout)
    (shared : Nat → Prop) (sp aRet block : BitVec 64)
    (regs : (R : Register) → Option (RegisterType R)) : Prop where
  baseCovered : Covers shared (block.toNat + 8) 8
  countCovered : Covers shared (block.toNat + 16) 4
  savedOffArena : sp.toNat + 16 ≤ A.lo ∨ A.hi ≤ sp.toNat + 8
  stackHi : sp.toNat + 16 ≤ SL.hi
  savedOffRet : sp.toNat + 16 ≤ aRet.toNat ∨ aRet.toNat + 24 ≤ sp.toNat + 8
  spill20 : ∃ v, regs .x20 = some v
  spill21 : ∃ v, regs .x21 = some v

/-- Bind header resources to the block held by the actual cursor register. -/
inductive ExecSeqBlockResources.At (A : Arena) (SL : StackLayout)
    (shared : Nat → Prop) (sp aRet : BitVec 64)
    (regs : (R : Register) → Option (RegisterType R)) : Prop where
  | intro (block : BitVec 64) (blockReg : regs .x8 = some block)
      (resources : ExecSeqBlockResources A SL shared sp aRet block regs) :
      ExecSeqBlockResources.At A SL shared sp aRet regs

/-- The owned block header supplies the two immutable loop words. -/
theorem ExecSeqBlockResources.of_header
    {A : Arena} {SL : StackLayout} {shared : Nat → Prop} {sp aRet block : BitVec 64}
    {regs : (R : Register) → Option (RegisterType R)} {m : Mem} {ss : List Vsa.While.Stmt}
    (header : StmtReprWithin m shared block.toNat (.block ss))
    (savedOffArena : sp.toNat + 16 ≤ A.lo ∨ A.hi ≤ sp.toNat + 8) (stackHi : sp.toNat + 16 ≤ SL.hi)
    (savedOffRet : sp.toNat + 16 ≤ aRet.toNat ∨ aRet.toNat + 24 ≤ sp.toNat + 8)
    (spill20 : ∃ v, regs .x20 = some v) (spill21 : ∃ v, regs .x21 = some v) :
    ExecSeqBlockResources A SL shared sp aRet block regs :=
  { baseCovered := header.fieldCovers (.word64 8) (by simp [stmtReadFields])
    countCovered := header.fieldCovers (.word32 16) (by simp [stmtReadFields])
    savedOffArena := savedOffArena, stackHi := stackHi, savedOffRet := savedOffRet
    spill20 := spill20, spill21 := spill21 }

#print axioms ExecSeqBlockResources.of_header

end Vsa.Sim
