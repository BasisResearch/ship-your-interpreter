import Vsa.Sim.MemcpyCopyBulkShape
import Vsa.Sim.SegEffect

namespace Vsa.Sim.MemcpyCopy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc Vsa.Logic

private def outRegs (dst src r : BitVec 64) (n i : Nat) (lds : List (List (BitVec 8))) : GRegs :=
  [(11, (src + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x048#12)),
   (13, (dst + BitVec.ofNat 64 (8*(n/8))) -
     ((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x048#12))),
   (14, (dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x048#12)),
   (16, bytesVal .ld (lds.getD 7 [])), (6, bytesVal .ld (lds.getD 6 [])),
   (28, bytesVal .ld (lds.getD 5 [])), (29, bytesVal .ld (lds.getD 4 [])),
   (30, bytesVal .ld (lds.getD 3 [])), (31, bytesVal .ld (lds.getD 2 [])),
   (5, bytesVal .ld (lds.getD 1 [])), (12, dst + BitVec.ofNat 64 (8*(n/8))),
   (15, 64#64), (17, dst + BitVec.ofNat 64 n), (10, dst), (1, r)]

private theorem regsExact (dst src r : BitVec 64) (n i : Nat) (m : Mem) (more : Bool) :
    (evalBlocks (bulkSeg more)
      (SegEvalState.init (bulkRegs dst src r n i) (bulkLoads m (src.toNat + i)))).regs =
      outRegs dst src r n i (bulkLoads m (src.toNat + i)) := by
  cases more <;> rfl

/-- Exact live-register projections of the reflected bulk iteration. -/
theorem bulkProjects (dst src r : BitVec 64) (n i : Nat) (m : Mem) (more : Bool) :
    GProjects (evalBlocks (bulkSeg more)
      (SegEvalState.init (bulkRegs dst src r n i) (bulkLoads m (src.toNat + i)))).regs
      (bulkRegs dst src r n (i+72)) := by
  rw [regsExact]
  change some ((src + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x048#12)) = _ ∧
    some ((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x048#12)) = _ ∧
    some (dst + BitVec.ofNat 64 (8*(n/8))) = _ ∧ some 64#64 = _ ∧
    some (dst + BitVec.ofNat 64 n) = _ ∧ some dst = _ ∧ some r = _ ∧ True
  simp only [bulkIncrement, and_self]

theorem bulkOK (more : Bool) : ChainOK 0x80006c60#64 [11,14,12,15,17,10,1] (bulkSeg more) := by
  cases more <;> decide

theorem bulkAvoids (more : Bool) : WrChainAvoids AbiPreserved (bulkSeg more) := by
  cases more <;> decide

#print axioms bulkProjects

end Vsa.Sim.MemcpyCopy
