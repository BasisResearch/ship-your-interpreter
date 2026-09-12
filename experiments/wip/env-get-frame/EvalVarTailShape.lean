import EnvGetCopyLog
import Vsa.Sim.EvalValueReturnTail

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr

namespace Vsa.Sim.EnvGetReflected

def valueTailLoads (b0 b1 b2 br b8 b18 b9 : List (BitVec 8)) : List (List (BitVec 8)) :=
  [b0, b1, b2, br, b8, b18, b9]

def valueTailRegs (sp dst ret r8 r9 r18 : BitVec 64) : GRegs :=
  [(1, ret), (2, sp + 1088#64), (8, r8), (9, r9), (18, r18), (10, dst)]

def valueTailKeep (R : Register) : Bool :=
  kept R || [Register.x19, .x20, .x21].contains R

/-- The final copy uses the three words loaded before any destination write. -/
def valueTailCopy (m : Mem) (dst : BitVec 64) (b0 b1 b2 : List (BitVec 8)) : Mem :=
  writeMap8 (writeMap8 (writeMap8 m
    (dst + sign_extend (m := 64) (0#12)).toNat (sdData_val (bytesVal .ld b0)))
    (dst + sign_extend (m := 64) (8#12)).toNat (sdData_val (bytesVal .ld b1)))
    (dst + sign_extend (m := 64) (16#12)).toNat (sdData_val (bytesVal .ld b2))

/-- The generated tail's log is exactly its three destination writes. -/
theorem value_tail_log (m : Mem) (sp dst : BitVec 64)
    (b0 b1 b2 br b8 b18 b9 : List (BitVec 8)) :
    writeLog m (evalBlocks evalValueReturnTailSeg (SegEvalState.init
      (evalValueReturnTailL sp dst) (valueTailLoads b0 b1 b2 br b8 b18 b9))).log =
      valueTailCopy m dst b0 b1 b2 := rfl

/-- Identify the actual copied memory with the shared total-copy contract. -/
theorem value_tail_copy (m : Mem) (dst : BitVec 64) (src : Nat)
    (b0 b1 b2 : List (BitVec 8)) (hdst : dst.toNat + 24 < 2^64)
    (h0 : bytesVal .ld b0 = bytesVal .ld (EvalChildArm.wordLds8 m src))
    (h1 : bytesVal .ld b1 = bytesVal .ld (EvalChildArm.wordLds8 m (src + 8)))
    (h2 : bytesVal .ld b2 = bytesVal .ld (EvalChildArm.wordLds8 m (src + 16))) :
    valueTailCopy m dst b0 b1 b2 = copy3Log m src dst.toNat := by
  unfold valueTailCopy
  rw [off_ed_00, off_ed_08 dst (by omega), off_ed_10 dst (by omega), h0, h1, h2]
  rfl

/-- Select the restored caller registers from the same symbolic tail result. -/
theorem value_tail_regs (sp dst ret r8 r9 r18 : BitVec 64)
    (b0 b1 b2 br b8 b18 b9 : List (BitVec 8))
    (hr : bytesVal .ld br = ret) (h8 : bytesVal .ld b8 = r8)
    (h18 : bytesVal .ld b18 = r18) (h9 : bytesVal .ld b9 = r9) :
    GProjects (evalBlocks evalValueReturnTailSeg (SegEvalState.init
      (evalValueReturnTailL sp dst) (valueTailLoads b0 b1 b2 br b8 b18 b9))).regs
      (valueTailRegs sp dst ret r8 r9 r18) := by
  change some (bytesVal .ld br) = some ret ∧
    some (sp + sign_extend (m := 64) (0x440#12)) = some (sp + 1088#64) ∧
    some (bytesVal .ld b8) = some r8 ∧ some (bytesVal .ld b9) = some r9 ∧
    some (bytesVal .ld b18) = some r18 ∧
    some (dst + sign_extend (m := 64) (0#12)) = some dst ∧ True
  simp only [hr, h8, h18, h9,
    show sign_extend (m := 64) (0x440#12) = 1088#64 from by decide,
    show sign_extend (m := 64) (0#12) = 0#64 from by decide, BitVec.add_zero, and_true]

theorem value_tail_pc (sp dst ret : BitVec 64)
    (b0 b1 b2 br b8 b18 b9 : List (BitVec 8))
    (hr : bytesVal .ld br = ret) (halign : ret.toNat % 4 = 0) :
    evalBlocksPC 0x80003448#64 (SegEvalState.init (evalValueReturnTailL sp dst)
      (valueTailLoads b0 b1 b2 br b8 b18 b9)) evalValueReturnTailSeg = ret := by
  change Sail.BitVec.update (bytesVal .ld br + sign_extend (m := 64) (0#12)) 0 0#1 = ret
  rw [hr, ret_tgt ret halign]

#print axioms value_tail_log
#print axioms value_tail_copy
#print axioms value_tail_regs
#print axioms value_tail_pc

end Vsa.Sim.EnvGetReflected
