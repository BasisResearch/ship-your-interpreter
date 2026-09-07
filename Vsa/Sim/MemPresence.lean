import Vsa.Sim.BlockMem
import Vsa.Sim.EvalSimCommon
import Vsa.Sim.JmpSpec

namespace Vsa.Sim
open Vsa.MemRepr

/-- Inserting a byte preserves presence at every previously populated address. -/
theorem memExtends_insert (m : Mem) (a : Nat) (b : BitVec 8) :
    MemExtends m (m.insert a b) := by
  intro k v hv
  rw [Std.ExtHashMap.getElem?_insert]
  split
  · exact ⟨b, rfl⟩
  · exact ⟨v, hv⟩

/-- Every reflected write width preserves the memory domain. -/
theorem memExtends_applyW (m : Mem) (e : WEntry) : MemExtends m (applyW m e) := by
  obtain ⟨a, w, d⟩ := e
  unfold applyW
  split
  · exact memExtends_insert _ _ _
  · exact (memExtends_insert _ _ _).trans (memExtends_insert _ _ _)
  · exact memExtends_writeMap4 _ _ _
  · exact memExtends_writeMap8 _ _ _
  · exact .refl m

/-- A complete reflected write log preserves all initially populated addresses. -/
theorem memExtends_writeLog (m : Mem) (log : List WEntry) :
    MemExtends m (writeLog m log) := by
  induction log generalizing m with
  | nil => exact .refl m
  | cons e es ih =>
    exact (memExtends_applyW m e).trans (ih (applyW m e))

/-- Extend an existing presence proof through one word write. -/
theorem MemExtends.writeMap8 {m0 m : Mem} (h : MemExtends m0 m)
    (a : Nat) (d : BitVec (8 * 8)) : MemExtends m0 (writeMap8 m a d) :=
  h.trans (memExtends_writeMap8 m a d)

/-- The exact setjmp save buffer retains every previously populated address. -/
theorem memExtends_setjmpBuf (m : Mem) (jb : BitVec 64)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64) :
    MemExtends m (setjmpBuf m jb ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v
      s10v s11v spv) := by
  unfold setjmpBuf
  repeat' apply MemExtends.writeMap8
  exact .refl m

#print axioms memExtends_insert
#print axioms memExtends_applyW
#print axioms memExtends_writeLog
#print axioms MemExtends.writeMap8
#print axioms memExtends_setjmpBuf
end Vsa.Sim
