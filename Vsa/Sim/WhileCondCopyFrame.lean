import Vsa.Sim.rows.ExecWhileRouteRows

/-!
# While-condition copy-prefix memory extension

The reflected condition-copy prefix performs three `sd` writes.  Each total
write preserves every populated address, so their composition extends the
entry memory.
-/

namespace Vsa.Sim

open LeanRV64DExecutable Sail Vsa
open Vsa.MemRepr
open Vsa.Sim.Rows

/-- The three-write condition-copy prefix preserves memory presence. -/
theorem execWhileCondCopy_memExtends
    (m : Mem) (esp aStmt aInterp aRet aEnv : BitVec 64) :
    MemExtends m
      (writeLog m (evalBlocks execWhileCondCopySeg
        (SegEvalState.init
          (execWhileCondCopyL esp aStmt aInterp aRet aEnv)
          (execWhileCondCopyLds m esp))).log) := by
  rw [execWhileCondCopy_writeLog_eq]
  exact
    ((memExtends_writeMap8 m _ _).trans
      (memExtends_writeMap8 _ _ _)).trans
      (memExtends_writeMap8 _ _ _)

/-- Every populated entry byte remains populated after the copy prefix. -/
theorem execWhileCondCopy_preserves_populated
    (m : Mem) (esp aStmt aInterp aRet aEnv : BitVec 64)
    {a : Nat} {b : BitVec 8} (hbyte : m[a]? = some b) :
    exists b',
      (writeLog m (evalBlocks execWhileCondCopySeg
        (SegEvalState.init
          (execWhileCondCopyL esp aStmt aInterp aRet aEnv)
          (execWhileCondCopyLds m esp))).log)[a]? = some b' :=
  execWhileCondCopy_memExtends m esp aStmt aInterp aRet aEnv a b hbyte

end Vsa.Sim

#print axioms Vsa.Sim.execWhileCondCopy_memExtends
#print axioms Vsa.Sim.execWhileCondCopy_preserves_populated
