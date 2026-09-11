import Vsa.Sim.InitialExecEntry
import Vsa.Sim.ExecRuntimeEntry
import Vsa.Sim.StoreInvariant
import Vsa.Sim.BindingArena

namespace Vsa.Sim
open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Machine Vsa.While Vsa.Alloc

variable {inp : BitVec 64} {stmts count aStmt : Nat}
  {before dispatch initialized after : Config} {s : Stmt} {ss : List Stmt}
  {N : NativeAddrs} {A : Arena} {phiF phiC : Addr → Nat}
  {D : RuntimeOwnership.InitialOwnershipData}

/-- The reached initial runtime supplies ownership, arrays, and arena placement.
The initial shared domain's word-read slack remains a separate obligation. -/
theorem OwnedInitialExecFacts.runtime
    (H : OwnedInitialExecFacts inp stmts count aStmt before dispatch initialized after
      s ss N A phiF phiC D)
    (geometry : SharedReadGeom D.shared LayoutInstance.stackSL) :
    RuntimeOwnership.StoreRuntimeData N A LayoutInstance.stackSL phiF phiC
      D.allocations D.exts D.shared initSt.store after.σ.mem := by
  have O := H.nullReturn.entered.initial
  exact
    { owned := H.heap.store
      repr := H.store
      arrays := H.arrays
      ledger := H.heap.ledger
      geometry := geometry
      arenaLo := by have := O.heapLower; omega
      arenaHi := by
        have := O.heapUpper
        change A.hi ≤ 0x87800000 at this
        omega
      arenaHtif := by
        have := O.heapLower
        change 0x8001ad00 + 8 ≤ A.lo
        omega
      arenaStack := Or.inl O.heapUpper
      parents := storeInvariant_initSt.parents }

/-- Assemble the first statement entry without dropping its owned runtime.
Hereditary ground, stack bounds, body bounds, and shared read geometry remain explicit. -/
theorem OwnedInitialExecFacts.execRuntimeEntry
    (H : OwnedInitialExecFacts inp stmts count aStmt before dispatch initialized after
      s ss N A phiF phiC D) {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts before stmts count inp N A phiF phiC aLeft)
    (hground : ExecGround after.σ.mem LayoutInstance.stackSL A 0x87fffc50#64
      0x87fffca8#64 (BitVec.ofNat 64 aStmt).toNat s)
    (hbudget : StackOK LayoutInstance.stackSL 0x87fffc50#64
      (s.stackNeed + maxCallDepth * perCallBudget + 1088))
    (hbodies : Stmt.bodiesBound perCallBudget s = true)
    (geometry : SharedReadGeom D.shared LayoutInstance.stackSL) :
    ExecRuntimeEntry after.σ.regs.get? N A LayoutInstance.stackSL phiF phiC
      D.allocations D.exts D.shared initSt 0 0 s 0x87fffc50#64 0x80004478#64
      inp (BitVec.ofNat 64 aStmt) (BitVec.ofNat 64 (phiF 0)) 0x87fffca8#64
      after.σ.mem after := by
  refine ⟨H.execEntry F hground hbudget hbodies, H.runtime geometry, ?_⟩
  have ha : (BitVec.ofNat 64 aStmt).toNat = aStmt :=
    Nat.mod_eq_of_lt (by
      have := H.access.tag.ram_hi
      change aStmt + 4 ≤ 0x100000000 at this
      omega)
  rw [ha]
  exact H.access.pointer.target

/-- The first recursive statement receives the initialized depth after all setup writes. -/
theorem OwnedInitialExecFacts.call_depth
    (H : OwnedInitialExecFacts inp stmts count aStmt before dispatch initialized after
      s ss N A phiF phiC D) {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts before stmts count inp N A phiF phiC aLeft) :
    read32 after.σ.mem (inp.toNat + 8) = some 0 :=
  H.preservation.toReadyPrefixFacts.call_depth F

/-- The first recursive statement retains the concrete placement needed by parameter binding. -/
theorem OwnedInitialExecFacts.bindingArena
    (H : OwnedInitialExecFacts inp stmts count aStmt before dispatch initialized after
      s ss N A phiF phiC D) : BindingArena A LayoutInstance.stackSL :=
  H.nullReturn.entered.initial.bindingArena

#print axioms OwnedInitialExecFacts.runtime
#print axioms OwnedInitialExecFacts.execRuntimeEntry
#print axioms OwnedInitialExecFacts.call_depth
#print axioms OwnedInitialExecFacts.bindingArena

end Vsa.Sim
