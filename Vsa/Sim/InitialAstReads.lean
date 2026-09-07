import Vsa.MemReprReadArrays
import Vsa.Sim.InitialLoopHead
import Vsa.Sim.AstReadGeometry

namespace Vsa.Sim
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Machine Vsa.While Vsa.Alloc

/-- One program cell and exact read geometry for its selected statement. -/
structure StmtReadAccess (m : Mem) (SL : StackLayout) (shared : Nat → Prop)
    (slot aStmt : Nat) (s : Stmt) : Prop where
  pointer : PointerReadWithin m shared (StmtReprWithin m shared) slot aStmt s
  slotGeometry : AstReadGeometry SL slot 8
  fields : ∀ f ∈ stmtReadFields s, AstReadGeometry SL (aStmt + f.offset) f.width

/-- Dispatch consumes only the represented four-byte statement tag. -/
theorem StmtReadAccess.tag {m : Mem} {SL : StackLayout} {shared : Nat → Prop}
    {slot aStmt : Nat} {s : Stmt} (h : StmtReadAccess m SL shared slot aStmt s) :
    AstReadGeometry SL aStmt 4 := by
  simpa [ReadField.word32] using h.fields (.word32 0) (by simp [stmtReadFields])

/-- The reached runtime supplies every indexed statement read from its own ownership. -/
theorem ReadyRuntimeFacts.stmtReadAccess
    {c : Config} {stmts count : Nat} {p : Program} {N : NativeAddrs} {A : Arena}
    {phiF phiC : Addr → Nat} {D : RuntimeOwnership.InitialOwnershipData}
    (F : ReadyRuntimeFacts c stmts count p N A phiF phiC D)
    (i : Nat) (hi : i < p.length) :
    ∃ aStmt, StmtReadAccess c.σ.mem LayoutInstance.stackSL D.shared
      (stmts + 8 * i) aStmt p[i] := by
  obtain ⟨aStmt, R⟩ := F.program.1.pointers.get i hi
  exact ⟨aStmt, R, .of_covered F.heap.immutable R.covered (by decide),
    fun f hf => .stmt_field F.heap.immutable R.target f hf⟩

/-- The first statement access is obtained at the actual nonempty loop head. -/
theorem OwnedLoopHeadFacts.firstRead
    {inp : BitVec 64} {stmts count : Nat} {before after : Config}
    {s : Stmt} {ss : List Stmt} {N : NativeAddrs} {A : Arena}
    {phiF phiC : Addr → Nat} {D : RuntimeOwnership.InitialOwnershipData}
    (H : OwnedLoopHeadFacts inp stmts count before after (s :: ss) N A phiF phiC D) :
    ∃ aStmt, StmtReadAccess after.σ.mem LayoutInstance.stackSL D.shared stmts aStmt s := by
  simpa using H.toReadyRuntimeFacts.stmtReadAccess 0 (by simp)

#print axioms StmtReadAccess.tag
#print axioms ReadyRuntimeFacts.stmtReadAccess
#print axioms OwnedLoopHeadFacts.firstRead
end Vsa.Sim
