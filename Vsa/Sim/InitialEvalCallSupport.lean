import Vsa.Sim.EvalCallImage
import Vsa.Sim.InitialExecEntry

namespace Vsa.Sim
open LeanRV64DExecutable Vsa.MemRepr Vsa.RuntimeRepr Vsa.Machine Vsa.While Vsa.Alloc

/-- The allocated root frame makes the initial arena nonempty. Existing image
protection then excludes its entire interval from text and rodata. -/
theorem LayoutInstance.InterpRunPhysicalFacts.arena_image
    {before : Config} {stmts count aLeft : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {phiF phiC : Addr → Nat}
    (F : LayoutInstance.InterpRunPhysicalFacts before stmts count inp N A phiF phiC aLeft) :
    A.hi ≤ 0x80000000 ∨ 0x8001acf0 ≤ A.lo := by
  have ha := (F.store.frames_arena 0 (by decide)).1
  change A.lo ≤ phiF 0 ∧ phiF 0 + 32 ≤ A.hi at ha
  have hpos : A.lo < A.hi := by omega
  have hp : ∀ k, 0x80000000 ≤ k → k < 0x8001acf0 → ProtectedInitialByte k := by
    intro k hlo hhi
    change ∃ r ∈ exitProtectedRegions, r.1 ≤ k ∧ k < r.1 + r.2
    by_cases ht : k < 0x80018be0
    · exact ⟨(0x80000000, 0x18be0), by simp [exitProtectedRegions, exitFixedImageRegions],
        hlo, by omega⟩
    · exact ⟨(0x80018be0, 0x2110), by simp [exitProtectedRegions, exitFixedImageRegions],
        by omega, by omega⟩
  by_cases hleft : A.hi ≤ 0x80000000
  · exact Or.inl hleft
  · right
    apply Classical.byContradiction
    intro hright
    exact F.arena_protected (max 0x80000000 A.lo)
      (hp _ (by omega) (by omega)) ⟨by omega, by omega⟩

/-- The existing physical image supplies eval-call support at any stack cut. -/
theorem LayoutInstance.InterpRunPhysicalFacts.evalCallSupport
    {before : Config} {stmts count aLeft : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {phiF phiC : Addr → Nat}
    (F : LayoutInstance.InterpRunPhysicalFacts before stmts count inp N A phiF phiC aLeft)
    (sp : BitVec 64) : EvalCallSupport before.σ.mem LayoutInstance.stackSL A sp :=
  evalCallSupport_of_fixedImage sp F.text_image F.rodata_image (by decide) F.arena_image

/-- Retain initial eval-call support through the actual first statement call. -/
theorem OwnedInitialExecFacts.evalCallSupport
    {inp : BitVec 64} {stmts count aStmt aLeft : Nat}
    {before dispatch initialized after : Config} {s : Stmt} {ss : List Stmt}
    {N : NativeAddrs} {A : Arena} {phiF phiC : Addr → Nat}
    {D : RuntimeOwnership.InitialOwnershipData}
    (H : OwnedInitialExecFacts inp stmts count aStmt before dispatch initialized after
      s ss N A phiF phiC D)
    (F : LayoutInstance.InterpRunReadyFacts before stmts count inp N A phiF phiC aLeft) :
    EvalCallSupport after.σ.mem LayoutInstance.stackSL A 0x87fffc50#64 := by
  have hi := F.interp_local
  subst inp
  exact evalCallSupport_of_fixedImage _ (H.preservation.text_image F.text_image)
    (H.preservation.rodata_image F.rodata_image) (by decide)
    F.toInterpRunPhysicalFacts.arena_image

#print axioms LayoutInstance.InterpRunPhysicalFacts.arena_image
#print axioms LayoutInstance.InterpRunPhysicalFacts.evalCallSupport
#print axioms OwnedInitialExecFacts.evalCallSupport
end Vsa.Sim
