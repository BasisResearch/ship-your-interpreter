import Vsa.Sim.RuntimeOwnershipInitial
import Vsa.Sim.RuntimeOwnershipBinding
import Vsa.Sim.SharedReadGeometry

namespace Vsa.Sim

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The initial heap placement, retained while names enter the shared domain. -/
structure BindingArena (A : Arena) (SL : StackLayout) : Prop where
  lower : 0x8001c170 ≤ A.lo
  upper : A.hi ≤ SL.lo

/-- The loaded run's existing ownership supplies the binding arena bounds. -/
theorem RuntimeOwnership.InitialOwned.bindingArena
    {m : Mem} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {stmts count : Nat} {D : InitialOwnershipData}
    (h : InitialOwned m A SL phiF phiC stmts count D) : BindingArena A SL :=
  ⟨h.heapLower, h.heapUpper⟩

/-- An arena byte avoids the ELF's writable data and the full runtime stack. -/
theorem BindingArena.outsideWrites {A : Arena} {SL : StackLayout}
    (h : BindingArena A SL) {p n k : Nat} (arena : A.contains p n)
    (within : ExtentByte (p, n) k) : ¬ InitialWriteByte SL k := by
  obtain ⟨lo, hi⟩ := arena
  obtain ⟨lower, upper⟩ := within
  have := h.lower
  have := h.upper
  intro written
  rcases written with written | written <;> omega

/-- Stack headroom leaves every heap byte enough RAM space for shared word reads. -/
theorem BindingArena.readGeometry {A : Arena} {SL : StackLayout} {sp : BitVec 64}
    (h : BindingArena A SL) (stack : StackOK SL sp 1088) (ramHi : SL.hi ≤ 0x100000000) :
    SharedReadGeom (fun k => A.lo ≤ k ∧ k < A.hi) SL := by
  have := h.lower
  have := h.upper
  have := stack.1
  have := stack.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk; constructor <;> omega
  · intro k hk; right; omega
  · intro k hk; right; unfold tohostAddr; omega
  · intro k hk; left; omega

/-- The existing shared domain extends to the exact fresh name allocation. -/
theorem BindingArena.extend {A : Arena} {SL : StackLayout} {sp : BitVec 64}
    {shared : Nat → Prop} {p n : Nat}
    (h : BindingArena A SL) (stack : StackOK SL sp 1088) (ramHi : SL.hi ≤ 0x100000000)
    (old : SharedReadGeom shared SL) (arena : A.contains p n) :
    SharedReadGeom (BindingShared shared p n) SL := by
  have fresh := h.readGeometry stack ramHi
  have contained : ∀ k, ExtentByte (p, n) k → A.lo ≤ k ∧ k < A.hi := by
    intro k hk
    obtain ⟨lo, hi⟩ := arena
    obtain ⟨lower, upper⟩ := hk
    exact ⟨by omega, by omega⟩
  exact
    { ram := fun k hk => hk.elim (old.ram k) (fun hb => fresh.ram k (contained k hb))
      code := fun k hk => hk.elim (old.code k) (fun hb => fresh.code k (contained k hb))
      htif := fun k hk => hk.elim (old.htif k) (fun hb => fresh.htif k (contained k hb))
      stack := fun k hk => hk.elim (old.stack k) (fun hb => fresh.stack k (contained k hb)) }

#print axioms RuntimeOwnership.InitialOwned.bindingArena
#print axioms BindingArena.outsideWrites
#print axioms BindingArena.readGeometry
#print axioms BindingArena.extend

end Vsa.Sim
