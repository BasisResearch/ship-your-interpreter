import Vsa.Sim.NativeNameAudit.OwnershipExclusion
import Vsa.Sim.RuntimeOwnershipInitial

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While

namespace Vsa.Sim.NativeNameAudit
open Vsa.Sim.OutputAliasLoaded Vsa.Sim.LayoutInstance RuntimeOwnership

/-- No initial ownership data can repair the binding-name alias while keeping
the actual physical snapshot and global-environment pointer. -/
theorem nativeName_not_initialOwned
    {stmts count : Nat} {inp : BitVec 64} {N : NativeAddrs} {A : Arena}
    {phiF phiC : Addr → Nat} {budget : Nat} {D : InitialOwnershipData}
    (F : InterpRunPhysicalFacts nativeNameConfig stmts count inp N A phiF phiC budget) :
    ¬ InitialOwned nativeNameMem A stackSL phiF phiC stmts count D := by
  intro h
  have hg := F.globals
  rw [F.interp_local] at hg
  have hlink : phiF 0 = 0x81000000 :=
    Option.some.inj (hg.symm.trans nativeName_globals)
  exact nativeName_frame_not_owned hlink (Or.inl (by decide)) h.heap.immutable
    (h.heap.store.frames 0 (by decide))

#print axioms nativeName_not_initialOwned

theorem nativeName_not_readyFacts
    {stmts count : Nat} {inp : BitVec 64} {N : NativeAddrs} {A : Arena}
    {phiF phiC : Addr → Nat} {budget : Nat} :
    ¬ InterpRunReadyFacts nativeNameConfig stmts count inp N A phiF phiC budget := by
  intro F
  obtain ⟨D, h⟩ := F.ownership
  exact nativeName_not_initialOwned F.toInterpRunPhysicalFacts h

/-- Exclusion quantifies over every represented program and all data witnesses. -/
theorem nativeName_not_loaded (p : Program) :
    ¬ Vsa.Refine.Loaded interpRunLayout p nativeNameConfig := by
  rintro ⟨stmts, count, _, inp, N, A, phiF, phiC, budget, F⟩
  exact nativeName_not_readyFacts F

#print axioms nativeName_not_readyFacts
#print axioms nativeName_not_loaded

end Vsa.Sim.NativeNameAudit
