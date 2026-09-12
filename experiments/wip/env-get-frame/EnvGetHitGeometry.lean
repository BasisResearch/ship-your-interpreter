import EnvGetHitTail

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config)
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim.EnvGetReflected

/-- Static caller windows: the output and spills are disjoint stack ranges,
and the runtime arena lies outside the stack. -/
structure CallerTailWindow (A : Arena) (SL : StackLayout) (out sp : BitVec 64) : Prop where
  ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  htif : tohostAddr + 16 ≤ SL.lo
  output : SL.lo ≤ out.toNat ∧ out.toNat + 24 ≤ SL.hi
  spill : SL.lo ≤ sp.toNat ∧ sp.toNat + 64 ≤ SL.hi
  outputAlign : out.toNat % 8 = 0
  outputSpill : out.toNat + 24 ≤ sp.toNat ∨ sp.toNat + 64 ≤ out.toNat
  arena : A.hi ≤ SL.lo ∨ SL.hi ≤ A.lo

/-- The machine-selected source allocation supplies every source-side bound;
the caller windows and shared geometry supply destination separation. -/
theorem LookupData.hit_geometry
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Vsa.While.Addr → Nat} {alloc : RuntimeOwnership.Allocations}
    {exts : List Extent} {shared : Nat → Prop} {s : Vsa.While.Store}
    {query : String} {name out sp : BitVec 64} {v : Vsa.While.Value}
    {fa : Nat} {f : Vsa.While.Frame} {i pv : Nat} {c : Config}
    (D : LookupData N A SL phiF phiC alloc exts shared s query name c.σ.mem)
    (h : OwnedLookupHit N A phiF phiC shared s query v out sp fa f i pv c)
    (w : CallerTailWindow A SL out sp) :
    HitTailGeom (BitVec.ofNat 64 (phiF fa)) out sp pv i shared := by
  obtain ⟨hfa, _⟩ := Array.getElem?_eq_some_iff.mp h.source.frame
  have hframe := (D.repr.frames_arena fa hfa).1
  change A.lo ≤ phiF fa ∧ phiF fa + 32 ≤ A.hi at hframe
  have hsource := h.access.arena
  change A.lo ≤ pv + 24 * i ∧ pv + 24 * i + 24 ≤ A.hi at hsource
  have hlo := D.arenaLo
  have hhi := D.arenaHi
  have hht := D.arenaHtif
  have hram := w.ram
  have hwin := w.htif
  have hout := w.output
  have hspill := w.spill
  exact
    { envLo := by rw [h.envPointer]; omega
      envHi := by rw [h.envPointer]; omega
      envHtif := by rw [h.envPointer]; omega
      sourceLo := by omega
      sourceHi := by omega
      sourceHtif := by omega
      outLo := by omega
      outHi := by omega
      outHtif := by omega
      outAlign := w.outputAlign
      disjoint := by have := w.arena; omega
      index := Nat.lt_trans h.access.indexSigned (by decide)
      stackLo := by omega
      stackHi := by omega
      stackHtif := by omega
      outputSpill := w.outputSpill
      sharedOutput := fun k hk hin => by
        have := D.geometry.stack k hk
        omega }

#print axioms LookupData.hit_geometry

end Vsa.Sim.EnvGetReflected
