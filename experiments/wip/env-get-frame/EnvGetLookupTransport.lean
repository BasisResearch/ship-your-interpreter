import EnvGetLookupData
import Vsa.Sim.RuntimeOwnershipTransport
import Vsa.Sim.EnvGetSpec9

open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim.EnvGetReflected
open RuntimeOwnership

/-- The caller's stack bounds and memory map place the prologue's spill window
inside the stack, outside the arena, and above the comparison mask. -/
structure LookupSpillWindow (A : Arena) (SL : StackLayout) (sp0 : BitVec 64) : Prop where
  stack : SL.lo ≤ (sp0 - 64#64).toNat ∧ (sp0 - 64#64).toNat + 64 ≤ SL.hi
  arena : A.hi ≤ SL.lo ∨ SL.hi ≤ A.lo
  mask : maskAddr + 8 ≤ (sp0 - 64#64).toNat

/-- The actual prologue memory frame preserves every lookup read supplier. -/
theorem LookupData.after_spill
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Vsa.While.Addr → Nat} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {s : Vsa.While.Store}
    {query : String} {name sp0 : BitVec 64} {m m' : Mem}
    (D : LookupData N A SL phiF phiC alloc exts shared s query name m)
    (hw : LookupSpillWindow A SL sp0)
    (hm : ∀ k, OutsideSpill sp0 k → m'[k]? = m[k]?) :
    LookupData N A SL phiF phiC alloc exts shared s query name m' := by
  have hag : AgreeP (OutsideSpill sp0) m m' := agreeP_of_prologue hm
  have ha : ∀ role p n, Allocated alloc role p n →
      ∀ k, ExtentByte (p, n) k → OutsideSpill sp0 k := by
    intro role p n hp k hk hin
    have hb := (D.ledger.arena.1 _ (D.ledger.live role p n hp)).2
    change A.lo ≤ p ∧ p + n ≤ A.hi at hb
    change p ≤ k ∧ k < p + n at hk
    change (sp0 - 64#64).toNat ≤ k ∧ k < (sp0 - 64#64).toNat + 64 at hin
    have hs := hw.stack
    rcases hw.arena with h | h <;> omega
  have hs : ∀ k, shared k → OutsideSpill sp0 k := by
    intro k hk hin
    have hshared := D.geometry.stack k hk
    have hstack := hw.stack
    change (sp0 - 64#64).toNat ≤ k ∧ k < (sp0 - 64#64).toNat + 64 at hin
    omega
  exact
    { owned := D.owned.transport hag ha hs
      repr := D.owned.repr_transport D.repr hag ha hs
      arrays := D.arrays.transport D.owned hag ha hs
      ledger := D.ledger
      geometry := D.geometry
      arenaLo := D.arenaLo
      arenaHi := D.arenaHi
      arenaHtif := D.arenaHtif
      queryString := D.queryString.transport (fun k hk => hag k (hs k hk))
      mask := maskPinned_outsideSpill hag (by
        intro k hk hin
        have hmask := hw.mask
        change (sp0 - 64#64).toNat ≤ maskAddr + k ∧
          maskAddr + k < (sp0 - 64#64).toNat + 64 at hin
        omega) D.mask
      parents := D.parents }

#print axioms LookupData.after_spill

end Vsa.Sim.EnvGetReflected
