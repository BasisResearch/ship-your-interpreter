import Vsa.Sim.EnvGetReflected.EnvGetHitGeometry
import Vsa.Sim.ValueEqualSpec3

open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim.EnvGetReflected
open RuntimeOwnership

/-- The actual output-copy frame preserves the lookup store and shared data. -/
theorem LookupData.after_stack_slot
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Vsa.While.Addr → Nat} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {s : Vsa.While.Store}
    {query : String} {name out : BitVec 64} {m m' : Mem}
    (D : LookupData N A SL phiF phiC alloc exts shared s query name m)
    (slot : SL.lo ≤ out.toNat ∧ out.toNat + 24 ≤ SL.hi)
    (arena : A.hi ≤ SL.lo ∨ SL.hi ≤ A.lo)
    (htif : tohostAddr + 16 ≤ SL.lo)
    (hm : ∀ k, ¬ (out.toNat ≤ k ∧ k < out.toNat + 24) → m'[k]? = m[k]?) :
    LookupData N A SL phiF phiC alloc exts shared s query name m' := by
  let P := fun k => ¬ (out.toNat ≤ k ∧ k < out.toNat + 24)
  have hag : AgreeP P m m' := fun k hk => (hm k hk).symm
  have ha : ∀ role p n, Allocated alloc role p n → ∀ k, ExtentByte (p, n) k → P k := by
    intro role p n hp k hk hin
    have hb := (D.ledger.arena.1 _ (D.ledger.live role p n hp)).2
    change A.lo ≤ p ∧ p + n ≤ A.hi at hb
    change p ≤ k ∧ k < p + n at hk
    omega
  have hs : ∀ k, shared k → P k := by
    intro k hk hin
    have hg := D.geometry.stack k hk
    omega
  exact
    { owned := D.owned.transport hag ha hs
      repr := D.owned.repr_transport D.repr hag ha hs
      arrays := D.arrays.transport D.owned hag ha hs
      ledger := D.ledger, geometry := D.geometry
      arenaLo := D.arenaLo, arenaHi := D.arenaHi, arenaHtif := D.arenaHtif
      queryString := D.queryString.transport (fun k hk => hag k (hs k hk))
      mask := maskPinned_of_agree m m' (fun k hlo hhi => hm k (by
        have ht : tohostAddr = 0x8001ad00 := rfl
        have hmask : maskAddr = 0x8001ac80 := rfl
        omega)) D.mask
      parents := D.parents }

/-- The existing caller-window adapter projects the shared stack-slot transport. -/
theorem LookupData.after_output
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Vsa.While.Addr → Nat} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {s : Vsa.While.Store}
    {query : String} {name out sp : BitVec 64} {m m' : Mem}
    (D : LookupData N A SL phiF phiC alloc exts shared s query name m)
    (w : CallerTailWindow A SL out sp)
    (hm : ∀ k, ¬ (out.toNat ≤ k ∧ k < out.toNat + 24) → m'[k]? = m[k]?) :
    LookupData N A SL phiF phiC alloc exts shared s query name m' :=
  D.after_stack_slot w.output w.arena w.htif hm

#print axioms LookupData.after_stack_slot
#print axioms LookupData.after_output

end Vsa.Sim.EnvGetReflected
