import EnvGetOutputTransport

open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim.EnvGetReflected
open RuntimeOwnership

/-- The reached evaluator prologue preserves every owned lookup supplier. -/
theorem LookupData.after_stack
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Vsa.While.Addr → Nat} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {s : Vsa.While.Store}
    {query : String} {name : BitVec 64} {m m' : Mem}
    (D : LookupData N A SL phiF phiC alloc exts shared s query name m)
    (arena : A.hi ≤ SL.lo ∨ SL.hi ≤ A.lo)
    (htif : tohostAddr + 16 ≤ SL.lo)
    (hm : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → m'[k]? = m[k]?) :
    LookupData N A SL phiF phiC alloc exts shared s query name m' := by
  let P := fun k => ¬ (SL.lo ≤ k ∧ k < SL.hi)
  have hag : AgreeP P m m' := fun k hk => (hm k hk).symm
  have ha : ∀ role p n, Allocated alloc role p n → ∀ k, ExtentByte (p, n) k → P k := by
    intro role p n hp k hk hin
    have hb := (D.ledger.arena.1 _ (D.ledger.live role p n hp)).2
    change A.lo ≤ p ∧ p + n ≤ A.hi at hb
    change p ≤ k ∧ k < p + n at hk
    omega
  have hs : ∀ k, shared k → P k := by
    intro k hk hin
    have := D.geometry.stack k hk
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

#print axioms LookupData.after_stack

end Vsa.Sim.EnvGetReflected
