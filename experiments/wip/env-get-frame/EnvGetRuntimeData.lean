import StoreRuntimeData
import EnvGetLookupData

open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim.RuntimeOwnership

theorem StoreRuntimeData.lookup
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Vsa.While.Addr → Nat} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {s : Vsa.While.Store} {m : Mem}
    (D : StoreRuntimeData N A SL phiF phiC alloc exts shared s m)
    {query : String} {name : BitVec 64} (hquery : SharedCString m shared name.toNat query)
    (hmask : MaskPinned m) :
    EnvGetReflected.LookupData N A SL phiF phiC alloc exts shared s query name m :=
  { owned := D.owned, repr := D.repr, arrays := D.arrays, ledger := D.ledger
    geometry := D.geometry, arenaLo := D.arenaLo, arenaHi := D.arenaHi
    arenaHtif := D.arenaHtif, queryString := hquery, mask := hmask, parents := D.parents }

end Vsa.Sim.RuntimeOwnership

namespace Vsa.Sim.EnvGetReflected
open RuntimeOwnership

theorem LookupData.runtime
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Vsa.While.Addr → Nat} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {s : Vsa.While.Store} {m : Mem}
    {query : String} {name : BitVec 64}
    (D : LookupData N A SL phiF phiC alloc exts shared s query name m)
    (arena : A.hi ≤ SL.lo ∨ SL.hi ≤ A.lo) :
    StoreRuntimeData N A SL phiF phiC alloc exts shared s m :=
  { owned := D.owned, repr := D.repr, arrays := D.arrays, ledger := D.ledger
    geometry := D.geometry, arenaLo := D.arenaLo, arenaHi := D.arenaHi
    arenaHtif := D.arenaHtif, arenaStack := arena, parents := D.parents }

#print axioms StoreRuntimeData.lookup
#print axioms LookupData.runtime

end Vsa.Sim.EnvGetReflected
