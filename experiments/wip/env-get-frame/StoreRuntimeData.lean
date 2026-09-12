import Vsa.Sim.RuntimeOwnershipInitial
import SharedReadGeometry

open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim.RuntimeOwnership

/-- Query-independent runtime data carried between recursive entries and exits. -/
structure StoreRuntimeData (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (phiF phiC : Vsa.While.Addr → Nat) (alloc : Allocations)
    (exts : List Extent) (shared : Nat → Prop) (s : Vsa.While.Store) (m : Mem) : Prop where
  owned : StoreOwned m phiF phiC alloc shared s
  repr : StoreRepr m N A phiF phiC s
  arrays : StoreArraysReady m phiF s
  ledger : Ledger A exts alloc
  geometry : SharedReadGeom shared SL
  arenaLo : 0x80000000 ≤ A.lo
  arenaHi : A.hi ≤ 0x100000000
  arenaHtif : tohostAddr + 8 ≤ A.lo
  arenaStack : A.hi ≤ SL.lo ∨ SL.hi ≤ A.lo
  parents : StoreParents s

end Vsa.Sim.RuntimeOwnership
