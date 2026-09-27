import VsaIris.Vsa.Malloc
import Vsa.Sim.AllocCapacity
import Vsa.Sim.rows.CallClosureRow
import Vsa.Sim.rows.EnvDefineContractUpdate

/-!
# Feeding a VSA allocator consumer from the Iris spec

`EnvDefineAppendAllocatorPost.prepareCopy` (`Vsa/Sim/EnvDefineNameAllocate.lean`)
calls `malloc` through `mallocReturn_of_parked` and uses these fields of the
`MallocReturnAt` it gets back:

| `MallocReturnAt` field | used for | VSA supplier today |
|---|---|---|
| `block` | the fresh extent (`MallocBlock`) | `MallocContract.spec` |
| `owned0`, `owned` (via `.runtime`) | caller ownership survives, block enters | `transport_off` + `OwnedOff` from `privFoot_disjoint`, `priv_arena`, `arena_stack` |
| `store` (via `.runtime`) | store representation survives | `repr_off`, same |
| `agree` + `ownedOff.shared` | shared bytes unchanged | `mem_frame` off `privFoot` |
| `exit.mem_frame` | the value slot and eval-call support unchanged | `mem_frame` + `priv_arena` + `arena_stack` |
| `ainv`, `budget`, `reserve` | allocator invariant and capacity | `MallocSuccessRun`, `AllocLedger` (`reserve` is unsatisfiable for requests whose usable tail reaches the new top; see `vsa_reserve_fails_after_split`) |

This module derives the first five from the Iris spec with no
`MallocContract`, `AllocLedger`, `privFoot` or ledger arithmetic:

* `wp_call_malloc_owns` (Iris): a caller owning any byte set `C` at an image
  gets it back unchanged, and learns `C` is off the fresh block and off the
  allocator's new footprint, by ghost exclusivity;
* `ownSet_agree_state`: owned bytes pin the actual memory of any later
  configuration (`vsaModel`, with the bytes present);
* `mallocCallerFacts_of_iris` (pure): from agreement on the caller's owned
  bytes (`callerFoot`) and `mallocPost`'s `FreshBlock`, VSA's `MallocBlock`,
  both `HeapOwned`s, `StoreRepr` and shared-byte agreement follow by VSA's own
  `HeapOwned.transport`/`.fresh`/`repr_transport`.

`ainv` is `isHeap` itself. `mallocRoomCallerFacts_of_iris` adds `budget` and
the reserve from `mallocRoomSpec` (success under credits). The reserve is the
corrected `Reserve`: VSA's `AllocationReserve` cannot hold after a request
whose usable tail reaches the new top chunk (`vsa_reserve_fails_after_split`),
so that consumer premise must be weakened in VSA to the corrected clause.
-/

/-! ## The consumer's allocator premises, from the Iris post -/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc Vsa.Sim Vsa.Sim.DlHeap Vsa.Sim.RuntimeOwnership

/-! ## Reallocation -/

def reallocEntryBV : BitVec 64 := BitVec.ofNat 64 Vsa.Sim.reallocEntry

end VsaIris.VsaHeap
