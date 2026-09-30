import Vsa.Sim.ExitFootprint
import Vsa.Sim.RuntimeOwnershipAllocation

/-!
# `IHClauseGenericAlloc` — the allocating arms' footprint premises (IH tower, Level 2)

The `Footprint` clause at `noArenaFoot` is FALSE for the arms that allocate:
`fn` (closure record + closure-array push), `call` of a closure (`env_new`,
argument binding, the body's own allocations), and string concatenation (the
concatenated payload; `value_str` itself only boxes a pointer —
`value_str_spec_full_exact` — so the string leaf is non-allocating).  Their footprint
includes fresh arena extents and allocator-private bytes.  This file states,
as doc-commented named premises, the exact fact each arm needs from the
allocator/ownership layer (`MallocContract`, `MallocRun`, `HeapOwned`,
`Reserved`; `PROOF_CLOSURE_PLAN.md`, task 2).  No step is proved here.

The footprint of an allocating call is `allocFoot`: the stack window, the result
slot, the allocator-private set `M.privFoot`, and the fresh extents (arena
blocks disjoint from every live extent of the entry ledger).  The clause extra
is stated over the entry ledger `exts` through `HeapOwned … m0 …`, the
memory-only characterisation of the live ledger the `EvalExtraM` world can
see (`EvalEntry` carries no ledger).
-/

open LeanRV64DExecutable Sail Vsa
open Vsa.Machine (Config)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.RuntimeOwnership (ExtentByte HeapOwned Reserved Allocations)

