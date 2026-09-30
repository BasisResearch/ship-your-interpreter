import Vsa.Sim.ReallocSpec
import Vsa.Sim.StoreInvariant
import Vsa.Sim.AstTransport
import Vsa.Sim.rows.StoreReprPhicRebase

/-!
# `HeapOps` — one allocator ledger for interpreter heap operations

`MallocContract` and `ReallocOps` are packaged here against the same
allocator invariant and private footprint. `HeapRepr` adds the allocation
ownership facts deliberately absent from `StoreRepr`: environment records,
their backing arrays, copied binding names, and closure records all belong to
live extents.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open Vsa.MemRepr

