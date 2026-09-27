import Vsa.Sim.EnvDefSpec2
import Vsa.Sim.HeapOwnershipGeometry

/-!
# `ReallocSpec` — corrected allocator-operation interface

The earlier `ReallocContract` cannot express `realloc(NULL,n)` and its public
memory frame omits the returned extent. This module supplies the operation
interface used by `HeapOps`. It is parameterized by one allocator invariant and
one private footprint, so malloc and realloc share the same ledger.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine Vsa.Logic Vsa.RuntimeRepr Vsa.Sim Vsa.Alloc

