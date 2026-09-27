import Vsa.Sim.EnvCallBridge
import Vsa.Sim.ReprSurvival
import Vsa.Sim.HeapOps
import Vsa.Sim.RuntimeOwnershipAllocation
import Vsa.Sim.RuntimeOwnershipSeparation

/-!
# Exact footprint certificate for `env_set`

The machine overwrites one 24-byte `Value` slot.  `StoreRepr` does not imply
that this slot is disjoint from the objects reached by the other frames and
closures.  This file exposes that missing allocator/layout fact explicitly,
in the exact footprint shape consumed by `frameRepr_agreeP` and
`closureRepr_agreeP`.
-/

open Vsa
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While

