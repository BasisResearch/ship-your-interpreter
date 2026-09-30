import Vsa.Sim.RuntimeOwnershipAllocation
import Vsa.Sim.ReallocSpec

/-! Reallocation geometry for one old mutable role. The replacement may overlap
its old extent. Freshness is required only against surviving live extents,
exactly as in ReallocGrowResult. No old-extent byte preservation is asserted. -/

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

