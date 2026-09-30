import Vsa.Sim.RuntimeOwnership

/-! Derive the old append/set byte-footprint interfaces from allocation roles.
The geometry arguments are data facts. No machine transition is a premise. -/

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

