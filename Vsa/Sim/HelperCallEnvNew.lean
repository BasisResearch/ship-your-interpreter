import Vsa.Sim.HelperCall

/-!
# `HelperCallEnvNew` — the `env_new` contract and its adapter

`env_new(parent)` allocates a fresh 32-byte frame whose parent is the given
environment and returns its address (`Store.allocFrame`).  `env_new_spec`
(`EnvNewSpec.lean`) proves the machine path over a `MallocContract`; what the
statement arms need beyond it is the store representation of the pushed
store under an extended frame map, which requires the fresh address to be
disjoint from every represented frame (the allocation ledger of task 2).
This file states the contract the block and for arms consume, ONCE, as a
named premise:

* `EnvNewEntryState`: the parametric call parked at `env_new` with `a0` the
  parent frame pointer, plus the memory facts every consumer has
  (`EnvNewMem`);
* `EnvNewReturnState`: the return at the link PC with the fresh frame
  pointer in `a0`, the extended map (`EnvNewFresh`), memory unchanged outside
  the arena and the callee's stack window, presence preserved;
* `EnvNewContract`: the Triple between them, for all ghosts.

**Supplier.** `env_new_spec` with `MallocContract`, `storeRepr_allocFrame`
(`rows/CallClosureEnvNewMarshal.lean`) for the pushed store, the freshness of
the returned block against the represented frames (the ownership ledger
relating `StoreRepr` images to the allocator's extents), and the
allocator-private footprint inside the arena.
-/

