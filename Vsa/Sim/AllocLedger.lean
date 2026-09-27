import Vsa.Sim.rows.EnvDefineMissLedger
import Vsa.Sim.AllocOff
import Vsa.Sim.AllocRuns
import Vsa.Sim.AllocMallocAdapters

/-!
# `AllocLedger` — ONE run-global allocator ledger and its call adapters

Every allocating call site of the interpreter (`env_new`, the three `env_define`
lanes, the closure build of the `fn` arm, the concatenation scratch buffers,
`strdup`, `stringify`) needs the same external facts about the fixed binary's
allocator: the `malloc`/`free`/`realloc` runs with silence and byte presence, the
`strlen`/`memcpy` runs, where the allocator-private footprint lives, how the
arena sits against the stack and the HTIF window, and that the allocator
invariant reads only `gp` and its private bytes.  Before this module each
per-entry ledger (`EnvNewLedger`, `EnvDefineUpdateLedger`, `EnvDefineMissLedger`)
restated those facts field by field, keyed to that entry's `esp`, `m` and `exts`.

`AllocLedger` is the run-global record: one per run, no entry parameters.  The
per-entry ledgers become projections of it plus the facts that are genuinely
entry-local (`EnvNewLedger.of_alloc`, `EnvDefineUpdateLedger.of_alloc`,
`EnvDefineMissLedger.of_alloc`), so a new allocating site adds no allocator
fields at all.

* `AInvAt` states the allocator invariant at a memory with the pinned `gp` and
  transports it; the per-entry `ainv_stable`/`ainv_private` fields collapse to
  `AllocLedger.ainv_stable` and `.ainvAt_transport`.
* `mallocReturn_of_parked` / `freeReturn_of_parked` are the callee adapters:
  from a parked call carrying the caller's ownership to the named return with
  the ledger advanced, the invariant re-established, the memory frame, the
  footprint (`allocFoot`, the allocating clause family), and the caller's store
  and ownership survived — via `OwnedOff` (`Vsa/Sim/AllocOff.lean`), which is
  proved once.
* `closurePushed_of_mallocReturn` completes the `fn` arm's closure build on the
  same adapter (`PROOF_CLOSURE_PLAN.md`, task 2).

The only genuinely new external clause is `AllocLedger.ainv_perm`: the abstract
live list is a set, needed to release a block that is not at the list's head
(`MallocContract.freeSpec` pops the head).  Relating `MallocContract.privFoot`
to dlmalloc's actual bin-link writes stays the verified-allocator obligation
behind `MallocContract` itself.
-/

