import Vsa.Sim.ReallocSpec
import Vsa.Sim.AllocSuccess
import Vsa.Sim.StrlenSpec
import Vsa.Sim.MemcpySpecFramedWord
import Vsa.Sim.Code.FixedImage_Strlen
import Vsa.Sim.Code.FixedImage_Memcpy
import Vsa.Sim.AllocOff

/-!
# `AllocRuns` — the allocator's callee runs and the run-global ledger

The runs each allocating site needs, and the one record that bundles them, must
sit BELOW every per-entry ledger that carries them.  They did not: `MallocRun`
was declared in `rows/EnvNewContractSupply.lean` and the `realloc`/`strlen`/
`memcpy` runs in `rows/EnvDefineMissLedger.lean`, while `AllocLedger` bundles all
four and imports the latter — so no per-entry ledger could take an `AllocLedger`
field without an import cycle, and each went on restating the allocator fields
itself.

This module is that preparatory move.  It holds the runs (`MallocRun`, `FreeRun`,
`ReallocRun`/`ReallocInstance`, `StrlenRun`, `MemcpyRun`), each being the landed
callee contract plus the clauses it omits — no console output and no byte
removal — and the run-global `AllocLedger` with `AInvAt` and its transport
lemmas.  The call adapters stay in `Vsa/Sim/AllocLedger.lean`, above the
per-entry ledgers they serve.

Nothing here is new: every declaration moved verbatim from one of those three
files.  What changes is only that a per-entry ledger may now hold ONE `alloc`
field instead of restating the allocator.
-/

