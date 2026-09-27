import Vsa.Sim.InductionScaffold

/-!
# Honest no-op rows for the loop scaffold

`ExecInit.none`, `ForCond.none`, and `ExecStep.none` do not change the
specification state. Their machine rows are identity triples only when the
entry and exit PCs coincide. This file provides that common proof once.

HISTORICAL (2026-08-31, ledgers `scaffold-motive-independent-pq` then
`scaffold-some-motive-unsatisfiable`): the `TermSimAssembly` scaffold motives
formerly quantified independent `p`/`q` (no identity row could discharge them);
amended to a single identity-PC `p`, which fixed `.none` (via `segIdentity`) but
left the DUAL `.some` obstruction (store-mutating span at the same PC is
unsatisfiable). FINAL amendment: `mExecInit`/`mForCond`/`mExecStep` are now `True`
(dead recursor plumbing — `execForStartSim` ignores these sub-derivations), so all
six premises (`hInit{None,Some}`/`hFc{None,Some}`/`hEs{None,Some}`) are LANDED as
`trivial` rows in `Vsa/Sim/rows/ScaffoldRows.lean`; the `.some` `*_resid` defs are
DELETED. `segIdentity` (this file) is STILL live: `mForLoop` remains an
identity-PC `SegEntry → SegExit` span and `ScaffoldRows`/`SeqForRows`'s `ForResid`
uses it. A no-op row uses one shared PC.

Timing witness (2026-08-26): `lake env lean Vsa/Sim/LoopScaffoldClose.lean`
completed in 4.55 seconds.

-/

