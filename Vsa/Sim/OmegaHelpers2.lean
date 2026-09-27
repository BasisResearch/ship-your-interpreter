import Vsa.Sim.EvalSimCommon

/-!
# `OmegaHelpers2` — minimal-context re-index lemmas (omega paid ONCE)

Companion to `Vsa/Sim/OmegaHelpers.lean`. `OmegaHelpers` collapsed the spill/expr/slot
memory-safety omega shapes. This file collapses the OTHER dominant omega shape found in
`Vsa/Sim/EvalCallNative2.lean` (measured: ~245 `omega`, 53s — the file's whole elaboration
cost, `experiments/straggler-migration.md`): **stack-offset re-indexing** of the form
`fsp.toNat - c + d = fsp.toNat - c' + d'`, emitted as term-mode `show … from by omega`
inside a single ~600-line theorem. Each such `omega` was slow NOT because the goal is hard
(it needs only `80 ≤ fsp.toNat`) but because term-mode `by omega` ingests the theorem's
entire ~100-hypothesis linear-arith context. Proving the equality via a lemma whose ONLY
hypotheses are the frame bound + a ground arithmetic side-condition pays omega once (compiled
into this olean) and reduces each callsite to a typecheck.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

namespace Vsa.Sim

/-! ## `site_*_na` spill-store safety (the ~25s omega cluster in `EvalCallNative2`)

Each `site_<pc>_na` store takes FOUR safety preconditions over the store address
`addr = (v2 + sign_extend imm).toNat`: `0x80000000 ≤ addr`, `addr + 8 ≤ 2^64`,
`tohostAddr + 16 ≤ addr`, `addr % 8 = 0`. In `nativeAssertInternal` these were each a
term-mode `(by rw [haddrK]; …; omega)` running in the ~150-hypothesis theorem context —
measured ~25s of the file's 40s omega bill. `naStore_safe4` proves all four ONCE (omega in
this olean) from the address equation `haddr` (= `fsp.toNat - 80 + k`, `k ≤ 72` a multiple
of 8) + the four `RegionGuard fsp` frame bounds. Each site passes the four projections
`(h).1 (h).2.1 (h).2.2.1 (h).2.2.2`, running NO omega. -/

end Vsa.Sim
