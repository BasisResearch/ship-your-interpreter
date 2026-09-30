import LeanRiscv
import Vsa.Sim.InitValues

/-! # Paid-once plumbing for the decode table

Every per-word `decode_<w>` lemma proves, under the three register pins
(`misa = initMisa`, `cur_privilege = Machine`, `mseccfg = 0`), that
`(ext_decode w).run σ = .ok <instruction> σ` by a single grounding `simp only`
followed by `rfl`.

The grounding `simp only` must unfold `currentlyEnabled` and `hartSupports`,
whose bodies are large `match`es on the `extension` enum. Elaborating that
`simp` **realizes the match splitters**
`currentlyEnabled.match_1.splitter` / `hartSupports.match_1.splitter`, a
`Meta.realizeConst` step that costs ~1.6 s *the first time it is needed in a
module*. Measured: an isolated per-word lemma costs 2.45 s, of which 1.6 s is
that one-time splitter realization; every *subsequent* lemma in the same module
costs only ~0.4 s.

This module forces those splitters to be realized once, here, and bakes them
into `DecodeCommon.olean`. Any module that `import`s `DecodeCommon` reuses the
persisted splitters and pays 0 s for realization — dropping an isolated
per-word lemma from 2.45 s to ~0.4 s (measured 0.52 s incl. import).

Do not delete `decodeCommon_splitter_seed`: its proof is exactly the per-word
template, and running it is what realizes the splitters into this olean. -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 16000000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

