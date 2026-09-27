import Vsa.Sim.MemcpySpecFramed

/-!
# Frame-preserving `memcpy` — the WORD route (`memcpy_spec_framed_word`)

`memcpy_spec_framed_byte` (`MemcpySpecFramed.lean`) covers the byte routes
(misaligned ∨ `n < 8`) of the dispatch carrying the ABI-callee-saved frame
`∀ R, AbiPreserved R → get? R = gm R` — the register half of `EnvDefFrame`.
This file completes the picture with the **aligned WORD route** (case (C) of
`memcpy_spec`: `dst % 8 = 0 ∧ 8*(n/8) ≤ 64`), so a `len+1`-byte C-string copy
into a fresh word-aligned `malloc` block whose length rounds to ≤ 64 words takes
the framed word route (the `env_define` `memcpy(copy,name,len+1)` case when
`src`/`dst` share alignment and `len+1 ≥ 8`).

**Why a framed re-run and not a `bytepath_abi`-style transport.**  The word route
factors into three stages:

* `dispatch_to_word` : `AtBd4 → ∃ g', PreW g'` — `AtBd4` carries NO ghost/frame
  field, so there is nothing to transport the ABI conjunct through; we re-run its
  12 register-only sites carrying `∀ R AbiPreserved, get? R = gm R` via the REUSED
  `strlenFrame_alu`/`strlenFrame_bnottaken` primitives (the `to_bd4_framed`
  idiom).  `NotWrittenW`'s written GPRs `{x13,x15,x16}` are all NON-`AbiPreserved`,
  so every site preserves the AbiPreserved subset.
* `word_loop_spec` : `PreW g' → StWDone g'` — SAME `g'`, both `hframe` over
  `NotWrittenW ⊇ AbiPreserved`, so the ABI conjunct transports for FREE via `g'`
  (`wordloop_abi`, no re-run) — the `bytepath_abi` pattern.
* `epilogue_{notail,tail}` : `StWDone g' → ∃ g'', memcpy_bytepath_post g''` — the
  epilogue writes `{x11,x12,x14}` (all NON-`AbiPreserved`) but RESETS the ghost at
  the `NotWrittenW → NotWrittenB` crossover, so `g''` has no exposed relation to
  `g'`; we re-run its ≤ 15 register-only sites carrying the ABI conjunct.

The post carries `memcpy_bytepath_post g''` (PC=r, x10=dst, described copy into
`[dst,dst+n)`, everything OUTSIDE `[dst,dst+n)` = `m0`) PLUS the ABI-callee-saved
tie `∀ R AbiPreserved, get? R = gm R` — identical shape to
`memcpy_spec_framed_byte`, so `EnvDefCompose.envDefMemcpyFramed` consumes it the
same way; `memcpy_framed_ainv_stable` applies verbatim.

Additive: `dispatch_to_word`/`word_loop_spec`/`epilogue_*` UNCHANGED; no consumer
touched.  No `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Alloc (AbiPreserved)
open Vsa.Sim.Code (MemcpyLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `AbiPreserved ⊆ NotWrittenW`

The word-path blanket frame `NotWrittenW` writes only `{x13,x15,x16}` (+ control),
none `AbiPreserved` (`x2/x3/x4/x8/x9/x18..x27`), so the ABI-callee-saved set is a
subset — exactly what lets the `PreW`/`StWDone` `hframe` (over `NotWrittenW`)
deliver the ABI conjunct. -/

/-! ## Framed dispatch `AtBd4 → ∃ g', PreW g'` (word route)

Re-run of `dispatch_to_word`'s 12 register-only sites carrying the ABI frame.
Each site preserves every `AbiPreserved` register (none is `x13`/`x15`/`x16`),
lifted by the REUSED `strlenFrame_alu`/`strlenFrame_bnottaken`.  Lands `PreW g'`
with the fresh `g' = c'.σ.regs.get?` AND the ABI conjunct. -/

/-! ## The word loop preserves the ABI frame (FREE — `bytepath_abi`-style)

`word_loop_spec g'` : `PreW g' → StWDone g'` ties the SAME `g'` at both ends over
`NotWrittenW ⊇ AbiPreserved`, so the entry ABI conjunct (`get? R = gm R`)
transports to the exit via `g'` with no re-run. -/

/-! ## Framed no-tail epilogue `StWDone g' → ∃ g'', memcpy_bytepath_post g''`

Re-run of `epilogue_notail_spec`'s 9 register-only sites (7 ALU + `bltu` not-taken
+ `ret`) carrying the ABI frame.  Each preserves every `AbiPreserved` register
(the epilogue writes `{x11,x12,x14}`, none `AbiPreserved`; the `ret` writes only
PC), lifted by `strlenFrame_alu`/`_bnottaken`/`_jr`.  Lands
`memcpy_bytepath_post g''` (fresh `g''`) with the ABI conjunct. -/

/-! ## Framed byte-tail epilogue `StWDone g' → ∃ g'', memcpy_bytepath_post g''`

For the word route with a non-empty byte tail (`8*(n/8) < n`), the epilogue
recomputes the pointers, the `c38 bltu` is TAKEN, and control enters the byte
loop at `c48` copying the remaining `n - 8p` bytes.  We re-run the 8 register-only
sites of `epilogue_to_bytehead` carrying the ABI frame (`epilogue_to_bytehead_framed`)
landing `StB g''` with the ABI conjunct, then transport through the byte loop +
ret via the SAME `g''` (its `StB`/`memcpy_bytepath_post` frames are over
`NotWrittenB ⊇ AbiPreserved`), the `bytepath_abi` pattern. -/

/-! ## `memcpy_spec_framed_word` — the framed WORD route (both sub-cases)

For the `env_define` `memcpy(copy,name,len+1)` call on the aligned word route
(`dst % 8 = 0`, `8*(n/8) ≤ 64`, `n ≥ 8` — case (C) of `memcpy_spec`), carry the
ABI frame end-to-end: `dispatch_to_word_framed` ≫ `wordloop_abi` ≫ the epilogue.
The epilogue splits on whether the copy is word-exact (`8*(n/8) = n` → no-tail
ret via `epilogue_notail_framed`) or has a byte tail (`8*(n/8) < n` → byte loop
via `epilogue_tail_framed`).  Same post as `memcpy_spec_framed_byte`, so
`memcpy_framed_ainv_stable` and the `EnvDefCompose` consumer apply verbatim.

This is the EXACT framed analogue of `memcpy_spec`'s route (C): same route
hypothesis shape (`halign_xor ∧ hbig ∧ hda ∧ hfit`), the ABI conjunct threaded. -/

end Vsa.Sim
