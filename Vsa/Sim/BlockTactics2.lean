import Vsa.Sim.InterpEntry
import Vsa.Sim.BlockDecode
import Vsa.Sim.BlockTactics
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch03Part09
import Vsa.Sim.DecodeTable.Batch03Part19
import Vsa.Sim.DecodeTable.Batch04Part07
import Vsa.Sim.DecodeTable.Batch09Part03
import Vsa.Sim.DecodeTable.Batch09Part05
import Vsa.Sim.DecodeTable.Batch09Part07
import Vsa.Sim.DecodeTable.Batch09Part24
import Vsa.Sim.DecodeTable.Batch09Part25
import Vsa.Sim.DecodeTable.Batch09Part31
import Vsa.Sim.DecodeTable.Batch10Part09
import Vsa.Sim.DecodeTable.Batch11Part11
import Vsa.Sim.DecodeTable.Batch11Part21
import Vsa.Sim.DecodeTable.Batch13Part26
import Vsa.Sim.DecodeTable.Batch15Part07
import Vsa.Sim.RamReadPins

/-!
# Stage C — block-frame discharge helpers (`BlockTactics2`)

Reusable helpers for the register-frame side-conditions the block frame lemmas
(`hframePro`/`hframeBlk`/`hframeTail`, i.e. the `∀ R … → σ'.R = σ.R` outputs of
`neg_prologue_block`/`neg_loadstore_full`/`neg_tail_block`) demand at each call
site. Each such application needs two arguments for a universally-quantified
register `R`:

1. `(∀ rr ∈ noiseRegs, (rr == R) = false)` — closed by `abiNoise_noiseRegs hR`.
2. `(∀ n ∈ wrRegsM b.body, (gprReg n == R) = false)` — closed by the
   `block_frame_wr` tactic given the block's concrete written-reg index list.

`abiPreserved_ne` is the standalone form of the local `abi_ne'` those proofs
carried inline (the callee-saved exceptions like `he8 : (Register.x8 == R) =
false` are picked up by an `assumption` arm).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`. Only Lean 4 core + Std tactics.
-/

open LeanRV64DExecutable Vsa
open Register
open Vsa.Alloc
open Lean Elab Tactic
open Lean.Parser.Tactic

namespace Vsa.Sim

/-- `AbiPreserved R` and `¬ AbiPreserved X` give `(X == R) = false`: two distinct
callee-saved-vs-not registers can never be equal. The standalone form of the
inline `abi_ne'` that `blockC_neg`'s `hframeG` carried. -/
theorem abiPreserved_ne {R X : Register} (hR : AbiPreserved R = true)
    (hX : AbiPreserved X = false) : (X == R) = false := by
  rcases hXR : (X == R) with _ | _
  · rfl
  · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)

/-! ## C3 — load/store side-condition bundle discharge (`ld_ok` / `st_ok`)

The block Pres (`NegBlockProto.LdOK8`/`LdOK4`/`StOK8`) each bundle the RAM-bound /
HTIF-window / alignment sub-facts (and, for loads, the byte pins). Call sites used
to spell out the anonymous constructor with a per-field `by rw [haddr…]; omega`.
These tactics assemble the bundle from ONE address-normaliser `haddr : ea.toNat =
k` (the RAM/window/alignment facts then follow by `omega` off the ambient `sp`/
`tohost` bounds) plus the caller's byte pins.

`tohostAddr` is a `def`; `omega` can't see through it, so each tactic first
rewrites it to its literal value (`rfl`) before the `omega`. -/

end Vsa.Sim
