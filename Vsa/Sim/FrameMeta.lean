import Vsa.Sim.WriteLogNF
import Vsa.Sim.BlockTactics2

/-!
# `FrameMeta` — the two ONE-TIME framing metatheorems

The block-reflection soundness lemmas (`block_mem_sound`, `bblock_sound_bt`,
`bblocks_sound_bt`) each ALREADY carry, in their conclusion, a **register frame
clause** of the exact shape

    ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
                    (∀ n ∈ wrRegsM is, (gprReg n == R) = false) →
      σ'.regs.get? R = σ.regs.get? R                                  (block)

    …            (∀ n ∈ wrChain bs, (gprReg n == R) = false) → …      (chain)

and a **computed memory post** `σ'.mem = writeLog σ.mem (wlogM is L lds)` (block)
/ `σ'.mem = memChain bs σ.mem L lds` (chain).  Every framed *callee* variant so
far (e.g. `MemcpySpecFramed.to_bd4_framed`, `EnvGetSpec4`'s `hghost*` ladder) is
built by *re-threading these two facts by hand, per site* — `strlenFrame_alu
hobs R (by decide) hR` on every instruction, a per-callee re-derivation that
consumed multiple agent sessions.

This module makes the framed variant **free**, as a thin corollary of the frame
clause the layer already produces.  It contributes:

## (c) ABI-frame metatheorem

`WrRegsAvoidAbi is` / `WrChainAvoidAbi bs` — first-order `decide`-checkable
predicates: *no* register the block/chain writes is `AbiPreserved`.  These
reduce, per block/chain shape, to ONE small kernel `decide` on the concrete GPR
index list.

`abiFrame_of_wrRegs` / `abiFrame_of_wrChain` — from that decide fact,
**discharge both hypotheses** of the frame clause for every `AbiPreserved R`,
collapsing it to the familiar callee shape

    ∀ R, AbiPreserved R = true → σ'.regs.get? R = σ.regs.get? R.

(The noise disequalities come for free: no `noiseRegs` element is `AbiPreserved`,
so `abiPreserved_ne` closes each `(rr == R) = false`.)

`abiFramePost_block` / `abiFramePost_chain` — package the block/chain soundness
lemma's *whole* conclusion with the register frame already collapsed to the ABI
shape, so a caller `obtain`s the framed post directly.

## (d) Footprint metatheorem

The memory post is a `writeLog` / `memChain` (a fold of `writeLog`).
`Vsa/Sim/WriteLogNF.lean` already proves `writeLog_out : OutL log a →
(writeLog m log)[a]? = m[a]?`.  `outL_memChain` lifts this to the chain fold,
and `memFrame_of_block` / `memFrame_of_chain` expose the memory-frame post as a
**predicate over the (possibly symbolic) log** — reads outside the log footprint
agree with entry memory:

    ∀ a, OutL (wlogM is L lds) a → σ'.mem[a]? = σ.mem[a]?     (block)
    ∀ a, OutChain bs σ.mem L lds a → σ'.mem[a]? = σ.mem[a]?    (chain)

No ground addresses are demanded: `OutL` is the recursive list predicate that
unfolds to a conjunction of linear disjointness facts for any *concrete* log,
symbolic bounds included (closed at a use site by `simp only [OutL]; omega`).

NO Mathlib.  NO `sorry`/`axiom`/`native_decide`/`bv_decide`.  One small `decide`
per block/chain shape; all memory reasoning is on the write-log, never the Sail
state.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Alloc (AbiPreserved)

namespace Vsa.Sim

/-! ## (c) — the ABI register-frame metatheorem -/

/-- The chain analogue over `wrChain bs`. -/
def WrChainAvoidAbi (bs : List BBlock) : Prop :=
  ∀ n ∈ wrChain bs, AbiPreserved (gprReg n) = false

/-- **Noise never collides with a callee-saved register.**  `noiseRegs` is the
seven machine-control registers (PC/nextPC/minstret/…); none is `AbiPreserved`,
so for any `AbiPreserved R` every `(rr == R)` is `false`.  This discharges the
FIRST hypothesis of the frame clause from `AbiPreserved R = true` alone. -/
theorem noise_ne_abi {R : Register} (hR : AbiPreserved R = true) :
    ∀ rr ∈ noiseRegs, (rr == R) = false := by
  intro rr hrr
  simp only [noiseRegs, List.mem_cons, List.not_mem_nil, or_false] at hrr
  rcases hrr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact abiPreserved_ne hR (by decide)

theorem wrChain_ne_abi {bs : List BBlock} (hAvoid : WrChainAvoidAbi bs)
    {R : Register} (hR : AbiPreserved R = true) :
    ∀ n ∈ wrChain bs, (gprReg n == R) = false :=
  fun n hn => abiPreserved_ne hR (hAvoid n hn)

/-- **ABI-frame metatheorem (chain).**  Same, over `wrChain bs`. -/
theorem abiFrame_of_wrChain {bs : List BBlock} {σ' σ : MState}
    (hAvoid : WrChainAvoidAbi bs)
    (hframe : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      (∀ n ∈ wrChain bs, (gprReg n == R) = false) →
      σ'.regs.get? R = σ.regs.get? R) :
    ∀ R, AbiPreserved R = true → σ'.regs.get? R = σ.regs.get? R :=
  fun R hR => hframe R (noise_ne_abi hR) (wrChain_ne_abi hAvoid hR)

/-! ## (d) — the footprint metatheorem -/

/-! ## Packaged framed soundness — the block/chain lemma with the frame already
collapsed to the ABI + footprint shape.  A caller `obtain`s the framed post
directly; the two `WrRegsAvoidAbi`/`WrChainAvoidAbi` premises are `by decide`
per shape. -/

/-! ## Demonstration — the framed `memmove` dispatch variant, FREE

`BlockTermDemo.mv_dispatch_setup_block` is a REAL 4-block callee segment
(`mvDispatchSetup = [mvB1..mvB4]`, the `memmove` dispatch+setup, writing the
caller-saved `{a5=15, a3=13}`).  Its conclusion exposes the *raw* frame clause

    ∀ R, (∀ rr ∈ noiseRegs, (rr == R) = false) →
         (∀ nn ∈ [15,15,13,13,13], (gprReg nn == R) = false) →
      σ'.regs.get? R = σ.regs.get? R

— which every consumer then hand-threads with `block_frame_wr [15,15,13,13,13]`
per register.  Below, the **framed ABI variant** (callee-saved preservation +
footprint) is derived from that clause in ONE line each, via the metatheorems,
with the disjointness discharged by a single `decide`.

BEFORE (per consumer, per callee, the whole `MemcpySpecFramed`/`EnvGetSpec4`
`hghost*` ladder): re-run the segment site by site, `strlenFrame_alu hobs R
(by decide) hR` on *every* instruction, threading `∀ R, AbiPreserved R → … = gm R`
across each — O(sites) `have`s, a multi-session per-callee re-derivation.

AFTER (below): `abiFrame_of_wrChain (by decide) hframe` + `memFrame_of_chain`.
Two lines.  No site threading. -/

end Vsa.Sim
