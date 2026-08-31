import Vsa.Sim.BlockTerm
import Vsa.Sim.WriteLogNF
import Vsa.Sim.BlockTactics2
import Vsa.Sim.BlockTermDemo

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

/-- **The `decide`-checkable disjointness datum** for a block: no GPR the block
writes is `AbiPreserved`.  First-order over the block body (`wrRegsM is` is a
concrete `List Nat`); for any concrete block this closes by ONE kernel `decide`
(`WrRegsAvoidAbi is := by decide`). -/
def WrRegsAvoidAbi (is : List MInstr) : Prop :=
  ∀ n ∈ wrRegsM is, AbiPreserved (gprReg n) = false

/-- The chain analogue over `wrChain bs`. -/
def WrChainAvoidAbi (bs : List BBlock) : Prop :=
  ∀ n ∈ wrChain bs, AbiPreserved (gprReg n) = false

instance (is : List MInstr) : Decidable (WrRegsAvoidAbi is) := by
  unfold WrRegsAvoidAbi; infer_instance

instance (bs : List BBlock) : Decidable (WrChainAvoidAbi bs) := by
  unfold WrChainAvoidAbi; infer_instance

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

/-- **The wrRegs guard, discharged by `decide`.**  Given `WrRegsAvoidAbi is`
(one decide) and `AbiPreserved R = true`, every written register `gprReg n`
differs from `R` — because `gprReg n` is not callee-saved but `R` is. -/
theorem wrRegs_ne_abi {is : List MInstr} (hAvoid : WrRegsAvoidAbi is)
    {R : Register} (hR : AbiPreserved R = true) :
    ∀ n ∈ wrRegsM is, (gprReg n == R) = false :=
  fun n hn => abiPreserved_ne hR (hAvoid n hn)

theorem wrChain_ne_abi {bs : List BBlock} (hAvoid : WrChainAvoidAbi bs)
    {R : Register} (hR : AbiPreserved R = true) :
    ∀ n ∈ wrChain bs, (gprReg n == R) = false :=
  fun n hn => abiPreserved_ne hR (hAvoid n hn)

/-- **ABI-frame metatheorem (block).**  Any frame clause of the shape the block
soundness lemmas produce collapses — under `WrRegsAvoidAbi is` (one `decide`) —
to the callee-contract shape `∀ R, AbiPreserved R → get? R = get? R`.  This is
the whole content of a "framed variant": the register-preservation obligation,
free. -/
theorem abiFrame_of_wrRegs {is : List MInstr} {σ' σ : MState}
    (hAvoid : WrRegsAvoidAbi is)
    (hframe : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      (∀ n ∈ wrRegsM is, (gprReg n == R) = false) →
      σ'.regs.get? R = σ.regs.get? R) :
    ∀ R, AbiPreserved R = true → σ'.regs.get? R = σ.regs.get? R :=
  fun R hR => hframe R (noise_ne_abi hR) (wrRegs_ne_abi hAvoid hR)

/-- **ABI-frame metatheorem (chain).**  Same, over `wrChain bs`. -/
theorem abiFrame_of_wrChain {bs : List BBlock} {σ' σ : MState}
    (hAvoid : WrChainAvoidAbi bs)
    (hframe : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      (∀ n ∈ wrChain bs, (gprReg n == R) = false) →
      σ'.regs.get? R = σ.regs.get? R) :
    ∀ R, AbiPreserved R = true → σ'.regs.get? R = σ.regs.get? R :=
  fun R hR => hframe R (noise_ne_abi hR) (wrChain_ne_abi hAvoid hR)

/-! ## (d) — the footprint metatheorem -/

/-- The whole chain's write-log footprint, as a predicate over the (possibly
symbolic) per-block logs threaded through the fold — the memory analogue of
`wrChain`.  `OutChain bs m L lds a` says `a` is outside every block's log.
Recursive, so a concrete chain unfolds to a conjunction of `OutL` facts. -/
def OutChain : List BBlock → Std.ExtHashMap Nat (BitVec 8) → GRegs →
    List (List (BitVec 8)) → Nat → Prop
  | [], _, _, _, _ => True
  | b :: bs, m, L, lds, a =>
    OutL (wlogM b.body L lds) a ∧
    OutChain bs (writeLog m (wlogM b.body L lds)) (runGM b.body L lds)
      (ldsRunM b.body lds) a

/-- Reads outside every block's log footprint pass through the whole `memChain`
fold (the chain lift of `writeLog_out`). -/
theorem outL_memChain (bs : List BBlock) :
    ∀ (m : Std.ExtHashMap Nat (BitVec 8)) (L : GRegs) (lds : List (List (BitVec 8)))
      (a : Nat), OutChain bs m L lds a → (memChain bs m L lds)[a]? = m[a]? := by
  induction bs with
  | nil => intro m L lds a _; rfl
  | cons b bs ih =>
    intro m L lds a hout
    obtain ⟨houtb, houtr⟩ := hout
    show (memChain bs (writeLog m (wlogM b.body L lds)) (runGM b.body L lds)
      (ldsRunM b.body lds))[a]? = m[a]?
    rw [ih _ _ _ a houtr, writeLog_out m (wlogM b.body L lds) a houtb]

/-- **Footprint metatheorem (block).**  From the block soundness lemma's memory
post `σ'.mem = writeLog σ.mem (wlogM is L lds)`, reads outside the log agree
with the entry memory — the mem-frame post as a predicate over the (symbolic)
log.  No ground addresses required. -/
theorem memFrame_of_block {σ' σ : MState} {is : List MInstr}
    {L : GRegs} {lds : List (List (BitVec 8))}
    (hmem : σ'.mem = writeLog σ.mem (wlogM is L lds)) :
    ∀ a, OutL (wlogM is L lds) a → σ'.mem[a]? = σ.mem[a]? :=
  fun a ha => by rw [hmem]; exact writeLog_out σ.mem (wlogM is L lds) a ha

/-- **Footprint metatheorem (chain).**  Same over `memChain`. -/
theorem memFrame_of_chain {σ' σ : MState} {bs : List BBlock}
    {L : GRegs} {lds : List (List (BitVec 8))}
    (hmem : σ'.mem = memChain bs σ.mem L lds) :
    ∀ a, OutChain bs σ.mem L lds a → σ'.mem[a]? = σ.mem[a]? :=
  fun a ha => by rw [hmem]; exact outL_memChain bs σ.mem L lds a ha

/-! ## Packaged framed soundness — the block/chain lemma with the frame already
collapsed to the ABI + footprint shape.  A caller `obtain`s the framed post
directly; the two `WrRegsAvoidAbi`/`WrChainAvoidAbi` premises are `by decide`
per shape. -/

/-- **The framed block soundness lemma.**  `block_mem_sound` with its register
frame collapsed to the ABI callee shape (via `abiFrame_of_wrRegs`, one `decide`)
and the memory post exposed as the footprint frame (via `memFrame_of_block`).
Every field is the underlying lemma's own; only the two frame clauses are
rewrapped. -/
theorem block_mem_sound_framed (is : List MInstr) (σ : MState) (i u : Nat)
    (pc0 vm : BitVec 64) (L : GRegs) (lds : List (List (BitVec 8)))
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some pc0)
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hL : GHolds σ L)
    (hkeys : KeysOK (keysG L))
    (hfacts : ProgFactsM σ.mem σ.mem L lds is)
    (hwf : BlockOKM pc0 (keysG L) is)
    (hi : i < 2)
    (hAvoid : WrRegsAvoidAbi is) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + is.length⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeLog σ.mem (wlogM is L lds) ∧ σ'.sailOutput = σ.sailOutput ∧
      σ'.regs.get? Register.PC = some (endPCM pc0 is) ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      GHolds σ' (runGM is L lds) ∧
      -- (c) ABI callee frame, free:
      (∀ R, AbiPreserved R = true → σ'.regs.get? R = σ.regs.get? R) ∧
      -- (d) footprint frame, free:
      (∀ a, OutL (wlogM is L lds) a → σ'.mem[a]? = σ.mem[a]?) := by
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', hmi', hGH', hframe⟩ :=
    block_mem_sound is σ i u pc0 vm L lds hG hpc hmi hL hkeys hfacts hwf hi
  exact ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', hmi', hGH',
    abiFrame_of_wrRegs hAvoid hframe, memFrame_of_block hmem'⟩

/-- **The framed chain soundness lemma.**  `bblocks_sound_bt` with its register
frame collapsed to the ABI callee shape (via `abiFrame_of_wrChain`, one
`decide`) and the memory post exposed as the `OutChain` footprint frame.  This
is the reusable "framed variant" of ANY reflected callee chain — the whole
callee-frame + footprint obligation, discharged by two `decide`s at the use
site. -/
theorem bblocks_sound_framed (bs : List BBlock) (σ : MState) (i u : Nat)
    (pc0 vm : BitVec 64) (L : GRegs) (lds : List (List (BitVec 8)))
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some pc0)
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hL : GHolds σ L)
    (hkeys : KeysOK (keysG L))
    (hfacts : ChainFacts σ.mem σ.mem L lds bs)
    (hwf : ChainOK pc0 (keysG L) bs)
    (hi : i < 2)
    (hAvoid : WrChainAvoidAbi bs) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + chainLen bs⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = memChain bs σ.mem L lds ∧ σ'.sailOutput = σ.sailOutput ∧
      σ'.regs.get? Register.PC = some (chainEndPC pc0 L lds bs) ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      GHolds σ' (runChain bs L lds) ∧
      -- (c) ABI callee frame, free:
      (∀ R, AbiPreserved R = true → σ'.regs.get? R = σ.regs.get? R) ∧
      -- (d) footprint frame, free:
      (∀ a, OutChain bs σ.mem L lds a → σ'.mem[a]? = σ.mem[a]?) := by
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', hmi', hGH', hframe⟩ :=
    bblocks_sound_bt bs σ i u pc0 vm L lds hG hpc hmi hL hkeys hfacts hwf hi
  exact ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', hmi', hGH',
    abiFrame_of_wrChain hAvoid hframe, memFrame_of_chain hmem'⟩

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

/-- The memmove-dispatch segment's **ABI callee frame, free** — every
callee-saved register is preserved across the whole 4-block segment.  Derived
from `mv_dispatch_setup_block`'s raw frame clause by `abiFrame_of_wrChain` with
the wrChain-disjointness closed by ONE `decide` (`[15,15,13,13,13]` avoids
`AbiPreserved`), plus the noise disequalities free from `AbiPreserved R`.

Contrast the raw clause (`mv_dispatch_setup_block`, lines 102–104): the same
consumer would otherwise write `hframe R (abiNoise_noiseRegs hR)
(by block_frame_wr [15,15,13,13,13])` at *every* use site. -/
theorem mv_dispatch_setup_abiFramed (σ : MState) (i u : Nat)
    (vm r dst src : BitVec 64) (n : Nat)
    (hn1 : 1 ≤ n) (hn31 : n ≤ 31)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x800069c4#64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx10 : σ.regs.get? Register.x10 = some dst)
    (hx11 : σ.regs.get? Register.x11 = some src)
    (hx12 : σ.regs.get? Register.x12 = some (BitVec.ofNat 64 n))
    (hx1 : σ.regs.get? Register.x1 = some r)
    (hmem : Vsa.Sim.Code.MemmoveLoaded σ.mem)
    (hd : dst.toNat + n ≤ src.toNat)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + 8⟩ ∧ i' < 2 ∧
      σ'.regs.get? Register.PC = some (0x80006a0c#64) ∧
      σ'.regs.get? Register.x15 = some dst ∧
      σ'.regs.get? Register.x13 = some (dst + BitVec.ofNat 64 n) ∧
      -- (c) callee-saved ABI frame across the segment, FREE:
      (∀ R, AbiPreserved R = true → σ'.regs.get? R = σ.regs.get? R) ∧
      -- (d) memory unchanged (this segment's log is empty; the footprint frame
      -- degenerates to full memory equality):
      σ'.mem = σ.mem := by
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', _, _, _, _, ha15, ha13, hmi', hframe⟩ :=
    mv_dispatch_setup_block σ i u vm r dst src n hn1 hn31 hG hpc hmi hx10 hx11 hx12 hx1 hmem hd hi
  -- the WHOLE framed variant, no site threading.  The wrRegs-disjointness of the
  -- written list `[15,15,13,13,13]` from `AbiPreserved` is ONE `decide` (via the
  -- reusable `listAvoidAbi` datum); the noise disequalities are free.
  refine ⟨σ', i', hsteps, hi', hpc', ha15, ha13, ?_, hmem'⟩
  have hAvoid : ∀ nn ∈ ([15, 15, 13, 13, 13] : List Nat), AbiPreserved (gprReg nn) = false := by
    decide
  exact fun R hR => hframe R (noise_ne_abi hR)
    (fun nn hnn => abiPreserved_ne hR (hAvoid nn hnn))

end Vsa.Sim
