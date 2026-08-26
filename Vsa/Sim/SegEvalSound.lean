import Vsa.Sim.SegEval

/-!
# `SegEvalSound` — one bridge from reflected paths to `Machine.Steps`

All instruction execution remains in `bblocks_sound_bt`. This theorem merely
packages its computed result through `SegEvalState`, including the canonical
single write log supplied by `writeLog_evalBlocks_init`.

Timing witness (2026-08-26): `lake build Vsa.Sim.SegEvalSound` completed the
touched target in 6.9s.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState Config Steps)

namespace Vsa.Sim

/-- Soundness of a reflected multi-block path. One `ChainOK` proof checks the
whole concrete path. Per-block semantic facts remain explicit hypotheses. -/
theorem segEval_sound (bs : List BBlock) (σ : MState) (i u : Nat)
    (pc0 vm : BitVec 64) (L : GRegs) (lds : List (List (BitVec 8)))
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some pc0)
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hL : GHolds σ L)
    (hkeys : KeysOK (keysG L))
    (hfacts : ChainFacts σ.mem σ.mem L lds bs)
    (hwf : ChainOK pc0 (keysG L) bs)
    (hi : i < 2) :
    let out := evalBlocks bs (SegEvalState.init L lds)
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + evalBlocksFuel bs⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeLog σ.mem out.log ∧ σ'.sailOutput = σ.sailOutput ∧
      σ'.regs.get? Register.PC = some (evalBlocksPC pc0 (SegEvalState.init L lds) bs) ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      GHolds σ' out.regs ∧
      (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
        (∀ n ∈ wrChain bs, (gprReg n == R) = false) →
        σ'.regs.get? R = σ.regs.get? R) := by
  dsimp only [evalBlocksFuel, evalBlocksPC]
  obtain ⟨σ', i', hs, hi', hG', hmem, hout, hpc', hmi', hregs, hframe⟩ :=
    bblocks_sound_bt bs σ i u pc0 vm L lds hG hpc hmi hL hkeys hfacts hwf hi
  refine ⟨σ', i', hs, hi', hG', ?_, hout, hpc', hmi', ?_, hframe⟩
  · rw [writeLog_evalBlocks_init]
    exact hmem
  · rw [evalBlocks_regs]
    exact hregs

/-- Close a `segEval_sound` goal from named hypotheses and one small kernel
`decide` for the concrete `ChainOK` side condition. -/
macro "seg_eval" : tactic =>
  `(tactic|
    apply segEval_sound <;>
      first | assumption | decide)

example (bs : List BBlock) (σ : MState) (i u : Nat)
    (pc0 vm : BitVec 64) (L : GRegs) (lds : List (List (BitVec 8)))
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some pc0)
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hL : GHolds σ L)
    (hkeys : KeysOK (keysG L))
    (hfacts : ChainFacts σ.mem σ.mem L lds bs)
    (hwf : ChainOK pc0 (keysG L) bs)
    (hi : i < 2) :
    let out := evalBlocks bs (SegEvalState.init L lds)
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + evalBlocksFuel bs⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeLog σ.mem out.log ∧ σ'.sailOutput = σ.sailOutput ∧
      σ'.regs.get? Register.PC = some (evalBlocksPC pc0 (SegEvalState.init L lds) bs) ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      GHolds σ' out.regs ∧
      (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
        (∀ n ∈ wrChain bs, (gprReg n == R) = false) →
        σ'.regs.get? R = σ.regs.get? R) := by
  seg_eval

#print axioms segEval_sound

end Vsa.Sim
