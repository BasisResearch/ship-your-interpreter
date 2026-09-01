import Vsa.Sim.DeriveCaseRow
/-! Probe: `segToTripleFramed` — segToTriple keeping segEval_sound's frame
clause + sailOutput preservation (both currently DISCARDED), which the P1 loop
invariant needs (htif_payload_writes/htif_tohost across the body seg). -/
open LeanRV64DExecutable Vsa Vsa.Sim Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)

namespace Vsa.Sim

theorem segToTripleFramed (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (Q : Config → Prop)
    (hwf : ChainOK pc0 (keysG L) bs)
    (hpost : ∀ (c : Config) (σ' : MState) (i' u' : Nat),
      GoodState σ' → i' < 2 →
      σ'.mem = writeLog m0 (evalBlocks bs (SegEvalState.init L lds)).log →
      σ'.sailOutput = c.σ.sailOutput →
      σ'.regs.get? Register.PC
        = some (evalBlocksPC pc0 (SegEvalState.init L lds) bs) →
      (∃ w, σ'.regs.get? Register.minstret = some w) →
      GHolds σ' (evalBlocks bs (SegEvalState.init L lds)).regs →
      (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
        (∀ n ∈ wrChain bs, (gprReg n == R) = false) →
        σ'.regs.get? R = c.σ.regs.get? R) →
      Q ⟨σ', i', u'⟩) :
    Triple (SegPre bs L lds pc0 m0) Q := by
  intro c hpre
  obtain ⟨hG, hmem, hpc, ⟨vm, hmi⟩, hL, hkeys, hfacts, htick⟩ := hpre
  obtain ⟨σ', i', hs, hi', hG', hmem', hout, hpc', hmi', hregs, hframe⟩ :=
    segEval_sound bs c.σ c.tick c.steps pc0 vm L lds hG hpc hmi hL hkeys hfacts hwf htick
  rw [hmem] at hmem'
  exact ⟨⟨σ', i', c.steps + evalBlocksFuel bs⟩, hs,
    hpost c σ' i' (c.steps + evalBlocksFuel bs) hG' hi' hmem' hout hpc' hmi' hregs hframe⟩

end Vsa.Sim
#print axioms Vsa.Sim.segToTripleFramed
