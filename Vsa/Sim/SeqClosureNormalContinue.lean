import Vsa.Sim.SeqClosureNormalExitResume

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (Config)
open Vsa.MemRepr Vsa.Alloc

/- The same body-exit route with the final BGE not taken. -/
#derive_case seqClosureNormalContinueSeg chain
  []
    terminator ⟨0x80003378#64, 0xfc0504e3#32, 0xe3#8, 0x04#8, 0x05#8, 0xfc#8,
      .br bop.BEQ true, 10, 0, 0x1FC8#13, 0#21, 0#12⟩ ;;
  [(0x80003340#64, 0x00013803#32),
   (0x80003344#64, 0x00140413#32),
   (0x80003348#64, 0x0004079b#32),
   (0x8000334c#64, 0x01082703#32)]
    terminator ⟨0x80003350#64, 0x60e7d263#32, 0x63#8, 0xd2#8, 0xe7#8, 0x60#8,
      .br bop.BGE false, 15, 14, 0x0604#13, 0#21, 0#12⟩

/-- Concrete inputs after a normally returning child with a nonempty suffix. -/
structure SeqClosureNormalContinuePre (sp body : BitVec 64)
    (index count : Nat) (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? PC = some 0x80003378#64
  minstret : ∃ v, cfg.σ.regs.get? Register.minstret = some v
  status : cfg.σ.regs.get? x10 = some 0#64
  spReg : cfg.σ.regs.get? x2 = some sp
  indexReg : cfg.σ.regs.get? x8 = some (BitVec.ofNat 64 index)
  more : index + 1 < count
  countBound : count < 2^31
  savedBody : read64 cfg.σ.mem sp.toNat = some body.toNat
  bodyCount : read32 cfg.σ.mem (body.toNat + 16) = some count
  code : Code.Eval_exprLoaded cfg.σ.mem
  spLo : 0x80000000 ≤ sp.toNat
  spHi : sp.toNat + 8 ≤ 0x100000000
  spWin : tohostAddr + 8 ≤ sp.toNat
  spAlign : sp.toNat % 8 = 0
  bodyLo : 0x80000000 ≤ body.toNat
  bodyHi : body.toNat + 20 ≤ 0x100000000
  bodyWin : tohostAddr + 8 ≤ body.toNat + 16
  bodyAlign : body.toNat % 4 = 0

private theorem seqClosureNormalContinue_guard (index count : Nat)
    (hmore : index + 1 < count) (hbound : count < 2^31) :
    zopz0zKzJ_s (BitVec.ofNat 64 (index + 1)) (BitVec.ofNat 64 count) = false := by
  have hti (n : Nat) (hb : n < 2^31) : (BitVec.ofNat 64 n).toInt = (n : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), if_pos (by omega)]
  unfold zopz0zKzJ_s
  rw [hti count hbound, hti (index + 1) (by omega)]
  exact decide_eq_false (by omega)

theorem SeqClosureNormalContinuePre.facts
    {sp body : BitVec 64} {index count : Nat} {cfg : Config}
    (h : SeqClosureNormalContinuePre sp body index count cfg) :
    ChainFacts cfg.σ.mem cfg.σ.mem
      (callClosureBodyExitL 0#64 sp (BitVec.ofNat 64 index))
      (seqClosureNormalLoads cfg.σ.mem sp body) seqClosureNormalContinueSeg := by
  have hbody := execRetEpilogueWord_value _ _ _ h.savedBody
  have hn := seqClosureNormalCount_value _ _ _ h.countBound h.bodyCount
  have hinc : BitVec.ofNat 64 index + 1#64 = BitVec.ofNat 64 (index + 1) := by
    rw [← BitVec.ofNat_add]
  have hsext := seqClosureNormal_sext (index + 1)
    (Nat.lt_trans h.more h.countBound)
  have hextract : BitVec.extractLsb' 0 32 (BitVec.ofNat 64 (index + 1)) =
      BitVec.ofNat 32 (index + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
    omega
  unfold seqClosureNormalContinueSeg ChainFacts
  chain_facts h.code with "Vsa.Sim.Code.eval_expr_at_"
  · rfl
  · exact seqClosureNormal_load64 sp h.spLo h.spHi h.spWin h.spAlign
      (by decide) rfl (by decide)
  · apply seqClosureNormal_load32 body h.bodyLo h.bodyHi h.bodyWin h.bodyAlign
      (by decide) _ (by decide)
    simpa [srcVal, callClosureBodyExitL, seqClosureNormalLoads, runGM, stepGM,
      stepLdsM, ldsRunM, wvalM, lookupG, eraseG, mkLine, decodeM] using hbody
  · simpa [guardB, callClosureBodyExitL, seqClosureNormalLoads, runGM, stepGM,
      stepLdsM, ldsRunM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, hn,
      show (sign_extend (m := 64) (1#12) : BitVec 64) = 1#64 by decide,
      show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 by decide,
      hinc, Sail.BitVec.extractLsb, BitVec.extractLsb, hextract, hsext] using
      seqClosureNormalContinue_guard index count h.more h.countBound

def seqClosureNormalContinueEffect : FrameEffect where
  regs := fun R => seqClosureNormalKeep R = true
  mem := fun _ => True
  output := True

/-- Reached machine state before the next statement's argument setup. -/
structure SeqClosureNormalContinuePost (sp body : BitVec 64) (index : Nat)
    (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? PC = some 0x80003354#64
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  spReg : after.σ.regs.get? x2 = some sp
  indexReg : after.σ.regs.get? x8 = some (BitVec.ofNat 64 (index + 1))
  bodyReg : after.σ.regs.get? x16 = some body
  mem : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput

theorem seqClosureNormalContinue_run
    {sp body : BitVec 64} {index count : Nat} {cfg : Config}
    (h : SeqClosureNormalContinuePre sp body index count cfg) :
    ∃ cfg', SeqClosureNormalContinuePost sp body index cfg cfg' ∧
      FramedSteps seqClosureNormalContinueEffect cfg cfg' := by
  obtain ⟨vm, hmi⟩ := h.minstret
  obtain ⟨σ', i', hs, hi, hg, hm, ho, hpc, hmi', hregs, hframe⟩ :=
    segEval_sound seqClosureNormalContinueSeg cfg.σ cfg.tick cfg.steps
      0x80003378#64 vm (callClosureBodyExitL 0#64 sp (BitVec.ofNat 64 index))
      (seqClosureNormalLoads cfg.σ.mem sp body)
      h.good h.pc hmi ⟨h.status, h.spReg, h.indexReg, trivial⟩
      (by change KeysOK [10, 2, 8]; decide) h.facts
      (by change ChainOK 0x80003378#64 [10, 2, 8] _; decide) h.tick
  have hbody := execRetEpilogueWord_value _ _ _ h.savedBody
  have hmem : σ'.mem = cfg.σ.mem := by
    simpa +ground [seqClosureNormalContinueSeg, evalBlocks, evalBlock, SegEvalState.init,
      writeLog, wlogM] using hm
  have reg (n : Nat) (v : BitVec 64)
      (hp : lookupG n (evalBlocks seqClosureNormalContinueSeg (SegEvalState.init
        (callClosureBodyExitL 0#64 sp (BitVec.ofNat 64 index))
        (seqClosureNormalLoads cfg.σ.mem sp body))).regs = some v) :
      gprGet σ' n = some v := gholds_lookup _ hregs hp
  have selected : GHolds σ' [(2, sp), (8, BitVec.ofNat 64 (index + 1)), (16, body)] := by
    repeat' apply And.intro
    all_goals first
      | trivial
      | apply reg
        simp [seqClosureNormalContinueSeg, evalBlocks, evalBlock, SegEvalState.init,
          callClosureBodyExitL, seqClosureNormalLoads, runGM, stepGM, stepLdsM,
          ldsRunM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, hbody,
          show (sign_extend (m := 64) (1#12) : BitVec 64) = 1#64 by decide,
          BitVec.ofNat_add]
  obtain ⟨hsp, hindex, hbody', _⟩ := selected
  let cfg' : Config := ⟨σ', i', cfg.steps + evalBlocksFuel seqClosureNormalContinueSeg⟩
  refine ⟨cfg', ⟨hg, hi, hpc, hmi', hsp, hindex, hbody', hmem, ho⟩, hs, ?_⟩
  exact
    { regs := ⟨frame_of_wrChain_avoids
        (by decide : ∀ rr ∈ noiseRegs, seqClosureNormalKeep rr = false)
        (by decide : WrChainAvoids seqClosureNormalKeep seqClosureNormalContinueSeg) hframe⟩
      mem := fun a _ => congrArg (fun m : Mem => m[a]?) hmem
      output := fun _ => ho }

#print axioms SeqClosureNormalContinuePre.facts
#print axioms seqClosureNormalContinue_run

end Vsa.Sim
