import Vsa.Sim.SeqClosureRetResume
import Vsa.Sim.rows.CallClosureBodyExit
import Vsa.Sim.ExecRetEpilogue
import Vsa.Sim.EnvDefSpec4

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (Config)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc

def seqClosureNormalReads (sp body : BitVec 64) (a : Nat) : Prop :=
  (0x80003164 ≤ a ∧ a < 0x80003fe0) ∨
  (sp.toNat ≤ a ∧ a < sp.toNat + 8) ∨
  (body.toNat + 16 ≤ a ∧ a < body.toNat + 20)

/-- The reached final child's saved loop state and immutable read footprint. -/
structure SeqClosureNormalExitCarrier
    (g gExec : (R : Register) → Option (RegisterType R))
    (A : Arena) (SL : StackLayout) (sp aRet body : BitVec 64)
    (index count : Nat) (m0 mCall : Mem) : Prop
    extends SeqClosureRetCarrier g gExec A SL sp aRet m0 mCall where
  indexReg : gExec x8 = some (BitVec.ofNat 64 index)
  last : index + 1 = count
  countBound : count < 2^31
  savedBody : read64 mCall sp.toNat = some body.toNat
  bodyCount : read32 mCall (body.toNat + 16) = some count
  code : Code.Eval_exprLoaded mCall
  readSafe : ∀ a, seqClosureNormalReads sp body a →
    ¬ (SL.lo ≤ a ∧ a < sp.toNat) ∧ ¬ (A.lo ≤ a ∧ a < A.hi) ∧
      ¬ (aRet.toNat ≤ a ∧ a < aRet.toNat + 24)
  spLo : 0x80000000 ≤ sp.toNat
  spHi : sp.toNat + 8 ≤ 0x100000000
  spWin : tohostAddr + 8 ≤ sp.toNat
  spAlign : sp.toNat % 8 = 0
  bodyLo : 0x80000000 ≤ body.toNat
  bodyHi : body.toNat + 20 ≤ 0x100000000
  bodyWin : tohostAddr + 8 ≤ body.toNat + 16
  bodyAlign : body.toNat % 4 = 0

def seqClosureNormalCountBytes (m : Mem) (a : Nat) : List (BitVec 8) :=
  [(m[a]?).getD 0, (m[a+1]?).getD 0, (m[a+2]?).getD 0, (m[a+3]?).getD 0]

theorem seqClosureNormalCount_value (m : Mem) (a count : Nat)
    (hb : count < 2^31) (h : read32 m a = some count) :
    bytesVal .lw (seqClosureNormalCountBytes m a) = BitVec.ofNat 64 count := by
  obtain ⟨b0, b1, b2, b3, h0, h1, h2, h3, hv⟩ := read32_bytes_ed m a count h
  simpa [bytesVal, seqClosureNormalCountBytes, h0, h1, h2, h3] using
    sext_count_ed b0 b1 b2 b3 count hb hv

theorem seqClosureNormal_sext (count : Nat) (hb : count < 2^31) :
    (sign_extend (m := 64) (BitVec.ofNat 32 count) : BitVec 64) =
      BitVec.ofNat 64 count := by
  apply BitVec.eq_of_toNat_eq
  show ((BitVec.ofNat 32 count).signExtend 64).toNat = (BitVec.ofNat 64 count).toNat
  rw [BitVec.toNat_signExtend]
  have hmsb : (BitVec.ofNat 32 count).msb = false := by
    rw [BitVec.msb_eq_decide]
    simp only [decide_eq_false_iff_not, Nat.not_le, BitVec.toNat_ofNat]
    omega
  rw [hmsb, if_neg (by simp), Nat.add_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

def seqClosureNormalLoads (m : Mem) (sp body : BitVec 64) : List (List (BitVec 8)) :=
  [execRetEpilogueWord m sp.toNat, seqClosureNormalCountBytes m (body.toNat + 16)]

theorem seqClosureNormal_load64
    {m : Mem} {L : GRegs} {a : MInstr} (addr : BitVec 64)
    (hlo : 0x80000000 ≤ addr.toNat) (hhi : addr.toNat + 8 ≤ 0x100000000)
    (hwin : tohostAddr + 8 ≤ addr.toNat) (halign : addr.toNat % 8 = 0)
    (hk : a.kind = .ld) (hsrc : srcVal a.rs1 L = addr)
    (himm : (sign_extend (m := 64) a.imm : BitVec 64) = 0#64) :
    MemFacts m L (execRetEpilogueWord m addr.toNat) a := by
  have hea : eaddrM a L = addr := by simp [eaddrM, hsrc, himm]
  unfold MemFacts
  rw [hk, hea]
  exact ⟨⟨hlo, hhi, Or.inr hwin⟩,
    by simp [LPins8, execRetEpilogueWord]⟩

theorem seqClosureNormal_load32
    {m : Mem} {L : GRegs} {a : MInstr} (body : BitVec 64)
    (hlo : 0x80000000 ≤ body.toNat) (hhi : body.toNat + 20 ≤ 0x100000000)
    (hwin : tohostAddr + 8 ≤ body.toNat + 16) (halign : body.toNat % 4 = 0)
    (hk : a.kind = .lw) (hsrc : srcVal a.rs1 L = body)
    (himm : (sign_extend (m := 64) a.imm : BitVec 64) = 16#64) :
    MemFacts m L (seqClosureNormalCountBytes m (body.toNat + 16)) a := by
  have hea : (eaddrM a L).toNat = body.toNat + 16 := by
    rw [eaddrM, hsrc, himm, BitVec.toNat_add]
    change (body.toNat + 16) % 2^64 = body.toNat + 16
    exact Nat.mod_eq_of_lt (by omega)
  unfold MemFacts
  rw [hk, hea]
  exact ⟨⟨by omega, by omega, Or.inr hwin⟩,
    by simp [LPins4, seqClosureNormalCountBytes]⟩

/-- Caller frame and arithmetic facts for the last normal iteration. -/
structure SeqClosureNormalFinalData
    (g gExec : (R : Register) → Option (RegisterType R))
    (A : Arena) (SL : StackLayout) (sp aRet body : BitVec 64)
    (index count : Nat) (m0 mCall : Mem) : Prop
    extends SeqClosureRetCarrier g gExec A SL sp aRet m0 mCall where
  indexReg : gExec x8 = some (BitVec.ofNat 64 index)
  last : index + 1 = count
  countBound : count < 2^31
  spLo : 0x80000000 ≤ sp.toNat
  spHi : sp.toNat + 8 ≤ 0x100000000
  spWin : tohostAddr + 8 ≤ sp.toNat
  spAlign : sp.toNat % 8 = 0
  bodyLo : 0x80000000 ≤ body.toNat
  bodyHi : body.toNat + 20 ≤ 0x100000000
  bodyWin : tohostAddr + 8 ≤ body.toNat + 16
  bodyAlign : body.toNat % 4 = 0

theorem SeqClosureNormalFinalData.facts
    {g gExec : (R : Register) → Option (RegisterType R)}
    {A : Arena} {SL : StackLayout} {sp aRet body : BitVec 64}
    {index count : Nat} {m0 mCall : Mem}
    (h : SeqClosureNormalFinalData g gExec A SL sp aRet body index count m0 mCall)
    {m : Mem} (hc : Code.Eval_exprLoaded m)
    (hsaved : read64 m sp.toNat = some body.toNat)
    (hcount : read32 m (body.toNat + 16) = some count) :
    ChainFacts m m (callClosureBodyExitL 0#64 sp (BitVec.ofNat 64 index))
      (seqClosureNormalLoads m sp body) callClosureBodyExitNormalSeg := by
  have hbody := execRetEpilogueWord_value _ _ _ hsaved
  have hn := seqClosureNormalCount_value _ _ _ h.countBound hcount
  have hinc : BitVec.ofNat 64 index + 1#64 = BitVec.ofNat 64 count := by
    rw [← BitVec.ofNat_add, h.last]
  have hsext := seqClosureNormal_sext count h.countBound
  have hextract : BitVec.extractLsb' 0 32 (BitVec.ofNat 64 count) =
      BitVec.ofNat 32 count := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
    omega
  unfold callClosureBodyExitNormalSeg ChainFacts
  chain_facts hc with "Vsa.Sim.Code.eval_expr_at_"
  · rfl
  · exact seqClosureNormal_load64 sp h.spLo h.spHi h.spWin h.spAlign
      (by decide) rfl (by decide)
  · apply seqClosureNormal_load32 body h.bodyLo h.bodyHi h.bodyWin h.bodyAlign
      (by decide) _ (by decide)
    simpa [srcVal, callClosureBodyExitL, seqClosureNormalLoads, runGM, stepGM,
      stepLdsM, ldsRunM, wvalM, lookupG, eraseG, mkLine, decodeM] using hbody
  · simp [guardB, callClosureBodyExitL,
      seqClosureNormalLoads, runGM, stepGM, stepLdsM, ldsRunM, wvalM, srcVal,
      lookupG, eraseG, mkLine, decodeM, hn,
      show (sign_extend (m := 64) (1#12) : BitVec 64) = 1#64 by decide,
      show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 by decide,
      hinc, Sail.BitVec.extractLsb, BitVec.extractLsb, hextract, hsext,
      zopz0zKzJ_s]

/-- Project the final-iteration geometry from the ordinary carrier. -/
def SeqClosureNormalExitCarrier.finalData
    {g gExec : (R : Register) → Option (RegisterType R)}
    {A : Arena} {SL : StackLayout} {sp aRet body : BitVec 64}
    {index count : Nat} {m0 mCall : Mem}
    (h : SeqClosureNormalExitCarrier g gExec A SL sp aRet body index count m0 mCall) :
    SeqClosureNormalFinalData g gExec A SL sp aRet body index count m0 mCall :=
  { toSeqClosureRetCarrier := h.toSeqClosureRetCarrier
    indexReg := h.indexReg, last := h.last, countBound := h.countBound
    spLo := h.spLo, spHi := h.spHi, spWin := h.spWin, spAlign := h.spAlign
    bodyLo := h.bodyLo, bodyHi := h.bodyHi, bodyWin := h.bodyWin, bodyAlign := h.bodyAlign }

theorem SeqClosureNormalExitCarrier.facts
    {g gExec : (R : Register) → Option (RegisterType R)}
    {A : Arena} {SL : StackLayout} {sp aRet body : BitVec 64}
    {index count : Nat} {m0 mCall : Mem}
    (h : SeqClosureNormalExitCarrier g gExec A SL sp aRet body index count m0 mCall)
    {m : Mem} (hc : Code.Eval_exprLoaded m)
    (hsaved : read64 m sp.toNat = some body.toNat)
    (hcount : read32 m (body.toNat + 16) = some count) :
    ChainFacts m m (callClosureBodyExitL 0#64 sp (BitVec.ofNat 64 index))
      (seqClosureNormalLoads m sp body) callClosureBodyExitNormalSeg :=
  h.finalData.facts hc hsaved hcount

def seqClosureNormalKeep (R : Register) : Bool :=
  AbiPreserved R && !(R == x8)

/-- The final normal route retains the exact child-return memory. -/
structure SeqClosureNormalExitResult
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (phiF phiC : Addr → Nat)
    (nf nc : Nat) (st : Vsa.While.St) (sp aRet : BitVec 64) (m0 childMem : Mem)
    (cfg : Config) : Prop where
  exit : ExecSeqExitI .closureBody g N A SL phiF phiC nf nc st .normal sp aRet m0 cfg
  memory : cfg.σ.mem = childMem

/-- Run the final route from the actual child-return code and saved-word reads. -/
theorem seqClosureNormalExitRun
    {g gExec : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {nf nc : Nat} {st' : Vsa.While.St}
    {sp aRet body : BitVec 64} {index count : Nat} {m0 mCall : Mem}
    (h : SeqClosureNormalFinalData g gExec A SL sp aRet body index count m0 mCall)
    (cfg : Config)
    (hChild : ExecExitD gExec N A SL φf φc nf nc st' .normal sp 0x80003378#64 aRet mCall cfg)
    (hc : Code.Eval_exprLoaded cfg.σ.mem)
    (hb : read64 cfg.σ.mem sp.toNat = some body.toNat)
    (hn : read32 cfg.σ.mem (body.toNat + 16) = some count) :
    ∃ after, Vsa.Machine.Steps cfg after ∧
      SeqClosureNormalExitResult g N A SL φf φc nf nc st' sp aRet m0 cfg.σ.mem after := by
  have h8 := (hChild.1.frame x8 (by decide)).trans h.indexReg
  obtain ⟨vm, hmi⟩ := hChild.1.minstret
  obtain ⟨σ', i', hs, hi, hg, hm, ho, hpc, hmi', _, hframe⟩ :=
    segEval_sound callClosureBodyExitNormalSeg cfg.σ cfg.tick cfg.steps
      0x80003378#64 vm (callClosureBodyExitL 0#64 sp (BitVec.ofNat 64 index))
      (seqClosureNormalLoads cfg.σ.mem sp body)
      hChild.1.good hChild.1.pc hmi ⟨hChild.1.a0, hChild.1.spReg, h8, trivial⟩
      (by change KeysOK [10, 2, 8]; decide) (h.facts hc hb hn)
      (by change ChainOK 0x80003378#64 [10, 2, 8] _; decide) hChild.1.tick
  have hmem : σ'.mem = cfg.σ.mem := by
    simpa +ground [callClosureBodyExitNormalSeg, evalBlocks, evalBlock,
      SegEvalState.init, writeLog, wlogM] using hm
  have hregs := frame_of_wrChain_avoids
    (by decide : ∀ rr ∈ noiseRegs, seqClosureNormalKeep rr = false)
    (by decide : WrChainAvoids seqClosureNormalKeep callClosureBodyExitNormalSeg) hframe
  refine ⟨⟨σ', i', cfg.steps + evalBlocksFuel callClosureBodyExitNormalSeg⟩, hs, ⟨?_, hmem⟩⟩
  exact
    { supported := Or.inl rfl
      good := hg
      tick := hi
      pc := hpc
      status_abi := trivial
      store := by rw [hmem]; exact hChild.1.store
      out := by simpa [OutRepr, Vsa.Machine.output, ho] using hChild.1.out
      retval := by intro v hv; cases hv
      mem_frame := by
        intro a hstack hArena
        rw [hmem]
        have hsp := h.spLe
        have hret := h.retInStack
        rcases hChild.1.memFrame a
            (by intro ha; exact hstack ⟨ha.1, by omega⟩) hArena with hr | heq
        · exact False.elim (hstack ⟨by omega, by omega⟩)
        · exact heq.trans (h.memFrame a hstack hArena)
      stack_frame := by
        rw [hmem]
        exact h.highStack.trans (closureBodyStackFrame_of_execExitD h.childFrame hChild)
      mem_extends := by rw [hmem]; exact h.memExtends.trans hChild.2.1
      store_survives := by rw [hmem]; exact hChild.2.2
      frame := by
        intro R hR
        exact (hregs R (by simp [seqClosureNormalKeep, hR.1.1, hR.2])).trans
          ((hChild.1.frame R hR.1).trans (h.frame R hR))
      minstret := hmi' }


/-- Execute the reflected final-iteration route and retain the child's exact
store witnesses, output, and caller frame at the normal sequence boundary. -/
theorem seqClosureNormalExitResume
    {g gExec : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {nf nc : Nat} {st' : Vsa.While.St}
    {sp aRet body : BitVec 64} {index count : Nat} {m0 mCall : Mem}
    (h : SeqClosureNormalExitCarrier g gExec A SL sp aRet body index count m0 mCall) :
    Triple
      (ExecExitD gExec N A SL φf φc nf nc st' .normal
        sp 0x80003378#64 aRet mCall)
      (ExecSeqExitI .closureBody g N A SL φf φc nf nc
        st' .normal sp aRet m0) := by
  intro cfg hChild
  have hag : AgreeP (seqClosureNormalReads sp body) mCall cfg.σ.mem := by
    intro a ha
    obtain ⟨hs, hA, hr⟩ := h.readSafe a ha
    exact ((hChild.1.memFrame a hs hA).resolve_left hr).symm
  have hc := loaded_eval_expr_agreeP mCall cfg.σ.mem
    (fun a ha => hag a (Or.inl ha)) h.code
  have hb : read64 cfg.σ.mem sp.toNat = some body.toNat := by
    rw [← read64_agreeP hag (fun k hk => Or.inr (Or.inl ⟨by omega, by omega⟩))]
    exact h.savedBody
  have hn : read32 cfg.σ.mem (body.toNat + 16) = some count := by
    rw [← read32_agreeP hag (fun k hk => Or.inr (Or.inr ⟨by omega, by omega⟩))]
    exact h.bodyCount
  obtain ⟨after, steps, result⟩ := seqClosureNormalExitRun h.finalData cfg hChild hc hb hn
  exact ⟨after, steps, result.exit⟩

#print axioms SeqClosureNormalFinalData.facts
#print axioms SeqClosureNormalExitCarrier.finalData
#print axioms seqClosureNormalExitRun
#print axioms SeqClosureNormalExitCarrier.facts
#print axioms seqClosureNormalExitResume

/-- The last normal child reaches the exact empty recursive sequence entry. -/
theorem seqClosureNormalFinalStep
    {g gExec : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st st' stFin : Vsa.While.St} {d : Nat} {env : Addr}
    {sp aRet body : BitVec 64} {index count : Nat} {m0 mCall : Mem}
    (h : SeqClosureNormalExitCarrier g gExec A SL sp aRet body index count m0 mCall) :
    Triple
      (ExecExitD gExec N A SL φf φc st.store.frames.size st.store.closures.size
        st' .normal sp 0x80003378#64 aRet mCall)
      (ExecSeqStepPostI .closureBody g N A SL φf φc st st' stFin d env []
        sp aRet m0 .normal) :=
  (seqClosureNormalExitResume h).rmap fun _ hExit =>
    execSeqNormalStepPostI_nil_of_exit hExit

#print axioms seqClosureNormalFinalStep

end Vsa.Sim
