import Vsa.Sim.ClosureCallPrefixData

namespace Vsa.Sim.ClosureCallPrefix

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

/-- A total word is pinned in the reached memory by its byte-window frame. -/
private theorem load64Facts {m m' : Mem} {L : GRegs} {a : MInstr} {addr : Nat}
    (kind : a.kind = .ld) (address : (eaddrM a L).toNat = addr)
    (lo : 0x80000000 ≤ addr) (hi : addr + 8 ≤ 0x100000000)
    (htif : addr + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ addr)
    (agree : ∀ j, j < 8 → m'[addr + j]? = m[addr + j]?) :
    MemFacts m' L (EvalChildArm.wordLds8 m addr) a := by
  have zero := agree 0 (by decide)
  simp only [Nat.add_zero] at zero
  simp only [MemFacts, kind, address]
  exact ⟨⟨lo, hi, htif⟩, by simp [LPins8, EvalChildArm.wordLds8, agree, zero]⟩

private theorem load32Facts {m m' : Mem} {L : GRegs} {a : MInstr} {addr : Nat}
    (kind : a.kind = .lw) (address : (eaddrM a L).toNat = addr)
    (lo : 0x80000000 ≤ addr) (hi : addr + 4 ≤ 0x100000000)
    (htif : addr + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ addr)
    (agree : ∀ j, j < 4 → m'[addr + j]? = m[addr + j]?) :
    MemFacts m' L (wordLds4 m addr) a := by
  have zero := agree 0 (by decide)
  simp only [Nat.add_zero] at zero
  simp only [MemFacts, kind, address]
  exact ⟨⟨lo, hi, htif⟩, by simp [LPins4, wordLds4, agree, zero]⟩

private theorem storeFacts {sp call object fn interp : BitVec 64}
    (G : Geometry sp call object fn interp) {m : Mem} {L : GRegs} {a : MInstr}
    (bs : List (BitVec 8)) (off : Nat) (kind : a.kind = .sd)
    (address : (eaddrM a L).toNat = sp.toNat + off)
    (bound : off + 8 ≤ 1056) (aligned : off % 8 = 0) : MemFacts m L bs a := by
  apply memFacts_sd_frame m L a bs kind
  · rw [address]; have := G.stackLo; omega
  · rw [address]; have := G.stackHi; omega
  · rw [address]; have := G.stackHtif; omega
  · rw [address, Nat.add_mod, G.stackAlign, aligned]

/-- Depth increment and captured-environment staging from the actual third block. -/
private theorem tailFacts (m : Mem) (sp call object fn interp a3 saved5 saved3 : BitVec 64)
    (count depth : Nat) (G : Geometry sp call object fn interp)
    (h : Reads m sp object fn interp count depth) (code : Code.Eval_exprLoaded m) :
    ChainFacts m
      (memChain (callClosureDispatchStageSeg.take 3) m
        (callClosureDispatchStageL sp call a3 (BitVec.ofNat 64 count) interp saved5 saved3)
        (loads m sp call object fn interp))
      (runChain (callClosureDispatchStageSeg.take 3)
        (callClosureDispatchStageL sp call a3 (BitVec.ofNat 64 count) interp saved5 saved3)
        (loads m sp call object fn interp))
      ((loads m sp call object fn interp).drop 7)
      (callClosureDispatchStageSeg.drop 3) := by
  have payload := EvalChildArm.bytesVal_ld_wordLds m (sp.toNat + 104) object h.objectRead
  have node := EvalChildArm.bytesVal_ld_wordLds m object.toNat fn h.nodeRead
  have kind := bytesVal_lw_wordLds4 m (sp.toNat + 96) 4 (by decide) h.kind
  have arity := bytesVal_lw_wordLds4 m (fn.toNat + 24) count (by have := h.countBound; omega) h.countRead
  have depthValue := bytesVal_lw_wordLds4 m (interp.toNat + 8) depth (by have := h.depthBound; omega) h.depthRead
  have increment := addiw1_sn3 depth (by have := h.depthBound; omega)
  have callAddr : (call + 4#64).toNat = call.toNat + 4 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := G.callHi; change call.toNat + 4 < 2^64; omega)]
    rfl
  have fnAddr : (fn + 24#64).toNat = fn.toNat + 24 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := G.fnHi; change fn.toNat + 24 < 2^64; omega)]
    rfl
  have objectAddr : (object + 8#64).toNat = object.toNat + 8 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := G.objectHi; change object.toNat + 8 < 2^64; omega)]
    rfl
  have stack120 := G.stackAddr 120 (by decide)
  have stack128 := G.stackAddr 128 (by decide)
  have stack136 := G.stackAddr 136 (by decide)
  have stack1032 := G.stackAddr 1032 (by decide)
  have stack1048 := G.stackAddr 1048 (by decide)
  simp [callClosureDispatchStageSeg, List.take, List.drop, memChain, runChain,
    callClosureDispatchStageL, loads, wlogM, wentryM, widthOfM,
    runGM, stepGM, stepLdsM, ldsRunM, wvalM, srcVal, lookupG, eraseG,
    mkLine, decodeM, eaddrM]
  chain_facts code with "Vsa.Sim.Code.eval_expr_at_"
  · apply load32Facts rfl (by exact G.interpAddr)
      (by have := G.stackLo; have := G.interpAbove; omega) G.interpHi
      (Or.inr (by have := G.stackHtif; have := G.interpAbove; omega))
    intro j hj
    change (writeMap8 (writeMap8 (writeMap8 (writeMap8 m (sp + 120#64).toNat _)
      (sp + 128#64).toNat _) (sp + 136#64).toNat _) (sp + 1032#64).toNat _)[interp.toNat + 8 + j]? = _
    rw [stack120, stack128, stack136, stack1032]
    have := G.interpAbove
    simp (disch := omega) only [getElem_writeMap8_disjoint]
  · change 0x80000000 ≤ (interp + 8#64).toNat ∧
      (interp + 8#64).toNat + 4 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (interp + 8#64).toNat ∧ (interp + 8#64).toNat % 4 = 0
    rw [G.interpAddr]
    have := G.stackLo; have := G.stackHtif; have := G.interpAbove
    exact ⟨by omega, G.interpHi, by omega, by have := G.interpAlign; omega⟩
  · exact storeFacts G _ 1048 rfl stack1048 (by decide) (by decide)
  · change guardB bop.BLT 1000#64 (sign_extend (m := 64) (Sail.BitVec.extractLsb
      (bytesVal .lw (wordLds4 m (interp.toNat + 8)) + sign_extend (m := 64) (1#12)) 31 0)) = false
    rw [depthValue, increment]
    have signed : (BitVec.ofNat 64 (depth + 1)).toInt = ((depth + 1 : Nat) : Int) := by
      rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by have := h.depthBound; omega),
        if_pos (by have := h.depthBound; omega)]
    unfold guardB zopz0zI_s
    rw [signed]
    change decide ((1000 : Int) < ↑(depth + 1)) = false
    simp only [decide_eq_false_iff_not]
    have := h.depthBound; omega
  · apply load64Facts rfl
      (by change (bytesVal .ld (EvalChildArm.wordLds8 m (sp.toNat + 104)) + 8#64).toNat = object.toNat + 8
          rw [payload]; exact objectAddr)
      (by have := G.objectLo; omega) G.objectHi (by have := G.objectHtif; omega)
    intro j hj
    change (writeMap8 (writeMap4 (writeMap8 (writeMap8 (writeMap8 (writeMap8 m
      (sp + 120#64).toNat _) (sp + 128#64).toNat _) (sp + 136#64).toNat _)
      (sp + 1032#64).toNat _) (interp + 8#64).toNat _)
      (sp + 1048#64).toNat _)[object.toNat + 8 + j]? = _
    rw [stack120, stack128, stack136, stack1032, stack1048, G.interpAddr]
    have := G.objectOff; have := G.objectInterp
    simp (disch := omega) only [getElem_writeMap8_disjoint, getElem_writeMap4_disjoint]
  · exact storeFacts G _ 0 rfl (by change (sp + 0#64).toNat = sp.toNat + 0; simp)
      (by decide) (by decide)

/-- Semantic closure reads discharge all four dispatch guards. -/
theorem facts (m : Mem) (sp call object fn interp a3 saved5 saved3 : BitVec 64)
    (count depth : Nat) (G : Geometry sp call object fn interp)
    (h : Reads m sp object fn interp count depth) (code : Code.Eval_exprLoaded m) :
    ChainFacts m m (callClosureDispatchStageL sp call a3 (BitVec.ofNat 64 count) interp saved5 saved3)
      (loads m sp call object fn interp) callClosureDispatchStageSeg := by
  have payload := EvalChildArm.bytesVal_ld_wordLds m (sp.toNat + 104) object h.objectRead
  have node := EvalChildArm.bytesVal_ld_wordLds m object.toNat fn h.nodeRead
  have kind := bytesVal_lw_wordLds4 m (sp.toNat + 96) 4 (by decide) h.kind
  have arity := bytesVal_lw_wordLds4 m (fn.toNat + 24) count (by have := h.countBound; omega) h.countRead
  have depthValue := bytesVal_lw_wordLds4 m (interp.toNat + 8) depth (by have := h.depthBound; omega) h.depthRead
  have increment := addiw1_sn3 depth (by have := h.depthBound; omega)
  have callAddr : (call + 4#64).toNat = call.toNat + 4 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := G.callHi; change call.toNat + 4 < 2^64; omega)]
    rfl
  have fnAddr : (fn + 24#64).toNat = fn.toNat + 24 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := G.fnHi; change fn.toNat + 24 < 2^64; omega)]
    rfl
  have objectAddr : (object + 8#64).toNat = object.toNat + 8 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := G.objectHi; change object.toNat + 8 < 2^64; omega)]
    rfl
  have stack120 := G.stackAddr 120 (by decide)
  have stack128 := G.stackAddr 128 (by decide)
  have stack136 := G.stackAddr 136 (by decide)
  have stack1032 := G.stackAddr 1032 (by decide)
  have stack1048 := G.stackAddr 1048 (by decide)
  refine ⟨?_, ?_, ?_, tailFacts m sp call object fn interp a3 saved5 saved3 count depth G h code⟩
  all_goals chain_facts code with "Vsa.Sim.Code.eval_expr_at_"
  · apply load64Facts rfl (by exact G.stackAddr 96 (by decide))
      (by have := G.stackLo; omega) (by have := G.stackHi; omega)
      (Or.inr (by have := G.stackHtif; omega))
    intro j _; rfl
  · apply load64Facts rfl (by exact G.stackAddr 104 (by decide))
      (by have := G.stackLo; omega) (by have := G.stackHi; omega)
      (Or.inr (by have := G.stackHtif; omega))
    intro j _; rfl
  · apply load64Facts rfl (by exact G.stackAddr 112 (by decide))
      (by have := G.stackLo; omega) (by have := G.stackHi; omega)
      (Or.inr (by have := G.stackHtif; omega))
    intro j _; rfl
  · apply load32Facts rfl (by exact callAddr) G.callLo G.callHi G.callHtif
    intro j _; rfl
  · exact storeFacts G _ 120 rfl stack120 (by decide) (by decide)
  · apply load32Facts rfl (by exact G.stackAddr 96 (by decide))
      (by have := G.stackLo; omega) (by have := G.stackHi; omega)
      (Or.inr (by have := G.stackHtif; omega))
    intro j hj
    change (writeMap8 m (sp + 120#64).toNat _)[sp.toNat + 96 + j]? = _
    rw [stack120, getElem_writeMap8_disjoint _ _ _ _ (by omega)]
  · exact storeFacts G _ 128 rfl stack128 (by decide) (by decide)
  · exact storeFacts G _ 136 rfl stack136 (by decide) (by decide)
  · change guardB bop.BEQ (bytesVal .lw (wordLds4 m (sp.toNat + 96))) 5#64 = false
    rw [kind]; decide
  · change guardB bop.BNE (bytesVal .lw (wordLds4 m (sp.toNat + 96))) 4#64 = false
    rw [kind]; decide
  · apply load64Facts rfl
      (by change (bytesVal .ld (EvalChildArm.wordLds8 m (sp.toNat + 104)) + 0#64).toNat = object.toNat
          rw [payload, BitVec.add_zero])
      G.objectLo (by have := G.objectHi; omega) (by have := G.objectHtif; omega)
    intro j hj
    change (writeMap8 (writeMap8 (writeMap8 m (sp + 120#64).toNat _)
      (sp + 128#64).toNat _) (sp + 136#64).toNat _)[object.toNat + j]? = _
    rw [stack120, stack128, stack136]
    have := G.objectOff
    simp (disch := omega) only [getElem_writeMap8_disjoint]
  · exact storeFacts G _ 1032 rfl stack1032 (by decide) (by decide)
  · apply load32Facts rfl
      (by change (bytesVal .ld (EvalChildArm.wordLds8 m object.toNat) + 24#64).toNat = fn.toNat + 24
          rw [node]; exact fnAddr)
      G.fnLo G.fnHi G.fnHtif
    intro j hj
    change (writeMap8 (writeMap8 (writeMap8 (writeMap8 m (sp + 120#64).toNat _)
      (sp + 128#64).toNat _) (sp + 136#64).toNat _) (sp + 1032#64).toNat _)[fn.toNat + 24 + j]? = _
    rw [stack120, stack128, stack136, stack1032]
    have := G.fnOff
    simp (disch := omega) only [getElem_writeMap8_disjoint]
  · change guardB bop.BNE (BitVec.ofNat 64 count) (bytesVal .lw (wordLds4 m (fn.toNat + 24))) = false
    rw [arity]
    simp [guardB]

end Vsa.Sim.ClosureCallPrefix
