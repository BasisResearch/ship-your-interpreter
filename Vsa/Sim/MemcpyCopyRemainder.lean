import Vsa.Sim.MemcpyCopyBulkRun
import Vsa.Sim.MemcpyCopyWordTail

namespace Vsa.Sim.MemcpyCopy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc Vsa.Logic

/-- Reflected end PC of the remainder entry: `simp` no longer ground-reduces `evalBlocksPC`. -/
private theorem remainderSegPC (L : GRegs) (lds : List (List (BitVec 8))) :
    evalBlocksPC (0x80006bfc#64) (SegEvalState.init L lds) memcpyX6bfcFSeg = 0x80006c08#64 := by
  rw [evalBlocksPC, chainEndPC_eq_bt memcpyX6bfcFSeg _ _ _ (by decide)]
  rfl

/-- Enter the small-word loop after the bulk copy stops. -/
theorem remainderWords {dst src r : BitVec 64} {n i : Nat} {bs : Nat → BitVec 8} {m0 : Mem}
    {before : Config} (h : BulkState dst src r n i bs m0 before)
    (stopped : ¬ i+72 ≤ 8*(n/8)) (remaining : i < 8*(n/8)) :
    ∃ after, Steps before after ∧
      Retained (WordState dst src r n (i/8) (i/8) bs m0) before after := by
  have indexEq : 8*(i/8) = i := by have := h.offset_align; omega
  have wordRemaining : i/8 < n/8 := by omega
  let L := bulkRegs dst src r n i
  have facts : ChainFacts before.σ.mem before.σ.mem L [] memcpyX6bfcFSeg := by
    chain_facts h.loaded with "Vsa.Sim.Code.memcpy_at_"
    change zopz0zKzJ_u (dst + BitVec.ofNat 64 i) (dst + BitVec.ofNat 64 (8*(n/8))) = false
    unfold zopz0zKzJ_u Sail.BitVec.toNatInt
    rw [decide_eq_false_iff_not,
      ptr_toNat dst i (by have := h.regions.dst_hi; omega),
      ptr_toNat dst (8*(n/8)) (by have := h.regions.dst_hi; omega)]
    intro greater
    have := Int.ofNat_le.mp greater
    omega
  obtain ⟨vm, hvm⟩ := h.good.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed memcpyX6bfcFSeg L [] 0x80006bfc#64 vm
    (fun _ => False) AbiPreserved (wordRegs dst src r n (i/8) (i/8)) before
    h.good (by simpa [stopped] using h.pc) hvm ⟨h.a1, h.a4, h.a2, h.a5, h.a7, h.a0, h.ra, trivial⟩
    (by change KeysOK [11,14,12,15,17,10,1]; decide) facts
    (by change ChainOK 0x80006bfc#64 [11,14,12,15,17,10,1] memcpyX6bfcFSeg; decide) h.tick
    (by intro _ _; rfl) (by decide) (by decide) (by
      change some ((src + BitVec.ofNat 64 i) + 0#64) = _ ∧
        some ((dst + BitVec.ofNat 64 i) + 0#64) = _ ∧
        some (dst + BitVec.ofNat 64 (8*(n/8))) = _ ∧ some (src + BitVec.ofNat 64 i) = _ ∧
        some (dst + BitVec.ofNat 64 i) = _ ∧ some (dst + BitVec.ofNat 64 n) = _ ∧
        some dst = _ ∧ some r = _ ∧ True
      simp only [indexEq, BitVec.add_zero, and_self])
  obtain ⟨a3, a5, a2, a1, a4, a7, a0, ra, _⟩ := C.selected_regs
  exact ⟨after, C.steps,
    { output := C.output, frame := C.reg_frame, presence := by rw [C.mem]; exact .refl _
      state := { good := C.good, loaded := by rw [C.mem]; exact h.loaded
                 tick := C.tick, a0 := a0, ra := ra, regions := h.regions
                 bound := by rw [indexEq]; exact h.bound
                 meminv := by rw [C.mem, indexEq]; exact h.meminv
                 pc := by simpa only [wordRemaining, if_true, remainderSegPC] using C.pc
                 a1 := a1, a2 := a2, a3 := a3, a4 := a4, a5 := a5, a7 := a7
                 align := h.align, start_lt := wordRemaining
                 start_le := Nat.le_refl _, word_bound := Nat.le_of_lt wordRemaining } }⟩

/-- Skip the small-word loop when the bulk copy exhausted the whole words. -/
theorem remainderTail {dst src r : BitVec 64} {n i : Nat} {bs : Nat → BitVec 8} {m0 : Mem}
    {before : Config} (h : BulkState dst src r n i bs m0 before)
    (stopped : ¬ i+72 ≤ 8*(n/8)) (done : i = 8*(n/8)) :
    ∃ after, Steps before after ∧ Retained (TailInput dst src r n i bs m0) before after := by
  let L := bulkRegs dst src r n i
  have facts : ChainFacts before.σ.mem before.σ.mem L [] memcpyX6bfcTSeg := by
    chain_facts h.loaded with "Vsa.Sim.Code.memcpy_at_"
    change zopz0zKzJ_u (dst + BitVec.ofNat 64 i) (dst + BitVec.ofNat 64 (8*(n/8))) = true
    simp [done, zopz0zKzJ_u]
  obtain ⟨vm, hvm⟩ := h.good.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed memcpyX6bfcTSeg L [] 0x80006bfc#64 vm
    (fun _ => False) AbiPreserved (byteRegs dst src r n i) before h.good
    (by simpa [stopped] using h.pc) hvm ⟨h.a1, h.a4, h.a2, h.a5, h.a7, h.a0, h.ra, trivial⟩
    (by change KeysOK [11,14,12,15,17,10,1]; decide) facts
    (by change ChainOK 0x80006bfc#64 [11,14,12,15,17,10,1] memcpyX6bfcTSeg; decide) h.tick
    (by intro _ _; rfl) (by decide) (by decide) (by exact ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩)
  obtain ⟨a1, a4, a7, a0, ra, _⟩ := C.selected_regs
  exact ⟨after, C.steps,
    { output := C.output, frame := C.reg_frame, presence := by rw [C.mem]; exact .refl _
      state := { good := C.good, loaded := by rw [C.mem]; exact h.loaded
                 tick := C.tick, a0 := a0, ra := ra, regions := h.regions, bound := h.bound
                 meminv := by rw [C.mem]; exact h.meminv
                 pc := C.pc, a1 := a1, a4 := a4, a7 := a7 } }⟩

/-- Complete the remaining words and bytes after the bulk loop. -/
theorem remainder {dst src r : BitVec 64} {n i : Nat} {bs : Nat → BitVec 8} {m0 : Mem}
    {before : Config} (h : BulkState dst src r n i bs m0 before)
    (stopped : ¬ i+72 ≤ 8*(n/8)) (retAlign : r.toNat % 4 = 0) :
    ∃ after, Steps before after ∧ Retained (Returned dst src r n bs m0) before after := by
  by_cases remaining : i < 8*(n/8)
  · obtain ⟨entered, entrySteps, entryState⟩ := remainderWords h stopped remaining
    obtain ⟨after, copySteps, returned⟩ := wordsReturn entryState.state retAlign
    exact ⟨after, entrySteps.trans copySteps, entryState.then returned⟩
  · have done : i = 8*(n/8) := by have := h.word_bound; omega
    obtain ⟨entered, entrySteps, entryState⟩ := remainderTail h stopped done
    obtain ⟨after, tailSteps, returned⟩ := tail entryState.state retAlign
    exact ⟨after, entrySteps.trans tailSteps, entryState.then returned⟩

/-- Run all bulk iterations, remaining words and bytes, and the actual return. -/
theorem bulkReturn {dst src r : BitVec 64} {n i : Nat} {bs : Nat → BitVec 8} {m0 : Mem}
    {before : Config} (h : BulkState dst src r n i bs m0 before) (retAlign : r.toNat % 4 = 0) :
    ∃ after, Steps before after ∧ Retained (Returned dst src r n bs m0) before after := by
  obtain ⟨copied, copySteps, copiedState⟩ := bulks h
  obtain ⟨j, state, stopped⟩ := copiedState.state
  obtain ⟨after, restSteps, returned⟩ := remainder state stopped retAlign
  exact ⟨after, copySteps.trans restSteps, copiedState.then returned⟩

#print axioms remainder
#print axioms bulkReturn

end Vsa.Sim.MemcpyCopy
