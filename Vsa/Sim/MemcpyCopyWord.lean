import Vsa.Sim.MemcpyCopyWordMemory
import Vsa.Sim.MemcpyCopyByte

namespace Vsa.Sim.MemcpyCopy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc Vsa.Logic

def wordSeg (more : Bool) : List BBlock :=
  if more then memcpyX6c08TSeg else memcpyX6c08FSeg

def wordRegs (dst src r : BitVec 64) (n start j : Nat) : GRegs :=
  [(13, src + BitVec.ofNat 64 (8*j)), (15, dst + BitVec.ofNat 64 (8*j)),
   (12, dst + BitVec.ofNat 64 (8*(n/8))), (11, src + BitVec.ofNat 64 (8*start)),
   (14, dst + BitVec.ofNat 64 (8*start)), (17, dst + BitVec.ofNat 64 n), (10, dst), (1, r)]

/-- Reflected end PC of the word segment: `simp` no longer ground-reduces `evalBlocksPC`. -/
private theorem wordSegPC (L : GRegs) (lds : List (List (BitVec 8))) (more : Bool) :
    evalBlocksPC (0x80006c08#64) (SegEvalState.init L lds) (wordSeg more)
      = if more then 0x80006c08#64 else 0x80006c1c#64 := by
  cases more
  · rw [evalBlocksPC, chainEndPC_eq_bt (wordSeg false) _ _ _ (by decide)]
    rfl
  · rw [evalBlocksPC, chainEndPC_eq_bt (wordSeg true) _ _ _ (by decide)]
    rfl

/-- Normalize the actual word-store address in the reflected write log. -/
theorem wordMemory (dst src r : BitVec 64) (n start j : Nat) (bytes : List (BitVec 8))
    (m : Mem) (more : Bool) (bound : dst.toNat + 8*j < 2^64) :
    writeLog m (evalBlocks (wordSeg more)
      (SegEvalState.init (wordRegs dst src r n start j) [bytes])).log =
      writeMap8 m (dst.toNat + 8*j) (sdData_val (bytesVal .ld bytes)) := by
  cases more <;>
    change writeMap8 m
      (((dst + BitVec.ofNat 64 (8*j)) + sign_extend (m := 64) (0x008#12)) +
        sign_extend (m := 64) (0xff8#12)).toNat (sdData_val (bytesVal .ld bytes)) = _
  all_goals
    rw [ptr_word_succ]
    change writeMap8 m (sdAddrM8 (dst + BitVec.ofNat 64 (8*(j+1)))).toNat _ = _
    rw [sdAddrM8_word_succ, ptr_toNat dst (8*j) bound]

/-- Execute the word load, increments, store, and branch. -/
theorem word {dst src r : BitVec 64} {n start j : Nat} {bs : Nat → BitVec 8} {m0 : Mem}
    {before : Config} (h : WordState dst src r n start j bs m0 before)
    (remaining : j < n/8) :
    ∃ after, Steps before after ∧
      Retained (WordState dst src r n start (j+1) bs m0) before after := by
  let more := decide (j+1 < n/8)
  let L := wordRegs dst src r n start j
  let bytes := EvalChildArm.wordLds8 before.σ.mem (src.toNat + 8*j)
  have wordBound : 8*j + 8 ≤ n := by omega
  have srcAddr : ((src + BitVec.ofNat 64 (8*j)) + sign_extend (m := 64) (0#12)).toNat =
      src.toNat + 8*j := by
    rw [show sign_extend (m := 64) (0#12) = (0#64) from rfl, BitVec.add_zero]
    exact ptr_toNat src (8*j) (by have := h.regions.src_hi; omega)
  have dstAddr : (((dst + BitVec.ofNat 64 (8*j)) + sign_extend (m := 64) (0x008#12)) +
      sign_extend (m := 64) (0xff8#12)).toNat = dst.toNat + 8*j := by
    rw [ptr_word_succ]
    change (sdAddrM8 (dst + BitVec.ofNat 64 (8*(j+1)))).toNat = _
    rw [sdAddrM8_word_succ]
    exact ptr_toNat dst (8*j) (by have := h.regions.dst_hi; omega)
  have guard : guardB bop.BLTU
      ((dst + BitVec.ofNat 64 (8*j)) + sign_extend (m := 64) (0x008#12))
      (dst + BitVec.ofNat 64 (8*(n/8))) = more := by
    rw [ptr_word_succ]
    change zopz0zI_u (dst + BitVec.ofNat 64 (8*(j+1))) (dst + BitVec.ofNat 64 (8*(n/8))) = _
    unfold zopz0zI_u Sail.BitVec.toNatInt
    rw [ptr_toNat dst (8*(j+1)) (by have := h.regions.dst_hi; omega),
      ptr_toNat dst (8*(n/8)) (by have := h.regions.dst_hi; omega)]
    by_cases next : j+1 < n/8
    · rw [show more = true by simp [more, next], decide_eq_true_iff]
      exact Int.ofNat_lt.mpr (by omega)
    · rw [show more = false by simp [more, next], decide_eq_false_iff_not]
      intro smaller
      have := Int.ofNat_lt.mp smaller
      omega
  have load : MemFacts before.σ.mem L bytes (mkLine 0x80006c08#64 0x0006b803#32) := by
    let addr := ((src + BitVec.ofNat 64 (8*j)) + sign_extend (m := 64) (0#12)).toNat
    change (0x80000000 ≤ addr ∧ addr + 8 ≤ 0x100000000 ∧
      (addr + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ addr)) ∧ LPins8 before.σ.mem addr bytes
    dsimp only [addr]
    rw [srcAddr]
    refine ⟨⟨by have := h.regions.src_lo; omega, by have := h.regions.src_hi; omega,
      by have := h.regions.src_win; omega⟩, ?_⟩
    simp [LPins8, bytes, EvalChildArm.wordLds8]
  have store : 0x80000000 ≤ dst.toNat + 8*j ∧ dst.toNat + 8*j + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ dst.toNat + 8*j ∧ (dst.toNat + 8*j) % 8 = 0 :=
    ⟨by have := h.regions.dst_lo; omega, by have := h.regions.dst_hi; omega,
      by have := h.regions.dst_win; omega, by have := h.align; omega⟩
  have facts : ChainFacts before.σ.mem before.σ.mem L [bytes] (wordSeg more) := by
    cases chosen : more <;> unfold wordSeg <;>
      chain_facts h.loaded with "Vsa.Sim.Code.memcpy_at_"
    all_goals first
      | exact load
      | (let addr := (((dst + BitVec.ofNat 64 (8*j)) + sign_extend (m := 64) (0x008#12)) +
           sign_extend (m := 64) (0xff8#12)).toNat
         change 0x80000000 ≤ addr ∧ addr + 8 ≤ 0x100000000 ∧
           tohostAddr + 16 ≤ addr ∧ addr % 8 = 0
         dsimp only [addr]
         rw [dstAddr]; exact store)
      | exact guard.trans chosen
  obtain ⟨vm, hvm⟩ := h.good.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed (wordSeg more) L [bytes]
    0x80006c08#64 vm (fun a => dst.toNat + 8*j ≤ a ∧ a < dst.toNat + 8*j + 8) AbiPreserved
    (wordRegs dst src r n start (j+1)) before h.good (by simpa [remaining] using h.pc) hvm
    ⟨h.a3, h.a5, h.a2, h.a1, h.a4, h.a7, h.a0, h.ra, trivial⟩
    (by change KeysOK [13,15,12,11,14,17,10,1]; decide) facts
    (by change ChainOK 0x80006c08#64 [13,15,12,11,14,17,10,1] (wordSeg more)
        cases more <;> decide) h.tick
    (by
      intro a outside
      rw [wordMemory dst src r n start j bytes before.σ.mem more
        (by have := h.regions.dst_hi; omega)]
      exact (getElem?_writeMap8_out _ _ _ _ (by omega)).symm)
    (by decide) (by cases more <;> decide) (by
      cases more <;>
        change some ((src + BitVec.ofNat 64 (8*j)) + sign_extend (m := 64) (0x008#12)) = _ ∧
          some ((dst + BitVec.ofNat 64 (8*j)) + sign_extend (m := 64) (0x008#12)) = _ ∧
          some (dst + BitVec.ofNat 64 (8*(n/8))) = _ ∧
          some (src + BitVec.ofNat 64 (8*start)) = _ ∧
          some (dst + BitVec.ofNat 64 (8*start)) = _ ∧
          some (dst + BitVec.ofNat 64 n) = _ ∧ some dst = _ ∧ some r = _ ∧ True
      all_goals simp only [ptr_word_succ, and_self])
  obtain ⟨a3, a5, a2, a1, a4, a7, a0, ra, _⟩ := C.selected_regs
  have mem : after.σ.mem =
      writeMap8 before.σ.mem (dst.toNat + 8*j) (sdData_val (bytesVal .ld bytes)) :=
    C.mem.trans (wordMemory dst src r n start j bytes before.σ.mem more
      (by have := h.regions.dst_hi; omega))
  refine ⟨after, C.steps,
    { output := C.output, frame := C.reg_frame
      presence := by rw [mem]; exact memExtends_writeMap8 _ _ _
      state := { good := C.good, tick := C.tick, a0 := a0, ra := ra
                 regions := h.regions, bound := by omega
                 a1 := a1, a2 := a2, a3 := a3, a4 := a4, a5 := a5, a7 := a7
                 align := h.align, start_lt := h.start_lt
                 start_le := by have := h.start_le; omega, word_bound := by omega
                 meminv := ?_, loaded := ?_, pc := ?_ } }⟩
  · rw [mem]
    exact loadedWord h.loaded wordBound h.regions.code_disjoint
  · rw [mem]
    simpa only [Nat.mul_add, Nat.mul_one] using storeWord h.meminv h.regions.disjoint wordBound
  · have pc := C.pc
    by_cases next : j+1 < n/8
    · simp only [more, next, decide_true] at pc
      simpa only [next, if_true, wordSegPC] using pc
    · simp only [more, next, decide_false] at pc
      simpa only [next, wordSegPC, Bool.false_eq_true, ite_false] using pc

#print axioms wordMemory
#print axioms word

end Vsa.Sim.MemcpyCopy
