import Vsa.Sim.MemcpyCopyLengthTest
import Vsa.Sim.MemcpyCopyRemainder

namespace Vsa.Sim.MemcpyCopy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc Vsa.Logic

#derive_case lengthSmallSeg chain
  []
    terminator ⟨0x80006bdc#64, 0x06061263#32, 0x63#8, 0x12#8, 0x06#8, 0x06#8,
      .br bop.BNE true, 12, 0, 0x0064#13, 0#21, 0#12⟩

#derive_case lengthLargeSeg chain
  []
    terminator ⟨0x80006bdc#64, 0x06061263#32, 0x63#8, 0x12#8, 0x06#8, 0x06#8,
      .br bop.BNE false, 12, 0, 0x0064#13, 0#21, 0#12⟩

/-- Short copies take the binary's common byte path. -/
theorem smallEntry {dst src r : BitVec 64} {n : Nat} {bs : Nat → BitVec 8} {m0 : Mem}
    {before : Config} (h : TestedInput dst src r n bs m0 before) (small : n < 8) :
    ∃ after, Steps before after ∧ Retained (ByteInput dst src r n bs m0) before after := by
  let L : GRegs := [(12, lengthResult n), (10, dst), (11, src), (17, dst + BitVec.ofNat 64 n), (1, r)]
  have facts : ChainFacts before.σ.mem before.σ.mem L [] lengthSmallSeg := by
    chain_facts h.loaded with "Vsa.Sim.Code.memcpy_at_"
    exact (sltiu8_ne_zero_iff (BitVec.ofNat 64 n)).mpr (by
      rw [a2_ofNat_toNat n (by omega)]; exact small)
  obtain ⟨vm, hvm⟩ := h.good.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed lengthSmallSeg L [] 0x80006bdc#64 vm
    (fun _ => False) AbiPreserved [(10, dst), (11, src), (17, dst + BitVec.ofNat 64 n), (1, r)]
    before h.good h.pc hvm ⟨h.a2, h.a0, h.a1, h.a7, h.ra, trivial⟩
    (by change KeysOK [12,10,11,17,1]; decide) facts
    (by change ChainOK 0x80006bdc#64 [12,10,11,17,1] lengthSmallSeg; decide) h.tick
    (by intro _ _; rfl) (by decide) (by decide) (by exact ⟨rfl, rfl, rfl, rfl, trivial⟩)
  obtain ⟨a0, a1, a7, ra, _⟩ := C.selected_regs
  exact ⟨after, C.steps,
    { output := C.output, frame := C.reg_frame, presence := by rw [C.mem]; exact .refl _
      state := { good := C.good, loaded := by rw [C.mem]; exact h.loaded
                 tick := C.tick, a0 := a0, ra := ra, regions := h.regions, bound := h.bound
                 meminv := by rw [C.mem]; exact h.meminv
                 pc := C.pc, a1 := a1, a7 := a7, positive := h.positive } }⟩

def largeEntrySeg (bulk : Bool) : List BBlock :=
  lengthLargeSeg ++ memcpyX6be0FSeg ++ if bulk then memcpyX6becTSeg else memcpyX6becFSeg

/-- Reflected end PC of the aligned entry: `simp` no longer ground-reduces `evalBlocksPC`. -/
private theorem largeEntrySegPC (L : GRegs) (lds : List (List (BitVec 8))) (bulk : Bool) :
    evalBlocksPC (0x80006bdc#64) (SegEvalState.init L lds) (largeEntrySeg bulk)
      = if bulk then 0x80006c60#64 else 0x80006bfc#64 := by
  cases bulk
  · rw [evalBlocksPC, chainEndPC_eq_bt (largeEntrySeg false) _ _ _ (by decide)]
    rfl
  · rw [evalBlocksPC, chainEndPC_eq_bt (largeEntrySeg true) _ _ _ (by decide)]
    rfl

/-- The aligned destination enters the bulk or small-word route selected by the binary. -/
theorem largeEntry {dst src r : BitVec 64} {n : Nat} {bs : Nat → BitVec 8} {m0 : Mem}
    {before : Config} (h : TestedInput dst src r n bs m0 before)
    (large : 8 ≤ n) (align : dst.toNat % 8 = 0) :
    ∃ after, Steps before after ∧ Retained (BulkState dst src r n 0 bs m0) before after := by
  let more := decide (72 ≤ 8*(n/8))
  let L : GRegs := [(12, lengthResult n), (10, dst), (11, src), (17, dst + BitVec.ofNat 64 n), (1, r)]
  have sizeNat : (BitVec.ofNat 64 n).toNat = n :=
    a2_ofNat_toNat n (by have := h.regions.dst_hi; omega)
  have mask := andneg8_dst_span dst n align (by have := h.regions.dst_hi; omega)
  have branch : guardB bop.BLT ((0#64) + sign_extend (m := 64) (0x040#12))
      (((dst + BitVec.ofNat 64 n) &&& sign_extend (m := 64) (0xff8#12)) - (dst + 0#64)) = more := by
    rw [mask, BitVec.add_zero, sub_base_span]
    have signed : (BitVec.ofNat 64 (8*(n/8))).toInt = (8*(n/8) : Nat) := by
      rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by have := h.regions.dst_hi; omega), if_pos (by have := h.regions.dst_hi; omega)]
    change decide ((64#64).toInt < (BitVec.ofNat 64 (8*(n/8))).toInt) = _
    rw [signed]
    change decide ((64 : Int) < (8*(n/8) : Nat)) = _
    simp only [more, decide_eq_decide]
    omega
  have facts : ChainFacts before.σ.mem before.σ.mem L [] (largeEntrySeg more) := by
    cases chosen : more <;> unfold largeEntrySeg <;>
      chain_facts h.loaded with "Vsa.Sim.Code.memcpy_at_"
    all_goals first
      | exact sltiu8_ge_false (BitVec.ofNat 64 n) (by rw [sizeNat]; exact large)
      | exact and7_eq_zero_false dst align
      | exact branch.trans chosen
  obtain ⟨vm, hvm⟩ := h.good.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed (largeEntrySeg more) L [] 0x80006bdc#64 vm
    (fun _ => False) AbiPreserved (bulkRegs dst src r n 0) before h.good h.pc hvm
    ⟨h.a2, h.a0, h.a1, h.a7, h.ra, trivial⟩ (by change KeysOK [12,10,11,17,1]; decide) facts
    (by change ChainOK 0x80006bdc#64 [12,10,11,17,1] (largeEntrySeg more)
        cases more <;> decide) h.tick
    (by intro _ _; cases more <;> rfl) (by decide) (by cases more <;> decide) (by
      cases more <;>
        change some src = some (src + 0#64) ∧ some (dst + 0#64) = some (dst + 0#64) ∧
          some ((dst + BitVec.ofNat 64 n) &&& sign_extend (m := 64) (0xff8#12)) = _ ∧
          some 64#64 = some 64#64 ∧ some (dst + BitVec.ofNat 64 n) = _ ∧
          some dst = some dst ∧ some r = some r ∧ True
      all_goals simp only [mask, BitVec.add_zero, and_self])
  obtain ⟨a1, a4, a2, a5, a7, a0, ra, _⟩ := C.selected_regs
  have mem : after.σ.mem = before.σ.mem := by
    have memory := C.mem
    cases chosen : more <;> rw [chosen] at memory <;> exact memory
  refine ⟨after, C.steps,
    { output := C.output, frame := C.reg_frame, presence := by rw [mem]; exact .refl _
      state := { good := C.good, loaded := by rw [mem]; exact h.loaded
                 tick := C.tick, a0 := a0, ra := ra, regions := h.regions, bound := h.bound
                 meminv := by rw [mem]; exact h.meminv
                 a1 := a1, a2 := a2, a4 := a4, a5 := a5, a7 := a7, align := align
                 offset_align := by decide, word_bound := Nat.zero_le _, pc := ?_ } }⟩
  have pc := C.pc
  by_cases wide : 72 ≤ 8*(n/8)
  · simp only [more, wide, decide_true] at pc
    simpa only [Nat.zero_add, wide, if_true, largeEntrySegPC] using pc
  · simp only [more, wide, decide_false] at pc
    simpa only [Nat.zero_add, wide, largeEntrySegPC, Bool.false_eq_true, ite_false] using pc

#print axioms smallEntry
#print axioms largeEntry

end Vsa.Sim.MemcpyCopy
