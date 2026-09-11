import Vsa.Sim.MemcpyCopyBulkFacts
import Vsa.Sim.MemcpyCopyBulkCertificates

namespace Vsa.Sim.MemcpyCopy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc Vsa.Logic

theorem bulkDifference (dst : BitVec 64) (n i : Nat) (remaining : i+72 ≤ 8*(n/8)) :
    (dst + BitVec.ofNat 64 (8*(n/8))) -
      ((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x048#12)) =
      BitVec.ofNat 64 (8*(n/8)-(i+72)) := by
  rw [bulkIncrement]
  have sum : (dst + BitVec.ofNat 64 (i+72)) + BitVec.ofNat 64 (8*(n/8)-(i+72)) =
      dst + BitVec.ofNat 64 (8*(n/8)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add,
      show i+72+(8*(n/8)-(i+72)) = 8*(n/8) by omega]
  rw [← sum]
  exact sub_base_span _ _

/-- The signed branch tests whether another full 72-byte iteration remains. -/
theorem bulkGuard {dst src r : BitVec 64} {n i : Nat} {bs : Nat → BitVec 8} {m0 : Mem}
    {before : Config} (h : BulkState dst src r n i bs m0 before)
    (remaining : i+72 ≤ 8*(n/8)) :
    guardB bop.BLT 64#64 ((dst + BitVec.ofNat 64 (8*(n/8))) -
      ((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x048#12))) =
      decide (i+72+72 ≤ 8*(n/8)) := by
  rw [bulkDifference dst n i remaining]
  have signed : (BitVec.ofNat 64 (8*(n/8)-(i+72))).toInt = (8*(n/8)-(i+72) : Nat) := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := h.regions.dst_hi; omega), if_pos (by have := h.regions.dst_hi; omega)]
  change decide ((64#64).toInt < (BitVec.ofNat 64 (8*(n/8)-(i+72))).toInt) = _
  rw [signed]
  change decide ((64 : Int) < (8*(n/8)-(i+72) : Nat)) = _
  simp only [decide_eq_decide]
  have := h.offset_align
  omega

/-- Execute one complete 72-byte iteration and its actual back edge or exit jump. -/
theorem bulk {dst src r : BitVec 64} {n i : Nat} {bs : Nat → BitVec 8} {m0 : Mem}
    {before : Config} (h : BulkState dst src r n i bs m0 before)
    (remaining : i+72 ≤ 8*(n/8)) :
    ∃ after, Steps before after ∧ Retained (BulkState dst src r n (i+72) bs m0) before after := by
  let more := decide (i+72+72 ≤ 8*(n/8))
  let L := bulkRegs dst src r n i
  let lds := bulkLoads before.σ.mem (src.toNat + i)
  have bound : dst.toNat + i + 72 < 2^64 := by have := h.regions.dst_hi; omega
  have facts := bulkFacts h remaining more (bulkGuard h remaining)
  obtain ⟨vm, hvm⟩ := h.good.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed (bulkSeg more) L lds 0x80006c60#64 vm
    (fun a => dst.toNat + i ≤ a ∧ a < dst.toNat + i + 72) AbiPreserved
    (bulkRegs dst src r n (i+72)) before h.good (by simpa [remaining] using h.pc) hvm
    ⟨h.a1, h.a4, h.a2, h.a5, h.a7, h.a0, h.ra, trivial⟩
    (by change KeysOK [11,14,12,15,17,10,1]; decide) facts
    (bulkOK more) h.tick
    (by
      intro a outside
      rw [bulkLogExact dst src r n i before.σ.mem more bound]
      exact (bulkLog_outside _ _ _ _ (by omega)).symm)
    (by decide) (bulkAvoids more) (bulkProjects dst src r n i before.σ.mem more)
  obtain ⟨a1, a4, a2, a5, a7, a0, ra, _⟩ := C.selected_regs
  have mem : after.σ.mem = writeLog before.σ.mem (bulkLog (dst.toNat + i) lds) := by
    rw [C.mem, bulkLogExact dst src r n i before.σ.mem more bound]
  refine ⟨after, C.steps,
    { output := C.output, frame := C.reg_frame
      presence := by rw [mem]; exact memExtends_writeLog _ _
      state := { good := C.good, tick := C.tick, a0 := a0, ra := ra
                 regions := h.regions, bound := by omega
                 a1 := a1, a2 := a2, a4 := a4, a5 := a5, a7 := a7
                 align := h.align, offset_align := by have := h.offset_align; omega
                 word_bound := remaining, loaded := ?_, meminv := ?_, pc := ?_ } }⟩
  · rw [mem]
    exact loadedBulk _ _ _ h.loaded (by have := h.regions.code_disjoint; omega)
  · rw [mem]
    exact storeBulk h.meminv h.regions.disjoint (by omega)
  · have pc := C.pc
    by_cases next : i+72+72 ≤ 8*(n/8)
    · simp only [more, next, decide_true] at pc
      simpa only [next, if_true] using pc
    · simp only [more, next, decide_false] at pc
      simpa only [next, if_false] using pc

#print axioms bulkGuard
#print axioms bulk

end Vsa.Sim.MemcpyCopy
