import Vsa.Sim.StrlenLastRun

namespace Vsa.Sim.StrlenRun

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc Vsa.Logic

#derive_case lastByteSeg chain [(0x80006d60#64, 0xffe74783#32)]

def tail6Seg : List BBlock := strlenX6d2cFSeg ++ strlenX6d38FSeg ++
  strlenX6d40FSeg ++ strlenX6d48FSeg ++ strlenX6d50FSeg ++ strlenX6d58FSeg ++ lastByteSeg

/-- The final two offsets reach the existing snez seam and return. -/
theorem tail6 {p r : BitVec 64} {len off j : Nat} {cs : List Char} {m0 : Mem}
    {before : Config} (h : WTailG p r len cs m0 off j before)
    (last : off + 8*j + 5 < len) (retAlign : r.toNat % 4 = 0) :
    ∃ after, Steps before after ∧ Retained (Returned p r len m0) before after := by
  let pos := p + BitVec.ofNat 64 (off + 8*(j+1))
  let L : GRegs := [(14, pos), (10, p), (1, r)]
  let byte := fun n => (m0[p.toNat + (off + 8*j) + n]?).getD 0
  let bytes := [[byte 0], [byte 1], [byte 2], [byte 3], [byte 4], [byte 5], [byte 6]]
  have facts : ChainFacts before.σ.mem before.σ.mem L bytes tail6Seg := by
    chain_facts h.loaded with "Vsa.Sim.Code.strlen_at_"
    · apply tailLoad h 0 (by decide) _ _ rfl
      exact tailAddress h 0 (by decide) 0xff8#12 (by decide)
    · change ((zero_extend (m := 64) (byte 0)) == 0#64) = false
      rw [tdec_guardG p len off j 0 cs m0 h.cstr h.hlen (by omega)]
      simp only [decide_eq_false_iff_not]
      omega
    · apply tailLoad h 1 (by decide) _ _ rfl
      exact tailAddress h 1 (by decide) 0xff9#12 (by decide)
    · change ((zero_extend (m := 64) (byte 1)) == 0#64) = false
      rw [tdec_guardG p len off j 1 cs m0 h.cstr h.hlen (by omega)]
      simp only [decide_eq_false_iff_not]
      omega
    · apply tailLoad h 2 (by decide) _ _ rfl
      exact tailAddress h 2 (by decide) 0xffa#12 (by decide)
    · change ((zero_extend (m := 64) (byte 2)) == 0#64) = false
      rw [tdec_guardG p len off j 2 cs m0 h.cstr h.hlen (by omega)]
      simp only [decide_eq_false_iff_not]
      omega
    · apply tailLoad h 3 (by decide) _ _ rfl
      exact tailAddress h 3 (by decide) 0xffb#12 (by decide)
    · change ((zero_extend (m := 64) (byte 3)) == 0#64) = false
      rw [tdec_guardG p len off j 3 cs m0 h.cstr h.hlen (by omega)]
      simp only [decide_eq_false_iff_not]
      omega
    · apply tailLoad h 4 (by decide) _ _ rfl
      exact tailAddress h 4 (by decide) 0xffc#12 (by decide)
    · change ((zero_extend (m := 64) (byte 4)) == 0#64) = false
      rw [tdec_guardG p len off j 4 cs m0 h.cstr h.hlen (by omega)]
      simp only [decide_eq_false_iff_not]
      omega
    · apply tailLoad h 5 (by decide) _ _ rfl
      exact tailAddress h 5 (by decide) 0xffd#12 (by decide)
    · change ((zero_extend (m := 64) (byte 5)) == 0#64) = false
      rw [tdec_guardG p len off j 5 cs m0 h.cstr h.hlen (by omega)]
      simp only [decide_eq_false_iff_not]
      omega
    · apply tailLoad h 6 (by decide) _ _ rfl
      exact tailAddress h 6 (by decide) 0xffe#12 (by decide)
  have result : ((zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) (byte 6))))) + BitVec.ofNat 64 (off + 8*(j+1))) + sign_extend (m := 64) (0xffe#12) = BitVec.ofNat 64 len := by
    obtain ⟨b, read, zero⟩ := tail_byte_someG p len off j 6 cs m0 h.cstr h.hlen (by omega)
    have byteEq : byte 6 = b := by simp only [byte, read, Option.getD_some]
    rw [byteEq]
    exact snez_finalG off j len b last h.jhi
      (by have := h.regions.hi; have := h.jlo; omega) zero
  obtain ⟨vm, hvm⟩ := h.minstret
  obtain ⟨middle, C⟩ := segEval_selected_framed tail6Seg L bytes 0x80006d2c#64 vm
    (fun _ => False) AbiPreserved
    [(15, zero_extend (m := 64) (byte 6)), (13, BitVec.ofNat 64 (off + 8*(j+1))), (1, r)] before
    h.good h.pc hvm ⟨h.a4, h.a0, h.ra, trivial⟩
    (by change KeysOK [14, 10, 1]; decide) facts
    (by change ChainOK 0x80006d2c#64 [14, 10, 1] tail6Seg; decide) h.tick
    (by intro a _; rfl) (by decide) (by decide) (by
      change some (zero_extend (m := 64) (byte 6)) = some (zero_extend (m := 64) (byte 6)) ∧
        some (pos - p) = some (BitVec.ofNat 64 (off + 8*(j+1))) ∧ some r = some r ∧ True
      simp only [pos, sub_a4_a0_val, and_self])
  obtain ⟨a5, a3, ra, _⟩ := C.selected_regs
  have input : LastInput r len (off + 8*(j+1)) (byte 6) m0 middle :=
    { good := C.good, loaded := by rw [C.mem]; exact h.loaded
      memory := C.mem.trans h.mem, pc := C.pc, minstret := C.minstret
      tick := C.tick, a5 := a5, a3 := a3, ra := ra, length := result }
  obtain ⟨after, steps, returned⟩ := finishLast (p := p) input retAlign
  exact ⟨after, C.steps.trans steps,
    { state := returned.state, output := returned.output.trans C.output
      frame := fun R hR => (returned.frame R hR).trans (C.reg_frame R hR) }⟩

#print axioms tail6

/-- Every NUL position in the final word returns the exact string length. -/
theorem tail {p r : BitVec 64} {len off j : Nat} {cs : List Char} {m0 : Mem}
    {before : Config} (h : WTailG p r len cs m0 off j before) (retAlign : r.toNat % 4 = 0) :
    ∃ after, Steps before after ∧ Retained (Returned p r len m0) before after := by
  have lo := h.jlo
  have positions : off + 8*j = len ∨ off + 8*j + 1 = len ∨ off + 8*j + 2 = len ∨
      off + 8*j + 3 = len ∨ off + 8*j + 4 = len ∨ off + 8*j + 5 = len ∨
      off + 8*j + 5 < len := by omega
  rcases positions with at0 | at1 | at2 | at3 | at4 | at5 | at6
  · exact tail0 h (by omega) retAlign
  · exact tail1 h at1 retAlign
  · exact tail2 h at2 retAlign
  · exact tail3 h at3 retAlign
  · exact tail4 h at4 retAlign
  · exact tail5 h at5 retAlign
  · exact tail6 h at6 retAlign

#print axioms tail
end Vsa.Sim.StrlenRun
