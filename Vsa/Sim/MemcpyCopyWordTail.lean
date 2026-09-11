import Vsa.Sim.MemcpyCopyWordRun
import Vsa.Sim.MemcpyCopyTail
import Vsa.Sim.MemcpySpec3

namespace Vsa.Sim.MemcpyCopy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc Vsa.Logic

theorem restPointer (base : BitVec 64) (start stop : Nat) (bound : start ≤ stop) :
    (base + BitVec.ofNat 64 (8*start)) + BitVec.ofNat 64 (8*(stop-start)) =
      base + BitVec.ofNat 64 (8*stop) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [show 8*start + 8*(stop-start) = 8*stop by omega]

/-- Execute the pointer normalization after the final small-word iteration. -/
theorem normalizeWords {dst src r : BitVec 64} {n start : Nat} {bs : Nat → BitVec 8}
    {m0 : Mem} {before : Config} (h : WordState dst src r n start (n/8) bs m0 before) :
    ∃ after, Steps before after ∧ Retained (TailInput dst src r n (8*(n/8)) bs m0) before after := by
  let count := n/8 - start
  have positive : 1 ≤ count := by have := h.start_lt; omega
  have startBound : start ≤ n/8 := Nat.le_of_lt h.start_lt
  have startNat : (dst + BitVec.ofNat 64 (8*start)).toNat = dst.toNat + 8*start :=
    ptr_toNat dst (8*start) (by have := h.regions.dst_hi; omega)
  have limit : (dst + BitVec.ofNat 64 (8*start)).toNat + 8*count < 2^64 := by
    rw [startNat]
    have := h.regions.dst_hi
    dsimp only [count]
    omega
  let delta := (((dst + BitVec.ofNat 64 (8*(n/8))) + sign_extend (m := 64) (0xfff#12)) -
      (dst + BitVec.ofNat 64 (8*start))) &&& sign_extend (m := 64) (0xff8#12)
  have deltaEq : delta = BitVec.ofNat 64 (8*(count-1)) := by
    have offset := epilogue_a2 (dst + BitVec.ofNat 64 (8*start)) count positive limit
    dsimp only [count] at offset ⊢
    rw [restPointer dst start (n/8) startBound] at offset
    exact offset
  have sourceEnd : ((src + BitVec.ofNat 64 (8*start)) + sign_extend (m := 64) (0x008#12)) +
      delta = src + BitVec.ofNat 64 (8*(n/8)) := by
    rw [deltaEq, epilogue_ptr _ count positive]
    exact restPointer src start (n/8) startBound
  have destEnd : ((dst + BitVec.ofNat 64 (8*start)) + sign_extend (m := 64) (0x008#12)) +
      delta = dst + BitVec.ofNat 64 (8*(n/8)) := by
    rw [deltaEq, epilogue_ptr _ count positive]
    exact restPointer dst start (n/8) startBound
  let L := wordRegs dst src r n start (n/8)
  have facts : ChainFacts before.σ.mem before.σ.mem L [] memcpyX6c1cSeg := by
    chain_facts h.loaded with "Vsa.Sim.Code.memcpy_at_"
  obtain ⟨vm, hvm⟩ := h.good.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed memcpyX6c1cSeg L [] 0x80006c1c#64 vm
    (fun _ => False) AbiPreserved
    [(11, src + BitVec.ofNat 64 (8*(n/8))), (14, dst + BitVec.ofNat 64 (8*(n/8))),
     (17, dst + BitVec.ofNat 64 n), (10, dst), (1, r)] before h.good (by simpa using h.pc) hvm
    ⟨h.a3, h.a5, h.a2, h.a1, h.a4, h.a7, h.a0, h.ra, trivial⟩
    (by change KeysOK [13,15,12,11,14,17,10,1]; decide) facts
    (by change ChainOK 0x80006c1c#64 [13,15,12,11,14,17,10,1] memcpyX6c1cSeg; decide) h.tick
    (by intro _ _; rfl) (by decide) (by decide) (by
      change some (((src + BitVec.ofNat 64 (8*start)) + sign_extend (m := 64) (0x008#12)) + delta) = _ ∧
        some (((dst + BitVec.ofNat 64 (8*start)) + sign_extend (m := 64) (0x008#12)) + delta) = _ ∧
        some (dst + BitVec.ofNat 64 n) = _ ∧ some dst = _ ∧ some r = _ ∧ True
      simp only [sourceEnd, destEnd, and_self])
  obtain ⟨a1, a4, a7, a0, ra, _⟩ := C.selected_regs
  exact ⟨after, C.steps,
    { output := C.output, frame := C.reg_frame, presence := by rw [C.mem]; exact .refl _
      state := { good := C.good, loaded := by rw [C.mem]; exact h.loaded
                 tick := C.tick, a0 := a0, ra := ra, regions := h.regions, bound := h.bound
                 meminv := by rw [C.mem]; exact h.meminv
                 pc := C.pc, a1 := a1, a4 := a4, a7 := a7 } }⟩

/-- Complete the whole-word loop, normalize pointers, finish the bytes, and return. -/
theorem wordsReturn {dst src r : BitVec 64} {n start j : Nat} {bs : Nat → BitVec 8}
    {m0 : Mem} {before : Config} (h : WordState dst src r n start j bs m0 before)
    (retAlign : r.toNat % 4 = 0) :
    ∃ after, Steps before after ∧ Retained (Returned dst src r n bs m0) before after := by
  obtain ⟨copied, copySteps, copiedState⟩ := words h
  obtain ⟨normalized, normalizeSteps, normalizedState⟩ := normalizeWords copiedState.state
  obtain ⟨after, tailSteps, returned⟩ := tail normalizedState.state retAlign
  exact ⟨after, copySteps.trans (normalizeSteps.trans tailSteps),
    copiedState.then (normalizedState.then returned)⟩

#print axioms normalizeWords
#print axioms wordsReturn

end Vsa.Sim.MemcpyCopy
