import Vsa.Sim.MemcpyCopyWord

namespace Vsa.Sim.MemcpyCopy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc Vsa.Logic

def wordMeasure (dst : BitVec 64) (n : Nat) (c : Config) : Nat :=
  n - (((c.σ.regs.get? Register.x15).getD 0).toNat - dst.toNat)

theorem wordMeasure_at {dst src r : BitVec 64} {n start j : Nat} {bs : Nat → BitVec 8}
    {m0 : Mem} {c : Config} (h : WordState dst src r n start j bs m0 c) :
    wordMeasure dst n c = n - 8*j := by
  simp only [wordMeasure, h.a5, Option.getD_some]
  rw [ptr_toNat dst (8*j) (by have := h.regions.dst_hi; have := h.bound; omega)]
  omega

/-- Every actual small-word iteration decreases the remaining-byte measure. -/
theorem wordIteration (dst src r : BitVec 64) (n start : Nat) (bs : Nat → BitVec 8)
    (m0 : Mem) (origin : Config) (fuel : Nat) :
    Triple (fun c => Retained (fun c => ∃ j, WordState dst src r n start j bs m0 c) origin c ∧
      c.σ.regs.get? Register.PC = some 0x80006c08#64 ∧ wordMeasure dst n c = fuel)
      (fun c => Retained (fun c => ∃ j, WordState dst src r n start j bs m0 c) origin c ∧
        wordMeasure dst n c < fuel) := by
  intro before ⟨kept, atHead, measure⟩
  obtain ⟨j, state⟩ := kept.state
  have remaining : j < n/8 := by
    by_cases remaining : j < n/8
    · exact remaining
    · have pc := state.pc
      rw [if_neg remaining, atHead] at pc
      contradiction
  obtain ⟨after, steps, next⟩ := word state remaining
  have carried := kept.then next
  refine ⟨after, steps, { carried with state := ⟨j+1, next.state⟩ }, ?_⟩
  rw [wordMeasure_at next.state]
  rw [wordMeasure_at state] at measure
  omega

/-- Finish all whole words from the current small-word loop head. -/
theorem words {dst src r : BitVec 64} {n start j : Nat} {bs : Nat → BitVec 8} {m0 : Mem}
    {before : Config} (h : WordState dst src r n start j bs m0 before) :
    ∃ after, Steps before after ∧
      Retained (WordState dst src r n start (n/8) bs m0) before after := by
  have initial : Retained (fun c => ∃ j, WordState dst src r n start j bs m0 c) before before :=
    { state := ⟨j, h⟩, output := rfl, frame := fun _ _ => rfl, presence := .refl _ }
  obtain ⟨after, steps, reached, stopped⟩ :=
    loopFromBody (wordMeasure dst n) (wordIteration dst src r n start bs m0 before) before initial
  obtain ⟨k, state⟩ := reached.state
  have done : k = n/8 := by
    by_cases remaining : k < n/8
    · exact False.elim (stopped (by simpa only [remaining, if_true] using state.pc))
    · have := state.word_bound
      omega
  subst k
  exact ⟨after, steps, { reached with state := state }⟩

#print axioms words

end Vsa.Sim.MemcpyCopy
