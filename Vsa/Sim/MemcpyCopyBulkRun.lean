import Vsa.Sim.MemcpyCopyBulk
import Vsa.Sim.DeriveLoop

namespace Vsa.Sim.MemcpyCopy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc Vsa.Logic

def bulkMeasure (dst : BitVec 64) (n : Nat) (c : Config) : Nat :=
  n - (((c.σ.regs.get? Register.x14).getD 0).toNat - dst.toNat)

theorem bulkMeasure_at {dst src r : BitVec 64} {n i : Nat} {bs : Nat → BitVec 8}
    {m0 : Mem} {c : Config} (h : BulkState dst src r n i bs m0 c) :
    bulkMeasure dst n c = n - i := by
  simp only [bulkMeasure, h.a4, Option.getD_some]
  rw [ptr_toNat dst i (by have := h.regions.dst_hi; have := h.bound; omega)]
  omega

/-- Each executed bulk iteration decreases the remaining copy by 72 bytes. -/
theorem bulkIteration (dst src r : BitVec 64) (n : Nat) (bs : Nat → BitVec 8)
    (m0 : Mem) (origin : Config) (fuel : Nat) :
    Triple (fun c => Retained (fun c => ∃ i, BulkState dst src r n i bs m0 c) origin c ∧
      c.σ.regs.get? Register.PC = some 0x80006c60#64 ∧ bulkMeasure dst n c = fuel)
      (fun c => Retained (fun c => ∃ i, BulkState dst src r n i bs m0 c) origin c ∧
        bulkMeasure dst n c < fuel) := by
  intro before ⟨kept, atHead, measure⟩
  obtain ⟨i, state⟩ := kept.state
  have remaining : i+72 ≤ 8*(n/8) := by
    by_cases remaining : i+72 ≤ 8*(n/8)
    · exact remaining
    · have pc := state.pc
      rw [if_neg remaining, atHead] at pc
      contradiction
  obtain ⟨after, steps, next⟩ := bulk state remaining
  have carried := kept.then next
  refine ⟨after, steps, { carried with state := ⟨i+72, next.state⟩ }, ?_⟩
  rw [bulkMeasure_at next.state]
  rw [bulkMeasure_at state] at measure
  omega

/-- Execute every full bulk iteration and reach the remaining-word dispatch. -/
theorem bulks {dst src r : BitVec 64} {n i : Nat} {bs : Nat → BitVec 8} {m0 : Mem}
    {before : Config} (h : BulkState dst src r n i bs m0 before) :
    ∃ after, Steps before after ∧
      Retained (fun c => ∃ j, BulkState dst src r n j bs m0 c ∧ ¬ j+72 ≤ 8*(n/8)) before after := by
  have initial : Retained (fun c => ∃ i, BulkState dst src r n i bs m0 c) before before :=
    { state := ⟨i, h⟩, output := rfl, frame := fun _ _ => rfl, presence := .refl _ }
  obtain ⟨after, steps, reached, stopped⟩ :=
    loopFromBody (bulkMeasure dst n) (bulkIteration dst src r n bs m0 before) before initial
  obtain ⟨j, state⟩ := reached.state
  have done : ¬ j+72 ≤ 8*(n/8) := by
    intro remaining
    exact stopped (by simpa only [remaining, if_true] using state.pc)
  exact ⟨after, steps, { reached with state := ⟨j, state, done⟩ }⟩

#print axioms bulks

end Vsa.Sim.MemcpyCopy
