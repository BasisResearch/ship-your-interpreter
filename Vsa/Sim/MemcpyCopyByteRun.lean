import Vsa.Sim.MemcpyCopyByte

namespace Vsa.Sim.MemcpyCopy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc Vsa.Logic

def byteMeasure (dst : BitVec 64) (n : Nat) (c : Config) : Nat :=
  n - (((c.σ.regs.get? Register.x14).getD 0).toNat - dst.toNat)

theorem byteMeasure_at {dst src r : BitVec 64} {n i : Nat} {bs : Nat → BitVec 8}
    {m0 : Mem} {c : Config} (h : ByteState dst src r n i bs m0 c) :
    byteMeasure dst n c = n - i := by
  simp only [byteMeasure, h.a4, Option.getD_some]
  rw [ptr_toNat dst i (by have := h.regions.dst_hi; have := h.bound; omega)]
  omega

/-- One actual byte iteration decreases the remaining-byte measure. -/
theorem byteIteration (dst src r : BitVec 64) (n : Nat) (bs : Nat → BitVec 8)
    (m0 : Mem) (origin : Config) (fuel : Nat) :
    Triple (fun c => Retained (fun c => ∃ i, ByteState dst src r n i bs m0 c) origin c ∧
      c.σ.regs.get? Register.PC = some 0x80006c48#64 ∧ byteMeasure dst n c = fuel)
      (fun c => Retained (fun c => ∃ i, ByteState dst src r n i bs m0 c) origin c ∧
        byteMeasure dst n c < fuel) := by
  intro before ⟨kept, atHead, measure⟩
  obtain ⟨i, state⟩ := kept.state
  have remaining : i < n := by
    by_cases remaining : i < n
    · exact remaining
    · have pc := state.pc
      rw [if_neg remaining, atHead] at pc
      contradiction
  obtain ⟨after, steps, next⟩ := byte state remaining
  have carried := kept.then next
  refine ⟨after, steps, { carried with state := ⟨i+1, next.state⟩ }, ?_⟩
  rw [byteMeasure_at next.state]
  rw [byteMeasure_at state] at measure
  omega

/-- Complete every remaining byte, retaining the caller and memory domain. -/
theorem bytes {dst src r : BitVec 64} {n i : Nat} {bs : Nat → BitVec 8} {m0 : Mem}
    {before : Config} (h : ByteState dst src r n i bs m0 before) :
    ∃ after, Steps before after ∧ Retained (ByteState dst src r n n bs m0) before after := by
  have initial : Retained (fun c => ∃ i, ByteState dst src r n i bs m0 c) before before :=
    { state := ⟨i, h⟩, output := rfl, frame := fun _ _ => rfl, presence := .refl _ }
  obtain ⟨after, steps, reached, stopped⟩ :=
    loopFromBody (byteMeasure dst n) (byteIteration dst src r n bs m0 before) before initial
  obtain ⟨j, state⟩ := reached.state
  have done : j = n := by
    by_cases remaining : j < n
    · exact False.elim (stopped (by simpa only [remaining, if_true] using state.pc))
    · have := state.bound
      omega
  subst j
  exact ⟨after, steps, { reached with state := state }⟩

structure Returned (dst src r : BitVec 64) (n : Nat) (bs : Nat → BitVec 8)
    (m0 : Mem) (c : Config) : Prop extends State dst src r n n bs m0 c where
  pc : c.σ.regs.get? Register.PC = some r

/-- Execute the byte loop's return instruction. -/
theorem byteReturn {dst src r : BitVec 64} {n : Nat} {bs : Nat → BitVec 8} {m0 : Mem}
    {before : Config} (h : ByteState dst src r n n bs m0 before)
    (retAlign : r.toNat % 4 = 0) :
    ∃ after, Steps before after ∧ Retained (Returned dst src r n bs m0) before after := by
  have facts : ChainFacts before.σ.mem before.σ.mem [(1, r), (10, dst)] []
      memcpyX6c5cSeg := by
    chain_facts h.loaded with "Vsa.Sim.Code.memcpy_at_"
    change (BitVec.update (r + sign_extend (m := 64) (0#12)) 0 0#1).toNat % 4 = 0
    rw [ret_tgt r retAlign]
    exact retAlign
  obtain ⟨vm, hvm⟩ := h.good.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed memcpyX6c5cSeg [(1, r), (10, dst)] []
    0x80006c5c#64 vm (fun _ => False) AbiPreserved [(1, r), (10, dst)] before
    h.good (by simpa using h.pc) hvm ⟨h.ra, h.a0, trivial⟩
    (by change KeysOK [1,10]; decide) facts
    (by change ChainOK 0x80006c5c#64 [1,10] memcpyX6c5cSeg; decide) h.tick
    (by intro _ _; rfl) (by decide) (by decide) (by exact ⟨rfl, rfl, trivial⟩)
  obtain ⟨ra, a0, _⟩ := C.selected_regs
  have pc : after.σ.regs.get? Register.PC = some r := by
    have pc := C.pc
    change after.σ.regs.get? Register.PC =
      some (BitVec.update (r + sign_extend (m := 64) (0#12)) 0 0#1) at pc
    rwa [ret_tgt r retAlign] at pc
  exact ⟨after, C.steps,
    { output := C.output, frame := C.reg_frame, presence := by rw [C.mem]; exact .refl _
      state := { good := C.good, loaded := by rw [C.mem]; exact h.loaded
                 tick := C.tick, a0 := a0, ra := ra, regions := h.regions, bound := h.bound
                 meminv := by rw [C.mem]; exact h.meminv, pc := pc } }⟩

/-- Complete the byte suffix and return to the actual caller. -/
theorem bytesReturn {dst src r : BitVec 64} {n i : Nat} {bs : Nat → BitVec 8} {m0 : Mem}
    {before : Config} (h : ByteState dst src r n i bs m0 before)
    (retAlign : r.toNat % 4 = 0) :
    ∃ after, Steps before after ∧ Retained (Returned dst src r n bs m0) before after := by
  obtain ⟨copied, copySteps, copiedState⟩ := bytes h
  obtain ⟨after, returnSteps, returned⟩ := byteReturn copiedState.state retAlign
  exact ⟨after, copySteps.trans returnSteps, copiedState.then returned⟩

#print axioms bytes
#print axioms byteReturn
#print axioms bytesReturn

end Vsa.Sim.MemcpyCopy
