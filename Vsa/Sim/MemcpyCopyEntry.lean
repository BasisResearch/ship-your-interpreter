import Vsa.Sim.MemcpyCopyByteRun
import Vsa.Sim.MemcpySpec4
import Vsa.Sim.StepFrameOut

namespace Vsa.Sim.MemcpyCopy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc Vsa.Logic

/-- Actual memcpy call arguments and the source byte representation. -/
structure Input (dst src r : BitVec 64) (n : Nat) (bs : Nat → BitVec 8)
    (m0 : Mem) (c : Config) : Prop extends State dst src r n 0 bs m0 c where
  pc : c.σ.regs.get? Register.PC = some 0x80006bc8#64
  a1 : c.σ.regs.get? Register.x11 = some src
  a2 : c.σ.regs.get? Register.x12 = some (BitVec.ofNat 64 n)
  positive : 0 < n

/-- Reflected end PC of the entry branch: `simp` no longer ground-reduces `evalBlocksPC`. -/
private theorem entrySegPC (L : GRegs) (lds : List (List (BitVec 8))) :
    evalBlocksPC (0x80006c40#64) (SegEvalState.init L lds) memcpyX6c40FSeg = 0x80006c48#64 := by
  rw [evalBlocksPC, chainEndPC_eq_bt memcpyX6c40FSeg _ _ _ (by decide)]
  rfl

/-- The common byte-path setup at the actual branch destination. -/
structure ByteInput (dst src r : BitVec 64) (n : Nat) (bs : Nat → BitVec 8)
    (m0 : Mem) (c : Config) : Prop extends State dst src r n 0 bs m0 c where
  pc : c.σ.regs.get? Register.PC = some 0x80006c40#64
  a1 : c.σ.regs.get? Register.x11 = some src
  a7 : c.σ.regs.get? Register.x17 = some (dst + BitVec.ofNat 64 n)
  positive : 0 < n

/-- Enter the byte loop from the actual byte-path setup. -/
theorem byteEntry {dst src r : BitVec 64} {n : Nat} {bs : Nat → BitVec 8} {m0 : Mem}
    {before : Config} (h : ByteInput dst src r n bs m0 before) :
    ∃ after, Steps before after ∧ Retained (ByteState dst src r n 0 bs m0) before after := by
  let L : GRegs := [(10, dst), (11, src), (17, dst + BitVec.ofNat 64 n), (1, r)]
  have facts : ChainFacts before.σ.mem before.σ.mem L [] memcpyX6c40FSeg := by
    chain_facts h.loaded with "Vsa.Sim.Code.memcpy_at_"
    exact bgeu_false_dst_span dst n (by have := h.regions.dst_hi; omega) h.positive
  obtain ⟨vm, hvm⟩ := h.good.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed memcpyX6c40FSeg L [] 0x80006c40#64 vm
    (fun _ => False) AbiPreserved (byteRegs dst src r n 0) before h.good h.pc hvm
    ⟨h.a0, h.a1, h.a7, h.ra, trivial⟩ (by change KeysOK [10,11,17,1]; decide) facts
    (by change ChainOK 0x80006c40#64 [10,11,17,1] memcpyX6c40FSeg; decide) h.tick
    (by intro _ _; rfl) (by decide) (by decide) (by
      change some src = some (src + 0#64) ∧ some (dst + 0#64) = some (dst + 0#64) ∧
        some (dst + BitVec.ofNat 64 n) = some (dst + BitVec.ofNat 64 n) ∧
        some dst = some dst ∧ some r = some r ∧ True
      simp)
  obtain ⟨a1, a4, a7, a0, ra, _⟩ := C.selected_regs
  exact ⟨after, C.steps,
    { output := C.output, frame := C.reg_frame, presence := by rw [C.mem]; exact .refl _
      state := { good := C.good, loaded := by rw [C.mem]; exact h.loaded
                 tick := C.tick, a0 := a0, ra := ra, regions := h.regions, bound := h.bound
                 meminv := by rw [C.mem]; exact h.meminv
                 pc := by simpa only [h.positive, if_true, entrySegPC] using C.pc
                 a1 := a1, a4 := a4, a7 := a7 } }⟩

/-- Differing pointer alignments select the byte path in the binary. -/
theorem misalignedEntry {dst src r : BitVec 64} {n : Nat} {bs : Nat → BitVec 8} {m0 : Mem}
    {before : Config} (h : Input dst src r n bs m0 before)
    (different : (src.toNat ^^^ dst.toNat) % 8 ≠ 0) :
    ∃ after, Steps before after ∧ Retained (ByteInput dst src r n bs m0) before after := by
  let L : GRegs := [(11, src), (10, dst), (12, BitVec.ofNat 64 n), (1, r)]
  have facts : ChainFacts before.σ.mem before.σ.mem L [] memcpyX6bc8TSeg := by
    chain_facts h.loaded with "Vsa.Sim.Code.memcpy_at_"
    change (((src ^^^ dst) &&& sign_extend (m := 64) (0x007#12)) != 0#64) = true
    apply (and7_ne_zero_iff _).mpr
    simpa only [xor_toNat] using different
  obtain ⟨vm, hvm⟩ := h.good.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed memcpyX6bc8TSeg L [] 0x80006bc8#64 vm
    (fun _ => False) AbiPreserved [(11, src), (10, dst), (17, dst + BitVec.ofNat 64 n), (1, r)]
    before h.good h.pc hvm ⟨h.a1, h.a0, h.a2, h.ra, trivial⟩
    (by change KeysOK [11,10,12,1]; decide) facts
    (by change ChainOK 0x80006bc8#64 [11,10,12,1] memcpyX6bc8TSeg; decide) h.tick
    (by intro _ _; rfl) (by decide) (by decide) (by exact ⟨rfl, rfl, rfl, rfl, trivial⟩)
  obtain ⟨a1, a0, a7, ra, _⟩ := C.selected_regs
  exact ⟨after, C.steps,
    { output := C.output, frame := C.reg_frame, presence := by rw [C.mem]; exact .refl _
      state := { good := C.good, loaded := by rw [C.mem]; exact h.loaded
                 tick := C.tick, a0 := a0, ra := ra, regions := h.regions, bound := h.bound
                 meminv := by rw [C.mem]; exact h.meminv
                 pc := C.pc, a1 := a1, a7 := a7, positive := h.positive } }⟩

/-- Complete the actual byte path for any positive length and differing alignment. -/
theorem misaligned {dst src r : BitVec 64} {n : Nat} {bs : Nat → BitVec 8} {m0 : Mem}
    {before : Config} (h : Input dst src r n bs m0 before)
    (different : (src.toNat ^^^ dst.toNat) % 8 ≠ 0) (retAlign : r.toNat % 4 = 0) :
    ∃ after, Steps before after ∧ Retained (Returned dst src r n bs m0) before after := by
  obtain ⟨selected, selectSteps, selectedState⟩ := misalignedEntry h different
  obtain ⟨entered, entrySteps, enteredState⟩ := byteEntry selectedState.state
  obtain ⟨after, copySteps, returned⟩ := bytesReturn enteredState.state retAlign
  exact ⟨after, selectSteps.trans (entrySteps.trans copySteps),
    selectedState.then (enteredState.then returned)⟩

#print axioms byteEntry
#print axioms misalignedEntry
#print axioms misaligned

end Vsa.Sim.MemcpyCopy
