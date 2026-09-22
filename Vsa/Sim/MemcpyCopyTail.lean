import Vsa.Sim.MemcpyCopyByteRun

namespace Vsa.Sim.MemcpyCopy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc Vsa.Logic

/-- The common tail branch after the whole-word copy. -/
structure TailInput (dst src r : BitVec 64) (n i : Nat) (bs : Nat → BitVec 8)
    (m0 : Mem) (c : Config) : Prop extends State dst src r n i bs m0 c where
  pc : c.σ.regs.get? Register.PC = some 0x80006c38#64
  a1 : c.σ.regs.get? Register.x11 = some (src + BitVec.ofNat 64 i)
  a4 : c.σ.regs.get? Register.x14 = some (dst + BitVec.ofNat 64 i)
  a7 : c.σ.regs.get? Register.x17 = some (dst + BitVec.ofNat 64 n)

/-- Reflected end PC of the tail branch: `simp` no longer ground-reduces `evalBlocksPC`. -/
private theorem tailSegPC (L : GRegs) (lds : List (List (BitVec 8))) :
    evalBlocksPC (0x80006c38#64) (SegEvalState.init L lds) memcpyX6c38TSeg = 0x80006c48#64 := by
  rw [evalBlocksPC, chainEndPC_eq_bt memcpyX6c38TSeg _ _ _ (by decide)]
  rfl

/-- Take the actual branch to the remaining byte suffix. -/
theorem tailBytes {dst src r : BitVec 64} {n i : Nat} {bs : Nat → BitVec 8} {m0 : Mem}
    {before : Config} (h : TailInput dst src r n i bs m0 before) (remaining : i < n) :
    ∃ after, Steps before after ∧ Retained (ByteState dst src r n i bs m0) before after := by
  let L := byteRegs dst src r n i
  have facts : ChainFacts before.σ.mem before.σ.mem L [] memcpyX6c38TSeg := by
    chain_facts h.loaded with "Vsa.Sim.Code.memcpy_at_"
    change zopz0zI_u (dst + BitVec.ofNat 64 i) (dst + BitVec.ofNat 64 n) = true
    unfold zopz0zI_u Sail.BitVec.toNatInt
    rw [decide_eq_true_iff,
      ptr_toNat dst i (by have := h.regions.dst_hi; omega),
      ptr_toNat dst n (by have := h.regions.dst_hi; omega)]
    apply Int.ofNat_lt.mpr
    omega
  obtain ⟨vm, hvm⟩ := h.good.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed memcpyX6c38TSeg L [] 0x80006c38#64 vm
    (fun _ => False) AbiPreserved L before h.good h.pc hvm
    ⟨h.a1, h.a4, h.a7, h.a0, h.ra, trivial⟩ (by change KeysOK [11,14,17,10,1]; decide) facts
    (by change ChainOK 0x80006c38#64 [11,14,17,10,1] memcpyX6c38TSeg; decide) h.tick
    (by intro _ _; rfl) (by decide) (by decide) (by exact ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩)
  obtain ⟨a1, a4, a7, a0, ra, _⟩ := C.selected_regs
  exact ⟨after, C.steps,
    { output := C.output, frame := C.reg_frame, presence := by rw [C.mem]; exact .refl _
      state := { good := C.good, loaded := by rw [C.mem]; exact h.loaded
                 tick := C.tick, a0 := a0, ra := ra, regions := h.regions, bound := h.bound
                 meminv := by rw [C.mem]; exact h.meminv
                 pc := by simpa only [remaining, if_true, tailSegPC] using C.pc
                 a1 := a1, a4 := a4, a7 := a7 } }⟩

/-- Return directly when the whole-word copy exhausted the input. -/
theorem tailReturn {dst src r : BitVec 64} {n : Nat} {bs : Nat → BitVec 8} {m0 : Mem}
    {before : Config} (h : TailInput dst src r n n bs m0 before) (retAlign : r.toNat % 4 = 0) :
    ∃ after, Steps before after ∧ Retained (Returned dst src r n bs m0) before after := by
  let seg := memcpyX6c38FSeg ++ memcpyX6c3cSeg
  let L : GRegs := [(14, dst + BitVec.ofNat 64 n), (17, dst + BitVec.ofNat 64 n), (1, r), (10, dst)]
  have facts : ChainFacts before.σ.mem before.σ.mem L [] seg := by
    unfold seg
    chain_facts h.loaded with "Vsa.Sim.Code.memcpy_at_"
    · change zopz0zI_u (dst + BitVec.ofNat 64 n) (dst + BitVec.ofNat 64 n) = false
      simp [zopz0zI_u]
    · change (BitVec.update (r + sign_extend (m := 64) (0#12)) 0 0#1).toNat % 4 = 0
      rw [ret_tgt r retAlign]
      exact retAlign
  obtain ⟨vm, hvm⟩ := h.good.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed seg L [] 0x80006c38#64 vm
    (fun _ => False) AbiPreserved [(1, r), (10, dst)] before h.good h.pc hvm
    ⟨h.a4, h.a7, h.ra, h.a0, trivial⟩ (by change KeysOK [14,17,1,10]; decide) facts
    (by change ChainOK 0x80006c38#64 [14,17,1,10] seg; decide) h.tick
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

/-- Finish the actual common tail, with or without trailing bytes. -/
theorem tail {dst src r : BitVec 64} {n i : Nat} {bs : Nat → BitVec 8} {m0 : Mem}
    {before : Config} (h : TailInput dst src r n i bs m0 before) (retAlign : r.toNat % 4 = 0) :
    ∃ after, Steps before after ∧ Retained (Returned dst src r n bs m0) before after := by
  by_cases remaining : i < n
  · obtain ⟨entered, entrySteps, entryState⟩ := tailBytes h remaining
    obtain ⟨after, copySteps, returned⟩ := bytesReturn entryState.state retAlign
    exact ⟨after, entrySteps.trans copySteps, entryState.then returned⟩
  · have equal : i = n := by have := h.bound; omega
    subst i
    exact tailReturn h retAlign

#print axioms tailBytes
#print axioms tailReturn
#print axioms tail

end Vsa.Sim.MemcpyCopy
