import Vsa.Sim.MemcpyCopyEntry
import Vsa.Sim.StepFrameOut

namespace Vsa.Sim.MemcpyCopy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc Vsa.Logic

structure MatchedInput (dst src r : BitVec 64) (n : Nat) (bs : Nat → BitVec 8)
    (m0 : Mem) (c : Config) : Prop extends State dst src r n 0 bs m0 c where
  pc : c.σ.regs.get? Register.PC = some 0x80006bd8#64
  a1 : c.σ.regs.get? Register.x11 = some src
  a2 : c.σ.regs.get? Register.x12 = some (BitVec.ofNat 64 n)
  a7 : c.σ.regs.get? Register.x17 = some (dst + BitVec.ofNat 64 n)
  positive : 0 < n

def lengthResult (n : Nat) : BitVec 64 :=
  zero_extend (m := 64) (bool_to_bit
    (zopz0zI_u (BitVec.ofNat 64 n) (sign_extend (m := 64) (0x008#12))))

structure TestedInput (dst src r : BitVec 64) (n : Nat) (bs : Nat → BitVec 8)
    (m0 : Mem) (c : Config) : Prop extends State dst src r n 0 bs m0 c where
  pc : c.σ.regs.get? Register.PC = some 0x80006bdc#64
  a1 : c.σ.regs.get? Register.x11 = some src
  a2 : c.σ.regs.get? Register.x12 = some (lengthResult n)
  a7 : c.σ.regs.get? Register.x17 = some (dst + BitVec.ofNat 64 n)
  positive : 0 < n

/-- Matching alignment reaches the binary's length test. -/
theorem matchedEntry {dst src r : BitVec 64} {n : Nat} {bs : Nat → BitVec 8} {m0 : Mem}
    {before : Config} (h : Input dst src r n bs m0 before)
    (matching : (src.toNat ^^^ dst.toNat) % 8 = 0) :
    ∃ after, Steps before after ∧ Retained (MatchedInput dst src r n bs m0) before after := by
  let L : GRegs := [(11, src), (10, dst), (12, BitVec.ofNat 64 n), (1, r)]
  have facts : ChainFacts before.σ.mem before.σ.mem L [] memcpyX6bc8FSeg := by
    chain_facts h.loaded with "Vsa.Sim.Code.memcpy_at_"
    exact and7_eq_zero_false (src ^^^ dst) (by simpa only [xor_toNat] using matching)
  obtain ⟨vm, hvm⟩ := h.good.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed memcpyX6bc8FSeg L [] 0x80006bc8#64 vm
    (fun _ => False) AbiPreserved
    [(11, src), (10, dst), (12, BitVec.ofNat 64 n), (17, dst + BitVec.ofNat 64 n), (1, r)]
    before h.good h.pc hvm ⟨h.a1, h.a0, h.a2, h.ra, trivial⟩
    (by change KeysOK [11,10,12,1]; decide) facts
    (by change ChainOK 0x80006bc8#64 [11,10,12,1] memcpyX6bc8FSeg; decide) h.tick
    (by intro _ _; rfl) (by decide) (by decide) (by exact ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩)
  obtain ⟨a1, a0, a2, a7, ra, _⟩ := C.selected_regs
  exact ⟨after, C.steps,
    { output := C.output, frame := C.reg_frame, presence := by rw [C.mem]; exact .refl _
      state := { good := C.good, loaded := by rw [C.mem]; exact h.loaded
                 tick := C.tick, a0 := a0, ra := ra, regions := h.regions, bound := h.bound
                 meminv := by rw [C.mem]; exact h.meminv
                 pc := C.pc, a1 := a1, a2 := a2, a7 := a7, positive := h.positive } }⟩

/-- Execute the existing SLTIU observation without extending the reflection engine. -/
theorem lengthTest {dst src r : BitVec 64} {n : Nat} {bs : Nat → BitVec 8} {m0 : Mem}
    {before : Config} (h : MatchedInput dst src r n bs m0 before) :
    ∃ after, Steps before after ∧ Retained (TestedInput dst src r n bs m0) before after := by
  obtain ⟨vm, hvm⟩ := h.good.minstret
  obtain ⟨σ, tick, step, tickBound, good, mem, obs⟩ :=
    site_80006bd8 before.σ before.tick before.steps 0x80006bd8#64 vm (BitVec.ofNat 64 n)
      h.good h.pc hvm h.a2 h.loaded rfl h.tick
  let after : Config := ⟨σ, tick, before.steps+1⟩
  have framed := StepFrameOut.of_alu obs
  have a2 := obs_alu_rd obs (by decide) (by decide) (by decide) (by decide) (by decide)
  have pc : σ.regs.get? Register.PC = some 0x80006bdc#64 := obs_alu_pc obs
  refine ⟨after, Steps.single step,
    { output := framed.out, presence := by change MemExtends before.σ.mem σ.mem; rw [mem]; exact .refl _
      state := { good := good, loaded := by change Code.MemcpyLoaded σ.mem; rw [mem]; exact h.loaded
                 tick := tickBound, a0 := framed.get Register.x10 (by decide) h.a0
                 ra := framed.get Register.x1 (by decide) h.ra, regions := h.regions, bound := h.bound
                 meminv := by change MemInv dst src n bs 0 m0 σ.mem; rw [mem]; exact h.meminv
                 pc := pc, a1 := framed.get Register.x11 (by decide) h.a1, a2 := a2
                 a7 := framed.get Register.x17 (by decide) h.a7, positive := h.positive }
      frame := ?_ }⟩
  intro R hR
  apply framed.frame R
  intro rr member
  rcases List.mem_cons.mp member with rfl | noise
  · exact abiPreserved_ne hR (by decide)
  · exact noise_ne_abi hR rr noise

#print axioms matchedEntry
#print axioms lengthTest

end Vsa.Sim.MemcpyCopy
