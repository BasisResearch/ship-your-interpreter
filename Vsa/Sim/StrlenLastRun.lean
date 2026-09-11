import Vsa.Sim.StrlenTailRun
import Vsa.Sim.StepFrameOut

namespace Vsa.Sim.StrlenRun

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc Vsa.Logic

/-- Registers at the final byte's existing snez instruction. -/
structure LastInput (r : BitVec 64) (len offset : Nat) (byte : BitVec 8)
    (m0 : Mem) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : Code.StrlenLoaded c.σ.mem
  memory : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some 0x80006d64#64
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  a5 : c.σ.regs.get? Register.x15 = some (zero_extend (m := 64) byte)
  a3 : c.σ.regs.get? Register.x13 = some (BitVec.ofNat 64 offset)
  ra : c.σ.regs.get? Register.x1 = some r
  length : ((zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64)
    (zero_extend (m := 64) byte)))) + BitVec.ofNat 64 offset) +
    sign_extend (m := 64) (0xffe#12) = BitVec.ofNat 64 len

#derive_case lastReturnSeg chain
  [(0x80006d68#64, 0x00d50533#32),
   (0x80006d6c#64, 0xffe50513#32)]
    terminator ⟨0x80006d70#64, 0x00008067#32, 0x67#8, 0x80#8, 0#8, 0#8,
      .jr, 1, 0, 0#13, 0#21, 0#12⟩

/-- Execute the existing snez instruction and the reflected arithmetic return. -/
theorem finishLast {p r : BitVec 64} {len offset : Nat} {byte : BitVec 8} {m0 : Mem}
    {before : Config} (h : LastInput r len offset byte m0 before)
    (retAlign : r.toNat % 4 = 0) :
    ∃ after, Steps before after ∧ Retained (Returned p r len m0) before after := by
  obtain ⟨vm, hvm⟩ := h.minstret
  obtain ⟨σ, tick, step, tickBound, good, mem, obs⟩ :=
    site_80006d64 before.σ before.tick before.steps 0x80006d64#64 vm
      (zero_extend (m := 64) byte) h.good h.pc hvm h.a5 h.loaded rfl h.tick
  let middle : Config := ⟨σ, tick, before.steps + 1⟩
  have pc : σ.regs.get? Register.PC = some 0x80006d68#64 := obs_alu_pc obs
  have a0 := obs_alu_rd obs (by decide) (by decide) (by decide) (by decide) (by decide)
  have frame := StepFrameOut.of_alu obs
  have a3 := frame.get Register.x13 (by decide) h.a3
  have ra := frame.get Register.x1 (by decide) h.ra
  obtain ⟨vm', hvm'⟩ := obs_alu_minstret obs
  let result := zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) byte)))
  let L : GRegs := [(10, result), (13, BitVec.ofNat 64 offset), (1, r)]
  have code : Code.StrlenLoaded σ.mem := by rw [mem]; exact h.loaded
  have facts : ChainFacts σ.mem σ.mem L [] lastReturnSeg := by
    chain_facts code with "Vsa.Sim.Code.strlen_at_"
    change (BitVec.update (r + sign_extend (m := 64) (0#12)) 0 0#1).toNat % 4 = 0
    rw [ret_tgt r retAlign]
    exact retAlign
  obtain ⟨after, C⟩ := segEval_selected_framed lastReturnSeg L [] 0x80006d68#64 vm'
    (fun _ => False) AbiPreserved [(10, BitVec.ofNat 64 len), (1, r)] middle
    good pc hvm' ⟨a0, a3, ra, trivial⟩ (by change KeysOK [10, 13, 1]; decide) facts
    (by change ChainOK 0x80006d68#64 [10, 13, 1] lastReturnSeg; decide) tickBound
    (by intro k _; rfl) (by decide) (by decide) (by
      change some ((result + BitVec.ofNat 64 offset) + sign_extend (m := 64) (0xffe#12)) =
        some (BitVec.ofNat 64 len) ∧ some r = some r ∧ True
      simp only [result, h.length, and_self])
  obtain ⟨ha0, hra, _⟩ := C.selected_regs
  have returnedPC : after.σ.regs.get? Register.PC = some r := by
    have pc := C.pc
    change after.σ.regs.get? Register.PC =
      some (BitVec.update (r + sign_extend (m := 64) (0#12)) 0 0#1) at pc
    rwa [ret_tgt r retAlign] at pc
  refine ⟨after, (Steps.single step).trans C.steps,
    { output := C.output.trans frame.out, frame := ?_
      state := { good := C.good, pc := returnedPC, a0 := ha0, ra := hra
                 mem := C.mem.trans (mem.trans h.memory), tick := C.tick } }⟩
  intro R hR
  have avoids : ∀ rr ∈ Register.x10 :: noiseRegs, (rr == R) = false := by
    intro rr member
    rcases List.mem_cons.mp member with rfl | noise
    · exact abiPreserved_ne hR (by decide)
    · exact noise_ne_abi hR rr noise
  exact (C.reg_frame R hR).trans (frame.frame R avoids)

#print axioms finishLast

end Vsa.Sim.StrlenRun
