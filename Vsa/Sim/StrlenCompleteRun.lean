import Vsa.Sim.StrlenTailComplete

namespace Vsa.Sim.StrlenRun

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc Vsa.Logic

/-- Initialize word detection after the unaligned peel. -/
theorem setup {p r : BitVec 64} {len off : Nat} {cs : List Char} {m0 : Mem}
    {before : Config} (h : HAlign p r len cs m0 off before) :
    ∃ after, Steps before after ∧ Retained (WStG p r len cs m0 off 0) before after := by
  let L : GRegs := [(14, p + BitVec.ofNat 64 off), (10, p), (1, r)]
  have facts : ChainFacts before.σ.mem before.σ.mem L [] strlenX6cfcSeg := by
    chain_facts h.loaded with "Vsa.Sim.Code.strlen_at_"
  obtain ⟨vm, hvm⟩ := h.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed strlenX6cfcSeg L [] 0x80006cfc#64 vm
    (fun _ => False) AbiPreserved
    [(14, p + BitVec.ofNat 64 off), (10, p), (1, r), (13, magic7f), (11, BitVec.allOnes 64)]
    before h.good h.pc hvm ⟨h.a4, h.a0, h.ra, trivial⟩
    (by change KeysOK [14, 10, 1]; decide) facts
    (by change ChainOK 0x80006cfc#64 [14, 10, 1] strlenX6cfcSeg; decide) h.tick
    (by intro k _; rfl) (by decide) (by decide)
    (by exact ⟨rfl, rfl, rfl, congrArg some magic_build, congrArg some allOnes_build, trivial⟩)
  obtain ⟨a4, a0, ra, a3, a1, _⟩ := C.selected_regs
  exact ⟨after, C.steps,
    { output := C.output, frame := C.reg_frame
      state := { good := C.good, loaded := by rw [C.mem]; exact h.loaded
                 mem := C.mem.trans h.mem, pc := C.pc, a0 := a0, a1 := a1, a3 := a3
                 a4 := by simpa [gprGet] using a4, ra := ra, minstret := C.minstret, tick := C.tick
                 regions := h.regions, qalign := h.qalign, cstr := h.cstr, hlen := h.hlen
                 jle := by simpa using h.off0le } }⟩

def alignedEntrySeg : List BBlock := strlenX6cf0FSeg ++ strlenX6cfcSeg

/-- Aligned names enter the same word loop directly. -/
theorem alignedEntry {p r : BitVec 64} {len : Nat} {cs : List Char} {m0 : Mem}
    {before : Config} (h : Pre p r len cs m0 before) :
    ∃ after, Steps before after ∧ Retained (WStG p r len cs m0 0 0) before after := by
  let L : GRegs := [(10, p), (1, r)]
  have facts : ChainFacts before.σ.mem before.σ.mem L [] alignedEntrySeg := by
    chain_facts h.loaded with "Vsa.Sim.Code.strlen_at_"
    change ((p &&& sign_extend (m := 64) (0x007#12)) != 0#64) = false
    rw [andi7_aligned p h.align]
    decide
  obtain ⟨vm, hvm⟩ := h.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed alignedEntrySeg L [] 0x80006cf0#64 vm
    (fun _ => False) AbiPreserved
    [(14, p), (10, p), (1, r), (13, magic7f), (11, BitVec.allOnes 64)]
    before h.good h.pc hvm ⟨h.a0, h.ra, trivial⟩
    (by change KeysOK [10, 1]; decide) facts
    (by change ChainOK 0x80006cf0#64 [10, 1] alignedEntrySeg; decide) h.tick
    (by intro k _; rfl) (by decide) (by decide) (by
      refine ⟨?_, rfl, rfl, congrArg some magic_build, congrArg some allOnes_build, trivial⟩
      change some (p + 0#64) = some p
      rw [BitVec.add_zero])
  obtain ⟨a4, a0, ra, a3, a1, _⟩ := C.selected_regs
  exact ⟨after, C.steps,
    { output := C.output, frame := C.reg_frame
      state := { good := C.good, loaded := by rw [C.mem]; exact h.loaded
                 mem := C.mem.trans h.mem, pc := C.pc, a0 := a0, a1 := a1, a3 := a3
                 a4 := by simpa [gprGet] using a4, ra := ra, minstret := C.minstret, tick := C.tick
                 regions := h.regions, qalign := by simpa using h.align
                 cstr := h.cstr, hlen := h.hlen, jle := Nat.zero_le _ } }⟩

#derive_case headReturnSeg chain []
  terminator ⟨0x80006d90#64, 0x00008067#32, 0x67#8, 0x80#8, 0#8, 0#8,
    .jr, 1, 0, 0#13, 0#21, 0#12⟩

/-- Return when the byte peel itself finds NUL. -/
theorem headReturn {p r : BitVec 64} {len : Nat} {m0 : Mem}
    {before : Config} (h : AtRet r len m0 0x80006d90#64 before) (retAlign : r.toNat % 4 = 0) :
    ∃ after, Steps before after ∧ Retained (Returned p r len m0) before after := by
  obtain ⟨good, code, mem, pc, a0, ra, ⟨vm, hvm⟩, tick⟩ := h
  let L : GRegs := [(10, BitVec.ofNat 64 len), (1, r)]
  have facts : ChainFacts before.σ.mem before.σ.mem L [] headReturnSeg := by
    chain_facts code with "Vsa.Sim.Code.strlen_at_"
    change (BitVec.update (r + sign_extend (m := 64) (0#12)) 0 0#1).toNat % 4 = 0
    rw [ret_tgt r retAlign]
    exact retAlign
  obtain ⟨after, C⟩ := segEval_selected_framed headReturnSeg L [] 0x80006d90#64 vm
    (fun _ => False) AbiPreserved L before good pc hvm ⟨a0, ra, trivial⟩
    (by change KeysOK [10, 1]; decide) facts
    (by change ChainOK 0x80006d90#64 [10, 1] headReturnSeg; decide) tick
    (by intro k _; rfl) (by decide) (by decide) ⟨rfl, rfl, trivial⟩
  obtain ⟨a0', ra', _⟩ := C.selected_regs
  have pc' : after.σ.regs.get? Register.PC = some r := by
    have reached := C.pc
    change after.σ.regs.get? Register.PC =
      some (BitVec.update (r + sign_extend (m := 64) (0#12)) 0 0#1) at reached
    rwa [ret_tgt r retAlign] at reached
  exact ⟨after, C.steps,
    { output := C.output, frame := C.reg_frame
      state := { good := C.good, pc := pc', a0 := a0', ra := ra'
                 mem := C.mem.trans mem, tick := C.tick } }⟩

/-- Complete the word loop and its byte-tail return. -/
theorem wordReturn {p r : BitVec 64} {len off j : Nat} {cs : List Char} {m0 : Mem}
    {before : Config} (h : WStG p r len cs m0 off j before) (retAlign : r.toNat % 4 = 0) :
    ∃ after, Steps before after ∧ Retained (Returned p r len m0) before after := by
  obtain ⟨middle, scanSteps, scanned⟩ := words h
  obtain ⟨_, atTail⟩ := scanned.state
  obtain ⟨after, tailSteps, returned⟩ := tail atTail retAlign
  exact ⟨after, scanSteps.trans tailSteps, scanned.then returned⟩

/-- Run strlen for either name alignment and retain memory, ABI registers, and output. -/
theorem run {p r : BitVec 64} {s : String} {m0 : Mem} {before : Config}
    (h : Input p r s m0 before) :
    ∃ after, Steps before after ∧ Retained (Returned p r s.length m0) before after := by
  obtain ⟨good, code, mem, pc, a0, ra, mi, tick, regions, string, retAlign⟩ := h
  obtain ⟨cs, cstr, length⟩ := cstring_length m0 p.toNat s string
  by_cases aligned : p.toNat % 8 = 0
  · have pre : Pre p r s.length cs m0 before :=
      { good := good, loaded := code, mem := mem, pc := pc, a0 := a0, ra := ra
        minstret := mi, tick := tick, regions := regions, align := aligned,
        cstr := cstr, hlen := length.symm }
    obtain ⟨middle, entrySteps, entered⟩ := alignedEntry pre
    obtain ⟨after, restSteps, returned⟩ := wordReturn entered.state retAlign
    exact ⟨after, entrySteps.trans restSteps, entered.then returned⟩
  · have pre : UPre p r s.length cs m0 before :=
      { good := good, loaded := code, mem := mem, pc := pc, a0 := a0, ra := ra
        minstret := mi, tick := tick, regions := regions, align := aligned,
        cstr := cstr, hlen := length.symm }
    obtain ⟨middle, headSteps, peeled⟩ := head pre
    rcases peeled.state with atReturn | ⟨off, atSetup⟩
    · obtain ⟨after, returnSteps, returned⟩ := headReturn (p := p) atReturn retAlign
      exact ⟨after, headSteps.trans returnSteps, peeled.then returned⟩
    · obtain ⟨wordHead, setupSteps, ready⟩ := setup atSetup
      obtain ⟨after, restSteps, returned⟩ := wordReturn ready.state retAlign
      exact ⟨after, headSteps.trans (setupSteps.trans restSteps), peeled.then (ready.then returned)⟩

#print axioms setup
#print axioms alignedEntry
#print axioms headReturn
#print axioms wordReturn
#print axioms run

end Vsa.Sim.StrlenRun
