import Vsa.Sim.ClosureCallPrefixFacts
import Vsa.Sim.ClosureCallSites
import Vsa.Sim.BridgeSegFull
import Vsa.Sim.InterpSpillReads

namespace Vsa.Sim.ClosureCallPrefix

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- Reached closure dispatch, with the represented callee and actual argument count. -/
structure Pre (sp call object fn interp parent a3 saved5 saved3 : BitVec 64)
    (count depth : Nat) (before : Config) : Prop where
  good : GoodState before.σ
  tick : before.tick < 2
  pc : before.σ.regs.get? Register.PC = some 0x80003254#64
  minstret : ∃ w, before.σ.regs.get? Register.minstret = some w
  regs : GHolds before.σ
    (callClosureDispatchStageL sp call a3 (BitVec.ofNat 64 count) interp saved5 saved3)
  geometry : Geometry sp call object fn interp
  reads : Reads before.σ.mem sp object fn interp count depth
  parentRead : read64 before.σ.mem (object.toNat + 8) = some parent.toNat
  code : Code.Eval_exprLoaded before.σ.mem

def footprint (sp interp : BitVec 64) (k : Nat) : Prop :=
  (sp.toNat ≤ k ∧ k < sp.toNat + 8) ∨
  (sp.toNat + 120 ≤ k ∧ k < sp.toNat + 144) ∨
  (sp.toNat + 1032 ≤ k ∧ k < sp.toNat + 1040) ∨
  (sp.toNat + 1048 ≤ k ∧ k < sp.toNat + 1056) ∨
  (interp.toNat + 8 ≤ k ∧ k < interp.toNat + 12)

/-- The actual scope-allocation call retains the spills needed by the closure return. -/
structure Post (sp call object fn interp parent saved5 saved3 : BitVec 64)
    (count depth : Nat) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some 0x800029fc#64
  ra : after.σ.regs.get? Register.x1 = some 0x800032c0#64
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  regs : GHolds after.σ [(10, parent), (2, sp), (8, call), (13, object),
    (15, BitVec.ofNat 64 count), (18, interp), (19, saved3), (21, fn),
    (23, bytesVal .lw (wordLds4 before.σ.mem (call.toNat + 4)))]
  memory : after.σ.mem = writeLog before.σ.mem
    (writes before.σ.mem sp object interp saved5 saved3 count depth)
  countRead : read64 after.σ.mem sp.toNat = some count
  saved5Read : read64 after.σ.mem (sp.toNat + 1032) = some saved5.toNat
  saved3Read : read64 after.σ.mem (sp.toNat + 1048) = some saved3.toNat
  outside : ∀ k, ¬ footprint sp interp k → before.σ.mem[k]? = after.σ.mem[k]?
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, (∀ r ∈ noiseRegs, (r == R) = false) →
    (∀ n ∈ wrChain callClosureDispatchStageSeg, (gprReg n == R) = false) →
    (Register.x1 == R) = false → after.σ.regs.get? R = before.σ.regs.get? R

/-- Execute closure dispatch and the generated JAL into scope allocation. -/
theorem run {sp call object fn interp parent a3 saved5 saved3 : BitVec 64}
    {count depth : Nat} {before : Config}
    (h : Pre sp call object fn interp parent a3 saved5 saved3 count depth before) :
    ∃ after, Steps before after ∧
      Post sp call object fn interp parent saved5 saved3 count depth before after := by
  let L := callClosureDispatchStageL sp call a3 (BitVec.ofNat 64 count) interp saved5 saved3
  let lds := loads before.σ.mem sp call object fn interp
  have F := facts before.σ.mem sp call object fn interp a3 saved5 saved3 count depth
    h.geometry h.reads h.code
  have registerEq := regs (call := call) h.reads a3 saved5 saved3
  have logEq := log h.geometry h.reads a3 saved5 saved3
  obtain ⟨after, C⟩ := bridgeOfSegFull callClosureDispatchStageSeg L lds
    0x80003254#64 0x800029fc#64 0x800032c0#64 before h.good h.pc h.minstret h.tick h.regs
    (by change KeysOK [2, 8, 13, 15, 18, 21, 19]; decide) F
    (by change ChainOK 0x80003254#64 [2, 8, 13, 15, 18, 21, 19] callClosureDispatchStageSeg; decide)
    (by rw [registerEq]; change KeysOK [10, 14, 12, 21, 23, 11, 16, 13, 2, 8, 15, 18, 19]; decide)
    (by rw [registerEq]; change ∀ n ∈ ([10, 14, 12, 21, 23, 11, 16, 13, 2, 8, 15, 18, 19] : List Nat), n ≠ 1; decide)
    (by
      intro middle good tick pc minstret memory _
      have mem := memory.trans (congrArg (writeLog before.σ.mem) logEq)
      have code : Code.Eval_exprLoaded middle.σ.mem := by
        apply loaded_eval_expr_agreeP before.σ.mem middle.σ.mem _ h.code
        intro k hk
        rw [mem]
        symm
        apply writeLog_out
        simp only [writes, OutL, and_true]
        have := h.geometry.stackHtif
        have := h.geometry.interpAbove
        have : 0x80003fe0 ≤ tohostAddr := by decide
        exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      obtain ⟨vm, hvm⟩ := minstret
      obtain ⟨next, parity, step, tick', good', mem', obs⟩ :=
        site_800032bc_closureCall middle.σ middle.tick middle.steps 0x800032bc#64 vm
          good pc hvm code rfl tick
      exact ⟨⟨next, parity, middle.steps + 1⟩,
        jalCallFacts_of_obs step tick' good' mem' obs (by decide)⟩)
  have memory := C.mem.trans (congrArg (writeLog before.σ.mem) logEq)
  have selected : GHolds after.σ (registers before.σ.mem sp call object fn interp saved3 count depth) :=
    registerEq ▸ C.registers
  refine ⟨after, C.run,
    { good := C.good, tick := C.tick, pc := C.pc, ra := C.ra, minstret := C.minstret
      regs := ?_, memory := memory, countRead := ?_, saved5Read := ?_, saved3Read := ?_
      outside := ?_, output := C.output, frame := C.frame }⟩
  · apply gholds_selected (hregs := selected)
    have value := EvalChildArm.bytesVal_ld_wordLds before.σ.mem (object.toNat + 8) parent h.parentRead
    simp [GProjects, registers, lookupG, value]
  · rw [memory]
    have bound : count < 2^64 := by have := h.reads.countBound; omega
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] using
      read64_of_writeLog_at before.σ.mem (writes before.σ.mem sp object interp saved5 saved3 count depth)
        6 sp.toNat (BitVec.ofNat 64 count) rfl (by simp [writes, OutLRange])
  · rw [memory]
    apply read64_of_writeLog_at before.σ.mem (writes before.σ.mem sp object interp saved5 saved3 count depth) 3
      (sp.toNat + 1032) saved5 rfl
    simp only [writes, List.drop, OutLRange, and_true]
    have := h.geometry.interpAbove
    exact ⟨by omega, by omega, by omega⟩
  · rw [memory]
    apply read64_of_writeLog_at before.σ.mem (writes before.σ.mem sp object interp saved5 saved3 count depth) 5
      (sp.toNat + 1048) saved3 rfl
    simp only [writes, List.drop, OutLRange, and_true]
    omega
  · intro k hk
    rw [memory]
    symm
    apply writeLog_out
    simp only [writes, OutL, and_true]
    unfold footprint at hk
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

end Vsa.Sim.ClosureCallPrefix
