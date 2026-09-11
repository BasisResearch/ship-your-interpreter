import Vsa.Sim.CallArgReturnFacts

namespace Vsa.Sim.CallArgReturn

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

/-- The recursive argument result is back at the concrete copy entry. -/
structure Pre (node base sp env : BitVec 64) (index count : Nat) (before : Config) : Prop where
  good : GoodState before.σ
  tick : before.tick < 2
  pc : before.σ.regs.get? Register.PC = some 0x80003224#64
  spReg : before.σ.regs.get? Register.x2 = some sp
  geometry : CallArgStage.Geometry node base sp index count
  saved : CallArgStage.Saved before.σ.mem sp env index count
  code : Code.Eval_exprLoaded before.σ.mem

/-- The copied argument and next loop state at either actual branch endpoint. -/
structure Post (sp env : BitVec 64) (index count : Nat) (more : Bool) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some (nextPC more)
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  regs : GHolds after.σ [(2, sp), (13, env), (16, BitVec.ofNat 64 (index + 1)), (15, BitVec.ofNat 64 count)]
  more_iff : more = true ↔ index + 1 < count
  memory : after.σ.mem = writeLog before.σ.mem (writes before.σ.mem sp index)
  copied : ∀ j, j < 24 → after.σ.mem[slot sp index + j]? = some ((before.σ.mem[sp.toNat + 64 + j]?).getD 0)
  outside : ∀ k, ¬ (slot sp index ≤ k ∧ k < slot sp index + 24) → before.σ.mem[k]? = after.σ.mem[k]?
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, AbiPreserved R = true → after.σ.regs.get? R = before.σ.regs.get? R

/-- Copy all 24 bytes, advance the index, and execute the actual loop branch. -/
theorem run {node base sp env : BitVec 64} {index count : Nat} {before : Config}
    (h : Pre node base sp env index count before) :
    ∃ after more, Steps before after ∧ Post sp env index count more before after := by
  let more := decide (index + 1 < count)
  have ix := EvalChildArm.bytesVal_ld_wordLds before.σ.mem (sp.toNat + 16) (BitVec.ofNat 64 index) h.saved.indexRead
  have len := EvalChildArm.bytesVal_ld_wordLds before.σ.mem (sp.toNat + 24) (BitVec.ofNat 64 count) h.saved.countRead
  have envValue := EvalChildArm.bytesVal_ld_wordLds before.σ.mem (sp.toNat + 8) env h.saved.envRead
  have log := CallArgReturn.log h.geometry before.σ.mem env h.saved more
  have project : GProjects (evalBlocks (seg more) (SegEvalState.init (argsReturnL sp) (loads before.σ.mem sp))).regs
      [(2, sp), (13, env), (16, BitVec.ofNat 64 (index + 1)), (15, BitVec.ofNat 64 count)] := by
    generalize more = b
    cases b <;>
      change some sp = some sp ∧ some (bytesVal .ld (EvalChildArm.wordLds8 before.σ.mem (sp.toNat + 8))) = some env ∧
        some (bytesVal .ld (EvalChildArm.wordLds8 before.σ.mem (sp.toNat + 16)) + 1#64) = some (BitVec.ofNat 64 (index + 1)) ∧
        some (bytesVal .ld (EvalChildArm.wordLds8 before.σ.mem (sp.toNat + 24))) = some (BitVec.ofNat 64 count) ∧ True
    all_goals rw [ix, len, envValue]; exact ⟨rfl, rfl, congrArg some (BitVec.ofNat_add index 1).symm, rfl, trivial⟩
  obtain ⟨vm, hvm⟩ := h.good.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed (seg more) (argsReturnL sp) (loads before.σ.mem sp)
    0x80003224#64 vm (fun k => slot sp index ≤ k ∧ k < slot sp index + 24) AbiPreserved _ before
    h.good h.pc hvm ⟨h.spReg, trivial⟩ (by change KeysOK [2]; decide)
    (facts h.geometry before.σ.mem env h.saved h.code)
    (by generalize more = b; cases b <;> change ChainOK 0x80003224#64 [2] _ <;> decide) h.tick
    (by
      intro k hk
      rw [log]
      symm
      apply writeLog_out
      simp only [writes, OutL, and_true]
      exact ⟨by omega, by omega, by omega⟩)
    (by decide) (by generalize more = b; cases b <;> decide) project
  have memory := C.mem.trans (congrArg (writeLog before.σ.mem) log)
  refine ⟨after, more, C.steps,
    { good := C.good, tick := C.tick, pc := ?_, minstret := C.minstret, regs := C.selected_regs
      more_iff := by simp [more], memory := memory
      copied := by rw [memory]; exact copied _ _ _
      outside := C.outside, output := C.output, frame := C.reg_frame }⟩
  have pc := C.pc
  generalize more = b at pc ⊢
  cases b <;> exact pc

end Vsa.Sim.CallArgReturn
