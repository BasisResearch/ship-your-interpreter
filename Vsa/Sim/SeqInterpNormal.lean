import Vsa.Sim.rows.InterpBackEdgeSeg
import Vsa.Sim.Code.Interp_run
import Vsa.Sim.SegEffect
import Vsa.Sim.FrameMeta

namespace Vsa.Sim.SeqInterpNormal

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

#derive_case finalSeg chain
  []
    terminator ⟨0x80004478#64, 0x0d350463#32, 0x63#8, 0x04#8, 0x35#8, 0x0d#8,
      .br bop.BEQ false, 10, 19, 0x00c8#13, 0#21, 0#12⟩ ;;
  [(0x8000447c#64, 0xfff5051b#32)]
    terminator ⟨0x80004480#64, 0x0eaa7263#32, 0x63#8, 0x72#8, 0xaa#8, 0x0e#8,
      .br bop.BGEU false, 20, 10, 0x00e4#13, 0#21, 0#12⟩ ;;
  [(0x80004484#64, 0x00840413#32)]
    terminator ⟨0x80004488#64, 0x09240663#32, 0x63#8, 0x06#8, 0x24#8, 0x09#8,
      .br bop.BEQ true, 8, 18, 0x008c#13, 0#21, 0#12⟩

def seg (done : Bool) : List BBlock := if done then finalSeg else interpBackEdgeSeg

def input (cursor finish : BitVec 64) : GRegs :=
  interpBackEdgeL 0#64 3#64 1#64 cursor finish

def keep (R : Register) : Bool := AbiPreserved R && !(R == Register.x8)

def exitPC (done : Bool) : BitVec 64 := if done then 0x80004514#64 else 0x8000448c#64

/-- The actual normal child return and the final cursor comparison. -/
structure Pre (cursor finish : BitVec 64) (done : Bool) (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some 0x80004478#64
  minstret : ∃ w, cfg.σ.regs.get? Register.minstret = some w
  registers : GHolds cfg.σ (input cursor finish)
  branch : guardB bop.BEQ (cursor + 8#64) finish = done
  code : Code.Interp_runLoaded cfg.σ.mem

private theorem decrement :
    wvalM (mkLine 0x8000447c#64 0xfff5051b#32) [(10, 0#64)] [] =
      0xffffffffffffffff#64 := by decide

/-- Both normal routes use the same status checks and cursor increment. -/
theorem Pre.facts {cursor finish : BitVec 64} {done : Bool} {cfg : Config}
    (h : Pre cursor finish done cfg) :
    ChainFacts cfg.σ.mem cfg.σ.mem (input cursor finish) [] (seg done) := by
  cases done <;> simp only [seg, Bool.false_eq_true, if_false, if_true]
  all_goals
    chain_facts h.code with "Vsa.Sim.Code.interp_run_at_"
    · change guardB bop.BEQ 0#64 3#64 = false
      decide
    · change guardB bop.BGEU 1#64
        (wvalM (mkLine 0x8000447c#64 0xfff5051b#32) [(10, 0#64)] []) = false
      rw [decrement]
      decide
    · change guardB bop.BEQ (cursor + 8#64) finish = _
      exact h.branch

/-- The reached cursor and the exact unchanged memory of the normal route. -/
structure Post (cursor finish : BitVec 64) (done : Bool)
    (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some (exitPC done)
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  cursorReg : after.σ.regs.get? Register.x8 = some (cursor + 8#64)
  finishReg : after.σ.regs.get? Register.x18 = some finish
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, keep R = true → after.σ.regs.get? R = before.σ.regs.get? R
  count : after.steps = before.steps + 5

/-- Execute either normal branch once, retaining its frame and exact step count. -/
theorem run {cursor finish : BitVec 64} {done : Bool} {before : Config}
    (h : Pre cursor finish done before) :
    ∃ after, Steps before after ∧ Post cursor finish done before after := by
  obtain ⟨vm, hvm⟩ := h.minstret
  obtain ⟨after, result⟩ := segEval_selected_counted (seg done) (input cursor finish) []
    0x80004478#64 vm (fun _ => False) keep [(8, cursor + 8#64), (18, finish)] before
    h.good h.pc hvm h.registers (by change KeysOK [10, 19, 20, 8, 18]; decide) h.facts
    (by cases done <;> change ChainOK 0x80004478#64 [10, 19, 20, 8, 18] _ <;> decide)
    h.tick
    (by intro k _; cases done <;> rfl)
    (by decide)
    (by cases done <;> decide)
    (by
      cases done <;>
        change some (cursor + 8#64) = some (cursor + 8#64) ∧ some finish = some finish ∧ True
      all_goals exact ⟨rfl, rfl, trivial⟩)
  obtain ⟨cursorReg, finishReg, _⟩ := result.selected_regs
  refine ⟨after, result.steps,
    { good := result.good, tick := result.tick, pc := ?_, minstret := result.minstret
      cursorReg := cursorReg, finishReg := finishReg, memory := ?_, output := result.output
      frame := result.reg_frame, count := ?_ }⟩
  · cases done <;> exact result.pc
  · cases done <;> exact result.mem
  · cases done <;> exact result.count

#print axioms Pre.facts
#print axioms run

end Vsa.Sim.SeqInterpNormal
