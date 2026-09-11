import Vsa.Sim.SeqBlockExit
import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.SegEffect
import Vsa.Sim.FrameMeta
import Vsa.Sim.Code.FixedImage_Exec_stmt

namespace Vsa.Sim.SeqBlockAbrupt

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

#derive_case seg chain
  []
    terminator ⟨0x800041c8#64, 0xec051ae3#32, 0xe3#8, 0x1a#8, 0x05#8, 0xec#8,
      .br bop.BNE true, 10, 0, 0x1ed4#13, 0#21, 0#12⟩

/-- Every non-normal child takes the block's status exit without changing memory. -/
theorem run (status : Status) (before : Config) (abrupt : status ≠ .normal)
    (good : GoodState before.σ) (tick : before.tick < 2)
    (pc : before.σ.regs.get? Register.PC = some 0x800041c8#64)
    (minstret : ∃ w, before.σ.regs.get? Register.minstret = some w)
    (statusReg : before.σ.regs.get? Register.x10 = some (StatusCode status))
    (code : Code.Exec_stmtLoaded before.σ.mem) :
    ∃ after, Steps before after ∧ SeqBlockExitRoute status before after := by
  have facts : ChainFacts before.σ.mem before.σ.mem [(10, StatusCode status)] [] seg := by
    chain_facts code with "Vsa.Sim.Code.exec_stmt_at_"
    change guardB bop.BNE (StatusCode status) 0#64 = true
    cases status with
    | normal => exact False.elim (abrupt rfl)
    | brk => decide
    | cont => decide
    | ret v =>
      change guardB bop.BNE 3#64 0#64 = true
      decide
  obtain ⟨vm, hvm⟩ := minstret
  obtain ⟨after, C⟩ := segEval_selected_framed seg [(10, StatusCode status)] []
    0x800041c8#64 vm (fun _ => False) AbiPreserved [(10, StatusCode status)] before
    good pc hvm ⟨statusReg, trivial⟩ (by change KeysOK [10]; decide) facts
    (by change ChainOK 0x800041c8#64 [10] seg; decide) tick
    (by intro k _; rfl) (by decide) (by decide) (by exact ⟨rfl, trivial⟩)
  obtain ⟨status', _⟩ := C.selected_regs
  exact ⟨after, C.steps, C.good, C.tick, C.pc, status', C.minstret, C.mem, C.output, C.reg_frame⟩

#print axioms run

end Vsa.Sim.SeqBlockAbrupt
