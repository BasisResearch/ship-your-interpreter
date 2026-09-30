import Vsa.Sim.Skeleton
import Vsa.Sim.StepAddi

/-!
# M2 branch-class validation — `step_beq` for a concrete BGEU

Step-characterization for the concrete branch word `0x0062f863`
(`bgeu t0, t1, +16` = `bgeu x5, x6, +16`, taken from `_start` at
`0x8000001c`, disassembly at `experiments/disasm.txt:15`). This validates
the generalized `try_step` skeleton (`hnextPC₃ = some npc`) on the control-flow
class: the two source GPRs (`t0 = x5`, `t1 = x6`), the two branch outcomes
(taken ⇒ `nextPC := pc + sext 16` via `jump_to`/`set_next_pc`; not-taken ⇒
`nextPC := pc + 4` unchanged from the `run_hart_active` prelude write), and the
skeleton's PC-insert following the branch-chosen `nextPC`.

Pipeline (mirrors the ADDI pipeline of `StepAddi.lean`):
1. `decode_bgeu_t0_t1` — decode `0x0062f863` ⇒ `BTYPE (16, x6, x5, BGEU)`.
2. `rX_bits_x5` / `rX_bits_x6` — the two source GPR reads.
3. `execute_bgeu_taken` / `execute_bgeu_nottaken` — the BTYPE execute clause,
   both outcomes. The taken clause reads `PC` (for the target) and `misa` (the
   forced `Ext_Zca` read inside `jump_to`), and writes `nextPC := pc + sext 16`
   via `set_next_pc`; the not-taken clause leaves state untouched.
4. `try_step_beq_taken` / `try_step_beq_nottaken` — the skeleton instantiations.

The `+16` offset target is 4-aligned (so `jump_to`'s `assert target[0]==0` and the
`pc[1]`-guarded misaligned-fetch check both discharge from `pc.toNat % 4 = 0`).
The GPR values are universally quantified with the comparison outcome
(`zopz0zKzJ_u v1 v2`, i.e. `t0 ≥u t1`) taken as a hypothesis.

Reuses `StepAddi`'s frame helpers (`get?_afterPrelude`, `get?_afterNextPC`,
`mem_afterPrelude`, `mem_afterNextPC`) via the `Vsa.Sim.StepAddi` import.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Decode -/

/-! ## Source GPR reads (`t0 = x5`, `t1 = x6`) -/

/-- `x5` (`t0`) reads the pinned value, touching no state. -/
theorem rX_bits_x5 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x5 = some v) :
    (rX_bits (regidx.Regidx 0x05#5)).run σ = .ok v σ := by
  simp only [rX_bits, rX, PreSail.readReg, bind, EStateM.bind, pure, EStateM.pure,
    EStateM.run, get, getThe, MonadStateOf.get, EStateM.get,
    regval_from_reg, Sail.BitVec.toNatInt,
    Int.ofNat_eq_natCast, Int.toNat_natCast, BitVec.reduceToNat, h]

/-- `x6` (`t1`) reads the pinned value, touching no state. -/
theorem rX_bits_x6 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x6 = some v) :
    (rX_bits (regidx.Regidx 0x06#5)).run σ = .ok v σ := by
  simp only [rX_bits, rX, PreSail.readReg, bind, EStateM.bind, pure, EStateM.pure,
    EStateM.run, get, getThe, MonadStateOf.get, EStateM.get,
    regval_from_reg, Sail.BitVec.toNatInt,
    Int.ofNat_eq_natCast, Int.toNat_natCast, BitVec.reduceToNat, h]

/-! ## Branch target alignment -/

/-! ## Execute characterization of the BTYPE clause (both outcomes) -/

/-! ## Byte/word facts for the fetch path -/

/-! ## The skeleton's `σ₃` for each branch outcome -/

/-! ## Shared discharge of the skeleton's instruction-generic hypotheses

`dispatch` / `fetch` / `decode` / `lpad` run on `afterPrelude σ` and are identical
for any word at a good pc; only the code bytes and the decoded `ast` differ from
ADDI. These four `have`s are reproduced inline in each step lemma (the fetch
bytes are the BGEU bytes `0x63 0xf8 0x62 0x00`). -/

/-! ## `Machine.Step` wrappers (no clock tick) with `GoodState` preservation

The branch write-set is `{minstret_increment, nextPC, PC, minstret}` — note no GPR
`rd` is written (branches have no destination register), so unlike ADDI there is
no `x10` key. The taken/not-taken final states differ in shape (the taken `σ₃`
carries an extra `nextPC := target` insert), so each outcome gets its own
`sigmaPost`, frame lemma, and `GoodState`/`htif_done` re-establishment. -/

/-! ## `stepOnce` and `Machine.Step` (no clock tick) -/

end Vsa.Sim
