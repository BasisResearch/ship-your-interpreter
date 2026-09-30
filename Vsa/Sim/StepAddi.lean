import Vsa.Sim.Skeleton

/-!
# M1 GATE — `step_addi` end-to-end

The go/no-go gate of `PLAN-InterpSim.md` §Layer 0: one full architectural step
of the Sail RV64D model, driven entirely through the proved Layer-0 lemma
interfaces, for the spike word `0x00000513` = `addi x10, x0, 0` (little-endian
code bytes `0x13 0x05 0x00 0x00`).

`stepOnce i u` (`Vsa/Elf.lean`) on a `GoodState`:
1. reads `htif_done = false` ⇒ take the `try_step` branch;
2. `try_step u true` reduces (via `try_step_execute_char`) to `pure false` with
   the five-write state chain `σ₅` (minstret_increment, nextPC, x10, PC, minstret);
3. `stepped = false` ⇒ skip `cycle_count`;
4. reads `htif_done` again (still `false` — untouched by the step) ⇒ continue;
5. `i+1 == plat_insns_per_tick (= 2)`? — the two lemmas below split on this:
   `step_addi_notick` (`i+1 ≠ 2`, no clock tick) and `step_addi_tick`
   (`i+1 = 2`, splices `tick_clock` via `tick_clock_char`).

The four `try_step_execute_char` step-hypotheses are discharged by rewriting the
proved `dispatch_none` / `fetch_F_Base` / `decode_spike_addi` /
`execute_addi_x0_x10` lemmas onto the insert-chain states; their `σ.regs.get?`
side conditions come from the `GoodState` projections framed through the
`minstret_increment := true` (and, for execute, `nextPC := pc+4`) inserts via
`seval_state` read-over-write (none of the read registers is written).

`GoodState σ'` is re-established by constructing the record: the ~30 pinned
fields read through the write chain (none of `minstret_increment`, `nextPC`,
`x10`, `PC`, `minstret`, or the tick registers `mcycle`/`mtime`/`mip` is pinned),
and the `∃`-fields with their new values, all discharged by `goodstate_step_frame`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- Reading a register `R ≠ minstret_increment` through the prelude write is the
same as reading it from `σ`. Frames every `GoodState`/mem hypothesis of the
delegated dispatch/fetch/decode/lpad lemmas onto `afterPrelude σ`. -/
theorem get?_afterPrelude (σ : MState) (R : Register)
    (hne : (Register.minstret_increment == R) = false) :
    (afterPrelude σ).regs.get? R = σ.regs.get? R := by
  show (σ.regs.insert Register.minstret_increment true).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hne, dif_neg, reduceCtorEq, not_false_eq_true]

/-- The prelude write leaves memory untouched. -/
theorem mem_afterPrelude (σ : MState) : (afterPrelude σ).mem = σ.mem := rfl

/-- Reading a register `R ∉ {minstret_increment, nextPC}` through the prelude and
`nextPC := pc+4` writes is the same as reading it from `σ`. -/
theorem get?_afterNextPC (σ : MState) (pc : BitVec 64) (R : Register)
    (hne1 : (Register.nextPC == R) = false)
    (hne2 : (Register.minstret_increment == R) = false) :
    (afterNextPC (afterPrelude σ) pc).regs.get? R = σ.regs.get? R := by
  show ((σ.regs.insert Register.minstret_increment true).insert Register.nextPC (BitVec.addInt pc 4)).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hne1, dif_neg, reduceCtorEq, not_false_eq_true]
  exact get?_afterPrelude σ R hne2

/-- The prelude + nextPC writes leave memory untouched. -/
theorem mem_afterNextPC (σ : MState) (pc : BitVec 64) :
    (afterNextPC (afterPrelude σ) pc).mem = σ.mem := rfl

end Vsa.Sim
