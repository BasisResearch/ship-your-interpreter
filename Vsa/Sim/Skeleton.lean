import Vsa.Sim.Dispatch
import Vsa.Sim.Fetch
import Vsa.Sim.Decode
import Vsa.Sim.Execute
import Vsa.Sim.Hooks
import Vsa.Sim.Tick
import Vsa.Sim.GoodState
import Vsa.Sim.StateNF

/-!
# Layer 0, item 3 — the `try_step` skeleton lemma

`try_step_execute_char` — the reusable characterization of one architectural
step on the M-mode / HART_ACTIVE / retire-success hot path
(`PLAN-InterpSim.md` §Layer 0 item 3). Every M2 instruction-class lemma
instantiates this so the common `try_step` prelude/postlude is paid **once**,
not per instruction.

## What `try_step` does on the hot path (`Step.lean:398`)

1. `ext_pre_step_hook ()` — pure no-op.
2. `writeReg minstret_increment (← should_inc_minstret (← readReg cur_privilege))`
   — the FIRST state write. On the pinned control state
   `should_inc_minstret Machine = true`, so this yields
   `σ₁ := {σ with regs := σ.regs.insert minstret_increment true}`.
   Everything downstream runs on `σ₁`.
3. `match ← readReg hart_state` — `HART_ACTIVE` ⇒ `run_hart_active`:
   - `dispatchInterrupt (← readReg cur_privilege) = none` (interrupts dead).
   - `ext_fetch_hook (← fetch ()) = F_Base w` (the fetch lemma).
   - `sail_instr_announce`/`fetch_callback` — pure no-ops.
   - `ext_decode w = ast`.
   - `get_config_print_instr () = false`.
   - `is_landing_pad_expected () && not (is_lpad_instruction ast)` — `false`
     (elp = 0), so the CFI trap is skipped.
   - `writeReg nextPC (BitVec.addInt (← readReg PC) 4)` — SECOND write, reads
     `PC` from `σ₁`, giving `σ₂ := {σ₁ with regs := σ₁.regs.insert nextPC (addInt pc 4)}`.
   - `execute ast = RETIRE_SUCCESS` with the instruction's own state update ⇒ `σ₃`.
   - returns `Step_Execute (Retire_Success (), instbits)`.
4. Back in `try_step`: the `Step_Execute (Retire_Success (), _)` arm asserts
   `hart_is_active (← readReg hart_state)`; `hart_state` still reads `HART_ACTIVE`
   from `σ₃` (execute doesn't touch it) so the assert reduces to `pure ()`.
5. Final `match ← readReg hart_state` — `HART_ACTIVE`:
   - `tick_pc ()` — `writeReg PC (← readReg nextPC)`; reads `nextPC` from `σ₃`
     (= `addInt pc 4`) ⇒ `σ₄ := {σ₃ with regs := σ₃.regs.insert PC (addInt pc 4)}`.
   - `retired := true`.
   - `if retired && (← readReg minstret_increment) then writeReg minstret (addInt (← readReg minstret) 1)`;
     `minstret_increment` reads `true` from `σ₄` ⇒ FIFTH write
     `σ₅ := {σ₄ with regs := σ₄.regs.insert minstret (addInt vminstret 1)}`.
   - `get_config_rvfi () = false`; `ext_post_step_hook`/`instret_callback` no-ops.
   - `pure false`.

## Design: where the hypotheses live

The prelude/postlude are *fully generic* — they read only control-plane
registers (`cur_privilege`, `hart_state`, `minstret_increment`, `nextPC`,
`minstret`) plus the pinned counters `should_inc_minstret` consults. Those are
taken as explicit `σ.regs.get? R = …` facts on the **original** `σ`, and the
framing through the `minstret_increment`/`nextPC` inserts is discharged
internally by `seval_state` read-over-write.

The instruction-specific work — `dispatchInterrupt`, `fetch`, `decode`,
`is_landing_pad_expected`, `execute` — is delegated to the caller through four
`.run`-form hypotheses, each stated at the state the model actually evaluates it
on (`σ₁` for dispatch/fetch/decode/lpad; `σ₂` for execute). This keeps the
skeleton instruction-generic: `StepAddi` supplies these by rewriting the proved
`dispatch_none`/`fetch_F_Base`/`decode_spike_addi`/`execute_addi_x0_x10` lemmas
onto the insert-chain states (framing via `seval_state`).

`σ₃` (execute's output) is left abstract; the caller supplies the final
`minstret`/`nextPC` read-back facts on it as `hnextPC₃`/`hminstret₃`/`hhart₃`,
which for the concrete instruction discharge by projecting through its state
update with `seval_state`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- The state after the `minstret_increment := true` prelude write. -/
abbrev afterPrelude (σ : SequentialState RegisterType trivialChoiceSource) :
    SequentialState RegisterType trivialChoiceSource :=
  {σ with regs := σ.regs.insert Register.minstret_increment true}

/-- The state after the `nextPC := pc+4` write in `run_hart_active` (over `σ₁`). -/
abbrev afterNextPC (σ₁ : SequentialState RegisterType trivialChoiceSource)
    (pc : BitVec 64) : SequentialState RegisterType trivialChoiceSource :=
  {σ₁ with regs := σ₁.regs.insert Register.nextPC (BitVec.addInt pc 4)}

/--
**`run_hart_active` characterization.** On the M-mode / retire-success hot path,
`run_hart_active step_no` reads `cur_privilege` (⇒ dispatch none), fetches
`F_Base w`, decodes `ast`, writes `nextPC := pc+4`, executes `ast` to
`RETIRE_SUCCESS` yielding `σ₃`, and returns `Step_Execute (Retire_Success (), instbits)`
with `instbits = zero_extend (m:=32) w`. The dispatch/fetch/decode/lpad/execute
steps are delegated as `.run`-form hypotheses on the state they run on. -/
theorem run_hart_active_char
    (τ : SequentialState RegisterType trivialChoiceSource) (step_no : Nat)
    (pc : BitVec 64) (w : BitVec 32) (ast : instruction)
    (σ₃ : SequentialState RegisterType trivialChoiceSource)
    (hpriv : τ.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hpc : τ.regs.get? Register.PC = some pc)
    (hdisp : (dispatchInterrupt Privilege.Machine).run τ = .ok none τ)
    (hfetch : (fetch ()).run τ = .ok (FetchResult.F_Base w) τ)
    (hdec : (ext_decode w).run τ = .ok ast τ)
    (hlpad : (is_landing_pad_expected ()).run τ = .ok false τ)
    (hexec : (execute ast).run (afterNextPC τ pc) = .ok RETIRE_SUCCESS σ₃) :
    (run_hart_active step_no).run τ
      = .ok (Step.Step_Execute
          (ExecutionResult.Retire_Success (), (zero_extend (m := 32) w : instbits))) σ₃ := by
  simp only [EStateM.run] at hdisp hfetch hdec hlpad hexec
  unfold run_hart_active
  simp only [ext_fetch_hook, get_config_print_instr, is_lpad_instruction,
    LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, EStateM.pure, pure,
    PreSail.readReg, PreSail.writeReg, get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, hpriv]
  rw [hdisp]
  simp only [EStateM.bind, EStateM.pure, ExceptT.bindCont, EStateM.map]
  rw [hfetch]
  simp only [EStateM.bind, ExceptT.bindCont, EStateM.map]
  rw [hdec]
  simp only [EStateM.bind, EStateM.pure, ExceptT.bindCont, EStateM.map,
    Bool.false_eq_true, if_false]
  rw [hlpad]
  simp only [EStateM.bind, EStateM.pure, ExceptT.bindCont, EStateM.map,
    Bool.false_and, Bool.false_eq_true, if_false, EStateM.get, hpc]
  -- reduce the `nextPC := pc+4` modifyGet to `afterNextPC τ pc`, then execute
  simp only [EStateM.modifyGet, EStateM.map, EStateM.bind, ExceptT.bindCont]
  rw [show (execute ast { regs := τ.regs.insert Register.nextPC (BitVec.addInt pc 4), choiceState := τ.choiceState, mem := τ.mem, tags := τ.tags, cycleCount := τ.cycleCount, sailOutput := τ.sailOutput }) = _ from hexec]
  simp only [RETIRE_SUCCESS, EStateM.pure]

/--
**The `try_step` skeleton lemma (Layer 0, item 3).**

`try_step step_no true` on the M-mode / HART_ACTIVE / retire-success hot path
reduces to `pure false` with the explicit five-write state chain

  σ  --minstret_increment:=true-->  σ₁
     --nextPC:=pc+4-->              σ₂
     --(execute ast)-->            σ₃
     --PC:=pc+4-->                 σ₄
     --minstret:=addInt vminstret 1--> σ₅

The instruction-specific steps (dispatch, fetch, decode, lpad, execute) are
supplied as `.run`-form hypotheses at the states the model evaluates them on.
-/
theorem try_step_execute_char
    (σ : SequentialState RegisterType trivialChoiceSource) (step_no : Nat)
    (pc npc : BitVec 64) (w : BitVec 32) (ast : instruction)
    (σ₃ : SequentialState RegisterType trivialChoiceSource)
    (vminstret : BitVec 64)
    -- prelude control-plane facts (on σ)
    (hpriv : σ.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hhart : σ.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()))
    (hmci : σ.regs.get? Register.mcountinhibit = some (0#32))
    (hmic : σ.regs.get? Register.minstretcfg = some (0#64))
    (hpc : σ.regs.get? Register.PC = some pc)
    -- instruction-specific steps, each at the state the model runs it on
    (hdisp : (dispatchInterrupt Privilege.Machine).run (afterPrelude σ)
      = .ok none (afterPrelude σ))
    (hfetch : (fetch ()).run (afterPrelude σ)
      = .ok (FetchResult.F_Base w) (afterPrelude σ))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok ast (afterPrelude σ))
    (hlpad : (is_landing_pad_expected ()).run (afterPrelude σ)
      = .ok false (afterPrelude σ))
    (hexec : (execute ast).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ₃)
    -- postlude read-back facts on σ₃
    (hhart₃ : σ₃.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()))
    (hnextPC₃ : σ₃.regs.get? Register.nextPC = some npc)
    (hinc₃ : σ₃.regs.get? Register.minstret_increment = some true)
    (hminstret₃ : σ₃.regs.get? Register.minstret = some vminstret) :
    (try_step step_no true).run σ
      = .ok false
          {(({σ₃ with regs := σ₃.regs.insert Register.PC npc}) : SequentialState RegisterType trivialChoiceSource) with
            regs := (({σ₃ with regs := σ₃.regs.insert Register.PC npc}) : SequentialState RegisterType trivialChoiceSource).regs.insert Register.minstret (BitVec.addInt vminstret 1)} := by
  -- `should_inc_minstret Machine = true` on σ (the prelude write value)
  have hinc := should_inc_minstret_machine σ hmci hmic
  simp only [EStateM.run] at hinc
  -- unfold try_step and peel the prelude
  unfold try_step
  simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    PreSail.readReg, PreSail.writeReg, get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, hpriv]
  rw [hinc]
  -- now on afterPrelude σ; read hart_state ⇒ HART_ACTIVE ⇒ run_hart_active
  -- afterPrelude σ read-backs for control-plane registers
  have hhart₁ : (afterPrelude σ).regs.get? Register.hart_state
      = some (HartState.HART_ACTIVE ()) := by
    show (σ.regs.insert Register.minstret_increment true).get? Register.hart_state = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.minstret_increment == Register.hart_state) = false from by decide,
      dif_neg, reduceCtorEq, not_false_eq_true, hhart]
  have hpriv₁ : (afterPrelude σ).regs.get? Register.cur_privilege
      = some Privilege.Machine := by
    show (σ.regs.insert Register.minstret_increment true).get? Register.cur_privilege = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.minstret_increment == Register.cur_privilege) = false from by decide,
      dif_neg, reduceCtorEq, not_false_eq_true, hpriv]
  have hpc₁ : (afterPrelude σ).regs.get? Register.PC = some pc := by
    show (σ.regs.insert Register.minstret_increment true).get? Register.PC = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.minstret_increment == Register.PC) = false from by decide,
      dif_neg, reduceCtorEq, not_false_eq_true, hpc]
  -- run_hart_active on afterPrelude σ
  have hrha := run_hart_active_char (afterPrelude σ) step_no pc w ast σ₃
    hpriv₁ hpc₁ hdisp hfetch hdec hlpad hexec
  simp only [EStateM.run] at hrha
  -- reduce the prelude bind (`.ok true σ`), read hart_state (⇒ HART_ACTIVE) and
  -- fold `run_hart_active` on `afterPrelude σ`
  simp only [EStateM.pure, hhart₁]
  rw [hrha]
  -- the Step_Execute (Retire_Success, _) arm: assert hart_is_active (reads σ₃'s
  -- hart_state = HART_ACTIVE) ⇒ pure (); then the final hart_state match ⇒ HART_ACTIVE:
  -- tick_pc (PC := nextPC = pc+4), then minstret += 1 (retired ∧ minstret_increment).
  simp only [hart_is_active, LeanRV64DExecutable.assert, PreSail.assert,
    bind, Bind.bind, EStateM.bind, EStateM.pure, pure, Pure.pure, EStateM.get,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    LeanRV64DExecutable.writeReg, Sail.ConcurrencyInterfaceV1.PreSail.writeReg,
    show σ₃.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()) from hhart₃,
    tick_pc, PreSail.readReg, PreSail.writeReg, get, getThe, MonadStateOf.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    pc_write_callback, get_arch_pc,
    get_config_rvfi, hnextPC₃, if_true]
  -- `pc_write_callback (← readReg PC)` reads PC back (= pc+4) then discards it;
  -- read `minstret_increment` (= true) ⇒ retire branch; read `minstret` back
  -- (PC ≠ minstret) ⇒ minstret += 1; rvfi off ⇒ `pure false`.
  have hPCPC : (Register.PC == Register.PC) = true := by decide
  simp only [hPCPC, dif_pos, Std.ExtDHashMap.get?_insert,
    show (Register.PC == Register.minstret_increment) = false from by decide,
    show (Register.PC == Register.minstret) = false from by decide,
    dif_neg, not_false_eq_true, hinc₃, hminstret₃,
    Bool.and_true, if_true, Bool.false_eq_true, if_false,
    EStateM.pure, EStateM.bind, EStateM.get, EStateM.modifyGet]

end Vsa.Sim
