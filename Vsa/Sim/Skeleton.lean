import Vsa.Sim.Dispatch
import Vsa.Sim.Fetch
import Vsa.Sim.Execute
import Vsa.Sim.Tick
import Vsa.Sim.GoodState

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

abbrev afterPrelude (σ : SequentialState RegisterType trivialChoiceSource) :
    SequentialState RegisterType trivialChoiceSource :=
  {σ with regs := σ.regs.insert Register.minstret_increment true}

abbrev afterNextPC (σ₁ : SequentialState RegisterType trivialChoiceSource)
    (pc : BitVec 64) : SequentialState RegisterType trivialChoiceSource :=
  {σ₁ with regs := σ₁.regs.insert Register.nextPC (BitVec.addInt pc 4)}

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

  simp only [EStateM.modifyGet, EStateM.map, EStateM.bind, ExceptT.bindCont]
  rw [show (execute ast { regs := τ.regs.insert Register.nextPC (BitVec.addInt pc 4), choiceState := τ.choiceState, mem := τ.mem, tags := τ.tags, cycleCount := τ.cycleCount, sailOutput := τ.sailOutput }) = _ from hexec]
  simp only [RETIRE_SUCCESS, EStateM.pure]

theorem try_step_execute_char
    (σ : SequentialState RegisterType trivialChoiceSource) (step_no : Nat)
    (pc npc : BitVec 64) (w : BitVec 32) (ast : instruction)
    (σ₃ : SequentialState RegisterType trivialChoiceSource)
    (vminstret : BitVec 64)

    (hpriv : σ.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hhart : σ.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()))
    (hmci : σ.regs.get? Register.mcountinhibit = some (0#32))
    (hmic : σ.regs.get? Register.minstretcfg = some (0#64))
    (hpc : σ.regs.get? Register.PC = some pc)

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

    (hhart₃ : σ₃.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()))
    (hnextPC₃ : σ₃.regs.get? Register.nextPC = some npc)
    (hinc₃ : σ₃.regs.get? Register.minstret_increment = some true)
    (hminstret₃ : σ₃.regs.get? Register.minstret = some vminstret) :
    (try_step step_no true).run σ
      = .ok false
          {(({σ₃ with regs := σ₃.regs.insert Register.PC npc}) : SequentialState RegisterType trivialChoiceSource) with
            regs := (({σ₃ with regs := σ₃.regs.insert Register.PC npc}) : SequentialState RegisterType trivialChoiceSource).regs.insert Register.minstret (BitVec.addInt vminstret 1)} := by

  have hinc := should_inc_minstret_machine σ hmci hmic
  simp only [EStateM.run] at hinc

  unfold try_step
  simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    PreSail.readReg, PreSail.writeReg, get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, hpriv]
  rw [hinc]

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

  have hrha := run_hart_active_char (afterPrelude σ) step_no pc w ast σ₃
    hpriv₁ hpc₁ hdisp hfetch hdec hlpad hexec
  simp only [EStateM.run] at hrha

  simp only [EStateM.pure, hhart₁]
  rw [hrha]

  simp only [hart_is_active, LeanRV64DExecutable.assert, PreSail.assert,
    bind, Bind.bind, EStateM.bind, EStateM.pure, pure, Pure.pure, EStateM.get,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    LeanRV64DExecutable.writeReg, Sail.ConcurrencyInterfaceV1.PreSail.writeReg,
    show σ₃.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()) from hhart₃,
    tick_pc, PreSail.readReg, PreSail.writeReg, get, getThe, MonadStateOf.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    pc_write_callback, get_arch_pc,
    get_config_rvfi, hnextPC₃, if_true]

  have hPCPC : (Register.PC == Register.PC) = true := by decide
  simp only [hPCPC, dif_pos, Std.ExtDHashMap.get?_insert,
    show (Register.PC == Register.minstret_increment) = false from by decide,
    show (Register.PC == Register.minstret) = false from by decide,
    dif_neg, not_false_eq_true, hinc₃, hminstret₃,
    Bool.and_true, if_true, Bool.false_eq_true, if_false,
    EStateM.pure, EStateM.bind, EStateM.get, EStateM.modifyGet]

end Vsa.Sim
