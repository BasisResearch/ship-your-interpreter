import Vsa.Sim.Fetch
import Vsa.Sim.InitValues
import Vsa.Sim.RegAccess

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem update_elp_state_noop (σ : SequentialState RegisterType trivialChoiceSource)
    (rs1 : regidx)
    (hpriv : σ.regs.get? Register.cur_privilege = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg = some ((0#64) : RegisterType Register.mseccfg)) :
    (update_elp_state rs1).run σ = .ok () σ := by
  simp only [update_elp_state]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg]
  simp only [show bool_bit_backwards (_get_Seccfg_MLPE (0#64)) = false from by decide,
    Bool.false_eq_true, if_false, EStateM.pure]

theorem get_next_pc_char (σ : SequentialState RegisterType trivialChoiceSource)
    (link : BitVec 64) (h : σ.regs.get? Register.nextPC = some link) :
    (get_next_pc ()).run σ = .ok link σ := by
  simp only [get_next_pc, PreSail.readReg, bind, EStateM.bind, pure, EStateM.pure,
    EStateM.run, get, getThe, MonadStateOf.get, EStateM.get, h]

theorem execute_jal_char
    (imm : BitVec 21) (rd : regidx) (link pc : BitVec 64)
    (vmisa : RegisterType Register.misa)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hnpc : σ.regs.get? Register.nextPC = some link)
    (hpc : σ.regs.get? Register.PC = some pc)
    (hmisa : σ.regs.get? Register.misa = some vmisa)
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hwr : (wX_bits rd link).run
        {σ with regs := σ.regs.insert Register.nextPC (pc + sign_extend (m := 64) imm)}
        = .ok () σ') :
    (execute (instruction.JAL (imm, rd))).run σ = .ok RETIRE_SUCCESS σ' := by
  have hlink := get_next_pc_char σ link hnpc
  simp only [EStateM.run] at hlink hwr
  have hb0 := access_bit0 _ htgt
  have hb1 := access_bit1 _ htgt
  have hzca := currentlyEnabled_Zca σ vmisa hmisa
  simp only [EStateM.run] at hzca
  simp only [execute, execute_JAL, EStateM.run, bind, EStateM.bind, pure]
  rw [hlink]
  simp only [bind, EStateM.bind, PreSail.readReg, get, getThe,
    MonadStateOf.get, EStateM.get, hpc]
  unfold jump_to
  simp only [ext_control_check_pc, LeanRV64DExecutable.SailME.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.bind, EStateM.pure, pure, Pure.pure]
  simp only [LeanRV64DExecutable.assert, PreSail.assert, hb0, beq_self_eq_true, if_true,
    EStateM.bind, EStateM.pure, EStateM.map, ExceptT.bindCont, pure, Pure.pure]
  rw [hzca, hb1, show bit_to_bool (0#1 : BitVec 1) = false from rfl]
  simp only [Bool.false_and, Bool.false_eq_true, if_false,
    set_next_pc, redirect_callback, PreSail.writeReg,
    Bind.bind, EStateM.bind, EStateM.pure, EStateM.map, ExceptT.bindCont, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, pure, Pure.pure]
  simp only [RETIRE_SUCCESS, EStateM.bind, EStateM.pure]
  rw [hwr]

theorem execute_jalr_char
    (imm : BitVec 12) (rs1 rd : regidx) (link vrs1 : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hmisa : σ.regs.get? Register.misa = some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg = some ((0#64) : RegisterType Register.mseccfg))
    (hnpc : σ.regs.get? Register.nextPC = some link)
    (hrs1 : (rX_bits rs1).run σ = .ok vrs1 σ)
    (htgt : (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1).toNat % 4 = 0)
    (hwr : (wX_bits rd link).run
        {σ with regs := σ.regs.insert Register.nextPC (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)}
        = .ok () σ') :
    (execute (instruction.JALR (imm, rs1, rd))).run σ = .ok RETIRE_SUCCESS σ' := by
  have help := update_elp_state_noop σ rs1 hpriv hsec
  have hlink := get_next_pc_char σ link hnpc
  simp only [EStateM.run] at help hlink hrs1 hwr
  have hb0 := access_bit0 _ htgt
  have hb1 := access_bit1 _ htgt
  have hzca := currentlyEnabled_Zca σ _ hmisa
  simp only [EStateM.run] at hzca
  simp only [execute, execute_JALR, EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
    help, hlink, hrs1]
  unfold jump_to
  simp only [ext_control_check_pc, LeanRV64DExecutable.SailME.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.bind, EStateM.pure, pure, Pure.pure]
  simp only [LeanRV64DExecutable.assert, PreSail.assert, hb0, beq_self_eq_true, if_true,
    EStateM.bind, EStateM.pure, EStateM.map, ExceptT.bindCont, pure, Pure.pure]
  rw [hzca, hb1, show bit_to_bool (0#1 : BitVec 1) = false from rfl]
  simp only [Bool.false_and, Bool.false_eq_true, if_false,
    set_next_pc, redirect_callback, PreSail.writeReg,
    Bind.bind, EStateM.bind, EStateM.pure, EStateM.map, ExceptT.bindCont, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, pure, Pure.pure]
  simp only [RETIRE_SUCCESS, EStateM.bind, EStateM.pure]
  rw [hwr]

theorem execute_jal_x0_char
    (imm : BitVec 21) (link pc : BitVec 64)
    (vmisa : RegisterType Register.misa)
    (σ : SequentialState RegisterType trivialChoiceSource)
    (hnpc : σ.regs.get? Register.nextPC = some link)
    (hpc : σ.regs.get? Register.PC = some pc)
    (hmisa : σ.regs.get? Register.misa = some vmisa)
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0) :
    (execute (instruction.JAL (imm, regidx.Regidx 0x00#5))).run σ
      = .ok RETIRE_SUCCESS
          {σ with regs := σ.regs.insert Register.nextPC (pc + sign_extend (m := 64) imm)} :=
  execute_jal_char imm (regidx.Regidx 0x00#5) link pc vmisa σ _ hnpc hpc hmisa htgt
    (wX_bits_zero _ link)

theorem execute_jalr_x0_char
    (imm : BitVec 12) (rs1 : regidx) (link vrs1 : BitVec 64)
    (σ : SequentialState RegisterType trivialChoiceSource)
    (hmisa : σ.regs.get? Register.misa = some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg = some ((0#64) : RegisterType Register.mseccfg))
    (hnpc : σ.regs.get? Register.nextPC = some link)
    (hrs1 : (rX_bits rs1).run σ = .ok vrs1 σ)
    (htgt : (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1).toNat % 4 = 0) :
    (execute (instruction.JALR (imm, rs1, regidx.Regidx 0x00#5))).run σ
      = .ok RETIRE_SUCCESS
          {σ with regs := σ.regs.insert Register.nextPC (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)} :=
  execute_jalr_char imm rs1 (regidx.Regidx 0x00#5) link vrs1 σ _ hmisa hpriv hsec hnpc hrs1 htgt
    (wX_bits_zero _ link)

end Vsa.Sim
