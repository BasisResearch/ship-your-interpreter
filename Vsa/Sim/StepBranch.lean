import Vsa.Sim.Skeleton
import Vsa.Sim.Retire
import Vsa.Sim.StepAddi
import Vsa.Sim.StepBeq
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.Frame

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

abbrev sigma3_branch_taken (σ : MState) (pc : BitVec 64) (imm : BitVec 13) : MState :=
  {(afterNextPC (afterPrelude σ) pc) with
    regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
      (pc + sign_extend (m := 64) imm)}

abbrev sigma3_branch_nottaken (σ : MState) (pc : BitVec 64) : MState :=
  afterNextPC (afterPrelude σ) pc

theorem execute_btype_bgeu_taken
    (imm : BitVec 13) (rs1 rs2 : regidx) (v1 v2 pc : BitVec 64)
    (vmisa : RegisterType Register.misa)
    (σ : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hpc : σ.regs.get? Register.PC = some pc)
    (hmisa : σ.regs.get? Register.misa = some vmisa)
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hv : zopz0zKzJ_u v1 v2 = true) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BGEU))).run σ
      = .ok RETIRE_SUCCESS
          {σ with regs := σ.regs.insert Register.nextPC (pc + sign_extend (m := 64) imm)} := by
  simp only [EStateM.run] at hrs1 hrs2
  have hb0 := access_bit0 _ htgt
  have hb1 := access_bit1 _ htgt
  have hzca := currentlyEnabled_Zca σ vmisa hmisa
  simp only [EStateM.run] at hzca
  simp only [execute, execute_BTYPE, EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  rw [hrs1]
  simp only [hrs2, hv, if_true]
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

theorem execute_btype_bgeu_nottaken
    (imm : BitVec 13) (rs1 rs2 : regidx) (v1 v2 : BitVec 64)
    (σ : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hv : zopz0zKzJ_u v1 v2 = false) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BGEU))).run σ
      = .ok RETIRE_SUCCESS σ := by
  simp only [EStateM.run] at hrs1 hrs2
  simp only [execute, execute_BTYPE, EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  rw [hrs1]
  simp only [hrs2, hv, Bool.false_eq_true, if_false, EStateM.pure]

abbrev sigmaPost_branch_taken (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 13) : MState :=
  {(({(sigma3_branch_taken σ pc imm) with regs := (sigma3_branch_taken σ pc imm).regs.insert Register.PC (pc + sign_extend (m := 64) imm)}) : MState) with
    regs := (({(sigma3_branch_taken σ pc imm) with regs := (sigma3_branch_taken σ pc imm).regs.insert Register.PC (pc + sign_extend (m := 64) imm)}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)}

abbrev sigmaPost_branch_nottaken (σ : MState) (pc vminstret : BitVec 64) : MState :=
  {(({(sigma3_branch_nottaken σ pc) with regs := (sigma3_branch_nottaken σ pc).regs.insert Register.PC (BitVec.addInt pc 4)}) : MState) with
    regs := (({(sigma3_branch_nottaken σ pc) with regs := (sigma3_branch_nottaken σ pc).regs.insert Register.PC (BitVec.addInt pc 4)}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)}

theorem get?_sigmaPost_branch_taken (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 13) (R : Register)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false) :
    (sigmaPost_branch_taken σ pc vminstret imm).regs.get? R = σ.regs.get? R := by
  reg_reads [h1, h2, h4, h5]

theorem get?_sigmaPost_branch_nottaken (σ : MState) (pc vminstret : BitVec 64) (R : Register)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false) :
    (sigmaPost_branch_nottaken σ pc vminstret).regs.get? R = σ.regs.get? R := by
  reg_reads [h1, h2, h4, h5]

end Vsa.Sim
