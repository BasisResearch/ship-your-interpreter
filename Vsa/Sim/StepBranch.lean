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

theorem try_step_branch_taken
    (σ : MState) (u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (imm : BitVec 13) (rs1 rs2 : regidx) (op : bop)
    (w : BitVec 32) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.BTYPE (imm, rs2, rs1, op)) (afterPrelude σ))
    (hexec : (execute (instruction.BTYPE (imm, rs2, rs1, op))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc imm))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0) :
    (try_step u true).run σ
      = .ok false
          {(({(sigma3_branch_taken σ pc imm) with regs := (sigma3_branch_taken σ pc imm).regs.insert Register.PC (pc + sign_extend (m := 64) imm)}) : MState) with
            regs := (({(sigma3_branch_taken σ pc imm) with regs := (sigma3_branch_taken σ pc imm).regs.insert Register.PC (pc + sign_extend (m := 64) imm)}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)} := by
  exact try_step_retire (Fetched.of_bytes hG hpc hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec) hexec
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩

theorem try_step_branch_nottaken
    (σ : MState) (u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (imm : BitVec 13) (rs1 rs2 : regidx) (op : bop)
    (w : BitVec 32) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.BTYPE (imm, rs2, rs1, op)) (afterPrelude σ))
    (hexec : (execute (instruction.BTYPE (imm, rs2, rs1, op))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0) :
    (try_step u true).run σ
      = .ok false
          {(({(sigma3_branch_nottaken σ pc) with regs := (sigma3_branch_nottaken σ pc).regs.insert Register.PC (BitVec.addInt pc 4)}) : MState) with
            regs := (({(sigma3_branch_nottaken σ pc) with regs := (sigma3_branch_nottaken σ pc).regs.insert Register.PC (BitVec.addInt pc 4)}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)} := by
  exact try_step_retire (Fetched.of_bytes hG hpc hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec) hexec
    ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hminstret]⟩

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

theorem goodstate_sigmaPost_branch_taken (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 13)
    (hG : GoodState σ) : GoodState (sigmaPost_branch_taken σ pc vminstret imm) := by
  exact (((hG.insert_nonpinned (by decide) _).insert_nonpinned (by decide) _).insert_nonpinned
    (by decide) _).retirePost _ _

theorem goodstate_sigmaPost_branch_nottaken (σ : MState) (pc vminstret : BitVec 64)
    (hG : GoodState σ) : GoodState (sigmaPost_branch_nottaken σ pc vminstret) := by
  exact ((hG.insert_nonpinned (by decide) _).insert_nonpinned (by decide) _).retirePost _ _

theorem stepOnce_branch_taken_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (imm : BitVec 13) (rs1 rs2 : regidx) (op : bop)
    (w : BitVec 32) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.BTYPE (imm, rs2, rs1, op)) (afterPrelude σ))
    (hexec : (execute (instruction.BTYPE (imm, rs2, rs1, op))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc imm))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 ≠ 2) :
    (stepOnce i u).run σ = .ok (.inr (i + 1, u + 1)) (sigmaPost_branch_taken σ pc vminstret imm) := by
  exact stepOnce_retire_notick (try_step_branch_taken σ u pc vminstret imm rs1 rs2 op w b0 b1 b2 b3
      hG hpc hminstret hword hnotrvc hdec hexec hb0 hb1 hb2 hb3 hlo hhi halign)
    hG (goodstate_sigmaPost_branch_taken σ pc vminstret imm hG) htick

theorem stepOnce_branch_nottaken_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (imm : BitVec 13) (rs1 rs2 : regidx) (op : bop)
    (w : BitVec 32) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.BTYPE (imm, rs2, rs1, op)) (afterPrelude σ))
    (hexec : (execute (instruction.BTYPE (imm, rs2, rs1, op))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 ≠ 2) :
    (stepOnce i u).run σ = .ok (.inr (i + 1, u + 1)) (sigmaPost_branch_nottaken σ pc vminstret) := by
  exact stepOnce_retire_notick (try_step_branch_nottaken σ u pc vminstret imm rs1 rs2 op w b0 b1 b2 b3
      hG hpc hminstret hword hnotrvc hdec hexec hb0 hb1 hb2 hb3 hlo hhi halign)
    hG (goodstate_sigmaPost_branch_nottaken σ pc vminstret hG) htick

noncomputable abbrev sigmaTick_branch_taken
    (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 13)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64) : MState :=
  {(sigmaPost_branch_taken σ pc vminstret imm) with
    regs := (((((sigmaPost_branch_taken σ pc vminstret imm).regs.insert Register.mcycle (BitVec.addInt vmcycle 1)).insert Register.mtime (BitVec.addInt vmtime 1)).insert Register.mip (Sail.BitVec.updateSubrange vmip 7 7 (bool_to_bit (zopz0zIzJ_u vmtimecmp (BitVec.addInt vmtime 1))))))}

noncomputable abbrev sigmaTick_branch_nottaken
    (σ : MState) (pc vminstret : BitVec 64)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64) : MState :=
  {(sigmaPost_branch_nottaken σ pc vminstret) with
    regs := (((((sigmaPost_branch_nottaken σ pc vminstret).regs.insert Register.mcycle (BitVec.addInt vmcycle 1)).insert Register.mtime (BitVec.addInt vmtime 1)).insert Register.mip (Sail.BitVec.updateSubrange vmip 7 7 (bool_to_bit (zopz0zIzJ_u vmtimecmp (BitVec.addInt vmtime 1))))))}

theorem stepOnce_branch_taken_tick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (imm : BitVec 13) (rs1 rs2 : regidx) (op : bop)
    (w : BitVec 32) (b0 b1 b2 b3 : BitVec 8)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmip : (sigmaPost_branch_taken σ pc vminstret imm).regs.get? Register.mip = some vmip)
    (hmtime : (sigmaPost_branch_taken σ pc vminstret imm).regs.get? Register.mtime = some vmtime)
    (hmtimecmp : (sigmaPost_branch_taken σ pc vminstret imm).regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : (sigmaPost_branch_taken σ pc vminstret imm).regs.get? Register.mcycle = some vmcycle)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.BTYPE (imm, rs2, rs1, op)) (afterPrelude σ))
    (hexec : (execute (instruction.BTYPE (imm, rs2, rs1, op))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc imm))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 = 2) :
    (stepOnce i u).run σ
      = .ok (.inr (0, u + 1)) (sigmaTick_branch_taken σ pc vminstret imm vmip vmtime vmtimecmp vmcycle) := by
  exact stepOnce_retire_tick (try_step_branch_taken σ u pc vminstret imm rs1 rs2 op w b0 b1 b2 b3
      hG hpc hminstret hword hnotrvc hdec hexec hb0 hb1 hb2 hb3 hlo hhi halign)
    hG (goodstate_sigmaPost_branch_taken σ pc vminstret imm hG) hmip hmtime hmtimecmp hmcycle htick

theorem stepOnce_branch_nottaken_tick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (imm : BitVec 13) (rs1 rs2 : regidx) (op : bop)
    (w : BitVec 32) (b0 b1 b2 b3 : BitVec 8)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmip : (sigmaPost_branch_nottaken σ pc vminstret).regs.get? Register.mip = some vmip)
    (hmtime : (sigmaPost_branch_nottaken σ pc vminstret).regs.get? Register.mtime = some vmtime)
    (hmtimecmp : (sigmaPost_branch_nottaken σ pc vminstret).regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : (sigmaPost_branch_nottaken σ pc vminstret).regs.get? Register.mcycle = some vmcycle)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.BTYPE (imm, rs2, rs1, op)) (afterPrelude σ))
    (hexec : (execute (instruction.BTYPE (imm, rs2, rs1, op))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 = 2) :
    (stepOnce i u).run σ
      = .ok (.inr (0, u + 1)) (sigmaTick_branch_nottaken σ pc vminstret vmip vmtime vmtimecmp vmcycle) := by
  exact stepOnce_retire_tick (try_step_branch_nottaken σ u pc vminstret imm rs1 rs2 op w b0 b1 b2 b3
      hG hpc hminstret hword hnotrvc hdec hexec hb0 hb1 hb2 hb3 hlo hhi halign)
    hG (goodstate_sigmaPost_branch_nottaken σ pc vminstret hG) hmip hmtime hmtimecmp hmcycle htick

theorem step_branch_taken_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (imm : BitVec 13) (rs1 rs2 : regidx) (op : bop)
    (w : BitVec 32) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.BTYPE (imm, rs2, rs1, op)) (afterPrelude σ))
    (hexec : (execute (instruction.BTYPE (imm, rs2, rs1, op))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc imm))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 ≠ 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩ ⟨sigmaPost_branch_taken σ pc vminstret imm, i + 1, u + 1⟩
    ∧ GoodState (sigmaPost_branch_taken σ pc vminstret imm) := by
  exact step_retire_notick (try_step_branch_taken σ u pc vminstret imm rs1 rs2 op w b0 b1 b2 b3
      hG hpc hminstret hword hnotrvc hdec hexec hb0 hb1 hb2 hb3 hlo hhi halign)
    hG (goodstate_sigmaPost_branch_taken σ pc vminstret imm hG) htick

theorem step_branch_nottaken_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (imm : BitVec 13) (rs1 rs2 : regidx) (op : bop)
    (w : BitVec 32) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.BTYPE (imm, rs2, rs1, op)) (afterPrelude σ))
    (hexec : (execute (instruction.BTYPE (imm, rs2, rs1, op))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 ≠ 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩ ⟨sigmaPost_branch_nottaken σ pc vminstret, i + 1, u + 1⟩
    ∧ GoodState (sigmaPost_branch_nottaken σ pc vminstret) := by
  exact step_retire_notick (try_step_branch_nottaken σ u pc vminstret imm rs1 rs2 op w b0 b1 b2 b3
      hG hpc hminstret hword hnotrvc hdec hexec hb0 hb1 hb2 hb3 hlo hhi halign)
    hG (goodstate_sigmaPost_branch_nottaken σ pc vminstret hG) htick

theorem step_branch_taken_tick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (imm : BitVec 13) (rs1 rs2 : regidx) (op : bop)
    (w : BitVec 32) (b0 b1 b2 b3 : BitVec 8)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmip : (sigmaPost_branch_taken σ pc vminstret imm).regs.get? Register.mip = some vmip)
    (hmtime : (sigmaPost_branch_taken σ pc vminstret imm).regs.get? Register.mtime = some vmtime)
    (hmtimecmp : (sigmaPost_branch_taken σ pc vminstret imm).regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : (sigmaPost_branch_taken σ pc vminstret imm).regs.get? Register.mcycle = some vmcycle)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.BTYPE (imm, rs2, rs1, op)) (afterPrelude σ))
    (hexec : (execute (instruction.BTYPE (imm, rs2, rs1, op))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc imm))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 = 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩
      ⟨sigmaTick_branch_taken σ pc vminstret imm vmip vmtime vmtimecmp vmcycle, 0, u + 1⟩
    ∧ GoodState (sigmaTick_branch_taken σ pc vminstret imm vmip vmtime vmtimecmp vmcycle) := by
  exact step_retire_tick (try_step_branch_taken σ u pc vminstret imm rs1 rs2 op w b0 b1 b2 b3
      hG hpc hminstret hword hnotrvc hdec hexec hb0 hb1 hb2 hb3 hlo hhi halign)
    hG (goodstate_sigmaPost_branch_taken σ pc vminstret imm hG) hmip hmtime hmtimecmp hmcycle htick

theorem step_branch_nottaken_tick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (imm : BitVec 13) (rs1 rs2 : regidx) (op : bop)
    (w : BitVec 32) (b0 b1 b2 b3 : BitVec 8)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmip : (sigmaPost_branch_nottaken σ pc vminstret).regs.get? Register.mip = some vmip)
    (hmtime : (sigmaPost_branch_nottaken σ pc vminstret).regs.get? Register.mtime = some vmtime)
    (hmtimecmp : (sigmaPost_branch_nottaken σ pc vminstret).regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : (sigmaPost_branch_nottaken σ pc vminstret).regs.get? Register.mcycle = some vmcycle)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.BTYPE (imm, rs2, rs1, op)) (afterPrelude σ))
    (hexec : (execute (instruction.BTYPE (imm, rs2, rs1, op))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 = 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩
      ⟨sigmaTick_branch_nottaken σ pc vminstret vmip vmtime vmtimecmp vmcycle, 0, u + 1⟩
    ∧ GoodState (sigmaTick_branch_nottaken σ pc vminstret vmip vmtime vmtimecmp vmcycle) := by
  exact step_retire_tick (try_step_branch_nottaken σ u pc vminstret imm rs1 rs2 op w b0 b1 b2 b3
      hG hpc hminstret hword hnotrvc hdec hexec hb0 hb1 hb2 hb3 hlo hhi halign)
    hG (goodstate_sigmaPost_branch_nottaken σ pc vminstret hG) hmip hmtime hmtimecmp hmcycle htick

end Vsa.Sim
