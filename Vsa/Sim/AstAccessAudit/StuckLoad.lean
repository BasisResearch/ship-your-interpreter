import Vsa.Sim.StepAlu
import Vsa.Sim.ExecuteLoad
import Vsa.Sim.DecodeTable.Batch01Part13
import Vsa.Sim.AstAccessAudit.StuckPrefix

/- Local PMA-denied statement-tag load. No AST or initial-boundary claim. -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa Vsa.Machine Vsa.Sim

namespace Vsa.Sim.AstAccessAudit

abbrev faultPC : BitVec 64 := 0x80004014#64
abbrev badAddr : BitVec 64 := 0x4000#64
abbrev loadAccess : MemoryAccessType mem_payload := .Load .Data
abbrev loadInsn : instruction := .LOAD (0#12, .Regidx 8#5, .Regidx 15#5, false, 4)
abbrev loadTrap : ExecutionResult :=
  .Trap (.Machine, make_sync_exception (.E_Load_Access_Fault ()) badAddr, faultPC)

theorem pma_denies (σ : MState) (hG : GoodState σ) :
    (pmaCheck (.Physaddr badAddr) 4 loadAccess .PBMT_PMA false).run σ =
      .ok (.Err (.E_Load_Access_Fault ())) σ := by
  have hm : matching_pma_region initPmaRegions (.Physaddr badAddr) 4 = none := by
    decide
  simp [pmaCheck, simp_sail, throw, throwThe, Bind.bind, MonadExceptOf.throw, EStateM.throw, get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.bindCont,
    ExceptT.pure, liftM, monadLift, MonadLift.monadLift, Functor.map, EStateM.map, hG.pma_regions, hm, accessFaultFromAccessType,
    loadAccess, EStateM.run, bind, EStateM.bind, pure, EStateM.pure]

theorem mem_read_denied (σ : MState) (hG : GoodState σ) :
    (mem_read loadAccess .PBMT_PMA (.Physaddr badAddr) 4 false false false).run σ =
      .ok (.Err (.Physaddr badAddr, .E_Load_Access_Fault ())) σ := by
  have hp := pma_denies σ hG
  have hmp := pmp_allows σ (.Physaddr badAddr) 4 loadAccess initPmpaddr
    hG.pmpcfg_n hG.pmpaddr_n
  have he := effectivePrivilege_data σ initMstatus .Machine (by decide)
  simp only [EStateM.run] at hp hmp he
  simp [mem_read, mem_read_meta, mem_read_priv, mem_read_priv_meta,
    checked_mem_read, check_pma_with_pmp_priority, simp_sail, throw, throwThe, Bind.bind, MonadExceptOf.throw, EStateM.throw, get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.bindCont,
    ExceptT.pure, liftM, monadLift, MonadLift.monadLift, Functor.map, EStateM.map,
    hG.mstatus, hG.cur_privilege, he, hp, hmp, MemoryOpResult_drop_meta,
    EStateM.run, bind, EStateM.bind, pure, EStateM.pure]

theorem translated_read_traps (σ : MState) (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some faultPC) :
    (translate_and_read_value (.Virtaddr badAddr) 4 loadAccess false false false).run σ =
      .ok (.Err loadTrap) σ := by
  have ht := translateAddr_machine_data σ badAddr initMstatus
    hG.cur_privilege hG.mstatus (by decide)
  have hr := mem_read_denied σ hG
  have hz : zero_extend (m := 64) badAddr = badAddr := by decide
  simp only [EStateM.run] at ht hr
  have ha : badAddr + BitVec.extractLsb ((Functions.xlen : Int) - 1).toNat 0 (badAddr - badAddr) = badAddr := by decide
  simp [translate_and_read_value, ha, ht, hz, hr, bits_of_virtaddr, loadTrap, memory_exception, trap,
    offset_virtaddr_by, simp_sail, throw, throwThe, Bind.bind, MonadExceptOf.throw, EStateM.throw, get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.bindCont,
    ExceptT.pure, liftM, monadLift, MonadLift.monadLift, Functor.map, EStateM.map, hG.cur_privilege, hpc,
    EStateM.run, bind, EStateM.bind, pure, EStateM.pure]

  exact congrArg (make_sync_exception (.E_Load_Access_Fault ())) ha

theorem vmem_addr_traps (σ : MState) (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some faultPC) :
    (vmem_read_addr (.Virtaddr badAddr) 4 loadAccess false false false).run σ =
      .ok (.Err loadTrap) σ := by
  have hsplit := split_on_page_boundary_data_w σ badAddr 4
    (by decide) (by decide) (by decide)
  have hep := effectivePrivilege_data σ initMstatus .Machine (by decide)
  have htm := translationMode_machine σ
  have htrv := translated_read_traps σ hG hpc
  have halignv : is_aligned_vaddr (.Virtaddr badAddr) 4 = true := by decide
  simp only [EStateM.run] at hsplit hep htm htrv
  unfold vmem_read_addr
  simp only [halignv, LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, pure, EStateM.pure,
    bits_of_virtaddr, sys_misaligned_order_decreasing,
    Functions.not, Bool.not_true, Bool.false_and, Bool.and_false, if_false, if_true,
    Bool.false_eq_true]
  rw [hsplit]
  simp only [EStateM.bind, EStateM.pure, ExceptT.bindCont, EStateM.map,
    bind, ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.pure, liftM, monadLift,
    MonadLift.monadLift, Functor.map, pure,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hG.mstatus, hG.cur_privilege]
  rw [hep]
  simp only [bne, EStateM.bind, EStateM.pure, ExceptT.bindCont, EStateM.map, htm,
    show (SATPMode.Bare == SATPMode.Bare) = true from by decide,
    Bool.not_true, Bool.false_and, Bool.and_false, Bool.false_eq_true, if_false,
    gt_iff_lt, sys_misaligned_order_decreasing]
  simp [htrv, MonadExceptOf.throw, ExceptT.mk, pure, EStateM.pure, EStateM.bind,
    ExceptT.bindCont, EStateM.map]

theorem execute_traps (σ : MState) (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some faultPC)
    (hx8 : σ.regs.get? Register.x8 = some badAddr) :
    (execute loadInsn).run σ = .ok loadTrap σ := by
  have hrs : (rX_bits (.Regidx 8#5)).run σ = .ok badAddr σ := by
    simp [rX_bits, rX, regval_from_reg, bind, EStateM.bind, pure, EStateM.pure, simp_sail, throw, throwThe, Bind.bind, MonadExceptOf.throw, EStateM.throw, get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.bindCont,
    ExceptT.pure, liftM, monadLift, MonadLift.monadLift, Functor.map, EStateM.map, hx8, EStateM.run]
  have hv := vmem_read_data_w σ (.Regidx 8#5) 0#64 badAddr 4 (.Err loadTrap)
    initMstatus hG.cur_privilege hG.mstatus (by decide) hG.mseccfg hrs
    (by simpa using vmem_addr_traps σ hG hpc)
  simp only [EStateM.run] at hv
  change (execute_LOAD 0#12 (.Regidx 8#5) (.Regidx 15#5) false 4).run σ = _
  simp [execute_LOAD, Functions.xlen_bytes, sign_extend, simp_sail, throw, throwThe, Bind.bind, MonadExceptOf.throw, EStateM.throw, get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.bindCont,
    ExceptT.pure, liftM, monadLift, MonadLift.monadLift, Functor.map, EStateM.map, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, hv]

theorem handler_stuck (σ : MState) (hG : GoodState σ)
    (hmcause : σ.regs.get? Register.mcause = none) :
    ∃ τ, (exception_handler .Machine
      (make_sync_exception (.E_Load_Access_Fault ()) badAddr) faultPC).run σ =
      .error .Unreachable τ := by
  simp [exception_handler, exception_delegatee, trap_handler, currentlyEnabled,
    hartSupports, zicfilp_preserve_elp_on_trap, reset_elp,
    simp_sail, throw, throwThe, Bind.bind, MonadExceptOf.throw, EStateM.throw, get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.bindCont,
    ExceptT.pure, liftM, monadLift, MonadLift.monadLift, Functor.map, EStateM.map, hG.misa, hG.medeleg, hG.mstatus, hG.elp, hmcause,
    make_sync_exception, initMisa, initMstatus,
    get_config_print_exception, get_config_print_interrupt, _get_Misa_S,
    exceptionType_bits_forwards, bit_to_bool, privLevel_to_bits, zopz0zI_u,
    trapCause_is_interrupt, trapCause_bits_forwards, bool_bit_backwards, privLevel_bits_backwards,
    Std.ExtDHashMap.get?_insert, EStateM.run, bind, EStateM.bind, pure, EStateM.pure]

/-- The fetch/decode skeleton forwards the actual load trap. -/
theorem run_hart_trap
    (τ : MState) (step_no : Nat) (pc : BitVec 64) (w : BitVec 32)
    (ast : instruction)
    (hpriv : τ.regs.get? Register.cur_privilege = some .Machine)
    (hpc : τ.regs.get? Register.PC = some pc)
    (hdisp : (dispatchInterrupt .Machine).run τ = .ok none τ)
    (hfetch : (fetch ()).run τ = .ok (.F_Base w) τ)
    (hdec : (ext_decode w).run τ = .ok ast τ)
    (hlpad : (is_landing_pad_expected ()).run τ = .ok false τ)
    (hexec : (execute ast).run (afterNextPC τ pc) = .ok loadTrap (afterNextPC τ pc)) :
    (run_hart_active step_no).run τ =
      .ok (.Step_Execute (loadTrap, zero_extend (m := 32) w)) (afterNextPC τ pc) := by
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
    Bool.false_and, Bool.false_eq_true, if_false, EStateM.get, hpc,
    EStateM.modifyGet]
  rw [show (execute ast (afterNextPC τ pc)) = _ from hexec]
  rfl

theorem stepOnce_stuck (σ : MState) (i u : Nat) (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some faultPC)
    (hx8 : σ.regs.get? Register.x8 = some badAddr)
    (hmcause : σ.regs.get? Register.mcause = none)
    (hb0 : σ.mem[0x80004014]? = some 0x83#8)
    (hb1 : σ.mem[0x80004015]? = some 0x27#8)
    (hb2 : σ.mem[0x80004016]? = some 0x04#8)
    (hb3 : σ.mem[0x80004017]? = some 0x00#8) :
    ∃ τ, (stepOnce i u).run σ = .error .Unreachable τ := by
  let σ1 := afterPrelude σ
  let σ2 := afterNextPC σ1 faultPC
  have hG1 : GoodState σ1 := by dsimp [σ1]; goodstate_frame hG
  have hG2 : GoodState σ2 := by dsimp [σ2, σ1]; goodstate_frame hG
  have hpc1 : σ1.regs.get? Register.PC = some faultPC := by
    rw [get?_afterPrelude σ _ (by decide)]; exact hpc
  have hpc2 : σ2.regs.get? Register.PC = some faultPC := by
    rw [get?_afterNextPC σ faultPC _ (by decide) (by decide)]; exact hpc
  have hx82 : σ2.regs.get? Register.x8 = some badAddr := by
    rw [get?_afterNextPC σ faultPC _ (by decide) (by decide)]; exact hx8
  have hmcause2 : σ2.regs.get? Register.mcause = none := by
    rw [get?_afterNextPC σ faultPC _ (by decide) (by decide)]; exact hmcause
  obtain ⟨vmip, hmip⟩ := hG1.mip
  obtain ⟨vmeip, hmeip⟩ := hG1.sig_meip
  obtain ⟨vseip, hseip⟩ := hG1.sig_seip
  have hdisp := dispatch_none σ1 vmip vmeip vseip _ _
    hG1.misa hG1.mie hmip hmeip hseip hG1.mideleg hG1.mstatus
  have hfetch := fetch_F_Base σ1 faultPC 0x83#8 0x27#8 0x04#8 0#8 _ _ _
    hpc1 hG1.cur_privilege hG1.mstatus hG1.misa hG1.pma_regions
    hG1.pmpcfg_n hG1.pmpaddr_n hG1.htif_tohost_base
    (by decide) (by decide) (by decide) hb0 hb1 hb2 hb3 (by decide)
  have hdec := Vsa.Sim.DecodeTable.decode_00042783 σ1 hG1.misa hG1.cur_privilege hG1.mseccfg
  have hlpad := is_landing_pad_expected_false σ1 hG1.elp
  have hexec := execute_traps σ2 hG2 hpc2 hx82
  have hrun := run_hart_trap σ1 u faultPC 0x00042783#32 loadInsn
    hG1.cur_privilege hpc1 hdisp hfetch hdec hlpad hexec
  obtain ⟨τ, hhandler⟩ := handler_stuck σ2 hG2 hmcause2
  have hinc := should_inc_minstret_machine σ hG.mcountinhibit hG.minstretcfg
  simp only [EStateM.run] at hrun hhandler hinc
  refine ⟨τ, ?_⟩
  simp [stepOnce, try_step, simp_sail, throw, throwThe, Bind.bind, MonadExceptOf.throw, EStateM.throw, get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.bindCont,
    ExceptT.pure, liftM, monadLift, MonadLift.monadLift, Functor.map, EStateM.map, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, hG.htif_done, hG.cur_privilege, hinc,
    hG1.hart_state, hrun, loadTrap, hhandler,
    σ1, σ2, afterPrelude, afterNextPC, Std.ExtDHashMap.get?_insert, hG.hart_state]

  simp [σ2, σ1, afterPrelude, afterNextPC] at hhandler
  rw [show BitVec.addInt faultPC 4 = faultPC + 4#64 from by decide] at hhandler
  rw [hhandler]

theorem local_stuck (σ : MState) (i u : Nat) (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some faultPC)
    (hx8 : σ.regs.get? Register.x8 = some badAddr)
    (hmcause : σ.regs.get? Register.mcause = none)
    (hb0 : σ.mem[0x80004014]? = some 0x83#8)
    (hb1 : σ.mem[0x80004015]? = some 0x27#8)
    (hb2 : σ.mem[0x80004016]? = some 0x04#8)
    (hb3 : σ.mem[0x80004017]? = some 0x00#8) :
    Vsa.Machine.Stuck ⟨σ, i, u⟩ := by
  obtain ⟨τ, he⟩ := stepOnce_stuck σ i u hG hpc hx8 hmcause hb0 hb1 hb2 hb3
  constructor
  · intro c hs
    cases hs with | mk hs => rw [he] at hs; cases hs
  · intro code σf hh
    cases hh with | mk hh => rw [he] at hh; cases hh

#print axioms pma_denies
#print axioms stepOnce_stuck
#print axioms local_stuck

end Vsa.Sim.AstAccessAudit
