import Vsa.Elf
import Vsa.Sim.InitValues
import Vsa.Sim.StateNF

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem currentlyEnabled_S
    (τ : SequentialState RegisterType trivialChoiceSource)
    (hmisa : τ.regs.get? Register.misa = some initMisa) :
    (currentlyEnabled extension.Ext_S).run τ = .ok true τ := by
  have hbit : BitVec.extractLsb 18 18 initMisa = 1#1 := by decide
  simp only [currentlyEnabled, hartSupports, _get_Misa_S]
  simp [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    readReg, get, getThe, MonadStateOf.get, EStateM.get, hmisa, hbit]

theorem currentlyEnabled_Sstc
    (τ : SequentialState RegisterType trivialChoiceSource) :
    (currentlyEnabled extension.Ext_Sstc).run τ = .ok true τ := by
  simp only [currentlyEnabled, hartSupports]
  simp [simp_sail, EStateM.run, pure, EStateM.pure]

theorem csr_map_mip_eq :
    csr_name_map_backwards "mip" = (pure 0x344#12 : SailM (BitVec 12)) := by
  unfold csr_name_map_backwards; rfl

theorem read_mip_run
    (τ : SequentialState RegisterType trivialChoiceSource)
    (vmip : BitVec 64)
    (hmip : τ.regs.get? Register.mip = some vmip)
    (vmeip : BitVec 1) (hmeip : τ.regs.get? Register.sig_meip = some vmeip)
    (vseip : BitVec 1) (hseip : τ.regs.get? Register.sig_seip = some vseip)
    (hmisa : τ.regs.get? Register.misa = some initMisa) :
    (read_mip XipReadType.IncludePlatformInterrupts).run τ
      = .ok (Mk_Minterrupts (vmip ||| (_update_Minterrupts_SEI
          (_update_Minterrupts_MEI (Mk_Minterrupts zeros) vmeip) vseip))) τ := by
  have hS : (currentlyEnabled extension.Ext_S) τ = .ok true τ :=
    currentlyEnabled_S τ hmisa
  simp only [read_mip, external_interrupts_pending, bind, Bind.bind, EStateM.bind,
    EStateM.run, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    pure, EStateM.pure, hmip, hmeip, hseip, hS, if_pos]

theorem mip_write_callback_noop
    (τ : SequentialState RegisterType trivialChoiceSource)
    (vmip : BitVec 64)
    (hmip : τ.regs.get? Register.mip = some vmip)
    (hmeip : ∃ v, τ.regs.get? Register.sig_meip = some v)
    (hseip : ∃ v, τ.regs.get? Register.sig_seip = some v)
    (hmisa : τ.regs.get? Register.misa = some initMisa) :
    ((read_mip XipReadType.IncludePlatformInterrupts) >>=
        fun v => csr_name_write_callback "mip" v).run τ
      = .ok () τ := by
  obtain ⟨vmeip, hmeip⟩ := hmeip
  obtain ⟨vseip, hseip⟩ := hseip
  have hrm := read_mip_run τ vmip hmip vmeip hmeip vseip hseip hmisa
  simp only [EStateM.run] at hrm
  simp only [csr_name_write_callback, csr_full_write_callback, csr_map_mip_eq,
    bind, Bind.bind, EStateM.bind, EStateM.run, pure, EStateM.pure, hrm]

theorem clint_dispatch_false_char
    (σ : SequentialState RegisterType trivialChoiceSource)
    (vmip vmtime vmtimecmp : BitVec 64)
    (hmip : σ.regs.get? Register.mip = some vmip)
    (hmtime : σ.regs.get? Register.mtime = some vmtime)
    (hmtimecmp : σ.regs.get? Register.mtimecmp = some vmtimecmp)
    (hmenvcfg : σ.regs.get? Register.menvcfg = some (0#64))
    (hmisa : σ.regs.get? Register.misa = some initMisa)
    (hmeip : ∃ v, σ.regs.get? Register.sig_meip = some v)
    (hseip : ∃ v, σ.regs.get? Register.sig_seip = some v) :
    (clint_dispatch false).run σ
      = .ok () {σ with regs :=
          σ.regs.insert Register.mip (Sail.BitVec.updateSubrange vmip 7 7 (bool_to_bit (zopz0zIzJ_u vmtimecmp vmtime)))} := by

  simp only [clint_dispatch, bind, Bind.bind, EStateM.bind, EStateM.run,
    PreSail.readReg, PreSail.writeReg, get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    pure, EStateM.pure, hmip, hmtime, hmtimecmp]

  simp only [show ∀ τ, currentlyEnabled extension.Ext_Sstc τ = EStateM.Result.ok true τ from
    fun τ => currentlyEnabled_Sstc τ]

  simp only [Std.ExtDHashMap.get?_insert, show (mip == menvcfg) = false from by decide,
    dif_neg, reduceCtorEq, not_false_eq_true, hmenvcfg,
    Bool.true_and, _get_MEnvcfg_STCE]
  simp only [show (Sail.BitVec.extractLsb (0#64) 63 63 == 1#1) = false from by decide,
    if_false, Bool.false_eq_true, EStateM.pure]

  simp only [get_config_print_clint, Bool.false_eq_true, if_false,
    EStateM.bind, EStateM.pure, EStateM.get,
    Std.ExtDHashMap.get?_insert_self]

  have hmip' : ({σ with regs := σ.regs.insert Register.mip (Sail.BitVec.updateSubrange vmip 7 7 (bool_to_bit (zopz0zIzJ_u vmtimecmp vmtime)))} : SequentialState RegisterType trivialChoiceSource).regs.get? Register.mip
      = some (Sail.BitVec.updateSubrange vmip 7 7 (bool_to_bit (zopz0zIzJ_u vmtimecmp vmtime))) := by
    show (σ.regs.insert Register.mip _).get? Register.mip = _
    rw [Std.ExtDHashMap.get?_insert_self]
  have hmeip' : ∃ v, ({σ with regs := σ.regs.insert Register.mip (Sail.BitVec.updateSubrange vmip 7 7 (bool_to_bit (zopz0zIzJ_u vmtimecmp vmtime)))} : SequentialState RegisterType trivialChoiceSource).regs.get? Register.sig_meip = some v := by
    obtain ⟨v, hv⟩ := hmeip
    refine ⟨v, ?_⟩
    show (σ.regs.insert Register.mip _).get? Register.sig_meip = _
    rw [Std.ExtDHashMap.get?_insert]; simp [hv]
  have hseip' : ∃ v, ({σ with regs := σ.regs.insert Register.mip (Sail.BitVec.updateSubrange vmip 7 7 (bool_to_bit (zopz0zIzJ_u vmtimecmp vmtime)))} : SequentialState RegisterType trivialChoiceSource).regs.get? Register.sig_seip = some v := by
    obtain ⟨v, hv⟩ := hseip
    refine ⟨v, ?_⟩
    show (σ.regs.insert Register.mip _).get? Register.sig_seip = _
    rw [Std.ExtDHashMap.get?_insert]; simp [hv]
  have hmisa' : ({σ with regs := σ.regs.insert Register.mip (Sail.BitVec.updateSubrange vmip 7 7 (bool_to_bit (zopz0zIzJ_u vmtimecmp vmtime)))} : SequentialState RegisterType trivialChoiceSource).regs.get? Register.misa = some initMisa := by
    show (σ.regs.insert Register.mip _).get? Register.misa = _
    rw [Std.ExtDHashMap.get?_insert]; simp [hmisa]
  have hcb := mip_write_callback_noop _ _ hmip' hmeip' hseip' hmisa'
  simp only [bind, Bind.bind, EStateM.bind, EStateM.run] at hcb
  split
  · exact hcb
  · rfl

theorem should_inc_mcycle_machine
    (σ : SequentialState RegisterType trivialChoiceSource)
    (hmci : σ.regs.get? Register.mcountinhibit = some (0#32 : RegisterType Register.mcountinhibit))
    (hmcc : σ.regs.get? Register.mcyclecfg = some (0#64 : RegisterType Register.mcyclecfg)) :
    (should_inc_mcycle Privilege.Machine).run σ = .ok true σ := by
  simp only [should_inc_mcycle, counter_priv_filter_bit, _get_Counterin_CY,
    _get_CountSmcntrpmf_MINH]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    readReg, get, getThe, MonadStateOf.get, EStateM.get]

theorem tick_clock_char
    (σ : SequentialState RegisterType trivialChoiceSource)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hpriv : σ.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hmci : σ.regs.get? Register.mcountinhibit = some (0#32 : RegisterType Register.mcountinhibit))
    (hmcc : σ.regs.get? Register.mcyclecfg = some (0#64 : RegisterType Register.mcyclecfg))
    (hmenvcfg : σ.regs.get? Register.menvcfg = some (0#64))
    (hmisa : σ.regs.get? Register.misa = some initMisa)
    (hmip : σ.regs.get? Register.mip = some vmip)
    (hmtime : σ.regs.get? Register.mtime = some vmtime)
    (hmtimecmp : σ.regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : σ.regs.get? Register.mcycle = some vmcycle)
    (hmeip : ∃ v, σ.regs.get? Register.sig_meip = some v)
    (hseip : ∃ v, σ.regs.get? Register.sig_seip = some v) :
    (tick_clock ()).run σ
      = .ok () {σ with regs := (((σ.regs.insert Register.mcycle (BitVec.addInt vmcycle 1)).insert Register.mtime (BitVec.addInt vmtime 1)).insert Register.mip (Sail.BitVec.updateSubrange vmip 7 7 (bool_to_bit (zopz0zIzJ_u vmtimecmp (BitVec.addInt vmtime 1)))))} := by
  have hinc := should_inc_mcycle_machine σ hmci hmcc
  simp only [EStateM.run] at hinc

  simp only [tick_clock, bind, Bind.bind, EStateM.bind, EStateM.run,
    PreSail.readReg, PreSail.writeReg, get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    pure, EStateM.pure, hpriv, hinc, if_true]

  simp only [hmcycle, EStateM.pure, Std.ExtDHashMap.get?_insert, hmtime]

  have hcd := clint_dispatch_false_char ({σ with regs := (σ.regs.insert Register.mcycle (BitVec.addInt vmcycle 1)).insert Register.mtime (BitVec.addInt vmtime 1)} : SequentialState RegisterType trivialChoiceSource) vmip (BitVec.addInt vmtime 1) vmtimecmp ?hmipτ ?hmtimeτ ?hmtimecmpτ ?hmenvτ ?hmisaτ ?hmeipτ ?hseipτ
  case hmipτ =>
    show ((σ.regs.insert Register.mcycle _).insert Register.mtime _).get? Register.mip = _
    simp only [Std.ExtDHashMap.get?_insert, show (mtime == mip) = false from by decide,
      show (mcycle == mip) = false from by decide, dif_neg, reduceCtorEq,
      not_false_eq_true, hmip]
  case hmtimeτ =>
    show ((σ.regs.insert Register.mcycle _).insert Register.mtime _).get? Register.mtime = _
    rw [Std.ExtDHashMap.get?_insert_self]
  case hmtimecmpτ =>
    show ((σ.regs.insert Register.mcycle _).insert Register.mtime _).get? Register.mtimecmp = _
    simp only [Std.ExtDHashMap.get?_insert, show (mtime == mtimecmp) = false from by decide,
      show (mcycle == mtimecmp) = false from by decide, dif_neg, reduceCtorEq,
      not_false_eq_true, hmtimecmp]
  case hmenvτ =>
    show ((σ.regs.insert Register.mcycle _).insert Register.mtime _).get? Register.menvcfg = _
    simp only [Std.ExtDHashMap.get?_insert, show (mtime == menvcfg) = false from by decide,
      show (mcycle == menvcfg) = false from by decide, dif_neg, reduceCtorEq,
      not_false_eq_true, hmenvcfg]
  case hmisaτ =>
    show ((σ.regs.insert Register.mcycle _).insert Register.mtime _).get? Register.misa = _
    simp only [Std.ExtDHashMap.get?_insert, show (mtime == misa) = false from by decide,
      show (mcycle == misa) = false from by decide, dif_neg, reduceCtorEq,
      not_false_eq_true, hmisa]
  case hmeipτ =>
    obtain ⟨v, hv⟩ := hmeip
    refine ⟨v, ?_⟩
    show ((σ.regs.insert Register.mcycle _).insert Register.mtime _).get? Register.sig_meip = _
    simp only [Std.ExtDHashMap.get?_insert, show (mtime == sig_meip) = false from by decide,
      show (mcycle == sig_meip) = false from by decide, dif_neg, reduceCtorEq,
      not_false_eq_true, hv]
  case hseipτ =>
    obtain ⟨v, hv⟩ := hseip
    refine ⟨v, ?_⟩
    show ((σ.regs.insert Register.mcycle _).insert Register.mtime _).get? Register.sig_seip = _
    simp only [Std.ExtDHashMap.get?_insert, show (mtime == sig_seip) = false from by decide,
      show (mcycle == sig_seip) = false from by decide, dif_neg, reduceCtorEq,
      not_false_eq_true, hv]
  simp only [EStateM.run] at hcd
  exact hcd

end Vsa.Sim
