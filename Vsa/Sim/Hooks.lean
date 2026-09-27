import Vsa.Elf
import Vsa.Sim.InitValues

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem currentlyEnabled_Ziccif
    (σ : SequentialState RegisterType trivialChoiceSource) :
    (currentlyEnabled extension.Ext_Ziccif).run σ = .ok true σ := by
  simp only [currentlyEnabled, hartSupports]
  simp [simp_sail, EStateM.run, pure, EStateM.pure]

theorem effectivePrivilege_fetch
    (σ : SequentialState RegisterType trivialChoiceSource)
    (m : BitVec 64) (p : Privilege) :
    (effectivePrivilege (MemoryAccessType.InstructionFetch ()) m p).run σ
      = .ok p σ := by
  simp only [effectivePrivilege, bne]
  have hc : (MemoryAccessType.InstructionFetch () ==
      (MemoryAccessType.InstructionFetch () : MemoryAccessType mem_payload)) = true := by
    decide
  simp [simp_sail, EStateM.run, pure, EStateM.pure, hc]

theorem translationMode_machine
    (σ : SequentialState RegisterType trivialChoiceSource) :
    (translationMode Privilege.Machine).run σ = .ok SATPMode.Bare σ := by
  simp only [translationMode]
  have hc : (Privilege.Machine == Privilege.Machine) = true := by decide
  simp [simp_sail, EStateM.run, pure, EStateM.pure, hc]

theorem translateAddr_machine_fetch
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64)
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus) :
    (translateAddr (virtaddr.Virtaddr a) (MemoryAccessType.InstructionFetch ())).run σ
      = .ok (.Ok (physaddr.Physaddr (zero_extend (m := 64) a),
          page_based_mem_type.PBMT_PMA, ())) σ := by
  unfold translateAddr
  simp only [LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, EStateM.pure, readReg,
    Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hpriv, hmstatus,
    effectivePrivilege, translationMode, is_shadow_stack_access, bne,
    bits_of_virtaddr, init_ext_ptw, pure]
  have hm : (MemoryAccessType.InstructionFetch () ==
      (MemoryAccessType.InstructionFetch () : MemoryAccessType mem_payload)) = true := by
    decide
  have hpm : (Privilege.Machine == Privilege.Machine) = true := by decide
  have hb : (SATPMode.Bare == SATPMode.Bare) = true := by decide
  simp only [hm, hpm, hb, EStateM.pure, EStateM.map, EStateM.bind, ExceptT.bindCont,
    Bool.not_true, Bool.false_and, Bool.and_false,
    if_false, if_true, Bool.false_eq_true]

theorem is_landing_pad_expected_false
    (σ : SequentialState RegisterType trivialChoiceSource)
    (help : σ.regs.get? Register.elp = some (0#1 : RegisterType Register.elp)) :
    (is_landing_pad_expected ()).run σ = .ok false σ := by
  simp only [is_landing_pad_expected, landing_pad_bits_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    readReg, get, getThe, MonadStateOf.get, EStateM.get]

theorem should_inc_minstret_machine
    (σ : SequentialState RegisterType trivialChoiceSource)
    (hmci : σ.regs.get? Register.mcountinhibit
      = some (0#32 : RegisterType Register.mcountinhibit))
    (hmic : σ.regs.get? Register.minstretcfg
      = some (0#64 : RegisterType Register.minstretcfg)) :
    (should_inc_minstret Privilege.Machine).run σ = .ok true σ := by
  simp only [should_inc_minstret, counter_priv_filter_bit,
    _get_Counterin_IR, _get_CountSmcntrpmf_MINH]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    readReg, get, getThe, MonadStateOf.get, EStateM.get]

theorem split_misaligned_aligned
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (e : Nat) (s : Splittability)
    (ha : Int.tmod (BitVec.toNatInt a) 4 = 0) :
    (split_misaligned (physaddr.Physaddr a) 4 e s).run σ
      = .ok (1, 4) σ := by
  simp only [split_misaligned]
  split
  · simp [simp_sail, EStateM.run, pure, EStateM.pure]
  · rename_i hneg
    exfalso
    apply hneg
    simp only [Bool.or_eq_true, beq_iff_eq]
    refine Or.inr (Or.inl ?_)
    exact_mod_cast ha

theorem within_mmio_readable_ram_false
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hlo : 0x80000000 ≤ a.toNat)
    (hhi : a.toNat + 4 ≤ tohostAddr) :
    (within_mmio_readable (physaddr.Physaddr a) 4).run σ = .ok false σ := by
  simp only [within_mmio_readable, within_clint, within_sig, within_htif_readable,
    within_htif_writable, get_config_rvfi, plat_have_clint, plat_have_sig,
    zopz0zI_u, zopz0zK_u, LeanRV64DExecutable.Functions.not]
  simp only [tohostAddr] at hhi
  have hcb : BitVec.toNat plat_clint_base = 33554432 := by decide
  have hcs : BitVec.toNat plat_clint_size = 786432 := by decide
  have hsb : BitVec.toNat plat_sig_base = 201326592 := by decide
  have hss : BitVec.toNat plat_sig_size = 32 := by decide
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    readReg, get, getThe, MonadStateOf.get, EStateM.get, BitVec.toNatInt,
    htif_tohost_size]
  simp only [tohostAddr] at *
  have hadd : (a + 4#64).toNat = a.toNat + 4 := by
    have h4 : (4#64).toNat = 4 := by decide
    rw [BitVec.toNat_add, h4, Nat.mod_eq_of_lt (by omega)]
  refine ⟨fun _ => by omega, fun _ => by omega, fun _ => ?_⟩
  have hle : (a + 4#64).toNat ≤ 2147593472 := by rw [hadd]; omega
  have hrhs : ((2147593472 : Nat) : Int) % 18446744073709551616 = ((2147593472 : Nat) : Int) := by
    decide
  rw [hrhs]
  omega

open MemoryRegionType AtomicSupport Reservability misaligned_exception in

theorem pmaCheck_ram_exec
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64)
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hlo : 0x80000000 ≤ a.toNat)
    (hhi : a.toNat + 4 ≤ 0x100000000)
    (halign : Int.tmod (BitVec.toNatInt a) 4 = 0) :
    (pmaCheck (physaddr.Physaddr a) 4 (MemoryAccessType.InstructionFetch ())
        page_based_mem_type.PBMT_PMA false).run σ
      = .ok (.Ok { splittable := Splittability.CannotSplit, granule_size_exp := 0 }) σ := by
  have hmatch : matching_pma_region_bits_range initPmaRegions
      (zero_extend (bits_of_physaddr (physaddr.Physaddr a))) (to_bits 4)
      = some ({ base := 0x80000000#64
                size := 0x80000000#64
                attributes := { mem_type := MainMemory
                                cacheable := true
                                coherent := true
                                executable := true
                                readable := true
                                writable := true
                                read_idempotent := true
                                write_idempotent := true
                                misaligned_exceptions := { load_store := none
                                                           vector := none
                                                           amo := AccessFault }
                                atomic_support := AMOCASQ
                                reservability := RsrvEventual
                                supports_cbo_zero := true
                                supports_pte_read := true
                                supports_pte_write := true
                                misaligned_atomicity_granule_size_exp := 4
                                vector_misaligned_atomicity_granule_size_exp := 4 }
                include_in_device_tree := true } : PMA_Region) := by
    have hz : (zero_extend (bits_of_physaddr (physaddr.Physaddr a)) : BitVec 64) = a :=
      BitVec.setWidth_eq a
    rw [hz, show (to_bits 4 : BitVec 64) = 4#64 from by decide]
    simp only [initPmaRegions, matching_pma_region_bits_range, range_subset,
      zopz0zIzJ_u, BitVec.toNatInt]
    rw [if_neg, if_neg, if_pos]
    · simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨?_, ?_, ?_⟩ <;> · apply Int.ofNat_le.mpr; bv_omega
    · simp only [Bool.and_eq_true, decide_eq_true_eq]
      rintro ⟨h1, _⟩; have := Int.ofNat_le.mp h1; bv_omega
    · simp only [Bool.and_eq_true, decide_eq_true_eq]
      rintro ⟨h1, _⟩; have := Int.ofNat_le.mp h1; bv_omega
  unfold pmaCheck
  simp only [LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, readReg,
    Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hpma]
  simp only [pure, EStateM.pure, matching_pma_region, hmatch, override_PMA,
    Functions.not, mag_pma_check, is_mag_applicable_access, is_aligned_paddr,
    BitVec.toNatInt, ExceptT.pure, ExceptT.bindCont, ExceptT.mk,
    EStateM.map, EStateM.bind, bind, Bind.bind,
    Bool.not_true, Bool.false_eq_true,
    if_false, Bool.false_and, Bool.or_false]
  rw [if_pos]
  · rfl
  · rw [beq_iff_eq]; exact_mod_cast halign

end Vsa.Sim
