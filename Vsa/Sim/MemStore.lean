import Vsa.Sim.Hooks
import Vsa.Sim.Pmp
import Vsa.Sim.MemWidth

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem within_mmio_writable_ram_false
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (w : Nat)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hwle : w ≤ 8)
    (hlo : 0x80000000 ≤ a.toNat)
    (hhiwin : tohostAddr + 16 ≤ a.toNat) :
    (within_mmio_writable (physaddr.Physaddr a) w).run σ = .ok false σ := by
  simp only [within_mmio_writable, within_clint, within_sig, within_htif_writable,
    get_config_rvfi, plat_have_clint, plat_have_sig,
    zopz0zI_u, zopz0zK_u, LeanRV64DExecutable.Functions.not]
  simp only [tohostAddr] at hhiwin
  have hcb : BitVec.toNat plat_clint_base = 33554432 := by decide
  have hcs : BitVec.toNat plat_clint_size = 786432 := by decide
  have hsb : BitVec.toNat plat_sig_base = 201326592 := by decide
  have hss : BitVec.toNat plat_sig_size = 32 := by decide
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, BitVec.toNatInt,
    htif_tohost_size]
  simp only [tohostAddr]
  refine ⟨fun _ => by push_cast; omega, fun _ => by push_cast; omega,
    fun hcontra => by omega⟩

/-- Little-endian byte codec: the `w` bytes of `v` inserted at `addr, …, addr + w - 1`. -/
def memWriteLE (m : Std.ExtHashMap Nat (BitVec 8)) (addr w : Nat) (v : BitVec (8 * w)) :
    Std.ExtHashMap Nat (BitVec 8) :=
  (List.ofFn fun i : Fin w => (addr + i.val, v.extractLsb' (8 * i.val) 8)).foldl
    (fun m p => m.insert p.1 p.2) m

theorem forM_writeByte_run {ue : Type} (l : List (Nat × BitVec 8))
    (σ : SequentialState RegisterType trivialChoiceSource) :
    (List.forM l (fun x => (PreSail.writeByte x.fst x.snd :
        PreSailM RegisterType trivialChoiceSource ue PUnit))) σ
      = .ok () { σ with mem := l.foldl (fun m p => m.insert p.1 p.2) σ.mem } := by
  induction l generalizing σ with
  | nil => rfl
  | cons p l ih => exact ih _

theorem write_ram_w
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (w : Nat) (v : BitVec (8 * w)) :
    (Functions.write_ram write_kind.Write_plain (physaddr.Physaddr a) w v ()).run σ
      = .ok true { σ with mem := memWriteLE σ.mem a.toNat w v } := by
  simp only [Functions.write_ram, PreSail.sail_mem_write, PreSail.writeBytes, memWriteLE,
    bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  rw [forM_writeByte_run]; rfl

theorem write_ram_1
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec (8 * 1)) :
    (Functions.write_ram write_kind.Write_plain (physaddr.Physaddr a) 1 v ()).run σ
      = .ok true
          { σ with mem := σ.mem.insert a.toNat v } := by
  rw [write_ram_w]; simp [memWriteLE]

theorem write_ram_2
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec (8 * 2)) :
    (Functions.write_ram write_kind.Write_plain (physaddr.Physaddr a) 2 v ()).run σ
      = .ok true
          { σ with mem := ((σ.mem.insert a.toNat (v.extractLsb' 0 8)).insert
              (a.toNat + 1) (v.extractLsb' 8 8)) } :=
  write_ram_w σ a 2 v

theorem write_ram_4
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec (8 * 4)) :
    (Functions.write_ram write_kind.Write_plain (physaddr.Physaddr a) 4 v ()).run σ
      = .ok true
          { σ with mem := ((((σ.mem.insert a.toNat (v.extractLsb' 0 8)).insert
              (a.toNat + 1) (v.extractLsb' 8 8)).insert
              (a.toNat + 2) (v.extractLsb' 16 8)).insert
              (a.toNat + 3) (v.extractLsb' 24 8)) } :=
  write_ram_w σ a 4 v

theorem write_ram_8
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec (8 * 8)) :
    (Functions.write_ram write_kind.Write_plain (physaddr.Physaddr a) 8 v ()).run σ
      = .ok true
          { σ with mem := ((((((((σ.mem.insert a.toNat (v.extractLsb' 0 8)).insert
              (a.toNat + 1) (v.extractLsb' 8 8)).insert
              (a.toNat + 2) (v.extractLsb' 16 8)).insert
              (a.toNat + 3) (v.extractLsb' 24 8)).insert
              (a.toNat + 4) (v.extractLsb' 32 8)).insert
              (a.toNat + 5) (v.extractLsb' 40 8)).insert
              (a.toNat + 6) (v.extractLsb' 48 8)).insert
              (a.toNat + 7) (v.extractLsb' 56 8)) } :=
  write_ram_w σ a 8 v

theorem ofInt_zero_gen' (n : Nat) : (BitVec.ofInt n 0) = 0#n := by
  apply BitVec.eq_of_toNat_eq; simp

theorem addInt_zero_pa' (a : physaddrbits) : BitVec.addInt a (0 : Int) = a := by
  simp only [BitVec.addInt, ofInt_zero_gen', BitVec.add_zero]

theorem setWidth_extractLsb_full (w : Nat) (hw : 0 < w) (data : BitVec (8 * w))
    (hi lo : Nat) (hhi : hi = 8 * w - 1) (hlo : lo = 0) :
    BitVec.setWidth (8 * w) (Sail.BitVec.extractLsb data hi lo) = data := by
  subst hhi hlo
  apply BitVec.eq_of_toNat_eq
  have hlt := data.isLt
  have he : 8 * w - 1 - 0 + 1 = 8 * w := by omega
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
    BitVec.toNat_setWidth, Nat.shiftRight_zero, BitVec.toNat_ofNat, he]
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]

theorem checked_mem_write_w
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (w : Nat) (data : BitVec (8 * w))
    (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hwpos : 0 < w) (hwle : w ≤ 8)
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hlo : 0x80000000 ≤ a.toNat)
    (hhiram : a.toNat + w ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ a.toNat)
    (halign : a.toNat % w = 0)
    (hram : (Functions.write_ram write_kind.Write_plain (physaddr.Physaddr a) w data ()).run σ
      = .ok true σ') :
    (checked_mem_write (physaddr.Physaddr a) w data
        (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine () false false false).run σ
      = .ok (.Ok true) σ' := by
  have htmod := tmod_toNatInt_of_mod a w halign
  have hpmaC := pmaCheck_ram σ a w _ (Or.inr rfl) hpma hlo hhiram htmod
  have hpmp := pmp_allows σ (physaddr.Physaddr a) w
    (MemoryAccessType.Store mem_payload.Data) vpmpaddr hcfg haddr
  have hmmio := within_mmio_writable_ram_false σ a w hbase hwle hlo hhiwin
  have hsplit := split_misaligned_aligned_w σ a w 0 Splittability.CannotSplit htmod
  simp only [EStateM.run] at hpmaC hpmp hmmio hsplit hram
  unfold checked_mem_write
  simp only [check_pma_with_pmp_priority, write_kind_of_flags, misaligned_order,
    sys_misaligned_order_decreasing, bits_of_physaddr,
    LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, pure]
  rw [hpmaC]
  simp only [EStateM.pure, ExceptT.bindCont, EStateM.map, EStateM.bind]
  rw [hsplit]
  simp only [EStateM.pure, EStateM.bind, ExceptT.bindCont, EStateM.map]
  simp only [Int.reduceNeg, Bool.false_eq_true, if_false,
    show ((1 : Int) - 1) = 0 from by decide,
    show Int.toNat 1 = 1 from rfl, Int.toNat_natCast,
    show Int.toNat 0 = 0 from rfl]
  rw [untilFuelM]
  simp only [untilFuelM.go]
  simp only [ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure,
    EStateM.map, EStateM.bind, EStateM.pure, bind, pure, Pure.pure,
    LeanRV64DExecutable.assert, PreSail.assert, if_true,
    show (↑(0 : Nat) * ((w : Nat) : Int)) = (0 : Int) from by simp, addInt_zero_pa',
    hpmp, hmmio, Bool.false_eq_true, if_false]
  rw [setWidth_extractLsb_full w hwpos data _ _ (by omega) (by omega), hram]
  simp only [EStateM.pure, EStateM.bind, ExceptT.bindCont, Bool.true_and,
    beq_self_eq_true, if_true]

theorem mem_write_value_w
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (w : Nat) (data : BitVec (8 * w))
    (vmstatus : RegisterType Register.mstatus)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hwpos : 0 < w) (hwle : w ≤ 8)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hlo : 0x80000000 ≤ a.toNat)
    (hhiram : a.toNat + w ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ a.toNat)
    (halign : a.toNat % w = 0)
    (hram : (Functions.write_ram write_kind.Write_plain (physaddr.Physaddr a) w data ()).run σ
      = .ok true σ') :
    (mem_write_value (physaddr.Physaddr a) w data
        (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA false false false).run σ
      = .ok (.Ok true) σ' := by
  have hcmw := checked_mem_write_w σ σ' a w data vpmpaddr hwpos hwle hpma hcfg haddr hbase
    hlo hhiram hhiwin halign hram
  have hep := effectivePrivilege_machine σ (MemoryAccessType.Store mem_payload.Data) vmstatus
    Privilege.Machine (by decide) hmprv
  simp only [EStateM.run] at hcmw hep
  unfold mem_write_value mem_write_value_meta mem_write_value_priv_meta
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hmstatus, hpriv]
  rw [hep]
  simp only [default_meta]
  rw [hcmw]

theorem mem_write_ea_w
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (w : Nat)
    (vmstatus : RegisterType Register.mstatus)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hwpos : 0 < w) (hwle : w ≤ 8)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hlo : 0x80000000 ≤ a.toNat)
    (hhiram : a.toNat + w ≤ 0x100000000)
    (halign : a.toNat % w = 0) :
    (mem_write_ea (physaddr.Physaddr a) w (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA false false false).run σ
      = .ok (.Ok ()) σ := by
  have htmod := tmod_toNatInt_of_mod a w halign
  have hpmaC := pmaCheck_ram σ a w _ (Or.inr rfl) hpma hlo hhiram htmod
  have hpmp := pmp_allows σ (physaddr.Physaddr a) w
    (MemoryAccessType.Store mem_payload.Data) vpmpaddr hcfg haddr
  have hep := effectivePrivilege_machine σ (MemoryAccessType.Store mem_payload.Data) vmstatus
    Privilege.Machine (by decide) hmprv
  have hsplit := split_misaligned_aligned_w σ a w 0 Splittability.CannotSplit htmod
  simp only [EStateM.run] at hpmaC hpmp hep hsplit
  unfold mem_write_ea
  simp only [check_pma_with_pmp_priority, write_kind_of_flags, misaligned_order,
    sys_misaligned_order_decreasing, bits_of_physaddr, write_ram_ea,
    LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, pure, LeanRV64DExecutable.readReg,
    Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hmstatus, hpriv]
  simp only [EStateM.pure, EStateM.map, EStateM.bind, ExceptT.bindCont,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hmstatus, hpriv]
  rw [hep]
  simp only [EStateM.pure, ExceptT.bindCont, EStateM.map, EStateM.bind]
  rw [hpmaC]
  simp only [EStateM.pure, ExceptT.bindCont, EStateM.map, EStateM.bind]
  rw [hsplit]
  simp only [EStateM.pure, EStateM.bind, ExceptT.bindCont, EStateM.map]
  simp only [Int.reduceNeg, Bool.false_eq_true, if_false,
    show ((1 : Int) - 1) = 0 from by decide,
    show Int.toNat 1 = 1 from rfl, Int.toNat_natCast,
    show Int.toNat 0 = 0 from rfl]
  rw [untilFuelM]
  simp only [untilFuelM.go]
  simp only [ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure,
    EStateM.map, EStateM.bind, EStateM.pure, bind, pure, Pure.pure,
    LeanRV64DExecutable.assert, PreSail.assert, if_true,
    show (↑(0 : Nat) * ((w : Nat) : Int)) = (0 : Int) from by simp, addInt_zero_pa',
    hpmp, Bool.false_eq_true, if_false, beq_self_eq_true]

theorem mem_write_ea_8
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64)
    (vmstatus : RegisterType Register.mstatus)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hlo : 0x80000000 ≤ a.toNat)
    (hhiram : a.toNat + 8 ≤ 0x100000000)
    (halign : a.toNat % 8 = 0) :
    (mem_write_ea (physaddr.Physaddr a) 8 (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA false false false).run σ
      = .ok (.Ok ()) σ :=
  mem_write_ea_w σ a 8 vmstatus vpmpaddr (by decide) (by decide) hpriv hmstatus hmprv hpma hcfg
    haddr hlo hhiram halign

theorem translateAddr_machine_store
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64)
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1) :
    (translateAddr (virtaddr.Virtaddr a) (MemoryAccessType.Store mem_payload.Data)).run σ
      = .ok (.Ok (physaddr.Physaddr (zero_extend (m := 64) a),
          page_based_mem_type.PBMT_PMA, ())) σ := by
  unfold translateAddr
  simp only [LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, EStateM.pure, LeanRV64DExecutable.readReg,
    Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hpriv, hmstatus,
    effectivePrivilege, translationMode, is_shadow_stack_access, bne,
    bits_of_virtaddr, init_ext_ptw, pure]
  have hda : (MemoryAccessType.Store mem_payload.Data ==
      (MemoryAccessType.InstructionFetch () : MemoryAccessType mem_payload)) = false := by
    decide
  have hmprv0 : (_get_Mstatus_MPRV vmstatus == 1#1) = false := by
    rw [hmprv]; decide
  have hpm : (Privilege.Machine == Privilege.Machine) = true := by decide
  have hb : (SATPMode.Bare == SATPMode.Bare) = true := by decide
  simp only [hda, hmprv0, hpm, hb, EStateM.pure, EStateM.map, EStateM.bind,
    ExceptT.bindCont, Bool.not_false, Bool.and_false,
    if_false, if_true, Bool.false_eq_true]

theorem get_pmlen_store_machine
    (σ : SequentialState RegisterType trivialChoiceSource)
    (vmstatus : RegisterType Register.mstatus)
    (vmseccfg : RegisterType Register.mseccfg)
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hseccfg : σ.regs.get? Register.mseccfg = some vmseccfg)
    (hpmm : _get_Seccfg_PMM vmseccfg = 0#2) :
    (get_pmlen (MemoryAccessType.Store mem_payload.Data) Privilege.Machine).run σ
      = .ok 0 σ := by
  have hpmmd : pmm_mode_backwards (_get_Seccfg_PMM vmseccfg)
      = PointerMaskingMode.PMM_Disabled := by rw [hpmm]; simp only [pmm_mode_backwards]
  have hcond : (!(MemoryAccessType.Store mem_payload.Data ==
        (MemoryAccessType.InstructionFetch () : MemoryAccessType mem_payload)) &&
      (!(MemoryAccessType.Store mem_payload.Data ==
          (MemoryAccessType.Load mem_payload.PageTableEntry : MemoryAccessType mem_payload)) &&
        (!(MemoryAccessType.Store mem_payload.Data ==
            (MemoryAccessType.Store mem_payload.PageTableEntry : MemoryAccessType mem_payload)) &&
          ((Privilege.Machine == Privilege.Machine || _get_Mstatus_MXR vmstatus == 0#1) &&
            Functions.xlen == 64)))) = true := by
    simp only [show (Privilege.Machine == Privilege.Machine) = true from by decide, Bool.true_or]
    decide
  unfold get_pmlen is_pmm_applicable get_pmm
  simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hmstatus, hseccfg, bne, hpmmd,
    hcond, if_true]

theorem transform_effective_address_store
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64)
    (vmstatus : RegisterType Register.mstatus)
    (vmseccfg : RegisterType Register.mseccfg)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hseccfg : σ.regs.get? Register.mseccfg = some vmseccfg)
    (hpmm : _get_Seccfg_PMM vmseccfg = 0#2) :
    (transform_effective_address (virtaddr.Virtaddr a)
        (MemoryAccessType.Store mem_payload.Data)).run σ
      = .ok (virtaddr.Virtaddr (zero_extend (m := 64) a)) σ := by
  have hep := effectivePrivilege_machine σ (MemoryAccessType.Store mem_payload.Data) vmstatus
    Privilege.Machine (by decide) hmprv
  have hpml := get_pmlen_store_machine σ vmstatus vmseccfg hmstatus hseccfg hpmm
  have htm := translationMode_machine σ
  simp only [EStateM.run] at hep hpml htm
  unfold transform_effective_address
  simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hmstatus, hpriv]
  rw [hep]
  simp only [EStateM.bind]
  rw [hpml]
  simp only [EStateM.bind]
  rw [htm]
  simp only [EStateM.bind, EStateM.pure,
    show (SATPMode.Bare == SATPMode.Bare) = true from by decide,
    if_true, pm_transform_PA]
  have hidx : ((Functions.xlen : Int) - ((Int.toNat 0 : Nat) : Int) - 1).toNat = 63 := by decide
  rw [hidx]
  have hext : (Sail.BitVec.extractLsb a 63 0) = a := by
    apply BitVec.eq_of_toNat_eq
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
      Nat.shiftRight_zero, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by have := a.isLt; simpa using this)]
  rw [hext]

theorem page_mask_eq : (0xFFFFFFFFFFFFF000#64) = (BitVec.allOnes 64) <<< 12 := by
  apply BitVec.eq_of_toNat_eq; decide

theorem and_page_mask_shift (a : BitVec 64) :
    (a &&& 0xFFFFFFFFFFFFF000#64) = (a >>> 12) <<< 12 := by
  rw [page_mask_eq]; ext i
  simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight,
    BitVec.getElem_allOnes]
  by_cases h : (i : Nat) < 12
  · simp [h]
  · have hi : 12 + (i - 12) = i := by omega
    rw [hi, BitVec.getLsbD_eq_getElem (by omega)]; simp [h, Bool.and_comm]

theorem and_page_mask_toNat_store (a : BitVec 64) :
    (a &&& 0xFFFFFFFFFFFFF000#64).toNat = a.toNat / 4096 * 4096 := by
  rw [and_page_mask_shift, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  have ha : a.toNat < 2 ^ 64 := a.isLt
  have hb : a.toNat / 4096 < 2 ^ 52 := by omega
  rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]

theorem split_on_page_boundary_store_w
    (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64) (w : Nat)
    (hwpos : 0 < w) (hwle : w ≤ 8)
    (hpage : (a.toNat + (w - 1)) / 4096 = a.toNat / 4096) :
    (split_on_page_boundary a w).run σ = .ok ((w : Int), 0) σ := by
  have hmask : (Sail.BitVec.updateSubrange ((ones (n := 64)) : BitVec 64)
      (Functions.pagesize_bits -i 1) 0 (zeros (n := ((12 -i 1) -i (0 -i 1))))) = 0xFFFFFFFFFFFFF000#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  simp only [split_on_page_boundary, Sail.BitVec.length, hmask]
  have hai : BitVec.addInt a ((w : Nat) : Int) = a + BitVec.ofNat 64 w := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.addInt]; rfl
  have hsi : BitVec.subInt (a + BitVec.ofNat 64 w) 1 = a + BitVec.ofNat 64 (w - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.subInt, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_sub]
    have h64 : a.toNat < 2 ^ 64 := a.isLt
    have : (BitVec.ofInt 64 1).toNat = 1 := by decide
    omega
  have hintra : ((a &&& 0xFFFFFFFFFFFFF000#64)
      == (BitVec.subInt (BitVec.addInt a ((w : Nat) : Int)) 1 &&& 0xFFFFFFFFFFFFF000#64)) = true := by
    rw [hai, hsi]
    simp only [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [and_page_mask_toNat_store, and_page_mask_toNat_store]
    have h64 : a.toNat < 2 ^ 64 := a.isLt
    have haw : (a + BitVec.ofNat 64 (w - 1)).toNat = a.toNat + (w - 1) := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    rw [haw, hpage]
  simp only [hintra, if_true, bind, EStateM.bind, EStateM.run, pure, EStateM.pure]

theorem vmem_write_addr_w
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (w : Nat) (data : BitVec (8 * w))
    (vmstatus : RegisterType Register.mstatus)
    (hwpos : 0 < w) (hwle : w ≤ 8)
    (halign : a.toNat % w = 0)
    (hpage : (a.toNat + (w - 1)) / 4096 = a.toNat / 4096)
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (htr : (translateAddr (virtaddr.Virtaddr a) (MemoryAccessType.Store mem_payload.Data)).run σ
      = .ok (.Ok (physaddr.Physaddr (zero_extend (m := 64) a), page_based_mem_type.PBMT_PMA, ())) σ)
    (hea : (mem_write_ea (physaddr.Physaddr a) w
        (MemoryAccessType.Store mem_payload.Data) page_based_mem_type.PBMT_PMA
        false false false).run σ = .ok (.Ok ()) σ)
    (hmwv : (mem_write_value (physaddr.Physaddr a) w data
        (MemoryAccessType.Store mem_payload.Data) page_based_mem_type.PBMT_PMA
        false false false).run σ = .ok (.Ok true) σ')
    (hwval : (BitVec.setWidth (8 * w)
        (Sail.BitVec.extractLsb data (8 * (w : Int) - 1).toNat 0)) = data) :
    (vmem_write_addr (virtaddr.Virtaddr a) w data
        (MemoryAccessType.Store mem_payload.Data) false false false).run σ
      = .ok (.Ok true) σ' := by
  have htmod : Int.tmod (BitVec.toNatInt a) w = 0 := by
    simp only [BitVec.toNatInt]
    have : ((Int.ofNat a.toNat).tmod (Int.ofNat w)) = Int.ofNat (a.toNat % w) :=
      (Int.ofNat_tmod _ _).symm
    rw [show (w : Int) = Int.ofNat w from rfl, this, halign]; rfl
  have hsplit := split_on_page_boundary_store_w σ a w hwpos hwle hpage
  have hep := effectivePrivilege_machine σ (MemoryAccessType.Store mem_payload.Data) vmstatus
    Privilege.Machine (by decide) hmprv
  have htm := translationMode_machine σ
  have hze : (zero_extend (m := 64) a : BitVec 64) = a := BitVec.setWidth_eq a
  simp only [EStateM.run] at hsplit hep htm htr hea hmwv
  unfold vmem_write_addr
  simp only [LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, pure, EStateM.pure,
    is_aligned_vaddr, bits_of_virtaddr, sys_misaligned_order_decreasing,
    is_store_conditional, Functions.not,
    show (!((BitVec.toNatInt a).tmod ((w:Nat):Int) == 0)) = false from by
      rw [show ((w:Nat):Int) = (w:Int) from rfl, htmod]; rfl,
    Bool.not_true, Bool.false_and, Bool.and_false, if_false, if_true,
    Bool.false_eq_true]
  rw [hsplit]
  simp only [bind, Bind.bind, pure, Pure.pure, EStateM.bind, EStateM.pure, ExceptT.bindCont,
    EStateM.map, LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hmstatus, hpriv]
  rw [hep]
  simp only [bind, Bind.bind, EStateM.bind, EStateM.pure, ExceptT.bindCont, EStateM.map]
  rw [htm]
  simp only [bne, bind, Bind.bind, EStateM.bind, EStateM.pure, ExceptT.bindCont, EStateM.map,
    show (SATPMode.Bare != SATPMode.Bare) = false from by decide,
    Bool.false_and, Bool.and_false, if_false, Bool.false_eq_true]
  rw [htr]
  simp only [EStateM.bind, EStateM.pure, ExceptT.bindCont, EStateM.map, hze,
    LeanRV64DExecutable.assert, PreSail.assert,
    show ((false : Bool) == false) = true from by decide, if_true,
    Bool.and_false, Bool.false_and, if_false, Bool.false_eq_true]
  simp only [bind, Bind.bind, pure, Pure.pure, EStateM.bind, EStateM.pure, ExceptT.bindCont,
    EStateM.map, ite_self, Int.toNat_natCast,
    show (!(SATPMode.Bare == SATPMode.Bare) && (0 : Int) >b 0) = false from by decide]
  rw [hea]
  simp only [EStateM.bind, EStateM.pure, ExceptT.bindCont, EStateM.map]
  rw [show (if (!(SATPMode.Bare == SATPMode.Bare) && (0 : Int) >b 0) = true
      then ((w:Nat):Int) else ((w:Nat):Int)) = ((w:Nat):Int) from ite_self _]
  simp only [Int.toNat_natCast]
  rw [hwval, hmwv]
  simp only [LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, EStateM.pure, pure, Pure.pure,
    Bool.true_and, Bool.and_true]
  rfl

theorem vmem_write_addr_ram_w
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (w : Nat) (data : BitVec (8 * w))
    (vmstatus : RegisterType Register.mstatus)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hwpos : 0 < w) (hwle : w ≤ 8)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hlo : 0x80000000 ≤ a.toNat)
    (hhiram : a.toNat + w ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ a.toNat)
    (halign : a.toNat % w = 0)
    (hpage : (a.toNat + (w - 1)) / 4096 = a.toNat / 4096)
    (hram : (Functions.write_ram write_kind.Write_plain (physaddr.Physaddr a) w data ()).run σ
      = .ok true σ') :
    (vmem_write_addr (virtaddr.Virtaddr a) w data
        (MemoryAccessType.Store mem_payload.Data) false false false).run σ
      = .ok (.Ok true) σ' :=
  vmem_write_addr_w σ σ' a w data vmstatus hwpos hwle halign hpage hmstatus hpriv hmprv
    (translateAddr_machine_store σ a vmstatus hpriv hmstatus hmprv)
    (mem_write_ea_w σ a w vmstatus vpmpaddr hwpos hwle hpriv hmstatus hmprv hpma hcfg haddr
      hlo hhiram halign)
    (mem_write_value_w σ σ' a w data vmstatus vpmpaddr hwpos hwle hpriv hmstatus hmprv hpma
      hcfg haddr hbase hlo hhiram hhiwin halign hram)
    (setWidth_extractLsb_full w hwpos data _ _ (by omega) rfl)

theorem vmem_write_addr_8
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (data : BitVec (8 * 8))
    (vmstatus : RegisterType Register.mstatus)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hlo : 0x80000000 ≤ a.toNat)
    (hhiram : a.toNat + 8 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ a.toNat)
    (halign : a.toNat % 8 = 0) :
    (vmem_write_addr (virtaddr.Virtaddr a) 8 data
        (MemoryAccessType.Store mem_payload.Data) false false false).run σ
      = .ok (.Ok true)
          { σ with mem := ((((((((σ.mem.insert a.toNat (data.extractLsb' 0 8)).insert
              (a.toNat + 1) (data.extractLsb' 8 8)).insert
              (a.toNat + 2) (data.extractLsb' 16 8)).insert
              (a.toNat + 3) (data.extractLsb' 24 8)).insert
              (a.toNat + 4) (data.extractLsb' 32 8)).insert
              (a.toNat + 5) (data.extractLsb' 40 8)).insert
              (a.toNat + 6) (data.extractLsb' 48 8)).insert
              (a.toNat + 7) (data.extractLsb' 56 8)) } :=
  vmem_write_addr_ram_w σ _ a 8 data vmstatus vpmpaddr (by decide) (by decide) hpriv hmstatus
    hmprv hpma hcfg haddr hbase hlo hhiram hhiwin halign (by omega) (write_ram_8 σ a data)

theorem vmem_write_addr_4
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (data : BitVec (8 * 4))
    (vmstatus : RegisterType Register.mstatus)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hlo : 0x80000000 ≤ a.toNat)
    (hhiram : a.toNat + 4 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ a.toNat)
    (halign : a.toNat % 4 = 0) :
    (vmem_write_addr (virtaddr.Virtaddr a) 4 data
        (MemoryAccessType.Store mem_payload.Data) false false false).run σ
      = .ok (.Ok true)
          { σ with mem := ((((σ.mem.insert a.toNat (data.extractLsb' 0 8)).insert (a.toNat + 1) (data.extractLsb' 8 8)).insert (a.toNat + 2) (data.extractLsb' 16 8)).insert (a.toNat + 3) (data.extractLsb' 24 8)) } :=
  vmem_write_addr_ram_w σ _ a 4 data vmstatus vpmpaddr (by decide) (by decide) hpriv hmstatus
    hmprv hpma hcfg haddr hbase hlo hhiram hhiwin halign (by omega) (write_ram_4 σ a data)

theorem vmem_write_addr_2
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (data : BitVec (8 * 2))
    (vmstatus : RegisterType Register.mstatus)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hlo : 0x80000000 ≤ a.toNat)
    (hhiram : a.toNat + 2 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ a.toNat)
    (halign : a.toNat % 2 = 0) :
    (vmem_write_addr (virtaddr.Virtaddr a) 2 data
        (MemoryAccessType.Store mem_payload.Data) false false false).run σ
      = .ok (.Ok true)
          { σ with mem := ((σ.mem.insert a.toNat (data.extractLsb' 0 8)).insert (a.toNat + 1) (data.extractLsb' 8 8)) } :=
  vmem_write_addr_ram_w σ _ a 2 data vmstatus vpmpaddr (by decide) (by decide) hpriv hmstatus
    hmprv hpma hcfg haddr hbase hlo hhiram hhiwin halign (by omega) (write_ram_2 σ a data)

theorem vmem_write_addr_1
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (data : BitVec (8 * 1))
    (vmstatus : RegisterType Register.mstatus)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hlo : 0x80000000 ≤ a.toNat)
    (hhiram : a.toNat + 1 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ a.toNat) :
    (vmem_write_addr (virtaddr.Virtaddr a) 1 data
        (MemoryAccessType.Store mem_payload.Data) false false false).run σ
      = .ok (.Ok true)
          { σ with mem := σ.mem.insert a.toNat data } :=
  vmem_write_addr_ram_w σ _ a 1 data vmstatus vpmpaddr (by decide) (by decide) hpriv hmstatus
    hmprv hpma hcfg haddr hbase hlo hhiram hhiwin (Nat.mod_one _) (by omega) (write_ram_1 σ a data)

end Vsa.Sim
