import Vsa.Sim.Hooks
import Vsa.Sim.Pmp

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem effectivePrivilege_store
    (σ : SequentialState RegisterType trivialChoiceSource)
    (m : BitVec 64) (p : Privilege)
    (hmprv : _get_Mstatus_MPRV m = 0#1) :
    (effectivePrivilege (MemoryAccessType.Store mem_payload.Data) m p).run σ
      = .ok p σ := by
  simp only [effectivePrivilege, bne, hmprv]
  have hc : (MemoryAccessType.Store mem_payload.Data ==
      (MemoryAccessType.InstructionFetch () : MemoryAccessType mem_payload)) = false := by
    decide
  simp [simp_sail, EStateM.run, pure, EStateM.pure, hc]

theorem split_misaligned_aligned_w
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (w : Nat) (e : Nat) (s : Splittability)
    (ha : Int.tmod (BitVec.toNatInt a) w = 0) :
    (split_misaligned (physaddr.Physaddr a) w e s).run σ
      = .ok (1, w) σ := by
  simp only [split_misaligned]
  split
  · simp [simp_sail, EStateM.run, pure, EStateM.pure]
  · rename_i hneg
    exfalso
    apply hneg
    simp only [Bool.or_eq_true, beq_iff_eq]
    refine Or.inr (Or.inl ?_)
    exact_mod_cast ha

open MemoryRegionType AtomicSupport Reservability misaligned_exception in

theorem pmaCheck_ram_write
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (w : Nat) (wbv : BitVec 64)
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hwpos : 0 < w) (hwle : w ≤ 8)
    (hwbv : (to_bits w : BitVec 64) = wbv)
    (hlo : 0x80000000 ≤ a.toNat)
    (hhi : a.toNat + w ≤ 0x100000000)
    (halign : Int.tmod (BitVec.toNatInt a) w = 0) :
    (pmaCheck (physaddr.Physaddr a) w (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA false).run σ
      = .ok (.Ok { splittable := Splittability.CannotSplit, granule_size_exp := 0 }) σ := by
  have hmatch : matching_pma_region_bits_range initPmaRegions
      (zero_extend (bits_of_physaddr (physaddr.Physaddr a))) wbv
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
    have hwn : wbv.toNat = w := by
      rw [← hwbv]
      simp only [to_bits, get_slice_int, BitVec.extractLsb', Nat.zero_add,
        BitVec.toNat_ofInt, Nat.shiftRight_zero]
      have hmod : ((w : Int) % ((2 ^ (64 + 1) : Nat) : Int)) = (w : Int) := by
        rw [Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le w)]
        have : (w : Int) < ((2 ^ (64 + 1) : Nat) : Int) := by
          have : w < 2 ^ (64 + 1) := by omega
          exact_mod_cast this
        exact this
      rw [hmod, Int.toNat_natCast, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
    rw [hz]
    simp only [initPmaRegions, matching_pma_region_bits_range, range_subset,
      zopz0zIzJ_u, BitVec.toNatInt]
    rw [if_neg, if_neg, if_pos]
    · simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨?_, ?_, ?_⟩ <;> · apply Int.ofNat_le.mpr <;> bv_omega
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
    EStateM.run, EStateM.bind, LeanRV64DExecutable.readReg,
    Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hpma]
  simp only [matching_pma_region, hwbv, pure, EStateM.pure, hmatch, override_PMA,
    Functions.not, LeanRV64DExecutable.assert, PreSail.assert,
    mag_pma_check, is_mag_applicable_access, is_aligned_paddr,
    BitVec.toNatInt, ExceptT.pure, ExceptT.bindCont, ExceptT.mk,
    EStateM.map, EStateM.bind, bind, Bind.bind,
    Bool.not_false, Bool.not_true, Bool.false_eq_true,
    if_false, if_true]
  rw [if_pos]
  · rfl
  · simp only [Bool.or_eq_true, beq_iff_eq]
    exact Or.inl (by exact_mod_cast halign)

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

theorem write_ram_1
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec (8 * 1)) :
    (Functions.write_ram write_kind.Write_plain (physaddr.Physaddr a) 1 v ()).run σ
      = .ok true
          { σ with mem := σ.mem.insert a.toNat v } := by
  simp only [Functions.write_ram, PreSail.sail_mem_write, PreSail.writeBytes,
    PreSail.writeByte, List.ofFn, Fin.foldr_succ, Fin.foldr_zero, List.forM_cons,
    List.forM_nil, __WriteRAM_Meta, Fin.val_succ, Fin.val_zero]
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    get, getThe, MonadStateOf.get, EStateM.get]

theorem write_ram_2
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec (8 * 2)) :
    (Functions.write_ram write_kind.Write_plain (physaddr.Physaddr a) 2 v ()).run σ
      = .ok true
          { σ with mem := ((σ.mem.insert a.toNat (v.extractLsb' 0 8)).insert
              (a.toNat + 1) (v.extractLsb' 8 8)) } := by
  simp only [Functions.write_ram, PreSail.sail_mem_write, PreSail.writeBytes,
    PreSail.writeByte, List.ofFn, Fin.foldr_succ, Fin.foldr_zero, List.forM_cons,
    List.forM_nil, __WriteRAM_Meta, Fin.val_succ, Fin.val_zero]
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    get, getThe, MonadStateOf.get, EStateM.get]

theorem write_ram_4
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec (8 * 4)) :
    (Functions.write_ram write_kind.Write_plain (physaddr.Physaddr a) 4 v ()).run σ
      = .ok true
          { σ with mem := ((((σ.mem.insert a.toNat (v.extractLsb' 0 8)).insert
              (a.toNat + 1) (v.extractLsb' 8 8)).insert
              (a.toNat + 2) (v.extractLsb' 16 8)).insert
              (a.toNat + 3) (v.extractLsb' 24 8)) } := by
  simp only [Functions.write_ram, PreSail.sail_mem_write, PreSail.writeBytes,
    PreSail.writeByte, List.ofFn, Fin.foldr_succ, Fin.foldr_zero, List.forM_cons,
    List.forM_nil, __WriteRAM_Meta, Fin.val_succ, Fin.val_zero]
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    get, getThe, MonadStateOf.get, EStateM.get]

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
              (a.toNat + 7) (v.extractLsb' 56 8)) } := by
  simp only [Functions.write_ram, PreSail.sail_mem_write, PreSail.writeBytes,
    PreSail.writeByte, List.ofFn, Fin.foldr_succ, Fin.foldr_zero, List.forM_cons,
    List.forM_nil, __WriteRAM_Meta, Fin.val_succ, Fin.val_zero]
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    get, getThe, MonadStateOf.get, EStateM.get]

theorem ofInt_zero_gen' (n : Nat) : (BitVec.ofInt n 0) = 0#n := by
  apply BitVec.eq_of_toNat_eq; simp

theorem addInt_zero_pa' (a : physaddrbits) : BitVec.addInt a (0 : Int) = a := by
  simp only [BitVec.addInt, ofInt_zero_gen', BitVec.add_zero]

theorem checked_mem_write_8
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (data : BitVec (8 * 8))
    (vpmpaddr : RegisterType Register.pmpaddr_n)
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
    (checked_mem_write (physaddr.Physaddr a) 8 data
        (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine () false false false).run σ
      = .ok (.Ok true)
          { σ with mem := ((((((((σ.mem.insert a.toNat (data.extractLsb' 0 8)).insert
              (a.toNat + 1) (data.extractLsb' 8 8)).insert
              (a.toNat + 2) (data.extractLsb' 16 8)).insert
              (a.toNat + 3) (data.extractLsb' 24 8)).insert
              (a.toNat + 4) (data.extractLsb' 32 8)).insert
              (a.toNat + 5) (data.extractLsb' 40 8)).insert
              (a.toNat + 6) (data.extractLsb' 48 8)).insert
              (a.toNat + 7) (data.extractLsb' 56 8)) } := by
  have htmod : Int.tmod (BitVec.toNatInt a) 8 = 0 := by
    simp only [BitVec.toNatInt]
    have : ((Int.ofNat a.toNat).tmod (Int.ofNat 8)) = Int.ofNat (a.toNat % 8) :=
      (Int.ofNat_tmod _ _).symm
    rw [show (8 : Int) = Int.ofNat 8 from rfl, this, halign]; rfl
  have hpmaC := pmaCheck_ram_write σ a 8 (BitVec.ofNat 64 8) hpma (by decide) (by decide)
    (by decide) hlo hhiram htmod
  have hpmp := pmp_allows σ (physaddr.Physaddr a) 8
    (MemoryAccessType.Store mem_payload.Data) vpmpaddr hcfg haddr
  have hmmio := within_mmio_writable_ram_false σ a 8 hbase (by decide) hlo hhiwin
  have hsplit : (split_misaligned (physaddr.Physaddr a) 8 0 Splittability.CannotSplit).run σ
      = .ok (1, 8) σ := split_misaligned_aligned_w σ a 8 0 Splittability.CannotSplit htmod
  have hwval : (BitVec.setWidth (8 * Int.toNat 8)
      (Sail.BitVec.extractLsb data (8 * (((0:Nat):Int) + 1) * 8 - 1).toNat
        (8 * ((0:Nat):Int) * 8).toNat)) = data := by
    have hhi : (8 * (((0:Nat):Int) + 1) * 8 - 1).toNat = 63 := by decide
    have hlo : (8 * ((0:Nat):Int) * 8).toNat = 0 := by decide
    have hw : (8 * Int.toNat 8) = 64 := by decide
    have hlt : data.toNat < 2 ^ 64 := by have h := data.isLt; simpa using h
    apply BitVec.eq_of_toNat_eq
    simp only [hhi, hlo, hw, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
      BitVec.toNat_setWidth, Nat.shiftRight_zero, BitVec.toNat_ofNat,
      Nat.reduceSub, Nat.reduceAdd]
    rw [Nat.mod_eq_of_lt hlt]
    exact Nat.mod_eq_of_lt hlt
  have hram := write_ram_8 σ a data
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
    show Int.toNat 1 = 1 from rfl, show Int.toNat 8 = 8 from rfl,
    show Int.toNat 0 = 0 from rfl]
  rw [untilFuelM]
  simp only [untilFuelM.go]
  simp only [ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure,
    EStateM.map, EStateM.bind, EStateM.pure, bind, pure, Pure.pure,
    LeanRV64DExecutable.assert, PreSail.assert, if_true,
    show (↑(0 : Nat) * (8 : Int)) = (0 : Int) from by decide, addInt_zero_pa',
    hpmp, hmmio, Bool.false_eq_true, if_false]
  rw [hwval]
  have hram' : Functions.write_ram write_kind.Write_plain (physaddr.Physaddr a) (Int.toNat 8) data () σ
      = EStateM.Result.ok true
          { σ with mem := ((((((((σ.mem.insert a.toNat (data.extractLsb' 0 8)).insert
              (a.toNat + 1) (data.extractLsb' 8 8)).insert
              (a.toNat + 2) (data.extractLsb' 16 8)).insert
              (a.toNat + 3) (data.extractLsb' 24 8)).insert
              (a.toNat + 4) (data.extractLsb' 32 8)).insert
              (a.toNat + 5) (data.extractLsb' 40 8)).insert
              (a.toNat + 6) (data.extractLsb' 48 8)).insert
              (a.toNat + 7) (data.extractLsb' 56 8)) } := hram
  rw [hram']
  simp only [EStateM.pure, EStateM.bind, ExceptT.bindCont, Bool.true_and,
    beq_self_eq_true, if_true]

theorem checked_mem_write_4
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (data : BitVec (8 * 4))
    (vpmpaddr : RegisterType Register.pmpaddr_n)
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
    (checked_mem_write (physaddr.Physaddr a) 4 data
        (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine () false false false).run σ
      = .ok (.Ok true)
          { σ with mem := ((((σ.mem.insert a.toNat (data.extractLsb' 0 8)).insert
              (a.toNat + 1) (data.extractLsb' 8 8)).insert
              (a.toNat + 2) (data.extractLsb' 16 8)).insert
              (a.toNat + 3) (data.extractLsb' 24 8)) } := by
  have htmod : Int.tmod (BitVec.toNatInt a) 4 = 0 := by
    simp only [BitVec.toNatInt]
    have : ((Int.ofNat a.toNat).tmod (Int.ofNat 4)) = Int.ofNat (a.toNat % 4) :=
      (Int.ofNat_tmod _ _).symm
    rw [show (4 : Int) = Int.ofNat 4 from rfl, this, halign]; rfl
  have hpmaC := pmaCheck_ram_write σ a 4 (BitVec.ofNat 64 4) hpma (by decide) (by decide)
    (by decide) hlo hhiram htmod
  have hpmp := pmp_allows σ (physaddr.Physaddr a) 4
    (MemoryAccessType.Store mem_payload.Data) vpmpaddr hcfg haddr
  have hmmio := within_mmio_writable_ram_false σ a 4 hbase (by decide) hlo hhiwin
  have hsplit : (split_misaligned (physaddr.Physaddr a) 4 0 Splittability.CannotSplit).run σ
      = .ok (1, 4) σ := split_misaligned_aligned_w σ a 4 0 Splittability.CannotSplit htmod
  have hwval : (BitVec.setWidth (8 * Int.toNat 4)
      (Sail.BitVec.extractLsb data (8 * (((0:Nat):Int) + 1) * 4 - 1).toNat
        (8 * ((0:Nat):Int) * 4).toNat)) = data := by
    have hhi : (8 * (((0:Nat):Int) + 1) * 4 - 1).toNat = 31 := by decide
    have hlo : (8 * ((0:Nat):Int) * 4).toNat = 0 := by decide
    have hw : (8 * Int.toNat 4) = 32 := by decide
    have hlt : data.toNat < 2 ^ 32 := by have h := data.isLt; simpa using h
    apply BitVec.eq_of_toNat_eq
    simp only [hhi, hlo, hw, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
      BitVec.toNat_setWidth, Nat.shiftRight_zero, BitVec.toNat_ofNat,
      Nat.reduceSub, Nat.reduceAdd]
    rw [Nat.mod_eq_of_lt hlt]
    exact Nat.mod_eq_of_lt hlt
  have hram := write_ram_4 σ a data
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
    show Int.toNat 1 = 1 from rfl, show Int.toNat 4 = 4 from rfl,
    show Int.toNat 0 = 0 from rfl]
  rw [untilFuelM]
  simp only [untilFuelM.go]
  simp only [ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure,
    EStateM.map, EStateM.bind, EStateM.pure, bind, pure, Pure.pure,
    LeanRV64DExecutable.assert, PreSail.assert, if_true,
    show (↑(0 : Nat) * (4 : Int)) = (0 : Int) from by decide, addInt_zero_pa',
    hpmp, hmmio, Bool.false_eq_true, if_false]
  rw [hwval]
  have hram' : Functions.write_ram write_kind.Write_plain (physaddr.Physaddr a) (Int.toNat 4) data () σ
      = EStateM.Result.ok true
          { σ with mem := ((((σ.mem.insert a.toNat (data.extractLsb' 0 8)).insert
              (a.toNat + 1) (data.extractLsb' 8 8)).insert
              (a.toNat + 2) (data.extractLsb' 16 8)).insert
              (a.toNat + 3) (data.extractLsb' 24 8)) } := hram
  rw [hram']
  simp only [EStateM.pure, EStateM.bind, ExceptT.bindCont, Bool.true_and,
    beq_self_eq_true, if_true]

theorem checked_mem_write_2
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (data : BitVec (8 * 2))
    (vpmpaddr : RegisterType Register.pmpaddr_n)
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
    (checked_mem_write (physaddr.Physaddr a) 2 data
        (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine () false false false).run σ
      = .ok (.Ok true)
          { σ with mem := ((σ.mem.insert a.toNat (data.extractLsb' 0 8)).insert
              (a.toNat + 1) (data.extractLsb' 8 8)) } := by
  have htmod : Int.tmod (BitVec.toNatInt a) 2 = 0 := by
    simp only [BitVec.toNatInt]
    have : ((Int.ofNat a.toNat).tmod (Int.ofNat 2)) = Int.ofNat (a.toNat % 2) :=
      (Int.ofNat_tmod _ _).symm
    rw [show (2 : Int) = Int.ofNat 2 from rfl, this, halign]; rfl
  have hpmaC := pmaCheck_ram_write σ a 2 (BitVec.ofNat 64 2) hpma (by decide) (by decide)
    (by decide) hlo hhiram htmod
  have hpmp := pmp_allows σ (physaddr.Physaddr a) 2
    (MemoryAccessType.Store mem_payload.Data) vpmpaddr hcfg haddr
  have hmmio := within_mmio_writable_ram_false σ a 2 hbase (by decide) hlo hhiwin
  have hsplit : (split_misaligned (physaddr.Physaddr a) 2 0 Splittability.CannotSplit).run σ
      = .ok (1, 2) σ := split_misaligned_aligned_w σ a 2 0 Splittability.CannotSplit htmod
  have hwval : (BitVec.setWidth (8 * Int.toNat 2)
      (Sail.BitVec.extractLsb data (8 * (((0:Nat):Int) + 1) * 2 - 1).toNat
        (8 * ((0:Nat):Int) * 2).toNat)) = data := by
    have hhi : (8 * (((0:Nat):Int) + 1) * 2 - 1).toNat = 15 := by decide
    have hlo : (8 * ((0:Nat):Int) * 2).toNat = 0 := by decide
    have hw : (8 * Int.toNat 2) = 16 := by decide
    have hlt : data.toNat < 2 ^ 16 := by have h := data.isLt; simpa using h
    apply BitVec.eq_of_toNat_eq
    simp only [hhi, hlo, hw, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
      BitVec.toNat_setWidth, Nat.shiftRight_zero, BitVec.toNat_ofNat,
      Nat.reduceSub, Nat.reduceAdd]
    rw [Nat.mod_eq_of_lt hlt]
    exact Nat.mod_eq_of_lt hlt
  have hram := write_ram_2 σ a data
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
    show Int.toNat 1 = 1 from rfl, show Int.toNat 2 = 2 from rfl,
    show Int.toNat 0 = 0 from rfl]
  rw [untilFuelM]
  simp only [untilFuelM.go]
  simp only [ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure,
    EStateM.map, EStateM.bind, EStateM.pure, bind, pure, Pure.pure,
    LeanRV64DExecutable.assert, PreSail.assert, if_true,
    show (↑(0 : Nat) * (2 : Int)) = (0 : Int) from by decide, addInt_zero_pa',
    hpmp, hmmio, Bool.false_eq_true, if_false]
  rw [hwval]
  have hram' : Functions.write_ram write_kind.Write_plain (physaddr.Physaddr a) (Int.toNat 2) data () σ
      = EStateM.Result.ok true
          { σ with mem := ((σ.mem.insert a.toNat (data.extractLsb' 0 8)).insert
              (a.toNat + 1) (data.extractLsb' 8 8)) } := hram
  rw [hram']
  simp only [EStateM.pure, EStateM.bind, ExceptT.bindCont, Bool.true_and,
    beq_self_eq_true, if_true]

theorem checked_mem_write_1
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (data : BitVec (8 * 1))
    (vpmpaddr : RegisterType Register.pmpaddr_n)
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
    (checked_mem_write (physaddr.Physaddr a) 1 data
        (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine () false false false).run σ
      = .ok (.Ok true)
          { σ with mem := σ.mem.insert a.toNat data } := by
  have htmod : Int.tmod (BitVec.toNatInt a) 1 = 0 := by
    simp only [BitVec.toNatInt]
    have : ((Int.ofNat a.toNat).tmod (Int.ofNat 1)) = Int.ofNat (a.toNat % 1) :=
      (Int.ofNat_tmod _ _).symm
    rw [show (1 : Int) = Int.ofNat 1 from rfl, this, Nat.mod_one]; rfl
  have hpmaC := pmaCheck_ram_write σ a 1 (BitVec.ofNat 64 1) hpma (by decide) (by decide)
    (by decide) hlo hhiram htmod
  have hpmp := pmp_allows σ (physaddr.Physaddr a) 1
    (MemoryAccessType.Store mem_payload.Data) vpmpaddr hcfg haddr
  have hmmio := within_mmio_writable_ram_false σ a 1 hbase (by decide) hlo hhiwin
  have hsplit : (split_misaligned (physaddr.Physaddr a) 1 0 Splittability.CannotSplit).run σ
      = .ok (1, 1) σ := split_misaligned_aligned_w σ a 1 0 Splittability.CannotSplit htmod
  have hwval : (BitVec.setWidth (8 * Int.toNat 1)
      (Sail.BitVec.extractLsb data (8 * (((0:Nat):Int) + 1) * 1 - 1).toNat
        (8 * ((0:Nat):Int) * 1).toNat)) = data := by
    have hhi : (8 * (((0:Nat):Int) + 1) * 1 - 1).toNat = 7 := by decide
    have hlo : (8 * ((0:Nat):Int) * 1).toNat = 0 := by decide
    have hw : (8 * Int.toNat 1) = 8 := by decide
    have hlt : data.toNat < 2 ^ 8 := by have h := data.isLt; simpa using h
    apply BitVec.eq_of_toNat_eq
    simp only [hhi, hlo, hw, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
      BitVec.toNat_setWidth, Nat.shiftRight_zero, BitVec.toNat_ofNat,
      Nat.reduceSub, Nat.reduceAdd]
    rw [Nat.mod_eq_of_lt hlt]
    exact Nat.mod_eq_of_lt hlt
  have hram := write_ram_1 σ a data
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
    show Int.toNat 1 = 1 from rfl,
    show Int.toNat 0 = 0 from rfl]
  rw [untilFuelM]
  simp only [untilFuelM.go]
  simp only [ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure,
    EStateM.map, EStateM.bind, EStateM.pure, bind, pure, Pure.pure,
    LeanRV64DExecutable.assert, PreSail.assert, if_true,
    show (↑(0 : Nat) * (1 : Int)) = (0 : Int) from by decide, addInt_zero_pa',
    hpmp, hmmio, Bool.false_eq_true, if_false]
  rw [hwval]
  have hram' : Functions.write_ram write_kind.Write_plain (physaddr.Physaddr a) (Int.toNat 1) data () σ
      = EStateM.Result.ok true
          { σ with mem := σ.mem.insert a.toNat data } := hram
  rw [hram']
  simp only [EStateM.pure, EStateM.bind, ExceptT.bindCont, Bool.true_and,
    beq_self_eq_true, if_true]

theorem mem_write_value_8
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
    (mem_write_value (physaddr.Physaddr a) 8 data
        (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA false false false).run σ
      = .ok (.Ok true)
          { σ with mem := ((((((((σ.mem.insert a.toNat (data.extractLsb' 0 8)).insert
              (a.toNat + 1) (data.extractLsb' 8 8)).insert
              (a.toNat + 2) (data.extractLsb' 16 8)).insert
              (a.toNat + 3) (data.extractLsb' 24 8)).insert
              (a.toNat + 4) (data.extractLsb' 32 8)).insert
              (a.toNat + 5) (data.extractLsb' 40 8)).insert
              (a.toNat + 6) (data.extractLsb' 48 8)).insert
              (a.toNat + 7) (data.extractLsb' 56 8)) } := by
  have hcmw := checked_mem_write_8 σ a data vpmpaddr hpma hcfg haddr hbase hlo hhiram
    hhiwin halign
  have hep := effectivePrivilege_store σ vmstatus Privilege.Machine hmprv
  simp only [EStateM.run] at hcmw hep
  unfold mem_write_value mem_write_value_meta mem_write_value_priv_meta
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hmstatus, hpriv]
  rw [hep]
  simp only [EStateM.bind, default_meta]
  rw [hcmw]

theorem mem_write_value_4
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
    (mem_write_value (physaddr.Physaddr a) 4 data
        (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA false false false).run σ
      = .ok (.Ok true)
          { σ with mem := ((((σ.mem.insert a.toNat (data.extractLsb' 0 8)).insert
              (a.toNat + 1) (data.extractLsb' 8 8)).insert
              (a.toNat + 2) (data.extractLsb' 16 8)).insert
              (a.toNat + 3) (data.extractLsb' 24 8)) } := by
  have hcmw := checked_mem_write_4 σ a data vpmpaddr hpma hcfg haddr hbase hlo hhiram
    hhiwin halign
  have hep := effectivePrivilege_store σ vmstatus Privilege.Machine hmprv
  simp only [EStateM.run] at hcmw hep
  unfold mem_write_value mem_write_value_meta mem_write_value_priv_meta
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hmstatus, hpriv]
  rw [hep]
  simp only [default_meta]
  rw [hcmw]

theorem mem_write_value_2
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
    (mem_write_value (physaddr.Physaddr a) 2 data
        (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA false false false).run σ
      = .ok (.Ok true)
          { σ with mem := ((σ.mem.insert a.toNat (data.extractLsb' 0 8)).insert
              (a.toNat + 1) (data.extractLsb' 8 8)) } := by
  have hcmw := checked_mem_write_2 σ a data vpmpaddr hpma hcfg haddr hbase hlo hhiram
    hhiwin halign
  have hep := effectivePrivilege_store σ vmstatus Privilege.Machine hmprv
  simp only [EStateM.run] at hcmw hep
  unfold mem_write_value mem_write_value_meta mem_write_value_priv_meta
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hmstatus, hpriv]
  rw [hep]
  simp only [default_meta]
  rw [hcmw]

theorem mem_write_value_1
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
    (mem_write_value (physaddr.Physaddr a) 1 data
        (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA false false false).run σ
      = .ok (.Ok true) { σ with mem := σ.mem.insert a.toNat data } := by
  have hcmw := checked_mem_write_1 σ a data vpmpaddr hpma hcfg haddr hbase hlo hhiram hhiwin
  have hep := effectivePrivilege_store σ vmstatus Privilege.Machine hmprv
  simp only [EStateM.run] at hcmw hep
  unfold mem_write_value mem_write_value_meta mem_write_value_priv_meta
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hmstatus, hpriv]
  rw [hep]
  simp only [default_meta]
  rw [hcmw]

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
      = .ok (.Ok ()) σ := by
  have htmod : Int.tmod (BitVec.toNatInt a) 8 = 0 := by
    simp only [BitVec.toNatInt]
    have : ((Int.ofNat a.toNat).tmod (Int.ofNat 8)) = Int.ofNat (a.toNat % 8) :=
      (Int.ofNat_tmod _ _).symm
    rw [show (8 : Int) = Int.ofNat 8 from rfl, this, halign]; rfl
  have hpmaC := pmaCheck_ram_write σ a 8 (BitVec.ofNat 64 8) hpma (by decide) (by decide)
    (by decide) hlo hhiram htmod
  have hpmp := pmp_allows σ (physaddr.Physaddr a) 8
    (MemoryAccessType.Store mem_payload.Data) vpmpaddr hcfg haddr
  have hep := effectivePrivilege_store σ vmstatus Privilege.Machine hmprv
  have hsplit : (split_misaligned (physaddr.Physaddr a) 8 0 Splittability.CannotSplit).run σ
      = .ok (1, 8) σ := split_misaligned_aligned_w σ a 8 0 Splittability.CannotSplit htmod
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
    show Int.toNat 1 = 1 from rfl, show Int.toNat 8 = 8 from rfl,
    show Int.toNat 0 = 0 from rfl]
  rw [untilFuelM]
  simp only [untilFuelM.go]
  simp only [ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure,
    EStateM.map, EStateM.bind, EStateM.pure, bind, pure, Pure.pure,
    LeanRV64DExecutable.assert, PreSail.assert, if_true,
    show (↑(0 : Nat) * (8 : Int)) = (0 : Int) from by decide, addInt_zero_pa',
    hpmp, Bool.false_eq_true, if_false, beq_self_eq_true]

theorem mem_write_ea_4
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
    (hhiram : a.toNat + 4 ≤ 0x100000000)
    (halign : a.toNat % 4 = 0) :
    (mem_write_ea (physaddr.Physaddr a) 4 (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA false false false).run σ
      = .ok (.Ok ()) σ := by
  have htmod : Int.tmod (BitVec.toNatInt a) 4 = 0 := by
    simp only [BitVec.toNatInt]
    have : ((Int.ofNat a.toNat).tmod (Int.ofNat 4)) = Int.ofNat (a.toNat % 4) :=
      (Int.ofNat_tmod _ _).symm
    rw [show (4 : Int) = Int.ofNat 4 from rfl, this, halign]; rfl
  have hpmaC := pmaCheck_ram_write σ a 4 (BitVec.ofNat 64 4) hpma (by decide) (by decide)
    (by decide) hlo hhiram htmod
  have hpmp := pmp_allows σ (physaddr.Physaddr a) 4
    (MemoryAccessType.Store mem_payload.Data) vpmpaddr hcfg haddr
  have hep := effectivePrivilege_store σ vmstatus Privilege.Machine hmprv
  have hsplit : (split_misaligned (physaddr.Physaddr a) 4 0 Splittability.CannotSplit).run σ
      = .ok (1, 4) σ := split_misaligned_aligned_w σ a 4 0 Splittability.CannotSplit htmod
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
    show Int.toNat 1 = 1 from rfl, show Int.toNat 4 = 4 from rfl,
    show Int.toNat 0 = 0 from rfl]
  rw [untilFuelM]
  simp only [untilFuelM.go]
  simp only [ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure,
    EStateM.map, EStateM.bind, EStateM.pure, bind, pure, Pure.pure,
    LeanRV64DExecutable.assert, PreSail.assert, if_true,
    show (↑(0 : Nat) * (4 : Int)) = (0 : Int) from by decide, addInt_zero_pa',
    hpmp, Bool.false_eq_true, if_false, beq_self_eq_true]

theorem mem_write_ea_2
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
    (hhiram : a.toNat + 2 ≤ 0x100000000)
    (halign : a.toNat % 2 = 0) :
    (mem_write_ea (physaddr.Physaddr a) 2 (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA false false false).run σ
      = .ok (.Ok ()) σ := by
  have htmod : Int.tmod (BitVec.toNatInt a) 2 = 0 := by
    simp only [BitVec.toNatInt]
    have : ((Int.ofNat a.toNat).tmod (Int.ofNat 2)) = Int.ofNat (a.toNat % 2) :=
      (Int.ofNat_tmod _ _).symm
    rw [show (2 : Int) = Int.ofNat 2 from rfl, this, halign]; rfl
  have hpmaC := pmaCheck_ram_write σ a 2 (BitVec.ofNat 64 2) hpma (by decide) (by decide)
    (by decide) hlo hhiram htmod
  have hpmp := pmp_allows σ (physaddr.Physaddr a) 2
    (MemoryAccessType.Store mem_payload.Data) vpmpaddr hcfg haddr
  have hep := effectivePrivilege_store σ vmstatus Privilege.Machine hmprv
  have hsplit : (split_misaligned (physaddr.Physaddr a) 2 0 Splittability.CannotSplit).run σ
      = .ok (1, 2) σ := split_misaligned_aligned_w σ a 2 0 Splittability.CannotSplit htmod
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
    show Int.toNat 1 = 1 from rfl, show Int.toNat 2 = 2 from rfl,
    show Int.toNat 0 = 0 from rfl]
  rw [untilFuelM]
  simp only [untilFuelM.go]
  simp only [ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure,
    EStateM.map, EStateM.bind, EStateM.pure, bind, pure, Pure.pure,
    LeanRV64DExecutable.assert, PreSail.assert, if_true,
    show (↑(0 : Nat) * (2 : Int)) = (0 : Int) from by decide, addInt_zero_pa',
    hpmp, Bool.false_eq_true, if_false, beq_self_eq_true]

theorem mem_write_ea_1
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
    (hhiram : a.toNat + 1 ≤ 0x100000000) :
    (mem_write_ea (physaddr.Physaddr a) 1 (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA false false false).run σ
      = .ok (.Ok ()) σ := by
  have htmod : Int.tmod (BitVec.toNatInt a) 1 = 0 := by
    simp only [BitVec.toNatInt]
    have : ((Int.ofNat a.toNat).tmod (Int.ofNat 1)) = Int.ofNat (a.toNat % 1) :=
      (Int.ofNat_tmod _ _).symm
    rw [show (1 : Int) = Int.ofNat 1 from rfl, this, Nat.mod_one]; rfl
  have hpmaC := pmaCheck_ram_write σ a 1 (BitVec.ofNat 64 1) hpma (by decide) (by decide)
    (by decide) hlo hhiram htmod
  have hpmp := pmp_allows σ (physaddr.Physaddr a) 1
    (MemoryAccessType.Store mem_payload.Data) vpmpaddr hcfg haddr
  have hep := effectivePrivilege_store σ vmstatus Privilege.Machine hmprv
  have hsplit : (split_misaligned (physaddr.Physaddr a) 1 0 Splittability.CannotSplit).run σ
      = .ok (1, 1) σ := split_misaligned_aligned_w σ a 1 0 Splittability.CannotSplit htmod
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
    show Int.toNat 1 = 1 from rfl,
    show Int.toNat 0 = 0 from rfl]
  rw [untilFuelM]
  simp only [untilFuelM.go]
  simp only [ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure,
    EStateM.map, EStateM.bind, EStateM.pure, bind, pure, Pure.pure,
    LeanRV64DExecutable.assert, PreSail.assert, if_true,
    show (↑(0 : Nat) * (1 : Int)) = (0 : Int) from by decide, addInt_zero_pa',
    hpmp, Bool.false_eq_true, if_false, beq_self_eq_true]

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
  have hep := effectivePrivilege_store σ vmstatus Privilege.Machine hmprv
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

theorem split_on_page_boundary_store_8
    (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64)
    (halign : a.toNat % 8 = 0) :
    (split_on_page_boundary a 8).run σ = .ok (((8 : Nat) : Int), 0) σ := by
  have hmask : (Sail.BitVec.updateSubrange ((ones (n := 64)) : BitVec 64)
      (Functions.pagesize_bits -i 1) 0 (zeros (n := ((12 -i 1) -i (0 -i 1))))) = 0xFFFFFFFFFFFFF000#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  simp only [split_on_page_boundary, Sail.BitVec.length, hmask]
  have hai : BitVec.addInt a ((8 : Nat) : Int) = a + 8#64 := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.addInt]; rfl
  have hsi : BitVec.subInt (a + 8#64) 1 = a + 7#64 := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.subInt]
    have h64 : a.toNat < 2 ^ 64 := a.isLt
    bv_omega
  have hintra : ((a &&& 0xFFFFFFFFFFFFF000#64)
      == (BitVec.subInt (BitVec.addInt a ((8 : Nat) : Int)) 1 &&& 0xFFFFFFFFFFFFF000#64)) = true := by
    rw [hai, hsi, and_page_mask_shift, and_page_mask_shift]
    simp only [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    have h64 : a.toNat < 2^64 := a.isLt
    have hadd : (a + 7#64).toNat = a.toNat + 7 := by rw [BitVec.toNat_add]; simp; omega
    rw [hadd]; simp; omega
  simp only [hintra, if_true, bind, EStateM.bind, EStateM.run, pure, EStateM.pure]

theorem split_on_page_boundary_store_4
    (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64)
    (halign : a.toNat % 4 = 0) :
    (split_on_page_boundary a 4).run σ = .ok (((4 : Nat) : Int), 0) σ := by
  have hmask : (Sail.BitVec.updateSubrange ((ones (n := 64)) : BitVec 64)
      (Functions.pagesize_bits -i 1) 0 (zeros (n := ((12 -i 1) -i (0 -i 1))))) = 0xFFFFFFFFFFFFF000#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  simp only [split_on_page_boundary, Sail.BitVec.length, hmask]
  have hai : BitVec.addInt a ((4 : Nat) : Int) = a + 4#64 := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.addInt]; rfl
  have hsi : BitVec.subInt (a + 4#64) 1 = a + 3#64 := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.subInt]
    have h64 : a.toNat < 2 ^ 64 := a.isLt
    bv_omega
  have hintra : ((a &&& 0xFFFFFFFFFFFFF000#64)
      == (BitVec.subInt (BitVec.addInt a ((4 : Nat) : Int)) 1 &&& 0xFFFFFFFFFFFFF000#64)) = true := by
    rw [hai, hsi, and_page_mask_shift, and_page_mask_shift]
    simp only [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    have h64 : a.toNat < 2^64 := a.isLt
    have hadd : (a + 3#64).toNat = a.toNat + 3 := by rw [BitVec.toNat_add]; simp; omega
    rw [hadd]; simp; omega
  simp only [hintra, if_true, bind, EStateM.bind, EStateM.run, pure, EStateM.pure]

theorem split_on_page_boundary_store_2
    (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64)
    (halign : a.toNat % 2 = 0) :
    (split_on_page_boundary a 2).run σ = .ok (((2 : Nat) : Int), 0) σ := by
  have hmask : (Sail.BitVec.updateSubrange ((ones (n := 64)) : BitVec 64)
      (Functions.pagesize_bits -i 1) 0 (zeros (n := ((12 -i 1) -i (0 -i 1))))) = 0xFFFFFFFFFFFFF000#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  simp only [split_on_page_boundary, Sail.BitVec.length, hmask]
  have hai : BitVec.addInt a ((2 : Nat) : Int) = a + 2#64 := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.addInt]; rfl
  have hsi : BitVec.subInt (a + 2#64) 1 = a + 1#64 := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.subInt]
    have h64 : a.toNat < 2 ^ 64 := a.isLt
    bv_omega
  have hintra : ((a &&& 0xFFFFFFFFFFFFF000#64)
      == (BitVec.subInt (BitVec.addInt a ((2 : Nat) : Int)) 1 &&& 0xFFFFFFFFFFFFF000#64)) = true := by
    rw [hai, hsi, and_page_mask_shift, and_page_mask_shift]
    simp only [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    have h64 : a.toNat < 2^64 := a.isLt
    have hadd : (a + 1#64).toNat = a.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    rw [hadd]; simp; omega
  simp only [hintra, if_true, bind, EStateM.bind, EStateM.run, pure, EStateM.pure]

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
              (a.toNat + 7) (data.extractLsb' 56 8)) } := by
  have htmod : Int.tmod (BitVec.toNatInt a) 8 = 0 := by
    simp only [BitVec.toNatInt]
    have : ((Int.ofNat a.toNat).tmod (Int.ofNat 8)) = Int.ofNat (a.toNat % 8) :=
      (Int.ofNat_tmod _ _).symm
    rw [show (8 : Int) = Int.ofNat 8 from rfl, this, halign]; rfl
  have hsplit := split_on_page_boundary_store_8 σ a halign
  have hep := effectivePrivilege_store σ vmstatus Privilege.Machine hmprv
  have htm := translationMode_machine σ
  have htr := translateAddr_machine_store σ a vmstatus hpriv hmstatus hmprv
  have hea := mem_write_ea_8 σ a vmstatus vpmpaddr hpriv hmstatus hmprv hpma hcfg haddr
    hlo hhiram halign
  have hmwv := mem_write_value_8 σ a data vmstatus vpmpaddr hpriv hmstatus hmprv hpma hcfg
    haddr hbase hlo hhiram hhiwin halign
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
    show (!((BitVec.toNatInt a).tmod ((8:Nat):Int) == 0)) = false from by
      rw [show ((8:Nat):Int) = (8:Int) from rfl, htmod]; rfl,
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
    EStateM.map, ite_self, show ((8:Nat):Int).toNat = 8 from by decide,
    show (!(SATPMode.Bare == SATPMode.Bare) && (0 : Int) >b 0) = false from by decide]
  rw [hea]
  simp only [EStateM.bind, EStateM.pure, ExceptT.bindCont, EStateM.map]
  rw [show (if (!(SATPMode.Bare == SATPMode.Bare) && (0 : Int) >b 0) = true
      then ((8:Nat):Int) else ((8:Nat):Int)) = ((8:Nat):Int) from ite_self _]
  simp only [Int.toNat_natCast]
  have hwval : (BitVec.setWidth (8 * 8)
      (Sail.BitVec.extractLsb data (8 * ((8:Nat):Int) - 1).toNat 0)) = data := by
    have hidx : (8 * ((8:Nat):Int) - 1).toNat = 63 := by decide
    apply BitVec.eq_of_toNat_eq
    simp only [hidx, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
      BitVec.toNat_setWidth, Nat.shiftRight_zero, BitVec.toNat_ofNat,
      Nat.reduceSub, Nat.reduceMul]
    have hlt : data.toNat < 2 ^ 64 := by have h := data.isLt; simpa using h
    rw [Nat.mod_eq_of_lt hlt]
    exact Nat.mod_eq_of_lt hlt
  rw [hwval, hmwv]
  simp only [LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, EStateM.pure, pure, Pure.pure,
    Bool.true_and, Bool.and_true]
  rfl

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
          { σ with mem := ((((σ.mem.insert a.toNat (data.extractLsb' 0 8)).insert (a.toNat + 1) (data.extractLsb' 8 8)).insert (a.toNat + 2) (data.extractLsb' 16 8)).insert (a.toNat + 3) (data.extractLsb' 24 8)) } := by
  have htmod : Int.tmod (BitVec.toNatInt a) 4 = 0 := by
    simp only [BitVec.toNatInt]
    have : ((Int.ofNat a.toNat).tmod (Int.ofNat 4)) = Int.ofNat (a.toNat % 4) :=
      (Int.ofNat_tmod _ _).symm
    rw [show (4 : Int) = Int.ofNat 4 from rfl, this, halign]; rfl
  have hsplit := split_on_page_boundary_store_4 σ a halign
  have hep := effectivePrivilege_store σ vmstatus Privilege.Machine hmprv
  have htm := translationMode_machine σ
  have htr := translateAddr_machine_store σ a vmstatus hpriv hmstatus hmprv
  have hea := mem_write_ea_4 σ a vmstatus vpmpaddr hpriv hmstatus hmprv hpma hcfg haddr
    hlo hhiram halign
  have hmwv := mem_write_value_4 σ a data vmstatus vpmpaddr hpriv hmstatus hmprv hpma hcfg
    haddr hbase hlo hhiram hhiwin halign
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
    show (!((BitVec.toNatInt a).tmod ((4:Nat):Int) == 0)) = false from by
      rw [show ((4:Nat):Int) = (4:Int) from rfl, htmod]; rfl,
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
    EStateM.map, ite_self, show ((4:Nat):Int).toNat = 4 from by decide,
    show (!(SATPMode.Bare == SATPMode.Bare) && (0 : Int) >b 0) = false from by decide]
  rw [hea]
  simp only [EStateM.bind, EStateM.pure, ExceptT.bindCont, EStateM.map]
  rw [show (if (!(SATPMode.Bare == SATPMode.Bare) && (0 : Int) >b 0) = true
      then ((4:Nat):Int) else ((4:Nat):Int)) = ((4:Nat):Int) from ite_self _]
  simp only [Int.toNat_natCast]
  have hwval : (BitVec.setWidth (8 * 4)
      (Sail.BitVec.extractLsb data (8 * ((4:Nat):Int) - 1).toNat 0)) = data := by
    have hidx : (8 * ((4:Nat):Int) - 1).toNat = 31 := by decide
    apply BitVec.eq_of_toNat_eq
    simp only [hidx, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
      BitVec.toNat_setWidth, Nat.shiftRight_zero, BitVec.toNat_ofNat,
      Nat.reduceSub, Nat.reduceMul]
    have hlt : data.toNat < 2 ^ 32 := by have h := data.isLt; simpa using h
    omega
  rw [hwval, hmwv]
  simp only [LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, EStateM.pure, pure, Pure.pure,
    Bool.true_and, Bool.and_true]
  rfl

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
          { σ with mem := ((σ.mem.insert a.toNat (data.extractLsb' 0 8)).insert (a.toNat + 1) (data.extractLsb' 8 8)) } := by
  have htmod : Int.tmod (BitVec.toNatInt a) 2 = 0 := by
    simp only [BitVec.toNatInt]
    have : ((Int.ofNat a.toNat).tmod (Int.ofNat 2)) = Int.ofNat (a.toNat % 2) :=
      (Int.ofNat_tmod _ _).symm
    rw [show (2 : Int) = Int.ofNat 2 from rfl, this, halign]; rfl
  have hsplit := split_on_page_boundary_store_2 σ a halign
  have hep := effectivePrivilege_store σ vmstatus Privilege.Machine hmprv
  have htm := translationMode_machine σ
  have htr := translateAddr_machine_store σ a vmstatus hpriv hmstatus hmprv
  have hea := mem_write_ea_2 σ a vmstatus vpmpaddr hpriv hmstatus hmprv hpma hcfg haddr
    hlo hhiram halign
  have hmwv := mem_write_value_2 σ a data vmstatus vpmpaddr hpriv hmstatus hmprv hpma hcfg
    haddr hbase hlo hhiram hhiwin halign
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
    show (!((BitVec.toNatInt a).tmod ((2:Nat):Int) == 0)) = false from by
      rw [show ((2:Nat):Int) = (2:Int) from rfl, htmod]; rfl,
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
    EStateM.map, ite_self, show ((2:Nat):Int).toNat = 2 from by decide,
    show (!(SATPMode.Bare == SATPMode.Bare) && (0 : Int) >b 0) = false from by decide]
  rw [hea]
  simp only [EStateM.bind, EStateM.pure, ExceptT.bindCont, EStateM.map]
  rw [show (if (!(SATPMode.Bare == SATPMode.Bare) && (0 : Int) >b 0) = true
      then ((2:Nat):Int) else ((2:Nat):Int)) = ((2:Nat):Int) from ite_self _]
  simp only [Int.toNat_natCast]
  have hwval : (BitVec.setWidth (8 * 2)
      (Sail.BitVec.extractLsb data (8 * ((2:Nat):Int) - 1).toNat 0)) = data := by
    have hidx : (8 * ((2:Nat):Int) - 1).toNat = 15 := by decide
    apply BitVec.eq_of_toNat_eq
    simp only [hidx, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
      BitVec.toNat_setWidth, Nat.shiftRight_zero, BitVec.toNat_ofNat,
      Nat.reduceSub, Nat.reduceMul]
    have hlt : data.toNat < 2 ^ 16 := by have h := data.isLt; simpa using h
    omega
  rw [hwval, hmwv]
  simp only [LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, EStateM.pure, pure, Pure.pure,
    Bool.true_and, Bool.and_true]
  rfl

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
  have hep := effectivePrivilege_store σ vmstatus Privilege.Machine hmprv
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
          { σ with mem := σ.mem.insert a.toNat data } := by
  have halign : a.toNat % 1 = 0 := Nat.mod_one _
  have htr := translateAddr_machine_store σ a vmstatus hpriv hmstatus hmprv
  have hea := mem_write_ea_1 σ a vmstatus vpmpaddr hpriv hmstatus hmprv hpma hcfg haddr
    hlo hhiram
  have hmwv := mem_write_value_1 σ a data vmstatus vpmpaddr hpriv hmstatus hmprv hpma hcfg
    haddr hbase hlo hhiram hhiwin
  have hwval : (BitVec.setWidth (8 * 1)
      (Sail.BitVec.extractLsb data (8 * ((1:Nat):Int) - 1).toNat 0)) = data := by
    have hidx : (8 * ((1:Nat):Int) - 1).toNat = 7 := by decide
    apply BitVec.eq_of_toNat_eq
    simp only [hidx, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
      BitVec.toNat_setWidth, Nat.shiftRight_zero, BitVec.toNat_ofNat,
      Nat.reduceSub, Nat.reduceMul]
    have hlt : data.toNat < 2 ^ 8 := by have h := data.isLt; simpa using h
    omega
  exact vmem_write_addr_w σ _ a 1 data vmstatus (by decide) (by decide) halign
    (by omega) hmstatus hpriv hmprv htr hea hmwv hwval

end Vsa.Sim
