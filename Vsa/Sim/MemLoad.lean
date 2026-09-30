import Vsa.Sim.Fetch
import Vsa.Sim.MemWidth

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem read_ram_eight
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (h0 : σ.mem[a.toNat]? = some b0) (h1 : σ.mem[a.toNat + 1]? = some b1)
    (h2 : σ.mem[a.toNat + 2]? = some b2) (h3 : σ.mem[a.toNat + 3]? = some b3)
    (h4 : σ.mem[a.toNat + 4]? = some b4) (h5 : σ.mem[a.toNat + 5]? = some b5)
    (h6 : σ.mem[a.toNat + 6]? = some b6) (h7 : σ.mem[a.toNat + 7]? = some b7) :
    (Functions.read_ram read_kind.Read_plain (physaddr.Physaddr a) 8 false).run σ
      = .ok (((((((b7.append b6).append b5).append b4).append b3).append
          b2).append b1).append b0, ()) σ := by
  have e2 : a.toNat + 1 + 1 = a.toNat + 2 := by omega
  have e3 : a.toNat + 1 + 1 + 1 = a.toNat + 3 := by omega
  have e4 : a.toNat + 1 + 1 + 1 + 1 = a.toNat + 4 := by omega
  have e5 : a.toNat + 1 + 1 + 1 + 1 + 1 = a.toNat + 5 := by omega
  have e6 : a.toNat + 1 + 1 + 1 + 1 + 1 + 1 = a.toNat + 6 := by omega
  have e7 : a.toNat + 1 + 1 + 1 + 1 + 1 + 1 + 1 = a.toNat + 7 := by omega
  simp only [Functions.read_ram, PreSail.sail_mem_read, PreSail.readBytes,
    PreSail.readByte, default_meta]
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get, Bool.false_eq_true,
    e2, e3, e4, e5, e6, e7, h0, h1, h2, h3, h4, h5, h6, h7]

theorem read_ram_one
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (b0 : BitVec 8)
    (h0 : σ.mem[a.toNat]? = some b0) :
    (Functions.read_ram read_kind.Read_plain (physaddr.Physaddr a) 1 false).run σ
      = .ok (b0, ()) σ := by
  simp only [Functions.read_ram, PreSail.sail_mem_read, PreSail.readBytes,
    PreSail.readByte, default_meta]
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get, Bool.false_eq_true, h0]

theorem within_mmio_readable_ram_false_w
    (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64) (w : Nat)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hwpos : 0 < w) (hwle : w ≤ 8)
    (hlo : 0x80000000 ≤ a.toNat) (hhiram : a.toNat + w ≤ 0x100000000)
    (hhtif : a.toNat + w ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat) :
    (within_mmio_readable (physaddr.Physaddr a) w).run σ = .ok false σ := by
  simp only [within_mmio_readable, within_clint, within_sig, within_htif_readable,
    within_htif_writable, get_config_rvfi, plat_have_clint, plat_have_sig,
    zopz0zI_u, zopz0zK_u, LeanRV64DExecutable.Functions.not]
  simp only [tohostAddr] at hhtif
  have hcb : BitVec.toNat plat_clint_base = 33554432 := by decide
  have hcs : BitVec.toNat plat_clint_size = 786432 := by decide
  have hsb : BitVec.toNat plat_sig_base = 201326592 := by decide
  have hss : BitVec.toNat plat_sig_size = 32 := by decide
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    Sail.ConcurrencyInterfaceV1.PreSail.readReg, get, getThe, MonadStateOf.get,
    EStateM.get, BitVec.toNatInt, htif_tohost_size]
  simp only [tohostAddr] at *
  have hadd : (a + BitVec.ofNat 64 w).toNat = a.toNat + w := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  refine ⟨fun _ => by omega, fun _ => by omega, fun _ => ?_⟩
  rename_i hx
  have hxlt : a.toNat < 2147593480 := by
    have hxv : (2147593472#64 + 8#64).toNat = 2147593480 := by decide
    omega
  have hle : (a + BitVec.ofNat 64 w).toNat ≤ 2147593472 := by rw [hadd]; omega
  have hrhs : ((2147593472 : Nat) : Int) % 18446744073709551616
      = ((2147593472 : Nat) : Int) := by decide
  rw [hrhs]
  omega

theorem within_mmio_readable_ram_false_eight
    (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hlo : 0x80000000 ≤ a.toNat) (hhiram : a.toNat + 8 ≤ 0x100000000)
    (hhtif : a.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat) :
    (within_mmio_readable (physaddr.Physaddr a) 8).run σ = .ok false σ :=
  within_mmio_readable_ram_false_w σ a 8 hbase (by decide) (by decide) hlo hhiram hhtif

theorem within_mmio_readable_ram_false_one
    (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hlo : 0x80000000 ≤ a.toNat) (hhiram : a.toNat + 1 ≤ 0x100000000)
    (hhtif : a.toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat) :
    (within_mmio_readable (physaddr.Physaddr a) 1).run σ = .ok false σ :=
  within_mmio_readable_ram_false_w σ a 1 hbase (by decide) (by decide) hlo hhiram hhtif


theorem checked_mem_read_data_w_of_ram
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (w : Nat) (v : BitVec (8 * w))
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
    (hhtif : a.toNat + w ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat)
    (halign : a.toNat % w = 0)
    (hram : (Functions.read_ram read_kind.Read_plain (physaddr.Physaddr a) w false).run σ
      = .ok (v, ()) σ) :
    (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        w false false false false).run σ
      = .ok (.Ok (v, ())) σ := by
  have htmod := tmod_toNatInt_of_mod a w halign
  have hpmaC := pmaCheck_ram σ a w _ (Or.inl rfl) hpma hlo hhiram htmod
  have hpmp := pmp_allows σ (physaddr.Physaddr a) w
    (MemoryAccessType.Load mem_payload.Data) vpmpaddr hcfg haddr
  have hmmio := within_mmio_readable_ram_false_w σ a w hbase hwpos hwle hlo hhiram hhtif
  have hsplit := split_misaligned_aligned_w σ a w 0 Splittability.CannotSplit htmod
  simp only [EStateM.run] at hpmaC hpmp hmmio hsplit hram
  unfold checked_mem_read
  simp only [check_pma_with_pmp_priority, read_kind_of_flags, misaligned_order,
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
    show (↑(0 : Nat) * ((w : Nat) : Int)) = (0 : Int) from by simp, addInt_zero_pa,
    hpmp, hmmio, Bool.false_eq_true, if_false]
  rw [hram]
  simp only [EStateM.pure, EStateM.bind, ExceptT.bindCont,
    beq_self_eq_true, if_true, default_meta]
  have e1 : (8 * (((0:Nat):Int) + 1) * (w : Int) - 1 : Int).toNat = 8 * w - 1 := by omega
  have e2 : (8 * ((0:Nat):Int) * (w : Int) : Int).toNat = 0 := by omega
  rw [e1, e2]
  congr 3
  simp only [BitVec.updateSubrange, Sail.BitVec.updateSubrange', Functions.zeros]
  apply BitVec.eq_of_toNat_eq
  have hlt := v.isLt
  have h1 : 8 * w - 1 + 1 = 8 * w := by omega
  have h2 : (8 * (w : Int)).toNat = 8 * w := by omega
  simp [BitVec.shiftLeft_zero, h1, h2, Nat.mod_eq_of_lt hlt]

theorem checked_mem_read_data_eight_of_ram
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec 64)
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
    (hhtif : a.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat)
    (halign : a.toNat % 8 = 0)
    (hram : (Functions.read_ram read_kind.Read_plain (physaddr.Physaddr a) 8 false).run σ
      = .ok (v, ()) σ) :
    (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        8 false false false false).run σ
      = .ok (.Ok (v, ())) σ :=
  checked_mem_read_data_w_of_ram σ a 8 v vpmpaddr (by decide) (by decide) hpma hcfg haddr hbase
    hlo hhiram hhtif halign hram

theorem checked_mem_read_data_eight
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
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
    (hhtif : a.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat)
    (halign : a.toNat % 8 = 0)
    (h0 : σ.mem[a.toNat]? = some b0)
    (h1 : σ.mem[a.toNat + 1]? = some b1)
    (h2 : σ.mem[a.toNat + 2]? = some b2)
    (h3 : σ.mem[a.toNat + 3]? = some b3)
    (h4 : σ.mem[a.toNat + 4]? = some b4)
    (h5 : σ.mem[a.toNat + 5]? = some b5)
    (h6 : σ.mem[a.toNat + 6]? = some b6)
    (h7 : σ.mem[a.toNat + 7]? = some b7) :
    (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        8 false false false false).run σ
      = .ok (.Ok ((((((((b7.append b6).append b5).append b4).append b3).append
          b2).append b1).append b0), ())) σ :=
  checked_mem_read_data_eight_of_ram σ a _ vpmpaddr hpma hcfg haddr hbase
    hlo hhiram hhtif halign (read_ram_eight σ a b0 b1 b2 b3 b4 b5 b6 b7 h0 h1 h2 h3 h4 h5 h6 h7)

theorem checked_mem_read_data_one_of_ram
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec 8)
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
    (hhtif : a.toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat)
    (hram : (Functions.read_ram read_kind.Read_plain (physaddr.Physaddr a) 1 false).run σ
      = .ok (v, ()) σ) :
    (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        1 false false false false).run σ
      = .ok (.Ok (v, ())) σ :=
  checked_mem_read_data_w_of_ram σ a 1 v vpmpaddr (by decide) (by decide) hpma hcfg haddr hbase
    hlo hhiram hhtif (Nat.mod_one _) hram

theorem checked_mem_read_data_one
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (b0 : BitVec 8)
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
    (hhtif : a.toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat)
    (h0 : σ.mem[a.toNat]? = some b0) :
    (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        1 false false false false).run σ
      = .ok (.Ok ((b0), ())) σ :=
  checked_mem_read_data_one_of_ram σ a _ vpmpaddr hpma hcfg haddr hbase
    hlo hhiram hhtif (read_ram_one σ a b0 h0)

theorem mem_read_data_w_of_cmr
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (w : Nat) (v : BitVec (8 * w))
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hcmr : (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        w false false false false).run σ = .ok (.Ok (v, ())) σ) :
    (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) w false false false).run σ
      = .ok (.Ok v) σ := by
  have hep := effectivePrivilege_machine σ (MemoryAccessType.Load mem_payload.Data) vmstatus
    Privilege.Machine (by decide) hmprv
  simp only [EStateM.run] at hcmr hep
  unfold mem_read mem_read_priv mem_read_priv_meta
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hmstatus, hpriv]
  rw [hep]
  simp only [MemoryOpResult_drop_meta]
  rw [hcmr]

theorem mem_read_data_eight_of_cmr
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec 64)
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hcmr : (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        8 false false false false).run σ = .ok (.Ok (v, ())) σ) :
    (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) 8 false false false).run σ
      = .ok (.Ok v) σ :=
  mem_read_data_w_of_cmr σ a 8 v vmstatus hpriv hmstatus hmprv hcmr

theorem mem_read_data_eight
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
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
    (hhtif : a.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat)
    (halign : a.toNat % 8 = 0)
    (h0 : σ.mem[a.toNat]? = some b0)
    (h1 : σ.mem[a.toNat + 1]? = some b1)
    (h2 : σ.mem[a.toNat + 2]? = some b2)
    (h3 : σ.mem[a.toNat + 3]? = some b3)
    (h4 : σ.mem[a.toNat + 4]? = some b4)
    (h5 : σ.mem[a.toNat + 5]? = some b5)
    (h6 : σ.mem[a.toNat + 6]? = some b6)
    (h7 : σ.mem[a.toNat + 7]? = some b7) :
    (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) 8 false false false).run σ
      = .ok (.Ok (((((((b7.append b6).append b5).append b4).append b3).append
          b2).append b1).append b0)) σ :=
  mem_read_data_eight_of_cmr σ a _ vmstatus hpriv hmstatus hmprv
    (checked_mem_read_data_eight σ a b0 b1 b2 b3 b4 b5 b6 b7 vpmpaddr hpma hcfg haddr hbase
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)

theorem mem_read_data_four_of_cmr
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec 32)
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hcmr : (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        4 false false false false).run σ = .ok (.Ok (v, ())) σ) :
    (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) 4 false false false).run σ
      = .ok (.Ok v) σ :=
  mem_read_data_w_of_cmr σ a 4 v vmstatus hpriv hmstatus hmprv hcmr

theorem mem_read_data_two_of_cmr
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec 16)
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hcmr : (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        2 false false false false).run σ = .ok (.Ok (v, ())) σ) :
    (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) 2 false false false).run σ
      = .ok (.Ok v) σ :=
  mem_read_data_w_of_cmr σ a 2 v vmstatus hpriv hmstatus hmprv hcmr

theorem mem_read_data_one_of_cmr
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec 8)
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hcmr : (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        1 false false false false).run σ = .ok (.Ok (v, ())) σ) :
    (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) 1 false false false).run σ
      = .ok (.Ok v) σ :=
  mem_read_data_w_of_cmr σ a 1 v vmstatus hpriv hmstatus hmprv hcmr

theorem mem_read_data_one
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (b0 : BitVec 8)
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
    (hhtif : a.toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat)
    (h0 : σ.mem[a.toNat]? = some b0) :
    (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) 1 false false false).run σ
      = .ok (.Ok (b0)) σ :=
  mem_read_data_one_of_cmr σ a _ vmstatus hpriv hmstatus hmprv
    (checked_mem_read_data_one σ a b0 vpmpaddr hpma hcfg haddr hbase
      hlo hhiram hhtif h0)

theorem translateAddr_machine_data
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64)
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1) :
    (translateAddr (virtaddr.Virtaddr a) (MemoryAccessType.Load mem_payload.Data)).run σ
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
  have hda : (MemoryAccessType.Load mem_payload.Data ==
      (MemoryAccessType.InstructionFetch () : MemoryAccessType mem_payload)) = false := by
    decide
  have hmprv0 : (_get_Mstatus_MPRV vmstatus == 1#1) = false := by
    rw [hmprv]; decide
  have hpm : (Privilege.Machine == Privilege.Machine) = true := by decide
  have hb : (SATPMode.Bare == SATPMode.Bare) = true := by decide
  simp only [hda, hmprv0, hpm, hb, EStateM.pure, EStateM.map, EStateM.bind,
    ExceptT.bindCont, Bool.not_false, Bool.and_false,
    if_false, if_true, Bool.false_eq_true]

theorem translate_and_read_value_data_w_of_mr
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (w : Nat) (v : BitVec (8 * w))
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hmr : (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) w false false false).run σ
      = .ok (.Ok v) σ) :
    (translate_and_read_value (virtaddr.Virtaddr a) w
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (physaddr.Physaddr (zero_extend (m := 64) a), v)) σ := by
  have htr := translateAddr_machine_data σ a vmstatus hpriv hmstatus hmprv
  simp only [EStateM.run] at htr hmr
  unfold translate_and_read_value
  simp only [bind, EStateM.bind, EStateM.run, pure]
  have hze : (zero_extend (m := 64) a : BitVec 64) = a := BitVec.setWidth_eq a
  rw [htr]
  simp only [EStateM.bind, hze]
  rw [hmr]
  simp only [EStateM.pure]

theorem translate_and_read_value_data_eight_of_mr
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec 64)
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hmr : (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) 8 false false false).run σ
      = .ok (.Ok v) σ) :
    (translate_and_read_value (virtaddr.Virtaddr a) 8
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (physaddr.Physaddr (zero_extend (m := 64) a), v)) σ :=
  translate_and_read_value_data_w_of_mr σ a 8 v vmstatus hpriv hmstatus hmprv hmr

theorem translate_and_read_value_data_eight
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
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
    (hhtif : a.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat)
    (halign : a.toNat % 8 = 0)
    (h0 : σ.mem[a.toNat]? = some b0)
    (h1 : σ.mem[a.toNat + 1]? = some b1)
    (h2 : σ.mem[a.toNat + 2]? = some b2)
    (h3 : σ.mem[a.toNat + 3]? = some b3)
    (h4 : σ.mem[a.toNat + 4]? = some b4)
    (h5 : σ.mem[a.toNat + 5]? = some b5)
    (h6 : σ.mem[a.toNat + 6]? = some b6)
    (h7 : σ.mem[a.toNat + 7]? = some b7) :
    (translate_and_read_value (virtaddr.Virtaddr a) 8
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (physaddr.Physaddr (zero_extend (m := 64) a),
          (((((((b7.append b6).append b5).append b4).append b3).append
          b2).append b1).append b0))) σ :=
  translate_and_read_value_data_eight_of_mr σ a _ vmstatus hpriv hmstatus hmprv
    (mem_read_data_eight σ a b0 b1 b2 b3 b4 b5 b6 b7 vmstatus vpmpaddr hpriv hmstatus hmprv hpma hcfg
      haddr hbase hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)

theorem translate_and_read_value_data_four_of_mr
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec 32)
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hmr : (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) 4 false false false).run σ
      = .ok (.Ok v) σ) :
    (translate_and_read_value (virtaddr.Virtaddr a) 4
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (physaddr.Physaddr (zero_extend (m := 64) a), v)) σ :=
  translate_and_read_value_data_w_of_mr σ a 4 v vmstatus hpriv hmstatus hmprv hmr

theorem translate_and_read_value_data_two_of_mr
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec 16)
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hmr : (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) 2 false false false).run σ
      = .ok (.Ok v) σ) :
    (translate_and_read_value (virtaddr.Virtaddr a) 2
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (physaddr.Physaddr (zero_extend (m := 64) a), v)) σ :=
  translate_and_read_value_data_w_of_mr σ a 2 v vmstatus hpriv hmstatus hmprv hmr

theorem translate_and_read_value_data_one_of_mr
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec 8)
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hmr : (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) 1 false false false).run σ
      = .ok (.Ok v) σ) :
    (translate_and_read_value (virtaddr.Virtaddr a) 1
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (physaddr.Physaddr (zero_extend (m := 64) a), v)) σ :=
  translate_and_read_value_data_w_of_mr σ a 1 v vmstatus hpriv hmstatus hmprv hmr

theorem translate_and_read_value_data_one
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (b0 : BitVec 8)
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
    (hhtif : a.toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat)
    (h0 : σ.mem[a.toNat]? = some b0) :
    (translate_and_read_value (virtaddr.Virtaddr a) 1
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (physaddr.Physaddr (zero_extend (m := 64) a),
          (b0))) σ :=
  translate_and_read_value_data_one_of_mr σ a _ vmstatus hpriv hmstatus hmprv
    (mem_read_data_one σ a b0 vmstatus vpmpaddr hpriv hmstatus hmprv hpma hcfg
      haddr hbase hlo hhiram hhtif h0)

end Vsa.Sim
