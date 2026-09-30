import Vsa.Sim.ExecuteLoad

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

abbrev bytesT1 (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) : BitVec 8 := (m[a]?).getD 0

abbrev bytesT2 (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) : BitVec 16 :=
  ((m[a + 1]?).getD 0).append ((m[a]?).getD 0)

abbrev bytesT4 (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) : BitVec 32 :=
  ((((m[a + 3]?).getD 0).append ((m[a + 2]?).getD 0)).append
    ((m[a + 1]?).getD 0)).append ((m[a]?).getD 0)

abbrev bytesT8 (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) : BitVec 64 :=
  ((((((((m[a + 7]?).getD 0).append ((m[a + 6]?).getD 0)).append
    ((m[a + 5]?).getD 0)).append ((m[a + 4]?).getD 0)).append
    ((m[a + 3]?).getD 0)).append ((m[a + 2]?).getD 0)).append
    ((m[a + 1]?).getD 0)).append ((m[a]?).getD 0)

abbrev ldByteT (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64) : BitVec 8 :=
  bytesT1 σ.mem a.toNat

abbrev ldBytesT (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64) : BitVec 64 :=
  bytesT8 σ.mem a.toNat

theorem read_ram_one_total (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64) :
    (Functions.read_ram read_kind.Read_plain (physaddr.Physaddr a) 1 false).run σ
      = .ok (ldByteT σ a, ()) σ := by
  simp only [Functions.read_ram, PreSail.sail_mem_read, PreSail.readBytes,
    PreSail.readByte, default_meta]
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get, Bool.false_eq_true, ldByteT, bytesT1]

theorem read_ram_eight_total (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64) :
    (Functions.read_ram read_kind.Read_plain (physaddr.Physaddr a) 8 false).run σ
      = .ok (ldBytesT σ a, ()) σ := by
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
    e2, e3, e4, e5, e6, e7, ldBytesT, bytesT8]

theorem checked_mem_read_data_one_total
    (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64)
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
    (hhtif : a.toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat) :
    (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        1 false false false false).run σ
      = .ok (.Ok (ldByteT σ a, ())) σ :=
  checked_mem_read_data_one_of_ram σ a _ vpmpaddr hpma hcfg haddr hbase
    hlo hhiram hhtif (read_ram_one_total σ a)

theorem mem_read_data_one_total
    (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64)
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
    (hhtif : a.toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat) :
    (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) 1 false false false).run σ
      = .ok (.Ok (ldByteT σ a)) σ :=
  mem_read_data_one_of_cmr σ a _ vmstatus hpriv hmstatus hmprv
    (checked_mem_read_data_one_total σ a vpmpaddr hpma hcfg haddr hbase
      hlo hhiram hhtif)

theorem translate_and_read_value_data_one_total
    (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64)
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
    (hhtif : a.toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat) :
    (translate_and_read_value (virtaddr.Virtaddr a) 1
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (physaddr.Physaddr (zero_extend (m := 64) a), ldByteT σ a)) σ :=
  translate_and_read_value_data_one_of_mr σ a _ vmstatus hpriv hmstatus hmprv
    (mem_read_data_one_total σ a vmstatus vpmpaddr hpriv hmstatus hmprv hpma hcfg
      haddr hbase hlo hhiram hhtif)

theorem vmem_read_addr_data_one_total
    (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64)
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
    (hhtif : a.toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat) :
    (vmem_read_addr (virtaddr.Virtaddr a) 1
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (ldByteT σ a)) σ :=
  vmem_read_addr_data_w σ a 1 (physaddr.Physaddr (zero_extend (m := 64) a)) (ldByteT σ a)
    vmstatus hpriv hmstatus hmprv (by decide) (by decide) (by omega)
    (is_aligned_vaddr_of_mod a 1 (Nat.mod_one _))
    (translate_and_read_value_data_one_total σ a vmstatus vpmpaddr
      hpriv hmstatus hmprv hpma hcfg haddr hbase hlo hhiram hhtif)

theorem vmem_read_data_one_total
    (σ : SequentialState RegisterType trivialChoiceSource) (rs : regidx) (offset v1 : BitVec 64)
    (vmstatus : RegisterType Register.mstatus) (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hmseccfg : σ.regs.get? Register.mseccfg = some (0#64 : RegisterType Register.mseccfg))
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hrs : (rX_bits rs).run σ = .ok v1 σ)
    (hlo : 0x80000000 ≤ (v1 + offset).toNat)
    (hhiram : (v1 + offset).toNat + 1 ≤ 0x100000000)
    (hhtif : (v1 + offset).toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v1 + offset).toNat) :
    (vmem_read rs offset 1 (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (ldByteT σ (v1 + offset))) σ :=
  vmem_read_data_w σ rs offset v1 1 _ vmstatus hpriv hmstatus hmprv hmseccfg hrs
    (vmem_read_addr_data_one_total σ (v1 + offset) vmstatus vpmpaddr
      hpriv hmstatus hmprv hpma hcfg haddr hbase hlo hhiram hhtif)

theorem checked_mem_read_data_eight_total
    (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64)
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
    (halign : a.toNat % 8 = 0) :
    (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        8 false false false false).run σ
      = .ok (.Ok (ldBytesT σ a, ())) σ :=
  checked_mem_read_data_eight_of_ram σ a _ vpmpaddr hpma hcfg haddr hbase
    hlo hhiram hhtif halign (read_ram_eight_total σ a)

theorem mem_read_data_eight_total
    (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64)
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
    (halign : a.toNat % 8 = 0) :
    (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) 8 false false false).run σ
      = .ok (.Ok (ldBytesT σ a)) σ :=
  mem_read_data_eight_of_cmr σ a _ vmstatus hpriv hmstatus hmprv
    (checked_mem_read_data_eight_total σ a vpmpaddr hpma hcfg haddr hbase
      hlo hhiram hhtif halign)

theorem translate_and_read_value_data_eight_total
    (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64)
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
    (halign : a.toNat % 8 = 0) :
    (translate_and_read_value (virtaddr.Virtaddr a) 8
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (physaddr.Physaddr (zero_extend (m := 64) a), ldBytesT σ a)) σ :=
  translate_and_read_value_data_eight_of_mr σ a _ vmstatus hpriv hmstatus hmprv
    (mem_read_data_eight_total σ a vmstatus vpmpaddr hpriv hmstatus hmprv hpma hcfg
      haddr hbase hlo hhiram hhtif halign)

theorem vmem_read_addr_data_eight_total
    (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64)
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
    (halign : a.toNat % 8 = 0) :
    (vmem_read_addr (virtaddr.Virtaddr a) 8
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (ldBytesT σ a)) σ :=
  vmem_read_addr_data_w σ a 8 (physaddr.Physaddr (zero_extend (m := 64) a)) (ldBytesT σ a)
    vmstatus hpriv hmstatus hmprv (by decide) (by decide) (by omega)
    (is_aligned_vaddr_of_mod a 8 halign)
    (translate_and_read_value_data_eight_total σ a vmstatus vpmpaddr
      hpriv hmstatus hmprv hpma hcfg haddr hbase hlo hhiram hhtif halign)

theorem vmem_read_data_eight_total
    (σ : SequentialState RegisterType trivialChoiceSource) (rs : regidx) (offset v1 : BitVec 64)
    (vmstatus : RegisterType Register.mstatus) (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hmseccfg : σ.regs.get? Register.mseccfg = some (0#64 : RegisterType Register.mseccfg))
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hrs : (rX_bits rs).run σ = .ok v1 σ)
    (hlo : 0x80000000 ≤ (v1 + offset).toNat)
    (hhiram : (v1 + offset).toNat + 8 ≤ 0x100000000)
    (hhtif : (v1 + offset).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v1 + offset).toNat)
    (halign : (v1 + offset).toNat % 8 = 0) :
    (vmem_read rs offset 8 (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (ldBytesT σ (v1 + offset))) σ :=
  vmem_read_data_w σ rs offset v1 8 _ vmstatus hpriv hmstatus hmprv hmseccfg hrs
    (vmem_read_addr_data_eight_total σ (v1 + offset) vmstatus vpmpaddr
      hpriv hmstatus hmprv hpma hcfg haddr hbase hlo hhiram hhtif halign)

end Vsa.Sim
