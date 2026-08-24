import Vsa.Sim.ExecuteLoad

/-!
# Total (`getD 0`) width-8 `Load Data` chain for the `strlen` word-wise loop

The word-wise `strlen` loop reads the aligned 8-byte word *containing* the
terminating NUL. Its trailing bytes may be UNMAPPED in the `ExtHashMap` (a
malloc'd buffer is only written up to `len+1`). `readByte` is `getD 0`, so an
unmapped read is `0` — but the byte-consuming leaves of the load chain in
`Vsa/Sim/MemLoad.lean` (`read_ram_eight` → `checked_mem_read_data_eight` →
`mem_read_data_eight` → `translate_and_read_value_data_eight`) take
`σ.mem[a+k]? = some bk` hypotheses, unusable for unmapped bytes.

This file clones exactly those four byte-consuming leaves at width 8 with the
byte values given UNCONDITIONALLY as `bk := (σ.mem[(a.toNat)+k]?).getD 0` and NO
byte hypotheses. The `getD` value facts hold *definitionally* through `readByte`
(`pure ((get).mem.get? a |>.getD 0)`), so the same proof scripts go through with
the `hk`-rewrites replaced by `Option.getD`-normal-form. Everything above
`translate_and_read_value` — `vmem_read_addr_data_w` and `vmem_read_data_w`
(`Vsa/Sim/ExecuteLoad.lean`) — is already width-generic over an abstract
`htrv`/`hvra`, so it is reused verbatim rather than duplicated.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail


set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- The eight little-endian bytes at `a.toNat + 0..7`, read totally as `getD 0`
(unmapped ⇒ `0`). This is the value the word-wise `strlen` load produces. -/
abbrev ldBytesT (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64) : BitVec 64 :=
  ((((((((σ.mem[a.toNat + 7]?).getD 0).append ((σ.mem[a.toNat + 6]?).getD 0)).append
    ((σ.mem[a.toNat + 5]?).getD 0)).append ((σ.mem[a.toNat + 4]?).getD 0)).append
    ((σ.mem[a.toNat + 3]?).getD 0)).append ((σ.mem[a.toNat + 2]?).getD 0)).append
    ((σ.mem[a.toNat + 1]?).getD 0)).append ((σ.mem[a.toNat]?).getD 0)

/-- `read_ram Read_plain (Physaddr a) 8 false` reads the eight little-endian
bytes `getD 0` at `a.toNat + 0..7`, unchanged state. Unconditional clone of
`read_ram_eight` (`Vsa/Sim/MemLoad.lean`): the byte values are `getD 0`, so the
`readByte` (`pure (get.mem.get? a |>.getD 0)`) leaves land on them by `rfl`. -/
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
    e2, e3, e4, e5, e6, e7]

/-- `checked_mem_read (Load Data) … (Physaddr a) 8 …` reads the eight bytes
`getD 0`, unchanged. Unconditional clone of `checked_mem_read_data_eight`. -/
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
      = .ok (.Ok (ldBytesT σ a, ())) σ := by
  have htmod : Int.tmod (BitVec.toNatInt a) 8 = 0 := by
    simp only [BitVec.toNatInt]
    have : ((Int.ofNat a.toNat).tmod (Int.ofNat 8)) = Int.ofNat (a.toNat % 8) :=
      (Int.ofNat_tmod _ _).symm
    rw [show (8 : Int) = Int.ofNat 8 from rfl, this, halign]; rfl
  have hpmaC := pmaCheck_ram_read σ a 8 (by decide) hpma hlo hhiram htmod
  have hpmp := pmp_allows σ (physaddr.Physaddr a) 8
    (MemoryAccessType.Load mem_payload.Data) vpmpaddr hcfg haddr
  have hmmio := within_mmio_readable_ram_false_eight σ a hbase hlo hhiram hhtif
  have hsplit : (split_misaligned (physaddr.Physaddr a) 8 0 Splittability.CannotSplit).run σ
      = .ok (1, (8 : Int)) σ := by
    have h := split_misaligned_aligned_w σ a 8 0 Splittability.CannotSplit htmod
    rw [h, show ((8 : Nat) : Int) = (8 : Int) from rfl]
  have hram := read_ram_eight_total σ a
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
    show Int.toNat 1 = 1 from rfl, show Int.toNat 8 = 8 from rfl,
    show Int.toNat 0 = 0 from rfl]
  rw [untilFuelM]
  simp only [untilFuelM.go]
  simp only [ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure,
    EStateM.map, EStateM.bind, EStateM.pure, bind, pure, Pure.pure,
    LeanRV64DExecutable.assert, PreSail.assert, if_true,
    show (↑(0 : Nat) * (8 : Int)) = (0 : Int) from by decide, addInt_zero_pa,
    hpmp, hmmio, Bool.false_eq_true, if_false]
  have hram' : Functions.read_ram read_kind.Read_plain (physaddr.Physaddr a) (Int.toNat 8) false σ
      = EStateM.Result.ok (ldBytesT σ a, ()) σ := hram
  rw [hram']
  simp only [EStateM.pure, EStateM.bind, ExceptT.bindCont,
    beq_self_eq_true, if_true, default_meta]
  have e1 : (8 * (((0:Nat):Int) + 1) * 8 - 1 : Int).toNat = 63 := by decide
  have e2 : (8 * ((0:Nat):Int) * 8 : Int).toNat = 0 := by decide
  rw [e1, e2]
  congr 3
  simp only [BitVec.updateSubrange, Sail.BitVec.updateSubrange', Functions.zeros]
  have key : (0#64 ||| (ldBytesT σ a) <<< 0) = ldBytesT σ a := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.shiftLeft_zero]
  exact key

/-- `mem_read (Load Data) … (Physaddr a) 8 …` returns `Ok (ldBytesT …)`,
unchanged. Unconditional clone of `mem_read_data_eight`. -/
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
      = .ok (.Ok (ldBytesT σ a)) σ := by
  have hcmr := checked_mem_read_data_eight_total σ a vpmpaddr hpma hcfg
    haddr hbase hlo hhiram hhtif halign
  have hep := effectivePrivilege_data σ vmstatus Privilege.Machine hmprv
  simp only [EStateM.run] at hcmr hep
  unfold mem_read mem_read_priv mem_read_priv_meta
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hmstatus, hpriv]
  rw [hep]
  simp only [MemoryOpResult_drop_meta]
  rw [hcmr]

/-- `translate_and_read_value (Virtaddr a) 8 (Load Data) …` returns
`Ok (Physaddr (zero_extend a), ldBytesT …)`, unchanged. Unconditional clone of
`translate_and_read_value_data_eight`. -/
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
      = .ok (.Ok (physaddr.Physaddr (zero_extend (m := 64) a), ldBytesT σ a)) σ := by
  have htr := translateAddr_machine_data σ a vmstatus hpriv hmstatus hmprv
  have hmr := mem_read_data_eight_total σ a vmstatus vpmpaddr hpriv
    hmstatus hmprv hpma hcfg haddr hbase hlo hhiram hhtif halign
  simp only [EStateM.run] at htr hmr
  unfold translate_and_read_value
  simp only [bind, EStateM.bind, EStateM.run, pure]
  have hze : (zero_extend (m := 64) a : BitVec 64) = a := BitVec.setWidth_eq a
  rw [htr]
  simp only [EStateM.bind, hze]
  rw [hmr]
  simp only [EStateM.pure]

/-- `vmem_read_addr (Virtaddr a) 8 (Load Data) …` returns `Ok (ldBytesT …)`,
unchanged. Reuses the width-generic `vmem_read_addr_data_w` engine with the total
`translate_and_read_value` leaf. -/
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

/-- **`vmem_read rs offset 8 (Load Data) …` (`ld`), total version.** Resolves
`a := v1 + offset`, reads the eight bytes there `getD 0` (unmapped ⇒ `0`). Thin
composition of the width-generic `vmem_read_data_w` + the total
`vmem_read_addr_data_eight_total`. This is the load the word-wise `strlen` loop
issues; the trailing bytes of the NUL-containing word may be unmapped. -/
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
    (hlo : 0x80000000 ≤ (v1 + offset).toNat) (hhiram : (v1 + offset).toNat + 8 ≤ 0x100000000)
    (hhtif : (v1 + offset).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v1 + offset).toNat)
    (halign : (v1 + offset).toNat % 8 = 0) :
    (vmem_read rs offset 8 (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (ldBytesT σ (v1 + offset))) σ :=
  vmem_read_data_w σ rs offset v1 8 _ vmstatus hpriv hmstatus hmprv hmseccfg hrs
    (vmem_read_addr_data_eight_total σ (v1 + offset) vmstatus vpmpaddr
      hpriv hmstatus hmprv hpma hcfg haddr hbase hlo hhiram hhtif halign)

end Vsa.Sim
