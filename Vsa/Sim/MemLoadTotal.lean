import Vsa.Sim.ExecuteLoad

/-!
# TOTAL (`getD 0`) `Load Data` chains at widths 1/2/4/8

The Sail model reads memory **totally**: `readByte a = (m.get? a).getD 0`, so an
unmapped/unwritten address reads as `0` — a load never faults on absence.  The
presence-hypothesis load chain in `Vsa/Sim/MemLoad.lean` (`σ.mem[a+k]? = some
bk`) therefore states something STRICTLY STRONGER than the model guarantees, and
every downstream obligation that demanded presence over unwritten bytes (the
`frame_pop` class over the callee's own unwritten entry frame) was asking for a
fact no honest supplier can produce — machine-checked in
`experiments/fleet/obstructions/FramePopRamTotalityVerdict48j.lean`.

This file is the total half of the load layer.  Since wave 48k the four
`Load Data` layers in `MemLoad.lean` are factored over the value the layer below
returns (`checked_mem_read_data_*_of_ram`, `mem_read_data_*_of_cmr`,
`translate_and_read_value_data_*_of_mr`), so the ONLY genuinely new content here
is the four `read_ram_*_total` leaves — the byte values are given
UNCONDITIONALLY as `(σ.mem[a+k]?).getD 0` and the `readByte` leaves land on them
definitionally.  Everything above is the shared factored proof, instantiated.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail


set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The total byte reads

Stated first on the raw byte map (`bytesT*`), then lifted to a state.  `Mem`-level
is the form every downstream consumer wants: the machine-state versions are
DEFEQ to it (`(afterNextPC (afterPrelude σ) pc).mem = σ.mem` is `rfl`). -/

/-- The byte at `a`, read totally as `getD 0` (unmapped ⇒ `0`) — exactly what the
model's `readByte` returns. -/
abbrev bytesT1 (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) : BitVec 8 := (m[a]?).getD 0

/-- The two little-endian bytes at `a + 0..1`, read totally. -/
abbrev bytesT2 (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) : BitVec 16 :=
  ((m[a + 1]?).getD 0).append ((m[a]?).getD 0)

/-- The four little-endian bytes at `a + 0..3`, read totally. -/
abbrev bytesT4 (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) : BitVec 32 :=
  ((((m[a + 3]?).getD 0).append ((m[a + 2]?).getD 0)).append
    ((m[a + 1]?).getD 0)).append ((m[a]?).getD 0)

/-- The eight little-endian bytes at `a + 0..7`, read totally. -/
abbrev bytesT8 (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) : BitVec 64 :=
  ((((((((m[a + 7]?).getD 0).append ((m[a + 6]?).getD 0)).append
    ((m[a + 5]?).getD 0)).append ((m[a + 4]?).getD 0)).append
    ((m[a + 3]?).getD 0)).append ((m[a + 2]?).getD 0)).append
    ((m[a + 1]?).getD 0)).append ((m[a]?).getD 0)

/-- The byte at `a.toNat`, read totally as `getD 0` (unmapped ⇒ `0`). -/
abbrev ldByteT (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64) : BitVec 8 :=
  bytesT1 σ.mem a.toNat

/-- The two little-endian bytes at `a.toNat + 0..1`, read totally. -/
abbrev ldBytesT2 (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64) :
    BitVec 16 := bytesT2 σ.mem a.toNat

/-- The four little-endian bytes at `a.toNat + 0..3`, read totally. -/
abbrev ldBytesT4 (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64) :
    BitVec 32 := bytesT4 σ.mem a.toNat

/-- The eight little-endian bytes at `a.toNat + 0..7`, read totally as `getD 0`
(unmapped ⇒ `0`). This is the value an `ld` produces. -/
abbrev ldBytesT (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64) : BitVec 64 :=
  bytesT8 σ.mem a.toNat

/-! ## The `read_ram` leaves — the ONLY place byte-level information enters -/

/-- `read_ram Read_plain (Physaddr a) 1 false` reads the byte at `a.toNat`
`getD 0`, unchanged state. -/
theorem read_ram_one_total (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64) :
    (Functions.read_ram read_kind.Read_plain (physaddr.Physaddr a) 1 false).run σ
      = .ok (ldByteT σ a, ()) σ := by
  simp only [Functions.read_ram, PreSail.sail_mem_read, PreSail.readBytes,
    PreSail.readByte, default_meta]
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get, Bool.false_eq_true, ldByteT, bytesT1]

/-- `read_ram Read_plain (Physaddr a) 2 false` reads the two little-endian bytes
at `a.toNat + 0..1` `getD 0`, unchanged state. -/
theorem read_ram_two_total (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64) :
    (Functions.read_ram read_kind.Read_plain (physaddr.Physaddr a) 2 false).run σ
      = .ok (ldBytesT2 σ a, ()) σ := by
  simp only [Functions.read_ram, PreSail.sail_mem_read, PreSail.readBytes,
    PreSail.readByte, default_meta]
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get, Bool.false_eq_true, ldBytesT2, bytesT2]

/-- `read_ram Read_plain (Physaddr a) 4 false` reads the four little-endian bytes
at `a.toNat + 0..3` `getD 0`, unchanged state. -/
theorem read_ram_four_total (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64) :
    (Functions.read_ram read_kind.Read_plain (physaddr.Physaddr a) 4 false).run σ
      = .ok (ldBytesT4 σ a, ()) σ := by
  have e2 : a.toNat + 1 + 1 = a.toNat + 2 := by omega
  have e3 : a.toNat + 1 + 1 + 1 = a.toNat + 3 := by omega
  simp only [Functions.read_ram, PreSail.sail_mem_read, PreSail.readBytes,
    PreSail.readByte, default_meta]
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get, Bool.false_eq_true, e2, e3, ldBytesT4, bytesT4]

/-- `read_ram Read_plain (Physaddr a) 8 false` reads the eight little-endian
bytes `getD 0` at `a.toNat + 0..7`, unchanged state. -/
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

/-! ## The `Load Data` chain above `read_ram`, instantiated at the total leaf.

Each layer is the SHARED factored proof from `Vsa/Sim/MemLoad.lean`
(`checked_mem_read_data_*_of_ram` / `mem_read_data_*_of_cmr` /
`translate_and_read_value_data_*_of_mr`), fed the total `read_ram_*_total`
leaf.  No byte-presence hypothesis appears anywhere. -/

/-- `checked_mem_read (Load Data) … (Physaddr a) 1 …` reads the 1 byte(s)
totally (`getD 0`), unchanged. -/
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

/-- `mem_read (Load Data) … (Physaddr a) 1 …` returns the total read, unchanged. -/
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

/-- `translate_and_read_value (Virtaddr a) 1 (Load Data) …`, total. -/
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

/-- `vmem_read_addr (Virtaddr a) 1 (Load Data) …`, total. -/
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

/-- **`vmem_read rs offset 1 (Load Data) …`, TOTAL.**  Resolves `a := v1 +
offset` and reads the 1 byte(s) there `getD 0` (unmapped ⇒ `0`).  No
byte-presence hypothesis: this is exactly what the model does. -/
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

/-- `checked_mem_read (Load Data) … (Physaddr a) 2 …` reads the 2 byte(s)
totally (`getD 0`), unchanged. -/
theorem checked_mem_read_data_two_total
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
    (hhiram : a.toNat + 2 ≤ 0x100000000)
    (hhtif : a.toNat + 2 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat)
    (halign : a.toNat % 2 = 0) :
    (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        2 false false false false).run σ
      = .ok (.Ok (ldBytesT2 σ a, ())) σ :=
  checked_mem_read_data_two_of_ram σ a _ vpmpaddr hpma hcfg haddr hbase
    hlo hhiram hhtif halign (read_ram_two_total σ a)

/-- `mem_read (Load Data) … (Physaddr a) 2 …` returns the total read, unchanged. -/
theorem mem_read_data_two_total
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
    (hhiram : a.toNat + 2 ≤ 0x100000000)
    (hhtif : a.toNat + 2 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat)
    (halign : a.toNat % 2 = 0) :
    (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) 2 false false false).run σ
      = .ok (.Ok (ldBytesT2 σ a)) σ :=
  mem_read_data_two_of_cmr σ a _ vmstatus hpriv hmstatus hmprv
    (checked_mem_read_data_two_total σ a vpmpaddr hpma hcfg haddr hbase
      hlo hhiram hhtif halign)

/-- `translate_and_read_value (Virtaddr a) 2 (Load Data) …`, total. -/
theorem translate_and_read_value_data_two_total
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
    (hhiram : a.toNat + 2 ≤ 0x100000000)
    (hhtif : a.toNat + 2 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat)
    (halign : a.toNat % 2 = 0) :
    (translate_and_read_value (virtaddr.Virtaddr a) 2
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (physaddr.Physaddr (zero_extend (m := 64) a), ldBytesT2 σ a)) σ :=
  translate_and_read_value_data_two_of_mr σ a _ vmstatus hpriv hmstatus hmprv
    (mem_read_data_two_total σ a vmstatus vpmpaddr hpriv hmstatus hmprv hpma hcfg
      haddr hbase hlo hhiram hhtif halign)

/-- `vmem_read_addr (Virtaddr a) 2 (Load Data) …`, total. -/
theorem vmem_read_addr_data_two_total
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
    (hhiram : a.toNat + 2 ≤ 0x100000000)
    (hhtif : a.toNat + 2 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat)
    (halign : a.toNat % 2 = 0) :
    (vmem_read_addr (virtaddr.Virtaddr a) 2
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (ldBytesT2 σ a)) σ :=
  vmem_read_addr_data_w σ a 2 (physaddr.Physaddr (zero_extend (m := 64) a)) (ldBytesT2 σ a)
    vmstatus hpriv hmstatus hmprv (by decide) (by decide) (by omega)
    (is_aligned_vaddr_of_mod a 2 halign)
    (translate_and_read_value_data_two_total σ a vmstatus vpmpaddr
      hpriv hmstatus hmprv hpma hcfg haddr hbase hlo hhiram hhtif halign)

/-- **`vmem_read rs offset 2 (Load Data) …`, TOTAL.**  Resolves `a := v1 +
offset` and reads the 2 byte(s) there `getD 0` (unmapped ⇒ `0`).  No
byte-presence hypothesis: this is exactly what the model does. -/
theorem vmem_read_data_two_total
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
    (hhiram : (v1 + offset).toNat + 2 ≤ 0x100000000)
    (hhtif : (v1 + offset).toNat + 2 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v1 + offset).toNat)
    (halign : (v1 + offset).toNat % 2 = 0) :
    (vmem_read rs offset 2 (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (ldBytesT2 σ (v1 + offset))) σ :=
  vmem_read_data_w σ rs offset v1 2 _ vmstatus hpriv hmstatus hmprv hmseccfg hrs
    (vmem_read_addr_data_two_total σ (v1 + offset) vmstatus vpmpaddr
      hpriv hmstatus hmprv hpma hcfg haddr hbase hlo hhiram hhtif halign)

/-- `checked_mem_read (Load Data) … (Physaddr a) 4 …` reads the 4 byte(s)
totally (`getD 0`), unchanged. -/
theorem checked_mem_read_data_four_total
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
    (hhiram : a.toNat + 4 ≤ 0x100000000)
    (hhtif : a.toNat + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat)
    (halign : a.toNat % 4 = 0) :
    (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        4 false false false false).run σ
      = .ok (.Ok (ldBytesT4 σ a, ())) σ :=
  checked_mem_read_data_four_of_ram σ a _ vpmpaddr hpma hcfg haddr hbase
    hlo hhiram hhtif halign (read_ram_four_total σ a)

/-- `mem_read (Load Data) … (Physaddr a) 4 …` returns the total read, unchanged. -/
theorem mem_read_data_four_total
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
    (hhiram : a.toNat + 4 ≤ 0x100000000)
    (hhtif : a.toNat + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat)
    (halign : a.toNat % 4 = 0) :
    (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) 4 false false false).run σ
      = .ok (.Ok (ldBytesT4 σ a)) σ :=
  mem_read_data_four_of_cmr σ a _ vmstatus hpriv hmstatus hmprv
    (checked_mem_read_data_four_total σ a vpmpaddr hpma hcfg haddr hbase
      hlo hhiram hhtif halign)

/-- `translate_and_read_value (Virtaddr a) 4 (Load Data) …`, total. -/
theorem translate_and_read_value_data_four_total
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
    (hhiram : a.toNat + 4 ≤ 0x100000000)
    (hhtif : a.toNat + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat)
    (halign : a.toNat % 4 = 0) :
    (translate_and_read_value (virtaddr.Virtaddr a) 4
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (physaddr.Physaddr (zero_extend (m := 64) a), ldBytesT4 σ a)) σ :=
  translate_and_read_value_data_four_of_mr σ a _ vmstatus hpriv hmstatus hmprv
    (mem_read_data_four_total σ a vmstatus vpmpaddr hpriv hmstatus hmprv hpma hcfg
      haddr hbase hlo hhiram hhtif halign)

/-- `vmem_read_addr (Virtaddr a) 4 (Load Data) …`, total. -/
theorem vmem_read_addr_data_four_total
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
    (hhiram : a.toNat + 4 ≤ 0x100000000)
    (hhtif : a.toNat + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat)
    (halign : a.toNat % 4 = 0) :
    (vmem_read_addr (virtaddr.Virtaddr a) 4
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (ldBytesT4 σ a)) σ :=
  vmem_read_addr_data_w σ a 4 (physaddr.Physaddr (zero_extend (m := 64) a)) (ldBytesT4 σ a)
    vmstatus hpriv hmstatus hmprv (by decide) (by decide) (by omega)
    (is_aligned_vaddr_of_mod a 4 halign)
    (translate_and_read_value_data_four_total σ a vmstatus vpmpaddr
      hpriv hmstatus hmprv hpma hcfg haddr hbase hlo hhiram hhtif halign)

/-- **`vmem_read rs offset 4 (Load Data) …`, TOTAL.**  Resolves `a := v1 +
offset` and reads the 4 byte(s) there `getD 0` (unmapped ⇒ `0`).  No
byte-presence hypothesis: this is exactly what the model does. -/
theorem vmem_read_data_four_total
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
    (hhiram : (v1 + offset).toNat + 4 ≤ 0x100000000)
    (hhtif : (v1 + offset).toNat + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v1 + offset).toNat)
    (halign : (v1 + offset).toNat % 4 = 0) :
    (vmem_read rs offset 4 (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (ldBytesT4 σ (v1 + offset))) σ :=
  vmem_read_data_w σ rs offset v1 4 _ vmstatus hpriv hmstatus hmprv hmseccfg hrs
    (vmem_read_addr_data_four_total σ (v1 + offset) vmstatus vpmpaddr
      hpriv hmstatus hmprv hpma hcfg haddr hbase hlo hhiram hhtif halign)

/-- `checked_mem_read (Load Data) … (Physaddr a) 8 …` reads the 8 byte(s)
totally (`getD 0`), unchanged. -/
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

/-- `mem_read (Load Data) … (Physaddr a) 8 …` returns the total read, unchanged. -/
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

/-- `translate_and_read_value (Virtaddr a) 8 (Load Data) …`, total. -/
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

/-- `vmem_read_addr (Virtaddr a) 8 (Load Data) …`, total. -/
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

/-- **`vmem_read rs offset 8 (Load Data) …`, TOTAL.**  Resolves `a := v1 +
offset` and reads the 8 byte(s) there `getD 0` (unmapped ⇒ `0`).  No
byte-presence hypothesis: this is exactly what the model does. -/
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
