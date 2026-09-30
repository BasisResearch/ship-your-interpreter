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
  vmem_read_data_ram_w σ rs offset v1 1 _ vmstatus vpmpaddr hpriv hmstatus hmprv hmseccfg
    hpma hcfg haddr hbase hrs (by decide) (by decide) hlo hhiram hhtif (Nat.mod_one _) (by omega)
    (read_ram_one_total σ (v1 + offset))

end Vsa.Sim
