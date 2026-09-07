import Vsa.Sim.RamReadSingle
import Vsa.Sim.MemLoadTotal
import Vsa.Sim.GoodState
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register Sail.ConcurrencyInterfaceV1.PreSail
namespace Vsa.Sim

/-- `within_mmio_readable a w = false` for a RAM window. -/
theorem within_mmio_readable_ram_false_width
    (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64) (w : Nat)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
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
    have hw : (BitVec.ofNat 64 w).toNat = w := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_add, hw, Nat.mod_eq_of_lt (by omega)]
  refine ⟨fun _ => by omega, fun _ => by omega, fun _ => ?_⟩
  rename_i hx
  have hxlt : a.toNat < 2147593480 := by
    have hxv : (2147593472#64 + 8#64).toNat = 2147593480 := by decide
    exact Nat.lt_of_lt_of_eq hx hxv
  have hle : (a + BitVec.ofNat 64 w).toNat ≤ 2147593472 := by rw [hadd]; omega
  have hrhs : ((2147593472 : Nat) : Int) % 18446744073709551616
      = ((2147593472 : Nat) : Int) := by decide
  rw [hrhs]
  intro hbad
  exact False.elim ((Nat.not_lt_of_ge hle) (by exact_mod_cast hbad))


/-- Concrete RAM checks for a scalar access accepted without splitting. -/
theorem RamReadChecks.of_scalar
    (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64) (w : Nat)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hpma : σ.regs.get? Register.pma_regions = some initPmaRegions)
    (hcfg : σ.regs.get? Register.pmpcfg_n = some (Vector.replicate 64 (0#8)))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base = some (some (BitVec.ofNat 64 tohostAddr)))
    (hlo : 0x80000000 ≤ a.toNat) (hhi : a.toNat + w ≤ 0x100000000)
    (hhtif : a.toNat + w ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat)
    (hw : w ≤ 8) (hsingle : ramReadSingle a w = true) : RamReadChecks σ a w where
  pma := by
    have h := pmaCheck_ram_scalar σ a w hpma hlo hhi hw
    simpa only [ramReadInfo, hsingle, if_true] using h
  pmp := pmp_allows σ (physaddr.Physaddr a) w (MemoryAccessType.Load mem_payload.Data)
    vpmpaddr hcfg haddr
  mmio := within_mmio_readable_ram_false_width σ a w hbase hlo hhi hhtif

/-- Standard machine-state invariants discharge the register checks. -/
theorem RamReadChecks.of_good {σ : Vsa.Machine.MState} (h : GoodState σ)
    (a : BitVec 64) (w : Nat)
    (hlo : 0x80000000 ≤ a.toNat) (hhi : a.toNat + w ≤ 0x100000000)
    (hhtif : a.toNat + w ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat)
    (hw : w ≤ 8) (hsingle : ramReadSingle a w = true) : RamReadChecks σ a w :=
  RamReadChecks.of_scalar σ a w initPmpaddr h.pma_regions h.pmpcfg_n
    h.pmpaddr_n h.htif_tohost_base hlo hhi hhtif hw hsingle

/-- Four-byte scalar read using total memory bytes and the actual access checks. -/
theorem RamReadChecks.readFour
    {σ : SequentialState RegisterType trivialChoiceSource} {a : BitVec 64}
    (h : RamReadChecks σ a 4) :
    (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
      page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
      4 false false false false).run σ = .ok (.Ok (ldBytesT4 σ a, ())) σ :=
  checked_mem_read_single_of_ram σ a 4 _ (by decide) h (read_ram_four_total σ a)

/-- Eight-byte scalar read using total memory bytes and the actual access checks. -/
theorem RamReadChecks.readEight
    {σ : SequentialState RegisterType trivialChoiceSource} {a : BitVec 64}
    (h : RamReadChecks σ a 8) :
    (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
      page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
      8 false false false false).run σ = .ok (.Ok (ldBytesT σ a, ())) σ :=
  checked_mem_read_single_of_ram σ a 8 _ (by decide) h (read_ram_eight_total σ a)

#print axioms RamReadChecks.readFour
#print axioms RamReadChecks.readEight

#print axioms RamReadChecks.of_scalar
#print axioms RamReadChecks.of_good

#print axioms within_mmio_readable_ram_false_width
end Vsa.Sim
