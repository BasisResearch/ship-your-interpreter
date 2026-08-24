import Vsa.Sim.Htif

/-! # HTIF mailbox MMIO dispatch -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

namespace Vsa.Sim

/-- The concrete eight-byte `tohost` window is writable MMIO. -/
theorem within_mmio_writable_tohost_8
    (σ : SequentialState RegisterType trivialChoiceSource)
    (hbase : σ.regs.get? Register.htif_tohost_base =
      some (some (BitVec.ofNat 64 tohostAddr) :
        RegisterType Register.htif_tohost_base)) :
    (within_mmio_writable
        (physaddr.Physaddr (BitVec.ofNat 64 tohostAddr)) 8).run σ =
      .ok true σ := by
  simp only [within_mmio_writable, within_clint, within_sig, within_htif_writable,
    get_config_rvfi, plat_have_clint, plat_have_sig,
    zopz0zI_u, zopz0zK_u, LeanRV64DExecutable.Functions.not]
  simp only [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    readReg, get, getThe, MonadStateOf.get, EStateM.get, BitVec.toNatInt,
    htif_tohost_size, hbase, tohostAddr]
  simp_all [simp_sail, EStateM.bind, EStateM.pure, EStateM.get, tohostAddr]

/-- An eight-byte write at `tohost` selects `htif_store` exactly. -/
theorem mmio_write_tohost_8
    (σ : SequentialState RegisterType trivialChoiceSource)
    (data : BitVec 64)
    (hbase : σ.regs.get? Register.htif_tohost_base =
      some (some (BitVec.ofNat 64 tohostAddr) :
        RegisterType Register.htif_tohost_base)) :
    (mmio_write
        (physaddr.Physaddr (BitVec.ofNat 64 tohostAddr)) 8 data).run σ =
      (htif_store
        (physaddr.Physaddr (BitVec.ofNat 64 tohostAddr)) 8 data).run σ := by
  have hclint :
      within_clint
          (physaddr.Physaddr (BitVec.ofNat 64 tohostAddr)) 8 σ =
        .ok false σ := by
    simp only [within_clint, plat_have_clint, LeanRV64DExecutable.Functions.not,
      zopz0zI_u, zopz0zK_u, EStateM.run, pure, EStateM.pure, BitVec.toNatInt,
      tohostAddr]
    rfl
  have hsig :
      within_sig
          (physaddr.Physaddr (BitVec.ofNat 64 tohostAddr)) 8 σ =
        .ok false σ := by
    simp only [within_sig, plat_have_sig, LeanRV64DExecutable.Functions.not,
      zopz0zI_u, zopz0zK_u, EStateM.run, pure, EStateM.pure, BitVec.toNatInt,
      tohostAddr]
    rfl
  have hhtif :
      within_htif_writable
          (physaddr.Physaddr (BitVec.ofNat 64 tohostAddr)) 8 σ =
        .ok true σ := by
    simp only [within_htif_writable, zopz0zI_u, zopz0zK_u,
      bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
      readReg, get, getThe, MonadStateOf.get, EStateM.get,
      BitVec.toNatInt, htif_tohost_size, hbase, tohostAddr]
    simp only [Sail.ConcurrencyInterfaceV1.PreSail.readReg, bind, EStateM.bind,
      get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure,
      hbase, tohostAddr]
    rfl
  change mmio_write
      (physaddr.Physaddr (BitVec.ofNat 64 tohostAddr)) 8 data σ =
    htif_store (physaddr.Physaddr (BitVec.ofNat 64 tohostAddr)) 8 data σ
  unfold mmio_write
  simp only [bind, EStateM.bind]
  rw [hclint]
  simp only [Bool.false_eq_true, if_false]
  simp only [bind, EStateM.bind]
  rw [hsig]
  simp only [Bool.false_eq_true, if_false]
  simp only [bind, EStateM.bind]
  rw [hhtif]
  rfl

end Vsa.Sim
