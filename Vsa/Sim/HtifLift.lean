import Vsa.Sim.HtifMmio
import Vsa.Sim.MemStore

/-!
# HTIF mailbox store lift

Lifts the verified `htif_store` result through `checked_mem_write` and
`mem_write_value`.  The HTIF state transition is not unfolded.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

namespace Vsa.Sim

/-- The aligned M-mode checked-write path routes an eight-byte `tohost` write
to the supplied verified `htif_store` transition. -/
theorem checked_mem_write_tohost_8
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (data : BitVec 64)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hpma : σ.regs.get? Register.pma_regions =
      some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n =
      some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base =
      some (some (BitVec.ofNat 64 tohostAddr) :
        RegisterType Register.htif_tohost_base))
    (hstore :
      (htif_store (physaddr.Physaddr (BitVec.ofNat 64 tohostAddr)) 8 data).run σ =
        .ok (.Ok true) σ') :
    (checked_mem_write
        (physaddr.Physaddr (BitVec.ofNat 64 tohostAddr)) 8 data
        (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine () false false false).run σ =
      .ok (.Ok true) σ' := by
  have htmod :
      Int.tmod (BitVec.toNatInt (BitVec.ofNat 64 tohostAddr)) 8 = 0 := by
    simp only [BitVec.toNatInt, tohostAddr]
    decide
  have hpmaC := pmaCheck_ram_write σ (BitVec.ofNat 64 tohostAddr) 8
    (BitVec.ofNat 64 8) hpma (by decide) (by decide) (by decide)
    (by simp only [tohostAddr]; decide)
    (by simp only [tohostAddr]; decide) htmod
  have hpmp := pmp_allows σ
    (physaddr.Physaddr (BitVec.ofNat 64 tohostAddr)) 8
    (MemoryAccessType.Store mem_payload.Data) vpmpaddr hcfg haddr
  have hsplit :
      (split_misaligned
          (physaddr.Physaddr (BitVec.ofNat 64 tohostAddr)) 8 0
          Splittability.CannotSplit).run σ = .ok (1, 8) σ :=
    split_misaligned_aligned_w σ (BitVec.ofNat 64 tohostAddr) 8 0
      Splittability.CannotSplit htmod
  have hmmio := within_mmio_writable_tohost_8 σ hbase
  have hwrite :
      (mmio_write
          (physaddr.Physaddr (BitVec.ofNat 64 tohostAddr)) 8 data).run σ =
        .ok (.Ok true) σ' :=
    (mmio_write_tohost_8 σ data hbase).trans hstore
  have hwval :
      BitVec.setWidth (8 * Int.toNat 8)
        (Sail.BitVec.extractLsb data
          (8 * (((0 : Nat) : Int) + 1) * 8 - 1).toNat
          (8 * ((0 : Nat) : Int) * 8).toNat) = data := by
    have hhi : (8 * (((0 : Nat) : Int) + 1) * 8 - 1).toNat = 63 := by decide
    have hlo : (8 * ((0 : Nat) : Int) * 8).toNat = 0 := by decide
    have hw : 8 * Int.toNat 8 = 64 := by decide
    have hlt : data.toNat < 2 ^ 64 := by
      simpa using data.isLt
    apply BitVec.eq_of_toNat_eq
    simp only [hhi, hlo, hw, Sail.BitVec.extractLsb, BitVec.extractLsb,
      BitVec.extractLsb', BitVec.toNat_setWidth, Nat.shiftRight_zero,
      BitVec.toNat_ofNat, Nat.reduceSub, Nat.reduceAdd]
    rw [Nat.mod_eq_of_lt hlt]
    exact Nat.mod_eq_of_lt hlt
  simp only [EStateM.run] at hpmaC hpmp hsplit hmmio hwrite
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
    show (↑(0 : Nat) * (8 : Int)) = (0 : Int) from by decide,
    addInt_zero_pa', hpmp, hmmio]
  rw [hwval]
  have hwrite' :
      mmio_write (physaddr.Physaddr (BitVec.ofNat 64 tohostAddr))
          (Int.toNat (8 : Int)) data σ = .ok (.Ok true) σ' := hwrite
  rw [hwrite']
  simp only [EStateM.pure, EStateM.bind, ExceptT.bindCont, Bool.true_and,
    beq_self_eq_true, if_true]

/-- `mem_write_value` preserves the same verified HTIF transition. -/
theorem mem_write_value_tohost_8
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (data : BitVec 64)
    (vmstatus : RegisterType Register.mstatus)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hpma : σ.regs.get? Register.pma_regions =
      some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n =
      some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base =
      some (some (BitVec.ofNat 64 tohostAddr) :
        RegisterType Register.htif_tohost_base))
    (hstore :
      (htif_store (physaddr.Physaddr (BitVec.ofNat 64 tohostAddr)) 8 data).run σ =
        .ok (.Ok true) σ') :
    (mem_write_value
        (physaddr.Physaddr (BitVec.ofNat 64 tohostAddr)) 8 data
        (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA false false false).run σ =
      .ok (.Ok true) σ' := by
  have hcmw := checked_mem_write_tohost_8 σ σ' data vpmpaddr hpma hcfg haddr
    hbase hstore
  have hep := effectivePrivilege_store σ vmstatus Privilege.Machine hmprv
  simp only [EStateM.run] at hcmw hep
  unfold mem_write_value mem_write_value_meta mem_write_value_priv_meta
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hmstatus, hpriv]
  rw [hep]
  simp only [EStateM.bind, default_meta]
  rw [hcmw]

/-- Console output survives the whole `mem_write_value` path. -/
theorem mem_write_value_tohost_putchar
    (σ : SequentialState RegisterType trivialChoiceSource)
    (c : BitVec 8) (data : BitVec 64)
    (vmstatus : RegisterType Register.mstatus)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
    (th : BitVec 64)
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hpma : σ.regs.get? Register.pma_regions =
      some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n =
      some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base =
      some (some (BitVec.ofNat 64 tohostAddr) :
        RegisterType Register.htif_tohost_base))
    (hpw : σ.regs.get? Register.htif_payload_writes = some (0#4))
    (hth : σ.regs.get? Register.htif_tohost = some th)
    (hdata : data =
      (0x0101000000000000#64) ||| BitVec.zeroExtend 64 c) :
    (mem_write_value
        (physaddr.Physaddr (BitVec.ofNat 64 tohostAddr)) 8 data
        (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA false false false).run σ =
      .ok (.Ok true)
        { σ with
          regs := ((((((σ.regs.insert Register.htif_cmd_write 1#1).insert
                      Register.htif_payload_writes
                        (0#4 + BitVec.ofInt 4 1)).insert
                    Register.htif_tohost data).insert
                  Register.htif_cmd_write 0#1).insert
                Register.htif_payload_writes 0#4).insert
              Register.htif_tohost (zeros (n := 64))),
          sailOutput := σ.sailOutput.push (toString (Char.ofNat c.toNat)) } := by
  apply mem_write_value_tohost_8 σ _ data vmstatus vpmpaddr hpriv hmstatus hmprv
    hpma hcfg haddr hbase
  exact htif_store_putchar σ c data hbase th hpw hth hdata

/-- Exit state survives the whole `mem_write_value` path. -/
theorem mem_write_value_tohost_exit
    (σ : SequentialState RegisterType trivialChoiceSource)
    (e data : BitVec 64)
    (vmstatus : RegisterType Register.mstatus)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
    (th : BitVec 64)
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hpma : σ.regs.get? Register.pma_regions =
      some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n =
      some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base =
      some (some (BitVec.ofNat 64 tohostAddr) :
        RegisterType Register.htif_tohost_base))
    (hpw : σ.regs.get? Register.htif_payload_writes = some (0#4))
    (hth : σ.regs.get? Register.htif_tohost = some th)
    (hsmall : e.toNat < 2 ^ 47)
    (hdata : data = (e <<< 1) ||| 1#64) :
    (mem_write_value
        (physaddr.Physaddr (BitVec.ofNat 64 tohostAddr)) 8 data
        (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA false false false).run σ =
      .ok (.Ok true)
        { σ with
          regs := (((((σ.regs.insert Register.htif_cmd_write 1#1).insert
                      Register.htif_payload_writes
                        (0#4 + BitVec.ofInt 4 1)).insert
                    Register.htif_tohost data).insert
                  Register.htif_done true).insert
                Register.htif_exit_code e) } := by
  apply mem_write_value_tohost_8 σ _ data vmstatus vpmpaddr hpriv hmstatus hmprv
    hpma hcfg haddr hbase
  exact htif_store_exit σ e data hbase th hpw hth hsmall hdata

end Vsa.Sim
