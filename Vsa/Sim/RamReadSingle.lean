import Vsa.Sim.RamReadPolicy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register Sail.ConcurrencyInterfaceV1.PreSail
namespace Vsa.Sim

/-- Successful access checks for one concrete scalar RAM read. -/
structure RamReadChecks (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (w : Nat) : Prop where
  pma : (pmaCheck (physaddr.Physaddr a) w (MemoryAccessType.Load mem_payload.Data)
    page_based_mem_type.PBMT_PMA false).run σ =
    .ok (.Ok { splittable := Splittability.CannotSplit, granule_size_exp := 0 }) σ
  pmp : (pmpCheck (physaddr.Physaddr a) w (MemoryAccessType.Load mem_payload.Data)
    Privilege.Machine).run σ = .ok none σ
  mmio : (within_mmio_readable (physaddr.Physaddr a) w).run σ = .ok false σ

/-- A single RAM access returns its leaf value without changing machine state. -/
theorem checked_mem_read_single_of_ram
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (w : Nat) (v : BitVec (8 * w))
    (hw : 0 < w) (checks : RamReadChecks σ a w)
    (hram : (Functions.read_ram read_kind.Read_plain (physaddr.Physaddr a) w false).run σ
      = .ok (v, ()) σ) :
    (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        w false false false false).run σ = .ok (.Ok (v, ())) σ := by
  have hpmaC := checks.pma
  have hpmp := checks.pmp
  have hmmio := checks.mmio
  have hsplit := split_misaligned_cannotSplit σ a w 0
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
    show (↑(0 : Nat) * (w : Int)) = (0 : Int) from by simp, addInt_zero_pa,
    hpmp, hmmio, Bool.false_eq_true, if_false]
  rw [hram]
  simp only [EStateM.pure, EStateM.bind, ExceptT.bindCont,
    beq_self_eq_true, if_true, default_meta]
  have e1 : (8 * (((0:Nat):Int) + 1) * w - 1 : Int).toNat = 8 * w - 1 := by omega
  have e2 : (8 * ((0:Nat):Int) * w : Int).toNat = 0 := by omega
  rw [e1, e2]
  congr 3
  simp [BitVec.updateSubrange, Sail.BitVec.updateSubrange', Functions.zeros,
    show 8 * w - 1 + 1 = 8 * w from by omega, Int.toNat_mul]


#print axioms checked_mem_read_single_of_ram
end Vsa.Sim
