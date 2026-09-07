import Vsa.Sim.SplitReadLoop

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register Sail.ConcurrencyInterfaceV1.PreSail
namespace Vsa.Sim

/-- Concrete policy and split result selecting a nonempty sequence of chunks. -/
structure SplitReadPlan (σ : Vsa.Machine.MState) (a : BitVec 64)
    (w n d : Nat) (info : Phys_Mem_Access_Info) : Prop where
  count_pos : 0 < n
  pma : (pmaCheck (physaddr.Physaddr a) w (MemoryAccessType.Load mem_payload.Data)
    page_based_mem_type.PBMT_PMA false).run σ = .ok (.Ok info) σ
  split : (split_misaligned (physaddr.Physaddr a) w info.granule_size_exp info.splittable).run σ =
    .ok ((n : Int), (d : Int)) σ

/-- The actual checked read returns exactly the assembled chunk values. -/
theorem checked_mem_read_of_split (σ : Vsa.Machine.MState) (a : BitVec 64)
    (w n d : Nat) (info : Phys_Mem_Access_Info) (values : Nat → BitVec (8 * d))
    (hp : SplitReadPlan σ a w n d info)
    (hc : ∀ i, i < n → SplitReadChunk σ a d i (values i)) :
    (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
      page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
      w false false false false).run σ =
      .ok (.Ok (((splitReadAccum n d values n).setWidth (8 * n * d)).setWidth (8 * w), ())) σ := by
  have hpma := hp.pma
  have hsplit := hp.split
  have hloop := splitReadLoop_trace σ a w n d values hc
  simp only [EStateM.run] at hpma hsplit
  unfold checked_mem_read
  simp only [check_pma_with_pmp_priority, read_kind_of_flags, misaligned_order,
    sys_misaligned_order_decreasing, bits_of_physaddr,
    LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, pure]
  rw [hpma]
  simp only [EStateM.pure, ExceptT.bindCont, EStateM.map, EStateM.bind]
  rw [hsplit]
  simp only [EStateM.pure, EStateM.bind, ExceptT.bindCont, EStateM.map,
    Int.toNat_natCast, Bool.false_eq_true, if_false,
    Int.reduceToNat]
  have hstart : splitReadTrace n d values 0 =
      (Functions.zeros (n := (8 * (n : Int) * (d : Int)).toNat), false, 0) := by
    simp [splitReadTrace, splitReadAccum, Functions.zeros, show ¬ n ≤ 0 from by have := hp.count_pos; omega]
  rw [hstart] at hloop
  simp only [ExceptT.run] at hloop
  unfold splitReadBody at hloop
  dsimp only [LeanRV64DExecutable.SailME.throw, Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.bind, pure] at hloop
  simp only [Int.toNat_natCast, Functions.zeros] at hloop ⊢
  erw [hloop]
  simp [splitReadTrace, EStateM.pure, default_meta]

#print axioms checked_mem_read_of_split
end Vsa.Sim
