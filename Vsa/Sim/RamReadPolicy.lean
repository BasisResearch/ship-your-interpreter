import Vsa.Sim.Hooks
import Vsa.Sim.Pmp
import Vsa.Sim.MemRead
import Vsa.Sim.Fetch

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register Sail.ConcurrencyInterfaceV1.PreSail
open MemoryRegionType AtomicSupport Reservability misaligned_exception

namespace Vsa.Sim

/-- Natural widths have the same bit representation in Sail and Lean. -/
theorem to_bits_nat (w l : Nat) : (to_bits (l := l) w : BitVec l) = BitVec.ofNat l w := by
  apply BitVec.eq_of_toNat_eq
  simp [to_bits, get_slice_int, BitVec.extractLsb']
  exact Nat.mod_mod_of_dvd w (Nat.pow_dvd_pow 2 (by omega))

/-- The configured readable RAM region, including its 16-byte misaligned granule. -/
def ramPmaRegion : PMA_Region where
  base := 0x80000000#64
  size := 0x80000000#64
  attributes := {
    mem_type := MainMemory
    cacheable := true
    coherent := true
    executable := true
    readable := true
    writable := true
    read_idempotent := true
    write_idempotent := true
    misaligned_exceptions := { load_store := none, vector := none, amo := AccessFault }
    atomic_support := AMOCASQ
    reservability := RsrvEventual
    supports_cbo_zero := true
    supports_pte_read := true
    supports_pte_write := true
    misaligned_atomicity_granule_size_exp := 4
    vector_misaligned_atomicity_granule_size_exp := 4 }
  include_in_device_tree := true

/-- The PMA region lookup depends on the complete window, not natural alignment. -/
theorem matchingPmaRam (a : BitVec 64) (w : Nat)
    (hlo : 0x80000000 ≤ a.toNat) (hhi : a.toNat + w ≤ 0x100000000) :
    matching_pma_region_bits_range initPmaRegions
      (zero_extend (bits_of_physaddr (physaddr.Physaddr a))) (to_bits w) =
      some ramPmaRegion := by
  have hz : (zero_extend (bits_of_physaddr (physaddr.Physaddr a)) : BitVec 64) = a :=
    BitVec.setWidth_eq a
  rw [hz, to_bits_nat]
  simp only [ramPmaRegion, initPmaRegions, matching_pma_region_bits_range, range_subset,
    zopz0zIzJ_u, BitVec.toNatInt]
  rw [if_neg, if_neg, if_pos]
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, ?_, ?_⟩ <;> · apply Int.ofNat_le.mpr; bv_omega
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    rintro ⟨h1, _⟩; have := Int.ofNat_le.mp h1; bv_omega
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    rintro ⟨h1, _⟩; have := Int.ofNat_le.mp h1; bv_omega

/-- Scalar loads within one supported granule do not split. -/
def ramReadSingle (a : BitVec 64) (w : Nat) : Bool :=
  is_aligned_paddr (physaddr.Physaddr a) w || allowed_misaligned a w 4

/-- Exact access policy for scalar RAM reads of at most eight bytes. -/
def ramReadInfo (a : BitVec 64) (w : Nat) : Phys_Mem_Access_Info :=
  if ramReadSingle a w then ⟨Splittability.CannotSplit, 0⟩ else ⟨Splittability.CanSplit, 4⟩

/-- Misalignment selects the configured split policy; it is not an access fault. -/
theorem pmaCheck_ram_scalar (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (w : Nat)
    (hpma : σ.regs.get? Register.pma_regions = some (initPmaRegions : RegisterType Register.pma_regions))
    (hlo : 0x80000000 ≤ a.toNat) (hhi : a.toNat + w ≤ 0x100000000)
    (hw : w ≤ 8) :
    (pmaCheck (physaddr.Physaddr a) w (MemoryAccessType.Load mem_payload.Data)
      page_based_mem_type.PBMT_PMA false).run σ = .ok (.Ok (ramReadInfo a w)) σ := by
  have hmatch := matchingPmaRam a w hlo hhi
  unfold pmaCheck
  simp only [LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind,
    Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hpma]
  simp only [pure, EStateM.pure, matching_pma_region, hmatch, ramPmaRegion, override_PMA,
    Functions.not, mag_pma_check, is_mag_applicable_access, within_pma_mag, mag_of_pma,
    is_vector_access, pma_misaligned_exception,
    LeanRV64DExecutable.assert, PreSail.assert,
    ExceptT.pure, ExceptT.bindCont, ExceptT.mk,
    EStateM.map, EStateM.bind, bind, Bind.bind,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, if_true, if_false]
  have hwidth : (↑w ≤b Functions.xlen_bytes) = true := by
    change decide (w ≤ 8) = true
    simp only [decide_eq_true_eq]
    omega
  rw [hwidth]
  simp only [Bool.true_and]
  by_cases h : ramReadSingle a w = true <;>
    simp only [ramReadSingle] at h <;>
    simp [ramReadInfo, ramReadSingle, Functions.xlen, Sail.BitVec.extractLsb,
      BitVec.extractLsb, h, EStateM.pure, EStateM.bind]

/-- An access marked indivisible never splits, regardless of address alignment. -/
theorem split_misaligned_cannotSplit
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (w e : Nat) :
    (split_misaligned (physaddr.Physaddr a) w e Splittability.CannotSplit).run σ =
      .ok (1, (w : Int)) σ := by
  simp [split_misaligned,
    show (Splittability.CannotSplit == Splittability.CannotSplit) = true from rfl,
    simp_sail, EStateM.run, pure, EStateM.pure]

/-- The RAM policy selects one access or the executable split planner. -/
theorem split_misaligned_ram
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (w : Nat) :
    (split_misaligned (physaddr.Physaddr a) w (ramReadInfo a w).granule_size_exp
      (ramReadInfo a w).splittable).run σ =
      if ramReadSingle a w then .ok (1, (w : Int)) σ else (split_access a w).run σ := by
  by_cases h : ramReadSingle a w = true
  · simp only [ramReadInfo, h, if_true]
    exact split_misaligned_cannotSplit σ a w 0
  · simp only [ramReadInfo, h, Bool.false_eq_true, if_false]
    simp only [ramReadSingle, is_aligned_paddr, Bool.or_eq_true, beq_iff_eq] at h
    simp [split_misaligned, Functions.xlen, Sail.BitVec.extractLsb,
      BitVec.extractLsb, sys_misaligned_byte_by_byte,
      show (Splittability.CanSplit == Splittability.CannotSplit) = false from rfl]
    rw [if_neg]
    exact h


#print axioms to_bits_nat
#print axioms matchingPmaRam
#print axioms pmaCheck_ram_scalar
#print axioms split_misaligned_cannotSplit
#print axioms split_misaligned_ram
end Vsa.Sim
