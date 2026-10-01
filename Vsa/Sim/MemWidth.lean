import Vsa.Sim.Hooks
import Vsa.Sim.Pmp

/-!
# The width layer shared by loads and stores

The access checks that `checked_mem_read` and `checked_mem_write` perform on an aligned RAM
access of width `w` do not depend on the direction: the effective privilege in machine mode, the
PMA region of RAM, the split plan of an aligned access. `MemLoad` and `MemStore` both import this
module.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail

namespace Vsa.Sim

/-- Machine mode with `MPRV = 0`: every data access runs at the current privilege. -/
theorem effectivePrivilege_machine
    (σ : SequentialState RegisterType trivialChoiceSource)
    (acc : MemoryAccessType mem_payload) (m : BitVec 64) (p : Privilege)
    (hacc : (acc == (MemoryAccessType.InstructionFetch () : MemoryAccessType mem_payload)) = false)
    (hmprv : _get_Mstatus_MPRV m = 0#1) :
    (effectivePrivilege acc m p).run σ = .ok p σ := by
  simp only [effectivePrivilege, bne, hacc, Bool.not_false, hmprv, Bool.true_and]
  have hz : (0#1 == 1#1) = false := by decide
  simp [simp_sail, EStateM.run, pure, EStateM.pure, hz]

theorem tmod_toNatInt_of_mod (a : BitVec 64) (w : Nat) (h : a.toNat % w = 0) :
    Int.tmod (BitVec.toNatInt a) w = 0 := by
  simp only [BitVec.toNatInt]
  have : ((Int.ofNat a.toNat).tmod (Int.ofNat w)) = Int.ofNat (a.toNat % w) :=
    (Int.ofNat_tmod _ _).symm
  rw [show (w : Int) = Int.ofNat w from rfl, this, h]; rfl

theorem to_bits_ofNat (w : Nat) :
    (to_bits (l := 64) w : BitVec 64) = BitVec.ofNat 64 w := by
  apply BitVec.eq_of_toNat_eq
  simp only [to_bits, get_slice_int, BitVec.extractLsb', Nat.zero_add,
    BitVec.toNat_ofInt, Nat.shiftRight_zero, BitVec.toNat_ofNat]
  omega

theorem split_misaligned_aligned_w
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (w : Nat) (e : Nat) (s : Splittability)
    (ha : Int.tmod (BitVec.toNatInt a) w = 0) :
    (split_misaligned (physaddr.Physaddr a) w e s).run σ
      = .ok (1, (w : Int)) σ := by
  simp only [split_misaligned]
  split
  · simp [simp_sail, EStateM.run, pure, EStateM.pure]
  · rename_i hneg
    exfalso
    apply hneg
    simp only [Bool.or_eq_true, beq_iff_eq]
    refine Or.inr (Or.inl ?_)
    exact_mod_cast ha

open MemoryRegionType AtomicSupport Reservability misaligned_exception in

/-- Any aligned data access of width `w` inside RAM passes the PMA check, load or store. -/
theorem pmaCheck_ram
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (w : Nat) (acc : MemoryAccessType mem_payload)
    (hacc : acc = MemoryAccessType.Load mem_payload.Data ∨
      acc = MemoryAccessType.Store mem_payload.Data)
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hlo : 0x80000000 ≤ a.toNat)
    (hhi : a.toNat + w ≤ 0x100000000)
    (halign : Int.tmod (BitVec.toNatInt a) w = 0) :
    (pmaCheck (physaddr.Physaddr a) w acc page_based_mem_type.PBMT_PMA false).run σ
      = .ok (.Ok { splittable := Splittability.CannotSplit, granule_size_exp := 0 }) σ := by
  have hmatch : matching_pma_region_bits_range initPmaRegions
      (zero_extend (bits_of_physaddr (physaddr.Physaddr a))) (to_bits w)
      = some ({ base := 0x80000000#64
                size := 0x80000000#64
                attributes := { mem_type := MainMemory
                                cacheable := true
                                coherent := true
                                executable := true
                                readable := true
                                writable := true
                                read_idempotent := true
                                write_idempotent := true
                                misaligned_exceptions := { load_store := none
                                                           vector := none
                                                           amo := AccessFault }
                                atomic_support := AMOCASQ
                                reservability := RsrvEventual
                                supports_cbo_zero := true
                                supports_pte_read := true
                                supports_pte_write := true
                                misaligned_atomicity_granule_size_exp := 4
                                vector_misaligned_atomicity_granule_size_exp := 4 }
                include_in_device_tree := true } : PMA_Region) := by
    have hz : (zero_extend (bits_of_physaddr (physaddr.Physaddr a)) : BitVec 64) = a :=
      BitVec.setWidth_eq a
    rw [hz, to_bits_ofNat w]
    simp only [initPmaRegions, matching_pma_region_bits_range, range_subset,
      zopz0zIzJ_u, BitVec.toNatInt]
    rw [if_neg, if_neg, if_pos]
    · simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨?_, ?_, ?_⟩ <;> · apply Int.ofNat_le.mpr; bv_omega
    · simp only [Bool.and_eq_true, decide_eq_true_eq]
      rintro ⟨h1, _⟩; have := Int.ofNat_le.mp h1; bv_omega
    · simp only [Bool.and_eq_true, decide_eq_true_eq]
      rintro ⟨h1, _⟩; have := Int.ofNat_le.mp h1; bv_omega
  unfold pmaCheck
  simp only [LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, LeanRV64DExecutable.readReg,
    Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hpma]
  rcases hacc with rfl | rfl <;>
  · simp only [pure, EStateM.pure, matching_pma_region, hmatch, override_PMA,
      Functions.not, mag_pma_check, is_mag_applicable_access, is_aligned_paddr,
      LeanRV64DExecutable.assert, PreSail.assert, BitVec.toNatInt,
      ExceptT.pure, ExceptT.bindCont, ExceptT.mk,
      EStateM.map, EStateM.bind, bind, Bind.bind,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, if_true,
      if_false]
    rw [if_pos]
    · rfl
    · simp only [Bool.or_eq_true, beq_iff_eq]
      exact Or.inl (by exact_mod_cast halign)

end Vsa.Sim
