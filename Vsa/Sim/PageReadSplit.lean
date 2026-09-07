import Vsa.Sim.ExecuteLoad

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register Sail.ConcurrencyInterfaceV1.PreSail
namespace Vsa.Sim

/-- The actual page planner's pair for a short, nonwrapping read. -/
def pageReadParts (a : BitVec 64) (w : Nat) : Int × Int :=
  if (a.toNat + (w - 1)) / 4096 = a.toNat / 4096 then ((w : Int), 0)
  else (8 - (a.toNat % 8 : Nat), (w : Int) - (8 - (a.toNat % 8 : Nat)))

/-- Short RAM reads complete the actual page split computation even when
misalignment crosses the page. Bare translation subsequently ignores this pair. -/
theorem split_on_page_boundary_ram
    (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64) (w : Nat)
    (hwpos : 0 < w) (hwle : w ≤ 8) (hwrap : a.toNat + w ≤ 2 ^ 64) :
    (split_on_page_boundary a w).run σ = .ok (pageReadParts a w) σ := by
  by_cases hpage : (a.toNat + (w - 1)) / 4096 = a.toNat / 4096
  · simpa only [pageReadParts, hpage, if_true] using
      split_on_page_boundary_data_w σ a w hwpos hwle hpage
  · have hmask : (Sail.BitVec.updateSubrange ((ones (n := 64)) : BitVec 64)
        (Functions.pagesize_bits -i 1) 0 (zeros (n := ((12 -i 1) -i (0 -i 1))))) =
        0xFFFFFFFFFFFFF000#64 := by
      apply BitVec.eq_of_toNat_eq
      decide
    have hend : (Sail.BitVec.subInt (Sail.BitVec.addInt a (w : Int)) 1).toNat =
        a.toNat + (w - 1) := by
      simp only [Sail.BitVec.subInt, Sail.BitVec.addInt, BitVec.toNat_sub,
        BitVec.toNat_add, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
      have ha := a.isLt
      have hone : (BitVec.ofInt 64 1).toNat = 1 := by decide
      rw [hone]
      omega
    have hintra : ((a &&& 0xFFFFFFFFFFFFF000#64) ==
        (Sail.BitVec.subInt (Sail.BitVec.addInt a (w : Int)) 1 &&& 0xFFFFFFFFFFFFF000#64)) = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      have heq := congrArg BitVec.toNat (beq_iff_eq.mp h)
      rw [and_page_mask_toNat, and_page_mask_toNat, hend] at heq
      omega
    have hlow : (Sail.BitVec.extractLsb a (3 -i 1) 0).toNat = a.toNat % 8 := by
      simp [Sail.BitVec.extractLsb, Nat.shiftRight_eq_div_pow]
    have hbytes : (8 : Int) - (a.toNat % 8 : Nat) < (w : Int) := by omega
    simp only [split_on_page_boundary, Sail.BitVec.length, hmask, hintra,
      Bool.false_eq_true, if_false, BitVec.toNatInt, hlow, pageReadParts, hpage]
    have hbytesInt : (8 : Int) - (a.toNat : Int) % 8 < (w : Int) := by
      exact_mod_cast hbytes
    simp [simp_sail, LeanRV64DExecutable.assert, PreSail.assert, hbytesInt,
      show (2 : Int) ^ (3 : Int) = 8 from by decide,
      bind, EStateM.bind, EStateM.run, pure, EStateM.pure]

#print axioms split_on_page_boundary_ram
end Vsa.Sim
