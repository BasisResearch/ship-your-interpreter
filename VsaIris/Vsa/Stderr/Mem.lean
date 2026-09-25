import VsaIris.Vsa.Stdout.Mem

/-!
# The low half of a doubleword load (lane N3)

`__swsetup_r` tests `fp->_flags & (__SSTR | __SMBF)` with a doubleword load of
the flags word (`ld a4,16(a5); andi a4,a4,640`, `0x8000f2b4`) right after a
halfword store to the flags. Only the low 16 bits matter, and those are the
halfword: `ldv_ld_and_lhu`.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast

theorem and_mod_two_pow_16 (x c : Nat) (hc : c < 2 ^ 16) : x &&& c = (x % 2 ^ 16) &&& c := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow]
  by_cases hi : i < 16
  · simp [hi]
  · have : c.testBit i = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc
      (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [this]

theorem ldv_ld_toNat (M : Mem) (a : Nat) : (ldv .ld M a).toNat = imgLE (imgM M) a 8 := by
  rw [show ldv .ld M a = ldvf .ld (imgM M) a from rfl, ldvf_ld_imgLE rfl, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by have := imgLE_lt (imgM M) a 8; omega)

/-- **A doubleword load masked to its low half** is the halfword load, masked. -/
theorem ldv_ld_and_lhu (M : Mem) (a : Nat) (c : BitVec 64) (hc : c.toNat < 2 ^ 16) :
    ldv .ld M a &&& c = ldv .lhu M a &&& c := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_and, ldv_ld_toNat, ldv_lhu_img, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := imgLE_lt (imgM M) a 2; omega), and_mod_two_pow_16 _ _ hc,
    show imgLE (imgM M) a 8 = imgLE (imgM M) a (2 + 6) from rfl, imgLE_split]
  congr 1
  have := imgLE_lt (imgM M) a 2
  rw [show (256 : Nat) ^ 2 = 2 ^ 16 by decide, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)

end VsaIris.Sym

namespace VsaIris.Sym
open Vsa.Sim Vsa.MemRepr

/-- `__swsetup_r`'s mask (`__SSTR | __SMBF`) of the doubleword flags load. -/
theorem ldv_ld_and_640 (M : Mem) (a : Nat) : ldv .ld M a &&& 640#64 = ldv .lhu M a &&& 640#64 :=
  ldv_ld_and_lhu M a _ (by decide)

end VsaIris.Sym

namespace VsaIris.Sym

/-- `sext.w` of a word below `2^31` is the word. -/
theorem sext_extract32_small {n : BitVec 64} (h : n.toNat < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 n) = n := by
  apply BitVec.eq_of_toNat_eq
  have hx : (BitVec.extractLsb 31 0 n).toNat = n.toNat := by
    simp only [BitVec.extractLsb_toNat, Nat.shiftRight_zero]; omega
  have hmsb : (BitVec.extractLsb 31 0 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [decide_eq_false_iff_not, Nat.not_le]; omega
  rw [BitVec.toNat_signExtend, hmsb]
  simp only [Bool.false_eq_true, ite_false, Nat.add_zero, BitVec.toNat_setWidth, hx]
  omega

end VsaIris.Sym
