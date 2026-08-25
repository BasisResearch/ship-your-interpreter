import Vsa.Sim.MemcpySpec

/-!
# `PtrArith` — canonical pointer / sign-extended-immediate arithmetic

The pointer lemmas used by every Layer-3 composition, in one place.  Existing
staples live elsewhere and stay put (`ptr_toNat`/`ptr_succ` in `MemcpySpec`,
`sub1_bv_sn5` in `SnprintfSpec5`); this file adds the *generic* forms new
compositions should reach for, plus the negative-immediate `toNat` constants.

**Kernel-recursion gotcha (recurring):** never prove a minus-K pointer identity
via `simp only [BitVec.toNat_add, BitVec.toNat_ofNat]` followed by rewriting a
`2^64 − K` literal and `omega` — the kernel dies with "deep recursion detected"
when more than one `toNat_ofNat` mod is in play.  The safe shape (used by
`ptr_sub` below, same as `sub1_bv_sn5`): `apply BitVec.eq_of_toNat_eq`, then a
single `rw [BitVec.toNat_add, <sext constant>, BitVec.toNat_ofNat]`, then
`omega` with `v.isLt` in context.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa

namespace Vsa.Sim

/-! ## Negative 12-bit immediates as `toNat` constants

Proved by the staged route (`toNat_signExtend` → `msb` → `decide`); a bare
`decide` on the unfolded `sign_extend` can blow the kernel. -/

theorem sext_fff_toNat : (sign_extend (m := 64) (0xfff#12) : BitVec 64).toNat = 2^64 - 1 := by
  show ((0xfff#12).signExtend 64).toNat = _
  rw [BitVec.toNat_signExtend]; simp only [BitVec.msb]; decide

theorem sext_ff8_toNat : (sign_extend (m := 64) (0xff8#12) : BitVec 64).toNat = 2^64 - 8 := by
  show ((0xff8#12).signExtend 64).toNat = _
  rw [BitVec.toNat_signExtend]; simp only [BitVec.msb]; decide

theorem sext_ff0_toNat : (sign_extend (m := 64) (0xff0#12) : BitVec 64).toNat = 2^64 - 16 := by
  show ((0xff0#12).signExtend 64).toNat = _
  rw [BitVec.toNat_signExtend]; simp only [BitVec.msb]; decide

theorem sext_fe0_toNat : (sign_extend (m := 64) (0xfe0#12) : BitVec 64).toNat = 2^64 - 32 := by
  show ((0xfe0#12).signExtend 64).toNat = _
  rw [BitVec.toNat_signExtend]; simp only [BitVec.msb]; decide

theorem sext_fd0_toNat : (sign_extend (m := 64) (0xfd0#12) : BitVec 64).toNat = 2^64 - 48 := by
  show ((0xfd0#12).signExtend 64).toNat = _
  rw [BitVec.toNat_signExtend]; simp only [BitVec.msb]; decide

theorem sext_fc0_toNat : (sign_extend (m := 64) (0xfc0#12) : BitVec 64).toNat = 2^64 - 64 := by
  show ((0xfc0#12).signExtend 64).toNat = _
  rw [BitVec.toNat_signExtend]; simp only [BitVec.msb]; decide

/-! ## Generic additive / subtractive pointer normal forms -/

/-- `(v + sext imm).toNat = v.toNat + k` for a non-negative immediate worth `k`,
under no-wrap.  (Positive `(sext imm).toNat = k` facts close by `decide`.) -/
theorem ptr_addoff (v : BitVec 64) (imm : BitVec 12) (k : Nat)
    (himm : (sign_extend (m := 64) imm : BitVec 64).toNat = k)
    (hnw : v.toNat + k < 2^64) :
    (v + sign_extend (m := 64) imm).toNat = v.toNat + k := by
  rw [BitVec.toNat_add, himm, Nat.mod_eq_of_lt hnw]

/-- `v + sext imm = ofNat (v.toNat − k)` for a negative immediate worth `−k`
(`himm` from the constants above), given `k ≤ v.toNat`.  Kernel-safe shape. -/
theorem ptr_sub (v : BitVec 64) (imm : BitVec 12) (k : Nat)
    (himm : (sign_extend (m := 64) imm : BitVec 64).toNat = 2^64 - k)
    (hk : k ≤ v.toNat) :
    v + sign_extend (m := 64) imm = BitVec.ofNat 64 (v.toNat - k) := by
  have hlt := v.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, himm, BitVec.toNat_ofNat]
  omega

/-- `toNat` form of `ptr_sub`. -/
theorem ptr_sub_toNat (v : BitVec 64) (imm : BitVec 12) (k : Nat)
    (himm : (sign_extend (m := 64) imm : BitVec 64).toNat = 2^64 - k)
    (hk : k ≤ v.toNat) :
    (v + sign_extend (m := 64) imm).toNat = v.toNat - k := by
  have hlt := v.isLt
  rw [ptr_sub v imm k himm hk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-! ## Stack-frame round trips (`addi sp,sp,-K` … `addi sp,sp,K`) -/

/-- Cancelling immediate pair: `(v + x) + y = v` whenever `x + y = 0`.
Total — no side conditions, works for any prologue/epilogue pair. -/
theorem add_cancel_pair (v x y : BitVec 64) (h : x + y = 0#64) : (v + x) + y = v := by
  rw [BitVec.add_assoc, h, BitVec.add_zero]

theorem sp_dec16_restore (vsp : BitVec 64) :
    (vsp + sign_extend (m := 64) (0xff0#12)) + sign_extend (m := 64) (0x010#12) = vsp :=
  add_cancel_pair _ _ _ (by apply BitVec.eq_of_toNat_eq; decide)

theorem sp_dec32_restore (vsp : BitVec 64) :
    (vsp + sign_extend (m := 64) (0xfe0#12)) + sign_extend (m := 64) (0x020#12) = vsp :=
  add_cancel_pair _ _ _ (by apply BitVec.eq_of_toNat_eq; decide)

theorem sp_dec48_restore (vsp : BitVec 64) :
    (vsp + sign_extend (m := 64) (0xfd0#12)) + sign_extend (m := 64) (0x030#12) = vsp :=
  add_cancel_pair _ _ _ (by apply BitVec.eq_of_toNat_eq; decide)

theorem sp_dec64_restore (vsp : BitVec 64) :
    (vsp + sign_extend (m := 64) (0xfc0#12)) + sign_extend (m := 64) (0x040#12) = vsp :=
  add_cancel_pair _ _ _ (by apply BitVec.eq_of_toNat_eq; decide)

end Vsa.Sim
