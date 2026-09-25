import VsaIris.Interp.HelperRun

/-!
# Store forwarding at every width (lane N1)

newlib's stdio code stores `FILE` fields with `sw`/`sh`/`sb` and reloads
them with `lw`/`lh`/`lhu`/`lbu` (`_putc_r` decrements `_w`, `__swbuf_r` reads
it back; `__swrite` rewrites `_flags`, `_fflush_r` reloads it). `ix_mem`
(`Arm.lean`) forwards doublewords and words through doubleword stores; this
module adds every load kind through a store of any width: the misses
(`ldv_*_miss`: disjoint bytes) and the hits (`ldv_*_hit`: the same address
and width, value the stored value's low bytes, `ofNat` of a `%`, which the
normalizer reduces for literal stores). `nx_mem` is `ix_mem` with them.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-! ## Load values through the little-endian image -/

theorem toNat_append2 (f : Nat → BitVec 8) (a : Nat) :
    (((f (a + 1)).append (f a)) : BitVec (8 * 2)).toNat = imgLE f a 2 := by
  simp only [BitVec.append_eq, BitVec.toNat_append, imgLE]
  have h0 := (f a).isLt; have h1 := (f (a + 1)).isLt
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
  simp only [Nat.shiftLeft_eq, Nat.reducePow]
  omega

theorem bytesAt2 (f : Nat → BitVec 8) (a : Nat) : bytesAt f a 2 = [f a, f (a + 1)] := rfl
theorem bytesAt1 (f : Nat → BitVec 8) (a : Nat) : bytesAt f a 1 = [f a] := by simp [bytesAt]

theorem ldv_lw_img (M : Mem) (a : Nat) :
    ldv .lw M a = sign_extend (m := 64) (BitVec.ofNat 32 (imgLE (imgM M) a 4)) := by
  have hw := toNat_append4 (imgM M) a
  simp only [ldv, bytesAt4, bytesVal, widthOfM, List.getD_cons_zero, List.getD_cons_succ]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := imgLE_lt (imgM M) a 4; omega)]

theorem ldv_lh_img (M : Mem) (a : Nat) :
    ldv .lh M a = sign_extend (m := 64) (BitVec.ofNat 16 (imgLE (imgM M) a 2)) := by
  have hw := toNat_append2 (imgM M) a
  simp only [ldv, bytesAt2, bytesVal, widthOfM, List.getD_cons_zero, List.getD_cons_succ]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := imgLE_lt (imgM M) a 2; omega)]

theorem ldv_lhu_img (M : Mem) (a : Nat) :
    ldv .lhu M a = BitVec.ofNat 64 (imgLE (imgM M) a 2) := by
  have hw := toNat_append2 (imgM M) a
  have hk := imgLE_lt (imgM M) a 2
  simp only [ldv, bytesAt2, bytesVal, widthOfM, List.getD_cons_zero, List.getD_cons_succ]
  apply BitVec.eq_of_toNat_eq
  simp only [LeanRV64DExecutable.zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth]
  rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem ldv_lbu_img (M : Mem) (a : Nat) :
    ldv .lbu M a = BitVec.ofNat 64 (imgLE (imgM M) a 1) := by
  have hk := (imgM M a).isLt
  simp only [ldv, bytesAt1, bytesVal, widthOfM, List.getD_cons_zero, imgLE]
  apply BitVec.eq_of_toNat_eq
  simp only [LeanRV64DExecutable.zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mul_zero, Nat.add_zero,
    Nat.mod_eq_of_lt (by omega)]

/-! ## Stores read back -/

theorem imgLE_store2_hit (Mt : Mem) (a : Nat) (v : BitVec 64) :
    imgLE (imgM (writeLog Mt [(a, 2, v)])) a 2 = v.toNat % 2 ^ 16 := by
  simp only [imgLE, imgM, writeLog, List.foldl_cons, List.foldl_nil, applyW]
  rw [Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert,
    Std.ExtHashMap.getElem?_insert_self]
  simp only [beq_iff_eq, show ¬ (a + 1 = a) by omega, ite_false, ite_true, Option.getD_some,
    Nat.mul_zero, Nat.add_zero]
  simp only [shData, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
    BitVec.toNat_ofNat, Nat.shiftRight_zero, Nat.reduceMul, Nat.reducePow]
  have hv := v.isLt
  rw [Nat.shiftRight_eq_div_pow]
  simp only [Nat.reducePow]
  omega

theorem imgLE_store1_hit (Mt : Mem) (a : Nat) (v : BitVec 64) :
    imgLE (imgM (writeLog Mt [(a, 1, v)])) a 1 = v.toNat % 2 ^ 8 := by
  simp only [imgLE, imgM, writeLog, List.foldl_cons, List.foldl_nil, applyW,
    Std.ExtHashMap.getElem?_insert_self, Option.getD_some, Nat.mul_zero, Nat.add_zero]
  show (BitVec.ofNat 8 v.toNat).toNat = _
  simp [BitVec.toNat_ofNat]

theorem ldv_lw_hit (Mt : Mem) {a b : Nat} (v : BitVec 64) (h : a = b) :
    ldv .lw (writeLog Mt [(b, 4, v)]) a = sign_extend (m := 64) (BitVec.ofNat 32 (v.toNat % 2 ^ 32)) := by
  subst h; rw [ldv_lw_img, imgLE_store4_hit]

theorem ldv_lh_hit (Mt : Mem) {a b : Nat} (v : BitVec 64) (h : a = b) :
    ldv .lh (writeLog Mt [(b, 2, v)]) a = sign_extend (m := 64) (BitVec.ofNat 16 (v.toNat % 2 ^ 16)) := by
  subst h; rw [ldv_lh_img, imgLE_store2_hit]

theorem ldv_lhu_hit (Mt : Mem) {a b : Nat} (v : BitVec 64) (h : a = b) :
    ldv .lhu (writeLog Mt [(b, 2, v)]) a = BitVec.ofNat 64 (v.toNat % 2 ^ 16) := by
  subst h; rw [ldv_lhu_img, imgLE_store2_hit]

theorem ldv_lbu_hit (Mt : Mem) {a b : Nat} (v : BitVec 64) (h : a = b) :
    ldv .lbu (writeLog Mt [(b, 1, v)]) a = BitVec.ofNat 64 (v.toNat % 2 ^ 8) := by
  subst h; rw [ldv_lbu_img, imgLE_store1_hit]

/-! ## Disjoint stores -/

theorem ldv_lh_miss (Mt : Mem) {a b w : Nat} (v : BitVec 64) (h : a + 2 ≤ b ∨ b + w ≤ a) :
    ldv .lh (writeLog Mt [(b, w, v)]) a = ldv .lh Mt a := ldv_store_miss .lh Mt v h
theorem ldv_lhu_miss (Mt : Mem) {a b w : Nat} (v : BitVec 64) (h : a + 2 ≤ b ∨ b + w ≤ a) :
    ldv .lhu (writeLog Mt [(b, w, v)]) a = ldv .lhu Mt a := ldv_store_miss .lhu Mt v h
theorem ldv_lbu_miss (Mt : Mem) {a b w : Nat} (v : BitVec 64) (h : a + 1 ≤ b ∨ b + w ≤ a) :
    ldv .lbu (writeLog Mt [(b, w, v)]) a = ldv .lbu Mt a := ldv_store_miss .lbu Mt v h
theorem ldv_lwu_miss (Mt : Mem) {a b w : Nat} (v : BitVec 64) (h : a + 4 ≤ b ∨ b + w ≤ a) :
    ldv .lwu (writeLog Mt [(b, w, v)]) a = ldv .lwu Mt a := ldv_store_miss .lwu Mt v h

/-! ### Goal-only address arithmetic

`sx_addr` normalizes every hypothesis (`simp … at *`), which dominates a
long run's cost: the context holds the run's facts and summaries. `nx_addr`
rewrites only the goal: `(x + k#64).toNat` becomes `x.toNat + k` or
`x.toNat - (2^64 - k)` (a negative offset), side conditions by `omega` from
the context's bounds; then `omega`. -/

theorem toNat_add_lit {x : BitVec 64} {k : Nat} (h : x.toNat + k < 2 ^ 64) :
    (x + BitVec.ofNat 64 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have : k < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt h]

theorem toNat_add_neg {x : BitVec 64} {k : Nat} (hk : k < 2 ^ 64) (h : 2 ^ 64 ≤ x.toNat + k) :
    (x + BitVec.ofNat 64 k).toNat = x.toNat - (2 ^ 64 - k) := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  have := x.isLt
  omega

syntax "nx_addr" : tactic
macro_rules
  | `(tactic| nx_addr) => `(tactic| ((try simp (disch := omega) only [mem_accAddrs_iff, LdOK, StOK, StOKb, Vsa.Sim.tohostAddr, toNat_add_lit, toNat_add_neg, BitVec.toNat_ofNat,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, and_true, true_and]); omega))

/-- Store forwarding at every width, for stdio runs. -/
syntax "nx_mem" : tactic
macro_rules
  | `(tactic| nx_mem) => `(tactic| simp (disch := nx_addr) only [ldv_store_hit, ldv_ld_hit_eq,
      ldv_ld_miss, ldv_lw_miss, ldv_lw_store8, ldv_lw_hit, ldv_lh_hit, ldv_lhu_hit, ldv_lbu_hit,
      ldv_lh_miss, ldv_lhu_miss, ldv_lbu_miss, ldv_lwu_miss])

end VsaIris.Sym
