import Vsa.Sim.SplitReadLoop
import Vsa.Sim.RamReadBytes

namespace Vsa.Sim

/-- Each bit of a subrange update comes from the selected input or the old word. -/
theorem getLsbD_updateSubrange' {w : Nat} (x : BitVec w) (lo len : Nat)
    (v : BitVec len) (k : Nat) (hk : k < w) :
    (Sail.BitVec.updateSubrange' x lo len v).getLsbD k =
      if lo ≤ k ∧ k < lo + len then v.getLsbD (k - lo) else x.getLsbD k := by
  simp only [Sail.BitVec.updateSubrange', BitVec.zeroExtend_eq_setWidth,
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes]
  by_cases hlo : lo ≤ k
  · have hkw : k - lo < w := by omega
    by_cases hlen : k < lo + len
    · have hkl : k - lo < len := by omega
      simp [hk, hlo, hkw, hlen, hkl, show ¬ k < lo from by omega]
    · have hkl : ¬ k - lo < len := by omega
      simp [hk, hlo, hkw, hlen, hkl, BitVec.getLsbD_of_ge v _ (by omega : len ≤ k - lo)]
  · simp [hk, hlo, show k < lo from by omega]

/-- Normalize Sail's integer-indexed insertion to its selected bit interval. -/
theorem getLsbD_splitReadInsert (n d i : Nat) (hd : 0 < d)
    (data : BitVec (8 * (n : Int) * (d : Int)).toNat) (v : BitVec (8 * d))
    (k : Nat) (hk : k < 8 * n * d) :
    (splitReadInsert n d i data v).getLsbD k =
      if 8 * i * d ≤ k ∧ k < 8 * (i + 1) * d then
        v.getLsbD (k - 8 * i * d) else data.getLsbD k := by
  have hlo : (8 * (i : Int) * (d : Int)).toNat = 8 * i * d := rfl
  have hhi : (8 * ((i : Int) + 1) * (d : Int) - 1).toNat = 8 * (i + 1) * d - 1 := by
    change ((↑(8 * (i + 1) * d) : Int) - ↑(1 : Nat)).toNat = _
    exact Int.toNat_sub _ _
  have he : 8 * (i + 1) * d = 8 * i * d + 8 * d := by
    simp [Nat.mul_add, Nat.add_mul]
  have hlen : 8 * (i + 1) * d - 1 - 8 * i * d + 1 = 8 * d := by omega
  unfold splitReadInsert
  simp only [hlo, Sail.BitVec.updateSubrange, BitVec.getLsbD_setWidth]
  rw [getLsbD_updateSubrange' _ _ _ _ k hk]
  simp only [BitVec.getLsbD_setWidth, hlo, hhi, hlen]
  have hw : (8 * (n : Int) * (d : Int)).toNat = 8 * n * d := rfl
  simp only [hw]
  by_cases hinside : 8 * i * d ≤ k ∧ k < 8 * (i + 1) * d
  · have hsmall : k - 8 * i * d < 8 * d := by omega
    simp [hinside, he, hk, hsmall]
  · simp [hinside, ← he, hk]

/-- Reassembling consecutive slices reconstructs the complete word. -/
theorem splitReadAccum_eq (n d : Nat) (hd : 0 < d)
    (full : BitVec (8 * (n : Int) * (d : Int)).toNat)
    (values : Nat → BitVec (8 * d))
    (hvalues : ∀ i, i < n → values i = full.extractLsb' (8 * i * d) (8 * d)) :
    splitReadAccum n d values n = full := by
  have hpref : ∀ j, j ≤ n → ∀ k, k < 8 * j * d →
      (splitReadAccum n d values j).getLsbD k = full.getLsbD k := by
    intro j
    induction j with
    | zero => intro _ k hk; simp at hk
    | succ j ih =>
      intro hj k hk
      have hjn : j < n := by omega
      have hkw : k < 8 * n * d :=
        Nat.lt_of_lt_of_le hk (Nat.mul_le_mul_right d (Nat.mul_le_mul_left 8 hj))
      rw [splitReadAccum, getLsbD_splitReadInsert n d j hd _ _ k hkw]
      by_cases hold : k < 8 * j * d
      · rw [if_neg (by omega)]
        exact ih (by omega) k hold
      · rw [if_pos (by omega), hvalues j hjn, BitVec.getLsbD_extractLsb']
        have he : 8 * (j + 1) * d = 8 * j * d + 8 * d := by
          simp [Nat.mul_add, Nat.add_mul]
        have hsmall : k - 8 * j * d < 8 * d := by omega
        have hsum : 8 * j * d + (k - 8 * j * d) = k := by omega
        simp [hsmall, hsum]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro k hk
  exact hpref n (Nat.le_refl n) k hk

/-- Total reads of consecutive chunks assemble to the complete total read. -/
theorem splitReadAccum_bytesT (m : Std.ExtHashMap Nat (BitVec 8)) (a n d : Nat)
    (hd : 0 < d) (values : Nat → BitVec (8 * d))
    (hv : ∀ i, i < n → values i = bytesT m (a + i * d) d) :
    ((splitReadAccum n d values n).setWidth (8 * n * d)).setWidth (8 * (n * d)) =
      bytesT m a (n * d) := by
  have hbits : 8 * (n * d) = (8 * (n : Int) * (d : Int)).toNat := by
    change 8 * (n * d) = 8 * n * d
    exact (Nat.mul_assoc _ _ _).symm
  let full := (bytesT m a (n * d)).cast hbits
  have hvalues : ∀ i, i < n → values i = full.extractLsb' (8 * i * d) (8 * d) := by
    intro i hi
    rw [hv i hi]
    simp only [full, BitVec.extractLsb'_cast, Nat.mul_assoc]
    exact (bytesT_extract m a (n * d) (i * d) d (by
      have h := Nat.mul_le_mul_right d (show i + 1 ≤ n by omega)
      simpa [Nat.add_mul] using h)).symm
  rw [splitReadAccum_eq n d hd full values hvalues]
  simp only [full, BitVec.setWidth_cast]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro k hk
  have hi : k < 8 * n * d := by simpa [Nat.mul_assoc] using hk
  simp [hk, hi]

#print axioms splitReadAccum_bytesT
#print axioms splitReadAccum_eq
#print axioms getLsbD_updateSubrange'
#print axioms getLsbD_splitReadInsert
end Vsa.Sim
