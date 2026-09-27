namespace VsaIris.Sym

theorem toNat_ofNat_lt {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  simp only [BitVec.toNat_ofNat]; omega

theorem toInt_ofNat_small {x : Nat} (h : x < 2 ^ 63) : (BitVec.ofNat 64 x).toInt = x := by
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_ofNat]
  split <;> omega

def strBytes (x : String) : List (BitVec 8) := x.toList.map fun c => BitVec.ofNat 8 c.toNat

end VsaIris.Sym
