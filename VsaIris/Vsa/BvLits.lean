/-!
# Literal `BitVec` facts shared by the symbolic runs (lanes N1, N2)

`toNat_ofNat_lt`/`toInt_ofNat_small` turn a small literal address or count
back into its number; `strBytes` is a string's byte list as `sb`/`lbu` see
it. One copy for the stdout runs (`Vsa/Stdout/`) and the `snprintf` runs
(`Vsa/Snp*.lean`).
-/

namespace VsaIris.Sym

theorem toNat_ofNat_lt {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  simp only [BitVec.toNat_ofNat]; omega

theorem toInt_ofNat_small {x : Nat} (h : x < 2 ^ 63) : (BitVec.ofNat 64 x).toInt = x := by
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_ofNat]
  split <;> omega

/-- A string's bytes, one per character. -/
def strBytes (x : String) : List (BitVec 8) := x.toList.map fun c => BitVec.ofNat 8 c.toNat

end VsaIris.Sym
