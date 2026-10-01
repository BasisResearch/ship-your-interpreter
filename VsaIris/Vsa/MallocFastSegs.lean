import Vsa.Elf
import Vsa.MemRepr
import Vsa.Sim.BlockDecode
import Vsa.Sim.ExecRetEpilogue
import Vsa.Sim.DlHeap

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa

namespace VsaIris.MallocFast

open Vsa.Sim

theorem ult_iff (a b : BitVec 64) : zopz0zI_u a b = true ↔ a.toNat < b.toNat := by
  unfold zopz0zI_u; simp [Sail.BitVec.toNatInt]

theorem ult_false_iff (a b : BitVec 64) : zopz0zI_u a b = false ↔ b.toNat ≤ a.toNat := by
  unfold zopz0zI_u; simp [Sail.BitVec.toNatInt]

theorem uge_iff (a b : BitVec 64) : zopz0zKzJ_u a b = true ↔ b.toNat ≤ a.toNat := by
  unfold zopz0zKzJ_u; simp [Sail.BitVec.toNatInt]

theorem and_high_toNat (a : BitVec 64) (k : Nat) (hk : k < 64) :
    (a &&& (BitVec.allOnes 64 <<< k)).toNat = a.toNat / 2 ^ k * 2 ^ k := by
  have hshift : (a &&& (BitVec.allOnes 64 <<< k)) = (a >>> k) <<< k := by
    apply BitVec.eq_of_getLsbD_eq
    intro i
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_allOnes]
    by_cases hi : i < k
    · simp [hi]
    · by_cases hlt : i < 64
      · have h3 : k + (i - k) = i := by omega
        have h2 : i - k < 64 := by omega
        simp [hi, hlt, h2, h3]
      · have hge : a.getLsbD i = false := BitVec.getLsbD_of_ge a i (by omega)
        simp [hi, hlt, hge]
  rw [hshift, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  calc a.toNat / 2 ^ k * 2 ^ k ≤ a.toNat := Nat.div_mul_le_self _ _
    _ < 2 ^ 64 := a.isLt

abbrev gpV : BitVec 64 := 0x8001b510#64

def wordOf (f : Nat → BitVec 8) (a : Nat) : List (BitVec 8) :=
  [f a, f (a + 1), f (a + 2), f (a + 3), f (a + 4), f (a + 5), f (a + 6), f (a + 7)]

theorem wordOf_value {f : Nat → BitVec 8} {a : Nat} {m : Std.ExtHashMap Nat (BitVec 8)} {v : BitVec 64}
    (him : ∀ k, k < 8 → m[a + k]? = some (f (a + k))) (hr : Vsa.MemRepr.read64 m a = some v.toNat) :
    bytesVal .ld (wordOf f a) = v := by
  have := execRetEpilogueWord_value m a v hr
  have e : execRetEpilogueWord m a = wordOf f a := by
    simp only [execRetEpilogueWord, wordOf]
    rw [show m[a]? = some (f a) by simpa using him 0 (by omega), him 1 (by omega), him 2 (by omega),
      him 3 (by omega), him 4 (by omega), him 5 (by omega), him 6 (by omega), him 7 (by omega)]
    rfl
  rwa [e] at this

theorem and_m2_toNat (a : BitVec 64) :
    (a &&& sign_extend (m := 64) (0xffe#12)).toNat = a.toNat / 2 * 2 := by
  rw [show (sign_extend (m := 64) (0xffe#12) : BitVec 64) = BitVec.allOnes 64 <<< 1 by decide,
    and_high_toNat a 1 (by decide)]

end VsaIris.MallocFast
