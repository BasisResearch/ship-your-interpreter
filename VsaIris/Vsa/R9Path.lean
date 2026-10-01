import VsaIris.Vsa.Region
import VsaIris.Vsa.R9Omega

namespace VsaIris.VsaHeap

macro "rgn_arith_near" : tactic =>
  `(tactic| first
    | omega_near_only
    | (simp only [VsaIris.Sym.upd_apply, Nat.reduceEqDiff, ite_true, ite_false,
        LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.reduceAppend,
        BitVec.reduceSignExtend, VsaIris.VsaHeap.key_toNat_add,
        VsaIris.VsaHeap.key_toNat_ofNat, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod]
       repeat (first
         | (rw [Nat.mod_eq_of_lt]; rotate_left; omega_near)
         | (rw [VsaIris.VsaHeap.key_sub]; rotate_left; omega_near)
         | fail "no wrap-around to remove")
       first | done | omega_near)
    | omega
    | fail "rgn_arith_near: address arithmetic failed")

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap in
theorem NodeK.end_sep {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} {x : Nat} (N : NodeK H top chunks x)
    (h : HeapAt m H (fun e => e ∈ H) top brkv chunks bins) {a s : Nat} {u : Bool}
    (hc : (⟨a, s, u⟩ : Chunk) ∈ chunks) : a + s ≤ x ∨ x + 32 ≤ a + s := by
  have hb := N.bnd _ (h.end_bnd hc) (a + s - x)
  simp only at hb
  omega

end VsaIris.VsaHeap
