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

end VsaIris.VsaHeap
