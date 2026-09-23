import VsaIris.Interp.Repr
import Vsa.Sim.JmpSpec
import Vsa.Sim.BlockMem
open Vsa.Sim VsaIris.Interp LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

def imgWord (img : Nat → BitVec 8) (a : Nat) : List (BitVec 8) :=
  [img a, img (a + 1), img (a + 2), img (a + 3), img (a + 4), img (a + 5), img (a + 6), img (a + 7)]

theorem toNat_append8 {m : Nat} (x : BitVec m) (y : BitVec 8) :
    (x.append y).toNat = y.toNat + 256 * x.toNat := by
  change (x ++ y).toNat = _
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]
  omega

theorem bytesVal_imgWord (img : Nat → BitVec 8) (a : Nat) :
    bytesVal .ld (imgWord img a) = imgW img a := by
  apply BitVec.eq_of_toNat_eq
  rw [imgW_toNat]
  simp only [bytesVal, imgWord, List.getD_cons_zero, List.getD_cons_succ, sext64_id_jmp]
  simp only [imgLE, toNat_append8, Nat.add_assoc, Nat.reduceAdd]
  omega
