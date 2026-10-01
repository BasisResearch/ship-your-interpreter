import Vsa.Sim.MfrAttr
import Vsa.Sim.CodeRangeInsert
import Vsa.Sim.MemWriteBasics

open LeanRV64DExecutable Vsa

namespace Vsa.Sim

theorem getElem?_insert_out (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat)
    (v : BitVec 8) (a : Nat) (ha : a ≠ k) :
    (mem.insert k v)[a]? = mem[a]? := by
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

theorem getElem?_writeMap4_out (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat)
    (d : BitVec (8 * 4)) (a : Nat) (ha : a < k ∨ k + 4 ≤ a) :
    (writeMap4 mem k d)[a]? = mem[a]? :=
  getElem?_writeMap4_outside a (a + 1) mem k d (by omega) a (Nat.le_refl a) (by omega)

attribute [mfr]
  getElem?_writeMap8_out
  getElem?_writeMap4_out
  getElem?_insert_out

end Vsa.Sim
