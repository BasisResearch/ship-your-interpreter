import Vsa.Sim.MemWriteBasics

open LeanRV64DExecutable Vsa

namespace Vsa.Sim

theorem getElem?_writeMap4_outside (lo hi : Nat) (mem : Std.ExtHashMap Nat (BitVec 8))
    (k : Nat) (d : BitVec (8 * 4)) (hk : k + 4 ≤ lo ∨ hi ≤ k)
    (a : Nat) (ha1 : lo ≤ a) (ha2 : a < hi) :
    (writeMap4 mem k d)[a]? = mem[a]? := by
  show ((((mem.insert k _).insert (k+1) _).insert (k+2) _).insert (k+3) _)[a]? = mem[a]?
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

end Vsa.Sim
