import Vsa.Sim.ValueSites
import Vsa.Sim.ValueSpec

open LeanRV64DExecutable Vsa

namespace Vsa.Sim

theorem getElem?_writeMap8_out (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat)
    (d : BitVec (8 * 8)) (a : Nat) (ha : a < k ∨ k + 8 ≤ a) :
    (writeMap8 mem k d)[a]? = mem[a]? := by
  show ((((((((mem.insert k _).insert (k+1) _).insert (k+2) _).insert (k+3) _).insert
    (k+4) _).insert (k+5) _).insert (k+6) _).insert (k+7) _)[a]? = mem[a]?
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

def Pin4 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (w : BitVec 32) : Prop :=
  mem[a]? = some (w.extractLsb' 0 8) ∧
  mem[a + 1]? = some (w.extractLsb' 8 8) ∧
  mem[a + 2]? = some (w.extractLsb' 16 8) ∧
  mem[a + 3]? = some (w.extractLsb' 24 8)

theorem Pin4_writeMap4 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (w : BitVec 32) :
    Pin4 (writeMap4 mem a w) a w :=
  ⟨getElem_writeMap4_0 _ _ _, getElem_writeMap4_1 _ _ _,
   getElem_writeMap4_2 _ _ _, getElem_writeMap4_3 _ _ _⟩

theorem Pin4_frame {mem mem' : Std.ExtHashMap Nat (BitVec 8)} {a : Nat} {w : BitVec 32}
    (hf : ∀ k, a ≤ k → k < a + 4 → mem'[k]? = mem[k]?) (h : Pin4 mem a w) : Pin4 mem' a w :=
  ⟨(hf a (by omega) (by omega)).trans h.1,
   (hf (a+1) (by omega) (by omega)).trans h.2.1,
   (hf (a+2) (by omega) (by omega)).trans h.2.2.1,
   (hf (a+3) (by omega) (by omega)).trans h.2.2.2⟩

end Vsa.Sim
