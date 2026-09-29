import Vsa.Sim.BlockMem
import Vsa.Sim.FrameOn
import Vsa.Sim.DecodeNF
import Vsa.Sim.SnprintfSitesRet5
import Vsa.Sim.SnprintfSpec20

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa

namespace Vsa.Sim

def OutL : List WEntry → Nat → Prop
  | [], _ => True
  | e :: log, a => (a < e.1 ∨ e.1 + e.2.1 ≤ a) ∧ OutL log a

def OutLRange : List WEntry → Nat → Nat → Prop
  | [], _, _ => True
  | e :: log, A, n => (A + n ≤ e.1 ∨ e.1 + e.2.1 ≤ A) ∧ OutLRange log A n

def LogInW (ws : List W) : List WEntry → Prop
  | [] => True
  | e :: log => InsideW ws e.1 e.2.1 ∧ LogInW ws log

theorem outL_of_range {log : List WEntry} {A n k : Nat}
    (h : OutLRange log A n) (hk1 : A ≤ k) (hk2 : k < A + n) : OutL log k := by
  induction log with
  | nil => trivial
  | cons e log ih => exact ⟨by have := h.1; omega, ih h.2⟩

theorem writeLog_append (m : Std.ExtHashMap Nat (BitVec 8)) (l1 l2 : List WEntry) :
    writeLog m (l1 ++ l2) = writeLog (writeLog m l1) l2 :=
  List.foldl_append

theorem applyW_eq_of_ne (m : Std.ExtHashMap Nat (BitVec 8)) (A w : Nat) (dv : BitVec 64)
    (h1 : w ≠ 1) (h2 : w ≠ 2) (h4 : w ≠ 4) (h8 : w ≠ 8) : applyW m (A, w, dv) = m := by
  unfold applyW
  split <;> simp_all

theorem applyW_out (m : Std.ExtHashMap Nat (BitVec 8)) (A w : Nat) (dv : BitVec 64)
    (a : Nat) (h : a < A ∨ A + w ≤ a) :
    (applyW m (A, w, dv))[a]? = m[a]? := by
  by_cases h1 : w = 1
  · subst h1
    show (m.insert A (sbData dv))[a]? = m[a]?
    rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]
  · by_cases h2 : w = 2
    · subst h2
      show ((m.insert A ((shData dv).extractLsb' 0 8)).insert (A + 1)
          ((shData dv).extractLsb' 8 8))[a]? = m[a]?
      exact getElem_writeMap2_disjoint m A a (shData dv) (by omega)
    · by_cases h4 : w = 4
      · subst h4
        show (writeMap4 m A (swData dv))[a]? = m[a]?
        exact getElem?_writeMap4_out _ _ _ _ (by omega)
      · by_cases h8 : w = 8
        · subst h8
          show (writeMap8 m A (sdData_val dv))[a]? = m[a]?
          exact getElem?_writeMap8_out _ _ _ _ (by omega)
        · rw [applyW_eq_of_ne m A w dv h1 h2 h4 h8]

theorem writeLog_out (m : Std.ExtHashMap Nat (BitVec 8)) (log : List WEntry) (a : Nat)
    (h : OutL log a) : (writeLog m log)[a]? = m[a]? := by
  induction log generalizing m with
  | nil => rfl
  | cons e log ih =>
    obtain ⟨A, w, dv⟩ := e
    simp only [OutL] at h
    show (writeLog (applyW m (A, w, dv)) log)[a]? = m[a]?
    rw [ih _ h.2, applyW_out m A w dv a h.1]

theorem frameOn_writeLog (ws : List W) (m : Std.ExtHashMap Nat (BitVec 8))
    (log : List WEntry) (h : LogInW ws log) : FrameOn ws m (writeLog m log) := by
  induction log generalizing m with
  | nil => exact frameOn_refl ws m
  | cons e log ih =>
    obtain ⟨A, w, dv⟩ := e
    simp only [LogInW] at h
    intro a ha
    show (writeLog (applyW m (A, w, dv)) log)[a]? = m[a]?
    rw [ih _ h.2 a ha]
    exact applyW_out m A w dv a (outW_disjoint_inside ha h.1)

theorem pin1_of_writeLog (m : Std.ExtHashMap Nat (BitVec 8)) (log1 log2 : List WEntry)
    (A : Nat) (dv : BitVec 64) (hdis : OutL log2 A) :
    (writeLog m (log1 ++ (A, 1, dv) :: log2))[A]? = some (sbData dv) := by
  rw [writeLog_append]
  show (writeLog ((writeLog m log1).insert A (sbData dv)) log2)[A]? = some (sbData dv)
  rw [writeLog_out _ log2 A hdis, Std.ExtHashMap.getElem?_insert,
    if_pos (by simp only [beq_iff_eq])]

theorem pin4_of_writeLog (m : Std.ExtHashMap Nat (BitVec 8)) (log1 log2 : List WEntry)
    (A : Nat) (dv : BitVec 64) (hdis : OutLRange log2 A 4) :
    Pin4 (writeLog m (log1 ++ (A, 4, dv) :: log2)) A (swData dv) := by
  rw [writeLog_append]
  show Pin4 (writeLog (writeMap4 (writeLog m log1) A (swData dv)) log2) A (swData dv)
  exact Pin4_frame (fun k hk1 hk2 => writeLog_out _ log2 k (outL_of_range hdis hk1 hk2))
    (Pin4_writeMap4 _ _ _)

end Vsa.Sim
