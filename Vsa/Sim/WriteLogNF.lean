import Vsa.Sim.BlockMem
import Vsa.Sim.FrameOn
import Vsa.Sim.SnprintfSpec25

/-!
# `WriteLogNF` — the write log as the canonical post-memory form

`Vsa/Sim/BlockMem.lean` introduced `writeLog`/`applyW` as *computed* memory
posts (the fold of a block's stores over the entry memory).  This module
provides the interop lemmas that let a `writeLog` post replace the bespoke
`writeMap8 (writeMap4 (writeMap8 …))` chains and their hand-rolled frame /
pin extraction:

* `writeLog_append` — logs concatenate (`foldl` on `++`);
* `applyW_out` / `writeLog_out` — reads outside an entry's / the whole log's
  footprint are unchanged (`OutL`/`OutLRange` are recursive list predicates:
  concrete logs unfold to conjunctions of linear facts, closed by
  `simp only [OutL(Range), and_true]; omega`);
* `frameOn_writeLog` — a log whose entries all land inside the frame windows
  produces the `FrameOn` directly (`LogInW` side condition, same recipe);
* `pin1/pin4/pin8_of_writeLog` — a pin whose range matches one log entry and
  is disjoint from all *later* entries reads back out of the fold;
* `slotHolds_of_writeLog` — the `SlotHolds` shape of the same.

Widths outside `{1,2,4,8}` never occur in real logs; `applyW` ignores them
(`applyW_eq_of_ne`), so every lemma is total over `WEntry` anyway.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa

namespace Vsa.Sim

/-! ## Footprint predicates (recursive; `simp only [...]; omega`-dischargeable) -/

/-- `a` lies outside the footprint of every entry of `log`. -/
def OutL : List WEntry → Nat → Prop
  | [], _ => True
  | e :: log, a => (a < e.1 ∨ e.1 + e.2.1 ≤ a) ∧ OutL log a

/-- The whole range `[A, A+n)` lies outside every entry footprint of `log`. -/
def OutLRange : List WEntry → Nat → Nat → Prop
  | [], _, _ => True
  | e :: log, A, n => (A + n ≤ e.1 ∨ e.1 + e.2.1 ≤ A) ∧ OutLRange log A n

/-- Every entry of `log` writes inside some window of `ws`. -/
def LogInW (ws : List W) : List WEntry → Prop
  | [] => True
  | e :: log => InsideW ws e.1 e.2.1 ∧ LogInW ws log

theorem outL_of_range {log : List WEntry} {A n k : Nat}
    (h : OutLRange log A n) (hk1 : A ≤ k) (hk2 : k < A + n) : OutL log k := by
  induction log with
  | nil => trivial
  | cons e log ih => exact ⟨by have := h.1; omega, ih h.2⟩

/-! ## The fold algebra -/

/-- Logs concatenate: run the first, then the second. -/
theorem writeLog_append (m : Std.ExtHashMap Nat (BitVec 8)) (l1 l2 : List WEntry) :
    writeLog m (l1 ++ l2) = writeLog (writeLog m l1) l2 :=
  List.foldl_append

/-- `applyW` is the identity at widths outside `{1,2,4,8}`. -/
theorem applyW_eq_of_ne (m : Std.ExtHashMap Nat (BitVec 8)) (A w : Nat) (dv : BitVec 64)
    (h1 : w ≠ 1) (h2 : w ≠ 2) (h4 : w ≠ 4) (h8 : w ≠ 8) : applyW m (A, w, dv) = m := by
  unfold applyW
  split <;> simp_all

/-- Reads outside one entry's footprint pass through `applyW`. -/
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

/-- Reads outside the whole log's footprint pass through the fold. -/
theorem writeLog_out (m : Std.ExtHashMap Nat (BitVec 8)) (log : List WEntry) (a : Nat)
    (h : OutL log a) : (writeLog m log)[a]? = m[a]? := by
  induction log generalizing m with
  | nil => rfl
  | cons e log ih =>
    obtain ⟨A, w, dv⟩ := e
    simp only [OutL] at h
    show (writeLog (applyW m (A, w, dv)) log)[a]? = m[a]?
    rw [ih _ h.2, applyW_out m A w dv a h.1]

/-! ## `FrameOn` production: log windows ⊆ frame windows -/

/-- A write log whose entries all land inside the declared windows *is* a
frame: `FrameOn ws m (writeLog m log)` with no pointwise reasoning.  For
concrete `ws`/`log` the side condition closes by
`simp only [LogInW, InsideW, and_true]; omega`. -/
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

/-! ## Pin extraction: one entry, disjoint from all later entries -/

/-- The byte pin of a width-1 log entry disjoint from every later entry. -/
theorem pin1_of_writeLog (m : Std.ExtHashMap Nat (BitVec 8)) (log1 log2 : List WEntry)
    (A : Nat) (dv : BitVec 64) (hdis : OutL log2 A) :
    (writeLog m (log1 ++ (A, 1, dv) :: log2))[A]? = some (sbData dv) := by
  rw [writeLog_append]
  show (writeLog ((writeLog m log1).insert A (sbData dv)) log2)[A]? = some (sbData dv)
  rw [writeLog_out _ log2 A hdis, Std.ExtHashMap.getElem?_insert,
    if_pos (by simp only [beq_iff_eq])]

/-- The `Pin4` of a width-4 log entry disjoint from every later entry (the
pinned word is the entry's `swData` low half, exactly what the `sw` wrote). -/
theorem pin4_of_writeLog (m : Std.ExtHashMap Nat (BitVec 8)) (log1 log2 : List WEntry)
    (A : Nat) (dv : BitVec 64) (hdis : OutLRange log2 A 4) :
    Pin4 (writeLog m (log1 ++ (A, 4, dv) :: log2)) A (swData dv) := by
  rw [writeLog_append]
  show Pin4 (writeLog (writeMap4 (writeLog m log1) A (swData dv)) log2) A (swData dv)
  exact Pin4_frame (fun k hk1 hk2 => writeLog_out _ log2 k (outL_of_range hdis hk1 hk2))
    (Pin4_writeMap4 _ _ _)

/-- The `Pin8` of a width-8 log entry disjoint from every later entry. -/
theorem pin8_of_writeLog (m : Std.ExtHashMap Nat (BitVec 8)) (log1 log2 : List WEntry)
    (A : Nat) (dv : BitVec 64) (hdis : OutLRange log2 A 8) :
    Pin8 (writeLog m (log1 ++ (A, 8, dv) :: log2)) A dv := by
  rw [writeLog_append]
  show Pin8 (writeLog (writeMap8 (writeLog m log1) A (sdData_val dv)) log2) A dv
  exact Pin8_frame (fun k hk1 hk2 => writeLog_out _ log2 k (outL_of_range hdis hk1 hk2))
    (Pin8_writeMap8 _ _ _)

/-- The `SlotHolds` shape of `pin8_of_writeLog` (a spilling `sd` in the log,
disjoint from all later entries; `hA` names the slot's effective address). -/
theorem slotHolds_of_writeLog (m : Std.ExtHashMap Nat (BitVec 8)) (log1 log2 : List WEntry)
    (base : BitVec 64) (off : Nat) (v : BitVec 64) (A : Nat)
    (hA : (base + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat = A)
    (hdis : OutLRange log2 A 8) :
    SlotHolds base off v (writeLog m (log1 ++ (A, 8, v) :: log2)) :=
  slotHolds_of_pin8_rt base off v A _ hA (pin8_of_writeLog m log1 log2 A v hdis)

end Vsa.Sim
