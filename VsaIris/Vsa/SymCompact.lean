import VsaIris.Vsa.SymRun

/-!
# Compacting a symbolic state (lane N3)

A long symbolic run (`SWP`) accumulates its whole write log in the tracking
memory and every register update in the register file, so each step costs
more than the last. At a function return the callee's stack frame is dead:
nothing reads it before writing it again. This file forgets dead state:

* `fillR M lo n g`: the memory `M` with the bytes `[lo, lo + n)` replaced by
  `g`. `fillR_writeLog_in` drops a store inside the region, and
  `fillR_writeLog_out` moves the region below a store outside it; together
  they push `fillR` under the live stores and erase the dead ones (term
  equalities: `Std.ExtHashMap` is extensional, and every store is pointwise,
  `pointwise_applyW`).
* `swp_forget_region`: to run from `Mt`, it suffices to run from `Mt` with the
  region at ANY bytes (instantiate `g` at `Mt`'s own image).
* `swp_forget_reg`: likewise for a register at any value.
* `upd_upd_same`/`upd_upd_lt`: the register file as at most one update per
  register, sorted.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

/-- `M` with the bytes `[lo, lo + n)` set to `g`. -/
def fillR (M : Mem) (lo : Nat) : Nat → (Nat → BitVec 8) → Mem
  | 0, _ => M
  | n + 1, g => (fillR M lo n g).insert (lo + n) (g (lo + n))

theorem fillR_get (M : Mem) (lo : Nat) (g : Nat → BitVec 8) (k : Nat) :
    ∀ n, (fillR M lo n g)[k]? = if lo ≤ k ∧ k < lo + n then some (g k) else M[k]?
  | 0 => by simp only [fillR]; rw [if_neg (by omega)]
  | n + 1 => by
    simp only [fillR]
    rw [Std.ExtHashMap.getElem?_insert, fillR_get M lo g k n]
    by_cases h : lo + n = k
    · subst h; simp
    · simp only [beq_iff_eq, h, ite_false]
      by_cases h2 : lo ≤ k ∧ k < lo + n
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

/-- A store inside the region is erased by it. -/
theorem fillR_writeLog_in (M : Mem) {lo n a w : Nat} (v : BitVec 64) (g : Nat → BitVec 8)
    (h : lo ≤ a ∧ a + w ≤ lo + n) :
    fillR (writeLog M [(a, w, v)]) lo n g = fillR M lo n g := by
  apply Std.ExtHashMap.ext_getElem?
  intro k
  rw [fillR_get, fillR_get]
  by_cases hk : lo ≤ k ∧ k < lo + n
  · rw [if_pos hk, if_pos hk]
  · rw [if_neg hk, if_neg hk, writeLog_out _ _ _ (show OutL [(a, w, v)] k from ⟨show k < a ∨ a + w ≤ k by omega, trivial⟩)]

/-- The region moves below a store outside it. -/
theorem fillR_writeLog_out (M : Mem) {lo n a w : Nat} (v : BitVec 64) (g : Nat → BitVec 8)
    (h : a + w ≤ lo ∨ lo + n ≤ a) :
    fillR (writeLog M [(a, w, v)]) lo n g = writeLog (fillR M lo n g) [(a, w, v)] := by
  apply Std.ExtHashMap.ext_getElem?
  intro k
  rw [fillR_get]
  by_cases hk : lo ≤ k ∧ k < lo + n
  · rw [if_pos hk, writeLog_out _ _ _ (show OutL [(a, w, v)] k from ⟨show k < a ∨ a + w ≤ k by omega, trivial⟩), fillR_get,
      if_pos hk]
  · rw [if_neg hk]
    rcases pointwise_writeLog [(a, w, v)] k with hp | ⟨b, hp⟩
    · rw [hp, hp, fillR_get, if_neg hk]
    · rw [hp, hp]

theorem imgM_fillR_out (M : Mem) {lo n k : Nat} (g : Nat → BitVec 8)
    (h : k < lo ∨ lo + n ≤ k) : imgM (fillR M lo n g) k = imgM M k := by
  unfold imgM; rw [fillR_get, if_neg (by omega)]

theorem imgM_fillR_in (M : Mem) {lo n k : Nat} (g : Nat → BitVec 8)
    (h : lo ≤ k ∧ k < lo + n) : imgM (fillR M lo n g) k = g k := by
  unfold imgM; rw [fillR_get, if_pos h]; rfl

/-- A load outside the region reads through it. -/
theorem ldv_fillR_miss (k : MKind) (M : Mem) {lo n a : Nat} (g : Nat → BitVec 8)
    (h : a + widthOfM k ≤ lo ∨ lo + n ≤ a) : ldv k (fillR M lo n g) a = ldv k M a := by
  unfold ldv bytesAt
  congr 1
  refine List.map_congr_left fun j hj => ?_
  have := List.mem_range.mp hj
  exact imgM_fillR_out M g (by omega)

theorem ldv_ld_fillR_miss (M : Mem) {lo n a : Nat} (g : Nat → BitVec 8)
    (h : a + 8 ≤ lo ∨ lo + n ≤ a) : ldv .ld (fillR M lo n g) a = ldv .ld M a :=
  ldv_fillR_miss .ld M g h

theorem ldv_lw_fillR_miss (M : Mem) {lo n a : Nat} (g : Nat → BitVec 8)
    (h : a + 4 ≤ lo ∨ lo + n ≤ a) : ldv .lw (fillR M lo n g) a = ldv .lw M a :=
  ldv_fillR_miss .lw M g h

theorem ldv_lwu_fillR_miss (M : Mem) {lo n a : Nat} (g : Nat → BitVec 8)
    (h : a + 4 ≤ lo ∨ lo + n ≤ a) : ldv .lwu (fillR M lo n g) a = ldv .lwu M a :=
  ldv_fillR_miss .lwu M g h

theorem ldv_lh_fillR_miss (M : Mem) {lo n a : Nat} (g : Nat → BitVec 8)
    (h : a + 2 ≤ lo ∨ lo + n ≤ a) : ldv .lh (fillR M lo n g) a = ldv .lh M a :=
  ldv_fillR_miss .lh M g h

theorem ldv_lhu_fillR_miss (M : Mem) {lo n a : Nat} (g : Nat → BitVec 8)
    (h : a + 2 ≤ lo ∨ lo + n ≤ a) : ldv .lhu (fillR M lo n g) a = ldv .lhu M a :=
  ldv_fillR_miss .lhu M g h

theorem ldv_lbu_fillR_miss (M : Mem) {lo n a : Nat} (g : Nat → BitVec 8)
    (h : a + 1 ≤ lo ∨ lo + n ≤ a) : ldv .lbu (fillR M lo n g) a = ldv .lbu M a :=
  ldv_fillR_miss .lbu M g h

/-! ## Registers in normal form -/

theorem upd_upd_same (R : Nat → BitVec 64) (k : Nat) (v w : BitVec 64) :
    upd (upd R k v) k w = upd R k w := by
  funext r; unfold upd; by_cases h : r = k <;> simp [h]

/-- Updates at distinct registers commute; sorted by decreasing index. -/
theorem upd_upd_lt (R : Nat → BitVec 64) {k j : Nat} (v w : BitVec 64) (h : k < j) :
    upd (upd R k v) j w = upd (upd R j w) k v := by
  funext r; unfold upd
  by_cases h1 : r = j
  · subst h1; simp [show r ≠ k by omega]
  · by_cases h2 : r = k
    · subst h2; simp [h1]
    · simp [h1, h2]

theorem upd_upd_ne_same (R : Nat → BitVec 64) {k j : Nat} (u v w : BitVec 64) (h : j ≠ k) :
    upd (upd (upd R k u) j v) k w = upd (upd R j v) k w := by
  funext r; unfold upd
  by_cases h1 : r = k
  · subst h1; simp
  · by_cases h2 : r = j <;> simp [h1, h2]

section SWP

variable {live : Nat → Prop} {text : List (Nat × BitVec 8)} {rs : List Nat} {S : Nat → Prop}
  {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- **Forget a memory region**: running from `Mt` with the region at any
bytes runs from `Mt`. -/
theorem swp_forget_region {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} (lo n : Nat)
    (h : ∀ g, SWP live text rs S Q pc R (fillR Mt lo n g)) : SWP live text rs S Q pc R Mt := by
  refine swp_congr_mem (fun a _ => ?_) (h (imgM Mt))
  by_cases ha : lo ≤ a ∧ a < lo + n
  · exact imgM_fillR_in Mt _ ha
  · exact imgM_fillR_out Mt _ (by omega)

/-- **Forget a register's value**. -/
theorem swp_forget_reg {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} (k : Nat)
    (h : ∀ v, SWP live text rs S Q pc (upd R k v) Mt) : SWP live text rs S Q pc R Mt := by
  have := h (R k)
  rwa [upd_self_eq rfl] at this

end SWP

end VsaIris.Sym
