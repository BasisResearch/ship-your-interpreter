import Vsa.Sim.TermAssembly

/-!
# `SmtReplaySupport` — reusable witness lemmas for SMT countermodel replays

Support lemmas for the `smt_check.py` `--refute` replay probes on the
agree-window falsity family (the ∀-mcall / prefix-agree class).  A refutation
witness populates a finite prefix map and demonstrates that an adversary map,
agreeing with it OFF a window, can still differ INSIDE the window (where the
agree-hypothesis says nothing) — the disease the historical amendments cured.

`pop ks v` = insert value `v` at every key in `ks`; `pop_mem`/`pop_not_mem`
give its exact `getElem?` behaviour.  Axiom-clean (⊆ {propext, Classical.choice,
Quot.sound}); analysis-only support, NOT wired into `Vsa.lean`.
-/

open Vsa Vsa.Sim Vsa.MemRepr
open Std (ExtHashMap)

namespace Vsa.SmtReplay

/-- Two commuting single-value inserts at distinct keys. -/
theorem ins_comm (m : Mem) (a b : Nat) (v : BitVec 8) (hab : a ≠ b) :
    (m.insert a v).insert b v = (m.insert b v).insert a v := by
  apply Std.ExtHashMap.ext_getElem?
  intro q
  by_cases hqa : q = a <;> by_cases hqb : q = b
  · exact absurd (hqa ▸ hqb ▸ rfl : a = b) hab
  · subst hqa
    rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert_self, Std.ExtHashMap.getElem?_insert_self]
  · subst hqb
    rw [Std.ExtHashMap.getElem?_insert_self, Std.ExtHashMap.getElem?_insert,
        if_neg (by simp only [beq_iff_eq]; omega), Std.ExtHashMap.getElem?_insert_self]
  · rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
        Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

/-- Insert `v` at every key in `ks`, starting from the empty map. -/
def pop (ks : List Nat) (v : BitVec 8) : Mem :=
  ks.foldl (fun m k => m.insert k v) ∅

/-- Every key present in `ks` looks up to `some v`. -/
theorem pop_mem (v : BitVec 8) : ∀ (a : Nat) (ks : List Nat),
    a ∈ ks → (pop ks v)[a]? = some v := by
  suffices H : ∀ (ks : List Nat) (m0 : Mem) (a : Nat),
      a ∈ ks → (ks.foldl (fun m k => m.insert k v) m0)[a]? = some v by
    intro a ks ha; exact H ks ∅ a ha
  intro ks
  induction ks with
  | nil => intro m0 a ha; exact absurd ha (by simp)
  | cons k ks ih =>
    intro m0 a ha
    simp only [List.foldl_cons]
    by_cases hlater : a ∈ ks
    · exact ih (m0.insert k v) a hlater
    · have hak : a = k := by
        rcases List.mem_cons.mp ha with h | h
        · exact h
        · exact absurd h hlater
      subst hak; clear ha ih
      induction ks generalizing m0 with
      | nil => simp only [List.foldl_nil]; exact Std.ExtHashMap.getElem?_insert_self
      | cons j js ih2 =>
        simp only [List.foldl_cons]
        have hja : ¬ a ∈ (j :: js) := hlater
        have hjne : ¬ (a = j) := fun h => hja (by simp [h])
        have hjs : ¬ a ∈ js := fun h => hja (by simp [h])
        rw [ins_comm m0 a j v hjne]; exact ih2 (m0.insert j v) hjs

/-- Every key absent from `ks` looks up to `none`. -/
theorem pop_not_mem (v : BitVec 8) : ∀ (a : Nat) (ks : List Nat),
    a ∉ ks → (pop ks v)[a]? = none := by
  suffices H : ∀ (ks : List Nat) (m0 : Mem) (a : Nat),
      a ∉ ks → m0[a]? = none → (ks.foldl (fun m k => m.insert k v) m0)[a]? = none by
    intro a ks ha; exact H ks ∅ a ha (by simp only [Std.ExtHashMap.getElem?_empty])
  intro ks
  induction ks with
  | nil => intro m0 a _ hm; simpa using hm
  | cons k ks ih =>
    intro m0 a ha hm
    simp only [List.foldl_cons]
    have hks : a ∉ ks := fun h => ha (by simp [h])
    have hak : a ≠ k := fun h => ha (by simp [h])
    apply ih (m0.insert k v) a hks
    rw [getElem?_insert_out m0 k v a hak, hm]

end Vsa.SmtReplay
