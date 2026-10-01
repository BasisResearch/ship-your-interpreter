import Vsa.Compiler.R6Attr

namespace Vsa.Compiler

theorem seg_app_iff {code : List Ins} {pos : Nat} {a b : List Ins} :
    Seg code pos (a ++ b) ↔ Seg code pos a ∧ Seg code (pos + a.length) b := by
  refine ⟨Seg.append, fun ⟨h1, h2⟩ j hj => ?_⟩
  rcases Nat.lt_or_ge j a.length with h | h
  · rw [h1 j h, List.getElem?_append_left h]
  · have := h2 (j - a.length) (by simp at hj; omega)
    rw [Nat.add_assoc, Nat.add_sub_cancel' h] at this
    rw [this, List.getElem?_append_right h]

theorem segP_app {code : List Ins} {pos : Nat} {a b : List Ins} :
    (Seg code pos (a ++ b) ∧ PosOK (pos + (a ++ b).length)) ↔
      (Seg code pos a ∧ PosOK (pos + a.length)) ∧
        (Seg code (pos + a.length) b ∧ PosOK (pos + a.length + b.length)) := by
  rw [seg_app_iff, List.length_append, ← Nat.add_assoc]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h1, by unfold PosOK at *; omega⟩, h2, h3⟩,
    fun ⟨⟨h1, _⟩, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

end Vsa.Compiler
