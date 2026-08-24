import Vsa.Sim.Pmp

/-! # Small state-normalization lemmas for `init_good` -/

open LeanRV64DExecutable Sail ConcurrencyInterfaceV1

namespace Vsa.Sim

/-- `trivialChoiceSource` returns its canonical value without changing state. -/
theorem choose_trivial_char {ue : Type} (p : Sail.Primitive)
    (σ : SequentialState RegisterType trivialChoiceSource) :
    (PreSail.choose (ue := ue) p) σ =
      EStateM.Result.ok (ε := Sail.Error ue)
        (trivialChoiceSource.choose p ()) σ := by
  cases σ with
  | mk regs choiceState mem tags cycleCount sailOutput =>
    cases choiceState
    rfl

/-- Re-inserting the value already stored at a dependent register key is identity. -/
theorem regs_insert_eq_self (m : Std.ExtDHashMap Register RegisterType)
    (r : Register) (v : RegisterType r) (h : m.get? r = some v) :
    m.insert r v = m := by
  apply Std.ExtDHashMap.ext_get?
  intro k
  rw [Std.ExtDHashMap.get?_insert]
  by_cases hrk : (r == k) = true
  · simp only [hrk, dif_pos]
    have herk : r = k := beq_iff_eq.mp hrk
    subst k
    simpa using h.symm
  · simp only [hrk, dif_neg, Bool.not_eq_true]

/-- Constant-state `IntRange.forIn'` loop for plain `EStateM`. -/
theorem forIn'_loop_const_estate {ε σ' β : Type}
    (range : IntRange)
    (f : (i : Int) → i ∈ range → β → EStateM ε σ' (ForInStep β))
    (b : β) (i : Int) (hs : (i - range.start) % range.step = 0)
    (σ : σ')
    (hbody : ∀ (j : Int) (hj : j ∈ range) (c : β),
      f j hj c σ = .ok (.yield c) σ) :
    IntRange.forIn'.loop range f b i hs σ = .ok b σ := by
  induction b, i, hs using IntRange.forIn'.loop.induct range with
  | case1 b i hs hmem ih =>
    rw [IntRange.forIn'.loop.eq_1]
    simp only [hmem, dif_pos, bind, Bind.bind, EStateM.bind]
    rw [show f i hmem b σ = EStateM.Result.ok (ForInStep.yield b) σ
      from hbody i hmem b]
    exact ih b
  | case2 b i hs hmem =>
    rw [IntRange.forIn'.loop.eq_1]
    simp only [hmem, dif_neg, not_false_iff]
    rfl

/-- Wrapper started at `range.start`. -/
theorem forIn'_const_estate {ε σ' β : Type}
    (range : IntRange) (b : β)
    (f : (i : Int) → i ∈ range → β → EStateM ε σ' (ForInStep β))
    (σ : σ')
    (hbody : ∀ (j : Int) (hj : j ∈ range) (c : β),
      f j hj c σ = .ok (.yield c) σ) :
    IntRange.forIn' range b f σ = .ok b σ :=
  forIn'_loop_const_estate range f b range.start (by simp) σ hbody

end Vsa.Sim
