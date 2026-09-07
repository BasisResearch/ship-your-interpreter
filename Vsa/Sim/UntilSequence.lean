import Vsa.Sim.RamReadPolicy

namespace Vsa.Sim

/-- A finite sequence of successful, state-preserving loop iterations.
The condition stops exactly at the final indexed value. -/
theorem untilFuelM_sequence {α ε error state : Type}
    (σ : state) (n : Nat) (x : Nat → α)
    (body : α → ExceptT ε (EStateM error state) α)
    (cond : α → ExceptT ε (EStateM error state) Bool)
    (hbody : ∀ i, i < n → (body (x i)).run σ = .ok (.ok (x (i + 1))) σ)
    (hcond : ∀ i, 0 < i → i ≤ n → (cond (x i)).run σ = .ok (.ok (i == n)) σ) :
    (untilFuelM n cond (x 0) body).run σ = .ok (.ok (x n)) σ := by
  have go : ∀ fuel i, i + fuel = n →
      (untilFuelM.go cond body (x i) fuel).run σ = .ok (.ok (x n)) σ := by
    intro fuel
    induction fuel with
    | zero =>
      intro i he
      have hi : i = n := by omega
      subst i
      rfl
    | succ fuel ih =>
      intro i he
      have hb := hbody i (by omega)
      have hc := hcond (i + 1) (by omega) (by omega)
      simp only [ExceptT.run] at hb hc
      simp only [untilFuelM.go, ExceptT.run, bind, ExceptT.bind, ExceptT.mk,
        ExceptT.bindCont, EStateM.bind, hb, hc]
      by_cases hn : i + 1 = n
      · simp [hn, pure, ExceptT.pure, ExceptT.mk, EStateM.pure]
      · have hf := ih (i + 1) (by omega)
        simpa [hn] using hf
  exact go n 0 (by omega)

#print axioms untilFuelM_sequence
end Vsa.Sim
