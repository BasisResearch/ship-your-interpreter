import Vsa.Elf

/-!
# Fuel monotonicity of the machine runner

`runSteps` checks `htif_done` before consuming fuel and returns immediately
once the machine has halted, so a halting result is stable under adding
fuel. This makes the refinement statement fuel-independent: one certified
run at a sufficient fuel determines the outcome at every fuel.
-/

namespace Vsa

open Sail ConcurrencyInterfaceV1 LeanRV64DExecutable

theorem runSteps_mono {f g : Nat} (hfg : f ≤ g) :
    ∀ {i u : Nat} {σ σ' : SequentialState RegisterType trivialChoiceSource}
      {e : Nat} {n : Nat},
      (runSteps f i u).run σ = .ok (some e, n) σ' →
      (runSteps g i u).run σ = .ok (some e, n) σ' := by
  induction f generalizing g with
  | zero =>
    intro i u σ σ' e n h
    simp [runSteps, pure, EStateM.pure, EStateM.run] at h
  | succ f ih =>
    intro i u σ σ' e n h
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    have hfg' : f ≤ g' := by omega
    rw [runSteps] at h ⊢
    simp only [bind, EStateM.bind, EStateM.run] at h ⊢
    -- One shared, fuel-independent prefix: the single `stepOnce` call.
    split at h
    · -- stepOnce succeeded; halt and continue branches
      split at h
      · exact h
      · exact ih hfg' h
    · -- stepOnce errored: h is a dead branch
      simp at h

/-- A halting `runElf` result is stable (bit for bit) under adding fuel. -/
theorem runElf_mono {f g : Nat} (hfg : f ≤ g) (elf : ELF64File)
    {r : RunResult} {e : Nat} (hr : r.exitCode = some e)
    (h : runElf elf f = .ok r) :
    runElf elf g = .ok r := by
  unfold runElf at h ⊢
  simp only [bind, EStateM.bind, EStateM.run] at h ⊢
  cases hS : setupElf elf (initState elf) with
  | error err s => rw [hS] at h; simp at h
  | ok a s =>
    rw [hS] at h
    dsimp only at h ⊢
    cases hR : runSteps f 0 0 s with
    | error err s' => rw [hR] at h; simp at h
    | ok res s' =>
      obtain ⟨oexit, used⟩ := res
      rw [hR] at h
      dsimp only at h
      cases oexit with
      | none =>
        injection h with h
        subst h
        simp at hr
      | some e' =>
        have hg := runSteps_mono hfg hR
        simp only [EStateM.run] at hg
        rw [hg]
        exact h

/-- Halting is stable under adding fuel, lifted to the whole ELF runner.
(The proof generalizes over the parsed-ELF value so that no tactic ever
tries to reduce `whileElf?`, a closed computation over the 138 KB binary.) -/
theorem elfHalts_mono {f g : Nat} (hfg : f ≤ g) {r : RunResult} {e : Nat}
    (hr : r.exitCode = some e)
    (h : runWhileElf f = .ok r) :
    runWhileElf g = .ok r := by
  have key : ∀ o : Except String ELF64File,
      o.bind (fun elf => runElf elf f) = .ok r →
      o.bind (fun elf => runElf elf g) = .ok r := by
    intro o ho
    cases o with
    | error err => simp [Except.bind] at ho
    | ok elf =>
      simp only [Except.bind] at ho ⊢
      exact runElf_mono hfg elf hr ho
  exact key whileElf? h

end Vsa
