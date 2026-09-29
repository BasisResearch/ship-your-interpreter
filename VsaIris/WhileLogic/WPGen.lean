import Iris.ProofMode
import VsaIris.WhileLogic.Res

/-!
# The generic big-step weakest precondition

`wpR lo R Φ` is the total-correctness weakest precondition of a big-step
relation `R : St → St → α → Prop` (pre-state, post-state, result) in the
iris-lean BI `vProp = UPred Res`. It holds of a resource `x` when, for every
well-formed state `σ` with at least `lo` frames and every frame resource `rf`
with `abs σ = x • rf`, there is a derivation `R σ σ' a` to a well-formed,
frame-extending `σ'` and a resource `r'` with `abs σ' = r' • rf` satisfying
`Φ a`. Quantifying over `rf` makes every `wpR` frame-preserving; this is the
frame rule `wpR_frame`.

All language weakest preconditions (`WP.lean`) are instances of `wpR`, and
every proof rule is an instance of the generic lemmas below.
-/

namespace Vsa.While.Logic

open Iris OFE CMRA BI Vsa.While

/-- Total-correctness weakest precondition of a big-step relation. -/
def wpR {α : Type} (lo : Nat) (R : St → St → α → Prop) (Φ : α → vProp) : vProp where
  holds n x := ∀ (σ : St) (rf : Res), σ.store.WF → lo ≤ σ.store.frames.size →
    abs σ = x.val • rf →
    ∃ σ' a r', R σ σ' a ∧ σ'.store.WF ∧ σ.store.frames.size ≤ σ'.store.frames.size ∧
      ∃ h : abs σ' = r' • rf, (Φ a).holds n ⟨r', validN_of_rep h⟩
  mono := by
    intro n1 n2 x1 x2 H hinc hle σ rf hwf hlo hrep
    obtain ⟨z, hz⟩ := incN_iff.mp hinc
    have : abs σ = x1.val • (z • rf) := by rw [hrep, hz, assoc']
    obtain ⟨σ', a, r', hR, hwf', hsz, hrep', hΦ⟩ := H σ (z • rf) hwf hlo this
    refine ⟨σ', a, r' • z, hR, hwf', hsz, by rw [hrep', assoc'], ?_⟩
    exact (Φ a).mono hΦ (incN_op_left n2 r' z) hle

theorem op_left_comm (a b c : Res) : a • (b • c) = b • (a • c) := by
  rw [assoc', assoc', comm' (x := a)]

theorem entails_iff {P Q : vProp} :
    Iff (P ⊢ Q) (∀ n (x : Iris.ValidAt Res n), P.holds n x → Q.holds n x) := Iff.rfl

theorem sep_holds {P Q : vProp} {n : Nat} {x : Iris.ValidAt Res n} :
    Iff ((iprop(P ∗ Q) : vProp).holds n x)
      (∃ x1 x2 : Res, ∃ h : x.val = x1 • x2,
        P.holds n ⟨x1, validN_op_left (h ▸ x.property)⟩ ∧
        Q.holds n ⟨x2, validN_op_right (h ▸ x.property)⟩) :=
  ⟨fun ⟨x1, x2, h, hP, hQ⟩ => ⟨x1, x2, dist_eq h, hP, hQ⟩,
   fun ⟨x1, x2, h, hP, hQ⟩ => ⟨x1, x2, h ▸ .rfl, hP, hQ⟩⟩

theorem and_holds {P Q : vProp} {n : Nat} {x : Iris.ValidAt Res n} :
    Iff ((iprop(P ∧ Q) : vProp).holds n x) (P.holds n x ∧ Q.holds n x) := Iff.rfl

section generic

variable {α β : Type} {lo : Nat} {R : St → St → α → Prop}

theorem wpR_mono {Φ Ψ : α → vProp} (h : ∀ a, Φ a ⊢ Ψ a) : wpR lo R Φ ⊢ wpR lo R Ψ := by
  intro n x H σ rf hwf hlo hrep
  obtain ⟨σ', a, r', hR, hwf', hsz, hrep', hΦ⟩ := H σ rf hwf hlo hrep
  exact ⟨σ', a, r', hR, hwf', hsz, hrep', h a n _ hΦ⟩

/-- Relation inclusion (and a weaker frame-count precondition). -/
theorem wpR_weaken {lo' : Nat} {R' : St → St → α → Prop} {Φ : α → vProp}
    (hlo : lo ≤ lo') (h : ∀ σ σ' a, R σ σ' a → R' σ σ' a) : wpR lo R Φ ⊢ wpR lo' R' Φ := by
  intro n x H σ rf hwf hlo' hrep
  obtain ⟨σ', a, r', hR, hwf', hsz, hrep', hΦ⟩ := H σ rf hwf (Nat.le_trans hlo hlo') hrep
  exact ⟨σ', a, r', h _ _ _ hR, hwf', hsz, hrep', hΦ⟩

/-- **Frame rule** (generic form). -/
theorem wpR_frame {P : vProp} {Φ : α → vProp} :
    iprop(P ∗ wpR lo R Φ) ⊢ wpR lo R (fun a => iprop(P ∗ Φ a)) := by
  intro n x H σ rf hwf hlo hrep
  obtain ⟨x1, x2, hx, hP, hW⟩ := sep_holds.mp H
  have : abs σ = x2 • (x1 • rf) := by rw [hrep, hx, op_left_comm, ← assoc']
  obtain ⟨σ', a, r', hR, hwf', hsz, hrep', hΦ⟩ := hW σ (x1 • rf) hwf hlo this
  have hrep'' : abs σ' = (x1 • r') • rf := by rw [hrep', op_left_comm, assoc']
  refine ⟨σ', a, x1 • r', hR, hwf', hsz, hrep'', ?_⟩
  exact sep_holds.mpr ⟨x1, r', rfl, hP, hΦ⟩

/-- A relation that holds reflexively at result `a` returns immediately. -/
theorem wpR_ret {Φ : α → vProp} {a : α} (hR : ∀ σ, R σ σ a) : Φ a ⊢ wpR lo R Φ := by
  intro n x H σ rf hwf _ hrep
  exact ⟨σ, a, x.val, hR σ, hwf, Nat.le_refl _, hrep, H⟩

/-- Sequential composition of relations. -/
theorem wpR_bind {R2 : α → St → St → β → Prop} {R' : St → St → β → Prop} {lo' : Nat}
    {Φ : β → vProp} (hlo : lo' ≤ lo)
    (h : ∀ σ σ' σ'' a b, R σ σ' a → R2 a σ' σ'' b → R' σ σ'' b) :
    wpR lo R (fun a => wpR lo' (R2 a) Φ) ⊢ wpR lo R' Φ := by
  intro n x H σ rf hwf hlo0 hrep
  obtain ⟨σ', a, r', hR, hwf', hsz, hrep', hK⟩ := H σ rf hwf hlo0 hrep
  obtain ⟨σ'', b, r'', hR2, hwf'', hsz', hrep'', hΦ⟩ :=
    hK σ' rf hwf' (by omega) hrep'
  exact ⟨σ'', b, r'', h _ _ _ _ _ hR hR2, hwf'', Nat.le_trans hsz hsz', hrep'', hΦ⟩

/-- Sequential composition with a continuation that entails a `wpR`. -/
theorem wpR_bind' {R2 : α → St → St → β → Prop} {R' : St → St → β → Prop} {lo' : Nat}
    {K : α → vProp} {Φ : β → vProp} (hlo : lo' ≤ lo)
    (hK : ∀ a, K a ⊢ wpR lo' (R2 a) Φ)
    (h : ∀ σ σ' σ'' a b, R σ σ' a → R2 a σ' σ'' b → R' σ σ'' b) :
    wpR lo R K ⊢ wpR lo R' Φ :=
  (wpR_mono hK).trans (wpR_bind hlo h)

/-- A primitive step owning `m`: from any state `abs σ = m • w` the step
reaches `abs σ' = m' • w` with `Q a` true of `m'`. The rest of the resource
(`Rest`) is framed around the step. -/
theorem wpR_prim {m : Res} {Q : α → vProp} {Rest : vProp} {Φ : α → vProp}
    (hstep : ∀ σ w, σ.store.WF → lo ≤ σ.store.frames.size → abs σ = m • w →
      ∃ σ' a m', R σ σ' a ∧ σ'.store.WF ∧ σ.store.frames.size ≤ σ'.store.frames.size ∧
        abs σ' = m' • w ∧ ∀ n (h : ✓{n} m'), (Q a).holds n ⟨m', h⟩)
    (hΦ : ∀ a, iprop(Q a ∗ Rest) ⊢ Φ a) :
    iprop(UPred.ownM m ∗ Rest) ⊢ wpR lo R Φ := by
  intro n x H σ rf hwf hlo hrep
  obtain ⟨x1, x2, hx, hm, hRest⟩ := sep_holds.mp H
  obtain ⟨z, hz⟩ := ownM_holds.mp hm
  have hz : x1 = m • z := hz
  have : abs σ = m • (z • (x2 • rf)) := by
    rw [hrep, hx, hz]; simp only [← assoc']
  obtain ⟨σ', a, m', hR, hwf', hsz, hrep', hQ⟩ := hstep σ _ hwf hlo this
  have hrep'' : abs σ' = ((m' • z) • x2) • rf := by rw [hrep']; simp only [← assoc']
  refine ⟨σ', a, (m' • z) • x2, hR, hwf', hsz, hrep'', ?_⟩
  refine hΦ a n _ (sep_holds.mpr ⟨m' • z, x2, rfl, ?_, hRest⟩)
  exact (Q a).mono (hQ n (validN_op_left (validN_op_left (validN_of_rep hrep''))))
    (incN_op_left n m' z) (Nat.le_refl n)

/-- A primitive observation that reads the owned `m` without changing the
state. -/
theorem wpR_read {m : Res} {Φ : α → vProp} {a : α}
    (hread : ∀ σ w, σ.store.WF → lo ≤ σ.store.frames.size → abs σ = m • w → R σ σ a) :
    iprop(UPred.ownM m ∧ Φ a) ⊢ wpR lo R Φ := by
  intro n x H σ rf hwf hlo hrep
  obtain ⟨hm, hΦ⟩ := and_holds.mp H
  obtain ⟨z, hz⟩ := ownM_holds.mp hm
  have : abs σ = m • (z • rf) := by rw [hrep, hz, assoc']
  exact ⟨σ, a, x.val, hread σ _ hwf hlo this, hwf, Nat.le_refl _, hrep, hΦ⟩

/-- Post-composing the result with `f`. -/
theorem wpR_map {f : α → β} {Φ : β → vProp} :
    wpR lo R (fun a => Φ (f a)) ⊢ wpR lo (fun σ σ' b => ∃ a, R σ σ' a ∧ b = f a) Φ := by
  intro n x H σ rf hwf hlo hrep
  obtain ⟨σ', a, r', hR, hwf', hsz, hrep', hΦ⟩ := H σ rf hwf hlo hrep
  exact ⟨σ', f a, r', ⟨a, hR, rfl⟩, hwf', hsz, hrep', hΦ⟩

/-- `False` entails every `wpR`. -/
theorem wpR_false {Φ : α → vProp} : (iprop(False) : vProp) ⊢ wpR lo R Φ :=
  fun _ _ h => h.elim

end generic

end Vsa.While.Logic
