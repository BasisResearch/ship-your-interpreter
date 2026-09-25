import Vsa.Densify.Resp

/-!
# From a respectful `stepOnce` to `Halts`/`Diverges` invariance

Given `Resp (stepOnce i u)` (supplied by `Vsa.Densify.GenC.stepOnce_resp`),
zero-equivalent configurations (`CEqv`: same counters, `SEqv` states) step in
lockstep (`Step`, `Halted`), so they have the same halting behaviour and the
same divergence. `fillZero` densifies RAM by inserting the total read of
every absent RAM byte; it is zero-equivalent to the original and every RAM
byte of its image is present.
-/

namespace Vsa.Densify

open Vsa.Machine
open Sail ConcurrencyInterfaceV1

/-- Zero-equivalent configurations. -/
structure CEqv (c c' : Config) : Prop where
  σ : SEqv c.σ c'.σ
  tick : c.tick = c'.tick
  steps : c.steps = c'.steps

theorem CEqv.refl (c : Config) : CEqv c c := ⟨SEqv.refl _, rfl, rfl⟩
theorem CEqv.symm {c c'} (h : CEqv c c') : CEqv c' c := ⟨h.σ.symm, h.tick.symm, h.steps.symm⟩

theorem output_of_seqv {σ σ' : MState} (h : SEqv σ σ') : output σ = output σ' := by
  unfold output; rw [h.out]

section Sim

variable (hres : ∀ i u, Resp (Vsa.stepOnce i u))
include hres

/-- Lockstep: a step of one configuration is matched by the other. -/
theorem step_sim {c c₁ c' : Config} (h : CEqv c c') (hs : Step c c₁) :
    ∃ c₁', Step c' c₁' ∧ CEqv c₁ c₁' := by
  obtain ⟨σ, i, u⟩ := c
  obtain ⟨σ', i', u'⟩ := c'
  obtain ⟨hσ, hi, hu⟩ := h
  cases hi; cases hu
  cases hs with
  | @mk _ σ₁ _ i₁ _ u₁ e =>
    have hr := (hres i u).run σ σ' hσ
    simp only [EStateM.run] at e
    rw [e] at hr
    revert hr
    cases hx : (Vsa.stepOnce i u) σ' <;> intro hr <;> simp only [REqv] at hr
    obtain ⟨rfl, hs⟩ := hr
    exact ⟨⟨_, i₁, u₁⟩, .mk hx, ⟨hs, rfl, rfl⟩⟩

theorem halted_sim {c c' : Config} {e : Nat} {σf : MState} (h : CEqv c c') (hh : Halted c e σf) :
    ∃ σf', Halted c' e σf' ∧ SEqv σf σf' := by
  obtain ⟨σ, i, u⟩ := c
  obtain ⟨σ', i', u'⟩ := c'
  obtain ⟨hσ, hi, hu⟩ := h
  cases hi; cases hu
  cases hh with
  | @mk _ σf _ _ _ n hx0 =>
    have hr := (hres i u).run σ σ' hσ
    simp only [EStateM.run] at hx0
    rw [hx0] at hr
    revert hr
    cases hx : (Vsa.stepOnce i u) σ' <;> intro hr <;> simp only [REqv] at hr
    obtain ⟨rfl, hs⟩ := hr
    exact ⟨_, .mk hx, hs⟩

theorem steps_sim {c c₁ c' : Config} (h : CEqv c c') (hs : Steps c c₁) :
    ∃ c₁', Steps c' c₁' ∧ CEqv c₁ c₁' := by
  induction hs generalizing c' with
  | refl c => exact ⟨c', .refl c', h⟩
  | head s _ ih =>
    obtain ⟨b', hb', hb⟩ := step_sim hres h s
    obtain ⟨c₁', hc', hc⟩ := ih hb
    exact ⟨c₁', .head hb' hc', hc⟩

theorem stepsN_sim {n : Nat} {c c₁ c' : Config} (h : CEqv c c') (hs : StepsN n c c₁) :
    ∃ c₁', StepsN n c' c₁' ∧ CEqv c₁ c₁' := by
  induction hs generalizing c' with
  | zero c => exact ⟨c', .zero c', h⟩
  | succ s _ ih =>
    obtain ⟨b', hb', hb⟩ := step_sim hres h s
    obtain ⟨c₁', hc', hc⟩ := ih hb
    exact ⟨c₁', .succ hb' hc', hc⟩

theorem halts_of_ceqv {c c' : Config} (h : CEqv c c') {out : String} {e : Nat}
    (hh : Halts c out e) : Halts c' out e := by
  obtain ⟨c₁, σf, hs, hh, ho⟩ := hh
  obtain ⟨c₁', hs', hc⟩ := steps_sim hres h hs
  obtain ⟨σf', hh', hf⟩ := halted_sim hres hc hh
  exact ⟨c₁', σf', hs', hh', (output_of_seqv hf).symm.trans ho⟩

theorem diverges_of_ceqv {c c' : Config} (h : CEqv c c') (hd : Diverges c) : Diverges c' := by
  intro n
  obtain ⟨c₁, hn⟩ := hd n
  obtain ⟨c₁', hn', _⟩ := stepsN_sim hres h hn
  exact ⟨c₁', hn'⟩

/-- **Halting is invariant under zero-equivalence.** -/
theorem halts_iff_of_ceqv {c c' : Config} (h : CEqv c c') (out : String) (e : Nat) :
    Halts c out e ↔ Halts c' out e :=
  ⟨halts_of_ceqv hres h, halts_of_ceqv hres h.symm⟩

/-- **Divergence is invariant under zero-equivalence.** -/
theorem diverges_iff_of_ceqv {c c' : Config} (h : CEqv c c') : Diverges c ↔ Diverges c' :=
  ⟨diverges_of_ceqv hres h, diverges_of_ceqv hres h.symm⟩

end Sim

/-! ## `fillZero` -/

/-- Insert the total read of every byte of `[base, base + n)`. -/
def fillMem (m : Std.ExtHashMap Nat (BitVec 8)) (base : Nat) : Nat → Std.ExtHashMap Nat (BitVec 8)
  | 0 => m
  | n + 1 => (fillMem m base n).insert (base + n) ((m[base + n]?).getD 0)

theorem fillMem_get (m : Std.ExtHashMap Nat (BitVec 8)) (base : Nat) :
    ∀ (n a : Nat), (fillMem m base n)[a]? =
      if base ≤ a ∧ a < base + n then some ((m[a]?).getD 0) else m[a]?
  | 0, a => by simp only [fillMem]; rw [if_neg (by omega)]
  | n + 1, a => by
    simp only [fillMem, Std.ExtHashMap.getElem?_insert, fillMem_get m base n]
    by_cases h : base + n = a
    · subst h; simp
    · have h' : (base + n == a) = false := by simp [h]
      simp only [h', Bool.false_eq_true, if_false]
      by_cases h1 : base ≤ a ∧ a < base + n
      · rw [if_pos h1, if_pos ⟨h1.1, by omega⟩]
      · rw [if_neg h1, if_neg (fun h2 => h1 ⟨h2.1, by omega⟩)]

/-- RAM: `[0x80000000, 0x88000000)`, as the loader and the Sail platform lay it out. -/
def ramBase : Nat := 0x80000000
def ramSize : Nat := 0x08000000

theorem fillZeroMem_exists (m : Std.ExtHashMap Nat (BitVec 8)) :
    ∃ m' : Std.ExtHashMap Nat (BitVec 8), ∀ a,
      m'[a]? = if ramBase ≤ a ∧ a < ramBase + ramSize then some ((m[a]?).getD 0) else m[a]? :=
  ⟨fillMem m ramBase ramSize, fun a => fillMem_get m ramBase ramSize a⟩

/-- The fill-with-zero memory: every absent RAM byte becomes `some 0`; every
other byte is unchanged. Chosen noncomputably from `fillZeroMem_exists`, so
that no elaboration or kernel check can ever try to compute the 2^27-entry
fill; `fillZeroMem_get` is its only interface. -/
noncomputable def fillZeroMem (m : Std.ExtHashMap Nat (BitVec 8)) : Std.ExtHashMap Nat (BitVec 8) :=
  Classical.choose (fillZeroMem_exists m)

theorem fillZeroMem_get (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) :
    (fillZeroMem m)[a]? = if ramBase ≤ a ∧ a < ramBase + ramSize then some ((m[a]?).getD 0) else m[a]? :=
  Classical.choose_spec (fillZeroMem_exists m) a

/-- The total read is unchanged. -/
theorem memEqv_fillZeroMem (m : Std.ExtHashMap Nat (BitVec 8)) : MemEqv m (fillZeroMem m) := by
  intro a
  simp only [Std.ExtHashMap.get?_eq_getElem?, fillZeroMem_get]
  split <;> rfl

/-- Present bytes keep their values. -/
theorem fillZeroMem_some {m : Std.ExtHashMap Nat (BitVec 8)} {a : Nat} {b : BitVec 8}
    (h : m[a]? = some b) : (fillZeroMem m)[a]? = some b := by
  rw [fillZeroMem_get]; split <;> simp [h]

/-- Every RAM byte is present. -/
theorem fillZeroMem_ram (m : Std.ExtHashMap Nat (BitVec 8)) {a : Nat} (hlo : ramBase ≤ a)
    (hhi : a < ramBase + ramSize) : (fillZeroMem m)[a]? = some ((m[a]?).getD 0) := by
  rw [fillZeroMem_get, if_pos ⟨hlo, hhi⟩]

/-- A memory whose RAM bytes are all present is its own fill. -/
theorem fillZeroMem_eq_of_dense {m : Std.ExtHashMap Nat (BitVec 8)}
    (h : ∀ a, ramBase ≤ a → a < ramBase + ramSize → (m[a]?).isSome) : fillZeroMem m = m := by
  apply Std.ExtHashMap.ext_getElem?
  intro a
  rw [fillZeroMem_get]
  split
  · next ha =>
    have := h a ha.1 ha.2
    cases hm : m[a]? with
    | none => rw [hm] at this; cases this
    | some b => rfl
  · rfl

/-- The fill-with-zero configuration. -/
noncomputable def fillZero (c : Config) : Config :=
  ⟨{ c.σ with mem := fillZeroMem c.σ.mem }, c.tick, c.steps⟩

theorem ceqv_fillZero (c : Config) : CEqv c (fillZero c) :=
  ⟨⟨rfl, rfl, memEqv_fillZeroMem _, rfl, rfl⟩, rfl, rfl⟩

theorem fillZero_eq_of_dense {c : Config}
    (h : ∀ a, ramBase ≤ a → a < ramBase + ramSize → (c.σ.mem[a]?).isSome) : fillZero c = c := by
  obtain ⟨σ, i, u⟩ := c
  show (⟨{ σ with mem := fillZeroMem σ.mem }, i, u⟩ : Config) = ⟨σ, i, u⟩
  rw [fillZeroMem_eq_of_dense h]

end Vsa.Densify
