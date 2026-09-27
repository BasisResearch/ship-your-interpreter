import Vsa.Densify.Resp

namespace Vsa.Densify

open Vsa.Machine
open Sail ConcurrencyInterfaceV1

structure CEqv (c c' : Config) : Prop where
  σ : SEqv c.σ c'.σ
  tick : c.tick = c'.tick
  steps : c.steps = c'.steps

theorem CEqv.symm {c c'} (h : CEqv c c') : CEqv c' c := ⟨h.σ.symm, h.tick.symm, h.steps.symm⟩

theorem output_of_seqv {σ σ' : MState} (h : SEqv σ σ') : output σ = output σ' := by
  unfold output; rw [h.out]

section Sim

variable (hres : ∀ i u, Resp (Vsa.stepOnce i u))
include hres

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

theorem halts_iff_of_ceqv {c c' : Config} (h : CEqv c c') (out : String) (e : Nat) :
    Halts c out e ↔ Halts c' out e :=
  ⟨halts_of_ceqv hres h, halts_of_ceqv hres h.symm⟩

theorem diverges_iff_of_ceqv {c c' : Config} (h : CEqv c c') : Diverges c ↔ Diverges c' :=
  ⟨diverges_of_ceqv hres h, diverges_of_ceqv hres h.symm⟩

end Sim

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

def ramBase : Nat := 0x80000000
def ramSize : Nat := 0x08000000

theorem fillZeroMem_exists (m : Std.ExtHashMap Nat (BitVec 8)) :
    ∃ m' : Std.ExtHashMap Nat (BitVec 8), ∀ a,
      m'[a]? = if ramBase ≤ a ∧ a < ramBase + ramSize then some ((m[a]?).getD 0) else m[a]? :=
  ⟨fillMem m ramBase ramSize, fun a => fillMem_get m ramBase ramSize a⟩

noncomputable def fillZeroMem (m : Std.ExtHashMap Nat (BitVec 8)) : Std.ExtHashMap Nat (BitVec 8) :=
  Classical.choose (fillZeroMem_exists m)

theorem fillZeroMem_get (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) :
    (fillZeroMem m)[a]? = if ramBase ≤ a ∧ a < ramBase + ramSize then some ((m[a]?).getD 0) else m[a]? :=
  Classical.choose_spec (fillZeroMem_exists m) a

theorem memEqv_fillZeroMem (m : Std.ExtHashMap Nat (BitVec 8)) : MemEqv m (fillZeroMem m) := by
  intro a
  simp only [Std.ExtHashMap.get?_eq_getElem?, fillZeroMem_get]
  split <;> rfl

theorem fillZeroMem_some {m : Std.ExtHashMap Nat (BitVec 8)} {a : Nat} {b : BitVec 8}
    (h : m[a]? = some b) : (fillZeroMem m)[a]? = some b := by
  rw [fillZeroMem_get]; split <;> simp [h]

theorem fillZeroMem_ram (m : Std.ExtHashMap Nat (BitVec 8)) {a : Nat} (hlo : ramBase ≤ a)
    (hhi : a < ramBase + ramSize) : (fillZeroMem m)[a]? = some ((m[a]?).getD 0) := by
  rw [fillZeroMem_get, if_pos ⟨hlo, hhi⟩]

noncomputable def fillZero (c : Config) : Config :=
  ⟨{ c.σ with mem := fillZeroMem c.σ.mem }, c.tick, c.steps⟩

theorem ceqv_fillZero (c : Config) : CEqv c (fillZero c) :=
  ⟨⟨rfl, rfl, memEqv_fillZeroMem _, rfl, rfl⟩, rfl, rfl⟩

end Vsa.Densify
