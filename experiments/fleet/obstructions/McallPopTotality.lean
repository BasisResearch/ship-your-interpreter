import Vsa.Sim.MemRegion

/-!
# Wave 47h — the `hMcallPop` totality oracle is UNSUPPLIABLE (Law 4)

The recursive eval-arm residuals (`NegResid`/`NotResid`/the logical four,
`rows/TermRouting.lean`; the B3/B4 cells carry the same class) each demand

  `∀ mcall : Mem, (∀ a, ¬(SL.lo ≤ a ∧ a < sp) → mcall[a]? = m0[a]?) →
     ∀ a : Nat, ∃ b, mcall[a]? = some b`

— TOTAL population of every memory agreeing with `m0` off the stack window
(the `blockC_*` dead-byte `ld`s of the sub-`Value` padding motivated it).

Machine-checked below: this is unsuppliable by ANY entry amendment, because it
is FALSE for every memory whatsoever — `Mem = Std.ExtHashMap Nat (BitVec 8)`
is a finite map, and no finite map is total on `Nat` (pigeonhole via
`size_erase`).  Instantiating the oracle at `mcall := m0` (agreement is `rfl`)
already demands `m0` itself be total, so even the entry-conditioned form is
uninhabited over every constructible entry memory.

Audit row X1 (`experiments/entry-needs-audit.md`).  Honest fix: restate the
residual with a presence hypothesis on the actual dead-byte read footprint
(`[subsret+4,+8) ∪ [subsret+16,+24)`) — suppliable by the consumer's concrete
`writeMap8` chain via `MemExtends` — NOT an entry field.

Verified with `lake env lean` only; NOT part of the build (obstruction
evidence).  NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open Vsa.MemRepr

namespace Vsa.Sim.McallPopTotality

/-- Pigeonhole: any `m : Mem` misses some address `≤ m.size` bounded by `n`. -/
theorem exists_none_le : ∀ (n : Nat) (m : Mem), m.size ≤ n →
    ∃ a : Nat, a ≤ n ∧ m[a]? = none := by
  intro n
  induction n with
  | zero =>
    intro m h
    have hempty : m = ∅ :=
      Std.ExtHashMap.eq_empty_iff_size_eq_zero.mpr (Nat.le_zero.mp h)
    exact ⟨0, Nat.le_refl 0, by rw [hempty]; exact Std.ExtHashMap.getElem?_empty⟩
  | succ n ih =>
    intro m h
    cases Classical.em ((n + 1) ∈ m) with
    | inr hnm => exact ⟨n + 1, Nat.le_refl _, Std.ExtHashMap.getElem?_eq_none hnm⟩
    | inl hm =>
      have hpos : 1 ≤ m.size := by
        rcases Nat.eq_zero_or_pos m.size with h0 | h1
        · exfalso
          have hempty : m = ∅ := Std.ExtHashMap.eq_empty_iff_size_eq_zero.mpr h0
          rw [hempty] at hm
          exact Std.ExtHashMap.not_mem_empty hm
        · exact h1
      have hsz : (m.erase (n + 1)).size ≤ n := by
        rw [Std.ExtHashMap.size_erase]
        simp only [hm, if_true]
        omega
      obtain ⟨a, ha, hnone⟩ := ih (m.erase (n + 1)) hsz
      refine ⟨a, Nat.le_succ_of_le ha, ?_⟩
      rw [Std.ExtHashMap.getElem?_erase] at hnone
      by_cases hba : ((n + 1 : Nat) == a) = true
      · exact absurd (eq_of_beq hba) (by omega)
      · rw [if_neg hba] at hnone
        exact hnone

/-- **No memory is total on `Nat`.** -/
theorem no_total_mem (m : Mem) : ¬ ∀ a : Nat, ∃ b, m[a]? = some b := by
  intro h
  obtain ⟨a, _, hnone⟩ := exists_none_le m.size m (Nat.le_refl _)
  obtain ⟨b, hb⟩ := h a
  rw [hb] at hnone
  cases hnone

/-- **The `hMcallPop` oracle shape is uninhabited for EVERY `m0`** (not just
`m0 = ∅`): instantiate the ∀-quantified `mcall` at `m0` itself. -/
theorem mcallPop_shape_unsuppliable (SLlo spN : Nat) (m0 : Mem) :
    ¬ (∀ mcall : Mem,
        (∀ a : Nat, ¬ (SLlo ≤ a ∧ a < spN) → mcall[a]? = m0[a]?) →
        ∀ a : Nat, ∃ b, mcall[a]? = some b) := by
  intro h
  exact no_total_mem m0 (h m0 (fun _ _ => rfl))

end Vsa.Sim.McallPopTotality

#print axioms Vsa.Sim.McallPopTotality.no_total_mem
#print axioms Vsa.Sim.McallPopTotality.mcallPop_shape_unsuppliable
