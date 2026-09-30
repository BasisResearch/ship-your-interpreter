import Vsa.MemRepr
import Vsa.While.Semantics

namespace Vsa.Refine

open Vsa.Machine Vsa.MemRepr Vsa.While

structure Layout where
  atInterpRun : Config → Nat → Nat → Prop

def Loaded (L : Layout) (p : Program) (c : Config) : Prop :=
  ∃ a n, ProgramRepr c.σ.mem a n p ∧ L.atInterpRun c a n

structure InterpSim (L : Layout) : Prop where
  term_sim : ∀ p c out, Loaded L p c → BigStep p out → Halts c out 0
  stuck_sim : ∀ p c, Loaded L p c → (¬ ∃ out, BigStep p out) →
    Diverges c ∨ ∃ out e, Halts c out e ∧ e ≠ 0

theorem halts_bigStep {L : Layout} (H : InterpSim L) {p : Program}
    {c : Config} (hL : Loaded L p c) {out : String}
    (h : Halts c out 0) : BigStep p out := by
  by_cases hex : ∃ out', BigStep p out'
  · obtain ⟨out', hb⟩ := hex
    obtain ⟨ho, -⟩ := h.deterministic (H.term_sim p c out' hL hb)
    exact ho ▸ hb
  · rcases H.stuck_sim p c hL hex with hd | ⟨out', e, h', he⟩
    · exact (hd.not_halts h).elim
    · obtain ⟨-, hee⟩ := h.deterministic h'
      exact (he hee.symm).elim

theorem diverges_no_bigStep {L : Layout} (H : InterpSim L) {p : Program}
    {c : Config} (hL : Loaded L p c) (hd : Diverges c) :
    ¬ ∃ out, BigStep p out := by
  rintro ⟨out, hb⟩
  exact hd.not_halts (H.term_sim p c out hL hb)

theorem refinement {L : Layout} (H : InterpSim L) :
    ∀ p c, Loaded L p c →
      (∀ out, BigStep p out ↔ Halts c out 0) ∧
      (Diverges c → ¬ ∃ out, BigStep p out) := by
  intro p c hL
  refine ⟨fun out => ⟨fun hb => H.term_sim p c out hL hb,
    fun h => halts_bigStep H hL h⟩, fun hd => diverges_no_bigStep H hL hd⟩

end Vsa.Refine
