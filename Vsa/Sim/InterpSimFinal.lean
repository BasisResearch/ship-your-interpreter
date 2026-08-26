import Vsa.Sim.TermSimClose
import Vsa.Sim.StuckSimClose
import Vsa.Sim.InterpSimBundle

/-!
# The ENDGAME CAPSTONE — `interpSim_conditional`

The end-to-end theorem of the development: the whole `InterpSim L` forward-
simulation structure — hence, via `Vsa.Refine.refinement`, the complete
behavioral correspondence between the interpreter binary under the ISA relation
and the big-step specification — assembled from the two close skeletons.

## The finish line, factored

The two per-field obligations are exactly:

* the **term arm** `hterm` — the `InterpSim.term_sim` field:
  `∀ p c out, Loaded L p c → BigStep p out → Halts c out 0`.
  It is discharged by `TermSimClose.termSimClosed L <M4 bundle> hEntryHalts`,
  conditional on the 50-premise **M4 residual bundle** (`hInt`…`hSeqConsAbrupt`,
  the per-constructor case Triples) plus the program-entry bridge `hEntryHalts`.

* the **stuck arm** `hstuck` — the `InterpSim.stuck_sim` field:
  `∀ p c, Loaded L p c → (¬∃out, BigStep p out) → Diverges c ∨ ∃ out e, …`.
  It is discharged, per introduced `(p, c)`, by
  `StuckSimClose.stuckSimClosed p c htri Corr hDivStep hentry <42 error sites>`,
  i.e. from the `Trichotomy` obligation, the divergence correspondence family
  (`DivFamily`, `Vsa/Sim/InterpSimBundle.lean`) and the 42 per-error-site
  residuals (`ErrFamily`/`errFamily_of_sites`, same file).

`interpSim_conditional` is the thin, fast assembler: it packs the two field-
shaped obligations into the `InterpSim L` structure.  Its two hypotheses ARE the
`InterpSim` fields; the residual-pinning lives in `termSimClosed`/`stuckSimClosed`
/`errFamily_of_sites`, which take the M4/M5 residual bundles explicitly.
`interpSimClosed_of_families` then wires the family-level M5 bundle
(`DivFamily`/`ErrFamily`) into the stuck arm, so the capstone can be driven from
the aggregated families directly.

Composing `interpSim_conditional` with `Vsa.Refine.refinement` yields the
conditional refinement corollary `refinement_conditional`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`/`admit`.
-/

namespace Vsa.Sim.InterpSimFinal

open Vsa.While
open Vsa.Machine (Config Halts Diverges)
open Vsa.Refine (Layout Loaded InterpSim refinement)
open Vsa.Sim
open Vsa.Sim.InterpSimBundle (DivFamily ErrFamily)

local notation "SpecSt" => Vsa.While.St

/-- **THE ENDGAME CAPSTONE (field form).**  The full `InterpSim L` forward-
simulation structure from the two field-shaped obligations.  `hterm` is
discharged by `TermSimClose.termSimClosed` (the 50-premise M4 bundle + the
program-entry bridge); `hstuck` by `StuckSimClose.stuckSimClosed` (trichotomy +
the divergence family + the 42 error-site residuals). -/
theorem interpSim_conditional (L : Layout)
    (hterm : ∀ (p : Program) (c : Config) (out : String),
      Loaded L p c → BigStep p out → Halts c out 0)
    (hstuck : ∀ (p : Program) (c : Config),
      Loaded L p c → (¬ ∃ out, BigStep p out) →
      Diverges c ∨ ∃ out e, Halts c out e ∧ e ≠ 0) :
    InterpSim L :=
  ⟨hterm, hstuck⟩

/-- **The stuck arm from the aggregated M5 families.**  From the `Trichotomy`
obligation, the divergence correspondence family and the error-site family, the
`InterpSim.stuck_sim` field follows — the family-level packaging of
`StuckSimClose.stuckSimClosed`'s per-`(p,c)` discharge. -/
theorem stuckField_of_families (L : Layout)
    (htri : Trichotomy) (hdivFam : DivFamily L) (herrFam : ErrFamily L) :
    ∀ (p : Program) (c : Config),
      Loaded L p c → (¬ ∃ out, BigStep p out) →
      Diverges c ∨ ∃ out e, Halts c out e ∧ e ≠ 0 := by
  intro p c hL hno
  obtain ⟨Corr, hDivStep, hentry⟩ := hdivFam p c hL
  exact stuckSim htri (fun herr => herrFam p c hL herr)
    (fun hdiv => stuck_of_divergenceSim Corr hDivStep hentry hdiv) hno

/-- **THE ENDGAME CAPSTONE (families form).**  `InterpSim L` from the program-
entry term arm and the aggregated M5 families.  The term arm `hterm` is the same
`termSimClosed`-discharged field; the stuck arm is built from
`stuckField_of_families`. -/
theorem interpSimClosed_of_families (L : Layout)
    (hterm : ∀ (p : Program) (c : Config) (out : String),
      Loaded L p c → BigStep p out → Halts c out 0)
    (htri : Trichotomy) (hdivFam : DivFamily L) (herrFam : ErrFamily L) :
    InterpSim L :=
  interpSim_conditional L hterm (stuckField_of_families L htri hdivFam herrFam)

/-- **Conditional refinement.**  The complete behavioral correspondence, from the
capstone: for every loaded program the machine's clean terminating behaviors are
exactly `p`'s big-step behaviors, and machine divergence entails `p` has none. -/
theorem refinement_conditional (L : Layout)
    (hterm : ∀ (p : Program) (c : Config) (out : String),
      Loaded L p c → BigStep p out → Halts c out 0)
    (htri : Trichotomy) (hdivFam : DivFamily L) (herrFam : ErrFamily L) :
    ∀ p c, Loaded L p c →
      (∀ out, BigStep p out ↔ Vsa.Machine.Halts c out 0) ∧
      (Diverges c → ¬ ∃ out, BigStep p out) :=
  refinement (interpSimClosed_of_families L hterm htri hdivFam herrFam)

end Vsa.Sim.InterpSimFinal
