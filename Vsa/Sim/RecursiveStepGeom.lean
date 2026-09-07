import Vsa.Sim.TripleCat

namespace Vsa.Sim

open Vsa.Machine (Config)
open Vsa.Logic

/-- A reached recursive boundary keeps the continuing and terminal cases distinct. -/
def RecursiveStepPost (continues : Prop) (Ready Exit : Config → Prop)
    (cfg : Config) : Prop :=
  (continues ∧ Ready cfg) ∨ (¬ continues ∧ Exit cfg)

/-- One finite iteration, indexed by its source status and exact boundary predicates. -/
structure RecursiveStepGeom (continues : Prop) (Pre Ready Exit : Config → Prop) : Prop where
  step : Triple Pre (RecursiveStepPost continues Ready Exit)

namespace RecursiveStepGeom

/-- A terminal source status selects the reached final exit. -/
theorem terminal {continues : Prop} {Pre Ready Exit : Config → Prop}
    (G : RecursiveStepGeom continues Pre Ready Exit) (hstop : ¬ continues) :
    Triple Pre Exit := by
  apply G.step.rmap
  intro cfg hpost
  rcases hpost with ⟨hc, _⟩ | ⟨_, he⟩
  · exact absurd hc hstop
  · exact he

/-- A continuing source status selects the exact recursive entry. -/
theorem continuing {continues : Prop} {Pre Ready Exit : Config → Prop}
    (G : RecursiveStepGeom continues Pre Ready Exit) (hcontinue : continues) :
    Triple Pre Ready := by
  apply G.step.rmap
  intro cfg hpost
  rcases hpost with ⟨_, hr⟩ | ⟨hs, _⟩
  · exact hr
  · exact absurd hcontinue hs

/-- Splice the recursive continuation without losing its reached entry. -/
theorem resume {continues : Prop} {Pre Ready Exit Final : Config → Prop}
    (G : RecursiveStepGeom continues Pre Ready Exit) (hcontinue : continues)
    (hrest : Triple Ready Final) : Triple Pre Final :=
  (G.continuing hcontinue).seq hrest

end RecursiveStepGeom

/-- A child call retains its exact machine indices and its parent's static facts. -/
structure ChildBoundary (Index : Type) (Carrier : Index → Prop)
    (Entry Exit : Index → Config → Prop) (Pre Post : Config → Prop) : Prop where
  dispatch : Triple Pre (fun cfg => ∃ index, Carrier index ∧ Entry index cfg)
  resume : ∀ index, Carrier index → Triple (Exit index) Post

/-- Apply the typed child IH at the dispatched entry, then resume at its actual exit. -/
theorem ChildBoundary.run {Index : Type} {Carrier : Index → Prop}
    {Entry Exit : Index → Config → Prop} {Pre Post : Config → Prop}
    (G : ChildBoundary Index Carrier Entry Exit Pre Post)
    (child : ∀ index, Triple (Entry index) (Exit index)) : Triple Pre Post := by
  intro cfg hpre
  obtain ⟨cfgE, hsE, index, hcarrier, hentry⟩ := G.dispatch cfg hpre
  obtain ⟨cfgX, hsX, hexit⟩ := child index cfgE hentry
  obtain ⟨cfgR, hsR, hpost⟩ := G.resume index hcarrier cfgX hexit
  exact ⟨cfgR, (hsE.trans hsX).trans hsR, hpost⟩

#print axioms RecursiveStepGeom.terminal
#print axioms RecursiveStepGeom.continuing
#print axioms RecursiveStepGeom.resume
#print axioms ChildBoundary.run

end Vsa.Sim
