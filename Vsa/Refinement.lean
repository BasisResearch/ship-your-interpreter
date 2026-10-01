import Vsa.MemRepr
import Vsa.While.Semantics
import Vsa.Lang.Basic

namespace Vsa.Refine

open Vsa.Machine Vsa.MemRepr Vsa.While

structure Layout where
  atInterpRun : Config → Nat → Nat → Prop

def Loaded (L : Layout) (p : Program) (c : Config) : Prop :=
  ∃ a n, ProgramRepr c.σ.mem a n p ∧ L.atInterpRun c a n

/-- WHILE as an output-only language (`Vsa.Lang.ofOutput`). -/
abbrev whileLang : Vsa.Lang.Lang := Vsa.Lang.ofOutput Program BigStep

/-- Forward simulation of `BigStep` at `L`'s loading relation. -/
abbrev InterpSim (L : Layout) : Prop := Vsa.Lang.OutSim BigStep (Loaded L)

theorem refinement {L : Layout} (H : InterpSim L) :
    ∀ p c, Loaded L p c →
      (∀ out, BigStep p out ↔ Halts c out 0) ∧
      (Diverges c → ¬ ∃ out, BigStep p out) :=
  H.refinement

end Vsa.Refine
