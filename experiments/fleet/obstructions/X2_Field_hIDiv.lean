import Vsa.Sim.rows.AssemblySkeleton
import Vsa.Sim.rows.BinDispatchRow
import Vsa.Sim.rows.Field_hIAdd

/-!
# Field `hIDiv` — MACHINE-CHECKED OBSTRUCTION (LA-int, X2 class)

`SkelHIDiv` unfolds to `∀ … a b, ¬(a=-2^63 ∧ b=-1) → ∀ … m0,
BinIntCellResid .div DivResid … m0`.  Discharge the non-overflow guard with a
witness `a=0, b=1`; the ∃-body still demands `BinArmExtras.slot6`, false at
`m0 = ∅`.  X2 diagnosis; cure = B2-carry `entry` field.  See Field_hIAdd.lean.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Halts Diverges)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Refine (Layout Loaded InterpSim)
open Vsa.Sim.Rows
open Vsa.Sim.Rows.FieldIAdd (witSt kindSlot6_empty_false)

namespace Vsa.Sim.Rows.FieldIDiv

theorem field_hIDiv_refuted (L : Layout) :
    ¬ Vsa.Sim.TermAssembly.Skel.SkelHIDiv L := by
  intro H
  have h := H (fun _ => none) ⟨0, 0, 0⟩ ⟨0, 0⟩ ⟨0, 0⟩ (fun _ => 0) (fun _ => 0)
    witSt witSt witSt .null .null 0 1 (by decide) (0#64) (0#64) (0#64) (0#64) (∅ : Mem)
  obtain ⟨_, _, _, aLOp, aROp, Wl, hX, _⟩ := h
  exact kindSlot6_empty_false _ hX.slot6

#print axioms field_hIDiv_refuted

end Vsa.Sim.Rows.FieldIDiv
