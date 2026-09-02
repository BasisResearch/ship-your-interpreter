import Vsa.Sim.rows.AssemblySkeleton
import Vsa.Sim.rows.BinDispatchRow
import Vsa.Sim.rows.Field_hIAdd

/-!
# Field `hNe` — MACHINE-CHECKED OBSTRUCTION (LA-int/ne, X2 class)

`SkelHEq` unfolds to `∀ … vl vr … m0, BinEqCellResid .ne .ne … m0` with NO
leading hypothesis; its ∃-body demands `BinArmExtras.slot6 :
KindSlotPinned 6 (0x800034e8#64) m0`, false at `m0 = ∅`.  X2 diagnosis
(`experiments/design/loop-arm.md` §LA-int).  Cure = B2-carry `entry : EvalEntry`
field on `BinEqCellResid` (coordinator statement change).  See Field_hIAdd.lean.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Halts Diverges)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Refine (Layout Loaded InterpSim)
open Vsa.Sim.Rows
open Vsa.Sim.Rows.FieldIAdd (witSt kindSlot6_empty_false)

namespace Vsa.Sim.Rows.FieldNe

theorem field_hNe_refuted (L : Layout) :
    ¬ Vsa.Sim.TermAssembly.Skel.SkelHEq L := by
  intro H
  have h := H (fun _ => none) ⟨0, 0, 0⟩ ⟨0, 0⟩ ⟨0, 0⟩ (fun _ => 0) (fun _ => 0)
    witSt witSt witSt .null .null .null .null (0#64) (0#64) (0#64) (0#64) (∅ : Mem)
  obtain ⟨_, _, _, aLOp, aROp, w19, hX, _, _⟩ := h
  exact kindSlot6_empty_false _ hX.slot6

#print axioms field_hNe_refuted

end Vsa.Sim.Rows.FieldNe
