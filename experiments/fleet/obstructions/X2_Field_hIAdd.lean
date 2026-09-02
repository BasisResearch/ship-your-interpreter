import Vsa.Sim.rows.AssemblySkeleton
import Vsa.Sim.rows.BinDispatchRow

/-!
# Field `hIAdd` — MACHINE-CHECKED OBSTRUCTION (LA-int, X2 class)

The skeleton hole
`SkelHIAdd L := ∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
    BinIntCellResid .add AddResid … m0`
is **refutable as stated**, not merely unprovable.  `BinIntCellResid` ∀-closes
over ALL ghosts (in particular `m0`) with NO leading hypothesis, yet its
∃-body demands `BinArmExtras … m0` whose field
`slot6 : KindSlotPinned 6 (0x800034e8#64) m0`
is a static jump-table pin of `m0`.  At `m0 = ∅` NO `aLOp aROp Wl` can satisfy
it (the four table bytes are absent), so the whole cell is false.

This is exactly the design's **X2** diagnosis (`experiments/design/loop-arm.md`
§LA-int): the int cell is stated under ∀-`m0` with no entry.  The cure is the
**B2-carry amendment** — add `entry : EvalEntry …` as a HYPOTHESIS field to
`BinIntCellResid` so `slot6`/`sproom` become preconditions the entry supplies,
not free conclusions (a statement change to `rows/BinDispatchRow.lean`, done by
the coordinator; value paths relight verbatim).

Refutes through `slot6` at `m0 = ∅`.  Same shape covers all 11 int/eq cells.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Halts Diverges)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Refine (Layout Loaded InterpSim)
open Vsa.Sim.Rows

namespace Vsa.Sim.Rows.FieldIAdd

local notation "SpecSt" => Vsa.While.St

/-- The empty spec state (any inhabitant works). -/
def witSt : SpecSt := ⟨⟨#[], #[]⟩, ""⟩

/-- `KindSlotPinned 6 armPC ∅` is false: the four table bytes are absent. -/
theorem kindSlot6_empty_false (armPC : BitVec 64) :
    ¬ KindSlotPinned 6 armPC (∅ : Mem) := by
  rintro ⟨t0, _, _, _, hb0, _, _, _, _⟩
  simp at hb0

/-- **`SkelHIAdd` is false** (for every `L`): instantiate `BinIntCellResid`
at `m0 = ∅`, `SL := ⟨0,0⟩`; the ∃-body's `BinArmExtras.slot6` demands the
jump-table slot-6 word to be present in `∅`. -/
theorem field_hIAdd_refuted (L : Layout) :
    ¬ Vsa.Sim.TermAssembly.Skel.SkelHIAdd L := by
  intro H
  have h := H (fun _ => none) ⟨0, 0, 0⟩ ⟨0, 0⟩ ⟨0, 0⟩ (fun _ => 0) (fun _ => 0)
    witSt witSt witSt .null .null 0 0 (0#64) (0#64) (0#64) (0#64) (∅ : Mem)
  obtain ⟨_, _, _, aLOp, aROp, Wl, hX, _⟩ := h
  exact kindSlot6_empty_false _ hX.slot6

#print axioms field_hIAdd_refuted

end Vsa.Sim.Rows.FieldIAdd
