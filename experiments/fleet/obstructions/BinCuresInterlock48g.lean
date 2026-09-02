import Vsa.Sim.rows.BinArmBridge
import Vsa.Sim.rows.AssemblySkeleton
import Vsa.Sim.rows.BinDispatchRow
open Vsa.MemRepr Vsa.Alloc Vsa.Sim Vsa.While
open LeanRV64DExecutable Sail Register

/-!
# Wave 48g — the three int/eq cures INTERLOCK into one atomic wave (Law 4 STOP)

The brief specced three "bounded" cures for the 17 int/eq + unary/logic fields:
(1) B2 entry-carry on `BinIntCellResid`/`BinEqCellResid`; (2) an `EvalGround`
frame-window presence field discharging `BinArmExtras.frame_pop`; (3) a `blockA_k`
x13 widening discharging `BinArmExtras.x13_pres`.

Deep cone tracing (logged in `experiments/logs/wave0.md`, wave-48g section) shows
they are ONE interlocked wave, not three independent gates:

* **x13 is LOAD-BEARING** (not droppable): `blockB_binary` reads `x13`(a3) at the
  arm entry and SPILLS it (`sd a3,0(sp)` → `writeMap8 ma (sp-1088)
  (sdData_val aEnvReg)`, `Vsa/Sim/EvalBinSim.lean` ~ line 424) as the env argument
  threaded to the RIGHT sub-call.  So cure 3's honest form is `blockA_k` EMITTING
  `∃w, c'.x13 = some w`, which changes `blockA_k`'s output ∃-tower and forces its
  18 callers + the doubled `EvalArmHeadExtras` combinator (`ArmDispatchCombinator`)
  to re-thread — and requires a new `EvalEntry.x13_defined` field (18 callers).
* **frame_pop's presence is over the POST-sub-call memory `mcall`** (SubEvalReturn,
  `EvalNegSim2.lean:120`), not the entry `m0` — the dead sub-result bytes are
  populated by the sub-`value_int` 24-byte buffer write, so the honest discharge is
  inside the SIM cone (SubEvalReturn), not a bounded `EvalGround` ground field; and
  the ground-field alternative would need an UNVERIFIED top-level `m0`-totality
  supplier on `[SL.lo,sp)` (a possible NEW falsity — the census's whole guard).
* **`BinArmExtras` is DUPLICATED as `EvalArmHeadExtras`** with its own `x13_pres`;
  both structures + 11 `binRow_*` + 10 `eval*Sim` + `TermRouting` re-thread.

So landing any ONE cure relights 0 fields; the whole must land atomically (a
broken-tree window across ~30 files).  This file re-checks the ONE decisive,
axiom-clean fact that the int/eq cells remain FALSE as stated (cure 1 alone inert)
— confirming no false lemma entered the tree and the census stays honest at 6/58.

Verified with `lake env lean` only; NOT part of the build.
NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open Vsa.Refine (Layout)

namespace Vsa.Sim.Rows.BinCuresInterlock48g

/-- The empty spec state (any inhabitant works). -/
def witSt : Vsa.While.St := ⟨⟨#[], #[]⟩, ""⟩

/-- `KindSlotPinned 6 armPC ∅` is false: the four table bytes are absent. -/
theorem kindSlot6_empty_false (armPC : BitVec 64) :
    ¬ KindSlotPinned 6 armPC (∅ : Mem) := by
  rintro ⟨t0, _, _, _, hb0, _, _, _, _⟩
  simp at hb0

/-- **`SkelHIAdd` is FALSE for every `L`** (the int/eq cell remains refutable as
stated): instantiate `BinIntCellResid` at `m0 = ∅`; the ∃-body's
`BinArmExtras.slot6` demands the jump-table slot-6 word present in `∅`.  Same shape
covers all 11 int/eq holes.  Hence cure 1 (entry-carry) is a mandatory STATEMENT
change and, alone, relights nothing. -/
theorem field_hIAdd_still_refuted (L : Layout) :
    ¬ Vsa.Sim.TermAssembly.Skel.SkelHIAdd L := by
  intro H
  have h := H (fun _ => none) ⟨0, 0, 0⟩ ⟨0, 0⟩ ⟨0, 0⟩ (fun _ => 0) (fun _ => 0)
    witSt witSt witSt .null .null 0 0 (0#64) (0#64) (0#64) (0#64) (∅ : Mem)
  obtain ⟨_, _, _, aLOp, aROp, Wl, hX, _⟩ := h
  exact kindSlot6_empty_false _ hX.slot6

#print axioms field_hIAdd_still_refuted

end Vsa.Sim.Rows.BinCuresInterlock48g
