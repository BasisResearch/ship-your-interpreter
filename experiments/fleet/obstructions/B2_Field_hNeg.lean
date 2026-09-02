import Vsa.Sim.rows.AssemblySkeleton

/-!
# Field `hNeg` — MACHINE-CHECKED OBSTRUCTION (fleet B2-unary-logic)

The skeleton hole `SkelHNeg L := ∀ st esub, NegResid st esub` is **refutable**,
not merely unprovable: `NegResid` ∀-closes over ALL ghosts
(`N A SL sp r sret aEnv aExpr aOperand m0`) with only the two operand-side
hypotheses (`read64 m0 (aExpr.toNat+16) = some aOperand.toNat` and
`ExprRepr m0 aOperand.toNat esub`), yet its conclusion `NegExtras` demands
entry-only geometry nothing supplies — e.g.

* `sp_headroom : SL.lo + 3264 ≤ sp.toNat`  (fails at `sp = 0#64`, ANY `SL`),
* `op_lo : 0x80000000 ≤ aOperand.toNat`    (fails at a low operand address),
* `slot8 : KindSlotPinned 8 (0x800035e0#64) m0` (a static-image pin of `m0`),

and the `hMcallPop` conjunct forces `m0` itself to be TOTALLY populated
(instantiate `mcall := m0`), which a finite witness memory refutes.

This file lands the batch's shared falsifying witness (a tiny concrete
`ExtHashMap` memory holding two `.null` expr nodes and their payload
pointers) and refutes the hole through `sp_headroom` at `sp = 0#64`.

**Consequence for the coordinator**: `field_hNeg` CANNOT be supplied as
stated; the `NegResid` statement needs an amendment threading entry linkage
(the `EvalEntry`/Layout facts that pin `SL`/`sp`/`m0`) — the same shape as
every other B2 field (`hNot`/`hOrTrue`/`hAndFalse`/`hOrFalse`/`hAndTrue`,
refuted in their own `Field_*.lean` files from this witness).  Precedent:
the `Trichotomy` falsity → amendment cycle (`Vsa/While/StmtDispatch.lean`).
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Halts Diverges)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Refine (Layout Loaded InterpSim)
open Vsa.Sim.Rows
open Vsa.Sim.ScaffoldRows
open Vsa.Sim.TermSimAssembly

namespace Vsa.Sim.Rows.FieldB2

local notation "SpecSt" => Vsa.While.St

/-! ## The shared B2 falsifying witness -/

/-- Witness memory: a `.null` expr node (tag 3) at 40 and another at 48, with
an enclosing node's payload slots `[16,24) ↦ 40` (left/operand pointer) and
`[24,32) ↦ 48` (right pointer).  Everything else absent — in particular the
jump-table slots, so the static pins of `NegExtras`/`OrTrueExtras` also fail,
and the memory is finite, so `hMcallPop` fails at `mcall := m0`. -/
def b2WitMem : Mem :=
  (∅ : Mem).insert 16 40 |>.insert 17 0 |>.insert 18 0 |>.insert 19 0
    |>.insert 20 0 |>.insert 21 0 |>.insert 22 0 |>.insert 23 0
    |>.insert 24 48 |>.insert 25 0 |>.insert 26 0 |>.insert 27 0
    |>.insert 28 0 |>.insert 29 0 |>.insert 30 0 |>.insert 31 0
    |>.insert 40 3 |>.insert 41 0 |>.insert 42 0 |>.insert 43 0
    |>.insert 48 3 |>.insert 49 0 |>.insert 50 0 |>.insert 51 0

/-- Payload read: the left/operand pointer slot `[16,24)` holds 40. -/
theorem b2WitMem_payL : read64 b2WitMem 16 = some 40 := by
  simp [b2WitMem, read64, readLE, Std.ExtHashMap.getElem_insert]

/-- Payload read: the right pointer slot `[24,32)` holds 48. -/
theorem b2WitMem_payR : read64 b2WitMem 24 = some 48 := by
  simp [b2WitMem, read64, readLE, Std.ExtHashMap.getElem_insert]

/-- The node at 40 represents `.null` (tag read 3). -/
theorem b2WitMem_nullL : ExprRepr b2WitMem 40 .null :=
  .null (by simp [b2WitMem, read32, readLE, Std.ExtHashMap.getElem_insert])

/-- The node at 48 represents `.null` (tag read 3). -/
theorem b2WitMem_nullR : ExprRepr b2WitMem 48 .null :=
  .null (by simp [b2WitMem, read32, readLE, Std.ExtHashMap.getElem_insert])

/-- The empty spec state (any inhabitant works for the refutations). -/
def b2WitSt : SpecSt := ⟨⟨#[], #[]⟩, ""⟩

/-- A machine configuration inhabitant (for the logical Resids' `c` slot). -/
def b2WitCfg : Config := ⟨default, 0, 0⟩

/-! ## The `hNeg` refutation -/

/-- **`SkelHNeg` is false** (for every `L`): instantiate `NegResid` at the
witness memory with `sp := 0#64`, `SL := ⟨0,0⟩`; the hypotheses hold
(payload slot 16 ↦ 40, `.null` node at 40), but `NegExtras.sp_headroom`
demands `SL.lo + 3264 ≤ 0`. -/
theorem field_hNeg_refuted (L : Layout) :
    ¬ Vsa.Sim.TermAssembly.Skel.SkelHNeg L := by
  intro H
  have h := H b2WitSt .null ⟨0, 0, 0⟩ ⟨0, 0⟩ ⟨0, 0⟩
    (0#64) (0#64) (0#64) (0#64) (0#64) (40#64) b2WitMem
    b2WitMem_payL b2WitMem_nullL
  exact absurd h.1.sp_headroom (by decide)

#print axioms field_hNeg_refuted

end Vsa.Sim.Rows.FieldB2
