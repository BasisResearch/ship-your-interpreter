import experiments.fleet.obstructions.CureValidationCur
open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Halts Diverges)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Refine (Layout)
open Vsa.Sim
open Vsa.Sim.TermAssembly (TermResidualsCore)

/-!
# The B2-carry LANDED — the 11 int/eq falsities are gone from the tree

`RefutBatteryCur.lean` proves the 11 BARE `∀ …, BinIntCellResid …` /
`BinEqCellResid …` statements FALSE at `m0 := ∅`; `CureValidationCur.lean`
validates the cure (`EvalEntry` entails the missing `KindSlotPinned 6` pin and is
itself uninhabited at `∅`).  Wave 49 APPLIED that cure: the 11
`TermResidualsCore` fields are now stated as `Vsa.Sim.BinIntCell` /
`Vsa.Sim.BinEqCell`, which carry the arm's `EvalEntry` exactly as the 6
unary/logic siblings always did.

This file is the machine-checked record that the amendment landed and works:

* **slot-verify** — each of the 11 fields IS the entry-guarded shape (the
  projection alone is accepted at the ascribed type, no adaptation);
* **vacuity at the killer witness** — instantiated at the `∅` memory that
  produced the countermodel, the amended obligation is DISCHARGED outright, so
  the refutation that killed the bare form has no analogue for the landed one.

Kernel proofs, axiom-clean, no solver.  Run via `lake env lean`.
-/

namespace Vsa.B2CarryLanded

/-! ## Slot-verify — the landed fields ARE the entry-guarded shapes. -/

section
variable (L : Layout) (R : TermResidualsCore L)

example : BinIntCell .add Vsa.Sim.AddResid (fun _ _ => True) := R.hIAdd
example : BinIntCell .sub Vsa.Sim.SubResid (fun _ _ => True) := R.hISub
example : BinIntCell .mul Vsa.Sim.MulResid (fun _ _ => True) := R.hIMul
example : BinIntCell .mod Vsa.Sim.ModResid (fun _ _ => True) := R.hIMod
example : BinIntCell .lt  Vsa.Sim.LtResid  (fun _ _ => True) := R.hILt
example : BinIntCell .le  Vsa.Sim.LeResid  (fun _ _ => True) := R.hILe
example : BinIntCell .gt  Vsa.Sim.GtResid  (fun _ _ => True) := R.hIGt
example : BinIntCell .ge  Vsa.Sim.GeResid  (fun _ _ => True) := R.hIGe
example : BinIntCell .div Vsa.Sim.DivResid (fun a b => ¬(a = -2^63 ∧ b = -1)) := R.hIDiv
example : BinEqCell .eq .eq (0x80003720#64) (0x8000371c#64) (0x1ff140#21) := R.hEq
example : BinEqCell .ne .ne (0x80003770#64) (0x8000376c#64) (0x1ff0f0#21) := R.hNe
end

/-! ## Vacuity at the killer witness — the `∅` countermodel is gone. -/

variable {g : (R : Register) → Option (RegisterType R)}
  {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
  {st st' st'' : While.St} {d : Nat} {env : Addr} {el er : Expr}
  {sp r sret aEnv aExpr : BitVec 64} {c : Config}

/-- The amended int-cell obligation is DISCHARGED at `m0 := ∅`: its `EvalEntry`
hypothesis entails `KindSlotPinned 6 0x800034e8 ∅`, which is false. -/
theorem binIntCell_at_empty
    (opTok : BinOp)
    (Resid : ((R : Register) → Option (RegisterType R)) → NativeAddrs → Arena →
      StackLayout → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
      Config → Prop)
    {a b : Int}
    (he : EvalEntry g N A SL φf φc st d env (.binary opTok el er) sp r sret aEnv aExpr
      (∅ : Mem) c) :
    BinIntCellResid opTok Resid g N A SL φf φc st st' st'' el er a b sp r sret aExpr
      (∅ : Mem) :=
  (kindSlot6_empty_false _ (evalEntry_supplies_slot6 he)).elim

/-- The same for the two eq/ne cells. -/
theorem binEqCell_at_empty
    (op : Vsa.Sim.EqNeOp) (opTok : BinOp) (link jalPC : BitVec 64) (jImm : BitVec 21)
    {vl vr : Value}
    (he : EvalEntry g N A SL φf φc st d env (.binary opTok el er) sp r sret aEnv aExpr
      (∅ : Mem) c) :
    BinEqCellResid op opTok link jalPC jImm g N A SL φf φc st st' st'' el er vl vr
      sp r sret aExpr (∅ : Mem) :=
  (kindSlot6_empty_false _ (evalEntry_supplies_slot6 he)).elim

#print axioms binIntCell_at_empty
#print axioms binEqCell_at_empty

end Vsa.B2CarryLanded
