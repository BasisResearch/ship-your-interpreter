import Vsa.Sim.BinaryPostGeom
import Vsa.Sim.FixedOperatorTable
import Vsa.Sim.EqNeDispatchInput

open LeanRV64DExecutable Vsa Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc
open Vsa.Machine Vsa.Sim.Code

namespace Vsa.Sim

namespace EqNeOp

def operator : EqNeOp → BinOp
  | .eq => .eq
  | .ne => .ne

def callPC : EqNeOp → BitVec 64
  | .eq => 0x8000371c#64
  | .ne => 0x8000376c#64

def returnPC : EqNeOp → BitVec 64
  | .eq => 0x80003720#64
  | .ne => 0x80003770#64

def callImm : EqNeOp → BitVec 21
  | .eq => 0x1ff140#21
  | .ne => 0x1ff0f0#21

def result (op : EqNeOp) (vl vr : Value) : Bool :=
  match op with
  | .eq => vl.equal vr
  | .ne => !(vl.equal vr)

/-- The fixed read-only image supplies either equality dispatch slot. -/
theorem slot_of_image (op : EqNeOp) {m : Mem} (image : FixedRodataLoaded m) :
    op.slotPinned m := by
  cases op with
  | eq => exact image.slotPinned 0x80019fa4#64 (by decide) (by decide)
  | ne => exact image.slotPinned 0x80019f9c#64 (by decide) (by decide)

/-- Named machine facts at either equality helper call site. -/
structure DispatchMachine (op : EqNeOp) (base : BitVec 64)
    (out : Array String) (gpre : (R : Register) → Option (RegisterType R))
    (c : Config) : Prop where
  good : GoodState c.σ
  pc : c.σ.regs.get? .PC = some op.callPC
  left : c.σ.regs.get? .x10 = some (base + 0x40#64)
  right : c.σ.regs.get? .x11 = some (base + 0x20#64)
  stack : c.σ.regs.get? .x2 = some base
  tick : c.tick < 2
  output : c.σ.sailOutput = out
  frame : ∀ R, AbiPreservedNoise R → (.x8 == R) = false → c.σ.regs.get? R = gpre R

/-- Destructure the existing dispatch post once for both operators. -/
theorem DispatchPost.machine {op : EqNeOp} {base : BitVec 64}
    {lds : List (List (BitVec 8))} {m : Mem} {out : Array String}
    {gpre : (R : Register) → Option (RegisterType R)} {c : Config}
    (h : op.DispatchPost base lds m out gpre c) :
    DispatchMachine op base out gpre c := by
  cases op <;>
    obtain ⟨good, _, pc, left, right, stack, tick, output, frame, _⟩ := h <;>
    exact ⟨good, pc, left, right, stack, tick, output, frame⟩

end EqNeOp

/-- The actual binary entry and operand return supply equality dispatch geometry. -/
theorem EvalEntry.eqDispatchInput
    (op : EqNeOp)
    {g gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {st middle final : Vsa.While.St} {d env : Nat} {el er : Expr} {vl vr : Value}
    {sp ret dst interp node v8 v9 v18 v19 : BitVec 64} {m0 : Mem} {before after : Config}
    (entry : EvalEntry g N A SL phiF phiC st d env (.binary op.operator el er)
      sp ret dst interp node m0 before)
    (frame : BinaryArmFrame g gpre sp node v8 v9 v18 v19)
    (returned : TwoSubReturn gpre N A SL phiF phiC st.store.frames.size
      st.store.closures.size middle final vl vr sp ret dst v8 v9 v18 m0 after) :
    EqNeDispatchInput op gpre SL sp node after := by
  have stack := entry.stackOK
  unfold StackOK at stack
  have image := entry.binaryReturnImage returned
  have token := entry.binaryReturnToken returned
  have tokenEq : binOpTok op.operator = op.token := by cases op <;> rfl
  exact
    { gx8 := frame.node
      opTok := tokenEq ▸ token
      slot := op.slot_of_image image.rodata
      expr := ⟨entry.expr_ram.1, entry.expr_ram.2, by have := entry.expr_win; omega⟩
      stack := ⟨by omega, entry.stack_ram.1, entry.stack_win, by omega,
        by have := entry.stack_ram.2; omega⟩ }

#print axioms EqNeOp.slot_of_image
#print axioms EqNeOp.DispatchPost.machine
#print axioms EvalEntry.eqDispatchInput

end Vsa.Sim
