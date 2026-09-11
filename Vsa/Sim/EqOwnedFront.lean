import Vsa.Sim.EqCaseImage
import Vsa.Sim.EqFrontPresent
import Vsa.Sim.ValueEqualOwned
import Vsa.Sim.Code.FixedImage_Strcmp
import Vsa.Sim.Code.FixedImage_Eval_expr

open LeanRV64DExecutable Vsa Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc
open Vsa.Machine Vsa.Sim.Code

namespace Vsa.Sim
open RuntimeOwnership

/-- An aligned in-stack value slot supplies the equality helper's read region. -/
theorem VERegion.of_stack_offset {base : BitVec 64} {offset : Nat} {SL : StackLayout}
    (low : SL.lo ≤ base.toNat) (high : base.toNat + offset + 24 ≤ SL.hi)
    (ramLow : 0x80000000 ≤ SL.lo) (ramHigh : SL.hi ≤ 0x100000000)
    (htif : tohostAddr + 16 ≤ SL.lo)
    (aligned : base.toNat % 8 = 0) (offsetAligned : offset % 8 = 0) :
    VERegion (base + BitVec.ofNat 64 offset) := by
  have addr : (base + BitVec.ofNat 64 offset).toNat = base.toNat + offset := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  exact ⟨by rw [addr, Nat.add_mod, aligned, offsetAligned],
    by rw [addr]; omega, by rw [addr]; omega, by rw [addr]; omega⟩

/-- Owned copied operands and the fixed image supply the actual equality call. -/
theorem EqNeOp.ownedFront (op : EqNeOp)
    {N : NativeAddrs} {phiC : Addr → Nat} {shared : Nat → Prop}
    {base dst : BitVec 64} {vl vr : Value} {m : Mem} {c : Config}
    {A : Arena} {SL : StackLayout} {out : Array String}
    {gpre : (R : Register) → Option (RegisterType R)}
    (machine : op.DispatchMachine base out gpre c)
    (copied : EqDispatchOperands N phiC shared base vl vr m c)
    (geometry : SharedReadGeom shared SL) (image : StaticImageSupport c.σ.mem SL A)
    (identity : ValueEqualityIdentity N phiC vl vr)
    (room : SL.lo + 16 ≤ base.toNat) (high : base.toNat + 88 ≤ SL.hi)
    (ramLow : 0x80000000 ≤ SL.lo) (ramHigh : SL.hi ≤ 0x100000000)
    (htif : tohostAddr + 16 ≤ SL.lo) (aligned : base.toNat % 8 = 0)
    (result : c.σ.regs.get? Register.x9 = some dst) :
    EqFrontPresent (fun R => c.σ.regs.get? R) N phiC base dst vl vr
      op.returnPC op.callPC op.callImm c.σ.mem out c := by
  refine
    { hmemD := rfl, hG := machine.good, htick := machine.tick, hpc := machine.pc
      hjalTgt := by cases op <;> decide
      hlink := by cases op <;> decide
      hlinkAl := by cases op <;> decide
      hx10 := machine.left, hx11 := machine.right, hx2 := machine.stack
      hx9 := result, hout := machine.output
      jalSite := ?_
      hVeLoaded := image.text.Value_equalLoaded
      hJT := image.rodata.equalityTable
      hEE := image.text.Eval_exprLoaded
      hStrc := image.text.StrcmpLoaded
      hMask := Vsa.Sim.FixedRodataLoaded.maskPinned image.rodata
      hRegA := VERegion.of_stack_offset (by omega) (by omega) ramLow ramHigh htif
        aligned (by decide : 64 % 8 = 0)
      hRegB := VERegion.of_stack_offset (by omega) (by omega) ramLow ramHigh htif
        aligned (by decide : 32 % 8 = 0)
      hReprA := copied.left, hReprB := copied.right, hIdentity := identity
      hraln4 := by cases op <;> decide
      strings := ?_
      hsnapEval := fun _ _ _ _ _ => rfl }
  · cases op with
    | eq => exact fun σ i u pc vm => site_8000371c_ee σ i u pc vm
    | ne => exact fun σ i u pc vm => site_8000376c_ee σ i u pc vm
  · intro sa sb left right
    exact ValueEqualStringData.of_owned (left ▸ copied.leftOwned)
      (right ▸ copied.rightOwned) geometry image room (by omega)
      ramLow ramHigh htif aligned

#print axioms VERegion.of_stack_offset
#print axioms EqNeOp.ownedFront

end Vsa.Sim
