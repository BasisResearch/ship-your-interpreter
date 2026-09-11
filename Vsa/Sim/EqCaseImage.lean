import Vsa.Sim.EqCaseEntry
import Vsa.Sim.EqDispatchOwned
import Vsa.Sim.Code.FixedImage_Value_equal
import Vsa.Sim.Code.FixedImage_Value_bool
import Vsa.Sim.StrCmpSeam

open LeanRV64DExecutable Vsa Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc
open Vsa.Machine Vsa.Sim.Code

namespace Vsa.Sim

/-- Extract one byte at an absolute address inside a bounded image. -/
theorem Code.FixedBytesLoaded.byteAt {m : Mem} {base size a : Nat}
    {byte : Nat → BitVec 8} (h : FixedBytesLoaded base size byte m)
    (low : base ≤ a) (high : a < base + size) :
    m[a]? = some (byte (a - base)) := by
  have pin := h (a - base) (by omega)
  simpa only [Nat.add_sub_of_le low] using pin

/-- The fixed read-only image supplies the equality kind table. -/
theorem Code.FixedRodataLoaded.equalityTable {m : Mem} (h : FixedRodataLoaded m) :
    JumpTable m := by
  unfold JumpTable
  repeat' apply And.intro
  all_goals exact FixedBytesLoaded.byteAt h (by decide) (by decide)

/-- Equality's operand copies retain the complete static interpreter image. -/
theorem EqDispatchOperands.image
    {N : NativeAddrs} {phiC : Addr → Nat} {shared : Nat → Prop}
    {base : BitVec 64} {vl vr : Value} {m : Mem} {c : Config}
    {A : Arena} {SL : StackLayout}
    (h : EqDispatchOperands N phiC shared base vl vr m c)
    (image : StaticImageSupport m SL A)
    (low : SL.lo ≤ base.toNat) (high : base.toNat + 88 ≤ SL.hi) :
    StaticImageSupport c.σ.mem SL A :=
  image.transport (fun k hk => h.outside k (by
    have outside := image.outsideStack hk
    omega))

#print axioms Code.FixedBytesLoaded.byteAt
#print axioms Code.FixedRodataLoaded.equalityTable
#print axioms EqDispatchOperands.image

end Vsa.Sim
