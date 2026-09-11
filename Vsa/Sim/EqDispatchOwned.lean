import Vsa.Sim.rows.EvalEqNeFront
import Vsa.Sim.RuntimeOwnershipCopy
import Vsa.Sim.SharedReadGeometry
import Vsa.Sim.MemPresence

open LeanRV64DExecutable Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc
open Vsa.Machine

namespace Vsa.Sim
open RuntimeOwnership

/-- Both equality dispatches produce the same six-word copy layout. -/
theorem EqNeOp.DispatchReadback.tower
    {op : EqNeOp} {base : BitVec 64} {lds : List (List (BitVec 8))}
    {m : Mem} {c : Config} (h : EqNeOp.DispatchReadback op base lds m c) :
    c.σ.mem = eqTower base m (lds.getD 0 []) (lds.getD 1 []) (lds.getD 2 [])
      (lds.getD 3 []) (lds.getD 4 []) (lds.getD 5 []) := by
  cases op with
  | eq => rw [h.memory, eqDispatch_log_trunc]; rfl
  | ne => rw [h.memory, neDispatch_log_trunc]; rfl

/-- The compare buffers retain their values and payload ownership at one map. -/
structure EqDispatchOperands (N : NativeAddrs) (phiC : Addr → Nat)
    (shared : Nat → Prop) (base : BitVec 64) (vl vr : Value)
    (m : Mem) (c : Config) : Prop where
  left : ValueRepr c.σ.mem N phiC (base + 0x40#64).toNat vl
  right : ValueRepr c.σ.mem N phiC (base + 0x20#64).toNat vr
  leftOwned : ValueOwned c.σ.mem shared (base + 0x40#64).toNat vl
  rightOwned : ValueOwned c.σ.mem shared (base + 0x20#64).toNat vr
  sharedAgreement : AgreeP shared m c.σ.mem
  presence : MemExtends m c.σ.mem
  outside : ∀ k, k < base.toNat + 32 ∨ base.toNat + 88 ≤ k → c.σ.mem[k]? = m[k]?

/-- Recover both owned operands from the actual reflected dispatch writes. -/
theorem EqNeOp.DispatchReadback.owned
    {op : EqNeOp} {base : BitVec 64} {lds : List (List (BitVec 8))}
    {m : Mem} {c : Config} {N : NativeAddrs} {phiC : Addr → Nat}
    {shared : Nat → Prop} {SL : StackLayout} {vl vr : Value}
    (h : EqNeOp.DispatchReadback op base lds m c)
    (bound : base.toNat + 4096 ≤ 2 ^ 64)
    (low : SL.lo ≤ base.toNat) (high : base.toNat + 88 ≤ SL.hi)
    (geometry : SharedReadGeom shared SL)
    (left : ValueRepr m N phiC (base + 0x78#64).toNat vl)
    (right : ValueRepr m N phiC (base + 0x90#64).toNat vr)
    (leftOwned : ValueOwned m shared (base + 0x78#64).toNat vl)
    (rightOwned : ValueOwned m shared (base + 0x90#64).toNat vr) :
    EqDispatchOperands N phiC shared base vl vr m c := by
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := h.pins
  have copyLeft : ∀ j, j < 24 → c.σ.mem[(base + 0x40#64).toNat + j]? =
      some ((m[(base + 0x78#64).toNat + j]?).getD 0) := by
    rw [h.tower]
    exact eqTower_copy_bufa base m _ _ _ _ _ _ bound p0 p1 p2
  have copyRight : ∀ j, j < 24 → c.σ.mem[(base + 0x20#64).toNat + j]? =
      some ((m[(base + 0x90#64).toNat + j]?).getD 0) := by
    rw [h.tower]
    exact eqTower_copy_bufb base m _ _ _ _ _ _ bound p3 p4 p5
  have outside : ∀ k, k < base.toNat + 32 ∨ base.toNat + 88 ≤ k →
      c.σ.mem[k]? = m[k]? := by
    rw [h.tower]
    exact eqTower_outside base m _ _ _ _ _ _ bound
  have agreement : AgreeP shared m c.σ.mem := by
    intro k hk
    exact (outside k (by have := geometry.stack k hk; omega)).symm
  exact
    { left := valueRepr_copy_total_exact copyLeft (leftOwned.covered agreement) left
      right := valueRepr_copy_total_exact copyRight (rightOwned.covered agreement) right
      leftOwned := leftOwned.copy_total copyLeft agreement
      rightOwned := rightOwned.copy_total copyRight agreement
      sharedAgreement := agreement
      presence := h.memory ▸ memExtends_writeLog m _
      outside := outside }

#print axioms EqNeOp.DispatchReadback.tower
#print axioms EqNeOp.DispatchReadback.owned

end Vsa.Sim
