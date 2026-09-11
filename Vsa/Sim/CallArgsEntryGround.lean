import Vsa.Sim.CallArgSource

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- The original evaluator entry supplies the argument-array ground and every child budget. -/
theorem EvalEntry.arguments_ground
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {st : Vsa.While.St} {d env : Nat} {callee : Expr} {args : List Expr}
    {sp ret dst interp node : BitVec 64} {m0 : Mem} {before : Config}
    (h : EvalEntry g N A SL phiF phiC st d env (.call callee args) sp ret dst interp node m0 before) :
    CallArgStage.Ground m0 SL A (sp - 1088#64) node d callee args := by
  have ground : EvalGround m0 SL A sp dst node.toNat (.call callee args) := h.mem ▸ h.ground
  have room : 1088 ≤ sp.toNat := by have := h.stackOK.1; omega
  have upper := h.stackOK.2.1
  have lowered : (sp - 1088#64).toNat = sp.toNat - 1088 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 1088 ≤ sp.toNat; exact room)
  have lower : SL.lo ≤ (sp - 1088#64).toNat := by rw [lowered]; have := h.stackOK.1; omega
  have result : ((sp - 1088#64) + 64#64).toNat = sp.toNat - 1088 + 64 := by
    rw [BitVec.toNat_add, lowered]
    change (sp.toNat - 1088 + 64) % 2^64 = _
    exact Nat.mod_eq_of_lt (by have := sp.isLt; omega)
  refine
    { ground := ground.child_params (fun _ _ hin => hin) h.table_stack_disjoint upper
        (sp' := sp - 1088#64) (subsret := (sp - 1088#64) + 64#64)
        (by rw [lowered]; omega) (by rw [result]; rw [lowered] at lower; omega)
        (by rw [result]; omega)
      budget := ?_, bodies := (Expr.bodiesBound_call h.expr_bodies).2 }
  apply h.stackBudget.child (by decide)
  change (Expr.stackNeedList args + (maxCallDepth - d) * perCallBudget + 1088) + 1088 ≤
    (1088 + max callee.stackNeed (Expr.stackNeedList args)) + (maxCallDepth - d) * perCallBudget + 1088
  have bound := Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.le_max_right callee.stackNeed (Expr.stackNeedList args))
      ((maxCallDepth - d) * perCallBudget)) (1088 + 1088)
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using bound

end Vsa.Sim
