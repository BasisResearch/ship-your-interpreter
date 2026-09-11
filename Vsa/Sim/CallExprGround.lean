import Vsa.Sim.EntryGroundKit

namespace Vsa.Sim

open LeanRV64DExecutable Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- Entry facts for a callee or argument expression at its actual result slot. -/
structure CallExprGround (m : Mem) (SL : StackLayout) (A : Arena)
    (sp dst : BitVec 64) (d node : Nat) (e : Expr) : Prop where
  ground : EvalGround m SL A sp dst node e
  budget : StackOK SL sp (e.stackNeed + (maxCallDepth - d) * perCallBudget + 1088)
  bodies : Expr.bodiesBound perCallBudget e = true

/-- Caller spills preserve the expression's hereditary ground and stack budget. -/
theorem CallExprGround.transport_stack
    {m m' : Mem} {SL : StackLayout} {A : Arena} {sp dst : BitVec 64}
    {d node : Nat} {e : Expr} (h : CallExprGround m SL A sp dst d node e)
    (presence : MemExtends m m')
    (frame : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → m[k]? = m'[k]?) :
    CallExprGround m' SL A sp dst d node e := by
  refine
    { ground := h.ground.transport_via ?_ ?_
        (h.ground.eval_call.transport_stack (fun k hk => (frame k hk).symm)) ?_
      budget := h.budget, bodies := h.bodies }
  · intro k hlo hhi
    apply frame k
    have ht := h.ground.eval_call.table_stack
    omega
  · intro lo hi region k hlo hhi
    exact frame k (by have := region.stack_disjoint; omega)
  · intro k hlo hhi
    obtain ⟨b, hb⟩ := h.ground.stack_bytes k hlo hhi
    exact presence k b hb

end Vsa.Sim
