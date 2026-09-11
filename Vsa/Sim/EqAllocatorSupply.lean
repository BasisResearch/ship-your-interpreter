import Vsa.Sim.AllocatorSupply
import Vsa.Sim.EqAllocatorStatement

open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine Vsa.Logic

namespace Vsa.Sim

/-- Equality combines independently proved child costs and request ceilings. -/
theorem evalAllocatorAt_eqne_requests (op : EqNeOp) {N : NativeAddrs}
    {st middle final : Vsa.While.St} {d env : Nat} {el er : Expr} {vl vr : Value}
    {costL costR requestL requestR : Nat}
    (native : ∀ f h, N.addr f = N.addr h → f = h)
    (leftSem : EvalE st d env el middle vl) (rightSem : EvalE middle d env er final vr)
    (bounded : StoreClosuresBounded st.store)
    (left : EvalAllocatorAt N st d env el middle vl costL requestL)
    (right : EvalAllocatorAt N middle d env er final vr costR requestR) :
    EvalAllocatorAt N st d env (.binary op.operator el er) final (.bool (op.result vl vr))
      (costL + costR) (max requestL requestR) :=
  evalAllocatorAt_eqne op native leftSem rightSem bounded
    (left.request_mono (Nat.le_max_left ..)) (right.request_mono (Nat.le_max_right ..))

/-- The equality source case derives its resources from both recursive child suppliers. -/
theorem EvalAllocatorSupply.eqne (op : EqNeOp)
    {st middle final : Vsa.While.St} {d env : Nat} {el er : Expr} {vl vr : Value}
    (leftSem : EvalE st d env el middle vl) (rightSem : EvalE middle d env er final vr)
    (left : EvalAllocatorSupply st d env el middle vl)
    (right : EvalAllocatorSupply middle d env er final vr) :
    EvalAllocatorSupply st d env (.binary op.operator el er) final (.bool (op.result vl vr)) where
  provide := by
    intro N native bounded
    obtain ⟨costL, requestL, leftRun⟩ := left.provide N native bounded
    obtain ⟨costR, requestR, rightRun⟩ := right.provide N native
      (storeClosuresBounded_mutual.onEvalE leftSem bounded).1
    exact ⟨costL + costR, max requestL requestR,
      evalAllocatorAt_eqne_requests op native leftSem rightSem bounded leftRun rightRun⟩

/-- The source expression-statement case retains the resources supplied by its child. -/
theorem ExecAllocatorSupply.expr
    {st st' : Vsa.While.St} {d env : Nat} {e : Expr} {v : Value}
    (child : EvalAllocatorSupply st d env e st' v) :
    ExecAllocatorSupply st d env (.expr e) st' .normal where
  provide := by
    intro N native bounded
    obtain ⟨cost, request, run⟩ := child.provide N native bounded
    exact ⟨cost, request, execAllocatorAt_expr run⟩

/-- Match the result selected by the source binary rule to the equality execution. -/
theorem EvalAllocatorSupply.binary_eqne (op : EqNeOp)
    {st middle final : Vsa.While.St} {d env : Nat} {el er : Expr} {vl vr v : Value}
    (leftSem : EvalE st d env el middle vl) (rightSem : EvalE middle d env er final vr)
    (result : binOpSem final.store op.operator vl vr = some v)
    (left : EvalAllocatorSupply st d env el middle vl)
    (right : EvalAllocatorSupply middle d env er final vr) :
    EvalAllocatorSupply st d env (.binary op.operator el er) final v := by
  have selected : v = .bool (op.result vl vr) := by
    cases op <;> exact (Option.some.inj result).symm
  subst v
  exact EvalAllocatorSupply.eqne op leftSem rightSem left right

#print axioms evalAllocatorAt_eqne_requests
#print axioms EvalAllocatorSupply.eqne
#print axioms ExecAllocatorSupply.expr
#print axioms EvalAllocatorSupply.binary_eqne

end Vsa.Sim
