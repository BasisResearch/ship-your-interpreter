import Vsa.Sim.EqAllocatorRecursive
import Vsa.Sim.ExecAllocatorExpr

open LeanRV64DExecutable Vsa Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc
open Vsa.Machine Vsa.Logic

namespace Vsa.Sim

/-- Equality expression statements return normally with the caller's allocator reserve. -/
theorem execAllocatorAt_eqne_fixed (op : EqNeOp)
    {initial : Config} {stmts count : Nat} {inp : BitVec 64} {N : NativeAddrs}
    {initialF initialC : Addr → Nat} {initialArena : Arena} {aLeft : Nat}
    {st middle final : Vsa.While.St} {d env : Nat} {el er : Expr} {vl vr : Value}
    {costL costR maxRequest : Nat}
    (physical : LayoutInstance.InterpRunPhysicalFacts initial stmts count inp N initialArena
      initialF initialC aLeft)
    (leftSem : EvalE st d env el middle vl) (rightSem : EvalE middle d env er final vr)
    (bounded : StoreClosuresBounded st.store)
    (leftIH : EvalAllocatorAt N st d env el middle vl costL maxRequest)
    (rightIH : EvalAllocatorAt N middle d env er final vr costR maxRequest) :
    ExecAllocatorAt N st d env (.expr (.binary op.operator el er)) final .normal
      (costL + costR) maxRequest :=
  execAllocatorAt_expr
    (evalAllocatorAt_eqne_fixed op physical leftSem rightSem bounded leftIH rightIH)

/-- A nested comparison statement executes without child supplier premises. -/
theorem execAllocatorAt_eqne_nested (outer left right : EqNeOp) {N : NativeAddrs}
    (st : Vsa.While.St) (d env : Nat) (a b : Int) (s t : String)
    (native : ∀ f h, N.addr f = N.addr h → f = h)
    (bounded : StoreClosuresBounded st.store) :
    ExecAllocatorAt N st d env
      (.expr (.binary outer.operator
        (.binary left.operator (.int a) (.int b))
        (.binary right.operator (.str s) (.str t)))) st .normal 0 0 :=
  execAllocatorAt_expr (evalAllocatorAt_eqne_nested outer left right st d env a b s t native bounded)

#print axioms execAllocatorAt_eqne_fixed
#print axioms execAllocatorAt_eqne_nested

end Vsa.Sim
