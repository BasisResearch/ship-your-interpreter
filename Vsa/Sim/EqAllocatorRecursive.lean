import Vsa.Sim.EqAllocatorFixed
import Vsa.Sim.EvalAllocatorLiteral

open LeanRV64DExecutable Vsa Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc
open Vsa.Machine Vsa.Logic

namespace Vsa.Sim

/-- Equality semantics for the same operator and result used by the binary proof. -/
theorem EqNeOp.eval (op : EqNeOp)
    {st middle final : Vsa.While.St} {d env : Nat} {el er : Expr} {vl vr : Value}
    (left : EvalE st d env el middle vl) (right : EvalE middle d env er final vr) :
    EvalE st d env (.binary op.operator el er) final (.bool (op.result vl vr)) :=
  EvalE.binary st d env op.operator el er middle final vl vr (.bool (op.result vl vr))
    left right (by cases op <;> rfl)

/-- Equality returns an owned child contract at the same native addresses.
The fixed binary boundary supplies native identity. Child contracts supply
their allocation costs; the comparison preserves the caller's reserve. -/
theorem evalAllocatorAt_eqne (op : EqNeOp) {N : NativeAddrs}
    {st middle final : Vsa.While.St} {d env : Nat} {el er : Expr} {vl vr : Value}
    {costL costR maxRequest : Nat}
    (native : ∀ f h, N.addr f = N.addr h → f = h)
    (leftSem : EvalE st d env el middle vl) (rightSem : EvalE middle d env er final vr)
    (bounded : StoreClosuresBounded st.store)
    (leftIH : EvalAllocatorAt N st d env el middle vl costL maxRequest)
    (rightIH : EvalAllocatorAt N middle d env er final vr costR maxRequest) :
    EvalAllocatorAt N st d env (.binary op.operator el er) final (.bool (op.result vl vr))
      (costL + costR) maxRequest where
  run := by
    intro g A SL gpv headroom maxReq M L request phiF phiC alloc exts shared reserve
      sp ret dst interp node m0 before entry
    have entry' : EvalAllocatorEntry g N M phiF phiC alloc exts shared
        (costL + (costR + reserve)) st d env (.binary op.operator el er)
        sp ret dst interp node m0 before := by
      simpa only [Nat.add_assoc] using entry
    exact evalEqAllocator_at op L request native leftSem rightSem bounded
      leftIH rightIH before entry'

/-- The physical binary boundary supplies equality's recursive contract. -/
theorem evalAllocatorAt_eqne_fixed (op : EqNeOp)
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
    EvalAllocatorAt N st d env (.binary op.operator el er) final (.bool (op.result vl vr))
      (costL + costR) maxRequest :=
  evalAllocatorAt_eqne op physical.native_injective leftSem rightSem bounded leftIH rightIH

/-- Nested integer and string comparisons execute with no child supplier premises. -/
theorem evalAllocatorAt_eqne_nested (outer left right : EqNeOp) {N : NativeAddrs}
    (st : Vsa.While.St) (d env : Nat) (a b : Int) (s t : String)
    (native : ∀ f h, N.addr f = N.addr h → f = h)
    (bounded : StoreClosuresBounded st.store) :
    EvalAllocatorAt N st d env
      (.binary outer.operator
        (.binary left.operator (.int a) (.int b))
        (.binary right.operator (.str s) (.str t))) st
      (.bool (outer.result (.bool (left.result (.int a) (.int b)))
        (.bool (right.result (.str s) (.str t))))) 0 0 := by
  have leftSem := left.eval (EvalE.int st d env a) (EvalE.int st d env b)
  have rightSem := right.eval (EvalE.str st d env s) (EvalE.str st d env t)
  have leftRun := evalAllocatorAt_eqne left native
    (EvalE.int st d env a) (EvalE.int st d env b) bounded
    ((evalAllocatorIH_int st d env a).at N) ((evalAllocatorIH_int st d env b).at N)
  have rightRun := evalAllocatorAt_eqne right native
    (EvalE.str st d env s) (EvalE.str st d env t) bounded
    ((evalAllocatorIH_str st d env s).at N) ((evalAllocatorIH_str st d env t).at N)
  exact evalAllocatorAt_eqne outer native leftSem rightSem bounded leftRun rightRun

#print axioms EqNeOp.eval
#print axioms evalAllocatorAt_eqne
#print axioms evalAllocatorAt_eqne_fixed
#print axioms evalAllocatorAt_eqne_nested

end Vsa.Sim
