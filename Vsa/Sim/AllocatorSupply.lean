import Vsa.Sim.ExecAllocatorAt

open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine Vsa.Logic

namespace Vsa.Sim

/-- A child also runs under any larger request ceiling. -/
theorem EvalAllocatorAt.request_mono
    {N : NativeAddrs} {st st' : Vsa.While.St} {d env : Nat} {e : Expr} {v : Value}
    {cost request larger : Nat}
    (ih : EvalAllocatorAt N st d env e st' v cost request) (le : request ≤ larger) :
    EvalAllocatorAt N st d env e st' v cost larger where
  run := fun g A SL gpv headroom maxReq M L hrequest =>
    ih.run g A SL gpv headroom maxReq M L (Nat.le_trans le hrequest)

/-- Statement execution also accepts a larger request ceiling. -/
theorem ExecAllocatorAt.request_mono
    {N : NativeAddrs} {st st' : Vsa.While.St} {d env : Nat} {s : Stmt} {status : Status}
    {cost request larger : Nat}
    (ih : ExecAllocatorAt N st d env s st' status cost request) (le : request ≤ larger) :
    ExecAllocatorAt N st d env s st' status cost larger where
  run := fun g A SL gpv headroom maxReq M L hrequest =>
    ih.run g A SL gpv headroom maxReq M L (Nat.le_trans le hrequest)

/-- Source induction supplies an evaluator cost and request ceiling before machine entry.
The physical binary supplies native identity; the source store invariant supplies
closure bounds. Every selected contract preserves all caller reserves. -/
structure EvalAllocatorSupply (st : Vsa.While.St) (d env : Nat) (e : Expr)
    (st' : Vsa.While.St) (v : Value) : Prop where
  provide : ∀ (N : NativeAddrs), (∀ f h, N.addr f = N.addr h → f = h) →
    StoreClosuresBounded st.store →
    ∃ cost request, EvalAllocatorAt N st d env e st' v cost request

/-- Source induction supplies statement resources before machine entry.
Native identity and initial closure bounds come from the same run as the evaluator. -/
structure ExecAllocatorSupply (st : Vsa.While.St) (d env : Nat) (s : Stmt)
    (st' : Vsa.While.St) (status : Status) : Prop where
  provide : ∀ (N : NativeAddrs), (∀ f h, N.addr f = N.addr h → f = h) →
    StoreClosuresBounded st.store →
    ∃ cost request, ExecAllocatorAt N st d env s st' status cost request

/-- Reuse an existing evaluator supplier with its proved cost and request ceiling. -/
theorem EvalAllocatorSupply.ofIH
    {st st' : Vsa.While.St} {d env : Nat} {e : Expr} {v : Value} {cost request : Nat}
    (ih : EvalAllocatorIH st d env e st' v cost request) :
    EvalAllocatorSupply st d env e st' v where
  provide := fun N _ _ => ⟨cost, request, ih.at N⟩

/-- Reuse an existing statement supplier with its proved cost and request ceiling. -/
theorem ExecAllocatorSupply.ofIH
    {st st' : Vsa.While.St} {d env : Nat} {s : Stmt} {status : Status} {cost request : Nat}
    (ih : ExecAllocatorIH st d env s st' status cost request) :
    ExecAllocatorSupply st d env s st' status where
  provide := fun N _ _ => ⟨cost, request, ih.at N⟩

#print axioms EvalAllocatorAt.request_mono
#print axioms ExecAllocatorAt.request_mono
#print axioms EvalAllocatorSupply.ofIH
#print axioms ExecAllocatorSupply.ofIH

end Vsa.Sim
