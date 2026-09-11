import Vsa.Sim.BlockAllocator
import Vsa.Sim.ExecSeqAllocatorSupply

namespace Vsa.Sim

open Vsa.While

/-- The block source constructor allocates its scope and runs the owned body. -/
theorem ExecAllocatorSupply.block
    {st final : Vsa.While.St} {d env : Nat} {ss : List Stmt} {status : Status}
    {store' : Store} {inner : Addr}
    (allocation : st.store.allocFrame (some env) = (store', inner))
    (body : ExecSeqAllocatorSupply .blockBody ⟨store', st.out⟩ d inner ss final status) :
    ExecAllocatorSupply st d env (.block ss) final status where
  provide := by
    intro N native bounded
    obtain ⟨cost, request, run⟩ := body.provide trivial N native (StoreClosuresBounded.allocFrame allocation bounded)
    have storeEq : store' = (st.store.allocFrame (some env)).1 :=
      (congrArg Prod.fst allocation).symm
    have innerEq : inner = st.store.frames.size := (congrArg Prod.snd allocation).symm
    subst store' inner
    exact ⟨cost + 1, max 32 request, execAllocatorAt_block run⟩

#print axioms ExecAllocatorSupply.block

end Vsa.Sim
