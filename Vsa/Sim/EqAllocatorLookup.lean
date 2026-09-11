import Vsa.Sim.AllocatorSupplyLeaf
import Vsa.Sim.EqAllocatorSupply

open LeanRV64DExecutable Vsa Vsa.While

namespace Vsa.Sim

/-- Comparing two successfully looked-up values supplies the complete owned execution. -/
theorem evalAllocatorSupply_eqne_vars (op : EqNeOp)
    {st : Vsa.While.St} {d env : Nat} {left right : String} {vl vr : Value}
    (foundL : st.store.get? env left = some vl)
    (foundR : st.store.get? env right = some vr) :
    EvalAllocatorSupply st d env (.binary op.operator (.var left) (.var right)) st
      (.bool (op.result vl vr)) :=
  EvalAllocatorSupply.eqne op (EvalE.var st d env left vl foundL)
    (EvalE.var st d env right vr foundR)
    (.var foundL) (.var foundR)

/-- The comparison statement returns normally for all represented operand kinds. -/
theorem execAllocatorSupply_eqne_vars (op : EqNeOp)
    {st : Vsa.While.St} {d env : Nat} {left right : String} {vl vr : Value}
    (foundL : st.store.get? env left = some vl)
    (foundR : st.store.get? env right = some vr) :
    ExecAllocatorSupply st d env (.expr (.binary op.operator (.var left) (.var right)))
      st .normal :=
  .expr (evalAllocatorSupply_eqne_vars op foundL foundR)

#print axioms evalAllocatorSupply_eqne_vars
#print axioms execAllocatorSupply_eqne_vars

end Vsa.Sim
