import Vsa.Sim.AllocatorSupply
import Vsa.Sim.EvalAllocatorLiteral
import Vsa.Sim.EvalAllocatorVariable

open LeanRV64DExecutable Vsa Vsa.While

namespace Vsa.Sim

/-- Integer source evaluation supplies its complete allocator contract. -/
theorem EvalAllocatorSupply.int (st : Vsa.While.St) (d env : Nat) (n : Int) :
    EvalAllocatorSupply st d env (.int n) st (.int n) :=
  .ofIH (evalAllocatorIH_int st d env n)

/-- String source evaluation retains ownership of the literal's bytes. -/
theorem EvalAllocatorSupply.str (st : Vsa.While.St) (d env : Nat) (s : String) :
    EvalAllocatorSupply st d env (.str s) st (.str s) :=
  .ofIH (evalAllocatorIH_str st d env s)

/-- Boolean source evaluation supplies its complete allocator contract. -/
theorem EvalAllocatorSupply.bool (st : Vsa.While.St) (d env : Nat) (b : Bool) :
    EvalAllocatorSupply st d env (.bool b) st (.bool b) :=
  .ofIH (evalAllocatorIH_bool st d env b)

/-- Null source evaluation supplies its complete allocator contract. -/
theorem EvalAllocatorSupply.null (st : Vsa.While.St) (d env : Nat) :
    EvalAllocatorSupply st d env .null st .null :=
  .ofIH (evalAllocatorIH_null st d env)

/-- A successful source lookup supplies ownership for any returned value kind. -/
theorem EvalAllocatorSupply.var
    {st : Vsa.While.St} {d env : Nat} {query : String} {v : Value}
    (found : st.store.get? env query = some v) :
    EvalAllocatorSupply st d env (.var query) st v :=
  .ofIH (evalAllocatorIH_var found)

#print axioms EvalAllocatorSupply.int
#print axioms EvalAllocatorSupply.str
#print axioms EvalAllocatorSupply.bool
#print axioms EvalAllocatorSupply.null
#print axioms EvalAllocatorSupply.var

end Vsa.Sim
