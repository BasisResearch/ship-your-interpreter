import Vsa.Alloc
import Vsa.Sim.InitValues

open Vsa.Alloc

namespace Vsa.Sim

structure SharedReadWin (shared : Nat → Prop) (SL : StackLayout) : Prop where
  ram : ∀ k, shared k → 0x80000000 ≤ k ∧ k + 8 ≤ 0x88000000
  htif : ∀ k, shared k → k + 8 ≤ tohostAddr ∨ tohostAddr + 16 ≤ k
  stack : ∀ k, shared k → k < SL.lo ∨ SL.hi ≤ k

end Vsa.Sim
