import Vsa.Alloc
import Vsa.Sim.InitValues

open Vsa.Alloc

namespace Vsa.Sim

/-- Geometry of the shared byte set: every shared byte is RAM above the static
image `[0x80000000, 0x8001acf0)` with the word loop's 8-byte slack below the
RAM top, above the HTIF window at `tohostAddr`, and outside the stack. -/
structure SharedGeom (shared : Nat → Prop) (SL : StackLayout) : Prop where
  ram : ∀ k, shared k → 0x8001acf0 ≤ k ∧ k + 8 ≤ 0x100000000
  htif : ∀ k, shared k → tohostAddr + 16 ≤ k
  stack : ∀ k, shared k → k < SL.lo ∨ SL.hi ≤ k

end Vsa.Sim
