import Vsa.Alloc
import Vsa.Sim.InitValues

open Vsa.Alloc

namespace Vsa.Sim

/-- The read window of the shared byte set at the boundary (REVIEW.md P7, user
decision 2026-09-25): every shared byte is RAM (below `0x88000000`, with the
word loop's 8-byte slack: everything the loader and boot write lies in RAM,
lane N2), its window avoids the 16 HTIF bytes at `tohostAddr`, and it is
outside the stack. Unlike `SharedGeom` it admits the fixed image
below `tohostAddr`: the natives' value names are `.rodata` literals. This is
exactly what the Iris route's string reads consume (`ReadOK`, `SharedWin`). -/
structure SharedReadWin (shared : Nat → Prop) (SL : StackLayout) : Prop where
  ram : ∀ k, shared k → 0x80000000 ≤ k ∧ k + 8 ≤ 0x88000000
  htif : ∀ k, shared k → k + 8 ≤ tohostAddr ∨ tohostAddr + 16 ≤ k
  stack : ∀ k, shared k → k < SL.lo ∨ SL.hi ≤ k

end Vsa.Sim
