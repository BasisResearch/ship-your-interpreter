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

/-- The read window of the shared byte set at the boundary (REVIEW.md P7, user
decision 2026-09-25): every shared byte is RAM with the word loop's 8-byte
slack below the RAM top, its window avoids the 16 HTIF bytes at `tohostAddr`,
and it is outside the stack. Unlike `SharedGeom` it admits the fixed image
below `tohostAddr`: the natives' value names are `.rodata` literals. This is
exactly what the Iris route's string reads consume (`ReadOK`, `SharedWin`). -/
structure SharedReadWin (shared : Nat → Prop) (SL : StackLayout) : Prop where
  ram : ∀ k, shared k → 0x80000000 ≤ k ∧ k + 8 ≤ 0x100000000
  htif : ∀ k, shared k → k + 8 ≤ tohostAddr ∨ tohostAddr + 16 ≤ k
  stack : ∀ k, shared k → k < SL.lo ∨ SL.hi ≤ k

/-- The above-image geometry is a special case. -/
theorem SharedGeom.toReadWin {shared : Nat → Prop} {SL : StackLayout}
    (h : SharedGeom shared SL) : SharedReadWin shared SL where
  ram := fun k hk => by have := h.ram k hk; omega
  htif := fun k hk => Or.inr (h.htif k hk)
  stack := h.stack

end Vsa.Sim
