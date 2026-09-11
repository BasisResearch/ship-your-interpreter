import Vsa.AllocReserve
import Vsa.Alloc
import Vsa.Sim.ReprSurvival

namespace Vsa.Sim

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

/-- Retain placement from byte agreement on its two metadata words. -/
theorem AllocationReserve.transport_bytes {A : Arena} {m m' : Mem}
    {exts : List (Nat × Nat)} {maxReq credits : Nat} {P : Nat → Prop}
    (h : AllocationReserve A m exts maxReq credits) (agreement : AgreeP P m m')
    (global : ∀ k < 8, P (0x8001ad20 + k))
    (header : ∀ top bytes, TopChunkReserve A m exts maxReq credits top bytes →
      ∀ k < 8, P (top + 8 + k)) : AllocationReserve A m' exts maxReq credits :=
  h.transport (read64_agreeP agreement global)
    (fun top bytes reserve => read64_agreeP agreement (header top bytes reserve))

/-- The top header lies in the arena, outside every live payload. -/
theorem TopChunkReserve.header_geometry {A : Arena} {m : Mem}
    {exts : List (Nat × Nat)} {maxReq credits top bytes k : Nat}
    (h : TopChunkReserve A m exts maxReq credits top bytes) (hk : k < 8) :
    A.lo ≤ top + 8 + k ∧ top + 8 + k < A.hi ∧
      ∀ e ∈ exts, ¬ (e.1 ≤ top + 8 + k ∧ top + 8 + k < e.1 + e.2) := by
  have size := physSize_min maxReq
  have remainder := h.chunk.remainder
  have arena := h.chunk.arena
  unfold Arena.contains at arena
  refine ⟨by omega, by omega, ?_⟩
  intro e he
  have disjoint := h.chunk.disjoint e he
  omega

/-- Actual stack writes preserve placement. Global-slot separation is a
linker/layout obligation independent of the live arena's stack separation. -/
theorem AllocationReserve.after_stack {A : Arena} {SL : StackLayout} {m m' : Mem}
    {exts : List (Nat × Nat)} {maxReq credits : Nat}
    (h : AllocationReserve A m exts maxReq credits)
    (agreement : ∀ a, ¬ (SL.lo ≤ a ∧ a < SL.hi) → m[a]? = m'[a]?)
    (global : ∀ k < 8, ¬ (SL.lo ≤ 0x8001ad20 + k ∧ 0x8001ad20 + k < SL.hi))
    (separate : A.hi ≤ SL.lo ∨ SL.hi ≤ A.lo) :
    AllocationReserve A m' exts maxReq credits := by
  apply h.transport_bytes agreement global
  intro top bytes reserve k hk
  have geometry := reserve.header_geometry hk
  rcases separate with above | below <;> omega

/-- Writes confined to live payloads preserve the free top's metadata.
The concrete heap lower bound must put allocator globals below live storage. -/
theorem AllocationReserve.after_live {A : Arena} {m m' : Mem}
    {exts : List (Nat × Nat)} {maxReq credits : Nat}
    (h : AllocationReserve A m exts maxReq credits)
    (agreement : ∀ a, (∀ e ∈ exts, ¬ (e.1 ≤ a ∧ a < e.1 + e.2)) → m[a]? = m'[a]?)
    (live : ∀ e ∈ exts, A.contains e.1 e.2)
    (globalsBelow : 0x8001ad28 ≤ A.lo) : AllocationReserve A m' exts maxReq credits := by
  apply h.transport_bytes agreement
  · intro k hk e he
    have arena := live e he
    unfold Arena.contains at arena
    omega
  · intro top bytes reserve k hk
    exact (reserve.header_geometry hk).2.2

#print axioms AllocationReserve.transport_bytes
#print axioms TopChunkReserve.header_geometry
#print axioms AllocationReserve.after_stack
#print axioms AllocationReserve.after_live

end Vsa.Sim
