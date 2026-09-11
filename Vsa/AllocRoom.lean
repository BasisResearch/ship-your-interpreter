import Vsa.AllocResource

namespace Vsa.Sim

open Vsa.MemRepr Vsa.RuntimeRepr

/-- Concrete placement for the fixed allocator's top-chunk split. The global
invariant must separately supply coherent bins, readable metadata, and code. -/
structure TopChunkRoom (A : Arena) (m : Mem) (exts : List (Nat × Nat))
    (n top bytes : Nat) : Prop where
  request_fits : physSize n < 2^31
  top_pointer : read64 m 0x8001ad20 = some top
  size_header : read64 m (top + 8) = some (bytes + 1)
  top_aligned : top % 16 = 0
  size_aligned : bytes % 16 = 0
  arena : A.contains top bytes
  addressable : top + bytes ≤ 0x100000000
  remainder : physSize n + 32 ≤ bytes
  disjoint : ∀ e ∈ exts, top + bytes ≤ e.1 ∨ e.1 + e.2 ≤ top

/-- A concrete free top chunk can accommodate this request. This predicate
does not assert successful execution or follow from numeric credit alone. -/
def AllocationRoom (A : Arena) (m : Mem) (exts : List (Nat × Nat)) (n : Nat) : Prop :=
  ∃ top bytes, TopChunkRoom A m exts n top bytes

/-- The user pointer selected by a top split is aligned and nonzero. -/
theorem TopChunkRoom.pointer {A : Arena} {m : Mem} {exts : List (Nat × Nat)}
    {n top bytes : Nat} (h : TopChunkRoom A m exts n top bytes) :
    top + 16 ≠ 0 ∧ (top + 16) % 16 = 0 := by
  have := h.top_aligned
  omega

/-- The requested payload fits inside the represented arena. -/
theorem TopChunkRoom.payload {A : Arena} {m : Mem} {exts : List (Nat × Nat)}
    {n top bytes : Nat} (h : TopChunkRoom A m exts n top bytes) :
    A.contains (top + 16) n := by
  have hn := physSize_ge n
  have hr := h.remainder
  have ha := h.arena
  unfold Arena.contains at ha ⊢
  omega

/-- The requested payload is disjoint from every live extent. -/
theorem TopChunkRoom.payload_disjoint {A : Arena} {m : Mem}
    {exts : List (Nat × Nat)} {n top bytes : Nat}
    (h : TopChunkRoom A m exts n top bytes) (e : Nat × Nat) (he : e ∈ exts) :
    top + 16 + n ≤ e.1 ∨ e.1 + e.2 ≤ top + 16 := by
  have hn := physSize_ge n
  have hr := h.remainder
  have hd := h.disjoint e he
  omega

#print axioms TopChunkRoom.pointer
#print axioms TopChunkRoom.payload
#print axioms TopChunkRoom.payload_disjoint

end Vsa.Sim
