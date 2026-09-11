import Vsa.AllocRoom

namespace Vsa.Sim

open Vsa.MemRepr Vsa.RuntimeRepr

/-- A top chunk with contiguous storage for the remaining request credits.
The allocator operation must retain this at its actual returned memory. -/
structure TopChunkReserve (A : Arena) (m : Mem) (exts : List (Nat × Nat))
    (maxReq credits top bytes : Nat) : Prop where
  chunk : TopChunkRoom A m exts maxReq top bytes
  capacity : credits * physSize maxReq + 32 ≤ bytes

/-- Concrete placement for every remaining credit. Zero credits require no
free chunk. Initialisation and allocating operations must supply this record. -/
structure AllocationReserve (A : Arena) (m : Mem) (exts : List (Nat × Nat))
    (maxReq credits : Nat) : Prop where
  available : 0 < credits → ∃ top bytes, TopChunkReserve A m exts maxReq credits top bytes

theorem TopChunkRoom.request_mono {A : Arena} {m : Mem} {exts : List (Nat × Nat)}
    {n maxReq top bytes : Nat} (h : TopChunkRoom A m exts maxReq top bytes)
    (hn : n ≤ maxReq) : TopChunkRoom A m exts n top bytes := by
  have size := physSize_mono hn
  exact
    { h with
      request_fits := Nat.lt_of_le_of_lt size h.request_fits
      remainder := Nat.le_trans (Nat.add_le_add_right size 32) h.remainder }

theorem AllocationReserve.zero (A : Arena) (m : Mem) (exts : List (Nat × Nat))
    (maxReq : Nat) : AllocationReserve A m exts maxReq 0 :=
  { available := fun h => False.elim (Nat.not_lt_zero _ h) }

/-- Numeric credit and placement have separate monotonicity proofs. -/
theorem AllocationReserve.mono {A : Arena} {m : Mem} {exts : List (Nat × Nat)}
    {maxReq credits remaining : Nat} (h : AllocationReserve A m exts maxReq credits)
    (hle : remaining ≤ credits) : AllocationReserve A m exts maxReq remaining := by
  refine { available := ?_ }
  intro positive
  obtain ⟨top, bytes, reserve⟩ := h.available (Nat.lt_of_lt_of_le positive hle)
  exact ⟨top, bytes,
    { chunk := reserve.chunk
      capacity := Nat.le_trans
        (Nat.add_le_add_right (Nat.mul_le_mul_right (physSize maxReq) hle) 32)
        reserve.capacity }⟩

/-- The next request consumes placement at its own entry memory and ledger. -/
theorem AllocationReserve.room {A : Arena} {m : Mem} {exts : List (Nat × Nat)}
    {maxReq credits n : Nat} (h : AllocationReserve A m exts maxReq credits)
    (positive : 0 < credits) (bounded : n ≤ maxReq) : AllocationRoom A m exts n := by
  obtain ⟨top, bytes, reserve⟩ := h.available positive
  exact ⟨top, bytes, reserve.chunk.request_mono bounded⟩

/-- Preserve the two concrete metadata words. The caller supplies agreement
from its actual write frame; allocator calls must instead establish a new reserve. -/
theorem AllocationReserve.transport {A : Arena} {m m' : Mem}
    {exts : List (Nat × Nat)} {maxReq credits : Nat}
    (h : AllocationReserve A m exts maxReq credits)
    (topRead : read64 m 0x8001ad20 = read64 m' 0x8001ad20)
    (headerRead : ∀ top bytes, TopChunkReserve A m exts maxReq credits top bytes →
      read64 m (top + 8) = read64 m' (top + 8)) :
    AllocationReserve A m' exts maxReq credits := by
  refine { available := ?_ }
  intro positive
  obtain ⟨top, bytes, reserve⟩ := h.available positive
  exact ⟨top, bytes,
    { chunk :=
        { reserve.chunk with
          top_pointer := topRead.symm.trans reserve.chunk.top_pointer
          size_header := (headerRead top bytes reserve).symm.trans reserve.chunk.size_header }
      capacity := reserve.capacity }⟩

#print axioms TopChunkRoom.request_mono
#print axioms AllocationReserve.zero
#print axioms AllocationReserve.mono
#print axioms AllocationReserve.room
#print axioms AllocationReserve.transport

end Vsa.Sim
