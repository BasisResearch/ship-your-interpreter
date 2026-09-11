import Vsa.Sim.MemcpyCopyBulkShape
import Vsa.Sim.rows.EnvDefineCallRuns

namespace Vsa.Sim.MemcpyCopy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc Vsa.Logic

def bulkSource (src : BitVec 64) (i word : Nat) : Nat :=
  ((src + BitVec.ofNat 64 i) + sign_extend (m := 64) (BitVec.ofNat 12 (8*word))).toNat

def bulkData (m : Mem) (src : BitVec 64) (i word : Nat) : List (BitVec 8) :=
  EvalChildArm.wordLds8 m (src.toNat + i + 8*word)

def bulkFirst (dst : BitVec 64) (i : Nat) : Nat :=
  ((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0#12)).toNat

def bulkDest (dst : BitVec 64) (i word : Nat) : Nat :=
  (((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x048#12)) +
    sign_extend (m := 64) (BitVec.ofNat 12 (4024+8*word))).toNat

/-- Access facts for the nine loads and nine stores in one bulk iteration. -/
structure BulkAccess (dst src : BitVec 64) (i : Nat) (m : Mem) : Prop where
  reads : ∀ word, word < 9 →
    (0x80000000 ≤ bulkSource src i word ∧ bulkSource src i word + 8 ≤ 0x100000000 ∧
      (bulkSource src i word + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ bulkSource src i word)) ∧
    LPins8 m (bulkSource src i word) (bulkData m src i word)
  firstStore : 0x80000000 ≤ bulkFirst dst i ∧ bulkFirst dst i + 8 ≤ 0x100000000 ∧
    tohostAddr + 16 ≤ bulkFirst dst i ∧ bulkFirst dst i % 8 = 0
  lastRead : (0x80000000 ≤ bulkSource src i 8 ∧ bulkSource src i 8 + 8 ≤ 0x100000000 ∧
      (bulkSource src i 8 + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ bulkSource src i 8)) ∧
    LPins8 (writeMap8 m (bulkFirst dst i) (sdData_val (bytesVal .ld (bulkData m src i 0))))
      (bulkSource src i 8) (bulkData m src i 8)
  stores : ∀ word, word < 9 →
    0x80000000 ≤ bulkDest dst i word ∧ bulkDest dst i word + 8 ≤ 0x100000000 ∧
    tohostAddr + 16 ≤ bulkDest dst i word ∧ bulkDest dst i word % 8 = 0

/-- The owned copy state supplies all bulk access facts. -/
theorem bulkAccess {dst src r : BitVec 64} {n i : Nat} {bs : Nat → BitVec 8} {m0 : Mem}
    {before : Config} (h : BulkState dst src r n i bs m0 before)
    (remaining : i+72 ≤ 8*(n/8)) : BulkAccess dst src i before.σ.mem := by
  have dstBound : dst.toNat + i + 72 < 2^64 := by have := h.regions.dst_hi; omega
  have srcBound : src.toNat + i + 72 < 2^64 := by have := h.regions.src_hi; omega
  let source (word : Nat) :=
    ((src + BitVec.ofNat 64 i) + sign_extend (m := 64) (BitVec.ofNat 12 (8*word))).toNat
  let data (word : Nat) := EvalChildArm.wordLds8 before.σ.mem (src.toNat + i + 8*word)
  have reads (word : Nat) (bound : word < 9) :
      (0x80000000 ≤ source word ∧ source word + 8 ≤ 0x100000000 ∧
        (source word + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ source word)) ∧
      LPins8 before.σ.mem (source word) (data word) := by
    dsimp only [source]
    rw [bulkLoadAddress src i word bound srcBound]
    refine ⟨⟨by have := h.regions.src_lo; omega, by have := h.regions.src_hi; omega,
      by have := h.regions.src_win; omega⟩, ?_⟩
    simp [LPins8, data, EvalChildArm.wordLds8]
  let firstAddr := ((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0#12)).toNat
  have firstNat : firstAddr = dst.toNat + i := by
    simpa only [Nat.mul_zero, Nat.add_zero] using bulkLoadAddress dst i 0 (by decide) dstBound
  have firstStore : 0x80000000 ≤ firstAddr ∧ firstAddr + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ firstAddr ∧ firstAddr % 8 = 0 := by
    rw [firstNat]
    exact ⟨by have := h.regions.dst_lo; omega, by have := h.regions.dst_hi; omega,
      by have := h.regions.dst_win; omega, by have := h.align; have := h.offset_align; omega⟩
  let stored := writeMap8 before.σ.mem firstAddr (sdData_val (bytesVal .ld (data 0)))
  have lastRead : (0x80000000 ≤ source 8 ∧ source 8 + 8 ≤ 0x100000000 ∧
      (source 8 + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ source 8)) ∧
      LPins8 stored (source 8) (data 8) := by
    refine ⟨(reads 8 (by decide)).1, lpins8_of_agree ?_ (reads 8 (by decide)).2⟩
    intro k bound
    dsimp only [stored, source]
    rw [firstNat, bulkLoadAddress src i 8 (by decide) srcBound]
    exact getElem?_writeMap8_out _ _ _ _ (by have := h.regions.disjoint; omega)
  let dest (word : Nat) :=
    (((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x048#12)) +
      sign_extend (m := 64) (BitVec.ofNat 12 (4024+8*word))).toNat
  have stores (word : Nat) (bound : word < 9) :
      0x80000000 ≤ dest word ∧ dest word + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ dest word ∧ dest word % 8 = 0 := by
    dsimp only [dest]
    rw [bulkStoreAddress dst i word bound dstBound]
    exact ⟨by have := h.regions.dst_lo; omega, by have := h.regions.dst_hi; omega,
      by have := h.regions.dst_win; omega, by have := h.align; have := h.offset_align; omega⟩
  exact { reads := reads, firstStore := firstStore, lastRead := lastRead, stores := stores }

#print axioms bulkAccess

end Vsa.Sim.MemcpyCopy
