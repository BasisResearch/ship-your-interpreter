import Vsa.Sim.JmpSpec
import Vsa.Sim.SegFrameFacts
import Vsa.Sim.ValueTruthySpec

open LeanRV64DExecutable.Functions
open Vsa.MemRepr

namespace Vsa.Sim

/-- One owned word read supplies both reflected memory facts and its loaded value. -/
structure WordLoadFacts (m : Mem) (L : GRegs) (a : MInstr)
    (v : BitVec 64) (bs : List (BitVec 8)) : Prop where
  facts : MemFacts m L bs a
  value : bytesVal .ld bs = v

/-- The byte witness is obtained once from the owned complete word. -/
theorem wordLoadFacts_of_read64 (m : Mem) (L : GRegs) (a : MInstr) (v : BitVec 64)
    (hk : a.kind = .ld)
    (hlo : 0x80000000 ≤ (eaddrM a L).toNat)
    (hhi : (eaddrM a L).toNat + 8 ≤ 0x100000000)
    (hht : (eaddrM a L).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (eaddrM a L).toNat)
    (hread : read64 m (eaddrM a L).toNat = some v.toNat) :
    ∃ bs, WordLoadFacts m L a v bs := by
  obtain ⟨b0,b1,b2,b3,b4,b5,b6,b7,p0,p1,p2,p3,p4,p5,p6,p7,hval⟩ :=
    ld_readback_jmp m (eaddrM a L).toNat v hread
  exact ⟨[b0,b1,b2,b3,b4,b5,b6,b7],
    memFacts_ld_frame m L a b0 b1 b2 b3 b4 b5 b6 b7 hk hlo hhi hht
      (lpin_of_present p0) (lpin_of_present p1)
      (lpin_of_present p2) (lpin_of_present p3)
      (lpin_of_present p4) (lpin_of_present p5)
      (lpin_of_present p6) (lpin_of_present p7), hval⟩

#print axioms wordLoadFacts_of_read64

/-- Total words depend only on their own byte window. -/
theorem bytesT_agree {m m' : Mem} (a width : Nat)
    (h : ∀ j, j < width → m[a + j]? = m'[a + j]?) :
    bytesT m a width = bytesT m' a width := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro k hk
  rw [getLsbD_bytesT m width a k hk, getLsbD_bytesT m' width a k hk,
    h (k / 8) (by omega)]

/-- Preserve a total four-byte word through its actual byte frame. -/
theorem bytesT4_agree {m m' : Mem} (a : Nat)
    (h : ∀ j, j < 4 → m[a + j]? = m'[a + j]?) :
    bytesT4 m a = bytesT4 m' a := by
  rw [← bytesT_four_eq, ← bytesT_four_eq]
  exact bytesT_agree a 4 h

/-- Preserve a total eight-byte word through its actual byte frame. -/
theorem bytesT8_agree {m m' : Mem} (a : Nat)
    (h : ∀ j, j < 8 → m[a + j]? = m'[a + j]?) :
    bytesT8 m a = bytesT8 m' a := by
  rw [← bytesT_eight_eq, ← bytesT_eight_eq]
  exact bytesT_agree a 8 h

/-- An owned eight-byte word determines the natural value of the total read. -/
theorem bytesT8_toNat_of_read64 {m : Mem} {a n : Nat}
    (h : read64 m a = some n) : (bytesT8 m a).toNat = n := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7,
    e0, e1, e2, e3, e4, e5, e6, e7, hv⟩ := read64_bytes m a n h
  simp only [bytesT8, e0, e1, e2, e3, e4, e5, e6, e7, Option.getD_some]
  rw [word8_toNat_recon]
  exact hv

/-- An owned complete word determines the total load value. -/
theorem load64_eq_of_read64 {m : Mem} {a : Nat} {v : BitVec 64}
    (h : read64 m a = some v.toNat) :
    (sign_extend (m := 64) (bytesT8 m a : BitVec (8 * 8)) : BitVec 64) = v := by
  rw [sext64_id_jmp]
  exact BitVec.eq_of_toNat_eq (bytesT8_toNat_of_read64 h)

/-- An owned four-byte word determines the total read value. -/
theorem bytesT4_of_read32 {m : Mem} {a : Nat} {v : BitVec 32}
    (h : read32 m a = some v.toNat) : bytesT4 m a = v := by
  obtain ⟨b0, b1, b2, b3, e0, e1, e2, e3, hv⟩ := read32_bytes m a v.toNat h
  simp only [bytesT4, e0, e1, e2, e3, Option.getD_some]
  apply BitVec.eq_of_toNat_eq
  rw [word_toNat_recon]
  exact hv

#print axioms bytesT_agree
#print axioms bytesT4_agree
#print axioms bytesT8_agree
#print axioms bytesT8_toNat_of_read64
#print axioms load64_eq_of_read64
#print axioms bytesT4_of_read32
end Vsa.Sim
