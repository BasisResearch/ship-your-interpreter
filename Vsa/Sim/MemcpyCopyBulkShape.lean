import Vsa.Sim.MemcpyCopyBulkMemory
import Vsa.Sim.MemcpyCopySegments
import Vsa.Sim.MemcpySpec4

namespace Vsa.Sim.MemcpyCopy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc Vsa.Logic

def bulkSeg (more : Bool) : List BBlock :=
  if more then memcpyX6c60TSeg else memcpyX6c60FSeg ++ memcpyX6cb8Seg

def bulkRegs (dst src r : BitVec 64) (n i : Nat) : GRegs :=
  [(11, src + BitVec.ofNat 64 i), (14, dst + BitVec.ofNat 64 i),
   (12, dst + BitVec.ofNat 64 (8*(n/8))), (15, 64#64),
   (17, dst + BitVec.ofNat 64 n), (10, dst), (1, r)]

structure BulkState (dst src r : BitVec 64) (n i : Nat) (bs : Nat → BitVec 8)
    (m0 : Mem) (c : Config) : Prop extends State dst src r n i bs m0 c where
  pc : c.σ.regs.get? Register.PC =
    some (if i+72 ≤ 8*(n/8) then 0x80006c60#64 else 0x80006bfc#64)
  a1 : c.σ.regs.get? Register.x11 = some (src + BitVec.ofNat 64 i)
  a2 : c.σ.regs.get? Register.x12 = some (dst + BitVec.ofNat 64 (8*(n/8)))
  a4 : c.σ.regs.get? Register.x14 = some (dst + BitVec.ofNat 64 i)
  a5 : c.σ.regs.get? Register.x15 = some 64#64
  a7 : c.σ.regs.get? Register.x17 = some (dst + BitVec.ofNat 64 n)
  align : dst.toNat % 8 = 0
  offset_align : i % 8 = 0
  word_bound : i ≤ 8*(n/8)

theorem bulkIncrement (base : BitVec 64) (i : Nat) :
    (base + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x048#12) =
      base + BitVec.ofNat 64 (i+72) := by
  rw [show sign_extend (m := 64) (0x048#12) = BitVec.ofNat 64 72 from rfl,
    BitVec.add_assoc, ← BitVec.ofNat_add]

theorem bulkLoadAddress (base : BitVec 64) (i word : Nat) (wordBound : word < 9)
    (bound : base.toNat + i + 72 < 2^64) :
    ((base + BitVec.ofNat 64 i) + sign_extend (m := 64) (BitVec.ofNat 12 (8*word))).toNat =
      base.toNat + i + 8*word := by
  have immediate : sign_extend (m := 64) (BitVec.ofNat 12 (8*word)) = BitVec.ofNat 64 (8*word) := by
    match word, wordBound with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ => decide
  rw [immediate, BitVec.add_assoc, ← BitVec.ofNat_add,
    ptr_toNat base (i+8*word) (by omega)]
  omega

theorem bulkStoreAddress (base : BitVec 64) (i word : Nat) (wordBound : word < 9)
    (bound : base.toNat + i + 72 < 2^64) :
    (((base + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x048#12)) +
      sign_extend (m := 64) (BitVec.ofNat 12 (4024+8*word))).toNat =
      base.toNat + i + 8*word := by
  have immediate : sign_extend (m := 64) (0x048#12) +
      sign_extend (m := 64) (BitVec.ofNat 12 (4024+8*word)) =
      BitVec.ofNat 64 (8*word) := by
    match word, wordBound with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ => decide
  rw [BitVec.add_assoc (base + BitVec.ofNat 64 i), immediate,
    BitVec.add_assoc, ← BitVec.ofNat_add, ptr_toNat base (i+8*word) (by omega)]
  omega

/-- The reflected body has exactly the binary's nine-word store log. -/
theorem bulkLogExact (dst src r : BitVec 64) (n i : Nat) (m : Mem)
    (more : Bool) (bound : dst.toNat + i + 72 < 2^64) :
    (evalBlocks (bulkSeg more)
      (SegEvalState.init (bulkRegs dst src r n i) (bulkLoads m (src.toNat + i)))).log =
      bulkLog (dst.toNat + i) (bulkLoads m (src.toNat + i)) := by
  let lds := bulkLoads m (src.toNat + i)
  have first : ((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0#12)).toNat = dst.toNat + i := by
    simpa using bulkLoadAddress dst i 0 (by decide) bound
  have next := bulkStoreAddress dst i
  cases more <;>
    change
      [(((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0#12)).toNat, 8, bytesVal .ld (lds.getD 0 [])),
       ((((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x048#12)) + sign_extend (m := 64) (0xfc0#12)).toNat, 8, bytesVal .ld (lds.getD 1 [])),
       ((((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x048#12)) + sign_extend (m := 64) (0xff8#12)).toNat, 8, bytesVal .ld (lds.getD 8 [])),
       ((((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x048#12)) + sign_extend (m := 64) (0xfc8#12)).toNat, 8, bytesVal .ld (lds.getD 2 [])),
       ((((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x048#12)) + sign_extend (m := 64) (0xfd0#12)).toNat, 8, bytesVal .ld (lds.getD 3 [])),
       ((((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x048#12)) + sign_extend (m := 64) (0xfd8#12)).toNat, 8, bytesVal .ld (lds.getD 4 [])),
       ((((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x048#12)) + sign_extend (m := 64) (0xfe0#12)).toNat, 8, bytesVal .ld (lds.getD 5 [])),
       ((((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x048#12)) + sign_extend (m := 64) (0xfe8#12)).toNat, 8, bytesVal .ld (lds.getD 6 [])),
       ((((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x048#12)) + sign_extend (m := 64) (0xff0#12)).toNat, 8, bytesVal .ld (lds.getD 7 []))] = bulkLog (dst.toNat + i) lds
  all_goals
    rw [first, next 1 (by decide) bound, next 8 (by decide) bound,
      next 2 (by decide) bound, next 3 (by decide) bound, next 4 (by decide) bound,
      next 5 (by decide) bound, next 6 (by decide) bound, next 7 (by decide) bound]
    rfl

#print axioms bulkLogExact

end Vsa.Sim.MemcpyCopy
