import Vsa.Sim.MemcpyCopyWordMemory

namespace Vsa.Sim.MemcpyCopy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc Vsa.Logic

def bulkLoads (m : Mem) (src : Nat) : List (List (BitVec 8)) :=
  [EvalChildArm.wordLds8 m src, EvalChildArm.wordLds8 m (src+8),
   EvalChildArm.wordLds8 m (src+16), EvalChildArm.wordLds8 m (src+24),
   EvalChildArm.wordLds8 m (src+32), EvalChildArm.wordLds8 m (src+40),
   EvalChildArm.wordLds8 m (src+48), EvalChildArm.wordLds8 m (src+56),
   EvalChildArm.wordLds8 m (src+64)]

/-- Store order of the actual 72-byte loop, including its early ninth word. -/
def bulkLog (dst : Nat) (lds : List (List (BitVec 8))) : List WEntry :=
  [(dst, 8, bytesVal .ld (lds.getD 0 [])),
   (dst+8, 8, bytesVal .ld (lds.getD 1 [])),
   (dst+64, 8, bytesVal .ld (lds.getD 8 [])),
   (dst+16, 8, bytesVal .ld (lds.getD 2 [])),
   (dst+24, 8, bytesVal .ld (lds.getD 3 [])),
   (dst+32, 8, bytesVal .ld (lds.getD 4 [])),
   (dst+40, 8, bytesVal .ld (lds.getD 5 [])),
   (dst+48, 8, bytesVal .ld (lds.getD 6 [])),
   (dst+56, 8, bytesVal .ld (lds.getD 7 []))]

theorem bulkLoads_at (m : Mem) (src word : Nat) (bound : word < 9) :
    (bulkLoads m src).getD word [] = EvalChildArm.wordLds8 m (src + 8*word) := by
  match word, bound with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ => simp [bulkLoads]

private theorem logWordByte (m : Mem) (left right : List WEntry) (dst k : Nat)
    (bytes : List (BitVec 8)) (bound : k < 8) (outside : OutLRange right dst 8) :
    (writeLog m (left ++ (dst, 8, bytesVal .ld bytes) :: right))[dst+k]? =
      some (bytes.getD k 0#8) := by
  rw [writeLog_append]
  change (writeLog (writeMap8 (writeLog m left) dst (sdData_val (bytesVal .ld bytes))) right)[dst+k]? = _
  rw [writeLog_out _ right _ (outL_of_range outside (by omega) (by omega))]
  exact writeMap8_ld_byte _ _ _ _ bound

/-- Every word reads back from the actual store order. -/
theorem bulkLog_read (m : Mem) (dst word k : Nat) (lds : List (List (BitVec 8)))
    (wordBound : word < 9) (byteBound : k < 8) :
    (writeLog m (bulkLog dst lds))[dst + 8*word + k]? = some ((lds.getD word []).getD k 0#8) := by
  let pos := if word < 2 then word else if word = 8 then 2 else word+1
  have split : bulkLog dst lds = (bulkLog dst lds).take pos ++
      (dst + 8*word, 8, bytesVal .ld (lds.getD word [])) :: (bulkLog dst lds).drop (pos+1) := by
    dsimp only [pos]
    match word, wordBound with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ => rfl
  rw [split]
  apply logWordByte _ _ _ _ _ _ byteBound
  dsimp only [pos]
  match word, wordBound with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ =>
    simp [bulkLog, OutLRange]

/-- The nine stores leave every byte outside their 72-byte window untouched. -/
theorem bulkLog_outside (m : Mem) (dst : Nat) (lds : List (List (BitVec 8)))
    (a : Nat) (outside : a < dst ∨ dst+72 ≤ a) :
    (writeLog m (bulkLog dst lds))[a]? = m[a]? := by
  apply writeLog_out
  simp only [bulkLog, OutL, and_true]
  omega

/-- The actual nine-word copy extends the copied prefix by 72 bytes. -/
theorem storeBulk {dst src : BitVec 64} {n i : Nat} {bs : Nat → BitVec 8} {m0 mem : Mem}
    (h : MemInv dst src n bs i m0 mem)
    (separate : dst.toNat + n ≤ src.toNat ∨ src.toNat + n ≤ dst.toNat)
    (bound : i+72 ≤ n) :
    MemInv dst src n bs (i+72) m0
      (writeLog mem (bulkLog (dst.toNat + i) (bulkLoads mem (src.toNat + i)))) := by
  apply advance h separate bound
  · intro k lower upper
    have wordBound : (k - i)/8 < 9 := by omega
    have byteBound : (k - i)%8 < 8 := Nat.mod_lt _ (by decide)
    rw [show dst.toNat + k = (dst.toNat + i) + 8*((k - i)/8) + (k - i)%8 by omega,
      bulkLog_read _ _ _ _ _ wordBound byteBound,
      bulkLoads_at _ _ _ wordBound, wordBytes_at _ _ _ byteBound,
      show src.toNat + i + 8*((k - i)/8) + (k - i)%8 = src.toNat + k by omega,
      h.src_intact k lower (by omega)]
    rfl
  · intro a outside
    exact bulkLog_outside _ _ _ _ outside

/-- Each word store preserves the instruction image. -/
private theorem loadedAtWord (m : Mem) (a : Nat) (value : BitVec 64)
    (loaded : Code.MemcpyLoaded m) (outside : a+8 ≤ 0x80006bc8 ∨ 0x80006cf0 ≤ a) :
    Code.MemcpyLoaded (writeMap8 m a (sdData_val value)) := by
  unfold writeMap8
  repeat' apply loaded_insert _ _ _ (by omega)
  exact loaded

theorem loadedBulk (m : Mem) (dst : Nat) (lds : List (List (BitVec 8)))
    (loaded : Code.MemcpyLoaded m) (outside : dst+72 ≤ 0x80006bc8 ∨ 0x80006cf0 ≤ dst) :
    Code.MemcpyLoaded (writeLog m (bulkLog dst lds)) := by
  unfold bulkLog writeLog
  repeat' apply loadedAtWord _ _ _ ?_ (by omega)
  exact loaded

#print axioms storeBulk
#print axioms loadedBulk

end Vsa.Sim.MemcpyCopy
