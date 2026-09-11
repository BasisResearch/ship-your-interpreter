import Vsa.Sim.MemcpyCopyState
import Vsa.Sim.EqNeReprReadback
import Vsa.Sim.EvalChildArm
import Vsa.Sim.MemcpySpec2

namespace Vsa.Sim.MemcpyCopy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc Vsa.Logic

/-- Positional bytes of the existing reflected word load. -/
theorem wordBytes_at (m : Mem) (a k : Nat) (bound : k < 8) :
    (EvalChildArm.wordLds8 m a).getD k 0#8 = (m[a + k]?).getD 0 := by
  match k, bound with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [EvalChildArm.wordLds8]

/-- A loaded and stored word extends the same copied-prefix invariant. -/
theorem storeWord {dst src : BitVec 64} {n i : Nat} {bs : Nat → BitVec 8}
    {m0 mem : Mem} (h : MemInv dst src n bs i m0 mem)
    (separate : dst.toNat + n ≤ src.toNat ∨ src.toNat + n ≤ dst.toNat)
    (bound : i+8 ≤ n) :
    MemInv dst src n bs (i+8) m0
      (writeMap8 mem (dst.toNat + i)
        (sdData_val (bytesVal .ld (EvalChildArm.wordLds8 mem (src.toNat + i))))) := by
  apply advance h separate bound
  · intro k lower upper
    have offset : k - i < 8 := by omega
    rw [show dst.toNat + k = dst.toNat + i+(k - i) by omega,
      writeMap8_ld_byte _ _ _ _ offset, wordBytes_at _ _ _ offset,
      show src.toNat + i+(k - i) = src.toNat + k by omega,
      h.src_intact k lower (by omega)]
    rfl
  · intro a outside
    exact getElem?_writeMap8_out _ _ _ _ outside

/-- The copied word is outside the memcpy instruction image. -/
theorem loadedWord {dst : BitVec 64} {n i : Nat} {mem : Mem} {value : BitVec 64}
    (loaded : Code.MemcpyLoaded mem) (bound : i+8 ≤ n)
    (code : dst.toNat + n ≤ 0x80006bc8 ∨ 0x80006cf0 ≤ dst.toNat) :
    Code.MemcpyLoaded (writeMap8 mem (dst.toNat + i) (sdData_val value)) := by
  unfold writeMap8
  repeat' apply loaded_insert _ _ _ (by omega)
  exact loaded

/-- The small word loop retains both base pointers for its normalization tail. -/
structure WordState (dst src r : BitVec 64) (n start j : Nat) (bs : Nat → BitVec 8)
    (m0 : Mem) (c : Config) : Prop extends State dst src r n (8*j) bs m0 c where
  pc : c.σ.regs.get? Register.PC =
    some (if j < n/8 then 0x80006c08#64 else 0x80006c1c#64)
  a1 : c.σ.regs.get? Register.x11 = some (src + BitVec.ofNat 64 (8*start))
  a2 : c.σ.regs.get? Register.x12 = some (dst + BitVec.ofNat 64 (8*(n/8)))
  a3 : c.σ.regs.get? Register.x13 = some (src + BitVec.ofNat 64 (8*j))
  a4 : c.σ.regs.get? Register.x14 = some (dst + BitVec.ofNat 64 (8*start))
  a5 : c.σ.regs.get? Register.x15 = some (dst + BitVec.ofNat 64 (8*j))
  a7 : c.σ.regs.get? Register.x17 = some (dst + BitVec.ofNat 64 n)
  align : dst.toNat % 8 = 0
  start_lt : start < n/8
  start_le : start ≤ j
  word_bound : j ≤ n/8

#print axioms storeWord
#print axioms loadedWord

end Vsa.Sim.MemcpyCopy
