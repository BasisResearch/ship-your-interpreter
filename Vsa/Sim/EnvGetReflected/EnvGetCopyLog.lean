import Vsa.Sim.EnvGetReflected.EnvGetSegments
import Vsa.Sim.EnvDefSpec4
import Vsa.Sim.HelperCall
import Vsa.Sim.RuntimeOwnershipCopy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Vsa.MemRepr Vsa.RuntimeRepr

namespace Vsa.Sim.EnvGetReflected
open RuntimeOwnership

/-- The four reads supplied to the generated hit block. Later source reads
must be justified at their actual memories when constructing `ChainFacts`. -/
def copyLoads (m : Mem) (env : BitVec 64) (src : Nat) : List (List (BitVec 8)) :=
  [EvalChildArm.wordLds8 m (env.toNat + 16),
   EvalChildArm.wordLds8 m src,
   EvalChildArm.wordLds8 m (src + 8),
   EvalChildArm.wordLds8 m (src + 16)]

/-- The loaded values determine the copy log independently of the byte witnesses. -/
theorem copy_log_of_loads (m : Mem) (env idx out : BitVec 64) (src : Nat)
    (be b0 b1 b2 : List (BitVec 8)) (hout : out.toNat + 24 < 2^64)
    (h0 : bytesVal .ld b0 = bytesVal .ld (EvalChildArm.wordLds8 m src))
    (h1 : bytesVal .ld b1 = bytesVal .ld (EvalChildArm.wordLds8 m (src + 8)))
    (h2 : bytesVal .ld b2 = bytesVal .ld (EvalChildArm.wordLds8 m (src + 16))) :
    writeLog m (evalBlocks env_getX2c70Seg (SegEvalState.init
      (env_getX2c70L env idx out) [be, b0, b1, b2])).log =
      copy3Log m src out.toNat := by
  change
    writeMap8 (writeMap8 (writeMap8 m
      (out + sign_extend (m := 64) (0x000#12)).toNat
      (sdData_val (bytesVal .ld b0)))
      (out + sign_extend (m := 64) (0x008#12)).toNat
      (sdData_val (bytesVal .ld b1)))
      (out + sign_extend (m := 64) (0x010#12)).toNat
      (sdData_val (bytesVal .ld b2)) = _
  rw [off_ed_00, off_ed_08 out (by omega), off_ed_10 out (by omega), h0, h1, h2]
  rfl

/-- Identify the generated write log with the shared three-word copy. -/
theorem copy_log (m : Mem) (env idx out : BitVec 64) (src : Nat)
    (hout : out.toNat + 24 < 2^64) :
    writeLog m (evalBlocks env_getX2c70Seg (SegEvalState.init
      (env_getX2c70L env idx out) (copyLoads m env src))).log =
      copy3Log m src out.toNat :=
  copy_log_of_loads m env idx out src _ _ _ _ hout rfl rfl rfl

/-- Semantic and ownership observations of the same concrete copied memory. -/
theorem copy_value {m m' : Mem} {N : NativeAddrs}
    {phiC : Vsa.While.Addr → Nat} {shared : Nat → Prop}
    {src dst : Nat} {v : Vsa.While.Value}
    (hmem : m' = copy3Log m src dst)
    (hshared : ∀ k, shared k → ¬ (dst ≤ k ∧ k < dst + 24))
    (hvalue : ValueWordRepr m N phiC src v)
    (howned : ValueOwned m shared src v) :
    ValueWordRepr m' N phiC dst v ∧ ValueOwned m' shared dst v ∧ MemExtends m m' := by
  subst m'
  have ha : AgreeP shared m (copy3Log m src dst) :=
    fun k hk => (copy3_frame m src dst k (hshared k hk)).symm
  exact ⟨valueWordRepr_copy_total_exact (copy3_total m src dst)
      (howned.covered ha) hvalue,
    howned.copy_total (copy3_total m src dst) ha,
    copy3_memExtends m src dst⟩

#print axioms copy_log_of_loads
#print axioms copy_log
#print axioms copy_value

end Vsa.Sim.EnvGetReflected
