import Vsa.Sim.TruthyCopy
import Vsa.Sim.TruthyCopySites
import Vsa.Sim.rows.EvalChildArmWhile
import Vsa.Sim.WhileGeomSuppliers

/-!
# `TruthyCopyWhile` — the while instance of the copy-and-`value_truthy` seam

The descriptor of the while condition's copy (`0x80004050`, reusing the
reflected `execWhileCondCopySeg`) and the confirmation that the parametric
`copyReady_of_exitKit` yields the hand-closed `ExecWhileCondCopyReady`.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

/-- The while condition's copy seam. -/
def whileTruthy : TruthyCopy :=
  { copySeg := execWhileCondCopySeg
    jalPC := 0x8000406c#64
    jalImm := 0x1fe7c0#21 }

theorem whileTruthy_cert : whileTruthy.Cert whileCondArm where
  src_lo := by decide
  chain_ok := by
    change ChainOK 0x80004050#64 [2, 8, 9, 18, 19] execWhileCondCopySeg; decide
  avoid_abi := by change WrChainAvoidAbi execWhileCondCopySeg; decide
  keys_out := by intros; change KeysOK [10, 15, 14, 13, 2, 8, 9, 18, 19]; decide
  ra_out := by intros; change ∀ n ∈ [10, 15, 14, 13, 2, 8, 9, 18, 19], n ≠ 1; decide
  end_pc := by intros; rfl
  a0_out := by intros; rfl
  sp_out := by intros; rfl
  log_eq := by intros; rfl
  jal_tgt := by decide
  ret_clean := by decide
  ret_align := by decide
  jal_site := fun σ i u vmi hG hpc hmi hmem hi =>
    site_8000406c_tc σ i u _ vmi hG hpc hmi hmem rfl hi
  copy_facts := fun m SL esp s0 s1 s2 s3 hcode hlo hhi hram hwin hal =>
    execWhileCondCopy_facts_of_stack m SL esp s0 s1 s2 s3 hcode hlo (by omega) hram hwin hal

/-- **Confirmation.**  The generic parked state is the hand-closed one. -/
theorem TruthyCopy.CopyReady.toWhile
    {gC : (R : Register) → Option (RegisterType R)} {N : NativeAddrs} {φc : Addr → Nat}
    {v : Value} {esp aStmt aInterp aRet aEnv : BitVec 64} {mCopy : Mem}
    {out : Array String} {cfg : Config}
    (h : whileTruthy.CopyReady gC v esp aStmt aInterp aRet aEnv mCopy out cfg) :
    ExecWhileCondCopyReady gC N φc v esp aStmt aInterp aRet aEnv mCopy out cfg where
  good := h.good
  tick := h.tick
  pc := h.pc
  minstret := h.minstret
  mem := h.mem
  out := h.out
  code := h.code
  truthy_loaded := h.truthy_loaded
  header := h.header
  region := h.region
  a0 := h.a0
  ra := h.ra
  sp := h.sp
  s0 := h.s0
  s1 := h.s1
  s2 := h.s2
  s3 := h.s3
  frame := h.frame

#print axioms whileTruthy_cert
#print axioms TruthyCopy.CopyReady.toWhile

end Vsa.Sim
