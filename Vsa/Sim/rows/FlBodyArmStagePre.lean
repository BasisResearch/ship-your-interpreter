import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.BridgeSeg
import Vsa.Sim.ArmSegSplitNonEval

/-!
# `FlBodyArmStagePre` — the exec-for-loop-body-arm-head → `ExecStmtPreBundle`
staging field (Wave 43, non-eval side)

The `flBody` field of `NonEvalChildStages` (`ArmSegSplitNonEval.lean`) is a STAGING
residual: from `FEntryC cnd step b` (the for-loop re-entry) plus `ForCond` (the
cond held), run the for-body arm head and land at `ExecStmtPreBundle b` — the
recursive `jal exec_stmt` on the loop BODY child statement.

The arm head (from `experiments/disasm.txt`, the for-body at `0x800042a8`, the
`value_truthy`-nonzero fallthrough of the for-cond block that loops back via
`bne a0,a5,0x8000425c`) is:

    800042a8:  ld a1,32(s0)   -- for-body stmt node ptr (from for-node)
    800042ac:  mv a3,s2       -- a3 := interp* (addi x13,x18,0)
    800042b0:  mv a2,s3       -- a2 := env     (addi x12,x19,0)
    800042b4:  mv a0,s1       -- a0 := ret     (addi x10,x9,0)
    800042b8:  jal exec_stmt  -- 0x80003fe0, link 0x800042bc

a STRAIGHT-LINE-then-`jal exec_stmt` span — exactly the `stmtWhileBody` shape (the
loop-body `ld` reads offset 32 here vs 16 there).  Per the CLAUDE.md discipline
table, the body `0x800042a8 → 0x800042b4` is a `#derive_case` seg and the
`jal exec_stmt` seam is `bridgeOfSeg`; the dispatch/marshalling residuals stay NAMED
typed premises (Law 2), exactly as `WhileBodyArmDispatch`/`WhileBodyArmStagePre`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats`
bump.  Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code
open Vsa.Sim.ApproxArmReseat

namespace Vsa.Sim

set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

/-! ## §1. The for-body-arm body seg `0x800042a8 → 0x800042b4` (straight-line, jal-terminated at 0x800042b8) -/
#derive_case flBodyBodySeg chain
  [(0x800042a8#64, 0x02043583#32),  -- ld a1,32(s0)   (for-body stmt node)
   (0x800042ac#64, 0x00090693#32),  -- mv a3,s2       (a3 := interp*)
   (0x800042b0#64, 0x00098613#32),  -- mv a2,s3       (a2 := env)
   (0x800042b4#64, 0x00048513#32)]  -- mv a0,s1       (a0 := ret)

/-- The `flBody` entry pin list — the registers the body READS before writing:
`x8` (s0, for-node, for the `ld`), `x18` (s2, interp), `x19` (s3, env),
`x9` (s1, ret), `x2` (sp). -/
def flBodyBodyL (sp s0 s2 s3 s1 : BitVec 64) : GRegs :=
  [(2, sp), (8, s0), (18, s2), (19, s3), (9, s1)]

/-! ## §2. The body ≫ jal bridge (`bridgeOfSeg`) — modelled on `stmtWhileBodyBridge`. -/
theorem flBodyBodyBridge
    (σ : MState) (i u : Nat) (vminstret : BitVec 64)
    (sp s0 s2 s3 s1 : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x800042a8#64 : BitVec 64))
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : σ.mem = m0)
    (hL : GHolds σ (flBodyBodyL sp s0 s2 s3 s1))
    (hfacts : ChainFacts σ.mem σ.mem (flBodyBodyL sp s0 s2 s3 s1) [] flBodyBodySeg)
    (hi : i < 2)
    (hKeysOut : KeysOK (keysG (evalBlocks flBodyBodySeg
      (SegEvalState.init (flBodyBodyL sp s0 s2 s3 s1) [])).regs))
    (hRaOut : KeysAvoidRa (evalBlocks flBodyBodySeg
      (SegEvalState.init (flBodyBodyL sp s0 s2 s3 s1) [])).regs)
    (hjalSeam : ∀ (σ' : MState) (i' u' : Nat),
      GoodState σ' → i' < 2 →
      σ'.regs.get? Register.PC = some
        (evalBlocksPC 0x800042a8#64 (SegEvalState.init (flBodyBodyL sp s0 s2 s3 s1) [])
          flBodyBodySeg) →
      (∃ w, σ'.regs.get? Register.minstret = some w) →
      σ'.mem = writeLog m0 (evalBlocks flBodyBodySeg
        (SegEvalState.init (flBodyBodyL sp s0 s2 s3 s1) [])).log →
      GHolds σ' (evalBlocks flBodyBodySeg
        (SegEvalState.init (flBodyBodyL sp s0 s2 s3 s1) [])).regs →
      JalStep 0x80003fe0#64 0x800042bc#64 σ' i' u') :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ2, i2, u + evalBlocksFuel flBodyBodySeg + 1⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧
      σ2.regs.get? Register.PC = some (0x80003fe0#64 : BitVec 64) ∧
      σ2.regs.get? Register.x1 = some (0x800042bc#64 : BitVec 64) ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧
      GHolds σ2 (evalBlocks flBodyBodySeg
        (SegEvalState.init (flBodyBodyL sp s0 s2 s3 s1) [])).regs ∧
      σ2.mem = writeLog m0 (evalBlocks flBodyBodySeg
        (SegEvalState.init (flBodyBodyL sp s0 s2 s3 s1) [])).log ∧
      (∀ R, Vsa.Alloc.AbiPreserved R = true → σ2.regs.get? R = σ.regs.get? R) := by
  apply bridgeOfSeg flBodyBodySeg (flBodyBodyL sp s0 s2 s3 s1) []
    σ i u (0x800042a8#64) (0x80003fe0#64) (0x800042bc#64) vminstret m0
    hG hpc hminstret hmem hL
    (by have h : keysG (flBodyBodyL sp s0 s2 s3 s1) = [2, 8, 18, 19, 9] := rfl
        rw [h]; decide)
    hfacts hi
    (by have h : keysG (flBodyBodyL sp s0 s2 s3 s1) = [2, 8, 18, 19, 9] := rfl
        rw [h]; show ChainOK 0x800042a8#64 [2, 8, 18, 19, 9] flBodyBodySeg; decide)
    (by show WrChainAvoidAbi flBodyBodySeg; decide)
    hKeysOut hRaOut
  exact hjalSeam

#print axioms flBodyBodyBridge

/-! ## §3. The arm-head bundle + named residuals + field composer -/

/-- **The for-body-arm-head bundle** — the machine at `0x800042a8` with the body pins
live (sp/s0/s2/s3/s1) and the loop-body node's `StmtRepr` at `ld a1,32(s0)`. -/
def FlBodyArmHeadInv
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st' : Vsa.While.St) (b : Stmt)
    (sp s0 s2 s3 s1 aBody : BitVec 64) (m0 : Mem) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some (0x800042a8#64) ∧
  GHolds c.σ (flBodyBodyL sp s0 s2 s3 s1) ∧
  (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
  c.σ.mem = m0 ∧
  StmtRepr m0 aBody.toNat b ∧
  StoreRepr m0 N A φf φc st'.store ∧
  Machine.output c.σ = st'.out

/-- **The `flBody` marshalling residual** — run the body (`flBodyBodyBridge`) and
marshal into `ExecStmtPreBundle b`.  Named per Law 2. -/
def FlBodyArmStagePre
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st' : Vsa.While.St) (d : Nat) (env : Addr) (b : Stmt)
    (sp s0 s2 s3 s1 aBody : BitVec 64) (m0 : Mem) : Prop :=
  ∀ c' : Config,
    FlBodyArmHeadInv N A SL φf φc st' b sp s0 s2 s3 s1 aBody m0 c' →
    LandedN 1 c' (fun c'' => ExecStmtPreBundle b c'' st' d env)

/-- **The `flBody` dispatch residual** — from `ForCond` + `FEntryC cnd step b`, land
(LandedN 0) at the arm-head bundle.  Analog of `ArgsHeadDispatch`; upstream. -/
def FlBodyArmDispatch (cnd : Option Expr) (step : Option Expr) (b : Stmt)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (c : Config) : Prop :=
  ForCond st d env cnd st' → FEntryC c st d env cnd step b →
  ∃ (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp s0 s2 s3 s1 aBody : BitVec 64) (m0 : Mem),
    LandedN 0 c (FlBodyArmHeadInv N A SL φf φc st' b sp s0 s2 s3 s1 aBody m0) ∧
    FlBodyArmStagePre N A SL φf φc st' d env b sp s0 s2 s3 s1 aBody m0

/-- **The `NonEvalChildStages.flBody` field, machine-composed.** -/
theorem flBody_field_of_dispatch
    (cnd : Option Expr) (step : Option Expr) (b : Stmt) (c : Config)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr)
    (hDisp : FlBodyArmDispatch cnd step b st st' d env c)
    (hFC : ForCond st d env cnd st') (hFE : FEntryC c st d env cnd step b) :
    LandedN 1 c (fun c' => ExecStmtPreBundle b c' st' d env) := by
  obtain ⟨N, A, SL, φf, φc, sp, s0, s2, s3, s1, aBody, m0, hLanded0, hStage⟩ :=
    hDisp hFC hFE
  have hcomp : LandedN (0 + 1) c (fun c' => ExecStmtPreBundle b c' st' d env) :=
    LandedN.bind hLanded0 (fun c' hInv => hStage c' hInv)
  exact LandedN.weakenCount (by omega) hcomp

#print axioms flBody_field_of_dispatch

end Vsa.Sim
