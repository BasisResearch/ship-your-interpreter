import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.BridgeSeg
import Vsa.Sim.ArmSegSplitTwins

/-!
# `FlStepArmStagePre` — the for-loop STEP-arm head → `ExecJalPreBundle` staging
(Wave 44 pilot for `flStep_split'`, twin 3)

The for-STEP sub-expression evaluates via `jal eval_expr @0x800042e8` sited in
**`exec_stmt`'s text** (the EXEC frame, sp-176) — so the staging must land at
`ExecJalPreBundle` (the `Exec_stmtLoaded`-typed jal seam, wave-40 falsity-#7
class), NOT the eval-frame `JalPreBundle` that `ArmSegSplitEval.flStep_split`
hardcodes.  `flStep_split'` (`ArmSegSplitTwins.lean` §3) is the exec twin; this
file is its pilot arm.

The arm head (from `experiments/disasm.txt`, entered from the post-body
classification `bnez a2,0x800042dc @0x80004268` with `a2` = the step node loaded
by `ld a2,24(s0) @0x80004264`):

    800042dc:  mv a3,s3        -- a3 := env
    800042e0:  mv a1,s1        -- a1 := interp*
    800042e4:  addi a0,sp,16   -- a0 := the sret buffer (exec frame, sp+16)
    800042e8:  jal eval_expr   -- 0x80003164, link 0x800042ec

a STRAIGHT-LINE-then-`jal eval_expr` span — exactly the wave-43
`stmtWhileBody` shape (`#derive_case` seg + `bridgeOfSeg`; the jal seam and the
marshalling into `ExecJalPreBundle` stay NAMED residuals per Law 2).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats`
bump beyond the seg-derivation budget the GEN idiom uses.  Axioms of every theorem
⊆ {propext, Classical.choice, Quot.sound}.
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

/-! ## §1. The step-arm body seg `0x800042dc → 0x800042e4` (straight-line,
jal-terminated at 0x800042e8) -/

#derive_case flStepBodySeg chain
  [(0x800042dc#64, 0x00098693#32),  -- mv a3,s3       (a3 := env)
   (0x800042e0#64, 0x00048593#32),  -- mv a1,s1       (a1 := interp*)
   (0x800042e4#64, 0x01010513#32)]  -- addi a0,sp,16  (a0 := sret buffer)

/-- The `flStep` entry pin list — the registers the body reads (`x19` env,
`x9` interp, `x2` sp) plus the step node `x12` (a2, staged upstream by
`ld a2,24(s0)`) carried through to the jal. -/
def flStepL (sp s1 s3 a2 : BitVec 64) : GRegs :=
  [(19, s3), (9, s1), (2, sp), (12, a2)]

/-! ## §2. The body ≫ jal bridge (`bridgeOfSeg`) -/

/-- **`flStepBridge`** — the step-arm body run ≫ `jal eval_expr @0x800042e8`
(link `0x800042ec`, target `eval_expr` entry `0x80003164`), via `bridgeOfSeg`.
The seg run + ABI frame are FREE; `hfacts` and the jal seam `hjalSeam` are the
only region-specific residuals.  Modelled on `stmtWhileBodyBridge`. -/
theorem flStepBridge
    (σ : MState) (i u : Nat) (vminstret : BitVec 64)
    (sp s1 s3 a2 : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x800042dc#64 : BitVec 64))
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : σ.mem = m0)
    (hL : GHolds σ (flStepL sp s1 s3 a2))
    (hfacts : ChainFacts σ.mem σ.mem (flStepL sp s1 s3 a2) [] flStepBodySeg)
    (hi : i < 2)
    (hKeysOut : KeysOK (keysG (evalBlocks flStepBodySeg
      (SegEvalState.init (flStepL sp s1 s3 a2) [])).regs))
    (hRaOut : KeysAvoidRa (evalBlocks flStepBodySeg
      (SegEvalState.init (flStepL sp s1 s3 a2) [])).regs)
    (hjalSeam : ∀ (σ' : MState) (i' u' : Nat),
      GoodState σ' → i' < 2 →
      σ'.regs.get? Register.PC = some
        (evalBlocksPC 0x800042dc#64 (SegEvalState.init (flStepL sp s1 s3 a2) [])
          flStepBodySeg) →
      (∃ w, σ'.regs.get? Register.minstret = some w) →
      σ'.mem = writeLog m0 (evalBlocks flStepBodySeg
        (SegEvalState.init (flStepL sp s1 s3 a2) [])).log →
      GHolds σ' (evalBlocks flStepBodySeg
        (SegEvalState.init (flStepL sp s1 s3 a2) [])).regs →
      JalStep 0x80003164#64 0x800042ec#64 σ' i' u') :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ2, i2, u + evalBlocksFuel flStepBodySeg + 1⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧
      σ2.regs.get? Register.PC = some (0x80003164#64 : BitVec 64) ∧
      σ2.regs.get? Register.x1 = some (0x800042ec#64 : BitVec 64) ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧
      GHolds σ2 (evalBlocks flStepBodySeg
        (SegEvalState.init (flStepL sp s1 s3 a2) [])).regs ∧
      σ2.mem = writeLog m0 (evalBlocks flStepBodySeg
        (SegEvalState.init (flStepL sp s1 s3 a2) [])).log ∧
      (∀ R, Vsa.Alloc.AbiPreserved R = true → σ2.regs.get? R = σ.regs.get? R) := by
  apply bridgeOfSeg flStepBodySeg (flStepL sp s1 s3 a2) []
    σ i u (0x800042dc#64) (0x80003164#64) (0x800042ec#64) vminstret m0
    hG hpc hminstret hmem hL
    (by have h : keysG (flStepL sp s1 s3 a2) = [19, 9, 2, 12] := rfl
        rw [h]; decide)
    hfacts hi
    (by have h : keysG (flStepL sp s1 s3 a2) = [19, 9, 2, 12] := rfl
        rw [h]; show ChainOK 0x800042dc#64 [19, 9, 2, 12] flStepBodySeg; decide)
    (by show WrChainAvoidAbi flStepBodySeg; decide)
    hKeysOut hRaOut
  exact hjalSeam

#print axioms flStepBridge

/-! ## §3. The arm-head bundle + named residuals + the field composers -/

/-- **The step-arm-head bundle** — the machine at `0x800042dc` with the body pins
live and the step node's `ExprRepr` at the address in `a2`. -/
def FlStepArmHeadInv
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st'' : Vsa.While.St) (e : Expr)
    (sp s1 s3 a2 : BitVec 64) (m0 : Mem) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some (0x800042dc#64) ∧
  GHolds c.σ (flStepL sp s1 s3 a2) ∧
  (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
  c.σ.mem = m0 ∧
  ExprRepr m0 a2.toNat e ∧
  StoreRepr m0 N A φf φc st''.store ∧
  Machine.output c.σ = st''.out

/-- **The `flStep` marshalling residual** — from the arm-head bundle, run the body
(`flStepBridge`) and marshal the computed `GHolds`/write-log at the jal site into
`ExecJalPreBundle e` (the exec-frame seam; ghost rebase `sp := esp + 1088` per the
wave-41 re-parametrization).  Named per Law 2. -/
def FlStepArmStagePre
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st'' : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr)
    (sp s1 s3 a2 : BitVec 64) (m0 : Mem) : Prop :=
  ∀ c' : Config,
    FlStepArmHeadInv N A SL φf φc st'' e sp s1 s3 a2 m0 c' →
    LandedN 1 c' (fun c'' => ExecJalPreBundle e c'' st'' d env)

/-- **The `flStep` dispatch residual** — from the parent `FEntryC` plus the
completed cond/body (normal-or-cont), land (LandedN 0) at the arm-head bundle.
Genuinely upstream (the body-status classification `bne a0,a5,0x8000425c` ≫
`ld a2,24(s0)` ≫ `bnez a2` routing is M4 arm-seg content). -/
def FlStepArmDispatch (cnd : Option Expr) (e : Expr) (b : Stmt) (status : Status)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (c : Config) : Prop :=
  ForCond st d env cnd st' → ExecS st' d env b st'' status →
  (status = .normal ∨ status = .cont) → FEntryC c st d env cnd (some e) b →
  ∃ (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp s1 s3 a2 : BitVec 64) (m0 : Mem),
    LandedN 0 c (FlStepArmHeadInv N A SL φf φc st'' e sp s1 s3 a2 m0) ∧
    FlStepArmStagePre N A SL φf φc st'' d env e sp s1 s3 a2 m0

/-- **The `ArmStages.flStep`-shaped staging (exec-typed), machine-composed.**
The `ExecJalPreBundle` counterpart of the (mistyped, eval-frame)
`ArmStages.flStep` premise — what wave-45 supplies to `flStep_split'`. -/
theorem flStep_stageField_of_dispatch
    (cnd : Option Expr) (e : Expr) (b : Stmt) (status : Status)
    (c : Config) (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr)
    (hDisp : FlStepArmDispatch cnd e b status st st' st'' d env c)
    (hFC : ForCond st d env cnd st') (hEx : ExecS st' d env b st'' status)
    (hst : status = .normal ∨ status = .cont)
    (hFE : FEntryC c st d env cnd (some e) b) :
    LandedN 1 c (fun c' => ExecJalPreBundle e c' st'' d env) := by
  obtain ⟨N, A, SL, φf, φc, sp, s1, s3, a2, m0, hLanded0, hStage⟩ :=
    hDisp hFC hEx hst hFE
  have hcomp : LandedN (0 + 1) c (fun c' => ExecJalPreBundle e c' st'' d env) :=
    LandedN.bind hLanded0 (fun c' hInv => hStage c' hInv)
  exact LandedN.weakenCount (by omega) hcomp

#print axioms flStep_stageField_of_dispatch

/-- **The full `ApproxArmResid.flStep` field, machine-composed** — dispatch
residual ≫ staging ≫ `flStep_split'` (the exec twin): EXACTLY the frozen field
type at the concrete entries. -/
theorem flStep_field_of_dispatch
    (cnd : Option Expr) (e : Expr) (b : Stmt) (status : Status)
    (c : Config) (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr)
    (hDisp : FlStepArmDispatch cnd e b status st st' st'' d env c)
    (hFC : ForCond st d env cnd st') (hEx : ExecS st' d env b st'' status)
    (hst : status = .normal ∨ status = .cont)
    (hFE : FEntryC c st d env cnd (some e) b) :
    LandedN 1 c (fun c' => EEntryC c' st'' d env e) :=
  flStep_split' cnd e b status c st st' st'' d env
    (fun hFC' hEx' hst' hFE' =>
      flStep_stageField_of_dispatch cnd e b status c st st' st'' d env
        hDisp hFC' hEx' hst' hFE')
    hFC hEx hst hFE

#print axioms flStep_field_of_dispatch

end Vsa.Sim
