import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.BridgeSeg
import Vsa.Sim.ArmSegSplitNonEval

/-!
# `StmtWhileBodyArmStagePre` — the exec-`whileStmt`-body-arm-head →
`ExecStmtPreBundle` staging field (Wave 43, non-eval side)

The `stmtWhileBody` field of `NonEvalChildStages` (`ArmSegSplitNonEval.lean`) is a
STAGING residual: from `SEntryC (.whileStmt cnd b)` (the parent statement entry) plus
the taken-condition, run the while-body arm head and land at `ExecStmtPreBundle b` —
the recursive `jal exec_stmt` on the loop BODY child statement.

The arm head (from `experiments/disasm.txt`, the while-loop body at `0x80004074`,
i.e. the `value_truthy`-nonzero fallthrough of the loop-head block `0x80004034`
that loops back via `bne a0,a5,0x80004034`) is:

    80004074:  ld a1,16(s0)   -- loop-body stmt node ptr (from while-node)
    80004078:  mv a3,s2       -- a3 := interp*  (addi x13,x18,0)
    8000407c:  mv a2,s3       -- a2 := env      (addi x12,x19,0)
    80004080:  mv a0,s1       -- a0 := ret      (addi x10,x9,0)
    80004084:  jal exec_stmt  -- 0x80003fe0, link 0x80004088

a STRAIGHT-LINE-then-`jal exec_stmt` span — exactly the wave-41 `argsHead` shape.
Per the CLAUDE.md discipline table (and the argsHead lesson: a straight-line-or-jal
-ended span needs NO hand sites), the body `0x80004074 → 0x80004080` is a
`#derive_case` seg and the `jal exec_stmt` seam is `bridgeOfSeg`.  The dispatch
residual (`SEntryC (.whileStmt …) → arm-head bundle at 0x80004074` with the
body-node `StmtRepr`) and the marshalling residual (`GHolds`/`writeLog` at the jal
target → `ExecStmtPreBundle b` conjuncts) stay NAMED typed premises (Law 2), exactly
as `ArgsHeadDispatch` / `ArgsHeadStagePre`.

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

/-! ## §1. The while-body-arm body seg `0x80004074 → 0x80004080` (straight-line, jal-terminated at 0x80004084)

The 4-instruction body between the while-loop-body dispatch and the recursive
`jal exec_stmt`, decoded from `experiments/disasm.txt`.  A `#derive_case` seg exactly
as the GEN `argsHeadBodySeg`; `bridgeOfSeg` runs it and takes the `jal` seam. -/
#derive_case stmtWhileBodySeg chain
  [(0x80004074#64, 0x01043583#32),  -- ld a1,16(s0)   (loop-body stmt node)
   (0x80004078#64, 0x00090693#32),  -- mv a3,s2       (a3 := interp*)
   (0x8000407c#64, 0x00098613#32),  -- mv a2,s3       (a2 := env)
   (0x80004080#64, 0x00048513#32)]  -- mv a0,s1       (a0 := ret)

/-- The `stmtWhileBody` entry pin list — the registers the body READS before
writing: `x8` (s0, while-node, for the `ld`), `x18` (s2, interp), `x19` (s3, env),
`x9` (s1, ret), `x2` (sp). -/
def stmtWhileBodyL (sp s0 s2 s3 s1 : BitVec 64) : GRegs :=
  [(2, sp), (8, s0), (18, s2), (19, s3), (9, s1)]

/-! ## §2. The body ≫ jal bridge (`bridgeOfSeg`)

`stmtWhileBodyBridge` — the then-arm body run ≫ `jal exec_stmt @0x80004084`
(link `0x80004088`, target `exec_stmt` entry `0x80003fe0` via imm `0x1fff5c`), via
`bridgeOfSeg`.  The seg run + ABI frame are FREE; `hfacts` (one `chain_facts` at the
caller) and `hjalSeam` (the call-seam `JalStep` off the `exec_stmt` jal-site obs)
are the only region-specific residuals.  Modelled on `argsHeadBodyBridge`. -/
theorem stmtWhileBodyBridge
    (σ : MState) (i u : Nat) (vminstret : BitVec 64)
    (sp s0 s2 s3 s1 : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x80004074#64 : BitVec 64))
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : σ.mem = m0)
    (hL : GHolds σ (stmtWhileBodyL sp s0 s2 s3 s1))
    (hfacts : ChainFacts σ.mem σ.mem (stmtWhileBodyL sp s0 s2 s3 s1) [] stmtWhileBodySeg)
    (hi : i < 2)
    (hKeysOut : KeysOK (keysG (evalBlocks stmtWhileBodySeg
      (SegEvalState.init (stmtWhileBodyL sp s0 s2 s3 s1) [])).regs))
    (hRaOut : KeysAvoidRa (evalBlocks stmtWhileBodySeg
      (SegEvalState.init (stmtWhileBodyL sp s0 s2 s3 s1) [])).regs)
    (hjalSeam : ∀ (σ' : MState) (i' u' : Nat),
      GoodState σ' → i' < 2 →
      σ'.regs.get? Register.PC = some
        (evalBlocksPC 0x80004074#64 (SegEvalState.init (stmtWhileBodyL sp s0 s2 s3 s1) [])
          stmtWhileBodySeg) →
      (∃ w, σ'.regs.get? Register.minstret = some w) →
      σ'.mem = writeLog m0 (evalBlocks stmtWhileBodySeg
        (SegEvalState.init (stmtWhileBodyL sp s0 s2 s3 s1) [])).log →
      GHolds σ' (evalBlocks stmtWhileBodySeg
        (SegEvalState.init (stmtWhileBodyL sp s0 s2 s3 s1) [])).regs →
      JalStep 0x80003fe0#64 0x80004088#64 σ' i' u') :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ2, i2, u + evalBlocksFuel stmtWhileBodySeg + 1⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧
      σ2.regs.get? Register.PC = some (0x80003fe0#64 : BitVec 64) ∧
      σ2.regs.get? Register.x1 = some (0x80004088#64 : BitVec 64) ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧
      GHolds σ2 (evalBlocks stmtWhileBodySeg
        (SegEvalState.init (stmtWhileBodyL sp s0 s2 s3 s1) [])).regs ∧
      σ2.mem = writeLog m0 (evalBlocks stmtWhileBodySeg
        (SegEvalState.init (stmtWhileBodyL sp s0 s2 s3 s1) [])).log ∧
      (∀ R, Vsa.Alloc.AbiPreserved R = true → σ2.regs.get? R = σ.regs.get? R) := by
  apply bridgeOfSeg stmtWhileBodySeg (stmtWhileBodyL sp s0 s2 s3 s1) []
    σ i u (0x80004074#64) (0x80003fe0#64) (0x80004088#64) vminstret m0
    hG hpc hminstret hmem hL
    (by have h : keysG (stmtWhileBodyL sp s0 s2 s3 s1) = [2, 8, 18, 19, 9] := rfl
        rw [h]; decide)
    hfacts hi
    (by have h : keysG (stmtWhileBodyL sp s0 s2 s3 s1) = [2, 8, 18, 19, 9] := rfl
        rw [h]; show ChainOK 0x80004074#64 [2, 8, 18, 19, 9] stmtWhileBodySeg; decide)
    (by show WrChainAvoidAbi stmtWhileBodySeg; decide)
    hKeysOut hRaOut
  exact hjalSeam

#print axioms stmtWhileBodyBridge

/-! ## §3. The arm-head bundle + the two named residuals + the field composer

The `stmtWhileBody` field of `NonEvalChildStages` is
`EvalE cnd st' v → v.truthy = true → SEntryC (.whileStmt cnd b) →
  LandedN 1 (ExecStmtPreBundle b)`.  We split it (mirroring wave-41 `argsHead`) into:

* `WhileBodyArmHeadInv` — the config predicate at the body-arm head `0x80004074`, with
  all the pins the body reads (sp/s0/s2/s3/s1) and the loop-body node's `StmtRepr` —
  the analog of `ArgsLoopHeadInv`.

* `WhileBodyArmDispatch` — the dispatch residual: from the parent `SEntryC (.whileStmt …)`
  plus the taken condition, reach (LandedN 0, the arm-head is a joinpoint the M4 arm
  seg already routes to at the `value_truthy`-nonzero fallthrough) the arm-head
  bundle.  The analog of `ArgsHeadDispatch`; genuinely upstream (the `SEntryC`
  bundle is dispatch-agnostic, and the cnd-eval → truthy-nonzero → body-fallthrough
  routing is M4 arm-seg content).

* `WhileBodyArmStagePre` — the marshalling residual consuming `WhileBodyArmHeadInv`: run
  the body (`stmtWhileBodyBridge`) and marshal `GHolds`/`writeLog` at the jal target
  into the `ExecStmtPreBundle b` conjuncts (the ABI-frame `x8/x9/x18/x19` witnesses,
  the lowered-`sp` frame geometry, the child `StmtRepr`/`StoreRepr` survival — the
  SAME ~20 side conditions `ExecStmtPreBundle` carries).  Named per Law 2. -/

/-- **The while-body-arm-head bundle** — the machine at `0x80004074` with the body
pins live (sp/s0/s2/s3/s1) and the loop-body node's `StmtRepr` at the address read
out of the while-node by `ld a1,16(s0)`.  The state `stmtWhileBody` stages from. -/
def WhileBodyArmHeadInv
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st' : Vsa.While.St) (b : Stmt)
    (sp s0 s2 s3 s1 aBody : BitVec 64) (m0 : Mem) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some (0x80004074#64) ∧
  GHolds c.σ (stmtWhileBodyL sp s0 s2 s3 s1) ∧
  (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
  c.σ.mem = m0 ∧
  StmtRepr m0 aBody.toNat b ∧
  StoreRepr m0 N A φf φc st'.store ∧
  Machine.output c.σ = st'.out

/-- **The `stmtWhileBody` marshalling residual** — from the arm-head bundle at ANY
config `c'`, run the body (`stmtWhileBodyBridge`) and marshal into
`ExecStmtPreBundle b`.  Named as a typed premise (Law 2): the body run + jal are
PROVED (`stmtWhileBodyBridge`, §2); the residual is the marshalling of the computed
`GHolds`/`writeLog` into the `ExecStmtPreBundle` conjuncts.  Universally quantified
over the config so it composes after a `LandedN` prefix. -/
def WhileBodyArmStagePre
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st' : Vsa.While.St) (d : Nat) (env : Addr) (b : Stmt)
    (sp s0 s2 s3 s1 aBody : BitVec 64) (m0 : Mem) : Prop :=
  ∀ c' : Config,
    WhileBodyArmHeadInv N A SL φf φc st' b sp s0 s2 s3 s1 aBody m0 c' →
    LandedN 1 c' (fun c'' => ExecStmtPreBundle b c'' st' d env)

/-- **The `stmtWhileBody` dispatch residual** — from the parent `SEntryC (.whileStmt …)`
plus the taken condition, land (LandedN 0) at the arm-head bundle.  The analog of
`ArgsHeadDispatch`; genuinely upstream (the cnd-eval → truthy-nonzero →
body-fallthrough routing is M4 arm-seg content the `SEntryC` bundle does not carry). -/
def WhileBodyArmDispatch (cnd : Expr) (b : Stmt)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (v : Value) (c : Config) : Prop :=
  EvalE st d env cnd st' v → v.truthy = true → SEntryC c st d env (.whileStmt cnd b) →
  ∃ (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp s0 s2 s3 s1 aBody : BitVec 64) (m0 : Mem),
    LandedN 0 c (WhileBodyArmHeadInv N A SL φf φc st' b sp s0 s2 s3 s1 aBody m0) ∧
    WhileBodyArmStagePre N A SL φf φc st' d env b sp s0 s2 s3 s1 aBody m0

/-- **The `NonEvalChildStages.stmtWhileBody` field, machine-composed.**  From the
parent `SEntryC (.whileStmt cnd b)` plus the taken condition and the dispatch
residual `WhileBodyArmDispatch`, the composer lands (zero-step) at the arm-head
bundle, then the marshalling residual runs the body and marshals into
`ExecStmtPreBundle b`.  Exactly the field type. -/
theorem stmtWhileBody_field_of_dispatch
    (cnd : Expr) (b : Stmt) (c : Config) (st st' : Vsa.While.St)
    (d : Nat) (env : Addr) (v : Value)
    (hDisp : WhileBodyArmDispatch cnd b st st' d env v c)
    (hE : EvalE st d env cnd st' v) (ht : v.truthy = true)
    (hSE : SEntryC c st d env (.whileStmt cnd b)) :
    LandedN 1 c (fun c' => ExecStmtPreBundle b c' st' d env) := by
  obtain ⟨N, A, SL, φf, φc, sp, s0, s2, s3, s1, aBody, m0, hLanded0, hStage⟩ :=
    hDisp hE ht hSE
  have hcomp : LandedN (0 + 1) c (fun c' => ExecStmtPreBundle b c' st' d env) :=
    LandedN.bind hLanded0 (fun c' hInv => hStage c' hInv)
  exact LandedN.weakenCount (by omega) hcomp

#print axioms stmtWhileBody_field_of_dispatch

end Vsa.Sim
