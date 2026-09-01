import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.BridgeSeg
import Vsa.Sim.ArmSegSplitNonEval

/-!
# `StmtForInitArmStagePre` — the exec-`forStmt`-init-arm-head → `ExecStmtPreBundle`
staging field (Wave 43, non-eval side)

The `stmtForInit` field of `NonEvalChildStages` (`ArmSegSplitNonEval.lean`) is a
STAGING residual: from `SEntryC (.forStmt (some init) cnd step b)` plus the
`allocFrame` (the for-loop's new inner scope) run the init-arm head and land at
`ExecStmtPreBundle init` — the recursive `jal exec_stmt` on the loop INIT statement.

The arm head (from `experiments/disasm.txt`, the for-init at `0x80004248`, the
NOT-taken branch of `beqz a1,0x8000426c` at `0x80004244`, after `env_new`
@0x80004238 established the new scope and `ld a1,8(s0)` @0x8000423c loaded the init
node) is:

    80004248:  mv a2,a0       -- a2 := env   (env_new result, addi x12,x10,0)
    8000424c:  mv a3,s2       -- a3 := interp* (addi x13,x18,0)
    80004250:  mv a0,s1       -- a0 := ret   (addi x10,x9,0)
    80004254:  jal exec_stmt  -- 0x80003fe0, link 0x80004258

a STRAIGHT-LINE-then-`jal exec_stmt` span — exactly the wave-41 `argsHead` shape
(the init node `a1` was loaded before the `beqz` and survives the three `mv`s).
Per the CLAUDE.md discipline table, the body `0x80004248 → 0x80004250` is a
`#derive_case` seg and the `jal exec_stmt` seam is `bridgeOfSeg`; the dispatch
residual (`SEntryC (.forStmt …) + allocFrame → arm-head bundle at 0x80004248`) and
the marshalling residual (`GHolds`/`writeLog` → `ExecStmtPreBundle init` conjuncts)
stay NAMED typed premises (Law 2), exactly as `ArgsHeadDispatch`/`ArgsHeadStagePre`.

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

/-! ## §1. The for-init-arm body seg `0x80004248 → 0x80004250` (straight-line, jal-terminated at 0x80004254) -/
#derive_case stmtForInitBodySeg chain
  [(0x80004248#64, 0x00050613#32),  -- mv a2,a0   (a2 := env, env_new result)
   (0x8000424c#64, 0x00090693#32),  -- mv a3,s2   (a3 := interp*)
   (0x80004250#64, 0x00048513#32)]  -- mv a0,s1   (a0 := ret)

/-- The `stmtForInit` entry pin list — the registers the body READS before writing:
`x10` (a0, env_new result), `x18` (s2, interp), `x9` (s1, ret), `x11` (a1, init
node — pinned to survive to the jal), `x2` (sp). -/
def stmtForInitBodyL (sp a0 s2 s1 a1 : BitVec 64) : GRegs :=
  [(2, sp), (10, a0), (18, s2), (9, s1), (11, a1)]

/-! ## §2. The body ≫ jal bridge (`bridgeOfSeg`) — modelled on `argsHeadBodyBridge`. -/
theorem stmtForInitBodyBridge
    (σ : MState) (i u : Nat) (vminstret : BitVec 64)
    (sp a0 s2 s1 a1 : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x80004248#64 : BitVec 64))
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : σ.mem = m0)
    (hL : GHolds σ (stmtForInitBodyL sp a0 s2 s1 a1))
    (hfacts : ChainFacts σ.mem σ.mem (stmtForInitBodyL sp a0 s2 s1 a1) [] stmtForInitBodySeg)
    (hi : i < 2)
    (hKeysOut : KeysOK (keysG (evalBlocks stmtForInitBodySeg
      (SegEvalState.init (stmtForInitBodyL sp a0 s2 s1 a1) [])).regs))
    (hRaOut : KeysAvoidRa (evalBlocks stmtForInitBodySeg
      (SegEvalState.init (stmtForInitBodyL sp a0 s2 s1 a1) [])).regs)
    (hjalSeam : ∀ (σ' : MState) (i' u' : Nat),
      GoodState σ' → i' < 2 →
      σ'.regs.get? Register.PC = some
        (evalBlocksPC 0x80004248#64 (SegEvalState.init (stmtForInitBodyL sp a0 s2 s1 a1) [])
          stmtForInitBodySeg) →
      (∃ w, σ'.regs.get? Register.minstret = some w) →
      σ'.mem = writeLog m0 (evalBlocks stmtForInitBodySeg
        (SegEvalState.init (stmtForInitBodyL sp a0 s2 s1 a1) [])).log →
      GHolds σ' (evalBlocks stmtForInitBodySeg
        (SegEvalState.init (stmtForInitBodyL sp a0 s2 s1 a1) [])).regs →
      JalStep 0x80003fe0#64 0x80004258#64 σ' i' u') :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ2, i2, u + evalBlocksFuel stmtForInitBodySeg + 1⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧
      σ2.regs.get? Register.PC = some (0x80003fe0#64 : BitVec 64) ∧
      σ2.regs.get? Register.x1 = some (0x80004258#64 : BitVec 64) ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧
      GHolds σ2 (evalBlocks stmtForInitBodySeg
        (SegEvalState.init (stmtForInitBodyL sp a0 s2 s1 a1) [])).regs ∧
      σ2.mem = writeLog m0 (evalBlocks stmtForInitBodySeg
        (SegEvalState.init (stmtForInitBodyL sp a0 s2 s1 a1) [])).log ∧
      (∀ R, Vsa.Alloc.AbiPreserved R = true → σ2.regs.get? R = σ.regs.get? R) := by
  apply bridgeOfSeg stmtForInitBodySeg (stmtForInitBodyL sp a0 s2 s1 a1) []
    σ i u (0x80004248#64) (0x80003fe0#64) (0x80004258#64) vminstret m0
    hG hpc hminstret hmem hL
    (by have h : keysG (stmtForInitBodyL sp a0 s2 s1 a1) = [2, 10, 18, 9, 11] := rfl
        rw [h]; decide)
    hfacts hi
    (by have h : keysG (stmtForInitBodyL sp a0 s2 s1 a1) = [2, 10, 18, 9, 11] := rfl
        rw [h]; show ChainOK 0x80004248#64 [2, 10, 18, 9, 11] stmtForInitBodySeg; decide)
    (by show WrChainAvoidAbi stmtForInitBodySeg; decide)
    hKeysOut hRaOut
  exact hjalSeam

#print axioms stmtForInitBodyBridge

/-! ## §3. The arm-head bundle + named residuals + field composer -/

/-- **The for-init-arm-head bundle** — the machine at `0x80004248` with the body pins
live (sp/a0/s2/s1/a1) and the init-statement node's `StmtRepr` at `a1`. -/
def ForInitArmHeadInv
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (stC : Vsa.While.St) (init : Stmt)
    (sp a0 s2 s1 a1 : BitVec 64) (m0 : Mem) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some (0x80004248#64) ∧
  GHolds c.σ (stmtForInitBodyL sp a0 s2 s1 a1) ∧
  (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
  c.σ.mem = m0 ∧
  StmtRepr m0 a1.toNat init ∧
  StoreRepr m0 N A φf φc stC.store ∧
  Machine.output c.σ = stC.out

/-- **The `stmtForInit` marshalling residual** — run the body (`stmtForInitBodyBridge`)
and marshal into `ExecStmtPreBundle init` at the child store `⟨store', st.out⟩` and
env `outer`.  Named per Law 2. -/
def ForInitArmStagePre
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (stC : Vsa.While.St) (d : Nat) (outer : Addr) (init : Stmt)
    (sp a0 s2 s1 a1 : BitVec 64) (m0 : Mem) : Prop :=
  ∀ c' : Config,
    ForInitArmHeadInv N A SL φf φc stC init sp a0 s2 s1 a1 m0 c' →
    LandedN 1 c' (fun c'' => ExecStmtPreBundle init c'' stC d outer)

/-- **The `stmtForInit` dispatch residual** — from the parent `SEntryC (.forStmt …)`
plus the `allocFrame`, land (LandedN 0) at the arm-head bundle.  Analog of
`ArgsHeadDispatch`; genuinely upstream (the `env_new`/init-load routing is M4 arm-seg
content the `SEntryC` bundle does not carry). -/
def ForInitArmDispatch (init : Stmt) (cnd step : Option Expr) (b : Stmt)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (store' : Store) (outer : Addr)
    (c : Config) : Prop :=
  st.store.allocFrame (some env) = (store', outer) →
  SEntryC c st d env (.forStmt (some init) cnd step b) →
  ∃ (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp a0 s2 s1 a1 : BitVec 64) (m0 : Mem),
    LandedN 0 c (ForInitArmHeadInv N A SL φf φc ⟨store', st.out⟩ init sp a0 s2 s1 a1 m0) ∧
    ForInitArmStagePre N A SL φf φc ⟨store', st.out⟩ d outer init sp a0 s2 s1 a1 m0

/-- **The `NonEvalChildStages.stmtForInit` field, machine-composed.** -/
theorem stmtForInit_field_of_dispatch
    (init : Stmt) (cnd step : Option Expr) (b : Stmt) (c : Config) (st : Vsa.While.St)
    (d : Nat) (env : Addr) (store' : Store) (outer : Addr)
    (hDisp : ForInitArmDispatch init cnd step b st d env store' outer c)
    (hAlloc : st.store.allocFrame (some env) = (store', outer))
    (hSE : SEntryC c st d env (.forStmt (some init) cnd step b)) :
    LandedN 1 c (fun c' => ExecStmtPreBundle init c' ⟨store', st.out⟩ d outer) := by
  obtain ⟨N, A, SL, φf, φc, sp, a0, s2, s1, a1, m0, hLanded0, hStage⟩ :=
    hDisp hAlloc hSE
  have hcomp : LandedN (0 + 1) c (fun c' => ExecStmtPreBundle init c' ⟨store', st.out⟩ d outer) :=
    LandedN.bind hLanded0 (fun c' hInv => hStage c' hInv)
  exact LandedN.weakenCount (by omega) hcomp

#print axioms stmtForInit_field_of_dispatch

end Vsa.Sim
