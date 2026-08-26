import Vsa.Sim.ExecBrkCont
import Vsa.Sim.ExecExprRet
import Vsa.Sim.ExecWhileSites
import Vsa.Sim.ExecDispatch
import Vsa.Sim.EvalRecCommon

/-!
# Layer 4 — M4 `whileStmt` cases: the loop with a re-evaluated condition

The `exec_stmt` `whileStmt` arm (kind 4, `0x8000403c`) is a genuine machine loop:

```
-- loop head 0x8000403c:
8000403c:  ld   a2,8(s0)       -- a2 := stmt->cond   (offset 8)
80004040:  mv   a3,s3          -- a3 := env
80004044:  addi a0,sp,80       -- cond eval sret buffer (sp'+80)
80004048:  mv   a1,s1          -- a1 := interp*
8000404c:  jal  eval_expr      -- link 0x80004050; the cond sub-derivation (EvalIH)
80004050:  ld   a3,80(sp)      -- reload the 24-byte cond result …
80004054:  ld   a4,88(sp)
80004058:  ld   a5,96(sp)
8000405c:  addi a0,sp,16       -- value_truthy arg buffer
80004060:  sd   a3,16(sp)      -- copy result into it
80004064:  sd   a4,24(sp)
80004068:  sd   a5,32(sp)
8000406c:  jal  value_truthy   -- link 0x80004070; a0 := (v.truthy ? 1 : 0)
80004070:  beqz a0,0x80004090  -- v.truthy == 0 (FALSY) → normal exit (whileFalse)
                               -- else (TRUTHY): run the body via a REAL jal exec_stmt
80004074:  ld   a1,16(s0)      -- a1 := stmt->body  (offset 16)
80004078:  mv   a3,s2          -- a3 := retslot
8000407c:  mv   a2,s3          -- a2 := env
80004080:  mv   a0,s1          -- a0 := interp*
80004084:  jal  exec_stmt      -- link 0x80004088; the body sub-derivation (ExecIH)
80004088:  li   a5,1
8000408c:  bne  a0,a5,0x80004034 -- body status ≠ 1 (≠ brk) → back-edge check 0x80004034
                               --   (else body status == 1 (brk) → fall through to normal exit)
-- normal exit:
80004090:  li   a0,0           -- x10 := 0 = StatusCode .normal
80004094:  j    0x8000409c     -- shared epilogue (execBlockD, status .normal)
-- back-edge check 0x80004034 (reached after body status ≠ brk):
80004034:  li   a5,3
80004038:  beq  a0,a5,0x80004150 -- body status == 3 (ret) → propagate (whileRet, 0x80004150 ret epilogue)
                               --   else (normal/cont) → fall through to loop head 0x8000403c (whileLoop)
```

So the whole thing is: eval cond; falsy → normal exit; truthy → run the body via
a genuine `jal exec_stmt` (the ordinary `ExecIH`, NOT re-dispatch); then dispatch
on the body's status — `.brk` → normal exit, `.ret v` → propagate (ret epilogue at
`0x80004150`), `.normal`/`.cont` → loop back to the cond head.

## `whileFalse` (this file)

`whileFalse` is the bounded first case: the condition evaluates falsy and NO body
runs, completing `.normal` with the condition's output store `st'`. It is
STRUCTURALLY IDENTICAL to `execIfNoneSim` — cond eval + `value_truthy` (falsy) +
`beqz a0` taken to `0x80004090` + `li a0,0` + `j 0x8000409c` + `execBlockD .normal`
— only the arm PC (`0x8000403c` kind 4) and the sret-buffer offset (`sp'+80` vs
`sp'+56`) differ. The cond-eval + `value_truthy` + falsy branch (`0x8000403c →
0x80004090`, landing in a `SubExecReturn` state) is delivered as the named glue
residual `hGlue`, exactly as in `execIfNoneSim`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `ExecWhileFalseSimGoal` — the `ExecS.whileFalse` simulation Triple (packaged) -/
def ExecWhileFalseSimGoal
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (v : Value)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String) : Prop :=
  Triple
    (fun cfg => ExecEntry g N A SL φf φc st d env (.whileStmt c b) sp r aInterp aStmt aEnv aRet m0 cfg
      ∧ cfg.σ.sailOutput = out0)
    (ExecExit g N A SL φf φc st' .normal sp r aRet m0)

/-! ## `execWhileFalseSim` — `ExecS.whileFalse`: `execBlockA ≫ hGlue ≫ (li a0,0 ; j ; execBlockD)`

The head (`execBlockA`, prologue+dispatch to the `whileStmt` arm `0x8000403c`) and
the tail (`li a0,0` at `0x80004090`, `j 0x8000409c`, then `execBlockD` with status
`.normal`) are threaded UNCONDITIONALLY around the arm-body glue `hGlue`, which
consumes the `EvalIH` for the condition, evaluates `value_truthy` (result `0`,
since `v.truthy = false`), takes the falsy branch (`beqz a0` → `0x80004090`), and
lands at `0x80004090` in a `SubExecReturn` state. Identical skeleton to
`execIfNoneSim`, for the `while`-with-falsy-cond arm. -/
theorem execWhileFalseSim
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (v : Value)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String)
    (_hSpec : ExecS st d env (.whileStmt c b) st' .normal)
    (hIH : EvalIH st d env c st' v)
    (_hfalsy : v.truthy = false)
    -- execBlockA residuals (as for brk/cont/expr/ifNone):
    (hslot : StmtSlotPinned 4 execArmWhile m0)
    (htableStk : stmtJumpTableBase + 4 * 4 + 4 ≤ SL.lo ∨ sp.toNat ≤ stmtJumpTableBase + 4 * 4)
    -- the arm-body glue: from the arm-entry state at `0x8000403c` the condition
    -- setup + `jal eval_expr` + the sub-call (the `EvalIH`) + the reload/copy +
    -- `value_truthy` (result `0`, since `v.truthy = false`) + the falsy branch
    -- (`beqz a0` TAKEN to `0x80004090`) reach `0x80004090` in a `SubExecReturn`
    -- state. Statement-frame analog of `execIfNoneSim`'s `hGlue`; RESIDUAL.
    (hGlue : EvalIH st d env c st' v →
      Triple
        (fun cfg => ∃ ment v8 v9 v18 v19,
          ExecArmEntryK g N A SL φf φc st execArmWhile sp r aInterp aStmt aEnv aRet
            v8 v9 v18 v19 out0 m0 ment cfg)
        (fun cfg => ∃ subsret v1 v8 v9 v18 v19 mcall,
          SubExecReturn g N A SL φf φc st' v
            sp r aRet subsret (0x80004090#64) v1 v8 v9 v18 v19 m0 mcall cfg)) :
    ExecWhileFalseSimGoal g N A SL φf φc st st' d env c b v
      sp r aInterp aStmt aEnv aRet m0 out0 := by
  intro cfg hpre
  obtain ⟨he, hout0⟩ := hpre
  -- kind read `read32 m0 aStmt = 4` from the `.whileStmt` StmtRepr
  have hkind : read32 m0 aStmt.toNat = some 4 := by
    have := he.stmt; rw [he.mem] at this; cases this with
    | whileS h0 _ _ _ _ => exact h0
  -- ===== head: execBlockA (prologue + dispatch → arm entry 0x8000403c) =====
  have hBlockA : ExecBlockAGoal g N A SL φf φc st d env (.whileStmt c b)
      sp r aInterp aStmt aEnv aRet execArmWhile m0 out0 :=
    execBlockA g N A SL φf φc st d env (.whileStmt c b) 4 execArmWhile
      sp r aInterp aStmt aEnv aRet m0 out0
      (by omega) (by omega) hkind hslot (by decide) htableStk
  obtain ⟨cA, hstepsA, hArmExists⟩ := hBlockA cfg ⟨he, hout0⟩
  -- ===== glue: arm body + jal eval_expr + value_truthy + falsy branch → SubExecReturn =====
  obtain ⟨cG, hstepsG, hGlueOut⟩ := hGlue hIH cA hArmExists
  obtain ⟨subsret, v1, v8, v9, v18, v19, mcall, hSub⟩ := hGlueOut
  obtain ⟨hGG, htickG, hpcG, hraG, hspG, hs2G, ⟨vmiG, hmiG⟩, houtG, hframeG,
    hgx8, hgx9, hgx18, hgx19, hgx2, _hvalG, hstoreG, hcodeG,
    hslotRa, hslotS0, hslotS1, hslotS2, hslotS3,
    hsubWin, hmemframeG, _hmemExtG, hmemPreG⟩ := hSub
  -- ===== tail: 0x80004090 `li a0,0` (x10 := 0 = StatusCode .normal) =====
  have hpcG' : cG.σ.regs.get? Register.PC = some (0x80004090#64) := hpcG
  obtain ⟨σ1, i1, hstep1', hi1, hG1, hmem1, hobs1⟩ :=
    site_80004090_es cG.σ cG.tick cG.steps (0x80004090#64) vmiG hGG hpcG' hmiG hcodeG rfl htickG
  have hstep1 : Step cG ⟨σ1, i1, cG.steps + 1⟩ := by cases cG; exact hstep1'
  have hmem1e : σ1.mem = cG.σ.mem := hmem1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80004094#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80004090#64) 4 = (0x80004094#64 : BitVec 64) from by decide] at this
  have ha0_1 : σ1.regs.get? Register.x10 = some (StatusCode .normal) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) = StatusCode .normal from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 176#64) := obs_alu_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspG
  have hra_1 : σ1.regs.get? Register.x1 = some (0x80004090#64) := obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hraG
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hcode1 : Exec_stmtLoaded σ1.mem := by rw [hmem1e]; exact hcodeG
  have abi_ne' : ∀ {X R : Register}, AbiPreserved X = false → AbiPreserved R = true →
      (X == R) = false := by
    intro X R hX hR
    rcases hXR : (X == R) with _ | _
    · rfl
    · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)
  have hframe1 : ∀ R : Register, AbiPreservedNoise R → (Register.x10 == R) = false →
      σ1.regs.get? R = cG.σ.regs.get? R := by
    intro R hR h10
    obtain ⟨_, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ := hR
    exact (hobs1.1 R hmc' hmt' hmip').trans
      (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' h10 hnpc' hmii')
  -- ===== 0x80004094 `j 0x8000409c` → PC := shared epilogue entry =====
  have htgt94 : (0x80004094#64 + sign_extend (m := 64) (0x000008#21)).toNat % 4 = 0 := by decide
  obtain ⟨σ2, i2, hstep2', hi2, hG2, hmem2, hobs2⟩ :=
    site_80004094_es σ1 i1 (cG.steps + 1) (0x80004094#64) vmi1 hG1 hpc1 hmi1 hcode1 rfl htgt94 hi1
  have hstep2 : Step ⟨σ1, i1, cG.steps + 1⟩ ⟨σ2, i2, cG.steps + 1 + 1⟩ := hstep2'
  have hmem2e : σ2.mem = cG.σ.mem := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x8000409c#64) := by
    have := obs_jr_pc hobs2
    rwa [show (0x80004094#64 + sign_extend (m := 64) (0x000008#21)) = (0x8000409c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have ha0_2 : σ2.regs.get? Register.x10 = some (StatusCode .normal) := obs_jr_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp - 176#64) := obs_jr_other hobs2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_1
  have hra_2 : σ2.regs.get? Register.x1 = some (0x80004090#64) := obs_jr_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  obtain ⟨vmi2, hmi2⟩ := obs_jr_minstret hobs2
  have hcode2 : Exec_stmtLoaded σ2.mem := by rw [hmem2e]; exact hcodeG
  have hframe2 : ∀ R : Register, AbiPreservedNoise R → (Register.x10 == R) = false →
      σ2.regs.get? R = cG.σ.regs.get? R := by
    intro R hR h10
    obtain ⟨_, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ := id hR
    exact ((hobs2.1 R hmc' hmt' hmip').trans
      (get?_sigmaPost_jump_x0 _ _ _ _ R hmi' hpc' hnpc' hmii')).trans (hframe1 R hR h10)
  -- output through the two tail steps: `String.join σ2.sailOutput.toList = st'.out`
  have hout2 : String.join σ2.sailOutput.toList = st'.out := by
    have h : String.join cG.σ.sailOutput.toList = st'.out := houtG
    rw [hobs2.out, sailOutput_sigmaPost_jump_x0, hobs1.out, sailOutput_sigmaPost_alu]; exact h
  -- the extended store maps from the sub-call, and the geometry the epilogue needs.
  obtain ⟨φfE, φcE, hpfE, hpcE, hstoreE⟩ := hstoreG
  have hstackOK := he.stackOK
  obtain ⟨hSLlo, hsphi, hsp16⟩ := hstackOK
  have hsp176 : 176 ≤ sp.toNat := by
    have := he.stack_win; have := he.stack_ram.1
    have htoh : tohostAddr = 0x8001ad00 := rfl; omega
  have hraAl := he.ra_align
  -- ===== execBlockD (at the EXTENDED maps, baseline `m0 := cG.σ.mem`) → ExecExit =====
  obtain ⟨cD, hstepsD, hExitE⟩ :=
    execBlockD g N A SL φfE φcE st' .normal sp r aRet v8 v9 v18 v19 σ2.sailOutput cG.σ.mem
      (by intro w hw; cases hw)
      ⟨σ2, i2, cG.steps + 1 + 1⟩
      ⟨cG.σ.mem,
        hG2, hi2, hpc2, ha0_2, hsp_2, ⟨_, hmi2⟩,
        rfl, hout2,
        hmem2e, hmem2e ▸ hcode2,
        hmem2e ▸ hstoreE,
        (by
          intro R hR he8 he9 he18 he19 he2
          have h10 : (Register.x10 == R) = false := abi_ne' (by decide) hR.1
          rw [hframe2 R hR h10]; exact hframeG R hR he8 he9 he18 he19 he2),
        hmem2e ▸ hslotRa, hmem2e ▸ hslotS0, hmem2e ▸ hslotS1, hmem2e ▸ hslotS2, hmem2e ▸ hslotS3,
        hgx8, hgx9, hgx18, hgx19, hgx2,
        (by intro a _; rfl),
        hsp176, (by have := he.stack_ram.2; omega), (by have := he.stack_ram.1; omega),
        (by have := he.stack_win; have htoh : tohostAddr = 0x8001ad00 := rfl; omega),
        (by have := hsp16; omega), hraAl⟩
  -- ===== convert ExecExit (baseline cG.σ.mem, maps φfE/φcE) to the goal =====
  refine ⟨cD, (hstepsA.trans (hstepsG.trans ((Steps.single hstep1).trans (Steps.single hstep2)))).trans hstepsD, ?_⟩
  refine
    { good := hExitE.good
      tick := hExitE.tick
      pc := hExitE.pc
      a0 := hExitE.a0
      ra := hExitE.ra
      spReg := hExitE.spReg
      minstret := hExitE.minstret
      store := ?_
      out := hExitE.out
      retval := (by intro w hw; cases hw)
      frame := hExitE.frame
      memFrame := ?_ }
  · obtain ⟨φf'', φc'', hpf'', hpc'', hst''⟩ := hExitE.store
    exact ⟨φf'', φc'',
      PhiExtends.trans hpfE hpf'', PhiExtends.trans hpcE hpc'', hst''⟩
  · intro a hstk harena
    have hbase := hExitE.memFrame a hstk harena
    rcases hbase with hret | heqG
    · exact Or.inl hret
    · rcases hmemframeG a hstk harena with hsub | heqC
      · exact absurd (⟨by omega, by omega⟩ : SL.lo ≤ a ∧ a < sp.toNat) hstk
      · exact Or.inr (by rw [heqG, heqC, hmemPreG a hstk])

/-! ## `ExecWhileStep` — one machine loop iteration (the per-iteration hypothesis)

From `ExecEntry` at the loop head (the `whileStmt` arm entry `0x8000403c`, reached
per-iteration with a fresh cond eval), one iteration runs the cond eval (`EvalIH`),
`value_truthy`, and — on the truthy path — the body via a genuine `jal exec_stmt`
(`ExecIH`), then dispatches on the body's status (mirroring the machine branches
`beqz a0` at the cond, `bne a0,1` after the body, and `beq a0,3` at `0x80004034`):

* **loop-back** (body `.normal`/`.cont`, `whileLoop`) → re-enter the head at `stMid`
  with EXTENDED φ-maps; the post carries the next-iteration `ExecEntry` (its own
  baseline `cfg.σ.mem`) PLUS a memory-agreement clause: `cfg.σ.mem` agrees with the
  original `m0` outside the stack window `[SL.lo, sp)` and the arena `[A.lo, A.hi)`
  (arena = where the store-growth writes land) — this re-bases the recursive exit's
  `memFrame` back to `m0`.
* **exit** (cond falsy `whileFalse`, body `.brk` `whileBreak`, body `.ret v`
  `whileRet`) → the loop is done; land the `ExecExit` for `stMid`/`loopStatus`
  against the original `m0` directly.

`stFin` is the loop's final post-state; the loop-back φ-extension is stated over
`stFin`'s store sizes so the loop rule composes the per-iteration extensions to the
final exit (like `ExecSeqStep`). -/
def ExecWhileStep
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String)
    (stMid stFin : Vsa.While.St) (bodyStatus loopStatus : Status) : Prop :=
  Triple
    (fun cfg => ExecEntry g N A SL φf φc st d env (.whileStmt c b) sp r aInterp aStmt aEnv aRet m0 cfg
      ∧ cfg.σ.sailOutput = out0)
    (fun cfg =>
      -- loop-back branch: body normal/cont → re-enter the head at `stMid`
      (((bodyStatus = .normal ∨ bodyStatus = .cont) ∧
        ∃ (φf' φc' : Addr → Nat),
          PhiExtends φf φf' stFin.store.frames.size ∧
          PhiExtends φc φc' stFin.store.closures.size ∧
          ExecEntry g N A SL φf' φc' stMid d env (.whileStmt c b) sp r aInterp aStmt aEnv aRet
            cfg.σ.mem cfg ∧ cfg.σ.sailOutput = out0 ∧
          (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
            cfg.σ.mem[a]? = m0[a]?))
      ) ∨
      -- exit branch: falsy / brk / ret → land the exit against `m0`
      (¬ (bodyStatus = .normal ∨ bodyStatus = .cont) ∧
        ExecExit g N A SL φf φc stMid loopStatus sp r aRet m0 cfg))

/-! ## `execWhileExit` — the three non-recursive `whileStmt` constructors

`whileFalse` (cond falsy → `.normal`), `whileBreak` (truthy, body `.brk` → `.normal`
with the body's output store `st'`), and `whileRet` (truthy, body `.ret v` →
propagate `.ret v`) all EXIT the loop in one iteration — they do not recurse. Each
is discharged directly by the `ExecWhileStep` iteration's EXIT branch (the machine's
`beqz a0` cond-falsy exit, the `bne a0,1` NOT-taken brk-fall-through, and the
`0x80004034 beq a0,3` ret-propagation). The `.brk`/`.ret v` body statuses are
`≠ .normal, .cont`, so the exit disjunct fires; the loop-back disjunct is
contradictory (impossible for these statuses). -/
theorem execWhileExit
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64)
    (hstep : ∀ (φf φc : Addr → Nat) (st stMid stFin : Vsa.While.St)
        (bodyStatus loopStatus : Status) (m0 : Mem) (out0 : Array String),
        ExecWhileStep g N A SL φf φc st d env c b sp r aInterp aStmt aEnv aRet m0 out0
          stMid stFin bodyStatus loopStatus)
    (φf φc : Addr → Nat) (st st' : Vsa.While.St) (status : Status) (m0 : Mem)
    (out0 : Array String)
    (hExec : ExecS st d env (.whileStmt c b) st' status)
    -- the loop's SINGLE-ITERATION exit witness: the body (if any) completes with a
    -- status that is NOT `.normal`/`.cont` (falsy = no body / `.brk` / `.ret v`),
    -- and the body status the machine observes is `bodyStatus`.
    (bodyStatus : Status) (hexit : ¬ (bodyStatus = .normal ∨ bodyStatus = .cont)) :
    Triple
      (fun cfg => ExecEntry g N A SL φf φc st d env (.whileStmt c b) sp r aInterp aStmt aEnv aRet m0 cfg
        ∧ cfg.σ.sailOutput = out0)
      (ExecExit g N A SL φf φc st' status sp r aRet m0) := by
  intro cfg hpre
  obtain ⟨cE, hs, hpost⟩ := hstep φf φc st st' st' bodyStatus status m0 out0 cfg hpre
  rcases hpost with ⟨hlb, _⟩ | ⟨_, hE⟩
  · exact absurd hlb hexit
  · exact ⟨cE, hs, hE⟩

end Vsa.Sim
