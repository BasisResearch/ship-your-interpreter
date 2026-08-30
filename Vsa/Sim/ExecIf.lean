import Vsa.Sim.ExecBrkCont
import Vsa.Sim.ExecExprRet
import Vsa.Sim.ExecIfSites
import Vsa.Sim.EvalRecCommon
import Vsa.Sim.ObsAvoid

/-!
# Layer 4 — M4 `ifStmt` bounded case: `ExecS.ifNone`

The `ExecS.ifNone` constructor: the condition evaluates FALSY and there is NO
`else` branch, so the `if` statement runs no sub-statement and completes
`.normal` with the condition's output store `st'`. This is the tractable `if`
sub-case — it sidesteps the re-dispatch problem entirely (ifTrue/ifFalse re-enter
the dispatch at `0x80004014` with `s0 := then/else`; ifNone never re-dispatches).
It is a clean bounded case exactly like `ExecS.expr` (`ExecExprRet.lean`): the
condition eval discards its value like `expr`, but here we additionally observe
its truthiness is falsy and there is no `else` node.

## The `ifStmt` arm (kind 3, `0x800041e8`) — the `ifNone` falsy path

```
800041e8:  ld   a2,8(s0)       -- a2 := stmt->cond   (offset 8, the condition node)
800041ec:  mv   a3,s3          -- a3 := env
800041f0:  mv   a1,s1          -- a1 := interp*
800041f4:  addi a0,sp,56       -- a0 := sp'+56 (cond eval sret buffer)
800041f8:  jal  eval_expr      -- link 0x800041fc; the cond sub-derivation (EvalIH)
800041fc:  ld   a2,56(sp)      -- reload the 24-byte cond result …
80004200:  ld   a3,64(sp)
80004204:  ld   a5,72(sp)
80004208:  addi a0,sp,16       -- a0 := sp'+16 (value_truthy arg buffer)
8000420c:  sd   a2,16(sp)      -- copy the result into the value_truthy arg buffer
80004210:  sd   a3,24(sp)
80004214:  sd   a5,32(sp)
80004218:  jal  value_truthy   -- link 0x8000421c; a0 := (v.truthy ? 1 : 0)
8000421c:  li   a6,8           -- (dispatch-bound reload; noise on this path)
80004220:  auipc a4,0x16       -- a4 := table base …
80004224:  addi a4,a4,-616     -- a4 := 0x80019fb8
80004228:  beqz a0,0x800042cc  -- v.truthy == 0 (FALSY) → 0x800042cc (else-check)
                               --   (the truthy path `s0:=then; j 0x80004014` is the re-dispatch)
800042cc:  ld   s0,24(s0)      -- s0 := stmt->else  (offset 24; = 0 here, no else)
800042d0:  bnez s0,0x80004014  -- else present → re-dispatch; NOT taken (else absent)
800042d4:  li   a0,0           -- x10 := 0 = StatusCode .normal
800042d8:  j    0x8000409c     -- into the shared epilogue (execBlockD, status .normal)
```

## Structure of `execIfNoneSim`

`execIfNoneSim = execBlockA (kind 3, arm 0x800041e8) ≫ hGlue ≫ (li a0,0 ; j ; execBlockD)`.

Exactly like `execExprSim`, the head (`execBlockA`) and the tail (`li a0,0` at
`0x800042d4`, `j 0x8000409c`, then `execBlockD` with status `.normal`) are
threaded UNCONDITIONALLY around the arm-body glue `hGlue`, which reaches
`0x800042d4` in a `SubExecReturn` state (the same post-recursive-call state the
`expr` arm holds at `0x80004184`, only at a different link PC). `hGlue` bundles:

* the cond eval (`armTail_rec_es`, `EvalIH` for the condition `c`);
* the reload/copy of the 24-byte cond result into the `value_truthy` arg buffer;
* `value_truthy` (`value_truthy_spec`), yielding `a0 = 0` since `v.truthy = false`;
* the falsy branch `beqz a0` TAKEN (`0x800042cc`) and the no-else branch `bnez s0`
  NOT-taken (`stmt->else = 0`), reading the `else`-absence from the `Stmt` node.

The falsy hypothesis `v.truthy = false` and the else-absence are the genuine
`ifNone`-spec / AST-transport premises; here they are named residuals inside
`hGlue`, exactly as `execExprSim` carries its recursion glue as `hGlue`.

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

/-! ## `ExecIfNoneSimGoal` — the `ExecS.ifNone` simulation Triple (packaged) -/
def ExecIfNoneSimGoal
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (c : Expr) (t : Stmt) (v : Value)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String) : Prop :=
  Triple
    (fun cfg => ExecEntry g N A SL φf φc st d env (.ifStmt c t none) sp r aInterp aStmt aEnv aRet m0 cfg
      ∧ cfg.σ.sailOutput = out0)
    (ExecExit g N A SL φf φc st.store.frames.size st.store.closures.size
      st' .normal sp r aRet m0)

/-! ## `execIfNoneSim` — `ExecS.ifNone`: `execBlockA ≫ (arm body ≫ IH ≫ value_truthy) ≫ tail`

The head (`execBlockA`, prologue+dispatch to `0x800041e8`) and the tail (`li a0,0`
at `0x800042d4`, `j 0x8000409c`, then `execBlockD` with status `.normal`) are
threaded UNCONDITIONALLY around the arm-body glue `hGlue`, which consumes the
`EvalIH` for the condition and lands at `0x800042d4` in a `SubExecReturn` state.
This validates the same `execBlockA ≫ … ≫ execBlockD` skeleton as `execExprSim`,
for the `if`-with-falsy-cond-no-else arm. -/
theorem execIfNoneSim
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (c : Expr) (t : Stmt) (v : Value)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String)
    (_hSpec : ExecS st d env (.ifStmt c t none) st' .normal)
    (hIH : EvalIH st d env c st' v)
    -- execBlockA residuals (as for brk/cont/expr):
    (hslot : StmtSlotPinned 3 execArmIf m0)
    (htableStk : stmtJumpTableBase + 4 * 3 + 4 ≤ SL.lo ∨ sp.toNat ≤ stmtJumpTableBase + 4 * 3)
    -- the arm-body glue: from the arm-entry state at `0x800041e8` the condition
    -- setup + `jal eval_expr` + the sub-call (the `EvalIH`) + the reload/copy +
    -- `value_truthy` (result `0`, since `v.truthy = false`) + the falsy branch +
    -- the no-else branch reach `0x800042d4` in a `SubExecReturn` state. This is the
    -- statement-frame analog of `execExprSim`'s `hGlue`, only with the extra truthy
    -- + else-absence discharges folded in; RESIDUAL.
    (hGlue : EvalIH st d env c st' v →
      Triple
        (fun cfg => ∃ ment v8 v9 v18 v19,
          ExecArmEntryK g N A SL φf φc st execArmIf sp r aInterp aStmt aEnv aRet
            v8 v9 v18 v19 out0 m0 ment cfg)
        (fun cfg => ∃ subsret v1 v8 v9 v18 v19 mcall,
          SubExecReturn g N A SL φf φc st.store.frames.size st.store.closures.size st' v
            sp r aRet subsret (0x800042d4#64) v1 v8 v9 v18 v19 m0 mcall cfg)) :
    ExecIfNoneSimGoal g N A SL φf φc st st' d env c t v
      sp r aInterp aStmt aEnv aRet m0 out0 := by
  intro cfg hpre
  obtain ⟨he, hout0⟩ := hpre
  -- kind read `read32 m0 aStmt = 3` from the `.ifStmt … none` StmtRepr
  have hkind : read32 m0 aStmt.toNat = some 3 := by
    have := he.stmt; rw [he.mem] at this; cases this with
    | ifNoElse h0 _ _ _ _ _ => exact h0
  -- ===== head: execBlockA (prologue + dispatch → arm entry 0x800041e8) =====
  have hBlockA : ExecBlockAGoal g N A SL φf φc st d env (.ifStmt c t none)
      sp r aInterp aStmt aEnv aRet execArmIf m0 out0 :=
    execBlockA g N A SL φf φc st d env (.ifStmt c t none) 3 execArmIf
      sp r aInterp aStmt aEnv aRet m0 out0
      (by omega) (by omega) hkind hslot (by decide) ⟨htableStk⟩
  obtain ⟨cA, hstepsA, hArmExists⟩ := hBlockA cfg ⟨he, hout0⟩
  -- ===== glue: arm body + jal eval_expr + value_truthy + falsy branches → SubExecReturn =====
  obtain ⟨cG, hstepsG, hGlueOut⟩ := hGlue hIH cA hArmExists
  obtain ⟨subsret, v1, v8, v9, v18, v19, mcall, hSub⟩ := hGlueOut
  obtain ⟨hGG, htickG, hpcG, hraG, hspG, hs2G, ⟨vmiG, hmiG⟩, houtG, hframeG,
    hgx8, hgx9, hgx18, hgx19, hgx2, _hvalG, hstoreG, hcodeG,
    hslotRa, hslotS0, hslotS1, hslotS2, hslotS3,
    hsubWin, hmemframeG, _hmemExtG, hmemPreG⟩ := hSub
  -- ===== tail: 0x800042d4 `li a0,0` (x10 := 0 = StatusCode .normal) =====
  have hpcG' : cG.σ.regs.get? Register.PC = some (0x800042d4#64) := hpcG
  obtain ⟨σ1, i1, hstep1', hi1, hG1, hmem1, hobs1⟩ :=
    site_800042d4_es cG.σ cG.tick cG.steps (0x800042d4#64) vmiG hGG hpcG' hmiG hcodeG rfl htickG
  have hstep1 : Step cG ⟨σ1, i1, cG.steps + 1⟩ := by cases cG; exact hstep1'
  have hmem1e : σ1.mem = cG.σ.mem := hmem1
  have hpc1 : σ1.regs.get? Register.PC = some (0x800042d8#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x800042d4#64) 4 = (0x800042d8#64 : BitVec 64) from by decide] at this
  have ha0_1 : σ1.regs.get? Register.x10 = some (StatusCode .normal) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) = StatusCode .normal from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 176#64) := obs_alu_other' hobs1 Register.x2 (by decide) hspG
  have hra_1 : σ1.regs.get? Register.x1 = some (0x800042d4#64) := obs_alu_other' hobs1 Register.x1 (by decide) hraG
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
  -- ===== 0x800042d8 `j 0x8000409c` → PC := shared epilogue entry =====
  have htgt2d8 : (0x800042d8#64 + sign_extend (m := 64) (0x1ffdc4#21)).toNat % 4 = 0 := by decide
  obtain ⟨σ2, i2, hstep2', hi2, hG2, hmem2, hobs2⟩ :=
    site_800042d8_es σ1 i1 (cG.steps + 1) (0x800042d8#64) vmi1 hG1 hpc1 hmi1 hcode1 rfl htgt2d8 hi1
  have hstep2 : Step ⟨σ1, i1, cG.steps + 1⟩ ⟨σ2, i2, cG.steps + 1 + 1⟩ := hstep2'
  have hmem2e : σ2.mem = cG.σ.mem := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x8000409c#64) := by
    have := obs_jr_pc hobs2
    rwa [show (0x800042d8#64 + sign_extend (m := 64) (0x1ffdc4#21)) = (0x8000409c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have ha0_2 : σ2.regs.get? Register.x10 = some (StatusCode .normal) := obs_jr_other' hobs2 Register.x10 (by decide) ha0_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp - 176#64) := obs_jr_other' hobs2 Register.x2 (by decide) hsp_1
  have hra_2 : σ2.regs.get? Register.x1 = some (0x800042d4#64) := obs_jr_other' hobs2 Register.x1 (by decide) hra_1
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
    execBlockD g N A SL φfE φcE st.store.frames.size st.store.closures.size
      st' .normal sp r aRet v8 v9 v18 v19 σ2.sailOutput cG.σ.mem
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

end Vsa.Sim
