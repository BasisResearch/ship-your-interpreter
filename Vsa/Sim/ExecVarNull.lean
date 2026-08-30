import Vsa.Sim.ExecVarDecl
import Vsa.Sim.ObsAvoid

/-!
# Layer 4 — M4 statement case: `ExecS.varNull` (variable declaration, no initializer)

The `varDecl` arm (kind 1, `0x800040d8`) with NO initializer (`.varDecl x none`).
The `beqz a2` at `0x800040dc` is TAKEN (`a2 = stmt->init = 0`), redirecting to the
`value_null` bridge at `0x800042fc`, which materialises a `.null` `Value` in the
local sret buffer (`sp'+0x68`) and jumps BACK to the shared varDecl tail at
`0x800040f0`:

```
800040d8:  ld   a2,0x10(s0)   -- a2 := stmt->init = 0 (varNull ⇒ null pointer)
800040dc:  beqz a2,0x800042fc -- (TAKEN: no initializer)   → varNull
…
800042fc:  addi a0,sp,0x68    -- a0 := sp'+0x68     (the sub-call sret buffer, in-frame)
80004300:  jal  value_null    -- fill the buffer with a null Value, link 0x80004304
80004304:  j    0x800040f0    -- rejoin the shared varDecl reload/define tail
800040f0:  ld   a1,0x8(s0)    -- a1 := stmt->name   (the variable name pointer)   [varNull rejoins]
800040f4:  ld   a3,0x68(sp)   -- reload the 24-byte value word0
800040f8:  ld   a4,0x70(sp)   --   … word1
800040fc:  ld   a5,0x78(sp)   --   … word2
80004100:  mv   a0,s3         -- a0 := env          (env_define ABI arg 0)
80004104:  addi a2,sp,0x10    -- a2 := sp'+0x10     (the value buffer for env_define)
80004108:  sd   a3,0x10(sp)   -- *pv         := word0
8000410c:  sd   a4,0x18(sp)   -- *(pv+8)     := word1
80004110:  sd   a5,0x20(sp)   -- *(pv+16)    := word2
80004114:  jal  env_define    -- link 0x80004118; env_define(env, name, pv) — Store.define
80004118:  li   a0,0          -- x10 := 0 = StatusCode .normal
8000411c:  j    0x8000409c    -- into the shared epilogue (execBlockD, status .normal)
```

`ExecS.varNull` binds `x` to `.null` in the current frame via
`st.store.define env x .null` (state otherwise unchanged), completing `.normal`.
So the machine arm produces `.null` in the sret buffer via the `value_null` bridge
(instead of `eval_expr`), re-stages it into the `pv` buffer, then a full
`env_define(env, name, pv)` — the `Store.define` — and finally `li a0,0`.

## The `env_define` callee

The `env_define` call site is `0x80004114`, entry PC `0x80002a5c`, ABI
`env_define(env=a0, name=a1, pv=a2)` (matching `EnvDefEntryCommon.EnvDefineEntry`
`x10=env, x11=name, x12=pv`). **M3 verified `env_define`'s prologue only**
(`EnvDefSpec17.env_define_prologue`: `0x80002a5c → 0x80002a90`,
`EnvDefinePrologueReady`); the composed callee contract — the scan loop, the
in-place update path, and the append/grow path (strlen + malloc + memcpy +
realloc×2, no landed realloc spec) that actually produce `Store.define env x v`
with a re-established `StoreRepr` — is documented in `EnvDefSpec.lean` as *staged
but not closed*. There is therefore **no top-level `env_define` Triple to reuse**;
this case bridges it as a NAMED RESIDUAL, exactly as `execExprSim` bridges its
recursion glue `hGlue` (`ExecExprRet.lean`) and `execRetSim` its `hGlue`.

## Status of this file

`execVarDeclNullSim` is the `.varDecl x none` mirror of `execVarDeclSim`. The tail
(`li a0,0` at `0x80004118`, `j 0x8000409c`, `execBlockD .normal`) is LITERALLY the
same code and the same proof — only the value is `.null` and the store post-state
is `⟨st.store.define env x .null, st.out⟩`. It is conditional on:

* `hslot`/`htableStk` — the jump-table slot pin + stack-disjointness (`execBlockA`);
* `hGlue` — the varNull-body glue: from the arm-entry state at `0x800040d8` the
  whole body (the `beqz`-TAKEN `value_null` bridge `0x800042fc → jal value_null →
  j 0x800040f0`, then the value reload/copy + `jal env_define` producing
  `Store.define`) reaches `0x80004118` in a `SubExecReturn` state for the DEFINED
  post-state `⟨st.store.define env x .null, st.out⟩`. (The `env_define` callee has
  no landed top-level Triple — M3 verified its prologue only; RESIDUAL.)

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

/-! ## `ExecVarNullSimGoal` — the `ExecS.varNull` simulation Triple (packaged)

The post-state is `⟨st.store.define env x .null, st.out⟩`, exactly the
`ExecS.varNull` conclusion; the status is `.normal`. -/
def ExecVarNullSimGoal
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (x : String)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String) : Prop :=
  Triple
    (fun c => ExecEntry g N A SL φf φc st d env (.varDecl x none)
        sp r aInterp aStmt aEnv aRet m0 c ∧ c.σ.sailOutput = out0)
    (ExecExit g N A SL φf φc st.store.frames.size st.store.closures.size
      ⟨st.store.define env x .null, st.out⟩ .normal sp r aRet m0)

/-! ## `execVarDeclNullSim` — `ExecS.varNull`: `execBlockA ≫ (value_null body glue) ≫ execBlockD`

The `.varDecl x none` mirror of `execVarDeclSim`. The head (`execBlockA`,
prologue+dispatch to `0x800040d8`) and the tail (`li a0,0` at `0x80004118`,
`j 0x8000409c`, then `execBlockD .normal`) are threaded UNCONDITIONALLY around the
body glue `hGlue`, which now takes the `beqz`-TAKEN `value_null` bridge rather than
`jal eval_expr`. The tail is LITERALLY the `execVarDeclSim` tail with `v := .null`
and the store `st.store.define env x .null`. -/
theorem execVarDeclNullSim
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (x : String)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String)
    (_hSpec : ExecS st d env (.varDecl x none)
      ⟨st.store.define env x .null, st.out⟩ .normal)
    -- execBlockA residuals (as for brk/cont/expr):
    (hslot : StmtSlotPinned 1 execArmVarDecl m0)
    (htableStk : stmtJumpTableBase + 4 * 1 + 4 ≤ SL.lo ∨ sp.toNat ≤ stmtJumpTableBase + 4 * 1)
    -- the body glue: from the arm-entry state at `0x800040d8`, the whole varNull
    -- body (the `beqz`-TAKEN `value_null` bridge, then the value reload/copy +
    -- `jal env_define` — the `env_define` callee producing `Store.define`) reaches
    -- the link PC `0x80004118` in a `SubExecReturn` state for the DEFINED post-state
    -- `⟨st.store.define env x .null, st.out⟩`. The sub-sret buffer `subsret` and the
    -- pre-call memory `mcall` are existentially chosen inside; RESIDUAL.
    (hGlue :
      Triple
        (fun c => ∃ ment v8 v9 v18 v19,
          ExecArmEntryK g N A SL φf φc st execArmVarDecl sp r aInterp aStmt aEnv aRet
            v8 v9 v18 v19 out0 m0 ment c)
        (fun c => ∃ subsret v1 v8 v9 v18 v19 mcall,
          SubExecReturn g N A SL φf φc st.store.frames.size st.store.closures.size
            ⟨st.store.define env x .null, st.out⟩ .null
            sp r aRet subsret (0x80004118#64) v1 v8 v9 v18 v19 m0 mcall c)) :
    ExecVarNullSimGoal g N A SL φf φc st d env x
      sp r aInterp aStmt aEnv aRet m0 out0 := by
  intro c hpre
  obtain ⟨he, hout0⟩ := hpre
  -- kind read `read32 m0 aStmt = 1` from the `.varDecl x none` StmtRepr
  have hkind : read32 m0 aStmt.toNat = some 1 := by
    have := he.stmt; rw [he.mem] at this; cases this with
    | varNull h0 _ _ _ => exact h0
  -- ===== head: execBlockA (prologue + dispatch → arm entry 0x800040d8) =====
  have hBlockA : ExecBlockAGoal g N A SL φf φc st d env (.varDecl x none)
      sp r aInterp aStmt aEnv aRet execArmVarDecl m0 out0 :=
    execBlockA g N A SL φf φc st d env (.varDecl x none) 1 execArmVarDecl
      sp r aInterp aStmt aEnv aRet m0 out0
      (by omega) (by omega) hkind hslot (by decide) ⟨htableStk⟩
  obtain ⟨cA, hstepsA, hArmExists⟩ := hBlockA c ⟨he, hout0⟩
  -- ===== glue: whole varNull body (value_null bridge + env_define) → SubExecReturn =====
  obtain ⟨cG, hstepsG, hGlueOut⟩ := hGlue cA hArmExists
  obtain ⟨subsret, v1, v8, v9, v18, v19, mcall, hSub⟩ := hGlueOut
  obtain ⟨hGG, htickG, hpcG, hraG, hspG, hs2G, ⟨vmiG, hmiG⟩, houtG, hframeG,
    hgx8, hgx9, hgx18, hgx19, hgx2, _hvalG, hstoreG, hcodeG,
    hslotRa, hslotS0, hslotS1, hslotS2, hslotS3,
    hsubWin, hmemframeG, _hmemExtG, hmemPreG⟩ := hSub
  -- ===== tail: 0x80004118 `li a0,0` (x10 := 0 = StatusCode .normal) =====
  have hpcG' : cG.σ.regs.get? Register.PC = some (0x80004118#64) := hpcG
  obtain ⟨σ1, i1, hstep1', hi1, hG1, hmem1, hobs1⟩ :=
    site_80004118_es cG.σ cG.tick cG.steps (0x80004118#64) vmiG hGG hpcG' hmiG hcodeG rfl htickG
  have hstep1 : Step cG ⟨σ1, i1, cG.steps + 1⟩ := by cases cG; exact hstep1'
  have hmem1e : σ1.mem = cG.σ.mem := hmem1
  have hpc1 : σ1.regs.get? Register.PC = some (0x8000411c#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80004118#64) 4 = (0x8000411c#64 : BitVec 64) from by decide] at this
  have ha0_1 : σ1.regs.get? Register.x10 = some (StatusCode .normal) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) = StatusCode .normal from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 176#64) := obs_alu_other' hobs1 Register.x2 (by decide) hspG
  have hra_1 : σ1.regs.get? Register.x1 = some (0x80004118#64) := obs_alu_other' hobs1 Register.x1 (by decide) hraG
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hcode1 : Exec_stmtLoaded σ1.mem := by rw [hmem1e]; exact hcodeG
  -- the `li a0` is an ALU write to x10 only; carry the SubExecReturn frame through it
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
  -- ===== 0x8000411c `j 0x8000409c` → PC := shared epilogue entry =====
  have htgt411c : (0x8000411c#64 + sign_extend (m := 64) (0x1fff80#21)).toNat % 4 = 0 := by decide
  obtain ⟨σ2, i2, hstep2', hi2, hG2, hmem2, hobs2⟩ :=
    site_8000411c_es σ1 i1 (cG.steps + 1) (0x8000411c#64) vmi1 hG1 hpc1 hmi1 hcode1 rfl htgt411c hi1
  have hstep2 : Step ⟨σ1, i1, cG.steps + 1⟩ ⟨σ2, i2, cG.steps + 1 + 1⟩ := hstep2'
  have hmem2e : σ2.mem = cG.σ.mem := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x8000409c#64) := by
    have := obs_jr_pc hobs2
    rwa [show (0x8000411c#64 + sign_extend (m := 64) (0x1fff80#21)) = (0x8000409c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have ha0_2 : σ2.regs.get? Register.x10 = some (StatusCode .normal) := obs_jr_other' hobs2 Register.x10 (by decide) ha0_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp - 176#64) := obs_jr_other' hobs2 Register.x2 (by decide) hsp_1
  have hra_2 : σ2.regs.get? Register.x1 = some (0x80004118#64) := obs_jr_other' hobs2 Register.x1 (by decide) hra_1
  obtain ⟨vmi2, hmi2⟩ := obs_jr_minstret hobs2
  have hcode2 : Exec_stmtLoaded σ2.mem := by rw [hmem2e]; exact hcodeG
  have hframe2 : ∀ R : Register, AbiPreservedNoise R → (Register.x10 == R) = false →
      σ2.regs.get? R = cG.σ.regs.get? R := by
    intro R hR h10
    obtain ⟨_, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ := id hR
    exact ((hobs2.1 R hmc' hmt' hmip').trans
      (get?_sigmaPost_jump_x0 _ _ _ _ R hmi' hpc' hnpc' hmii')).trans (hframe1 R hR h10)
  -- output through the two tail steps: `String.join σ2.sailOutput.toList = stPost.out`
  have hout2 : String.join σ2.sailOutput.toList = (⟨st.store.define env x .null, st.out⟩ : Vsa.While.St).out := by
    have h : String.join cG.σ.sailOutput.toList = (⟨st.store.define env x .null, st.out⟩ : Vsa.While.St).out := houtG
    rw [hobs2.out, sailOutput_sigmaPost_jump_x0, hobs1.out, sailOutput_sigmaPost_alu]; exact h
  -- the extended store maps from the sub-call, and the geometry the epilogue needs.
  obtain ⟨φfE, φcE, hpfE, hpcE, hstoreE⟩ := hstoreG
  -- entry-frame geometry (from ExecEntry.stackOK etc.), reused for the epilogue restores.
  have hstackOK := he.stackOK
  obtain ⟨hSLlo, hsphi, hsp16⟩ := hstackOK
  have hsp176 : 176 ≤ sp.toNat := by
    have := he.stack_win; have := he.stack_ram.1
    have htoh : tohostAddr = 0x8001ad00 := rfl; omega
  have hraAl := he.ra_align
  -- ===== execBlockD (at the EXTENDED maps, baseline `m0 := cG.σ.mem`) → ExecExit =====
  obtain ⟨cD, hstepsD, hExitE⟩ :=
    execBlockD g N A SL φfE φcE st.store.frames.size st.store.closures.size
      ⟨st.store.define env x .null, st.out⟩ .normal sp r aRet
      v8 v9 v18 v19 σ2.sailOutput cG.σ.mem
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
        (by intro a _; rfl),   -- mpre = cG.σ.mem baseline ⇒ trivial
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
  · -- store: compose PhiExtends φf φfE (sub-call) with PhiExtends φfE φf'' (execBlockD refl)
    obtain ⟨φf'', φc'', hpf'', hpc'', hst''⟩ := hExitE.store
    exact ⟨φf'', φc'',
      PhiExtends.trans hpfE hpf'', PhiExtends.trans hpcE hpc'', hst''⟩
  · -- memFrame: re-base from `cG.σ.mem` to `m0` via SubExecReturn's framing.
    intro a hstk harena
    have hbase := hExitE.memFrame a hstk harena
    rcases hbase with hret | heqG
    · exact Or.inl hret
    · rcases hmemframeG a hstk harena with hsub | heqC
      · exact absurd (⟨by omega, by omega⟩ : SL.lo ≤ a ∧ a < sp.toNat) hstk
      · exact Or.inr (by rw [heqG, heqC, hmemPreG a hstk])

end Vsa.Sim
