import Vsa.Sim.ExecBrkCont
import Vsa.Sim.Exec_stmtSites2
import Vsa.Sim.EvalRecCommon
import Vsa.Sim.ReprCopy

/-!
# Layer 4 — M4 first RECURSIVE statement cases: `ExecS.expr` (+ scaffolding for `ExecS.ret`)

The first statement cases that recurse into `eval_expr`. They validate the
recursive-statement pattern

    execBlockA  ≫  (arm sets up + jal eval_expr, consuming an EvalIH)  ≫  execBlockD

for the `exec_stmt` frame (176-byte, five callee-saved spills), the statement-side
analog of the expression-side recursive cases (`EvalNegSim`/`EvalBinSim`, which
use `armTail_rec` for the eval_expr frame).

## `ExecS.expr` — the `expr` arm (kind 0, `0x80004170`)

```
80004170:  ld   a2,8(s0)      -- a2 := stmt->expr  (the operand node, ExprRepr of e)
80004174:  addi a0,sp,16      -- a0 := sp' + 16    (the sub-call sret buffer, in-frame)
80004178:  mv   a3,s3         -- a3 := env         (unused by eval_expr's ABI; noise)
8000417c:  mv   a1,s1         -- a1 := interp*     (eval_expr ABI arg 1)
80004180:  jal  eval_expr     -- link 0x80004184; the recursive sub-derivation (EvalIH)
80004184:  li   a0,0          -- x10 := 0 = StatusCode .normal  (value discarded)
80004188:  j    0x8000409c    -- into the shared epilogue  (execBlockD, status .normal)
```

`ExecS.expr` evaluates `e` (store may change to `st'`), discards the value, and
completes `.normal`. So the machine sub-call is a full `eval_expr` on the operand
node; its returned value is thrown away (`li a0,0` clobbers the sret pointer in
`a0`), and only the store/output changes survive to the exit.

## `ExecS.ret` — the `ret` arm (kind 6, `0x80004120`, value-present path)

```
80004120:  ld   a2,8(s0)      -- a2 := stmt->expr
80004124:  beqz a2,…          -- (not taken: value present)
80004128:  mv   a3,s3         -- a3 := env
8000412c:  mv   a1,s1         -- a1 := interp*
80004130:  addi a0,sp,16      -- a0 := sp'+16 (local sret buffer)
80004134:  jal  eval_expr     -- the sub-derivation (EvalIH)
80004138:  ld   a3,16(sp) ; ld a4,24(sp) ; ld a5,32(sp)   -- reload the 24-byte result
80004144:  sd   a3,0(s2) ; sd a4,8(s2) ; sd a5,16(s2)     -- *retslot := v  (s2 = aRet)
80004150:  ld   ra,168(sp) … ld s3,136(sp) ; li a0,3 ; addi sp,176 ; ret
```

`ExecS.ret` evaluates `e` to `v`, copies `v` into the caller `retslot`, and
completes `.ret v` (exercising `ExecExit.retval`, the `retslot` disjunct).

## Status of this file

The straight-line arm SETUP + the epilogue TAIL are threaded here around the
recursion; the `jal eval_expr ≫ IH` glue is packaged as `SubExecReturn` (the
statement-frame analog of `SubEvalReturn`) — a NAMED RESIDUAL delivered as a
premise, exactly as `execBrkSim`/`blockB_unary` land conditional on their
`*Extras`/geometry residuals. `execExprSim` proves the full
`Triple (ExecEntry (.expr e)…) (ExecExit … st' .normal …)` conditional on:

* `hslot`/`htableStk` — the jump-table slot pin + stack-disjointness (`execBlockA`);
* `hGlue` — the recursion-glue residual: from the arm-entry state at `0x80004170`
  the setup + `jal eval_expr` + the sub-call (the `EvalIH`) reaches `0x80004184`
  in a `SubExecReturn` state (store `st'` re-represented, spills intact, output
  `st'.out`, callee-saved restored, memory framed).

`execExprSim`'s own contribution — the `execBlockA` head and the `li a0,0`/`j`/
`execBlockD` tail wrapped UNCONDITIONALLY around `hGlue` — is what validates the
`execBlockA ≫ … ≫ execBlockD` recursive-statement skeleton.

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

/-! ## `SubExecReturn` — the post-sub-call machine state (exec_stmt frame)

The statement-frame analog of `SubEvalReturn` (`EvalRecCommon.lean`). What the
`expr`/`ret` arm knows after its `jal eval_expr` returns (link PC `retPC`), for a
sub-derivation with post spec state `st'` and returned value `vsub` in the buffer
`subsret`:

* control back at `retPC`, `sp` still lowered (`sp - 176`), `s2 = aRet` (retslot),
  the four exec_stmt spill slots (`sp-{8,16,24,32,40}`) intact for the epilogue;
* callee-saved registers restored to the arm-frame ghost `garm`;
* the sub-result `ValueRepr` at `subsret` (extended `φc'`) — used by `ret` for the
  24-byte copy (`expr` discards it);
* `st'.store` re-represented at ONE coherent extended pair, WITH the stack-region
  survival clause;
* console output `= st'.out`; `exec_stmt`'s code still loaded;
* memory framed to the pre-call memory `mcall` outside
  (stack-window ∪ arena ∪ subsret-window), presence-extended.

`garm` is the arm-entry register frame (post-`execBlockA`): `x8 = aStmt`,
`x9 = aInterp`, `x18 = aRet`, `x19 = aEnv`, `x2 = sp`. -/
def SubExecReturn
    (garm : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st' : Vsa.While.St) (vsub : Value)
    (sp r aRet subsret retPC : BitVec 64) (v1 v8 v9 v18 v19 : BitVec 64)
    (m0 mcall : Mem)
    (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some retPC ∧
  c.σ.regs.get? Register.x1 = some retPC ∧
  c.σ.regs.get? Register.x2 = some (sp - 176#64) ∧
  c.σ.regs.get? Register.x18 = some aRet ∧             -- s2 = retslot (for the ret copy)
  (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
  OutRepr c.σ st' ∧
  -- callee-saved registers (excl s0/s1/s2/s3/sp) restored to the arm frame
  (∀ R : Register, AbiPreservedNoise R →
    (Register.x8 == R) = false → (Register.x9 == R) = false →
    (Register.x18 == R) = false → (Register.x19 == R) = false →
    (Register.x2 == R) = false → c.σ.regs.get? R = garm R) ∧
  garm Register.x8 = some v8 ∧ garm Register.x9 = some v9 ∧
  garm Register.x18 = some v18 ∧ garm Register.x19 = some v19 ∧ garm Register.x2 = some sp ∧
  (∃ φc' : Addr → Nat, PhiExtends φc φc' st'.store.closures.size ∧
    ValueRepr c.σ.mem N φc' subsret.toNat vsub) ∧
  (∃ φf' φc' : Addr → Nat,
    PhiExtends φf φf' st'.store.frames.size ∧
    PhiExtends φc φc' st'.store.closures.size ∧
    StoreRepr c.σ.mem N A φf' φc' st'.store) ∧
  Exec_stmtLoaded c.σ.mem ∧
  read64 c.σ.mem (sp.toNat - 8) = some r.toNat ∧
  read64 c.σ.mem (sp.toNat - 16) = some v8.toNat ∧
  read64 c.σ.mem (sp.toNat - 24) = some v9.toNat ∧
  read64 c.σ.mem (sp.toNat - 32) = some v18.toNat ∧
  read64 c.σ.mem (sp.toNat - 40) = some v19.toNat ∧
  -- the sub-sret buffer is inside the (lowered) exec_stmt frame — so it is inside
  -- the stack window `[SL.lo, sp)` (it lives at `sp' + 16`).
  (SL.lo ≤ subsret.toNat ∧ subsret.toNat + 24 ≤ sp.toNat) ∧
  -- memory framed to the pre-call memory outside stack ∪ arena ∪ subsret
  (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
    (subsret.toNat ≤ a ∧ a < subsret.toNat + 24) ∨ c.σ.mem[a]? = mcall[a]?) ∧
  MemExtends mcall c.σ.mem ∧
  -- the pre-call memory equals the arm-entry memory outside the stack window
  (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]?)

/-! ## `ExecExprSimGoal` — the `ExecS.expr` simulation Triple (packaged) -/
def ExecExprSimGoal
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr) (v : Value)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String) : Prop :=
  Triple
    (fun c => ExecEntry g N A SL φf φc st d env (.expr e) sp r aInterp aStmt aEnv aRet m0 c
      ∧ c.σ.sailOutput = out0)
    (ExecExit g N A SL φf φc st' .normal sp r aRet m0)

/-! ## `execExprSim` — `ExecS.expr`: `execBlockA ≫ (jal eval_expr ≫ IH) ≫ execBlockD`

The head (`execBlockA`, prologue+dispatch to `0x80004170`) and the tail
(`li a0,0` at `0x80004184`, `j 0x8000409c`, then `execBlockD` with status
`.normal`) are threaded UNCONDITIONALLY around the recursion glue `hGlue` (which
consumes the `EvalIH` for the sub-expression). This validates the
`execBlockA ≫ EvalIH ≫ execBlockD` skeleton for every recursive statement case. -/
theorem execExprSim
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr) (v : Value)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String)
    (_hSpec : ExecS st d env (.expr e) st' .normal)
    (hIH : EvalIH st d env e st' v)
    -- execBlockA residuals (as for brk/cont):
    (hslot : StmtSlotPinned 0 execArmExpr m0)
    (htableStk : stmtJumpTableBase + 4 * 0 + 4 ≤ SL.lo ∨ sp.toNat ≤ stmtJumpTableBase + 4 * 0)
    -- the recursion glue: the arm setup (`ld a2,8(s0)`, `addi a0,sp,16`, two `mv`)
    -- + `jal eval_expr` + the sub-call (consuming the IH) reach the link PC
    -- `0x80004184` in a `SubExecReturn` state. The sub-sret buffer `subsret` and
    -- the pre-call memory `mcall` are existentially chosen inside. This is the
    -- statement-frame analog of `armTail_rec` (`EvalRecCommon.lean`), instantiated
    -- for the 176-byte `exec_stmt` frame; RESIDUAL.
    (hGlue : EvalIH st d env e st' v →
      Triple
        (fun c => ∃ ment v8 v9 v18 v19,
          ExecArmEntryK g N A SL φf φc st execArmExpr sp r aInterp aStmt aEnv aRet
            v8 v9 v18 v19 out0 m0 ment c)
        (fun c => ∃ subsret v1 v8 v9 v18 v19 mcall,
          SubExecReturn g N A SL φf φc st' v
            sp r aRet subsret (0x80004184#64) v1 v8 v9 v18 v19 m0 mcall c)) :
    ExecExprSimGoal g N A SL φf φc st st' d env e v
      sp r aInterp aStmt aEnv aRet m0 out0 := by
  intro c hpre
  obtain ⟨he, hout0⟩ := hpre
  -- kind read `read32 m0 aStmt = 0` from the `.expr` StmtRepr
  have hkind : read32 m0 aStmt.toNat = some 0 := by
    have := he.stmt; rw [he.mem] at this; cases this with
    | expr h0 _ _ => exact h0
  -- ===== head: execBlockA (prologue + dispatch → arm entry 0x80004170) =====
  have hBlockA : ExecBlockAGoal g N A SL φf φc st d env (.expr e)
      sp r aInterp aStmt aEnv aRet execArmExpr m0 out0 :=
    execBlockA g N A SL φf φc st d env (.expr e) 0 execArmExpr
      sp r aInterp aStmt aEnv aRet m0 out0
      (by omega) (by omega) hkind hslot (by decide) ⟨htableStk⟩
  obtain ⟨cA, hstepsA, hArmExists⟩ := hBlockA c ⟨he, hout0⟩
  -- ===== glue: arm setup + jal eval_expr + sub-call (the IH) → SubExecReturn =====
  obtain ⟨cG, hstepsG, hGlueOut⟩ := hGlue hIH cA hArmExists
  obtain ⟨subsret, v1, v8, v9, v18, v19, mcall, hSub⟩ := hGlueOut
  obtain ⟨hGG, htickG, hpcG, hraG, hspG, hs2G, ⟨vmiG, hmiG⟩, houtG, hframeG,
    hgx8, hgx9, hgx18, hgx19, hgx2, _hvalG, hstoreG, hcodeG,
    hslotRa, hslotS0, hslotS1, hslotS2, hslotS3,
    hsubWin, hmemframeG, _hmemExtG, hmemPreG⟩ := hSub
  -- ===== tail: 0x80004184 `li a0,0` (x10 := 0 = StatusCode .normal) =====
  have hpcG' : cG.σ.regs.get? Register.PC = some (0x80004184#64) := hpcG
  obtain ⟨σ1, i1, hstep1', hi1, hG1, hmem1, hobs1⟩ :=
    site_80004184_es cG.σ cG.tick cG.steps (0x80004184#64) vmiG hGG hpcG' hmiG hcodeG rfl htickG
  have hstep1 : Step cG ⟨σ1, i1, cG.steps + 1⟩ := by cases cG; exact hstep1'
  have hmem1e : σ1.mem = cG.σ.mem := hmem1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80004188#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80004184#64) 4 = (0x80004188#64 : BitVec 64) from by decide] at this
  have ha0_1 : σ1.regs.get? Register.x10 = some (StatusCode .normal) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) = StatusCode .normal from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 176#64) := obs_alu_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspG
  have hra_1 : σ1.regs.get? Register.x1 = some (0x80004184#64) := obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hraG
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
  -- ===== 0x80004188 `j 0x8000409c` → PC := shared epilogue entry =====
  have htgt188 : (0x80004188#64 + sign_extend (m := 64) (0x1fff14#21)).toNat % 4 = 0 := by decide
  obtain ⟨σ2, i2, hstep2', hi2, hG2, hmem2, hobs2⟩ :=
    site_80004188_es σ1 i1 (cG.steps + 1) (0x80004188#64) vmi1 hG1 hpc1 hmi1 hcode1 rfl htgt188 hi1
  have hstep2 : Step ⟨σ1, i1, cG.steps + 1⟩ ⟨σ2, i2, cG.steps + 1 + 1⟩ := hstep2'
  have hmem2e : σ2.mem = cG.σ.mem := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x8000409c#64) := by
    have := obs_jr_pc hobs2
    rwa [show (0x80004188#64 + sign_extend (m := 64) (0x1fff14#21)) = (0x8000409c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have ha0_2 : σ2.regs.get? Register.x10 = some (StatusCode .normal) := obs_jr_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp - 176#64) := obs_jr_other hobs2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_1
  have hra_2 : σ2.regs.get? Register.x1 = some (0x80004184#64) := obs_jr_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
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
  -- entry-frame geometry (from ExecEntry.stackOK etc.), reused for the epilogue restores.
  have hstackOK := he.stackOK
  obtain ⟨hSLlo, hsphi, hsp16⟩ := hstackOK
  have hsp176 : 176 ≤ sp.toNat := by
    have := he.stack_win; have := he.stack_ram.1
    have htoh : tohostAddr = 0x8001ad00 := rfl; omega
  have hraAl := he.ra_align
  -- ===== execBlockD (at the EXTENDED maps, baseline `m0 := cG.σ.mem`) → ExecExit
  -- Using the pre-call/exit memory itself as the `execBlockD` baseline makes the
  -- (arena-agnostic) `PreExecEpilogue.memFrame` obligation trivial (`= rfl`); the
  -- resulting `ExecExit.memFrame` is then relative to `cG.σ.mem`, and we re-base it
  -- to the true entry `m0` from the `SubExecReturn` framing below. =====
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
    · -- heqG : cD.σ.mem[a]? = cG.σ.mem[a]?; cG.σ.mem[a]? = mcall[a]? = m0[a]? off stack/arena
      rcases hmemframeG a hstk harena with hsub | heqC
      · -- a ∈ [subsret, subsret+24): subsret ⊂ [SL.lo, sp), so this contradicts `hstk`.
        exact absurd (⟨by omega, by omega⟩ : SL.lo ≤ a ∧ a < sp.toNat) hstk
      · exact Or.inr (by rw [heqG, heqC, hmemPreG a hstk])

end Vsa.Sim
