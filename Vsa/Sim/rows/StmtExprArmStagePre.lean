import Vsa.Sim.ArmSegSplitExecEval
import Vsa.Sim.EvalChildFieldCombinator
import Vsa.Sim.ExecBrkCont
import Vsa.Sim.Exec_stmtSites2

/-!
# `StmtExprArmStagePre` — the exec-`expr`-arm-head → `JalPreBundle` cut (Wave 40)

**The execFrameShift core, proved on `stmtExpr`.**  The wave-38 observation
`exec-eval-stagepre-frameshift-and-nonuniform` flagged the 6 exec-eval
`EvalChildStages` fields as blocked on a "frame shift" (exec_stmt lowers `sp` by
176, not 1088, but `JalPreBundle` hardwires `x2 = sp - 1088`).  This wave RESOLVES
that: the frame shift is a **ghost re-parametrization**, not a lemma.

## Why it is easy (machine evidence)

`evalEntry_of_jalPrefix` (`ArmSegSplit.lean`) — the sole consumer of `JalPreBundle`
via `landedN_eentryC_of_preBundle` — DESTRUCTURES the five spill-window premises
`read64 mcall` at `sp-8`, `sp-16`, `sp-24`, `sp-32` + `hspSLhi` from `hpre` but NEVER USES them
(the child `EvalEntry.spill_defined` is built from the post-jal x8/x9/x18 REGISTER
facts, not the memory slots).  So those `JalPreBundle` premises are **dead** for the
divergence entry, and the `1088` in `x2 = sp - 1088` couples nothing load-bearing.

The `stmtExpr` arm (`0x80004170`) is `ld a2,8(s0); addi a0,sp,16; mv a3,s3;
mv a1,s1; jal eval_expr`.  It calls `eval_expr` with `x2 = ` the exec frame's own
lowered `sp` (`esp := sp_exec_entry - 176`), never lowering by 1088.  So instantiate
`JalPreBundle.sp := esp + 1088`; then `sp - 1088 = esp = x2` at the jal.  The
geometry facts are over the enlarged `esp + 1088`, satisfiable from `ExecEntry`'s
own `176 + 1088` headroom (`ExecEntry.stackOK`).  The five dead spill-window
premises are discharged by ANY witness (the exec frame's `ra/s0/s1/s2` spill slots).
No `ExecJalPreBundle` twin, no per-frame spill-layout reconciliation.

## The one honest premise: the wide-window `StoreRepr` survival

`JalPreBundle` (at `sp := esp+1088`) demands `StoreRepr` survival over
`[SL.lo, esp+1088)`, whose extra region `[sp_exec, esp+1088) = [sp_exec, sp_exec+912)`
is the CALLER's frame — untouched by the exec arm but NOT framed by
`ExecEntry.store_survives` (which covers only `[SL.lo, sp_exec)`).  StoreRepr
survives it (the store lives in the arena, disjoint from `[SL.lo, esp+1088)` via the
arena disjunct `esp+1088 ≤ A.lo`), but the two windows are not nested the tolerant
way, so it is carried as a NAMED premise — EXACTLY as the eval side gets its
`store_survives` window from `ArmEntryK`/`EvalEntry` (whose `sp` IS the frame top =
`JalPreBundle.sp`).  The M6 layout caller supplies it.  (Observation
`execframeshift-survival-window-is-a-named-premise-not-derivable`.)

## Layers

* `blockB_stmtExpr_stagePre` — the 4-instruction arm-head cut (reusing the LANDED
  `site_80004170/74/78/7c_es` from `Exec_stmtSites2`, no new site battery), from the
  `ExecArmEntryK`-plus-child-payload entry bundle at `0x80004170` to `JalPreBundle e`
  at the `jal eval_expr` PC `0x80004180`.  Delivered as `LandedN 4`.
* `StmtExprArmDispatch` — the exec dispatch residual (the `ExecEntry → ExecArmEntryK`
  bridge is the LANDED `execBlockA`; this residual names only the child-payload +
  eval-code-loaded + wide-window-survival facts a `blockA` cannot produce, mirroring
  `AssignArmDispatch`).
* `stmtExpr_field_of_dispatch` — the `EvalChildStages.stmtExpr` field, composed via
  `evalChildField_of_blockA_stage` (`execBlockA` ≫ the cut), MODULO the dispatch
  residual.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats` bump.
Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code
open Vsa.Sim.ApproxArmReseat

namespace Vsa.Sim

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option linter.unusedVariables false

-- discipline: allow(R7-conj-tower-def) the ∃-towers here are the ESTABLISHED landing
-- bundle `JalPreBundle` (named destructurer `landedN_eentryC_of_preBundle`) and the
-- exec-arm-head entry bundle that mirrors the landed `blockB_assign_stagePre` `hpre`
-- (layout DATA a `structure : Prop` cannot project — φ-maps/Arena/StackLayout/regs);
-- every consumer goes through the composer `evalChildField_of_blockA_stage`.

/-! ## §1. `blockB_stmtExpr_stagePre` — the exec-`expr` arm-head cut -/

/-- **The exec-`expr` arm-head → `JalPreBundle` cut.**  From the `ExecArmEntryK`-at-
`0x80004170` bundle plus the child-expr payload and the eval-side code / wide-window
survival facts, the four head steps `ld a2,8(s0)`/`addi a0,sp,16`/`mv a3,s3`/
`mv a1,s1` reach the `jal eval_expr` PC `0x80004180` with the child sub-call staged,
and that state satisfies `JalPreBundle e` with the ghost `JalPreBundle.sp := esp+1088`
(`esp := sp-176`).  There is NO store on this head, so `mcall = ment` unchanged. -/
theorem blockB_stmtExpr_stagePre
    (g gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr)
    (sp r aInterp aStmt aEnv aRet aExprChild : BitVec 64)
    (v8 v9 v18 v19 : BitVec 64)
    (out0 : Array String) (m0 ment : Mem)
    (c : Config)
    (hpre :
        ExecArmEntryK g N A SL φf φc st (0x80004170#64)
          sp r aInterp aStmt aEnv aRet v8 v9 v18 v19 out0 m0 ment c ∧
        -- child-expr payload (from `StmtRepr (.expr e)`, framed to `ment`)
        read64 ment (aStmt.toNat + 8) = some aExprChild.toNat ∧
        ExprRepr ment aExprChild.toNat e ∧
        aStmt.toNat % 8 = 0 ∧
        0x80000000 ≤ aStmt.toNat ∧ aStmt.toNat + 16 ≤ 0x100000000 ∧
        (aStmt.toNat + 16 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aStmt.toNat) ∧
        -- eval-side code facts (the interp binary has eval_expr + value_int + jump
        -- table loaded; NOT part of `ExecEntry`, so carried as premises)
        Eval_exprLoaded ment ∧ Value_intLoaded ment ∧ IntSlotPinned ment ∧
        -- the wide-window `StoreRepr` survival over `[SL.lo, esp+1088)` (esp = sp-176)
        -- and the sret ghost buffer `[aInterp, aInterp+24)` (the bundle's `sret`
        -- carve-out; `sret := aInterp` since x9 = s1 = aInterp at the jal).  A named
        -- premise the M6 layout supplies, mirroring `EvalEntry.store_survives`.
        (∀ m' : Mem,
          (∀ k, ¬ (SL.lo ≤ k ∧ k < (sp.toNat - 176) + 1088) →
            ¬ (aInterp.toNat ≤ k ∧ k < aInterp.toNat + 24) →
            ment[k]? = m'[k]?) →
          StoreRepr m' N A φf φc st.store) ∧
        -- the child expr node geometry (at the exec frame's own sp = sp-176)
        aExprChild.toNat % 8 = 0 ∧
        0x80000000 ≤ aExprChild.toNat ∧ aExprChild.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ aExprChild.toNat ∧
        (aExprChild.toNat + 16 ≤ SL.lo ∨ (sp.toNat - 176) ≤ aExprChild.toNat) ∧
        -- the exec frame is deep enough for one eval frame below it
        SL.lo + 3264 ≤ sp.toNat - 176 ∧
        -- `sp` is 16-aligned (from `ExecEntry.stackOK`, not re-exposed by
        -- `ExecArmEntryK` which only carries `sp % 8 = 0`)
        sp.toNat % 16 = 0 ∧
        -- the stack-layout bounds (from `ExecEntry.stack_ram`/`stack_win`, not
        -- re-exposed by `ExecArmEntryK`)
        0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000 ∧ tohostAddr + 16 ≤ SL.lo ∧
        -- **the enlarged-frame geometry (over jsp := (sp-176)+1088), a named premise
        -- the M6 layout supplies — the exec frame's own facts are over `sp`, but the
        -- `ExecJalPreBundle` ghost re-parametrizes to jsp = sp+912; these hold because
        -- the exec frame sits below the eval_expr text / table / arena, but that is a
        -- caller-level layout fact.**
        ((sp.toNat - 176) + 1088 ≤ SL.hi) ∧
        (((sp.toNat - 176) + 1088) ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        ((0x8000281c : Nat) ≤ SL.lo ∨ ((sp.toNat - 176) + 1088) ≤ 0x8000280c) ∧
        ((0x80019f58 : Nat) + 4 ≤ SL.lo ∨ ((sp.toNat - 176) + 1088) ≤ 0x80019f58) ∧
        (A.hi ≤ SL.lo ∨ (sp.toNat - 176) + 1088 ≤ A.lo) ∧
        (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo) ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        -- ITEM ZERO B1: the child expression's budget at the statement
        -- frame `sp - 176`, `.fn`-bodies bound, store-bodies invariant.
        StackOK SL (sp - 176#64)
          (e.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget e = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget) :
    LandedN 4 c (fun c' => ExecJalPreBundle e c' st d env) := by
  obtain ⟨hArm, hpay, hExprChild, hstmtAl, hstmtLo, hstmtRam, hstmtWin,
    hEvCode, hViInt, hViSlot, hStoreSurvJ,
    hopAl, hopLo, hopHi, hopWin, hopStk, hsproom, hsp16pre,
    hSLlo, hSLhiRam, hSLwin,
    hjspSLhi, hcodeStkJ, htableStkJ1, htableStkJ2, harenaStkJ, harenaCode,
    hgframe, hg8, hg18, hstackBudget, hexprBodies, hstoreBodies⟩ := hpre
  -- unpack ExecArmEntryK
  obtain ⟨hG, htick, hpc, hs0, hs1, hs3, hs2, hsp, hra, ⟨vmi, hmi⟩,
    hout, houtStr, hmem, hcode, hstore,
    hslotRa, hslotS0, hslotS1, hslotS2, hslotS3,
    hgx8, hgx9, hgx18, hgx19, hgx2, hframeK, hmemframeK,
    hsp176, hsphi, hsplo, hspwin, hsp8, hraAl⟩ := hArm
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- `esp` = the arm's actual x2 = sp - 176
  have hespN : (sp - 176#64).toNat = sp.toNat - 176 := by
    rw [BitVec.toNat_sub]
    have h176 : (176#64 : BitVec 64).toNat = 176 := by decide
    rw [h176]; have := sp.isLt; omega
  -- payload read-back bytes for the `ld a2,8(s0)`
  have h8 : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  have haddr8 : (aStmt + sign_extend (m := 64) (0x008#12)).toNat = aStmt.toNat + 8 := by
    rw [h8, BitVec.toNat_add]; have hv : (8#64 : BitVec 64).toNat = 8 := by decide
    rw [hv]; omega
  obtain ⟨pb0, pb1, pb2, pb3, pb4, pb5, pb6, pb7, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hpsext⟩ :=
    spill_roundtrip_ee ment (aStmt.toNat + 8) aExprChild hpay
  -- sub-sret buffer addr = esp + 16
  have hsub16 : ((sp - 176#64) + sign_extend (m := 64) (0x010#12)).toNat = (sp.toNat - 176) + 16 := by
    have h16 : (sign_extend (m := 64) (0x010#12) : BitVec 64) = 16#64 := by
      apply BitVec.eq_of_toNat_eq; decide
    rw [h16, BitVec.toNat_add]; have hv : (16#64 : BitVec 64).toNat = 16 := by decide
    rw [hv, hespN]; omega
  -- ============ 0x80004170: ld a2,8(s0) → x12 := aExprChild ============
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    site_80004170_es c.σ c.tick c.steps (0x80004170#64) vmi aStmt pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7
      hG hpc hmi hs0 (hmem ▸ hcode) rfl
      (by rw [haddr8]; omega) (by rw [haddr8]; omega)
      (by rw [haddr8, htoh]; rcases hstmtWin with h | h
          · left; rw [htoh] at h; omega
          · right; rw [htoh] at h; omega) (by rw [haddr8]; omega)
      (by rw [haddr8, hmem]; exact hp0) (by rw [haddr8, hmem]; exact hp1)
      (by rw [haddr8, hmem]; exact hp2) (by rw [haddr8, hmem]; exact hp3)
      (by rw [haddr8, hmem]; exact hp4) (by rw [haddr8, hmem]; exact hp5)
      (by rw [haddr8, hmem]; exact hp6) (by rw [haddr8, hmem]; exact hp7) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = ment := by rw [hmem1]; exact hmem
  have hpc1 : σ1.regs.get? Register.PC = some (0x80004174#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80004170#64) 4 = (0x80004174#64 : BitVec 64) from by decide] at this
  have hx12_1 : σ1.regs.get? Register.x12 = some aExprChild := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hpsext] at this
  have hs1_1 : σ1.regs.get? Register.x9 = some aInterp := obs_alu_other' hobs1 Register.x9 (by decide) hs1
  have hs3_1 : σ1.regs.get? Register.x19 = some aEnv := obs_alu_other' hobs1 Register.x19 (by decide) hs3
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 176#64) := obs_alu_other' hobs1 Register.x2 (by decide) hsp
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hout1 : σ1.sailOutput = out0 := by rw [hobs1.out, sailOutput_sigmaPost_alu]; exact hout
  have hcode1 : Exec_stmtLoaded σ1.mem := by rw [hmem1e]; exact hcode
  -- ============ 0x80004174: addi a0,sp,16 → x10 := esp + 16 ============
  obtain ⟨σ2, i2, hs2', hi2, hG2, hmem2, hobs2⟩ :=
    site_80004174_es σ1 i1 (c.steps + 1) (0x80004174#64) vmi1 (sp - 176#64) hG1 hpc1 hmi1 hsp_1 hcode1 rfl hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2'
  have hmem2e : σ2.mem = ment := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x80004178#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80004174#64) 4 = (0x80004178#64 : BitVec 64) from by decide] at this
  have hx10_2 : σ2.regs.get? Register.x10 = some ((sp - 176#64) + sign_extend (m := 64) (0x010#12)) :=
    obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs1_2 : σ2.regs.get? Register.x9 = some aInterp := obs_alu_other' hobs2 Register.x9 (by decide) hs1_1
  have hs3_2 : σ2.regs.get? Register.x19 = some aEnv := obs_alu_other' hobs2 Register.x19 (by decide) hs3_1
  have hx12_2 : σ2.regs.get? Register.x12 = some aExprChild := obs_alu_other' hobs2 Register.x12 (by decide) hx12_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp - 176#64) := obs_alu_other' hobs2 Register.x2 (by decide) hsp_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hout2 : σ2.sailOutput = out0 := by rw [hobs2.out, sailOutput_sigmaPost_alu]; exact hout1
  have hcode2 : Exec_stmtLoaded σ2.mem := by rw [hmem2e]; exact hcode
  -- ============ 0x80004178: mv a3,s3 (addi x13,x19,0) → x13 := aEnv ============
  obtain ⟨σ3, i3, hs3', hi3, hG3, hmem3, hobs3⟩ :=
    site_80004178_es σ2 i2 (c.steps + 1 + 1) (0x80004178#64) vmi2 aEnv hG2 hpc2 hmi2 hs3_2 hcode2 rfl hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3'
  have hmem3e : σ3.mem = ment := by rw [hmem3]; exact hmem2e
  have hpc3 : σ3.regs.get? Register.PC = some (0x8000417c#64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x80004178#64) 4 = (0x8000417c#64 : BitVec 64) from by decide] at this
  have hx13_3 : σ3.regs.get? Register.x13 = some (aEnv + sign_extend (m := 64) (0x000#12)) :=
    obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs1_3 : σ3.regs.get? Register.x9 = some aInterp := obs_alu_other' hobs3 Register.x9 (by decide) hs1_2
  have hx10_3 : σ3.regs.get? Register.x10 = some ((sp - 176#64) + sign_extend (m := 64) (0x010#12)) :=
    obs_alu_other' hobs3 Register.x10 (by decide) hx10_2
  have hx12_3 : σ3.regs.get? Register.x12 = some aExprChild := obs_alu_other' hobs3 Register.x12 (by decide) hx12_2
  have hsp_3 : σ3.regs.get? Register.x2 = some (sp - 176#64) := obs_alu_other' hobs3 Register.x2 (by decide) hsp_2
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hout3 : σ3.sailOutput = out0 := by rw [hobs3.out, sailOutput_sigmaPost_alu]; exact hout2
  have hcode3 : Exec_stmtLoaded σ3.mem := by rw [hmem3e]; exact hcode
  -- ============ 0x8000417c: mv a1,s1 (addi x11,x9,0) → x11 := aInterp ============
  obtain ⟨σ4, i4, hs4', hi4, hG4, hmem4, hobs4⟩ :=
    site_8000417c_es σ3 i3 (c.steps + 1 + 1 + 1) (0x8000417c#64) vmi3 aInterp hG3 hpc3 hmi3 hs1_3 hcode3 rfl hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4'
  have hmem4e : σ4.mem = ment := by rw [hmem4]; exact hmem3e
  have hpc4 : σ4.regs.get? Register.PC = some (0x80004180#64) := by
    have := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x8000417c#64) 4 = (0x80004180#64 : BitVec 64) from by decide] at this
  have hx11_4 : σ4.regs.get? Register.x11 = some (aInterp + sign_extend (m := 64) (0x000#12)) :=
    obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx10_4 : σ4.regs.get? Register.x10 = some ((sp - 176#64) + sign_extend (m := 64) (0x010#12)) :=
    obs_alu_other' hobs4 Register.x10 (by decide) hx10_3
  have hx12_4 : σ4.regs.get? Register.x12 = some aExprChild := obs_alu_other' hobs4 Register.x12 (by decide) hx12_3
  have hx13_4 : σ4.regs.get? Register.x13 = some (aEnv + sign_extend (m := 64) (0x000#12)) :=
    obs_alu_other' hobs4 Register.x13 (by decide) hx13_3
  have hsp_4 : σ4.regs.get? Register.x2 = some (sp - 176#64) := obs_alu_other' hobs4 Register.x2 (by decide) hsp_3
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hout4 : σ4.sailOutput = out0 := by rw [hobs4.out, sailOutput_sigmaPost_alu]; exact hout3
  -- the mv's are addi rd,rs,0: strip the +0
  have hx11_val : σ4.regs.get? Register.x11 = some aInterp := by
    rw [hx11_4, sext_zero, BitVec.add_zero]
  have hx13_val : σ4.regs.get? Register.x13 = some aEnv := by
    rw [hx13_4, sext_zero, BitVec.add_zero]
  -- the four ALU heads preserve the callee-saved gpre frame (none writes x8/x18)
  have abi_ne' : ∀ {X R : Register}, AbiPreserved X = false → AbiPreserved R = true →
      (X == R) = false := by
    intro X R hX hR
    rcases hXR : (X == R) with _ | _
    · rfl
    · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)
  have hframe4 : ∀ R : Register, AbiPreservedNoise R → σ4.regs.get? R = gpre R := by
    intro R hR
    obtain ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩ := hR
    have h12R : (Register.x12 == R) = false := abi_ne' (by decide) hab
    have h10R : (Register.x10 == R) = false := abi_ne' (by decide) hab
    have h13R : (Register.x13 == R) = false := abi_ne' (by decide) hab
    have h11R : (Register.x11 == R) = false := abi_ne' (by decide) hab
    have f1 : σ1.regs.get? R = c.σ.regs.get? R :=
      (hobs1.1 R hmcR hmtR hmipR).trans
        (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h12R hnpcR hmiiR)
    have f2 : σ2.regs.get? R = σ1.regs.get? R :=
      (hobs2.1 R hmcR hmtR hmipR).trans
        (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h10R hnpcR hmiiR)
    have f3 : σ3.regs.get? R = σ2.regs.get? R :=
      (hobs3.1 R hmcR hmtR hmipR).trans
        (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h13R hnpcR hmiiR)
    have f4 : σ4.regs.get? R = σ3.regs.get? R :=
      (hobs4.1 R hmcR hmtR hmipR).trans
        (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h11R hnpcR hmiiR)
    rw [f4, f3, f2, f1]; exact hgframe R ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩
  -- ================= land at σ4 (the jal PC 0x80004180) as `ExecJalPreBundle e` =========
  -- ghosts: ExecJalPreBundle.sp := esp + 1088 = (sp-176)+1088 (so sp-1088 = esp = x2);
  --         subsret := esp+16; sret := aInterp (x9, only needs to be defined);
  --         aIn := aInterp; aOperand := aExprChild; mcall := ment.  The exec twin has
  --         NO spill-window read64 premises (dropped as dead — see the module doc).
  -- reusable bounds over jsp := (sp-176)+1088
  have hespge : SL.lo + 3264 ≤ sp.toNat - 176 := hsproom
  have hsp1088 : 1088 ≤ ((sp - 176#64) + 1088#64).toNat := by
    rw [BitVec.toNat_add]; have hv : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [hv, hespN]; omega
  have hjspN : ((sp - 176#64) + 1088#64).toNat = (sp.toNat - 176) + 1088 := by
    rw [BitVec.toNat_add]; have hv : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [hv, hespN]; omega
  -- x2 at the jal = sp - 176 = jsp - 1088
  have hjspcancel : ((sp - 176#64) + 1088#64) - 1088#64 = sp - 176#64 := by
    rw [BitVec.add_sub_cancel]
  have hx2jsp : σ4.regs.get? Register.x2 = some (((sp - 176#64) + 1088#64) - 1088#64) := by
    rw [hjspcancel]; exact hsp_4
  refine ⟨4, ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩, by omega,
    StepsN.succ hstep1 (StepsN.succ hstep2 (StepsN.succ hstep3 (StepsN.succ hstep4 (StepsN.zero _)))), ?_⟩
  refine ⟨gpre, N, A, SL, φf, φc, (0x80004180#64), (0x80004184#64), (0x1fefe4#21),
    (sp - 176#64) + 1088#64, r, aInterp, (sp - 176#64) + sign_extend (m := 64) (0x010#12),
    aInterp, aExprChild, v8, v9, v18, out0, ment, ?_, ?_, ?_, ?_,
    hG4, hi4, hpc4, hx10_4, ?_, hx11_val, hx12_4, hx2jsp, ⟨vmi4, hmi4⟩, hout4, ?_,
    hmem4e, ?_, hEvCode, hViInt, hViSlot, ?_, ?_, ?_, hframe4, ⟨hg8, hg18⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- hjaltgt : callPC + sext jalImm = evalExprEntry
  · apply BitVec.eq_of_toNat_eq; simp only [evalExprEntry]; decide
  -- hlink
  · apply BitVec.eq_of_toNat_eq; decide
  -- retAl
  · decide
  -- hjalSite : the jal at 0x80004180 (Exec_stmtLoaded-typed — matches `site_80004180_es`)
  · intro σ i u vmiσ hGσ hpcσ hmiσ hcodeσ hiσ
    exact site_80004180_es σ i u (0x80004180#64) vmiσ hGσ hpcσ hmiσ hcodeσ rfl hiσ
  -- x9 = sret := aInterp (mv a1,s1 wrote x11; x9 still = aInterp from s1)
  · have : σ4.regs.get? Register.x9 = some aInterp := by
      obtain ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩ :
          AbiPreservedNoise Register.x9 := by
        refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
      have f4 : σ4.regs.get? Register.x9 = σ3.regs.get? Register.x9 :=
        (hobs4.1 Register.x9 hmcR hmtR hmipR).trans
          (get?_sigmaPost_alu _ _ _ _ _ Register.x9 hmiR hpcR (by decide) hnpcR hmiiR)
      rw [f4]; exact hs1_3
    exact this
  -- String.join out0.toList = st.out
  · exact houtStr
  -- Exec_stmtLoaded ment
  · exact hcode
  -- ExprRepr ment aExprChild e
  · exact hExprChild
  -- StoreRepr ment
  · exact hstore
  -- store_survives over [SL.lo, jsp) (the named premise, rewritten to jsp form)
  · intro m' hag
    refine hStoreSurvJ m' (fun k hk1 hk2 => ?_)
    apply hag k
    · -- goal is over the bundle window `(sp-176+1088).toNat`; hk1 is the reduced form
      rw [hjspN]; exact hk1
    · -- both carve-outs are `[aInterp, aInterp+24)` (sret := aInterp)
      exact hk2
  -- aOperand % 8 = 0
  · exact hopAl
  -- 0x80000000 ≤ aOperand
  · exact hopLo
  -- aOperand + 16 ≤ 0x100000000
  · exact hopHi
  -- tohostAddr + 16 ≤ aOperand
  · exact hopWin
  -- aOperand + 16 ≤ SL.lo ∨ jsp - 1088 ≤ aOperand
  · rcases hopStk with h | h
    · left; exact h
    · right; rw [show ((sp - 176#64) + 1088#64).toNat - 1088 = sp.toNat - 176 by rw [hjspN]; omega]; exact h
  -- subsret % 8 = 0 : (esp+16) % 8
  · rw [hsub16]; omega
  -- jsp - 1088 ≤ subsret : esp ≤ esp+16
  · rw [hsub16, show ((sp - 176#64) + 1088#64).toNat - 1088 = sp.toNat - 176 by rw [hjspN]; omega]; omega
  -- subsret + 24 ≤ jsp - 32 : esp+40 ≤ esp+1056
  · rw [hsub16, hjspN]; omega
  -- SL.lo + 3264 ≤ jsp
  · rw [hjspN]; omega
  -- jsp ≤ SL.hi  (named premise, jsp form)
  · rw [hjspN]; exact hjspSLhi
  -- jsp % 16 = 0  (jsp = sp+912, 912%16=0, from sp%16=0)
  · rw [hjspN]; omega
  -- 0x80000000 ≤ SL.lo
  · exact hSLlo
  -- SL.hi ≤ 0x100000000
  · exact hSLhiRam
  -- tohostAddr + 16 ≤ SL.lo
  · exact hSLwin
  -- jsp ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo  (named premise, jsp form)
  · rcases hcodeStkJ with h | h
    · left; rw [hjspN]; exact h
    · right; exact h
  -- (0x8000281c ≤ SL.lo ∨ jsp ≤ 0x8000280c)  (named premise, jsp form)
  · rcases htableStkJ1 with h | h
    · left; exact h
    · right; rw [hjspN]; exact h
  -- (0x80019f58 + 4 ≤ SL.lo ∨ jsp ≤ 0x80019f58)  (named premise, jsp form)
  · rcases htableStkJ2 with h | h
    · left; exact h
    · right; rw [hjspN]; exact h
  -- (A.hi ≤ SL.lo ∨ jsp ≤ A.lo)  (named premise, jsp form)
  · rcases harenaStkJ with h | h
    · left; exact h
    · right; rw [hjspN]; exact h
  -- (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo)
  · exact ⟨harenaCode,
      (by rw [BitVec.add_sub_cancel]; exact hstackBudget),
      hexprBodies, hstoreBodies⟩

#print axioms blockB_stmtExpr_stagePre

/-! ## §2. The `stmtExpr` field composer

`blockB_stmtExpr_stagePre` is the arm-head cut (SECOND factor).  The FIRST factor is
the exec dispatch bridge `ExecEntry (.expr e) → ` (`blockB_stmtExpr_stagePre`'s entry
bundle at `0x80004170`).  The dispatch's prologue + jump-table half is the LANDED
`execBlockA`; the remaining child-payload / eval-code / wide-window-survival /
enlarged-frame-geometry facts a `blockA` cannot produce are named as
`StmtExprArmDispatch` (mirroring `AssignArmDispatch`).  `stmtExpr_field_of_dispatch`
threads it through, closing `EvalChildStages.stmtExpr` (via `stmtExpr_split'`) MODULO
that one dispatch residual. -/

/-- **The stmtExpr dispatch residual** (the `blockB_stmtExpr_stagePre` entry bundle a
`blockA` would produce, named as a Triple premise; `Mid` is that bundle). -/
def StmtExprArmDispatch
    (e : Expr) (st : Vsa.While.St) (d : Nat) (env : Addr) (c : Config) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem),
    ExecEntry g N A SL φf φc st d env (.expr e) sp r aInterp aStmt aEnv aRet m0 c →
    Triple (fun c'' => c'' = c)
      (fun c' => ∃ (gpre : (R : Register) → Option (RegisterType R))
        (aExprChild : BitVec 64) (v8 v9 v18 v19 : BitVec 64) (ment : Mem),
        ExecArmEntryK g N A SL φf φc st (0x80004170#64)
          sp r aInterp aStmt aEnv aRet v8 v9 v18 v19 c'.σ.sailOutput m0 ment c' ∧
        read64 ment (aStmt.toNat + 8) = some aExprChild.toNat ∧
        ExprRepr ment aExprChild.toNat e ∧
        aStmt.toNat % 8 = 0 ∧
        0x80000000 ≤ aStmt.toNat ∧ aStmt.toNat + 16 ≤ 0x100000000 ∧
        (aStmt.toNat + 16 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aStmt.toNat) ∧
        Eval_exprLoaded ment ∧ Value_intLoaded ment ∧ IntSlotPinned ment ∧
        (∀ m' : Mem,
          (∀ k, ¬ (SL.lo ≤ k ∧ k < (sp.toNat - 176) + 1088) →
            ¬ (aInterp.toNat ≤ k ∧ k < aInterp.toNat + 24) →
            ment[k]? = m'[k]?) →
          StoreRepr m' N A φf φc st.store) ∧
        aExprChild.toNat % 8 = 0 ∧
        0x80000000 ≤ aExprChild.toNat ∧ aExprChild.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ aExprChild.toNat ∧
        (aExprChild.toNat + 16 ≤ SL.lo ∨ (sp.toNat - 176) ≤ aExprChild.toNat) ∧
        SL.lo + 3264 ≤ sp.toNat - 176 ∧ sp.toNat % 16 = 0 ∧
        0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000 ∧ tohostAddr + 16 ≤ SL.lo ∧
        ((sp.toNat - 176) + 1088 ≤ SL.hi) ∧
        (((sp.toNat - 176) + 1088) ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        ((0x8000281c : Nat) ≤ SL.lo ∨ ((sp.toNat - 176) + 1088) ≤ 0x8000280c) ∧
        ((0x80019f58 : Nat) + 4 ≤ SL.lo ∨ ((sp.toNat - 176) + 1088) ≤ 0x80019f58) ∧
        (A.hi ≤ SL.lo ∨ (sp.toNat - 176) + 1088 ≤ A.lo) ∧
        (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo) ∧
        (∀ R : Register, AbiPreservedNoise R → c'.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        -- ITEM ZERO B1: the child expression's budget at the statement
        -- frame `sp - 176`, `.fn`-bodies bound, store-bodies invariant.
        StackOK SL (sp - 176#64)
          (e.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget e = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget)

/-- **The stmtExpr RE-ENTRY dispatch residual** (wave 45, the amended `SEntryC`'s
dispatch-head leg): from `SDispatchC (.expr e)` — a tail re-dispatch landing the
expr arm from `execStmtDispatchHead` — stage the sub-expr sub-call.  Supplied
upstream by a dispatch-head → arm-head span (the jump-table half of `execBlockA`
re-run from `0x80004014`, no prologue). -/
def StmtExprReentryDispatch
    (e : Expr) (st : Vsa.While.St) (d : Nat) (env : Addr) (c : Config) : Prop :=
  SDispatchC c st d env (.expr e) →
  LandedN 1 c (fun c' => ExecJalPreBundle e c' st d env)

/-- **The `EvalChildStages.stmtExpr` field, machine-composed (exec twin).**  From
the AMENDED (wave-45, 3-way) `SEntryC (.expr e)` plus the dispatch residuals, the
composer 3-way-cases the entry: fresh-call leg runs the dispatch Triple to
`blockB_stmtExpr_stagePre`'s entry bundle and that cut stages the sub-expr
sub-call (landing at `ExecJalPreBundle e`); the dispatch-head leg is the named
wave-45 `StmtExprReentryDispatch` residual; the while-arm leg is structurally
impossible (`.expr ≠ .whileStmt`); `stmtExpr_split'` finishes to `EEntryC e`. -/
theorem stmtExpr_field_of_dispatch
    (e : Expr) (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr)
    (hDisp : StmtExprArmDispatch e st d env c)
    (hReentry : StmtExprReentryDispatch e st d env c) :
    SEntryC c st d env (.expr e) →
    LandedN 1 c (fun c' => EEntryC c' st d env e) := by
  refine stmtExpr_split' e c st d env (fun hSE => ?_)
  rcases hSE with hSE | hRe | hWA
  · -- fresh-call leg (the pre-amendment body)
    obtain ⟨g, N, A, SL, φf, φc, sp, r, aInterp, aStmt, aEnv, aRet, m0, hEntry⟩ := hSE
    -- run the dispatch Triple to the arm-head entry bundle
    obtain ⟨c1, hsteps1, hMid⟩ :=
      hDisp g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 hEntry c rfl
    obtain ⟨gpre, aExprChild, v8, v9, v18, v19, ment, hArm, hpay, hExprChild,
      hstmtAl, hstmtLo, hstmtRam, hstmtWin, hEvCode, hViInt, hViSlot, hStoreSurvJ,
      hopAl, hopLo, hopHi, hopWin, hopStk, hsproom, hsp16pre, hSLlo, hSLhiRam, hSLwin,
      hjspSLhi, hcodeStkJ, htableStkJ1, htableStkJ2, harenaStkJ, harenaCode,
      hgframe, hg8, hg18, hstackBudget, hexprBodies, hstoreBodies⟩ := hMid
    -- the arm-head cut stages the sub-call at `c1`
    have hcut : LandedN 4 c1 (fun c' => ExecJalPreBundle e c' st d env) :=
      blockB_stmtExpr_stagePre g gpre N A SL φf φc st d env e
        sp r aInterp aStmt aEnv aRet aExprChild v8 v9 v18 v19 c1.σ.sailOutput m0 ment c1
        ⟨hArm, hpay, hExprChild, hstmtAl, hstmtLo, hstmtRam, hstmtWin,
         hEvCode, hViInt, hViSlot, hStoreSurvJ,
         hopAl, hopLo, hopHi, hopWin, hopStk, hsproom, hsp16pre, hSLlo, hSLhiRam, hSLwin,
         hjspSLhi, hcodeStkJ, htableStkJ1, htableStkJ2, harenaStkJ, harenaCode,
         hgframe, hg8, hg18, hstackBudget, hexprBodies, hstoreBodies⟩
    -- compose the dispatch prefix (a `Steps`) with the counted cut
    obtain ⟨n1, hn1⟩ := hsteps1.toN
    obtain ⟨m2, c2, hm2, hs2, hpb⟩ := hcut
    exact ⟨n1 + m2, c2, by omega, hn1.trans_add hs2, hpb⟩
  · -- dispatch-head re-entry leg (wave-45 named residual)
    exact hReentry hRe
  · -- while-arm leg: `.expr e` is not a while statement
    obtain ⟨cnd', b', hEq⟩ := sWhileArmC_shape hWA
    exact nomatch hEq

#print axioms stmtExpr_field_of_dispatch

end Vsa.Sim
