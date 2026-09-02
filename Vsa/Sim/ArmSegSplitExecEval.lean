import Vsa.Sim.ArmSegSplitEval

/-!
# `ArmSegSplitExecEval` — the exec-arm `jal eval_expr` marshalling twin (Wave 40)

`ArmSegSplit.evalEntry_of_jalPrefix` marshals the recursive `jal eval_expr` seam
that lives INSIDE `eval_expr`'s own text: its `hjalSite` is typed with
`Eval_exprLoaded σ.mem` (the jal's instruction bytes are eval_expr text).  The SIX
exec-eval `EvalChildStages` fields (`stmtExpr`/`stmtRet`/`stmtVarInit`/`stmtIfCond`/
`stmtWhileCond`/`flCond`) reach `eval_expr` from a `jal` sited in **`exec_stmt`'s
text** (e.g. `0x80004180`), whose bytes come from `Exec_stmtLoaded` — and
`0x80004180` is NOT covered by any `eval_exprChunk`.  So those arm-head cuts cannot
satisfy `JalPreBundle.hjalSite` (observation
`execframeshift-REAL-obstruction-is-jalSite-loaded-predicate-not-frame`).

This file is the TWIN:

* `execEvalEntry_of_jalPrefix` — a clone of `evalEntry_of_jalPrefix` whose
  `hjalSite` is typed with `Exec_stmtLoaded σ.mem`.  The landed child `EvalEntry` is
  IDENTICAL (the child eval frame still needs `Eval_exprLoaded mcall`, carried as a
  separate premise); only the seam's loaded-predicate flips.
* `ExecJalPreBundle` — the `JalPreBundle` twin whose `hjalSite` uses
  `Exec_stmtLoaded` (and which additionally carries `Exec_stmtLoaded mcall`, since
  the exec-arm jal site consumes it).
* `landedN_eentryC_of_execPreBundle` — the exec twin of
  `landedN_eentryC_of_preBundle`.

Everything else (the frame-shift ghost rebase `sp := esp+1088`, the wide-window
`StoreRepr` survival premise, the mv/ld site batteries) is unchanged from the eval
design; the twin is the ONE shared bridge the 6 exec arm heads land through.

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

/-- **The exec-arm `jal eval_expr` marshalling twin.**  Identical to
`evalEntry_of_jalPrefix` except the `jal` site is fired from `Exec_stmtLoaded σ.mem`
(the jal lives in `exec_stmt`'s text).  `Eval_exprLoaded mcall` is still required
(the child eval frame runs eval_expr text) and is carried as its own premise. -/
theorem execEvalEntry_of_jalPrefix
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (esub : Expr)
    (callPC retPC : BitVec 64) (jalImm : BitVec 21)
    (sp r sret subsret aIn aOperand : BitVec 64) (v8 v9 v18 : BitVec 64)
    (out0 : Array String) (mcall : Mem)
    (c : Config)
    (hjaltgt : (callPC + sign_extend (m := 64) jalImm) = BitVec.ofNat 64 evalExprEntry)
    (hlink : (BitVec.addInt callPC 4) = retPC)
    (hretAl : retPC.toNat % 4 = 0)
    (hjalSite : ∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
      GoodState σ → σ.regs.get? Register.PC = some callPC →
      σ.regs.get? Register.minstret = some vmi → Exec_stmtLoaded σ.mem → i < 2 →
      ∃ (σ' : MState) (i' : Nat),
        Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
        ReadsLikePost σ' (sigmaPost_jal σ callPC vmi jalImm Register.x1 (BitVec.addInt callPC 4)))
    (hpre :
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some callPC ∧
        c.σ.regs.get? Register.x10 = some subsret ∧
        c.σ.regs.get? Register.x9 = some sret ∧
        c.σ.regs.get? Register.x11 = some aIn ∧
        c.σ.regs.get? Register.x12 = some aOperand ∧
        c.σ.regs.get? Register.x2 = some (sp - 1088#64) ∧
        (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
        c.σ.sailOutput = out0 ∧
        String.join out0.toList = st.out ∧
        c.σ.mem = mcall ∧
        Exec_stmtLoaded mcall ∧
        Eval_exprLoaded mcall ∧ Value_intLoaded mcall ∧ IntSlotPinned mcall ∧
        ExprRepr mcall aOperand.toNat esub ∧
        StoreRepr mcall N A φf φc st.store ∧
        (∀ m' : Mem,
          (∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
            mcall[k]? = m'[k]?) →
          StoreRepr m' N A φf φc st.store) ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        ((∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w)) ∧
        -- (the four `read64 mcall (sp-8/-16/-24/-32)` spill-window premises + the
        -- `sp ≤ 0x100000000` bound are DEAD in this bridge — the child EvalEntry's
        -- `spill_defined` uses the post-jal x8/x9/x18 REGISTER facts, not the memory
        -- slots — so they are DROPPED from this exec twin, which unblocks the exec
        -- arm: those slot addresses would sit in the caller's frame at `sp+912-8…`,
        -- for which no memory fact exists.  See the module doc.)
        aOperand.toNat % 8 = 0 ∧
        0x80000000 ≤ aOperand.toNat ∧ aOperand.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ aOperand.toNat ∧
        (aOperand.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aOperand.toNat) ∧
        subsret.toNat % 8 = 0 ∧
        sp.toNat - 1088 ≤ subsret.toNat ∧ subsret.toNat + 24 ≤ sp.toNat - 32 ∧
        SL.lo + 3264 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 ∧
        0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000 ∧ tohostAddr + 16 ≤ SL.lo ∧
        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        ((0x8000281c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x8000280c) ∧
        ((0x80019f58 : Nat) + 4 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58) ∧
        (A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧
        (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo) ∧
        -- ITEM ZERO B1: the child expression's recursion-sound budget at the
        -- lowered `sp - 1088`, `.fn`-bodies bound, store-bodies invariant.
        StackOK SL (sp - 1088#64)
          (esub.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget esub = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget) :
    LandedN 1 c (fun c' =>
      EvalEntry (fun R => c'.σ.regs.get? R) N A SL φf φc st d env esub
        (sp - 1088#64) retPC subsret aIn aOperand mcall c') := by
  obtain ⟨hG, htick, hpc, ha0, hs1, hx11, hx12, hsp, ⟨vmi, hmi⟩, hout, houtStr, hmemc,
    hcodeExec, hcode, hviCode, hslot, hsubexpr, hstore, hstoreSurv, hframe,
    ⟨⟨w8, hw8⟩, ⟨w18, hw18⟩⟩,
    hopAl, hopLo, hopHi, hopWin, hopStk,
    hssAl, hssLo, hssHi,
    hsproom, hspSLhi, hsp16, hSLlo, hSLhiRam, hSLwin,
    hcodeStk, hviStk, htableStk, harenaStk, harenaCode,
    hstackBudget, hexprBodies, hstoreBodies⟩ := hpre
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hsp1088 : 1088 ≤ sp.toNat := by omega
  have hspsub : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]; have := sp.isLt; omega
  -- ============ callPC: jal eval_expr → PC := evalExprEntry, x1 := retPC ============
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    hjalSite c.σ c.tick c.steps vmi hG hpc hmi (hmemc ▸ hcodeExec) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = mcall := by rw [hmem1]; exact hmemc
  have hpc1 : σ1.regs.get? Register.PC = some (BitVec.ofNat 64 evalExprEntry) := by
    have := obs_jalT_pc hobs1; rwa [hjaltgt] at this
  have hlink1 : σ1.regs.get? Register.x1 = some retPC := by
    have := obs_jalT_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hlink] at this
  have ha0_1 : σ1.regs.get? Register.x10 = some subsret := obs_jalT_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have hs1_1 : σ1.regs.get? Register.x9 = some sret := obs_jalT_other hobs1 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1
  have hx11_1 : σ1.regs.get? Register.x11 = some aIn := obs_jalT_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11
  have hx12_1 : σ1.regs.get? Register.x12 = some aOperand := obs_jalT_other hobs1 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 1088#64) := obs_jalT_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp
  have hx8_1 : σ1.regs.get? Register.x8 = some w8 := by
    have hc8 : c.σ.regs.get? Register.x8 = some w8 := (hframe Register.x8 (by decide)).trans hw8
    exact obs_jalT_other hobs1 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc8
  have hx18_1 : σ1.regs.get? Register.x18 = some w18 := by
    have hc18 : c.σ.regs.get? Register.x18 = some w18 := (hframe Register.x18 (by decide)).trans hw18
    exact obs_jalT_other hobs1 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc18
  obtain ⟨vmi1, hmi1⟩ := obs_jalT_minstret hobs1
  have hout1 : σ1.sailOutput = out0 := by
    rw [hobs1.out, sailOutput_sigmaPost_jal]; exact hout
  -- ============ the sub-call's EvalEntry at ⟨σ1, i1, steps+1⟩ ============
  refine ⟨1, ⟨σ1, i1, c.steps + 1⟩, Nat.le_refl _,
    StepsN.succ hstep1 (StepsN.zero _), ?_⟩
  · exact
      { good := hG1
        tick := hi1
        pc := hpc1
        a0 := ha0_1
        a1 := hx11_1
        a2 := hx12_1
        ra := hlink1
        ra_align := hretAl
        spReg := hsp_1
        stackOK := ⟨by rw [hspsub]; omega, by rw [hspsub]; omega, by rw [hspsub]; omega⟩
        stackBudget := hstackBudget
        expr_bodies := hexprBodies
        store_bodies := hstoreBodies
        minstret := ⟨vmi1, hmi1⟩
        mem := hmem1e
        code := by show Eval_exprLoaded σ1.mem; rw [hmem1e]; exact hcode
        expr := by rw [hmem1e]; exact hsubexpr
        store := by rw [hmem1e]; exact hstore
        store_survives := by
          intro m' hag
          refine hstoreSurv m' (fun k hk1 _ => ?_)
          have hk1' : ¬ (SL.lo ≤ k ∧ k < (sp - 1088#64).toNat) := by
            rw [hspsub]; intro ⟨ha, hb⟩; exact hk1 ⟨ha, by omega⟩
          have hk2' : ¬ (subsret.toNat ≤ k ∧ k < subsret.toNat + 24) := by
            intro ⟨ha, hb⟩; exact hk1 ⟨by omega, by omega⟩
          have := hag k hk1' hk2'
          rwa [hmem1e] at this
        out := by
          show Vsa.Machine.output σ1 = st.out
          simp only [Vsa.Machine.output]; rw [hout1]; exact houtStr
        frame := fun _ _ => rfl
        code_stack_disjoint := by
          rcases hcodeStk with h | h
          · left; rw [hspsub]; omega
          · right; exact h
        expr_stack_disjoint := by
          rcases hopStk with h | h
          · left; exact h
          · right; rw [hspsub]; omega
        expr_align := hopAl
        expr_ram := ⟨hopLo, hopHi⟩
        expr_win := hopWin
        sret_align := hssAl
        sret_ram := ⟨by omega, by omega⟩
        sret_win := by omega
        sret_vicode_disjoint := by
          rcases hviStk with h | h
          · right; omega
          · left; omega
        sret_stack_disjoint := by right; rw [hspsub]; omega
        sret_evalcode_disjoint := by
          rcases hcodeStk with h | h
          · left; omega
          · right; omega
        vicode_stack_disjoint := by
          rcases hviStk with h | h
          · left; exact h
          · right; rw [hspsub]; omega
        stack_ram := ⟨hSLlo, hSLhiRam⟩
        stack_win := hSLwin
        value_int_code := by rw [hmem1e]; exact hviCode
        int_slot := by rw [hmem1e]; exact hslot
        table_stack_disjoint := by
          rcases htableStk with h | h
          · left; exact h
          · right; rw [hspsub]; omega
        spill_defined := ⟨⟨w8, hx8_1⟩, ⟨sret, hs1_1⟩, ⟨w18, hx18_1⟩⟩ }

#print axioms execEvalEntry_of_jalPrefix

/-! ## The `ExecJalPreBundle` twin + its marshalling bridge -/

-- discipline: allow(R7-conj-tower-def) `ExecJalPreBundle` is the exec twin of the
-- SANCTIONED landing bundle `JalPreBundle` (carries layout DATA a `structure : Prop`
-- cannot project); its named destructurer is `landedN_eentryC_of_execPreBundle`.
set_option linter.unusedVariables false in
/-- **The exec-arm `jal eval_expr` PRE-bundle.**  `JalPreBundle` with the jal site
typed for `Exec_stmtLoaded` (and `Exec_stmtLoaded mcall` added, since the exec-arm
site consumes it).  The 6 exec-eval arm-head cuts land HERE. -/
def ExecJalPreBundle (e : Expr) (c' : Config) (st : Vsa.While.St) (d : Nat)
    (env : Addr) : Prop :=
  ∃ (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (callPC retPC : BitVec 64) (jalImm : BitVec 21)
    (sp r sret subsret aIn aOperand : BitVec 64) (v8 v9 v18 : BitVec 64)
    (out0 : Array String) (mcall : Mem),
    ((callPC + sign_extend (m := 64) jalImm) = BitVec.ofNat 64 evalExprEntry) ∧
    ((BitVec.addInt callPC 4) = retPC) ∧ retPC.toNat % 4 = 0 ∧
    (∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
      GoodState σ → σ.regs.get? Register.PC = some callPC →
      σ.regs.get? Register.minstret = some vmi → Exec_stmtLoaded σ.mem → i < 2 →
      ∃ (σ' : MState) (i' : Nat),
        Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
        ReadsLikePost σ' (sigmaPost_jal σ callPC vmi jalImm Register.x1 (BitVec.addInt callPC 4))) ∧
    GoodState c'.σ ∧ c'.tick < 2 ∧
    c'.σ.regs.get? Register.PC = some callPC ∧
    c'.σ.regs.get? Register.x10 = some subsret ∧
    c'.σ.regs.get? Register.x9 = some sret ∧
    c'.σ.regs.get? Register.x11 = some aIn ∧
    c'.σ.regs.get? Register.x12 = some aOperand ∧
    c'.σ.regs.get? Register.x2 = some (sp - 1088#64) ∧
    (∃ w, c'.σ.regs.get? Register.minstret = some w) ∧
    c'.σ.sailOutput = out0 ∧
    String.join out0.toList = st.out ∧
    c'.σ.mem = mcall ∧
    Exec_stmtLoaded mcall ∧
    Eval_exprLoaded mcall ∧ Value_intLoaded mcall ∧ IntSlotPinned mcall ∧
    ExprRepr mcall aOperand.toNat e ∧
    StoreRepr mcall N A φf φc st.store ∧
    (∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
        mcall[k]? = m'[k]?) →
      StoreRepr m' N A φf φc st.store) ∧
    (∀ R : Register, AbiPreservedNoise R → c'.σ.regs.get? R = gpre R) ∧
    ((∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w)) ∧
    -- (spill-window read64 premises + `sp ≤ 0x100000000` dropped — dead in the
    -- bridge, see `execEvalEntry_of_jalPrefix`.)
    aOperand.toNat % 8 = 0 ∧
    0x80000000 ≤ aOperand.toNat ∧ aOperand.toNat + 16 ≤ 0x100000000 ∧
    tohostAddr + 16 ≤ aOperand.toNat ∧
    (aOperand.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aOperand.toNat) ∧
    subsret.toNat % 8 = 0 ∧
    sp.toNat - 1088 ≤ subsret.toNat ∧ subsret.toNat + 24 ≤ sp.toNat - 32 ∧
    SL.lo + 3264 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 ∧
    0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000 ∧ tohostAddr + 16 ≤ SL.lo ∧
    (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
    ((0x8000281c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x8000280c) ∧
    ((0x80019f58 : Nat) + 4 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58) ∧
    (A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧
    (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo) ∧
    -- ITEM ZERO B1: the operand's recursion-sound budget at `sp - 1088`, its
    -- `.fn`-bodies bound, and the store-bodies invariant.
    StackOK SL (sp - 1088#64)
      (e.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
    Expr.bodiesBound Vsa.While.perCallBudget e = true ∧
    Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget

/-- **The exec pre-bundle drives into `EEntryC`.**  Exec twin of
`landedN_eentryC_of_preBundle`, through `execEvalEntry_of_jalPrefix`. -/
theorem landedN_eentryC_of_execPreBundle
    (e : Expr) (c' : Config) (st : Vsa.While.St) (d : Nat) (env : Addr)
    (h : ExecJalPreBundle e c' st d env) :
    LandedN 1 c' (fun c'' => EEntryC c'' st d env e) := by
  obtain ⟨gpre, N, A, SL, φf, φc, callPC, retPC, jalImm, sp, r, sret, subsret,
    aIn, aOperand, v8, v9, v18, out0, mcall, hjaltgt, hlink, hretAl, hjalSite, hrest⟩ := h
  have h := execEvalEntry_of_jalPrefix gpre N A SL φf φc st d env e
    callPC retPC jalImm sp r sret subsret aIn aOperand v8 v9 v18 out0 mcall c'
    hjaltgt hlink hretAl hjalSite hrest
  exact LandedN.weaken h (fun c'' hEE =>
    ⟨fun R => c''.σ.regs.get? R, N, A, SL, φf, φc,
      sp - 1088#64, retPC, subsret, aIn, aOperand, mcall, hEE⟩)

#print axioms landedN_eentryC_of_execPreBundle

/-- **Generic exec-eval-child split.**  A staging landing to `ExecJalPreBundle child`
composes with the exec marshalling bridge to `EEntryC child`.  The exec twin of
`evalChildSplit_of_stage`; shared by the 6 exec-eval `EvalChildStages` fields. -/
theorem execEvalChildSplit_of_stage
    (child : Expr) (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr)
    (hstaged : LandedN 1 c (fun c' => ExecJalPreBundle child c' st d env)) :
    LandedN 1 c (fun c' => EEntryC c' st d env child) :=
  LandedN.weakenCount (by omega : 1 ≤ 1 + 1)
    (LandedN.bind hstaged
      (fun c' hpb => landedN_eentryC_of_execPreBundle child c' st d env hpb))

#print axioms execEvalChildSplit_of_stage

/-! ## The 6 exec-eval `EvalChildStages` field splits (through `ExecJalPreBundle`)

Exact twins of `ArmSegSplitEval`'s `stmtExpr_split`/`stmtRet_split`/`stmtVarInit_split`/
`stmtIfCond_split`/`stmtWhileCond_split`/`flCond_split`, but the staging residual
lands at `ExecJalPreBundle` (the `Exec_stmtLoaded`-typed jal seam) and the exec
marshalling bridge finishes.  Each is a one-liner over `execEvalChildSplit_of_stage`;
the arm-head cut supplier (`blockB_<arm>_stagePre`) fills the residual. -/

/-- **`stmtExpr` field split (exec twin).**  `SEntryC (.expr e) → LandedN 1 (EEntryC e)`. -/
theorem stmtExpr_split' (e : Expr) (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr)
    (hstage : SEntryC c st d env (.expr e) →
      LandedN 1 c (fun c' => ExecJalPreBundle e c' st d env)) :
    SEntryC c st d env (.expr e) → LandedN 1 c (fun c' => EEntryC c' st d env e) :=
  fun hSE => execEvalChildSplit_of_stage e c st d env (hstage hSE)

#print axioms stmtExpr_split'

/-- **`stmtRet` field split (exec twin).** -/
theorem stmtRet_split' (e : Expr) (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr)
    (hstage : SEntryC c st d env (.ret (some e)) →
      LandedN 1 c (fun c' => ExecJalPreBundle e c' st d env)) :
    SEntryC c st d env (.ret (some e)) → LandedN 1 c (fun c' => EEntryC c' st d env e) :=
  fun hSE => execEvalChildSplit_of_stage e c st d env (hstage hSE)

#print axioms stmtRet_split'

/-- **`stmtVarInit` field split (exec twin).** -/
theorem stmtVarInit_split' (x : String) (e : Expr) (c : Config) (st : Vsa.While.St)
    (d : Nat) (env : Addr)
    (hstage : SEntryC c st d env (.varDecl x (some e)) →
      LandedN 1 c (fun c' => ExecJalPreBundle e c' st d env)) :
    SEntryC c st d env (.varDecl x (some e)) → LandedN 1 c (fun c' => EEntryC c' st d env e) :=
  fun hSE => execEvalChildSplit_of_stage e c st d env (hstage hSE)

#print axioms stmtVarInit_split'

/-- **`stmtIfCond` field split (exec twin).** -/
theorem stmtIfCond_split' (cnd : Expr) (t : Stmt) (e : Option Stmt) (c : Config)
    (st : Vsa.While.St) (d : Nat) (env : Addr)
    (hstage : SEntryC c st d env (.ifStmt cnd t e) →
      LandedN 1 c (fun c' => ExecJalPreBundle cnd c' st d env)) :
    SEntryC c st d env (.ifStmt cnd t e) → LandedN 1 c (fun c' => EEntryC c' st d env cnd) :=
  fun hSE => execEvalChildSplit_of_stage cnd c st d env (hstage hSE)

#print axioms stmtIfCond_split'

/-- **`stmtWhileCond` field split (exec twin).** -/
theorem stmtWhileCond_split' (cnd : Expr) (b : Stmt) (c : Config) (st : Vsa.While.St)
    (d : Nat) (env : Addr)
    (hstage : SEntryC c st d env (.whileStmt cnd b) →
      LandedN 1 c (fun c' => ExecJalPreBundle cnd c' st d env)) :
    SEntryC c st d env (.whileStmt cnd b) → LandedN 1 c (fun c' => EEntryC c' st d env cnd) :=
  fun hSE => execEvalChildSplit_of_stage cnd c st d env (hstage hSE)

#print axioms stmtWhileCond_split'

/-- **`flCond` field split (exec twin).** -/
theorem flCond_split' (cc : Expr) (step : Option Expr) (b : Stmt) (c : Config)
    (st : Vsa.While.St) (d : Nat) (env : Addr)
    (hstage : FEntryC c st d env (some cc) step b →
      LandedN 1 c (fun c' => ExecJalPreBundle cc c' st d env)) :
    FEntryC c st d env (some cc) step b → LandedN 1 c (fun c' => EEntryC c' st d env cc) :=
  fun hFE => execEvalChildSplit_of_stage cc c st d env (hstage hFE)

#print axioms flCond_split'

end Vsa.Sim
